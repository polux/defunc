{-# LANGUAGE ViewPatterns #-}
-- Copyright 2018 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE FlexibleContexts #-}

module TypeChecker where

import AST
import Pretty

import Control.Monad.Except
import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Internal.Fold as U
import Control.Exception.Base (assert)
import Control.Monad.Loops (allM)
import Debug.Trace

type DataConSignature = Bind Alphas (Delta, [Type], Type)
type Sigma = [(Name DataCon, DataConSignature)]
type Delta = [Constraint]
type Alphas = [Name Type]
type Gamma = [(Name FTerm, Type)]

typeCheck :: MonadError String m => FProgram -> m Type
typeCheck (FProgram b) = runFreshMT $ do
  (rdecls, FFunDefs bdefs) <- unbind b
  (rdefs, term) <- unbind bdefs
  let decls = unrec rdecls
      defs = [ (x, unembed ty, unembed t) | (x, ty, t) <- unrec rdefs ]
      sigma = extractSigma decls
      gamma = [ (x, ty) | (x, ty, _) <- defs ]
  mapM_ (checkDef sigma [] [] gamma) defs
  typeCheckFTerm sigma [] [] gamma term
 where
  extractSigma :: [TypeDecl] -> Sigma
  extractSigma decls = concatMap extract decls
   where
    extract (TypeDecl _ _ decls) = map break decls
    break (DataConDecl conName sig) = (conName, unembed sig)

typeCheckFTerm
  :: (Fresh m, MonadError String m)
  => Sigma
  -> Alphas
  -> Delta
  -> Gamma
  -> FTerm
  -> m Type
typeCheckFTerm sigma alphas delta gamma t = check t
 where
  check (FVar x) = lookupType gamma x
  check (FLam b) = do
    ((p, unembed->ty), t) <- unbind b
    (alphas', delta', gamma') <- typeCheckPattern sigma alphas p ty
    retType <- typeCheckFTerm sigma
                              (alphas ++ alphas')
                              (delta ++ delta')
                              (gamma ++ gamma')
                              t
    return (TCons (string2Name "->") [ty, retType])
  check (FTlam b) = do
    (tyvar, t) <- unbind b
    ty <- typeCheckFTerm sigma (tyvar : alphas) delta gamma t
    return $ TForall (bind tyvar ty)
  check (FCons con tys ts) = do
    bsig <- lookupDataCon sigma con
    (tvars, (constraints, argTypes, returnType)) <- unbind bsig
    when (length tvars < length tys)
         (throwError (show con ++ " is applied to too many type arguments"))
    when (length tvars > length tys)
         (throwError (show con ++ " is not applied to enough type arguments"))
    when (length argTypes < length ts)
         (throwError (show con ++ " is applied to too many arguments"))
    when (length argTypes > length ts)
         (throwError (show con ++ " is not applied to enough arguments"))
    let sub = zip tvars tys
        constraints' = substs sub constraints
        argTypes' = substs sub argTypes
        returnType' = substs sub returnType
    tsTypes <- mapM check ts
    checkEntailsAll alphas delta constraints'
    zipWithM_ (checkEqTypes alphas delta) tsTypes argTypes'
    return returnType'
  check (FApp t1 t2) = do
    ty1 <- check t1
    ty2 <- check t2
    case ty1 of
      TCons con [u1, u2] | con == string2Name "->" -> do
        checkEqTypes alphas delta u1 ty2
        return u2
      _ -> throwError
        (toString t1 ++ " cannot be applied: it has type " ++ toString ty1)
  check (FTApp t ty) = do
    checkKind alphas ty KType
    tty <- check t
    case tty of
      TForall b -> do
        (tvar, retType) <- unbind b
        return (subst tvar ty retType)
      _ -> throwError
        ("cannot apply "
        ++ toString t
        ++ " to type "
        ++ toString ty
        ++ ": it has type "
        ++ toString tty
        )
  check (FMatch returnType t rules) = do
    tty <- check t
    tys <- checkRules sigma alphas delta gamma tty returnType rules
    return returnType

checkRules
  :: (Fresh m, MonadError String m)
  => Sigma
  -> Alphas
  -> Delta
  -> Gamma
  -> Type
  -> Type
  -> FRules
  -> m ()
checkRules sigma alphas delta gamma patternType expectedType rules =
  mapM_ (checkRule sigma alphas delta gamma patternType expectedType) rules

checkRule
  :: (Fresh m, MonadError String m)
  => Sigma
  -> Alphas
  -> Delta
  -> Gamma
  -> Type
  -> Type
  -> FRule
  -> m ()
checkRule sigma alphas delta gamma patternType expectedType (FRule b) = do
  (p, t) <- unbind b
  (alphas', delta', gamma') <- typeCheckPattern sigma alphas p patternType
  inferredType <- typeCheckFTerm sigma (alphas ++ alphas') (delta ++ delta') (gamma ++ gamma') t
  checkEqTypes (alphas'++alphas) (delta'++delta) inferredType expectedType

typeCheckPattern
  :: (Fresh m, MonadError String m)
  => Sigma
  -> Alphas
  -> FPattern
  -> Type
  -> m (Alphas, Delta, Gamma)
typeCheckPattern sigma alphas = check
 where
  check (FPVar x) ty = do
    checkKind alphas ty KType
    return ([], [], [(x, ty)])
  check (FPCons (unembed->con) tvars ps) ty = do
    bsig <- lookupDataCon sigma con
    (sigTvars, (sigDelta, sigTys, sigReturnType)) <- unbind bsig
    case sigReturnType of
      TCons sigCon sigTyArgs -> do
        when
          (length sigTvars < length tvars)
          (throwError (show con ++ " is applied to too many type arguments"))
        when
          (length sigTvars > length tvars)
          (throwError (show con ++ " is not applied to enough type arguments"))
        when (length sigTys < length ps)
             (throwError (show con ++ " is applied to too many arguments"))
        when (length sigTys > length ps)
             (throwError (show con ++ " is not applied to enough arguments"))
        (concat->alphas', concat->deltas', concat->gammas') <-
          unzip3
            <$> zipWithM (typeCheckPattern sigma (tvars ++ alphas)) ps sigTys
        return
          ( tvars ++ alphas' ++ alphas
          , (ty :~: sigReturnType) : deltas'
          , gammas'
          )
      _ -> throwError
        ("pattern return type "
        ++ toString sigReturnType
        ++ " is not a type constructor application")

checkDef
  :: (MonadError String m, Fresh m)
  => Sigma
  -> Alphas
  -> Delta
  -> Gamma
  -> (Name FTerm, Type, FTerm)
  -> m ()
checkDef sigma alphas delta gamma (x, ty, t) = do
  ty' <- typeCheckFTerm sigma alphas delta gamma t
  eq <- entails alphas delta ty ty'
  if eq
    then return ()
    else throwError
      (show x
      ++ " does not have type "
      ++ toString ty
      ++ ", it has type "
      ++ toString ty'
      )

checkEqTypes
  :: (MonadError String m, Fresh m) => Alphas -> Delta -> Type -> Type -> m ()
checkEqTypes alphas delta ty1 ty2 = do
  eq <- entails alphas delta ty1 ty2
  if eq
    then return ()
    else throwError
      ("type "
      ++ toString ty1
      ++ " is not equal to "
      ++ toString ty2
      ++ " under the assumptions "
      ++ show delta
      )

checkEntailsAll
  :: (MonadError String m, Fresh m) => Alphas -> Delta -> Delta -> m ()
checkEntailsAll alphas delta1 delta2 = do
  ok <- entailsAll alphas delta1 delta2
  if ok
    then return ()
    else throwError (show delta1 ++ " does not entail " ++ show delta2)

lookupDataCon
  :: MonadError String m => Sigma -> Name DataCon -> m DataConSignature
lookupDataCon sigma con = maybe
  (throwError $ "data constructor " ++ show con ++ " not found")
  return
  (lookup con sigma)

lookupType
  :: MonadError String m => Gamma -> Name FTerm -> m Type
lookupType gamma x = maybe
  (throwError $ show x ++ " not found")
  return
  (lookup x gamma)


entailsAll :: Fresh m => Alphas -> Delta -> Delta -> m Bool
entailsAll alphas delta delta' = allM entailsConstraint delta'
 where
  entailsConstraint (ty1 :~: ty2) = entails alphas delta ty1 ty2

entails :: Fresh m => Alphas -> Delta -> Type -> Type -> m Bool
entails alphas delta ty1 ty2 | any conflict delta = return True
                             | any occurCheck delta = return True
                             | otherwise = entails' alphas delta ty1 ty2
 where
  conflict (TCons tyc1 _ :~: TCons tyc2 _) = not (tyc1 `aeq` tyc2)
  conflict _ = False

  occurCheck (TVar a :~: ty) | not (isTVar ty) && a `elem` U.toListOf fv ty =
    True
  occurCheck (ty :~: TVar a) = occurCheck (TVar a :~: ty)
  occurCheck _ = False

  isTVar (TVar _) = True
  isTVar _ = False

  entails' :: Fresh m => Alphas -> Delta -> Type -> Type -> m Bool
  entails' alphas [] ty1 ty2 | aeq ty1 ty2 = return (kindCheck alphas ty1 KType)
  entails' alphas (TVar a :~: TVar b : delta) ty1 ty2 | a == b =
    entails' alphas delta ty1 ty2
  -- we know that ty does not contain a by IH
  entails' alphas (TVar a :~: ty : delta) ty1 ty2 =
    entails alphas (subst a ty delta) (subst a ty ty1) (subst a ty ty2)
  -- we know that ty does not contain a by IH
  entails' alphas (ty :~: TVar a : delta) ty1 ty2 =
    entails alphas (subst a ty delta) (subst a ty ty1) (subst a ty ty2)
  -- we know that tyc1 == tyc2 by IH
  entails' alphas (TCons tyc1 ts1 :~: TCons tyc2 ts2 : delta) ty1 ty2 = assert
    (tyc1 == tyc2)
    (entails alphas delta' ty1 ty2)
    where delta' = (zipWith (:~:) ts1 ts2) ++ delta
  entails' alphas (TForall b1 :~: TForall b2 : delta) ty1 ty2 = do
    tyc <- fresh (string2Name "C")
    let ty = TCons tyc (map TVar alphas)
    (a1, u1) <- unbind b1
    (a2, u2) <- unbind b2
    entails alphas (subst a1 ty u1 :~: subst a2 ty u2 : delta) ty1 ty2
  entails' _ _ _ _ = return False

kindCheck :: Alphas -> Type -> Kind -> Bool
kindCheck _ _ _ = True

checkKind :: MonadError String m => Alphas -> Type -> Kind -> m ()
checkKind alphas ty k =
  if kindCheck alphas ty k
    then return ()
    else throwError ("type " ++ toString ty ++ " does not have kind " ++ show k)

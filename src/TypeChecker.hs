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
import qualified Data.Map as M

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
typeCheckFTerm sigma alphas delta gamma t = checkNf t
 where
  checkNf t = do
    mgu <- unify alphas delta
    ty <- check t
    return (substs mgu ty)

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
    mgu <- unify alphas delta
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
    let sub = zip tvars (substs mgu tys)
        constraints' = substs sub constraints
        argTypes' = substs sub argTypes
        returnType' = substs sub returnType
    tsTypes <- mapM checkNf ts
    checkEqTypesAll alphas delta constraints'
    zipWithM_ (checkEqTypes alphas delta) tsTypes argTypes'
    return returnType'
  check (FApp t1 t2) = do
    ty1 <- checkNf t1
    ty2 <- checkNf t2
    sigma <- unify alphas delta
    case ty1 of
      TCons con [u1, u2] | con == string2Name "->" -> do
        checkEqTypes alphas delta u1 ty2
        return u2
      _ -> throwError
        (toString t1
        ++ " cannot be applied: it has type "
        ++ toString ty1
        ++ " under the assumptions "
        ++ show delta
        )
  check (FTApp t ty) = do
    checkKind alphas ty KType
    tty <- checkNf t
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
    tty <- checkNf t
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
  inferredType <- typeCheckFTerm sigma (alphas'++ alphas) (delta' ++ delta) (gamma' ++ gamma) t
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
  checkEqTypes alphas delta ty ty'

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


checkEqTypesAll :: (MonadError String m, Fresh m) => Alphas -> Delta -> Delta -> m ()
checkEqTypesAll alphas delta delta' = mapM_ entailsConstraint delta'
 where
  entailsConstraint (ty1 :~: ty2) = checkEqTypes alphas delta ty1 ty2

checkEqTypes :: (MonadError String m, Fresh m) => Alphas -> Delta -> Type -> Type -> m ()
checkEqTypes alphas delta ty1 ty2 = do
  mgu <- unify alphas delta
  if aeq (substs mgu ty1) (substs mgu ty2)
    then return ()
    else throwError ("constraints " ++ show delta ++ " do not imply " ++ show (ty1 :~: ty2))

unify
  :: (MonadError String m, Fresh m) => Alphas -> Delta -> m [(Name Type, Type)]
unify alphas delta = M.toList <$> unify' M.empty delta
 where
  throwCannotUnify s = throwError (s ++ ": cannot unify " ++ show delta)

  unify' s [] = return s
  unify' s (ty1 :~: ty2 : delta) = unify'' s (apply s ty1) (apply s ty2) delta

  unify'' s (TVar a) (TVar b) delta
    | a == b = unify' s delta
    | a < b = unify' (extend s b (TVar a)) delta
    | otherwise = unify' (extend s a (TVar b)) delta
  unify'' s (TVar a) ty delta
    | a `notElem` U.toListOf fv ty = unify' (extend s a ty) delta
    | otherwise = throwCannotUnify "occur check"
  unify'' s ty (TVar a) delta = unify'' s (TVar a) ty delta
  unify'' s (TCons c1 tys1) (TCons c2 tys2) delta
    | c1 == c2 && length tys1 == length tys2 = unify' s (zipWith (:~:) tys1 tys2 ++ delta)
    | otherwise = throwCannotUnify "conflict"
  unify'' s (TForall b1) (TForall b2) delta = do
    con <- fresh (string2Name "C")
    let ty = TCons con (map TVar alphas)
    (a1, u1) <- unbind b1
    (a2, u2) <- unbind b2
    unify' s (subst a1 ty u1 :~: subst a2 ty u2 : delta)

  extend s a ty = M.insert a ty (M.map (subst a ty) s)

  apply s x = substs (M.toList s) x


kindCheck :: Alphas -> Type -> Kind -> Bool
kindCheck _ _ _ = True

checkKind :: MonadError String m => Alphas -> Type -> Kind -> m ()
checkKind alphas ty k =
  if kindCheck alphas ty k
    then return ()
    else throwError ("type " ++ toString ty ++ " does not have kind " ++ show k)

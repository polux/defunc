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
import Control.Monad.Except
import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Internal.Fold as U
import Control.Exception.Base (assert)
import Control.Monad.Loops (allM)

type DataConSignature = Bind Alphas (Delta, [Type], Type)
type Sigma = [(Name DataCon, DataConSignature)]
type Delta = [Constraint]
type Alphas = [Name Type]
type Gamma = [(Name FTerm, Type)]

typeCheck :: MonadError String m => FProgram -> m Type
typeCheck prog = throwError "type checking not yet implemented"

typeCheckFTerm
  :: MonadError String m => Sigma -> Alphas -> Delta -> Gamma -> FTerm -> m Type
typeCheckFTerm sigma alphas delta gamma _ = undefined

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

extractSigma :: [TypeDecl] -> Sigma
extractSigma decls = concatMap extract decls
  where
    extract (TypeDecl _ _ decls) = map break decls
    break (DataConDecl conName sig) = (conName, unembed sig)

entailsAll :: Fresh m => Alphas -> Delta -> [Constraint] -> m Bool
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

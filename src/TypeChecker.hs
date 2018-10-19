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

typeCheck :: MonadError String m => FProgram -> m Type
typeCheck prog = throwError "type checking not yet implemented"

entails :: Fresh m => [Constraint] -> Constraint -> m Bool
entails delta eq
  | any conflict delta = return True
  | any occurCheck delta = return True
  | otherwise = entails' delta eq

 where
   conflict (TCons tyc1 _ :~: TCons tyc2 _) = not (tyc1 `aeq` tyc2)
   conflict _ = False

   occurCheck (TVar a :~: ty) | not (isTVar ty) && a `elem` U.toListOf fv ty = True
   occurCheck (ty :~: TVar a) | not (isTVar ty) && a `elem` U.toListOf fv ty = True
   occurCheck _ = False

   isTVar (TVar _) = True
   isTVar _ = False

entails' [] (a :~: b) | aeq a b = return True
entails' (TVar a :~: TVar b : delta) eq | a == b = entails' delta eq
entails' (TVar a :~: ty : delta) eq =
  -- we know that ty does not contain a by IH
  entails (subst a ty delta) (subst a ty eq)
entails' (ty :~: TVar a : delta) eq =
  -- we know that ty does not contain a by IH
  entails (subst a ty delta) (subst a ty eq)
entails' (TCons tyc1 ts1 :~: TCons tyc2 ts2 : delta) eq =
  -- we know that tyc1 == tyc2 by IH
  assert (tyc1 == tyc2) (entails delta' eq)
 where delta' = (zipWith (:~:) ts1 ts2) ++ delta
entails' (TForall b1 :~: TForall b2 : delta) eq = do
  tyc <- fresh (string2Name "C")
  let as = U.toListOf fv delta
  let ty = TCons tyc (map TVar as)
  (a1, ty1) <- unbind b1
  (a2, ty2) <- unbind b2
  entails (subst a1 ty ty1 :~: subst a2 ty ty2 : delta) eq
entails' _ _ = return False

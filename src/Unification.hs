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

module Unification (unify) where

import AST
import Pretty

import Control.Monad.Except
import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Internal.Fold as UI
import qualified Data.Map as M

unify
  :: (MonadError String m, Fresh m)
  => [Name Type]
  -> [Constraint]
  -> m [(Name Type, Type)]
unify alphas delta = M.toList <$> unify' M.empty delta
 where
  throwCannotUnify s = throwError (s ++ ": cannot unify " ++ toString delta)

  unify' s [] = return s
  unify' s (ty1 :~: ty2 : delta) = unify'' s (apply s ty1) (apply s ty2) delta

  unify'' s (TVar a) (TVar b) delta
    | a == b = unify' s delta
    | a < b = unify' (extend s b (TVar a)) delta
    | otherwise = unify' (extend s a (TVar b)) delta
  unify'' s (TVar a) ty delta
    | a `notElem` UI.toListOf fv ty = unify' (extend s a ty) delta
    | otherwise = throwCannotUnify "occur check"
  unify'' s ty (TVar a) delta = unify'' s (TVar a) ty delta
  unify'' s (TCons c1 tys1) (TCons c2 tys2) delta
    | c1 == c2 && length tys1 == length tys2 = unify'
      s
      (zipWith (:~:) tys1 tys2 ++ delta)
    | otherwise = throwCannotUnify "conflict"
  unify'' s (TForall b1) (TForall b2) delta = do
    con <- fresh (string2Name "C")
    let ty = TCons con (map TVar alphas)
    (a1, u1) <- unbind b1
    (a2, u2) <- unbind b2
    unify' s (subst a1 ty u1 :~: subst a2 ty u2 : delta)

  extend s a ty = M.insert a ty (M.map (subst a ty) s)

  apply s x = substs (M.toList s) x


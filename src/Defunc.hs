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

module Defunc (defunctionalize) where

import AST
import Control.Monad.State
import Control.Monad.Writer
import Data.List ((\\))
import Unbound.Generics.LocallyNameless
import qualified Data.Set as S
import qualified Unbound.Generics.LocallyNameless.Internal.Fold as U

defunctionalize :: FunDefs -> FunDefs
defunctionalize (FunDefs b) =
  runFreshM $ do
    (fs, (ts, t)) <- unbind b
    a <- fresh (string2Name "apply")
    (t':ts', rules) <- defunc fs a (t:ts)
    at <- mkApply rules
    return $ FunDefs (bind (a:fs) (at:ts', t'))
 where
  mkApply rules = do
    x <- fresh (string2Name "x")
    return $ lam x (Match (Var x) rules)

defunc :: Fresh m => [Name Term] -> Name Term -> [Term] -> m ([Term], Rules)
defunc fs a ts = evalStateT (runWriterT (mapM (defuncTerm fs a) ts)) 0

freshConstructorName :: MonadState Int m => m String
freshConstructorName = do
  n <- get
  put (n+1)
  return $ "Clos" ++ show n

freeNames :: Term -> [Name Term]
freeNames t = S.toList (S.fromList (U.toListOf fv t))

defuncTerm
  :: (Fresh m, MonadState Int m, MonadWriter Rules m)
  => [Name Term]
  -> Name Term
  -> Term
  -> m Term
defuncTerm fs apply term = go term
 where
  go t@(Var _) = return t
  go t@(Lit _) = return t
  go (App t0 t1) = do
    t0' <- go t0
    t1' <- go t1
    return $ Var apply @: pair t0' t1'
  go t@(Lam b) = do
    (p, e) <- unbind b
    c <- freshConstructorName
    e' <- go e
    let fns = freeNames t \\ fs
    let pclos = PCons c (map PVar fns)
    tell [Rule $ bind (ppair pclos p) e']
    return $ Cons c (map Var fns)
  go (Let b t) = do
    (p, u) <- unbind b
    t' <- go t
    u' <- go u
    return $ Let (bind p u') t'
  go (Cons c ts) = do
    ts' <- mapM go ts
    return $ Cons c ts'
  go (Match t rs) = do
    t' <- go t
    rs' <- mapM (defuncRule fs apply) rs
    return (Match t' rs')

defuncRule fs apply (Rule b) = do
  (p, t) <- unbind b
  t' <- defuncTerm fs apply t
  return (Rule (bind p t'))


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
import Data.List ((\\), foldl')
import Unbound.Generics.LocallyNameless
import qualified Data.Set as S
import qualified Unbound.Generics.LocallyNameless.Internal.Fold as U
import qualified Data.Map as M
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

fixM f t = do
  t' <- f t
  if aeq t t'
    then return t
    else fixM f t'

defunctionalize :: FunDefs -> FunDefs
defunctionalize (FunDefs b) =
  runFreshM $ do
    (fs, (ts, t)) <- unbind b
    a <- fresh (string2Name "apply")
    let step (u:us) = mapM (saturate (arities (zip fs us))) (u:us)
    (t':ts') <- fixM step (t:ts)
    (t'':ts'', rules) <- defunc (arities (zip fs ts')) a (t':ts')
    at <- mkApply rules
    return $ FunDefs (bind (a:fs) (at:ts'', t''))
 where
  mkApply rules = do
    x <- fresh (string2Name "x")
    return $ lam x (Match (Var x) rules)

type Arities = M.Map (Name Term) Int

arities :: [(Name Term, Term)] -> Arities
arities fs = M.fromList [(f, arity t) | (f, t) <- fs]
  where arity (Lam b) = let (_, t) = unsafeUnbind b in 1 + arity t
        arity _ = 0

etaExpand :: Fresh m => Term -> Int -> m Term
etaExpand t n = do
  xs <- replicateM n (fresh (string2Name "x"))
  return (foldr plam (app t (map Var xs)) (map PVar xs))

saturate :: Fresh m => Arities -> Term -> m Term
saturate fs t = go t
  where
    go t | (Var f, ts) <- unApp t, (Just n) <- M.lookup f fs =
      if (length ts < n)
        then do
          ts' <- mapM go ts
          etaExpand (app (Var f) ts') (n - length ts)
        else app (Var f) <$> mapM go ts
    go x@(Var _) = return x
    go (App t u) = App <$> go t <*> go u
    go (Lam b) = do
      (p, t) <- unbind b
      t' <- go t
      return (plam p t')
    go (Let b t) = do
      (p, u) <- unbind b
      u' <- go u
      t' <- go t
      return (Let (bind p u') t)
    go l@(Lit _) = return l
    go (Cons f ts) = Cons f <$> mapM go ts
    go (Match t rs) = Match <$> go t <*> mapM goRule rs

    goRule (Rule b) = do
      (p, t) <- unbind b
      t' <- go t
      return (Rule (bind p t))


defunc :: Fresh m => Arities -> Name Term -> [Term] -> m ([Term], Rules)
defunc fs a ts = evalStateT (runWriterT (mapM (defuncFun fs a) ts)) 0

freshConstructorName :: MonadState Int m => m String
freshConstructorName = do
  n <- get
  put (n+1)
  return $ "Clos" ++ show n

freeNames :: Term -> [Name Term]
freeNames t = S.toList (S.fromList (U.toListOf fv t))

defuncFun
  :: (Fresh m, MonadState Int m, MonadWriter Rules m)
  => Arities
  -> Name Term
  -> Term
  -> m Term
defuncFun fs a (Lam b) = do
  (x, t) <- unbind b
  t' <- defuncFun fs a t
  return (plam x t')
defuncFun fs a t  = defuncTerm fs a t

defuncTerm
  :: (Fresh m, MonadState Int m, MonadWriter Rules m)
  => Arities
  -> Name Term
  -> Term
  -> m Term
defuncTerm fs apply term = go term
 where
  go t@(Var _) = return t
  go t@(Lit _) = return t
  go t | (Var f, ts) <- unApp t, (Just n) <- M.lookup f fs =
    if (length ts < n)
      then error ("toplevel function application not saturated: " ++ show t)
      else do
        let (args, extraArgs) = splitAt n ts
        u <- app (Var f) <$> mapM go args
        return $ foldl' mkApply u extraArgs
  go (App t0 t1) = do
    t0' <- go t0
    t1' <- go t1
    return $ mkApply t0' t1'
  go t@(Lam b) = do
    (p, e) <- unbind b
    c <- freshConstructorName
    e' <- go e
    let fns = freeNames t \\ M.keys fs
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

  mkApply a b = Var apply @: pair a b

defuncRule fs apply (Rule b) = do
  (p, t) <- unbind b
  t' <- defuncTerm fs apply t
  return (Rule (bind p t'))


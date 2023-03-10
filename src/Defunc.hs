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

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Fuse foldr/map" #-}
{-# HLINT ignore "Eta reduce" #-}

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
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Safe (maximumDef)

defunctionalize :: FunDefs -> FunDefs
defunctionalize defs = go (saturateFunDefs defs)
 where
  go defs =
    runFreshM $ do
      (eqs, t) <- unmakeFunDefs defs
      let (fs, ts) = unzip eqs
      applyName <- fresh (string2Name "apply")
      argName <- fresh (string2Name "x")
      tsrules <- defunc (arities eqs) applyName argName (t:ts)
      let (t':ts', rules) = tsrules
      applyTerm <- mkApplyFunction argName (S.toList rules)
      return $ makeFunDefs (zip (applyName:fs) (applyTerm:ts')) t'
  mkApplyFunction arg rules = do
    f <- fresh (string2Name "f")
    return $ plam (ppair (PVar f) (PVar arg)) (Match (Var f) rules)

type Arities = M.Map (Name Term) Int

saturateFunDefs defs = converge go defs
 where
  go defs = runFreshM $ do
    (eqs, t) <- unmakeFunDefs defs
    let ar = arities eqs
        (fs, ts) = unzip eqs
    ts' <- mapM (saturate ar) ts
    t' <- saturate ar t
    return $ makeFunDefs (zip fs ts') t'
  converge f t = if aeq t t' then t else converge f t'
    where t' = f t

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
      if length ts < n
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
    go (Let b) = do
      ((p, t), u) <- unbind b
      u' <- go u
      t' <- go (unembed t)
      return (Let (bind (p, embed t') u'))
    go l@(Lit _) = return l
    go (Cons f ts) = Cons f <$> mapM go ts
    go (Match t rs) = Match <$> go t <*> mapM goRule rs

    goRule (Rule b) = do
      (p, t) <- unbind b
      t' <- go t
      return (Rule (bind p t))

newtype PreRule = PreRule (Bind ([Name Term], Pattern) Term)
  deriving (Show, Generic, Typeable)

instance Alpha PreRule

instance Eq PreRule where
  (==) = aeq

instance Ord PreRule where
  compare = acompare

type PreRules = M.Map PreRule Int

defunc :: Fresh m => Arities -> Name Term -> Name Term -> [Term] -> m ([Term], S.Set Rule)
defunc fs apply arg ts = evalStateT (runWriterT (mapM (defuncFun fs apply arg) ts)) M.empty

getConstructorName :: MonadState PreRules m => PreRule -> m String
getConstructorName pr = fmap mkName $ do
  prs <- get
  case M.lookup pr prs of
    Just n -> return n
    Nothing -> do
      let n = maximumDef 0 (M.elems prs) + 1
      put (M.insert pr n prs)
      return n
  where mkName n = "C" ++ show n

freeNames :: Term -> [Name Term]
freeNames t = S.toList (S.fromList (U.toListOf fv t))

defuncFun
  :: (Fresh m, MonadState PreRules m, MonadWriter (S.Set Rule) m)
  => Arities
  -> Name Term
  -> Name Term
  -> Term
  -> m Term
defuncFun fs apply arg (Lam b) = do
  (x, t) <- unbind b
  t' <- defuncFun fs apply arg t
  return (plam x t')
defuncFun fs apply arg t  = defuncTerm fs apply arg t

defuncTerm
  :: (Fresh m, MonadState PreRules m, MonadWriter (S.Set Rule) m)
  => Arities
  -> Name Term
  -> Name Term
  -> Term
  -> m Term
defuncTerm fs apply arg term = go term
 where
  go t@(Var _) = return t
  go t@(Lit _) = return t
  go t | (Var f, ts) <- unApp t, (Just n) <- M.lookup f fs =
    if length ts < n
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
    e' <- go e
    let fns = freeNames t \\ M.keys fs
    let pr = PreRule (bind (fns, p) e')
    c <- getConstructorName pr
    let pclos = PCons c (map PVar fns)
    let rhs = case p of
                (PVar x) -> subst x (Var arg) e'
                _ -> Let (bind (p, embed (Var arg)) e')
    tell (S.singleton (Rule $ bind pclos rhs))
    return $ Cons c (map Var fns)
  go (Let b) = do
    ((p, t), u) <- unbind b
    t' <- go (unembed t)
    u' <- go u
    return $ Let (bind (p, embed t') u')
  go (Cons c ts) = do
    ts' <- mapM go ts
    return $ Cons c ts'
  go (Match t rs) = do
    t' <- go t
    rs' <- mapM (defuncRule fs apply arg) rs
    return (Match t' rs')

  mkApply a b = Var apply @: pair a b

defuncRule fs apply arg (Rule b) = do
  (p, t) <- unbind b
  t' <- defuncTerm fs apply arg t
  return (Rule (bind p t'))


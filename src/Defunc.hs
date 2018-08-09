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

fixM f t = do
  t' <- f t
  if aeq t t'
    then return t
    else fixM f t'

defunctionalize :: FunDefs -> FunDefs
defunctionalize (FunDefs b) =
  runFreshM $ do
    (fs, (ts, t)) <- unbind b
    apply <- fresh (string2Name "apply")
    arg <- fresh (string2Name "x")
    let step (u:us) = mapM (saturate (arities (zip fs us))) (u:us)
    (t':ts') <- fixM step (t:ts)
    (t'':ts'', rules) <- defunc (arities (zip fs ts')) apply arg (t':ts')
    at <- mkApply arg (S.toList rules)
    return $ FunDefs (bind (apply:fs) (at:ts'', t''))
 where
  mkApply arg rules = do
    f <- fresh (string2Name "f")
    return $ plam (ppair (PVar f) (PVar arg)) (Match (Var f) rules)

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

data PreRule = PreRule (Bind ([Name Term], Pattern) Term)
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
  where mkName n = "Clos" ++ show n

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
    e' <- go e
    let fns = freeNames t \\ M.keys fs
    let pr = PreRule (bind (fns, p) e')
    c <- getConstructorName pr
    let pclos = PCons c (map PVar fns)
    let rhs = case p of
                (PVar x) -> subst x (Var arg) e'
                _ -> Let (bind p e') (Var arg)
    tell (S.singleton (Rule $ bind pclos rhs))
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
    rs' <- mapM (defuncRule fs apply arg) rs
    return (Match t' rs')

  mkApply a b = Var apply @: pair a b

defuncRule fs apply arg (Rule b) = do
  (p, t) <- unbind b
  t' <- defuncTerm fs apply arg t
  return (Rule (bind p t'))


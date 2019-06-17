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

module CPS (cps) where

import AST
import Unbound.Generics.LocallyNameless

cps :: Program -> Program
cps (Program b) = runFreshM $ do
  (decls, defs) <- unbind b
  defs' <- fundefsCps defs
  return (Program (bind decls defs'))

fundefsCps :: Fresh m => FunDefs -> m FunDefs
fundefsCps defs = do
  (eqs, t) <- unmakeFunDefs defs
  let (fs, ts) = unzip eqs
  ts' <- mapM rhsCps ts
  idFun <- mkId
  t' <- eCps t idFun
  return $ makeFunDefs (zip fs ts') t'
 where
  mkId = do
    x <- fresh (string2Name "x")
    return $ lam x (Var x)

rhsCps t | serious t = termCps t
         | otherwise = tCps t

termCps t = do
  k <- fresh (string2Name "k")
  t' <- eCps t (Var k)
  return (lam k t')

serious (App _ _) = True
serious (Let _) = True
serious (Match _ _) = True
serious (Cons _ ts) = any serious ts
serious _ = False

comps :: Fresh m => Term -> m ([(Name Term, Term)], Term)
comps t
  | (Cons c us) <- t = do
      (cs, us') <- comps' us
      return (cs, Cons c us')
  | serious t = do
      x <- fresh (string2Name "x")
      return ([(x, t)], Var x)
  | otherwise = do
      t' <- tCps t
      return ([], t')

comps' :: Fresh m => [Term] -> m ([(Name Term, Term)], [Term])
comps' ts = do
  (css, ts') <- unzip <$> mapM comps ts
  return (concat css, ts')

eCps t k
  | serious t = sCps t k
  | otherwise = do
      t' <- tCps t
      return (k @: t')

cCps [] t = return t
cCps ((x,s):ts) t = do
  t' <- cCps ts t
  sCps s (lam x t')

rCps (Rule b) k = do
  (p, t) <- unbind b
  t' <- eCps t k
  return (Rule (bind p t'))

sCps (Match t rs) k
  | serious t = do
      x <- fresh (string2Name "x")
      rs' <- mapM (flip rCps k) rs
      sCps t (lam x (Match (Var x) rs'))
  | otherwise = do
      rs' <- mapM (flip rCps k) rs
      t' <- tCps t
      return (Match t' rs')
sCps t@(Cons _ _) k = do
  (cs, t) <- comps t
  cCps cs (k @: t)
sCps (Let b) k = do
  ((p, t), u) <- unbind b
  u' <- eCps u k
  eCps (unembed t) (plam p u')
sCps (App t0 t1) k
  | serious t0 && serious t1 = do
      x0 <- fresh (string2Name "x")
      t1' <- case t1 of
        Cons _ _ -> do
          (cs, ct) <- comps t1
          cCps cs (Var x0 @: pair ct k)
        _ -> do
          x1 <- fresh (string2Name "y")
          sCps t1 (lam x1 (Var x0 @: pair (Var x1) k))
      sCps t0 (lam x0 t1')
  | serious t1 = do
      t0' <- tCps t0
      case t1 of
        Cons _ _ -> do
          (cs, ct) <- comps t1
          cCps cs (t0' @: pair ct k)
        _ -> do
          x1 <- fresh (string2Name "y")
          sCps t1 (lam x1 (t0' @: pair (Var x1) k))
  | serious t0 = do
      x0 <- fresh (string2Name "x")
      t1' <- tCps t1
      sCps t0 (lam x0 (Var x0 @: pair t1' k))
  | otherwise = do
      t0' <- tCps t0
      t1' <- tCps t1
      return (t0' @: pair t1' k)

tCps (Lam b) = do
  k <- fresh (string2Name "k")
  (p, e) <- unbind b
  e' <- eCps e (Var k)
  return (plam (ppair p (PVar k)) e')
tCps (Cons c ts) = do
  ts' <- mapM tCps ts
  return (Cons c ts')
tCps x = return x


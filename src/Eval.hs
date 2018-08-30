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

{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleContexts #-}

module Eval(Val(..), eval) where

import AST
import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M

eval :: FunDefs -> Either String Val
eval defs = runFreshM . runExceptT $ mdo
  (eqs, t) <- unmakeFunDefs defs
  let (fs, ts) = unzip eqs
  env <- do
    tsv <- mapM (evalTermWith env) ts
    return $ zip fs (map embed tsv)
  evalTermWith env t

match :: MonadError String m => Pattern -> Val -> m Env
match p v =
  case match' p v of
    Nothing -> throwError ("cannot match " ++ show v ++ " with " ++ show p)
    Just env -> return env

match' :: Pattern -> Val -> Maybe Env
match' (PCons c ps) (VCons c' vs)
  | c == c' = concat <$> zipWithM match' ps vs
  | otherwise = Nothing
match' (PLit i) (VInt j)
  | i == j = Just []
  | otherwise = Nothing
match' (PVar x) v = Just [(x, embed v)]
match' _ _ = Nothing

evalTermWith :: (Fresh m, MonadError String m) => Env -> Term -> m Val
evalTermWith env t = runReaderT (evalTerm t) env

evalTerm :: (Fresh m, MonadError String m, MonadReader Env m) => Term -> m Val
evalTerm (Lit i) = return (VInt i)
evalTerm (Cons c ts) = do
  vts <- mapM evalTerm ts
  return (VCons c vts)
evalTerm (Var x) = do
  env <- ask
  case lookup x env of
    Just v -> return (unembed v)
    Nothing ->
      throwError ("cannot find " ++ show x ++ " in " ++ show (map fst env))
evalTerm t@(Lam b) = do
  env <- ask
  return (VClosure (bind env t))
evalTerm (App f t) = do
  vf <- evalTerm f
  vt <- evalTerm t
  case vf of
    VClosure b -> do
      (env, Lam b') <- unbind b
      (p, u) <- unbind b'
      env' <- match p vt
      local (const (env' ++ env)) (evalTerm u)
    _ -> throwError ("cannot apply " ++ show vf ++ " to " ++ show vt)
evalTerm (Let b) = do
  ((p, t), u) <- unbind b
  vt <- evalTerm (unembed t)
  env <- match p vt
  local (env++) (evalTerm u)
evalTerm (Match t rs) = do
  vt <- evalTerm t
  vs <- mapM (evalRule vt) rs
  case msum vs of
    Nothing -> throwError ("none of " ++ show rs ++ " matches " ++ show vt)
    Just v -> return v

evalRule
  :: (Fresh m, MonadReader Env m, MonadError String m)
  => Val
  -> Rule
  -> m (Maybe Val)
evalRule v (Rule b) = do
  (p, t) <- unbind b
  case match' p v of
    Just env -> Just <$> local (env++) (evalTerm t)
    Nothing -> return Nothing


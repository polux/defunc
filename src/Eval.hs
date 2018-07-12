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
import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad.Reader

data Val
  = VInt Int
  | VCons String [Val]
  | VClosure Term Env
  deriving Show

type Env = M.Map (Name Term) Val

eval :: FunDefs -> Either String Val
eval (FunDefs b) = runFreshM . runExceptT $ mdo
  (fs, (ts, t)) <- unbind b
  env <- do
    tsv <- mapM (evalTermWith env) ts
    return $ M.fromList (zip fs tsv)
  evalTermWith env t

match :: MonadError String m => Pattern -> Val -> m Env
match p v =
  case match' p v of
    Nothing -> throwError ("cannot match " ++ show v ++ " with " ++ show p)
    Just env -> return env

match' :: Pattern -> Val -> Maybe Env
match' (PCons c ps) (VCons c' vs)
  | c == c' = M.unions <$> zipWithM match' ps vs
  | otherwise = Nothing
match' (PLit i) (VInt j)
  | i == j = Just M.empty
  | otherwise = Nothing
match' (PVar x) v = Just (M.singleton x v)
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
  case M.lookup x env of
    Just v -> return v
    Nothing ->
      throwError ("cannot find " ++ show x ++ " in " ++ show (M.keys env))
evalTerm t@(Lam b) = do
  env <- ask
  return (VClosure t env)
evalTerm (App f t) = do
  vf <- evalTerm f
  vt <- evalTerm t
  case vf of
    VClosure (Lam b) env -> do
      (p, u) <- unbind b
      env' <- match p vt
      local (const (M.union env env')) (evalTerm u)
    _ -> throwError ("cannot apply " ++ show vf ++ " to " ++ show vt)
evalTerm (Let b t) = do
  (p, u) <- unbind b
  vt <- evalTerm t
  env <- match p vt
  local (M.union env) (evalTerm u)
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
    Just env -> Just <$> local (M.union env) (evalTerm t)
    Nothing -> return Nothing


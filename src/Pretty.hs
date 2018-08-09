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

{-# LANGUAGE OverloadedStrings      #-}

module Pretty () where

import AST
import qualified Data.Text.Prettyprint.Doc as D
import qualified Data.Text.Prettyprint.Doc as D
import qualified Data.Map as M
import Unbound.Generics.LocallyNameless (LFresh, lunbind, runLFreshM, unembed)
import Control.Monad (zipWithM)

prettyPattern :: LFresh m => Pattern -> m (D.Doc a)
prettyPattern (PVar x) = return $ D.viaShow x
prettyPattern (PLit i) = return $ D.viaShow i
prettyPattern p@(PCons "" _) = do
  ps' <- mapM prettyPattern (peel p)
  return $ D.align (D.tupled ps')
 where
  peel (PCons "" [p1, p2]) = peel p1 ++ [p2]
  peel p = [p]
prettyPattern (PCons c ps) = do
  ps' <- mapM prettyPattern ps
  return $ D.pretty c <> D.align (D.tupled ps')

prettyFunDefs :: LFresh m => FunDefs -> m (D.Doc a)
prettyFunDefs (FunDefs b) =
  lunbind b $ \(fs, (ts, t)) -> do
    eqs <- zipWithM prettyEq fs ts
    t' <- prettyTerm False t
    return $ D.hcat [eq <> D.semi <> D.hardline <> D.hardline | eq <- eqs] <> t'
 where
  prettyEq f t = do
    t' <- prettyEq' t
    return $ D.viaShow f D.<+> t'
  prettyEq' (Lam b) =
    lunbind b $ \(p, t) -> do
      t' <- prettyEq' t
      p' <- prettyPattern p
      return $ p' D.<+> t'
  prettyEq' t = do
    t' <- prettyTerm False t
    return $ D.group $ D.nest 2 $ "=" <> D.line <> t'

instance D.Pretty FunDefs where
  pretty fs = runLFreshM (prettyFunDefs fs)

prettyTerm :: LFresh m => Bool -> Term -> m (D.Doc a)
prettyTerm par t = prettyApps par (apps t)
  where
    prettyApps :: LFresh m => Bool -> [Term] -> m (D.Doc a)
    prettyApps par [t] = prettyAtom par t
    prettyApps par ts = do
      ts' <- mapM (prettyAtom True) ts
      return $ parens par (D.group $ D.align $ D.vsep ts')

    prettyAtom :: LFresh m => Bool -> Term -> m (D.Doc a)
    prettyAtom _ (Lit i) = return (D.viaShow i)
    prettyAtom _ (Var x) = return (D.viaShow x)
    prettyAtom par (Lam b) =
      lunbind b $ \(p, t) -> do
        td <- prettyTerm False t
        p' <- prettyPattern p
        return
          $ parens par
          $ D.group
          $ D.nest 2
          $ D.vsep ["\\" <> p' D.<+> "->", td]
    prettyAtom par (Let b t) = lunbind b $ \(p, u) -> do
      t' <- prettyTerm False t
      u' <- prettyTerm False u
      p' <- prettyPattern p
      return
        $ parens par
        $ D.group
        $ D.group ("let" D.<+> p' D.<+> "=" <> D.nest 2 (D.line <> t'))
        <> D.line
        <> "in"
        <> D.nest 2 (D.line <> u')
    prettyAtom _ t@(App _ _) = D.parens <$> prettyTerm False t
    prettyAtom _ t | Just ts <- asList t = do
      ts' <- mapM (prettyTerm False) ts
      return $ D.list ts'
    prettyAtom _ t@(Cons "" _) = do
      ts' <- mapM (prettyTerm False) (peel t)
      return $ D.align (D.tupled ts')
     where
      peel (Cons "" [t1, t2]) = peel t1 ++ [t2]
      peel t = [t]
    prettyAtom _ (Cons c ts) = do
      ts' <- traverse (prettyTerm False) ts
      return $ D.pretty c <> D.align (D.tupled ts')
    prettyAtom par (Match t rs) = do
      t' <- prettyTerm False t
      rs' <- prettyRules rs
      return
        $ parens par
        $ D.group
        $ "match"
        D.<+> t'
        D.<+> "with"
        D.<> D.line
        D.<> rs'
        <> D.line
        <> "end"

    prettyRules rs = hardVsep <$> mapM prettyRule rs

    prettyRule (Rule b) =
      lunbind b $ \(p, t) -> do
        p' <- prettyPattern p
        t' <- prettyTerm False t
        return $ D.group $ D.nest 4 $ "|" D.<+> p' D.<+> "->" <> D.line <> t'

    apps :: Term -> [Term]
    apps (App t1 t2) = apps t1 ++ [t2]
    apps t = [t]

    asList :: Term -> Maybe [Term]
    asList (Cons "Nil" []) = Just []
    asList (Cons "Cons" [x, y]) = (x:) <$> asList y
    asList _ = Nothing

    parens :: Bool -> D.Doc a -> D.Doc a
    parens b d = if b then D.parens d else d

    hardVsep = D.concatWith (\x y -> x <> D.hardline <> y)

instance D.Pretty Term where
  pretty t = runLFreshM (prettyTerm False t)

prettyVal :: LFresh m => Val -> m (D.Doc a)
prettyVal t | Just ts <- asList t = do
  ts' <- mapM prettyVal ts
  return $ D.list ts'
 where
  asList (VCons "Nil" []) = Just []
  asList (VCons "Cons" [x, y]) = (x:) <$> asList y
  asList _ = Nothing
prettyVal t@(VCons "" _) = do
  ts' <- mapM prettyVal (peel t)
  return $ D.align (D.tupled ts')
 where
  peel (VCons "" [t1, t2]) = peel t1 ++ [t2]
  peel t = [t]
prettyVal (VCons c ts) = do
  ts' <- traverse prettyVal ts
  return $ D.pretty c <> D.align (D.tupled ts')
prettyVal (VInt i) = return (D.viaShow i)
prettyVal (VClosure b) =
  lunbind b $ \(env, t) -> do
    t' <- prettyTerm False t
    return $ D.encloseSep (D.flatAlt "< " "<")
                          (D.flatAlt " >" ">")
                          (D.flatAlt "," ", ")
                          [t', prettyEnv env]

prettyEnv :: Env -> D.Doc a
prettyEnv env =
  D.list [ D.tupled [D.viaShow x, D.pretty (unembed v)] | (x, v) <- env ]

instance D.Pretty Val where
  pretty t = runLFreshM (prettyVal t)


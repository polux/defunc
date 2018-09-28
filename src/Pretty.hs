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
{-# LANGUAGE TypeFamilies #-}

module Pretty () where

import AST
import qualified Data.Text.Prettyprint.Doc as D
import qualified Data.Text.Prettyprint.Doc as D
import qualified Data.Map as M
import Unbound.Generics.LocallyNameless (string2Name, Name, unrec, LFresh, lunbind, runLFreshM, unembed)
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
  lunbind b $ \(eqs, t) -> do
    eqs' <- mapM prettyEq (unrec eqs)
    t' <- prettyTerm False t
    return $ D.hcat [eq <> D.semi <> D.hardline | eq <- eqs'] <> t'
 where
  prettyEq (f, t) = do
    t' <- prettyEq' (unembed t)
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
    prettyAtom par (Let b) = lunbind b $ \((p, t), u) -> do
      t' <- prettyTerm False (unembed t)
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

    prettyRules :: LFresh m => [Rule] -> m (D.Doc a)
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

prettyKind :: Bool -> Kind -> D.Doc a
prettyKind _ KType = "Type"
prettyKind par (KArrow ks k) =
  parens par
    $ D.align (sepByStar (map (prettyKind True) ks))
    D.<+> "->"
    D.<+> prettyKind False k
  where sepByStar = D.encloseSep mempty mempty " * "

prettyType :: LFresh m => Name TyCon -> Bool -> Type -> m (D.Doc a)
prettyType arName par ty = prettyArrows par (arrows ty)
  where
    prettyArrows :: LFresh m => Bool -> [Type] -> m (D.Doc a)
    prettyArrows par [ty] = prettyAtom par ty
    prettyArrows par (ty:tys) = do
      ty' <- prettyAtom True ty
      tys' <- mapM (prettyAtom True) tys
      return $ parens par (D.group $ D.align $ D.sep $ ty' : map ("->" D.<+>) tys')

    prettyAtom :: LFresh m => Bool -> Type -> m (D.Doc a)
    prettyAtom _ (TVar x) = return $ D.viaShow x
    prettyAtom _ TUnit = return "Unit"
    prettyAtom _ ty@(TCons c tys) | c == arName = D.parens <$> prettyType arName False ty
    prettyAtom _ (TCons c tys)
      | null tys = return (D.viaShow c)
      | otherwise = do
        tys' <- mapM (prettyType arName False) tys
        return $ D.viaShow c D.<> D.align (D.list tys')
    prettyAtom par (TForall b) =
      lunbind b $ \(x, ty) -> do
        ty' <- prettyType arName False ty
        return $ parens par $ "forall" D.<+> D.viaShow x D.<+> "." D.<+> ty'

    arrows (TCons c [ty1, ty2]) | c == arName = ty1 : arrows ty2
    arrows ty = [ty]

instance D.Pretty Type where
  pretty t = runLFreshM (prettyType (string2Name "->") False t)

prettyFPattern :: FPattern -> D.Doc a
prettyFPattern (FPVar x) = D.viaShow x
prettyFPattern (FPLit i) = D.viaShow i
prettyFPattern (FPCons c vs ps) = do
  D.viaShow c <> D.align (D.list vs') <> D.align (D.tupled ps')
  where
    ps' = map prettyFPattern ps
    vs' = map D.viaShow vs

prettyFTerm :: LFresh m => Name TyCon -> Bool -> FTerm -> m (D.Doc a)
prettyFTerm arName par t = prettyApps par (apps t)
  where
    prettyApps :: LFresh m => Bool -> [Either Type FTerm] -> m (D.Doc a)
    prettyApps par [t] = prettyAtom par t
    prettyApps par ts = do
      ts' <- mapM (prettyAtom True) ts
      return $ parens par (D.group $ D.align $ D.vsep ts')

    prettyAtom :: LFresh m => Bool -> Either Type FTerm -> m (D.Doc a)
    prettyAtom par (Right t) = prettyTermAtom par t
    prettyAtom par (Left ty) = do
      ty' <- prettyType arName True ty
      return $ "@" D.<> ty'

    prettyTermAtom :: LFresh m => Bool -> FTerm -> m (D.Doc a)
    prettyTermAtom _ (FLit i) = return (D.viaShow i)
    prettyTermAtom _ (FVar x) = return (D.viaShow x)
    prettyTermAtom par (FLam b) =
      lunbind b $ \((p, ty), t) -> do
        td <- prettyFTerm arName False t
        let p' = prettyFPattern p
        ty' <- prettyType arName False (unembed ty)
        return
          $ parens par
          $ D.group
          $ D.nest 2
          $ D.vsep ["\\" <> D.parens (p' D.<+> ":" D.<+> ty') D.<+> "->", td]
    prettyTermAtom par (FTlam b) =
      lunbind b $ \(x, t) -> do
        td <- prettyFTerm arName False t
        return
          $ parens par
          $ D.group
          $ D.nest 2
          $ D.vsep ["\\@" <> D.viaShow x D.<+> "->", td]
    prettyTermAtom par (FLet b) = lunbind b $ \((p, ty, t), u) -> do
      t' <- prettyFTerm arName False (unembed t)
      u' <- prettyFTerm arName False u
      let p' = prettyFPattern p
      ty' <- prettyType arName False (unembed ty)
      return
        $ parens par
        $ D.group
        $ D.group ("let" D.<+> p' D.<+> ":" D.<+> ty' D.<+> "=" <> D.nest 2 (D.line <> t'))
        <> D.line
        <> "in"
        <> D.nest 2 (D.line <> u')
    prettyTermAtom _ t@(FApp _ _) = D.parens <$> prettyFTerm arName False t
    prettyTermAtom _ t@(FTApp _ _) = D.parens <$> prettyFTerm arName False t
    prettyTermAtom _ (FCons c tys ts) = do
      ts' <- traverse (prettyFTerm arName False) ts
      tys' <- traverse (prettyType arName False) tys
      let typeAppl = if null tys then mempty else D.align (D.list tys')
      return $ D.viaShow c <> typeAppl D.<> D.align (D.tupled ts')
    prettyTermAtom par (FMatch ty t rs) = do
      ty' <- prettyType arName False ty
      t' <- prettyFTerm arName False t
      rs' <- prettyFRules rs
      return
        $ parens par
        $ D.group
        $ "match"
        D.<+> t'
        D.<+> "with"
        D.<+> (D.brackets ty')
        D.<> D.line
        D.<> rs'
        <> D.line
        <> "end"

    prettyFRules :: LFresh m => [FRule] -> m (D.Doc a)
    prettyFRules rs = hardVsep <$> mapM prettyFRule rs

    prettyFRule :: LFresh m => FRule -> m (D.Doc a)
    prettyFRule (FRule b) =
      lunbind b $ \(p, t) -> do
        let p' = prettyFPattern p
        t' <- prettyFTerm arName False t
        return $ D.group $ D.nest 4 $ "|" D.<+> p' D.<+> "->" <> D.line <> t'

    apps :: FTerm -> [Either Type FTerm]
    apps (FApp t1 t2) = apps t1 ++ [Right t2]
    apps (FTApp t ty) = apps t ++ [Left ty]
    apps t = [Right t]

    hardVsep = D.concatWith (\x y -> x <> D.hardline <> y)

instance D.Pretty FTerm where
  pretty t = runLFreshM (prettyFTerm (string2Name "->") False t)

prettyFFunDefs :: LFresh m => Name TyCon -> FFunDefs -> m (D.Doc a)
prettyFFunDefs arName (FFunDefs b) =
  lunbind b $ \(eqs, t) -> do
    eqs' <- mapM prettyEq (unrec eqs)
    t' <- prettyFTerm arName False t
    return $ D.hcat [eq <> D.semi <> D.hardline | eq <- eqs'] <> t'
 where
  prettyEq (f, t) = do
    t' <- prettyEq' (unembed t)
    return $ D.viaShow f D.<+> t'
  prettyEq' (FLam b) =
    lunbind b $ \((p, ty), t) -> do
      t' <- prettyEq' t
      let p' = prettyFPattern p
      ty' <- prettyType arName False (unembed ty)
      return $ D.parens (p' D.<+> ":" D.<+> ty') D.<+> t'
  prettyEq' t = do
    t' <- prettyFTerm arName False t
    return $ D.group $ D.nest 2 $ "=" <> D.line <> t'

instance D.Pretty FFunDefs where
  pretty fs = runLFreshM (prettyFFunDefs (string2Name "->") fs)

prettyDataConDecl :: LFresh m => Name TyCon -> DataConDecl -> m (D.Doc a)
prettyDataConDecl arName (DataConDecl c decl) =
  lunbind (unembed decl) $ \(xs, (cs, tys, ty)) -> do
    tys' <- mapM (prettyType arName True) tys
    ty' <- prettyType arName False ty
    let forAll = if null xs
          then mempty
          else "forall" D.<+> D.fillSep (map D.viaShow xs) D.<+> "." <> D.space
    let constraints =
          if null cs then mempty else D.viaShow cs D.<+> "=>" <> D.space
    let lhs = if null tys
          then mempty
          else D.encloseSep mempty mempty " * " tys' D.<+> "->" <> D.space
    return $ D.viaShow c D.<+> ":" D.<+> forAll <> constraints <> lhs <> ty'

prettyTypeDecl :: LFresh m => Name TyCon -> TypeDecl -> m (D.Doc a)
prettyTypeDecl arName (TypeDecl c k ds) = do
  let c' = D.viaShow c
  ds' <- mapM (prettyDataConDecl arName) ds
  let k' = prettyKind False (unembed k)
  return
    $ "data"
    D.<+> c'
    D.<+> ":"
    D.<+> k'
    D.<+> "where"
    <> D.hardline
    <> hardVsep (map ("|" D.<+>) ds')
    <> D.hardline
    <> "end"

prettyTypeDecls :: LFresh m => Name TyCon -> [TypeDecl] -> m (D.Doc a)
prettyTypeDecls arName decls = do
  decls' <- mapM (prettyTypeDecl arName) decls
  return $ D.hcat [d <> D.hardline | d <- decls']

prettyFProgram :: LFresh m => Name TyCon -> FProgram -> m (D.Doc a)
prettyFProgram arName (FProgram b) =
  lunbind b $ \(decls, defs) -> do
    decls' <- prettyTypeDecls arName (unrec decls)
    defs' <- prettyFFunDefs arName defs
    return $ decls' <> defs'

instance D.Pretty FProgram where
  pretty p = runLFreshM (prettyFProgram (string2Name "->") p)

parens :: Bool -> D.Doc a -> D.Doc a
parens b d = if b then D.parens d else d

hardVsep = D.concatWith (\x y -> x <> D.hardline <> y)

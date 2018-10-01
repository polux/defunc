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

module Parser (parseFunDefs, parseFProgram) where

import AST
import Control.Arrow ((***))
import Data.Void
import Text.Megaparsec hiding (match)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Unbound.Generics.LocallyNameless (rec, bind, embed, string2Name)

{- COMMON -}

sc = L.space (skipSome spaceChar *> pure ()) lineCmnt blockCmnt
 where
  lineCmnt = L.skipLineComment "--"
  blockCmnt = L.skipBlockComment "{-" "-}"

lexeme = L.lexeme sc

symbol = L.symbol sc

s_lparen = symbol "("
s_rparen = symbol ")"
s_comma = symbol ","
s_lambda = symbol "\\"
s_typeLambda = symbol "\\@"
s_arrow = symbol "->"
s_dot = symbol "."
s_let = symbol "let"
s_in = symbol "in"
s_semi = symbol ";"
s_equals = symbol "="
s_data = symbol "data"
s_end = symbol "end"
s_forall = symbol "forall"
s_match = symbol "match"
s_where = symbol "where"
s_with = symbol "with"
s_pipe = symbol "|"
s_at = symbol "@"
s_colon = symbol ":"
s_star = symbol "*"
s_type = symbol "Type"
s_unit = symbol "Unit"

parens = between s_lparen s_rparen

squares = between (symbol "[") (symbol "]")

idTail = many (alphaNumChar <|> char '_' <|> char '\'')

identifier = (lexeme . try) (p >>= check)
 where
  p = (:) <$> (lowerChar <|> char '_') <*> idTail
  check x = if x `elem` ["in", "let", "match", "with", "end", "data", "where", "forall"]
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

constructor = lexeme (try p)
  where p = (:) <$> (upperChar <|> char '_') <*> idTail

{- UNTYPED TERMS -}

lterm = foldl1 App <$> some atom

atom =
  (svar <$> identifier)
    <|> match
    <|> constructorApp
    <|> list
    <|> num
    <|> letIn
    <|> lambda
    <|> tupleOrparenthesizedTerm

tupleOrparenthesizedTerm = do
  _ <- s_lparen
  t <- lterm
  parenClose t <|> tupleClose t
 where
  parenClose t = do
    _ <- s_rparen
    return t
  tupleClose t = do
    _ <- s_comma
    ts <- lterm `sepBy` s_comma
    _ <- s_rparen
    return $ tuple (t : ts)

constructorApp = Cons <$> constructor <*> parens (lterm `sepBy` s_comma)

lambda = mkLam <$> s_lambda <*> some pattern <*> s_arrow <*> lterm
  where mkLam _ ids _ t = foldr plam t ids

letIn = mkLets <$> s_let <*> sepBy binding s_semi <*> s_in <*> lterm
  where mkLets _ bindings _ t = foldr mkLet t bindings
        mkLet (x, u) v = Let (bind (x, embed u) v)

binding = mkBinding <$> pattern <*> s_equals <*> lterm
  where mkBinding p _ t = (p, t)

num = Lit <$> lexeme L.decimal

list = mkList <$> squares (lterm `sepBy` s_comma)
  where mkList xs = foldr mkCons mkNil xs
        mkCons x y = Cons "Cons" [x, y]
        mkNil = Cons "Nil" []

pattern = patternLit <|> patternList <|> patternApp <|> (pvar <$> identifier)

patternLit = PLit <$> lexeme L.decimal

patternApp = mkCons <$> optional constructor <*> parens (pattern `sepBy` s_comma)
 where
  mkCons Nothing [p] = p
  mkCons Nothing ps = ptuple ps
  mkCons (Just c) ps = PCons c ps

patternList = mkList <$> squares (pattern `sepBy` s_comma)
  where mkList xs = foldr mkCons mkNil xs
        mkCons x y = PCons "Cons" [x, y]
        mkNil = PCons "Nil" []

match = mkMatch <$> s_match <*> lterm <*> s_with <*> many rule <*> s_end
  where mkMatch _ t _ rs _ = Match t rs

rule = mkRule <$> s_pipe <*> pattern <*> s_arrow <*> lterm
  where mkRule _ p _ t = Rule (bind p t)

eq = mkEq <$> identifier <*> many pattern <*> s_equals <*> lterm
  where mkEq f xs _ t = (f, foldr plam t xs)

fundefs = mkEqs <$> try eq `endBy` s_semi <*> lterm
 where
   mkEqs eqs t = makeFunDefs [(string2Name f, u) | (f, u) <- eqs] t

parseFunDefs :: String -> Either (ParseError Char Void) FunDefs
parseFunDefs s = parse (sc *> (fundefs <* eof)) "" s

{- SYSTEM F TERMS -}

fConstructorName = string2Name <$> constructor

fTermName = string2Name <$> identifier

fTypeName = string2Name <$> identifier

fTyConName = string2Name <$> constructor

kind = try arrow <|> kAtom
  where arrow = mkArrow <$> (kAtom `sepBy` s_star) <*> s_arrow <*> kAtom
        mkArrow tys _ ty = KArrow tys ty

kAtom = (s_type *> pure KType) <|> parens kind

typeDecl =
  mkDecl
    <$> s_data
    <*> fTyConName
    <*> s_colon
    <*> kind
    <*> s_where
    <*> many (s_pipe *> (dataConDecl))
    <*> s_end
  where mkDecl _ tyCon _ k _ decls _ = TypeDecl tyCon (embed k) decls

dataConDecl = mkDecl <$> fConstructorName <*> s_colon <*> option [] prefix <*> suffix
  where prefix = s_forall *> (many fTypeName <* s_dot)
          where mkForAll _ vs _ = vs
        suffix = (,) <$> option [] (try arrow) <*> tCons
        arrow = (tAtom `sepBy1` s_star) <* s_arrow
        mkDecl c _ vs (tys, ty) = DataConDecl c (embed (bind vs ([], tys, ty)))

fType = mkArrows <$> tProduct `sepBy1` s_arrow
  where mkArrows = foldr1 (\ty1 ty2 -> TCons (string2Name "->") [ty1, ty2])

tProduct = mkProducts <$> tAtom `sepBy` s_star
  where mkProducts = foldl1 (\ty1 ty2 -> TCons (string2Name "*") [ty1, ty2])

tAtom = tVar <|> tUnit <|> tCons <|> tForall <|> parens fType

tVar = TVar <$> fTypeName

tUnit = s_unit *> pure TUnit

tCons = TCons <$> fTyConName <*> option [] (squares (fType `sepBy` s_comma))

tForall = mkForall <$> some fTypeName <*> s_dot <*> fType
  where mkForall vs _ ty = foldr mkBinForall ty vs
        mkBinForall v ty = TForall (bind v ty)

fTerm = foldl app <$> fTermAtom <*> many fAtom
 where
  app t (Left u) = FApp t u
  app t (Right ty) = FTApp t ty

fAtom = Right <$> (s_at *> ty) <|> Left <$> fTermAtom
  where ty = tVar <|> tUnit <|> tCons <|> parens fType

fTermAtom =
  fVar
    <|> fMatch
    <|> fConstructorApp
    <|> fNum
    <|> fLetIn
    <|> fTLambda
    <|> fLambda
    <|> parens fTerm

fVar = FVar . string2Name <$> identifier

fConstructorApp =
  FCons
    <$> fConstructorName
    <*> option [] (squares (fType `sepBy` s_comma))
    <*> parens (fTerm `sepBy` s_comma)

fNum = FLit <$> lexeme L.decimal

fLetIn = mkLets <$> s_let <*> sepBy fBinding s_semi <*> s_in <*> fTerm
 where
  mkLets _ bindings _ t = foldr mkLet t bindings
  mkLet (x, ty, u) v = FLet (bind (x, embed ty, embed u) v)

fBinding = mkBinding <$> fPattern <*> s_colon <*> fType <*> s_equals <*> fTerm
  where mkBinding p _ ty _ t = (p, ty, t)

fLambda = mkLam <$> s_lambda <*> parens typedFPattern <*> s_arrow <*> fTerm
 where
  mkLam _ (p, ty) _ t = FLam (bind (p, embed ty) t)

typedFPattern = mkPair <$> fPattern <*> s_colon <*> fType
  where mkPair p _ ty = (p, ty)

fTLambda = mkLam <$> s_typeLambda <*> fTypeName <*> s_arrow <*> fTerm
  where mkLam _ tv _ t = FTlam (bind tv t)

fPattern = fPatternLit <|> fPatternApp <|> fPVar

fPatternLit = FPLit <$> lexeme L.decimal

fPatternApp =
  mkCons
    <$> fConstructorName
    <*> option [] (squares (fTypeName `sepBy` s_comma))
    <*> parens (fPattern `sepBy` s_comma)
  where mkCons c tvs ps = FPCons (embed c) tvs ps

fPVar = FPVar <$> fTermName

fMatch =
  mkMatch
    <$> s_match
    <*> fTerm
    <*> s_with
    <*> squares fType
    <*> many fRule
    <*> s_end
  where mkMatch _ t _ ty rs _ = FMatch ty t rs

fRule = mkRule <$> s_pipe <*> fPattern <*> s_arrow <*> fTerm
  where mkRule _ p _ t = FRule (bind p t)

fEq = (,) <$> try (fTermName <* s_equals) <*> fTerm

fFunDefs = mkEqs <$> fEq `endBy` s_semi <*> fTerm
  where mkEqs eqs t = FFunDefs $ bind (rec (map (id *** embed) eqs)) t

fProgram = mkProg <$> many typeDecl <*> fFunDefs
  where mkProg decls defs = FProgram (bind (rec decls) defs)

parseFProgram :: String -> Either (ParseError Char Void) FProgram
parseFProgram s = parse (sc *> (fProgram <* eof)) "" s

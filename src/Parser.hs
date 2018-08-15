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

module Parser (parseFunDefs) where

import AST
import Data.Void
import Text.Megaparsec hiding (match)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Unbound.Generics.LocallyNameless (bind, embed, string2Name)

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
s_dot = symbol "->"
s_let = symbol "let"
s_in = symbol "in"
s_semi = symbol ";"
s_equals = symbol "="
s_end = symbol "end"
s_match = symbol "match"
s_with = symbol "with"
s_pipe = symbol "|"

parens = between s_lparen s_rparen

squares = between (symbol "[") (symbol "]")

idTail = many (alphaNumChar <|> char '_' <|> char '\'')

identifier = (lexeme . try) (p >>= check)
 where
  p = (:) <$> (lowerChar <|> char '_') <*> idTail
  check x = if x `elem` ["in", "let", "match", "with", "end"]
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

constructor = lexeme (try p)
  where p = (:) <$> (upperChar <|> char '_') <*> idTail

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

lambda = mkLam <$> s_lambda <*> some pattern <*> s_dot <*> lterm
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

rule = mkRule <$> s_pipe <*> pattern <*> s_dot <*> lterm
  where mkRule _ p _ t = Rule (bind p t)

eq = mkEq <$> identifier <*> many pattern <*> s_equals <*> lterm
  where mkEq f xs _ t = (f, foldr plam t xs)

fundefs = mkEqs <$> try eq `endBy` s_semi <*> lterm
 where
  mkEqs eqs t =
    let (fs, ts) = unzip eqs in FunDefs (bind (map string2Name fs) (ts, t))

parseFunDefs :: String -> Either (ParseError Char Void) FunDefs
parseFunDefs s = parse (sc *> (fundefs <* eof)) "" s

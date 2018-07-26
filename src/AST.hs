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
{-# LANGUAGE MultiParamTypeClasses #-}

module AST where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import qualified Data.Map as M
import Data.List (foldl')
import Unbound.Generics.LocallyNameless
  ( Subst(..)
  , Alpha
  , Bind
  , Embed
  , Name
  , SubstName(..)
  , aeq
  , acompare
  , bind
  , string2Name)

data FunDefs = FunDefs (Bind [Name Term] ([Term], Term))
  deriving (Show, Generic, Typeable)

data Pattern
  = PCons String [Pattern]
  | PVar (Name Term)
  | PLit Int
  deriving (Show, Generic, Typeable)

type Rules = [Rule]

data Rule = Rule (Bind Pattern Term)
  deriving (Show, Generic, Typeable)

instance Eq Rule where
  (==) = aeq

instance Ord Rule where
  compare = acompare

data Term
  = Var (Name Term)
  | App Term Term
  | Lam (Bind Pattern Term)
  | Let (Bind Pattern Term) Term
  | Lit Int
  | Cons String [Term]
  | Match Term Rules
  deriving (Show, Generic, Typeable)

instance Alpha Term
instance Alpha Rule
instance Alpha Pattern

instance Subst Term Term where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Term Rule where
  isvar _ = Nothing

instance Subst Term Pattern where
  isvar _ = Nothing

instance Eq Term where
  (==) = aeq

instance Ord Term where
  compare = acompare

plam p t = Lam (bind p t)
lam x t = Lam (bind (PVar x) t)
slam x t = lam (string2Name x) t
svar = Var . string2Name
pvar = PVar . string2Name

infixl @:
t @: u = App t u

app :: Term -> [Term] -> Term
app t ts = foldl' App t ts

unApp :: Term -> (Term, [Term])
unApp (App t u) = let (t', ts) = unApp t in (t', ts++[u])
unApp t = (t, [])

pair x y = Cons "" [x, y]
ppair x y = PCons "" [x, y]
tuple xs = foldl1 pair xs
ptuple xs = foldl1 ppair xs

type Env = [(Name Term, Embed Val)]

data Val
  = VInt Int
  | VCons String [Val]
  | VClosure (Bind Env Term)
  deriving (Show, Generic, Typeable)

instance Alpha Val

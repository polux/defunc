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

{-# LANGUAGE EmptyDataDeriving #-}
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
  , Fresh
  , Name
  , Rec
  , SubstName(..)
  , aeq
  , acompare
  , bind
  , embed
  , rec
  , string2Name
  , unbind
  , unembed
  , unrec)

data FunDefs = FunDefs (Bind (Rec [(Name Term, Embed Term)]) Term)
  deriving (Show, Generic, Typeable)

data Program = Program (Bind (Rec [TypeDecl]) FunDefs)
  deriving (Show, Generic, Typeable)

unmakeFunDefs :: Fresh m => FunDefs -> m ([(Name Term, Term)], Term)
unmakeFunDefs (FunDefs b) = do
  (eqs, t) <- unbind b
  return (map unwrap (unrec eqs), t)
  where unwrap (x, u) = (x, unembed u)

makeFunDefs :: [(Name Term, Term)] -> Term -> FunDefs
makeFunDefs eqs t = FunDefs $ bind (rec (map wrap eqs)) t
  where wrap (x, u) = (x, embed u)

data Pattern
  = PCons (Embed (Name DataCon)) [Pattern]
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
  | Let (Bind (Pattern, Embed Term) Term)
  | Lit Int
  | Cons (Name DataCon) [Term]
  | Match Term Rules
  deriving (Show, Generic, Typeable)

instance Alpha Term
instance Alpha Rule
instance Alpha Pattern
instance Alpha FunDefs

instance Subst Term Term where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Term Rule
instance Subst Term Pattern

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

pair x y = Cons (string2Name "") [x, y]
ppair x y = PCons (embed (string2Name "")) [x, y]
tuple xs = foldl1 pair xs
ptuple xs = foldl1 ppair xs

type Env = [(Name Term, Embed Val)]

data Val
  = VInt Int
  | VCons (Name DataCon) [Val]
  | VClosure (Bind Env Term)
  deriving (Show, Generic, Typeable)

instance Alpha Val

data Kind
  = KType
  | KArrow [Kind] Kind
  deriving (Show, Generic, Typeable)

data TyCon

instance Alpha Kind

data Type
  = TVar (Name Type)
  | TUnit
  | TCons (Name TyCon) [Type]
  | TForall (Bind (Name Type) Type)
  deriving (Show, Generic, Typeable)

instance Alpha Type

instance Subst Type Type where
  isvar (TVar v) = Just (SubstName v)
  isvar _ = Nothing

data DataCon

data FPattern
  = FPCons (Embed (Name DataCon)) [Name Type] [FPattern]
  | FPVar (Name FTerm)
  | FPLit Int
  deriving (Show, Generic, Typeable)

type FRules = [FRule]

data FRule = FRule (Bind FPattern FTerm)
  deriving (Show, Generic, Typeable)

data FTerm
  = FVar (Name FTerm)
  | FApp FTerm FTerm
  | FTApp FTerm Type
  | FLam (Bind (FPattern, Embed Type) FTerm)
  | FTlam (Bind (Name Type) FTerm)
  | FLet (Bind (FPattern, Embed Type, Embed FTerm) FTerm)
  | FLit Int
  | FCons (Name DataCon) [Type] [FTerm]
  | FMatch Type FTerm FRules
  deriving (Show, Generic, Typeable)

instance Alpha FTerm
instance Alpha FRule
instance Alpha FPattern

instance Subst FTerm FTerm where
  isvar (FVar v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst FTerm Type
instance Subst FTerm FRule
instance Subst FTerm FPattern

data TypeDecl = TypeDecl (Name TyCon) (Embed Kind) [DataConDecl]
  deriving (Show, Generic, Typeable)

data Constraint = Type :~: Type
  deriving (Show, Generic, Typeable)

data DataConDecl = DataConDecl (Name DataCon) (Embed (Bind [Name Type] ([Constraint], [Type], Type)))
  deriving (Show, Generic, Typeable)

data FFunDefs = FFunDefs (Bind (Rec [(Name FTerm, Embed Type, Embed FTerm)]) FTerm)
  deriving (Show, Generic, Typeable)

data FProgram = FProgram (Bind (Rec [TypeDecl]) FFunDefs)
  deriving (Show, Generic, Typeable)

instance Alpha Constraint
instance Alpha TypeDecl
instance Alpha DataConDecl
instance Alpha FFunDefs
instance Alpha FProgram

instance Subst Type Constraint

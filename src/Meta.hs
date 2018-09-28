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

{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Meta
  ( MetaExpr()
  , parseMeta
  , evalMeta
  )
where

import AST
import CPS
import Eval
import Defunc
import Parser
import Pretty

import Control.Monad.Except
import Data.Text.Prettyprint.Doc (defaultLayoutOptions, layoutPretty, Pretty, pretty)
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import Text.Megaparsec (parseErrorPretty)

data MetaType :: * -> * where
  MString :: MetaType String
  MFunDefs :: MetaType FunDefs
  MFProgram :: MetaType FProgram
  MVal :: MetaType Val

instance Show (MetaType a) where
  show MString = "String"
  show MFunDefs = "FunDefs"
  show MFProgram = "FProgram"
  show MVal = "Val"

data MetaExpr :: * -> * -> * where
  Pipe :: MetaExpr a b -> MetaExpr b c -> MetaExpr a c
  ParseFunDefs :: MetaExpr String FunDefs
  ParseFProgram :: MetaExpr String FProgram
  Cps :: MetaExpr FunDefs FunDefs
  Defunc :: MetaExpr FunDefs FunDefs
  Eval :: MetaExpr FunDefs Val
  Pretty :: Pretty a => MetaExpr a String

parseMeta :: MonadError String m => [String] -> m (MetaExpr String String)
parseMeta es = go MString es
 where
  go
    :: (MonadError String m, Pretty a)
    => MetaType a
    -> [String]
    -> m (MetaExpr a String)
  go MString ("parse" : es) = Pipe ParseFunDefs <$> go MFunDefs es
  go MString ("parse_f" : es) = Pipe ParseFProgram <$> go MFProgram es
  go MFunDefs ("cps" : es) = Pipe Cps <$> go MFunDefs es
  go MFunDefs ("defunc" : es) = Pipe Defunc <$> go MFunDefs es
  go MFunDefs ("eval" : es) = Pipe Eval <$> go MVal es
  go mt (e : _) =
    throwError $ "cannot apply " ++ e ++ " to meta values of type " ++ show mt
  go MFunDefs [] = return Pretty
  go MFProgram [] = return Pretty
  go MVal [] = return Pretty
  go mt [] = throwError $ "cannot pretty print meta values of type " ++ show mt

evalMeta :: MonadError String m => MetaExpr a b -> a -> m b
evalMeta (Pipe e1 e2) x = evalMeta e1 x >>= evalMeta e2
evalMeta ParseFunDefs s = case parseFunDefs s of
  Left e -> throwError (parseErrorPretty e)
  Right defs -> return defs
evalMeta ParseFProgram s = case parseFProgram s of
  Left e -> throwError (parseErrorPretty e)
  Right prog -> return prog
evalMeta Cps defs = return (cps defs)
evalMeta Defunc defs = return (defunctionalize defs)
evalMeta Eval defs = case eval defs of
  Left e -> throwError e
  Right v -> return v
evalMeta Pretty x = return (toString x)

toString :: Pretty a => a -> String
toString = renderString . layoutPretty defaultLayoutOptions . pretty

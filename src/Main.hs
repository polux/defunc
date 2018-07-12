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

module Main where

import AST
import Pretty
import CPS
import Defunc
import Eval
import Parser

import Control.Arrow ((>>>))
import System.Environment (getArgs)
import Safe (lastMay)
import Text.Show.Pretty (pPrint)
import Text.Megaparsec (parseErrorPretty)
import Data.Text.Prettyprint.Doc (pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)

process :: (FunDefs -> FunDefs) -> (FunDefs -> IO ()) -> IO ()
process f k = do
  s <- getContents
  case parseFunDefs s of
    Left e -> error (parseErrorPretty e)
    Right lt -> k (f lt)

parseAgs :: [String] -> (FunDefs -> FunDefs)
parseAgs = foldr (>>>) id . map parseArg
  where parseArg "cps" = cps
        parseArg "defunc" = defunctionalize
        parseAgs x = error ("unknown option " ++ x)

printPrettyFunDefs :: FunDefs -> IO ()
printPrettyFunDefs defs = do
  putDoc (pretty defs)
  putStrLn ""

evalAndPrintValue :: FunDefs -> IO ()
evalAndPrintValue defs = do
  case eval defs of
    Left e -> putStrLn e
    Right v -> pPrint v

main = do
  args <- getArgs
  if (lastMay args == Just "eval")
    then process (parseAgs (init args)) evalAndPrintValue
    else process (parseAgs args) printPrettyFunDefs

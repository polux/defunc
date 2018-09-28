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
import Meta
import Parser

import Control.Monad.Except
import System.Environment (getArgs)

main = do
  args <- getArgs
  input <- getContents
  let res = runExcept $ do
        metaProg <- parseMeta args
        evalMeta metaProg input
  case res of
    Left e -> error e
    Right s -> putStrLn s

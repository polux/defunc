module TypeChecker where

import AST
import Unbound.Generics.LocallyNameless
import Control.Monad.IO.Class
import Data.Text.Prettyprint.Doc (defaultLayoutOptions, layoutPretty, pretty)
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import Parser
import Pretty
import Text.Megaparsec (parseErrorPretty)

nat, arrow, list, vec, sTyCon, zTyCon :: Name TyCon
nat = string2Name "Nat"
arrow = string2Name "->"
list = string2Name "List"
vec = string2Name "Vec"
sTyCon = string2Name "S"
zTyCon = string2Name "Z"

z, s, nil, cons, vnil, vcons :: Name DataCon
z = string2Name "Z"
s = string2Name "S"
nil = string2Name "Nil"
cons = string2Name "Cons"
vnil = string2Name "VNil"
vcons = string2Name "VCons"

idn :: Name FTerm
idn = string2Name "id"

arrowDecl, natDecl, listDecl, vecDecl :: TypeDecl
arrowDecl = TypeDecl arrow (embed $ KArrow [KType] KType) []
natDecl = TypeDecl nat (embed KType) [zDecl, sDecl]
listDecl = TypeDecl list (embed (KArrow [KType] KType)) [nilDecl, consDecl]
vecDecl = TypeDecl vec (embed (KArrow [KType, KType] KType)) [vNilDecl, vConsDecl]

mkArrow ty1 ty2 = TCons arrow [ty1, ty2]
natType = TCons nat []
idType = TForall $ bind (string2Name "a") (TVar (string2Name "a"))
mkListType ty = TCons list [ty]
mkVecType ty n = TCons vec [ty, n]
zType = TCons zTyCon []
mkSType n = TCons sTyCon [n]

zDecl, sDecl, nilDecl, consDecl :: DataConDecl
zDecl = DataConDecl z $ embed $ bind [] ([], [], natType)
sDecl = DataConDecl s $ embed $ bind [] ([], [natType], natType)
nilDecl = DataConDecl nil $ embed $ bind [a] ([], [], mkListType (TVar a))
  where a = string2Name "a"
consDecl = DataConDecl cons $ embed $ bind [a] ([], [TVar a, listA], listA)
 where
  a = string2Name "a"
  listA = mkListType (TVar a)
vNilDecl = DataConDecl vnil $ embed $ bind [a]
                                           ([], [], mkVecType (TVar a) zType)
  where a = string2Name "a"
vConsDecl = DataConDecl vcons $ embed $ bind
  [a, n]
  ([], [TVar a, vecA (TVar n)], vecA (mkSType (TVar n)))
 where
  a = string2Name "a"
  n = string2Name "n"
  vecA = mkVecType (TVar a)

typeDecls = [natDecl, listDecl, vecDecl]

idDef = (idn, embed $ FTlam (bind a (FLam (bind (FPVar x, embed $ TVar a) (FVar x)))))
  where a = string2Name "a"
        x = string2Name "x"

mainTerm = FLam
  (bind (FPVar x, embed natType)
        (mkConsNat (FCons s [] [FApp (FTApp (FVar idn) natType) (FVar x)]) mkNilNat)
  )
  where x = string2Name "x"
        mkConsNat t ts = FCons cons [natType] [t, ts]
        mkNilNat = FCons nil [natType] []

funDefs :: FFunDefs
funDefs = FFunDefs $ bind (rec ([idDef])) mainTerm

program :: FProgram
program = FProgram $ bind (rec typeDecls) funDefs


main :: IO ()
main = do
  let prettyProg = renderString (layoutPretty defaultLayoutOptions (pretty program))
  --prettyProg <- getContents
  putStrLn prettyProg
  putStrLn "-----"
  case parseFProgram prettyProg of
    Left e -> putStrLn (parseErrorPretty e)
    Right p -> do
      print p
      putStrLn "----------"
      putStrLn (render p)
      putStrLn "----------"
      print (render p == prettyProg)
  where render p = renderString (layoutPretty defaultLayoutOptions (pretty p))

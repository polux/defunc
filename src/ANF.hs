{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module ANF where

import AST
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe
import Safe (fromJustNote)

anf :: Term -> AnfTerm
anf = fromJustNote "anf conversion failed" . runFreshMT . normalizeTerm

normalizeTerm :: (MonadFail m, Fresh m) => Term -> m AnfTerm
normalizeTerm t = normalize t return

normalize :: (MonadFail m, Fresh m) => Term -> (AnfTerm -> m AnfTerm) -> m AnfTerm
normalize (Var x) k = k (AAtom (AVar x))
normalize (Lit i) k = k (AAtom (ALit i))
normalize (Lam b) k = do
  (p, t) <- unbind b
  t' <- normalizeTerm  t
  k (AAtom (ALam (bind p t')))
normalize (App t1 t2) k =
  normalizeName t1 $ \at1 ->
    normalizeName t2 $ \at2 ->
      k (AComp (AApp at1 at2))
normalize (Cons c ts) k =
  normalizeNames ts $ \as ->
      k (AComp (ACons c as))
normalize (Match t rs) k =
  normalizeName t $ \a ->
    normalizeRules rs $ \ars ->
      k (AComp (AMatch a ars))

normalizeRules :: (MonadFail m, Fresh m) => Rules -> (AnfRules -> m AnfTerm) -> m AnfTerm
normalizeRules [] k = k []
normalizeRules (r:rs) k =
  normalizeRule r $ \ar ->
    normalizeRules rs $ \ars ->
      k (ar:ars)

normalizeRule :: (MonadFail m, Fresh m) => Rule -> (AnfRule -> m AnfTerm) -> m AnfTerm
normalizeRule (Rule b) k = do
  (p, t) <- unbind b
  normalize t $ \at ->
    k (ARule (bind p at))

normalizeName :: (MonadFail m, Fresh m) => Term -> (AnfAtom -> m AnfTerm) -> m AnfTerm
normalizeName t k = normalize t $ \case
    AAtom a -> k a
    AComp c -> do
      x <- fresh (string2Name "t")
      kx <- k (AVar x)
      return (ALet (bind (PVar x, embed c) kx))
    x -> error ("unexpected: " ++ show x)

normalizeNames :: (MonadFail m, Fresh m) => [Term] -> ([AnfAtom] -> m AnfTerm) -> m AnfTerm
normalizeNames [] k = k []
normalizeNames (t:ts) k =
  normalizeName t $ \a ->
    normalizeNames ts $ \as ->
      k (a:as)

anfTermToTerm :: AnfTerm -> Term
anfTermToTerm (ALet (unsafeUnbind->((p, c), t))) = Let (bind (p, embed (anfCompToTerm (unembed c))) (anfTermToTerm t))
anfTermToTerm (AComp c) = anfCompToTerm c
anfTermToTerm (AAtom a) = anfAtomToTerm a

anfAtomToTerm :: AnfAtom -> Term
anfAtomToTerm (AVar x) = Var x
anfAtomToTerm (ALam (unsafeUnbind->(p, t))) = Lam (bind p (anfTermToTerm t))
anfAtomToTerm (ALit i) = Lit i

anfCompToTerm :: AnfComp -> Term
anfCompToTerm (AApp a1 a2) = App (anfAtomToTerm a1) (anfAtomToTerm a2)
anfCompToTerm (ACons c as) = Cons c (map anfAtomToTerm as)
anfCompToTerm (AMatch a rs) = Match (anfAtomToTerm a) (anfRulesToRules rs)

anfRulesToRules :: AnfRules -> Rules
anfRulesToRules = map anfRuleToRule

anfRuleToRule :: AnfRule -> Rule
anfRuleToRule (ARule (unsafeUnbind->(p, t))) = Rule (bind p (anfTermToTerm t))


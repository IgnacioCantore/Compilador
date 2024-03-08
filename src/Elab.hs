{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@NTerm) a locally closed (@Term@)
-}

module Elab ( desugar, desugarTy, desugarDecl, elab, elab_decl ) where

import Lang
import Subst
import MonadFD4

desugar :: MonadFD4 m => STerm -> m NTerm
desugar (SV i v) = return (V i v)
desugar (SConst i c) = return (Const i c)
desugar (SLam i [] _) = failPosFD4 i "Falta el argumento de la función"
desugar (SLam i [([v],ty)] t) = do
  ty' <- desugarTy ty
  t' <- desugar t
  return (Lam i v ty' t')
desugar (SLam i [(v:vs,ty)] t) = do
  ty' <- desugarTy ty
  t' <- desugar (SLam i [(vs,ty)] t)
  return (Lam i v ty' t')
desugar (SLam i (vs:vss) t) = desugar (SLam i [vs] (SLam i vss t))
desugar (SApp i h a) = do
  h' <- desugar h
  a' <- desugar a
  return (App i h' a')
desugar (SPrint i str t) = do
  t' <- desugar t
  return (Print i str t')
desugar (SUnPrint i str) = return (Lam i "x" NatTy (Print i str (V i "x")))
desugar (SBinaryOp i o t u) = do
  t' <- desugar t
  u' <- desugar u
  return (BinaryOp i o t' u')
desugar (SFix i _ _ [] _) = failPosFD4 i "Falta el argumento del punto fijo"
desugar (SFix i f fty [([v],vty)] t) = do
  fty' <- desugarTy fty
  vty' <- desugarTy vty
  t' <- desugar t
  return (Fix i f fty' v vty' t')
desugar (SFix i f fty [(v:vs,vty)] t) = do
  fty' <- desugarTy fty
  vty' <- desugarTy vty
  t' <- desugar (SLam i [(vs,vty)] t)
  return (Fix i f fty' v vty' t')
desugar (SFix i f fty (vs:vss) t) = desugar (SFix i f fty [vs] (SLam i vss t))
desugar (SIfZ i c t e) = do
  c' <- desugar c
  t' <- desugar t
  e' <- desugar e
  return (IfZ i c' t' e')
desugar (SLet i r v [] vty def body) =
  if r
    then failPosFD4 i "Falta el argumento del punto fijo"
    else do vty' <- desugarTy vty
            def' <- desugar def
            body' <- desugar body
            return (Let i v vty' def' body')
desugar (SLet i r f [([v],vty)] fty def body) = do
  fty' <- desugarTy fty
  vty' <- desugarTy vty
  def' <- desugar def
  body' <- desugar body
  let ty = FunTy vty' fty'
  if r
    then return (Let i f ty (Fix i f ty v vty' def') body')
    else return (Let i f ty (Lam i v vty' def') body')
desugar (SLet i r f [(v:vs,vty)] fty def body) = do
  fty' <- desugarTy fty
  vty' <- desugarTy vty
  def' <- desugar (SLam i [(vs,vty)] def)
  body' <- desugar body
  ty <- desugarTy $ buildFunTy ((v:vs),vty) [] fty
  if r
    then return (Let i f ty (Fix i f ty v vty' def') body')
    else return (Let i f ty (Lam i v vty' def') body')
desugar (SLet i r f (vs:vss) fty def body) = do
  let sty = buildFunTy vs vss fty
  ty <- desugarTy sty
  def' <- desugar $ if r
                      then SFix i f sty (vs:vss) def
                      else SLam i (vs:vss) def
  body' <- desugar body
  return (Let i f ty def' body')

desugarTy :: MonadFD4 m => STy -> m Ty
desugarTy SNatTy = return NatTy
desugarTy (SFunTy st1 st2) = do
  t1 <- desugarTy st1
  t2 <- desugarTy st2
  return (FunTy t1 t2)
desugarTy (SDecTy n) = do
  t <- lookupSTy n
  case t of
    Nothing -> failFD4 $ "El tipo " ++ n ++ " no está declarado"
    Just ty -> return ty

desugarDecl :: MonadFD4 m => SDecl -> m (Decl NTerm)
desugarDecl (STypeDecl i _ _ ) = failPosFD4 i $ "Se intentó hacer desugar sobre una declaración de tipo"
desugarDecl (SDecl i r v [] vty def) =
  if r
    then failPosFD4 i "Falta el argumento del punto fijo"
    else do vty' <- desugarTy vty
            def' <- desugar def
            return (Decl i v vty' def')
desugarDecl (SDecl i r f [([v],vty)] fty def) = do
  fty' <- desugarTy fty
  vty' <- desugarTy vty
  def' <- desugar def
  let ty = FunTy vty' fty'
  if r
    then return (Decl i f ty (Fix i f ty v vty' def'))
    else return (Decl i f ty (Lam i v vty' def'))
desugarDecl (SDecl i r f [(v:vs,vty)] fty def) = do
  fty' <- desugarTy fty
  vty' <- desugarTy vty
  def' <- desugar (SLam i [(vs,vty)] def)
  ty <- desugarTy $ buildFunTy ((v:vs),vty) [] fty
  if r
    then return (Decl i f ty (Fix i f ty v vty' def'))
    else return (Decl i f ty (Lam i v vty' def'))
desugarDecl (SDecl i r f (vs:vss) fty def) = do
  let sty = buildFunTy vs vss fty
  ty <- desugarTy sty
  def' <- desugar $ if r
                      then SFix i f sty (vs:vss) def
                      else SLam i (vs:vss) def
  return (Decl i f ty def')

buildFunTy :: ([Name],STy) -> [([Name],STy)] -> STy -> STy
buildFunTy ([_],vty)  []         fty = SFunTy vty fty
buildFunTy ([_],vty)  (arg:args) fty = SFunTy vty (buildFunTy arg args fty)
buildFunTy (_:vs,vty) args       fty = SFunTy vty (buildFunTy (vs,vty) args fty)


-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado.
elab :: NTerm -> Term
elab = elab' []

elab' :: [Name] -> NTerm -> Term
elab' env (V p v) =
  -- Tenemos que hver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then  V p (Free v)
    else V p (Global v)

elab' _ (Const p c) = Const p c
elab' env (Lam p v ty t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab' (x:f:env) t))
elab' env (IfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operador Print
elab' env (Print i str t) = Print i str (elab' env t)
-- Operadores binarios
elab' env (BinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Aplicaciones generales
elab' env (App p h a) = App p (elab' env h) (elab' env a)
elab' env (Let p v vty def body) = Let p v vty (elab' env def) (close v (elab' (v:env) body))

elab_decl :: Decl NTerm -> Decl Term
elab_decl = fmap elab

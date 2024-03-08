module Optimizations (
    optimizeDecl,
    optimizeTerm
    ) where

import Lang
import MonadFD4
import Eval ( semOp )
import Subst

optimizeDecl :: MonadFD4 m => Decl Term -> m (Decl Term)
optimizeDecl (Decl p x ty tt) = do
  optTerm <- optimizeTerm tt
  return $ Decl p x ty optTerm

optimizeTerm :: MonadFD4 m => Term -> m Term
optimizeTerm t = do
  iters <- getIters
  optimizeTerm' iters t

optimizeTerm' :: MonadFD4 m => Int -> Term -> m Term
optimizeTerm' 0 t = return t
optimizeTerm' n t = do
  optTerm <- folding t
  optTerm' <- propagation optTerm
  if optTerm' == t
    then return t
    else optimizeTerm' (n - 1) optTerm'

optimizer :: MonadFD4 m => (Term -> m Term) -> Term -> m Term
optimizer _ t@(V _ _) = return t
optimizer _ t@(Const _ _) = return t
optimizer opt (Lam i x ty t) = do
  t' <- opt t
  return $ Lam i x ty t'
optimizer opt (App i t u) = do
  t' <- opt t
  u' <- opt u
  return $ App i t' u'
optimizer opt (Print i str t) = do
  t' <- opt t
  return $ Print i str t'
optimizer opt (BinaryOp i op t e) = do
  t' <- opt t
  e' <- opt e
  return $ BinaryOp i op t' e'
optimizer opt (Fix i f fty x ty t) = do
  t' <- opt t
  return $ Fix i f fty x ty t'
optimizer opt (IfZ i c t e) = do
  c' <- opt c
  t' <- opt t
  e' <- opt e
  return $ IfZ i c' t' e'
optimizer opt (Let i x ty t e) = do
  t' <- opt t
  e' <- opt e
  return $ Let i x ty t' e'

folding :: MonadFD4 m => Term -> m Term
folding (BinaryOp i op t e) = do
  t' <- folding t
  e' <- folding e
  case (t', e') of
    (_, Const _ (CNat 0)) -> return t'
    (Const _ (CNat 0), _) -> case op of
                               Add -> return e'
                               Sub -> return $ Const i (CNat 0)
    (Const _ (CNat m), Const _ (CNat n)) -> return $ Const i $ CNat (semOp op m n)
    _ -> return $ BinaryOp i op t' e'
folding (IfZ i c t e) = do
  c' <- folding c
  t' <- folding t
  e' <- folding e
  case c' of
    (Const _ (CNat 0)) -> return t'
    (Const _ _) -> return e'
    _ -> return $ IfZ i c' t' e'
folding t = optimizer folding t

propagation :: MonadFD4 m => Term -> m Term
propagation (Let i x ty t e) = do
  t' <- propagation t
  e' <- propagation e
  case t' of
    c@(Const _ _) -> return $ subst' c e'
    _ -> return $ Let i x ty t' e'
propagation t = optimizer propagation t

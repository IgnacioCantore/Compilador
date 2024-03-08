module ClosureConvert ( runCC ) where

import Control.Monad.State
import Control.Monad.Writer
import Lang
import IR
import Subst

freshName :: Name -> StateT Int (Writer [IrDecl]) Name
freshName nm = do
  i <- get
  put (i + 1)
  return $ nm ++ "_" ++ show i

makeCode :: Ir -> [Name] -> Name -> Ir
makeCode t ns clos = let ns' = zip ns [1..]
                   in foldr (\(n,i) ir -> IrLet n (IrAccess (IrVar clos) i) ir) t ns'

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam _ x _ t) = do
  x' <- freshName x
  t' <- closureConvert (open x' t)
  fn <- freshName "f"
  let cn = "clos" ++ fn
      fv = freeVars t
      f = makeCode t' fv cn
      codef = IrFun fn [cn, x'] f
  tell [codef]
  return $ MkClosure fn (map IrVar fv)
closureConvert (App _ t u) = do
  t' <- closureConvert t
  u' <- closureConvert u
  nm <- freshName "closf"
  return $ IrLet nm t' (IrCall (IrAccess (IrVar nm) 0) [t', u'])
closureConvert (Print _ str t) = do
  t' <- closureConvert t
  return $ IrPrint str t'
closureConvert (BinaryOp _ op t e) = do
  t' <- closureConvert t
  e' <- closureConvert e
  return $ IrBinaryOp op t' e'
closureConvert (Fix _ f' fty x ty t) = do
  fn <- freshName $ f' ++ "rec"
  x' <- freshName x
  let cn = "clos" ++ fn
  t' <- closureConvert (openN [cn,x'] t)
  let fv = freeVars t
      f = makeCode t' fv cn
      codef = IrFun fn [cn, x'] f
  tell [codef]
  return $ MkClosure fn (map IrVar fv)
closureConvert (IfZ _ c t e) = do
  c' <- closureConvert c
  t' <- closureConvert t
  e' <- closureConvert e
  return $ IrIfZ c' t' e'
closureConvert (Let _ x _ t e) = do
  t' <- closureConvert t
  x' <- freshName x
  e' <- closureConvert $ open x' e
  return $ IrLet x' t' e'

runCC :: [Decl Term] -> [IrDecl]
runCC decls = snd $ runWriter $ runStateT (runCC' decls) 0

runCC' :: [Decl Term] -> StateT Int (Writer [IrDecl]) [IrDecl]
runCC' [] = return []
runCC' (Decl _ x _ body : decls) = do
  body' <- closureConvert body
  let irDecl = IrVal x body'
  tell [irDecl]
  runCC' decls

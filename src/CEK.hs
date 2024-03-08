module CEK ( evalCEK ) where

import Lang
import MonadFD4
import Eval ( semOp )
import PPrint ( ppName )
import Common

data Val = N Int | C Clos

data Clos = ClosFun Env Name Ty Term | ClosFix Env Name Ty Name Ty Term

type Env = [Val]

data Frame =
    KArg Env Term
  | KClos Clos
  | KIfZ Env Term Term
  | KBinOp Env BinaryOp Term
  | KBinOpVal Val BinaryOp
  | KPrint String
  | KLet Env Term

type Kont = [Frame]

search :: MonadFD4 m => Term -> Env -> Kont -> m Val
search (Print _ str t) env k = search t env (KPrint str : k)
search (BinaryOp _ op t u) env k = search t env (KBinOp env op u : k)
search (IfZ _ c t u) env k = search c env (KIfZ env t u : k)
search (App _ t u) env k = search t env (KArg env u : k)
search (V _ (Bound i)) env k = destroy (env !! i) k
search (V _ (Global nm)) env k = do
  mtm <- lookupDecl nm
  case mtm of
    Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName nm
    Just t -> search t env k
search (Const _ (CNat n)) env k = destroy (N n) k
search (Lam _ x ty t) env k = destroy (C (ClosFun env x ty t)) k
search (Fix _ f fty x ty t) env k = destroy (C (ClosFix env f fty x ty t)) k
search (Let _ _ _ t u) env k = search t env (KLet env u : k)

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy v@(N n) (KPrint str : k) = do
  printFD4 $ str ++ show n
  destroy v k
destroy v@(N n) (KBinOp env op u : k) = search u env (KBinOpVal v op : k)
destroy (N n') (KBinOpVal (N n) op : k) = destroy (N (semOp op n n')) k
destroy (N 0) (KIfZ env t e : k) = search t env k
destroy (N _) (KIfZ env t e : k) = search e env k
destroy (C clos) (KArg env t : k) = search t env (KClos clos : k)
destroy v (KClos (ClosFun env x ty t) : k) = search t (v : env) k
destroy v (KClos clos@(ClosFix env f fty x ty t) : k) = search t (v : (C clos) : env) k
destroy v (KLet env t : k) = search t (v : env) k

evalCEK :: MonadFD4 m => Term -> m Term
evalCEK t = do v <- search t [] []
               evalCEK' v

evalCEK' :: MonadFD4 m => Val -> m Term
evalCEK' (N n) = return (Const NoPos (CNat n))
evalCEK' (C (ClosFun _ x ty t)) = return (Lam NoPos x ty t)
evalCEK' (C (ClosFix _ f fty x ty t)) = return (Fix NoPos f fty x ty t)

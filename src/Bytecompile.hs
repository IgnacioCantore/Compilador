{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Byecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la BVM. También provee una implementación de la BVM
para ejecutar bytecode.
-}
module Bytecompile (
    Bytecode,
    runBC,
    bcWrite,
    bcRead,
    bytecompileModule
    ) where

import Lang
import Subst
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.Char

type Opcode = Int
type Bytecode = [Int]

data Val =
    I Int
  | Fun Env Bytecode
  | RA Env Bytecode

type Env = [Val]
type Stack = [Val]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern IFZ      = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern TAILCALL = 16

bc :: MonadFD4 m => Term -> m Bytecode
bc (Const _ (CNat n)) = return [CONST, n]
bc (BinaryOp _ op e1 e2) = do
  v1 <- bc e1
  v2 <- bc e2
  case op of
    Add -> return (v1 ++ v2 ++ [ADD])
    Sub -> return (v1 ++ v2 ++ [SUB])
bc (V _ (Bound i)) = return [ACCESS, i]
bc (App _ t u) = do
  f <- bc t
  e <- bc u
  return (f ++ e ++ [CALL])
bc (Lam _ _ _ t) = do
  t' <- bt t
  let flen = length t'
  return ([FUNCTION, flen] ++ t')
bc (Let _ _ _ e1 e2) = do
  e1' <- bc e1
  e2' <- bc e2
  return (e1' ++ [SHIFT] ++ e2' ++ [DROP])
bc (Print _ str t) = do
  let str' = map ord str
  t' <- bc t
  return ([PRINT] ++ str' ++ [NULL] ++ t' ++ [PRINTN])
bc (Fix _ _ _ _ _ t) = do
  t' <- bt t
  let flen = length t'
  return ([FUNCTION, flen] ++ t' ++ [FIX])
bc (IfZ _ c t u) = do
  c' <- bc c
  t' <- bc t
  u' <- bc u
  let skipTrue = length t' + 2
      skipFalse = length u'
  return (c' ++ [IFZ, skipTrue] ++ t' ++ [JUMP, skipFalse] ++ u')

bt :: MonadFD4 m => Term -> m Bytecode
bt (App _ t u) = do
  t' <- bc t
  u' <- bc u
  return (t' ++ u' ++ [TAILCALL])
bt (IfZ _ c t u) = do
  c' <- bc c
  t' <- bt t
  u' <- bt u
  let skipTrue = length t' + 2
      skipFalse = length u'
  return (c' ++ [IFZ, skipTrue] ++ t' ++ [JUMP, skipFalse] ++ u')
bt (Let _ _ _ e1 e2) = do
  e1' <- bc e1
  e2' <- bt e2
  return (e1' ++ [SHIFT] ++ e2')
bt t = do
  t' <- bc t
  return (t' ++ [RETURN])

type Module = [Decl Term]

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do
  let t = decl2let $ map (fmap (fmap g2f)) m
  t' <- bc t
  return (t' ++ [PRINTN, STOP])

decl2let :: Module -> Term
decl2let [Decl p x ty t] = Let p x ty (fmap g2f t) (V p (Bound 0))
decl2let (Decl p x ty t : decls) = Let p x ty (fmap g2f t) (close x $ decl2let decls)

g2f :: Var -> Var
g2f (Global n) = Free n
g2f v = v

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = map fromIntegral <$> un32  <$> decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC c = runBC' c [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' (CONST : n : c) e s = runBC' c e (I n : s)
runBC' (ADD : c) e (I n : I m : s) = runBC' c e (I (m + n) : s)
runBC' (SUB : c) e (I n : I m : s) = runBC' c e (I (max 0 (m - n)) : s)
runBC' (ACCESS : i : c) e s = runBC' c e (e !! i : s)
runBC' (CALL : c) e (v : Fun ef cf : s) = runBC' cf (v : ef) (RA e c : s)
runBC' (FUNCTION : j : c) e s = runBC' (drop j c) e (Fun e c : s)
runBC' (RETURN : _) _ (v : RA e c : s) = runBC' c e (v : s)
runBC' (SHIFT : c) e (v : s) = runBC' c (v : e) s
runBC' (DROP : c) (_ : e) s = runBC' c e s
runBC' (PRINTN : c) e (I n : s) = do
  printFD4 $ show n
  runBC' c e (I n : s)
runBC' (PRINT : c) e s = printStr c e s
runBC' (FIX : c) e (Fun ef cf : s) = do
  let efix = Fun (efix : ef) cf
  runBC' c e (efix : s)
runBC' (IFZ : j : c) e (I n : s) = do
  if n == 0
    then runBC' c e s
    else runBC' (drop j c) e s
runBC' (JUMP : j : c) e s = runBC' (drop j c) e s
runBC' [STOP] _ _ = return ()
runBC' (TAILCALL : _) _ (v : Fun ef cf : s) = runBC' cf (v : ef) s
runBC' c e s = failFD4 "Error en la ejecución de la máquina virtual"

printStr :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
printStr (NULL : c) e s = runBC' c e s
printStr (x : c) e s = do
  printCharFD4 $ chr x
  printStr c e s
printStr _ _ _ = failFD4 "Error al imprimir cadena"

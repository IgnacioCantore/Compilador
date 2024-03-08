{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

import Control.Monad.Trans
import Data.List (nub,  intersperse, isPrefixOf )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )

import System.Exit
import System.FilePath ( replaceExtension )
--import System.Process ( system )
import Options.Applicative
--import Data.Text.Lazy (unpack)

import Global ( GlEnv(..) )
import Errors
import Lang
import Parse ( P, stm, program, declOrTm, runP )
import Elab ( desugar, desugarTy, desugarDecl, elab )
import Eval ( eval )
import PPrint ( spp , ppTy, resugarDecl, sppDecl )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import CEK ( evalCEK )
import Bytecompile
import Optimizations
import C ( cCompile, cWrite )

prompt :: String
prompt = "FD4> "

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | InteractiveCEK
  | Bytecompile
  | RunVM
  | CC
  -- | Canon
  -- | LLVM
  -- | Build

-- | Parser de banderas
parseMode :: Parser (Mode,Bool)
parseMode = (,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' LLVM ( long "llvm" <> short 'l' <> help "Imprimir LLVM resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool, [FilePath])
parseArgs = (\(a,b) c -> (a,b,c)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2021" )

    go :: (Mode,Bool,[FilePath]) -> IO ()
    go (Interactive,opt,files) =
              do runFD4 opt (runInputT defaultSettings (repl Interactive files))
                 return ()
    go (Typecheck,opt, files) =
              runOrFail opt $ mapM_ typecheckFile files
    go (InteractiveCEK,opt, files) =
              do runFD4 opt (runInputT defaultSettings (repl InteractiveCEK files))
                 return ()
    go (Bytecompile,opt, files) =
              runOrFail opt $ mapM_ bytecompileFile files
    go (RunVM,_,files) =
              runOrFail False $ mapM_ bytecodeRun files
    go (CC,opt, files) =
              runOrFail opt $ mapM_ compileFile2C files
    -- go (Canon,_, files) =
    --           runOrFail $ mapM_ canonFile files
    -- go (LLVM,_, files) =
    --           runOrFail $ mapM_ llvmFile files
    -- go (Build,_, files) =
    --           runOrFail $ mapM_ buildFile files

runOrFail :: Bool -> FD4 a -> IO a
runOrFail opt m = do
  r <- runFD4 opt m
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => Mode -> [FilePath] -> InputT m ()
repl m args = do
       lift $ catchErrors $ compileFiles m args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand m c
                       maybe loop (`when` loop) b

compileFiles :: MonadFD4 m => Mode -> [FilePath] -> m ()
compileFiles _ []     = return ()
compileFiles m (x:xs) = do
        modify (\s -> s { lfile = x, inter = False })
        compileFile m x
        compileFiles m xs

loadFile :: MonadFD4 m => FilePath -> m [SDecl]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile :: MonadFD4 m => Mode -> FilePath -> m ()
compileFile m f = do
    printFD4 ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    decls <- parseIO filename program x
    mapM_ (handleDecl m) decls

typecheckFile :: MonadFD4 m => FilePath -> m ()
typecheckFile f = do
    printFD4  ("Chequeando " ++ f)
    sdecls <- loadFile f
    sdecls' <- filterM filterTypeDecl sdecls
    decls <- mapM typecheckDecl sdecls'
    opt <- getOptimize
    optDecls <- if opt
                  then mapM optimizeDecl decls
                  else return decls
    optSDecls <- replace sdecls optDecls
    ppterms <- mapM sppDecl optSDecls
    mapM_ printFD4 ppterms
  where
    replace :: MonadFD4 m => [SDecl] -> [Decl Term] -> m [SDecl]
    replace [] [] = return []
    replace (sdecl@(STypeDecl _ _ _) : sdecls) decls = do
      sdecls' <- replace sdecls decls
      return $ sdecl : sdecls'
    replace (SDecl _ _ _ _ _ _ : sdecls) (decl@(Decl _ _ _ _) : decls) = do
      sdecl <- resugarDecl decl
      sdecls' <- replace sdecls decls
      return $ sdecl : sdecls'

bytecompileFile :: MonadFD4 m => FilePath -> m ()
bytecompileFile f = do
    printFD4  ("Chequeando " ++ f)
    sdecls <- loadFile f
    sdecls' <- filterM filterTypeDecl sdecls
    decls <- mapM typecheckDecl sdecls'
    opt <- getOptimize
    optDecls <- if opt
                  then mapM optimizeDecl decls
                  else return decls
    bc <- bytecompileModule optDecls
    let f' = replaceExtension f "byte"
    liftIO $ bcWrite bc f'
    printFD4 $ "Archivo compilado en " ++ f'

filterTypeDecl :: MonadFD4 m => SDecl -> m Bool
filterTypeDecl (STypeDecl _ n sty) = do
    ty <- desugarTy sty
    addSTy n ty
    return False
filterTypeDecl _ = return True

bytecodeRun :: MonadFD4 m => FilePath -> m ()
bytecodeRun f = do
    bc <- liftIO $ bcRead f
    runBC bc

compileFile2C :: MonadFD4 m => FilePath -> m ()
compileFile2C f = do
    sdecls <- loadFile f
    sdecls' <- filterM filterTypeDecl sdecls
    decls <- mapM typecheckDecl sdecls'
    opt <- getOptimize
    optDecls <- if opt
                  then mapM optimizeDecl decls
                  else return decls
    let c = cCompile optDecls
    let f' = replaceExtension f "c"
    liftIO $ cWrite c f'
    printFD4 $ "Archivo compilado en " ++ f'

parseIO :: MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

typecheckDecl :: MonadFD4 m => SDecl -> m (Decl Term)
typecheckDecl sdecl = do
        Decl p x ty t <- desugarDecl sdecl
        let dd = Decl p x ty (elab t)
        tcDecl dd
        return dd

handleDecl :: MonadFD4 m => Mode -> SDecl -> m ()
handleDecl _ (STypeDecl _ n sty) = do
        ty <- desugarTy sty
        addSTy n ty
handleDecl m d = do
        Decl p x ty tt <- typecheckDecl d
        opt <- getOptimize
        optTerm <- if opt
                     then optimizeTerm tt
                     else return tt
        te <- case m of
          Interactive    -> eval optTerm
          InteractiveCEK -> evalCEK optTerm
        addDecl (Decl p x ty te)

data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) c))
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand :: MonadFD4 m => Mode -> Command -> m Bool
handleCommand m cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 ("Variables:\n" ++ (unlines [ name | name <- nub $ map declName glb ]))
                      printFD4 ("Tipos:\n" ++ (unlines [ name ++ " = " ++ ppTy ty | (name, ty) <- nub $ styEnv ]))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase m e
                          CompileFile f        -> put (s {lfile=f, cantDecl=0}) >> compileFile m f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile m) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase :: MonadFD4 m => Mode -> String -> m ()
compilePhrase m x =
  do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl m d
      Right t -> handleTerm m t

handleTerm :: MonadFD4 m => Mode -> STerm -> m ()
handleTerm m t = do
         t' <- desugar t
         let tt = elab t'
         s <- get
         ty <- tc tt (tyEnv s)
         opt <- getOptimize
         optTerm <- if opt
                      then optimizeTerm tt
                      else return tt
         te <- case m of
           Interactive    -> eval optTerm
           InteractiveCEK -> evalCEK optTerm
         ppte <- spp te
         printFD4 (ppte ++ " : " ++ ppTy ty)

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" stm x
    x'' <- desugar x'
    let ex = elab x''
    t  <- case x' of
           (SV p f) -> maybe ex id <$> lookupDecl f
           _        -> return ex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 ("\nNTerm:")
    printFD4 (show x'')
    printFD4 "\nTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" stm x
         t' <- desugar t
         let tt = elab t'
         s <- get
         ty <- tc tt (tyEnv s)
         printFD4 (ppTy ty)

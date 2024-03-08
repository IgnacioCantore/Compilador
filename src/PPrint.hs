{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    spp,
    ppTy,
    ppName,
    sppDecl,
    resugarDecl
    ) where

import Lang
import Subst ( open, openN )
import Elab ( desugarTy )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, bold, color, colorDull, Color (..), AnsiStyle )
import Data.Text.Prettyprint.Doc
import MonadFD4
import Global

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : (map (\i -> n ++ show i) [0..])
               in head (filter (\m -> not (elem m ns)) cands)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: [Name] -> Term -> NTerm
openAll ns (V p v) = case v of
      Bound i ->  V p $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> V p x
      Global x -> V p x
openAll ns (Const p c) = Const p c
openAll ns (Lam p x ty t) =
  let x' = freshen ns x
  in Lam p x' ty (openAll (x':ns) (open x' t))
openAll ns (App p t u) = App p (openAll ns t) (openAll ns u)
openAll ns (Fix p f fty x xty t) =
  let
    x' = freshen ns x
    f' = freshen (x':ns) f
  in Fix p f' fty x' xty (openAll (x:f:ns) (openN [f',x'] t))
openAll ns (IfZ p c t e) = IfZ p (openAll ns c) (openAll ns t) (openAll ns e)
openAll ns (Print p str t) = Print p str (openAll ns t)
openAll ns (BinaryOp p op t u) = BinaryOp p op (openAll ns t) (openAll ns u)
openAll ns (Let p v ty m n) =
    let v'= freshen ns v
    in  Let p v' ty (openAll ns m) (openAll (v':ns) (open v' n))

--Colores
constColor = annotate (color Red)
opColor = annotate (colorDull Green)
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor = annotate (color Blue <> italicized)
typeNameColor = annotate (color Cyan <> italicized)
typeOpColor = annotate (colorDull Blue)
defColor = annotate (colorDull Magenta <> italicized)
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: Ty -> Doc AnsiStyle
ty2doc NatTy     = typeColor (pretty "Nat")
ty2doc (FunTy x@(FunTy _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y]

-- | Pretty printer para tipos (Doc)
sty2doc :: STy -> Doc AnsiStyle
sty2doc SNatTy     = typeColor (pretty "Nat")
sty2doc (SFunTy x@(SFunTy _ _) y) = sep [parens (sty2doc x), typeOpColor (pretty "->"),sty2doc y]
sty2doc (SFunTy x y) = sep [sty2doc x, typeOpColor (pretty "->"),sty2doc y]
sty2doc (SDecTy n) = typeNameColor (pretty n)

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp t = go [] t where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo?
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c
t2doc at (SLam _ args t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , binding2doc args
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]
t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)
t2doc at (SFix _ f fty args m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , binding2doc (([f], fty) : args)
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]
t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]
t2doc at (SPrint _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]
t2doc at (SUnPrint _ str) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str)]
t2doc at (SLet _ _ v [] ty t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , binding2doc [([v],ty)]
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]
t2doc at (SLet _ rec f args fty t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , if rec then keywordColor (pretty "rec") else pretty ""
       , name2doc f
       , binding2doc args
       , pretty ":"
       , sty2doc fty
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]
t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: [([Name], STy)] -> Doc AnsiStyle
binding2doc [([x],ty)] = parens (sep [name2doc x, pretty ":", sty2doc ty])
binding2doc [(xs, ty)] = parens (sep [sep $ map name2doc xs, pretty ":", sty2doc ty])
binding2doc (arg : args) = sep [binding2doc [arg], binding2doc args]


-- | Pretty printing de términos azucarados (String)
spp :: MonadFD4 m => Term -> m String
spp t = do
       gdecl <- gets glb
       return (render . t2doc False $ resugar $ openAll (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

-- | Pretty printing de declaraciones azucaradas
sppDecl :: MonadFD4 m => SDecl -> m String
sppDecl (STypeDecl _ n sty) =
  return (render $ sep [defColor (pretty "type")
                       , nameColor (pretty n)
                       , defColor (pretty "=")
                       , sty2doc sty])
sppDecl (SDecl _ _ v [] vty t) =
  return (render $ sep [defColor (pretty "let")
                       , name2doc v
                       , defColor (pretty ":")
                       , sty2doc vty
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False t))
sppDecl (SDecl _ r f args fty t) =
  return (render $ sep [if r then defColor (pretty "let rec") else defColor (pretty "let")
                       , name2doc f
                       , binding2doc args
                       , defColor (pretty ":")
                       , sty2doc fty
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False t))

resugarDecl :: MonadFD4 m => Decl Term -> m SDecl
resugarDecl (Decl i n ty body) = do
  gdecl <- gets glb
  let body' = resugar (openAll (map declName gdecl) body)
      sty = resugarTy ty
  case body' of
    SLam _ args t' -> return $ SDecl i False n args (getCodom sty args) t'
    SFix _ _ _ args t' -> return $ SDecl i True n args (getCodom sty args) t'
    _ -> return $ SDecl i False n [] sty body'

resugar :: NTerm -> STerm
resugar (V i v) = SV i v
resugar (Const i c) = SConst i c
resugar (IfZ i c t e) = SIfZ i (resugar c) (resugar t) (resugar e)
resugar (Print i str t) = SPrint i str (resugar t)
resugar (BinaryOp i o t u) = SBinaryOp i o (resugar t) (resugar u)
resugar (App i h a) = SApp i (resugar h) (resugar a)
resugar (Lam i v ty t) =
  let ty' = resugarTy ty
      t' = resugar t
  in case t' of
    SLam _ ((vs, vty) : args) t2 -> if ty' == vty then SLam i ((v : vs, vty) : args) t2
                                                  else SLam i (([v], ty') : (vs, vty) : args) t2
    SPrint _ str (SV _ v')       -> if v == v' then SUnPrint i str else SLam i [([v],ty')] t'
    _                            -> SLam i [([v],ty')] t'
resugar (Fix i f fty x xty t) =
  let fty' = resugarTy fty
      xty' = resugarTy xty
      t' = resugar t
  in case t' of
    SLam _ ((vs, vty) : args) t2 -> if xty' == vty then SFix i f fty' ((x : vs, vty) : args) t2
                                                   else SFix i f fty' (([x], xty') : (vs, vty) : args) t2
    _                            -> SFix i f fty' [([x],xty')] t'
resugar (Let i v vty def body) =
  let vty' = resugarTy vty
      def' = resugar def
      body' = resugar body
  in case def' of
    SFix _ f fty args t' -> SLet i True f args (getCodom vty' args) t' body'
    SLam _ args t'       -> SLet i False v args (getCodom vty' args) t' body'
    _                    -> SLet i False v [] vty' def' body'

resugarTy :: Ty -> STy
resugarTy NatTy = SNatTy
resugarTy (FunTy t1 t2) = SFunTy (resugarTy t1) (resugarTy t2)

getCodom :: STy -> [([Name], STy)] -> STy
getCodom SNatTy _ = SNatTy
getCodom (SFunTy t1 t2) [([_], ty)] = if t1 == ty then t2 else SDecTy "a"
getCodom (SFunTy t1 t2) [((_ : vs), ty)] = if t1 == ty then getCodom t2 [(vs,ty)] else SDecTy "b"
getCodom (SFunTy t1 t2) ((vs,ty) : args) = if t1 == ty then getCodom (getCodom (SFunTy t1 t2) [(vs,ty)]) args else SDecTy "c"

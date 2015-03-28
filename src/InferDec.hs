-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE NoMonomorphismRestriction,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             OverloadedStrings,
             TemplateHaskell,
             CPP
    #-}
-----------------------------------------------------------------------------
--
-- Module      :  InferDec
-- Copyright   :  BSD
-- License     :  AllRightsReserved
--
-- Maintainer  :  Ki Yung Ahn
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module InferDec where

import Syntax
import Parser ( Dec(..), LIdent(..), UIdent(..), DataAlt(..), )
import Parser ( type2Ty, term2Tm, kind2Ki )
-- import qualified Parser as P
import Infer hiding (trace)
import Unify
#define uapply (foldl' (flip (.)) id . map (uncurry subst))

import Data.Char
import Data.List
import Data.Either
import Control.Monad
import Control.Monad.Error
import Control.Monad.Trans
import Control.Applicative
import Unbound.LocallyNameless ( unbind, bind, fresh, string2Name, aeq )
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Generics.RepLib.Unify hiding (solveUnification)
import GHC.Exts( IsString(..) )
-- import Debug.Trace
trace :: String -> a -> a
trace _ a = a

-- TODO raise error when tring to generalize undefined Con or TCon names
-- TODO check uniqueness of TCon and Con names (not yet checking uniqueness?)

tiDecs ds = foldl1 (>=>) (map tiDec ds)

-- TODO not checking wheter there are TyName with backquote in t outside { }.
-- It should be only TmName inside { } which can be backquote var.
-- I think current implementation does catch this kind of error eventually
-- but I expect that the error message would be misterious.

-- kind2Ki' env = substBackquote env . kind2Ki
kind2Ki' = kind2Ki
-- type2Ty' env = substBackquote env . type2Ty
type2Ty' = type2Ty
-- term2Tm' env = substBackquote env . term2Tm
term2Tm' = term2Tm


tiDec :: Dec -> (KCtx,Ctx,Env) -> TI (KCtx,Ctx,Env)
tiDec (Def (LIdent x) t) (kctx,ictx,env)
  | head x == '`' = throwError(strMsg $ show x++
                                      " backquoted variable not allowed")
tiDec (Def (LIdent x) t) (kctx,ictx,env) = trace ("\nDef "++ show x++" *****") $
  do let tm = term2Tm' t
     ty <- ti kctx ictx tm
           `catchErrorThrowWithMsg`
              (++ "\n\t" ++ "when checking defintion of " ++ x)
     u <- getSubstTy
     tysch <- closeTy kctx (filter (isUpper.head.show.fst) ictx) (uapply u ty)
     () <- trace (show (x, snd $ unsafeUnbind tysch)) $ return ()
     let ictx' = (string2Name x, tysch) : ictx
         env'  = (string2Name x, envApply env tm) : env
     u <- getSubstTy
     () <- trace ("length u = "++show(length u)) $ return ()
     return (kctx,ictx',env')
tiDec (Data (UIdent tc) is dAlts) (kctx,ictx,env) =
 -- trace ("\ntiDec "++tc) $
  do kArgSigs <- sequence $
                   do LIdent a <- is -- list monad
                      return $ (,) (string2Name a)
                               <$> (KVar <$> fresh "k")
     let kArgSigs' = map (fmap monoKi) kArgSigs
     mapM_ (kiDAlt (kArgSigs' ++ kctx) ictx) dAlts
     u <- getSubstTy
     tcSig <- (,) (string2Name tc) <$>
                  (closeKi kctx []
                       (uapply u $ foldr KArr Star (map snd kArgSigs)))
     let kctx' = tcSig : kctx
     ictx' <- (++ ictx) <$>
                  sequence
                    [ (,) (string2Name c) <$>
                          (closeTy kctx' ictx_upper
                               (uapply u $ foldr TArr retTy (map type2Ty' ts)) )
                     | DAlt (UIdent c) ts <- reverse dAlts ]
     u <- getSubstTy
     () <- trace ("length u = "++show(length u)) $ return ()
     return (kctx',ictx',env)
  where
  ictx_upper = filter (isUpper.head.show.fst) ictx
  retTy = foldl TApp (TCon(string2Name tc)) $
                     do LIdent a <- is -- list monad
                        return $ TVar(string2Name a)

kiDAlt :: KCtx -> Ctx -> DataAlt -> KI ()
kiDAlt kctx ictx (DAlt _ ts) =
  do ks <- mapM (ki kctx) (map type2Ty' ts)
     unifyManyKi (zip (repeat Star) ks)

evDecs env (Data _ _ _ : ds)       = evDecs env ds
-- evDecs env (Gadt _ _ _ _ : ds)     = evDecs env ds
evDecs env (Def (LIdent x) t : ds) = do v <- ev env (term2Tm t)
                                        -- v <- norm env (term2Tm t)
                                        evDecs ((string2Name x, v) : env) ds
evDecs env []                      = return env


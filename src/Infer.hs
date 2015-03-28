-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE CPP, TemplateHaskell,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             OverlappingInstances,
             IncoherentInstances,
             OverloadedStrings,
             GADTs,
             NoMonomorphismRestriction,
             NoMonoLocalBinds,
             ScopedTypeVariables
  #-}

module Infer where

import Syntax
import Parser (type2Ty,ty2Type)
import Unify
#define uapply (foldl' (flip (.)) id . map (uncurry subst))

import Data.Char
import Data.List
import Control.Lens
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.State
import Generics.RepLib.Unify hiding (solveUnification)
import Unbound.LocallyNameless hiding (subst, Con, union, fv)
import qualified Unbound.LocallyNameless as LN
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import GHC.Exts( IsString(..) )
-- import Debug.Trace
trace :: String -> a -> a
trace _ a = a

fv = filter (not . isUpper . head . name2String) . LN.fv

catchErrorThrowWithMsg m f = m `catchError` (\e -> throwError . strMsg $ f e)

envApply env = foldr (.) id (map (uncurry LN.subst) env)

type KCtx = [(TyName,KiSch)]
type KI = FreshMT (ErrorT UnifyError (State ( UnificationState TyName Ty
                                            , UnificationState KiName Ki
                                            , [(TyName,Ki)] )))
type KiSch = Bind [KiName] Ki

unifyKi k1 k2 = lift $ zoom _2 $ unify k1 k2
unifyTy t1 t2 = lift $ zoom _1 $ unify t1 t2

unifyManyKi = lift . zoom _2 . unifyMany
unifyManyTy = lift . zoom _1 . unifyMany

getSubstKi = lift $ zoom _2 $ getSubst
getSubstTy = lift $ zoom _1 $ getSubst

getFreshBinds = lift $ zoom _3 $ get
modifyFreshBinds = lift . zoom _3 . modify

ki :: KCtx -> Ty -> KI Ki
ki kctx (TVar x)
   | head(show x) == '`' = throwError(strMsg $ show x++
                                      " backquoted variable not allowed (ki)")
ki kctx (TVar x) =
  case lookup x kctx of
    Just kisch -> return =<< freshKiInst kisch -- ki vars must be simple though
    Nothing -> do
      ps <- getFreshBinds
      case lookup x ps of
        Just k -> return k
        Nothing -> throwError(strMsg $ "ty var "++show x++" undefined tyvar")
ki kctx (TCon x) =
  case lookup x kctx of
    Just kisch -> return =<< freshKiInst kisch
    Nothing -> do
      ps <- getFreshBinds
      case lookup x ps of
        Just k -> return k
        Nothing -> throwError(strMsg $ "ty con "++show x++" undefined tycon")
ki kctx (TArr t1 t2) =
  do k1 <- ki kctx t1
     k2 <- ki kctx t2
     unifyKi Star k1
     unifyKi Star k2
     return Star
ki kctx (TApp t1 t2) =
  do k1 <- ki kctx t1
     k2 <- ki kctx t2
     k <- KVar <$> fresh "k_TApp_"
     unifyKi (KArr k2 k) k1
     return k
ki kctx (TFix t) =
  do k1 <- ki kctx t
     k <- KVar <$> fresh "k_TFix_"
     unifyKi (KArr k k) k1
     return k

type Ctx = [(TmName,TySch)]
type TI = KI -- same as kind infer monad
type TySch = Bind [TyName] Ty

ti :: KCtx -> Ctx -> Tm -> TI Ty
ti kctx ctx (Var x)
       | head(show x) == '`' = throwError(strMsg $ show x++
                                 " backquoted variable not allowed (ti)")
ti kctx ctx (Var x) =
  case lookup x ctx of
    Just tysch -> return =<< freshTyInst tysch
    Nothing -> throwError(strMsg $ show x++" undefined var")
ti kctx ctx (Con x) =
  case lookup x ctx of
    Just tysch -> return =<< freshTyInst tysch
    Nothing -> throwError(strMsg $ show x++" undefined con")
ti kctx ctx e@(In m t)
  | m < 0     = throwError(strMsg $ show e ++ " has negative number")
  | otherwise =
    do ty <- ti kctx ctx t
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t)
       let m_ = fromInteger m
       is <- sequence $ replicate m_ (TVar <$> freshTyName' "t_In_")
       ty1 <- TVar <$> freshTyName' "t"
       unifyTy (foldl TApp ty1 (TFix ty1 : is)) ty
       return $ foldl TApp (TFix ty1) is
ti kctx ctx (MPr b) =
  do ((f,cast), Alt mphi as) <- unbind b
     k <- fresh "k"
     r <- freshTyName "_r" (KVar k)
     t <- freshTyName' "t"
     mphi' <- freshenMPhi kctx mphi
     (is, tyret) <- case mphi' of Nothing  -> (,) [] <$> (TVar <$> freshTyName "_b" Star)
                                  Just phi -> unbind phi
     let tyf    = foldl TApp (TCon r) (map TVar is) `TArr` tyret
     let tytm   = foldl TApp (TVar t) (TCon r : map TVar is) `TArr` tyret
     let kctx' = (r, monoKi $ KVar k) : kctx
     tyfsch <- case mphi' of
                 Nothing -> return (monoTy tyf)
                 _       ->                                  -- [] ??
                   do (vs,_) <- unsafeUnbind <$> closeTy kctx' ctx tyret
                      ps <- sequence $ [(,) x <$> (KVar <$> fresh "k") | x<-(is++vs)]
                      modifyFreshBinds (ps++)
                      () <- trace ("\tis = "++show is) $ return ()
                      () <- trace ("\tvs = "++show vs) $ return ()
                      () <- trace ("\ttyf = "++show tyf) $ return ()
                      return $ bind (union is vs) tyf
     let tycast = foldl TApp (TCon r) (map TVar is) `TArr`
                  foldl TApp (TFix (TVar t)) (map TVar is)
     let ctx' = (f,tyfsch) : (cast,bind is tycast) : ctx
     () <- trace ("\tkctx' = "++show kctx') $ return ()
     () <- trace ("\tctx' = "++show ctx') $ return ()
     tytm' <- tiAlts 1 kctx' ctx' (Alt mphi' as)
     unifyTy tytm tytm'
     u <- getSubstTy
     let ty = uapply u $
                foldl TApp (TFix(TVar t)) (map TVar is) `TArr` tyret
     when (r `elem` fv ty) (throwError . strMsg $
             "abstract type variable "++show r++" cannot escape in type "++
             show ty ++" of "++show(MPr b) )
     return ty
ti kctx ctx (Lam b) =
  do (x, t) <- unbind b
     ty1 <- TVar <$> freshTyName "_" Star
     ty2 <- ti kctx ((x, monoTy ty1) : ctx) t
     -- () <- trace ("\n\tkctx' = "++show kctx) $ return ()
     -- () <- trace ("\n\tictx' = "++show ictx) $ return ()
     ps <- getFreshBinds
     () <- trace ("\n\tps = "++show ps) $ return ()
     unifyKi Star =<< ki kctx ty2
             `catchErrorThrowWithMsg`
                (++ "\n\t" ++ "when checking kind of " ++ show ty2
                 ++ "\n" ++ "kctx = " ++ show kctx
                 ++ "\n" ++ "ctx = " ++ show ((x, monoTy ty1) : ctx)
                )
     return (TArr ty1 ty2)
ti kctx ctx (App t1 t2) =
  do ty1 <- ti kctx ctx t1
             `catchErrorThrowWithMsg`
                (++ "\n\t" ++ "when checking type of " ++ show t1)
     ty2 <- ti kctx ctx t2
             `catchErrorThrowWithMsg`
                (++ "\n\t" ++ "when checking type of " ++ show t2
                 ++ "\n" ++ "kctx = " ++ show kctx
                 ++ "\n" ++ "ctx = " ++ show ctx
                )
     ty <- TVar <$> freshTyName "a" Star
     unifyTy (TArr ty2 ty) ty1
     return ty
ti kctx ctx (Let b) =
  do ((x, Embed t1), t2) <- unbind b
     ty <- ti kctx ctx t1
            `catchErrorThrowWithMsg`
               (++ "\n\t" ++ "when checking type of " ++ show t1)
     u <- getSubstTy
     tysch <- closeTy kctx ctx (uapply u ty)
     ti kctx ((x, tysch) : ctx) t2
ti kctx ctx (Alt _ []) = throwError(strMsg "empty Alts") -- TODO empty type?
ti kctx ctx e@(Alt Nothing as) = tiAlts 0 kctx ctx e
ti kctx ctx (Alt (Just phi) as) =
  do phi <- freshenPhi kctx phi
     tiAlts 0 kctx ctx (Alt (Just phi) as)

-- freshTmName' x = freshTmName x =<< (Var <$> freshTyName "t" Star)
--
-- freshTmName x t = do nm <- fresh x
--                      modifyFreshBinds ((nm,t) :)
--                      return nm

freshTyName' x = freshTyName x =<< (KVar <$> fresh "k")

freshTyName x k = do
  nm <- fresh x
  modifyFreshBinds ((nm,k) :)
  () <- trace ("\nfreshTyName: adding "++show (nm,k)++" to ps") $ return ()
  return nm

freshKiInst sch = do
  (_, k) <- unbind sch
  return k

freshTyInst sch = do
  (vs, ty) <- unbind sch
  ps <- sequence $ [(,) x <$> (KVar <$> fresh "k_TyInst_") | x<-vs]
  modifyFreshBinds (ps++)
  return ty

freshenPhi kctx phi =
  do (xs,phi') <- unbind (bind fvPhi phi)
     ps <- sequence $ [(,) x <$> (KVar <$> fresh "k_frPhi_") | x<-xs]
     modifyFreshBinds (ps++)
     return phi'
  where
  (is,ty) = unsafeUnbind phi
  fvPhi =  nub $ fv phi \\ fv kctx :: [TyName]

freshenMPhi kctx Nothing    = return Nothing
freshenMPhi kctx (Just phi) = Just <$> freshenPhi kctx phi

monoKi = bind []

monoTy = bind []

closeTy kctx ctx ty = do
  return $ bind fvTy ty
  where
  fvTy = nub $ fv ty \\ (fv ctx ++ fv kctx)


closeKi kctx as k = do -- as are extra vars that should not to generalize
  return $ bind fvKi k
  where
  fvKi = nub $ fv k \\ (fv kctx ++ as)

tiAlts n kctx ctx (Alt Nothing as) =  -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ctx Nothing) as
     unifyManyTy (zip tys (tail tys))
     return (head tys)
tiAlts n kctx ctx (Alt (Just phi) as) =  -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ctx (Just phi)) as
     u <- getSubstTy
     let (tcon : args) =
            tApp2list $ case (head tys) of TArr t _ -> uapply u t
     (is, rngty) <- unbind phi
     when (n + length is < length args)
        $ throwError(strMsg $ "too many indices in "++show phi)
     let args' = replaceSuffix args (map TVar is)
     let domty = foldl TApp tcon args'
     let tysch = bind is (TArr domty rngty)
     tys' <- mapM freshTyInst (replicate (length as) tysch)
     unifyManyTy (zip tys' tys)
     return =<< freshTyInst tysch

kargs = unfoldr (\k -> case k of { KArr k1 k2 -> Just(k1,k2) ; _ -> Nothing })

arity nm kctx = length (kargs k)
   where Just k = lookup nm kctx

unfoldTArr (TArr t1 t2) = t1 : unfoldTArr t2
unfoldTArr ty           = [ty]

unfoldTApp (TApp t1 t2) = unfoldTApp t1 ++ [t2]
unfoldTApp ty           = [ty]


replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 targ) = tApp2list ty1 ++ [targ]
tApp2list ty             = [ty]

app2list (App t1 t2) = app2list t1 ++ [t2]
app2list t           = [t]

tiAlt :: KCtx -> Ctx -> Maybe IxMap -> (TmName,Bind [TmName] Tm) -> TI Ty
tiAlt kctx ctx mphi (x,b) =
  do xTy <- case lookup x ctx of
                 Nothing -> throwError . strMsg $ show x ++ " undefined"
                 Just xt -> freshTyInst xt
     u <- trace ("++++++++"++show x++"++++++++++++++\n"++show mphi++"\n xTy = "++show xTy) getSubstTy
     let xty = uapply u xTy
     let xtyUnfold = unfoldTArr xty
     let (xtyArgs, xtyRet) = (init xtyUnfold, last xtyUnfold)
     (u,is,bodyTy,mt) <- case trace (show(xty,xtyRet,mphi)) mphi of
        Nothing  -> return (u,[],undefined,Nothing)
        Just phi -> do
          (is, bodyTy) <- unbind phi
          ps <- sequence $ [(,) x <$> (KVar <$> fresh "k_AltR_") | x<-is]
          modifyFreshBinds (ps++)
          t <- TVar <$> freshTyName' "t"
          unifyTy (foldl TApp t $ map TVar is) xtyRet
          u <- getSubstTy
          let bodyTy' = uapply u bodyTy
          return (u,is,bodyTy',Just t)
     let xty_ = uapply u xty
     let xty = case trace ("xty_ = "++show xty_) () of _ -> xty_
     let xtyUnfold = unfoldTArr xty
     let (xtyArgs, xtyRet) = (init xtyUnfold, last xtyUnfold)
     let xTyVars = nub $ fv xty \\ (fv kctx ++ fv ctx)
     let eTyVars = xTyVars \\ fv xtyRet :: [TyName]

     () <- trace ("evars : "++show eTyVars) $ return ()

     let fvTyPhi = case mt of
                     Nothing -> []
                     Just _  -> nub $ (fv bodyTy \\ fv is) \\ fv kctx

     -- substitute existential vars as bogus TCon or Con to avoid unification
     -- TODO generalized existentials???
     let xty' = foldr (.) id [LN.subst nm (TCon nm) | nm <- eTyVars] xty
     () <- trace ("TODO " ++ show(ty2Type xty')) $ return ()
     let bodyTy' = foldr (.) id [LN.subst nm (TCon nm) | nm <- eTyVars] bodyTy
     let xtyArgs' = trace (show (xty',init (unfoldTArr xty'))) $ init (unfoldTArr xty')
     let kctx' = kctx
     -- -- adding existental TCon or Con to context seems unnecessary
     -- kctx' <- (++) <$> sequence [(,) nm <$> (Var <$> fresh "k") | nm <- eTyVars]
     --               <*> return kctx
     -- ictx' <- (++) <$> sequence [(,) nm <$> (monoTy . Var <$> fresh "c")
     --                             | nm <- eTmVars]
     --               <*> return ictx
     (ns,t) <- unbind b
     let ctx' = trace (show ns ++", "++ show xtyArgs') $ zip ns (map monoTy xtyArgs') ++ ctx
     () <- trace "zzaaa" $ return ()
     domty <- ti kctx' ctx' (foldl1 App (Con x : map Var ns))
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of "
                  ++ show (foldl1 App (Con x : map Var ns)))
     rngty <- ti kctx' ctx' t
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t)
     () <- trace ("zzaaa2\t"++show xtyRet++" =?= "++show domty) $ return ()
     unifyTy xtyRet domty
     () <- trace "zzaaa3" $ return ()
     case mt of
       Nothing  -> return ()
       Just _   ->
                do () <- trace ("zzaaa4\t"++
                                show bodyTy'++" =?= "++show rngty) $ return ()
                   unifyTy bodyTy' rngty
     u <- getSubstTy
     () <- trace "zzaaa5" $ return ()
     let ty = uapply u (TArr domty rngty)
     let TArr domty rngty = ty
     let eRetVars = intersect eTyVars (fv ty)
     unless (trace (show(ty,eRetVars)) $ null eRetVars)
            (throwError . strMsg $ "rigid variables "++ show eRetVars ++
                                   " in the return type "++ show rngty ++
                                   " of "++ show t)
     u <- getSubstTy
     unless (null $ filter (\(x,t)-> elem x fvTyPhi
                                  && case t of {TVar _ -> False; _ -> True}) u)
       (throwError . strMsg $ "polymorphic vars in phi cannot be specialized "
             ++"\n\t"
             ++show(filter (\(x,t)-> elem x fvTyPhi
                                  && case t of {TVar _ -> False; _ -> True}) u))
     case mphi of
       Nothing -> trace
                    ("return type: "++show ty ++ "\n"++
                     show(eTyVars::[TyName]
                         ,fv xtyRet::[TyName]
                         ,(eTyVars)\\fv xtyRet::[TyName])
                     ++
                     "\n\t"++ show(eTyVars)++" of "++show xtyRet
                           ++ show(fv xtyRet::[TyName])++" in "++show (x,b))
                    (return ty)
       Just phi -> do
         let Just t = trace
                        ("return type: "++show ty ++ "\n"++
                         show(eTyVars::[TyName]
                             ,fv xtyRet::[TyName]
                             ,(eTyVars)\\fv xtyRet::[TyName])
                         ++
                         "\n\t"++ show(eTyVars)++" of "++show xtyRet
                               ++ show(fv xtyRet::[TyName])++" in "++show (x,b))
                        mt
         let t' = uapply u t
         (is,bodyTy) <- unbind phi
         let bodyTy' = uapply u bodyTy
         return (foldl TApp t' (map TVar is) `TArr` bodyTy')
  -- catching error from do ...
  `catchErrorThrowWithMsg` (++ "\n\t" ++ "when checking case " ++ show x)


lam x t = Lam (bind x t)

idTm = lam "x" (Var "x")

nullState = (UState [] [], UState [] [], [])


-- runUS = runUSwith nullState

runUSwith st0 st = -- fst (runState st st0)
                   uapply (uSubst s) e where (e,(_,s,_)) = runState st st0

runTI = runTIwith nullState []

runTIwith stUS st = runUSwith stUS . runErrorT . runFreshMT


-- ti' ctx = runTI . ti [] [] [] ctx
--
-- ty = runTI $ ti [] [] [] [] (lam "x" (Var "x"))


unbindSch sch = snd (unsafeUnbind sch)


-- evaluation

type Env = [(TmName,Tm)]

sreturn env t = return $ foldr (.) id (map (uncurry LN.subst) env) t

ev env (Var x)
  | head(show x) == '`' = throwError(strMsg $ show x++
                                     " backquoted variable not allowed (ev)")
ev env (Var x) =
  case lookup x env of
    Nothing -> throwError(strMsg $ show x++" undefined")
    Just v  -> return v
ev env v@(Con x) = return v
ev env (In n t) = In n <$> ev env t
-- ev env v@(MIt b) = return v
ev env v@(MPr b) = return v
ev env v@(Lam b) = return v
ev env (App t1 t2) =
  do v1 <- ev env t1
     v2 <- ev env t2
     case v1 of
       Var x -> error $ show x ++ " (free variable): should never happen"
       Con _ -> return $ App v1 v2
       In _ _ -> return $ App v1 v2
       App _ _ -> return $ App v1 v2
       Lam b -> do (x, t) <- unbind b
                   let env' = (x,v2) : env
                   sreturn [(x,v2)] =<< ev env' t
--       MIt b -> do (f,t) <- unbind b
--                   let env' = (f,v1) : env
--                   let In _ v = v2
--                   sreturn [(f,v1)] =<< ev env' (App t v)
       MPr b -> do ((f,cast),t) <- unbind b
                   let env' = (f,v1) : (cast,idTm) : env
                   let In _ v = v2
                   sreturn [(f,v1),(cast,idTm)] =<< ev env' (App t v)
       Alt m as ->
         do let (Con c:vs) = app2list v2
            case lookup c as of
              Nothing -> throwError(strMsg $ show c++" undefined")
              Just b  ->
                do (xs,t) <- unbind b
                   let env' = zip xs vs ++ env
                   sreturn (zip xs vs) =<< ev env' t
ev env (Let b) = do ((x, Embed t1), t2) <- unbind b
                    v1 <- ev env t1
                    let env' = (x,v1) : env
                    sreturn [(x,v1)] =<< ev env' t2
ev env v@(Alt _ _) = return v


norm env v@(Var x)
  | head(show x) == '`' = throwError(strMsg $ show x++
                                     " backquoted variable not allowed (norm)")
norm env v@(Var x) =
  case lookup x env of
    Nothing -> return v
    Just v  -> return v
norm env v@(Con x) = return v
norm env (In n t) = In n <$> norm env t
-- norm env (MIt b) = do (xs,t) <- unbind b
--                       MIt <$> (bind xs <$> norm env t)
norm env (MPr b) = do (xs,t) <- unbind b
                      MPr <$> (bind xs <$> norm env t)
norm env (Lam b) = do (x, t) <- unbind b
                      Lam . bind x <$> norm env t
norm env (App t1 t2) =
  do v1 <- norm env t1
     v2 <- norm env t2
     case v1 of
       Var x -> return $ App v1 v2
       Con _ -> return $ App v1 v2
       In _ _ -> return $ App v1 v2
       App _ _ -> return $ App v1 v2
       Lam b ->
         do (x, t) <- unbind b
            let env' = (x,v2) : env
            sreturn [(x,v2)] =<< norm env' t
--       MIt b ->
--         do (f,t) <- unbind b
--            let env' = (f,v1) : env
--            case v2 of
--              In _ v -> sreturn [(f,v1)] =<< norm env' (App t v)
--              _      -> return (App v1 v2)
       MPr b ->
         do ((f,cast),t) <- unbind b
            let env' = (f,v1) : (cast,idTm) : env
            case v2 of
              In _ v -> sreturn [(f,v1),(cast,idTm)] =<< norm env' (App t v)
              _      -> return (App v1 v2)
       Alt m as ->
         do let (Con c:vs) = app2list v2
            case lookup c as of
              Nothing -> throwError(strMsg $ show c++" undefined")
              Just b  ->
                do (xs,t) <- unbind b
                   let env' = zip xs vs ++ env
                   sreturn (zip xs vs) =<< norm env' t
norm env (Let b) = do ((x, Embed t1), t2) <- unbind b
                      v1 <- norm env t1
                      let env' = (x,v1) : env
                      sreturn [(x,v1)] =<< norm env' t2
norm env (Alt m as) =
  Alt m <$> sequence [ do (xs,t) <- unbind b
                          (,) c <$> (bind xs <$> norm env t)
                      | (c,b) <- as ]

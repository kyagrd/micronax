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
             ScopedTypeVariables
  #-}

-----------------------------------------------------------------------------
--
-- Module      :  Unify
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

module Unify where

import Syntax
import Data.List
import Data.Maybe
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.State
import Language.LBNF.Runtime hiding (printTree)
import Parser (printTree)
import Generics.RepLib.Unify hiding (solveUnification)
import Unbound.LocallyNameless hiding (subst, Con, union)

-- uapply may cause problem becuase of subst
-- I had to inline this in mininax project
-- Let's see how it goes
#define uapply (foldl' (flip (.)) id . map (uncurry subst))

instance HasVar (Name Ki) Ki where
  is_var (KVar nm) = Just nm
  is_var _ = Nothing
  var = KVar

instance HasVar (Name Ty) Ty where
  is_var (TVar nm) = Just nm
  is_var _ = Nothing
  var = TVar

instance HasVar (Name Ty) Tm where


instance (Eq n, Show n, Show a, HasVar n a) => Unify n a String where
   unifyStep _ = unifyStepEq

instance (Eq n, Show n, Show a, HasVar n a) => Unify n a (Name s) where
   unifyStep _ = unifyStepEq

instance (Alpha n, Eq n, Show n, Alpha a, HasVar n a, Rep1 (UnifySubD n a) a) => Unify n a (Bind n a) where
   unifyStep _ b1 b2
       | b1 `aeq` b2 = return ()
       | otherwise   =
           do (e1,e2) <- runFreshMT $
                         do { (_,e1) <- unbind b1
                            ; (_,e2) <- unbind b2
                            ; return (e1,e2) }
              -- trace ("trace in instance Unify n a (Bind n a): " ++ show (e1,e2)) $
              unifyStep undefined e1 e2

--------------------------------------------
----- maybe we don't need this
--------------------------------------------
-- instance (Eq n, Show n, HasVar n Ty) => Unify n Ty Ty where
--    unifyStep (dum :: Proxy(n,Ty)) a1 a2 =
--       -- trace ("trace 2 in instance Unify n PSUT PSUT): " ++ show (a1,a2)) $
--        case ((is_var a1) :: Maybe n, (is_var a2) :: Maybe n) of
--            (Just n1, Just n2) ->  if n1 == n2
--                                     then return ()
--                                     else addSub n1 (var n2);
--            (Just n1, _) -> addSub n1 a2
--            (_, Just n2) -> addSub n2 a1
--            (_, _) -> unifyStepR1 rep1 dum a1 a2
--        where
--        addSub n t = extendSubstitution (n, t)

-- modified the Generics.Replib.Unify version to throwError rather than error
-- TODO Can be even better if we pass curret stat rather than (Ustate cs [])?
--      somehow this idea doesn't work ... [] replaced with current subst loops
-- solveUnification :: (HasVar n a, Eq n, Show n, Show a, Rep1 (UnifySubD n a) a) => [(a, a)] -> Either UnifyError [(n, a)]

solveUnification (eqs :: [(a, a)]) =
     case r of Left e  -> throwError e
               Right _ -> return $ uSubst final
     where
     (r, final) = runState (runErrorT rwConstraints) (UState cs [])
     cs = [(UC dict a1 a2) | (a1, a2) <- eqs]
     rwConstraints :: UM n a ()
     rwConstraints =
       do c <- dequeueConstraint
          case c of Just (UC d a1 a2) ->
                            do unifyStepD d (undefined :: Proxy (n, a)) a1 a2
                               rwConstraints
                    Nothing -> return ()

mgu t1 t2 = do
  case solveUnification [(t1, t2)] of
    Left e  -> throwError (strMsg $ e ++ "\n\t"++ errstr)
    Right u -> return u
  where errstr = "cannot unify "++printTree t1++" and "++printTree t2

mguMany ps = do
  case solveUnification ps of
    Left e  -> throwError (strMsg $ e ++ "\n\t" ++ errstr)
    Right u -> return u
  where errstr = "cannot unify \n" ++
                 ( concat [ "\t"++printTree t1++" and "++printTree t2++"\n"
                          | (t1,t2)<-ps ] )

lift2 = lift . lift
getSubst = do { UState _ s <- lift get; return s }

extendSubst :: ( HasVar (Name a) a, Show a, Print a
               , Rep1 (UnifySubD (Name a) a) a) =>
               (Name a, a)
            -> ErrorT UnifyError (State (UnificationState (Name a) a)) ()
extendSubst (x,t)
  | isJust my && x < y = extendSubst (y,var x)
  | isJust my && x== y = return ()
  where my = is_var t
        y  = fromJust my
extendSubst (x,t) =
  do u <- getSubst
     case lookup x u of
       Nothing -> extendSubstitution (x,t)
       Just t' -> mapM_ extendSubst =<< mgu t t'

unify t1 t2 = -- trace ("unify ("++show t1++") ("++show t2++")") $
  do u <- getSubst
     mapM_ extendSubst =<< mgu (uapply u t1) (uapply u t2)

unifyMany ps = do u <- getSubst
                  mapM_ extendSubst =<< mguMany (map (uapply u) ps)



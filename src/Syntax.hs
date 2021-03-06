-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             OverloadedStrings,
             CPP #-}
-----------------------------------------------------------------------------
--
-- Module      :  Syntax
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


module Syntax
  ( KiName, Ki(..)
  , TyName, Ty(..)
  , TmName, Tm(..)
  , IxMap
  ) where

import Unbound.LocallyNameless hiding (Con)
import GHC.Exts( IsString(..) )

type KiName = Name Ki
type TyName = Name Ty
type TmName = Name Tm

data Ki
  = KVar KiName
  | Star
  | KArr Ki Ki

data Ty
  = TVar TyName
  | TCon TyName
  | TArr Ty Ty
  | TApp Ty Ty
  | TFix Ty -- Ty must be TCon or applications headed TCon

data Tm
  = Var TmName
  | Con TmName
  | In Integer Tm
  | MPr (Bind (TmName,TmName) Tm) -- Tm must be Alt
  | Lam (Bind TmName Tm)
  | App Tm Tm
  | Let (Bind (TmName, Embed Tm) Tm)
  | Alt (Maybe IxMap) [(TmName, Bind [TmName] Tm)]

type IxMap = Bind [TyName] Ty

$(derive [''Ki, ''Ty, ''Tm])

instance Rep a => IsString (Name a) where
  fromString = string2Name

-- Alpha and Sbust instances are in Parser module
-- in order to avoid mutually recursive module imports
-- since Show class instantces for Ki, Ty, Tm depends on LBNF functions

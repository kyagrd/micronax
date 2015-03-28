-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE NamedFieldPuns, RecordWildCards,
             CPP, TemplateHaskell, QuasiQuotes, NoMonomorphismRestriction #-}
-----------------------------------------------------------------------------
--
-- Module      :  Main
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


module Main where
#ifdef MAIN_FUNCTION
import System.Exit (exitFailure)
import Test.QuickCheck.All (quickCheckAll)
#endif

import Syntax
import Parser
import Infer
import InferDec

import Language.LBNF.Runtime hiding (printTree)
import System.IO
import Options.Applicative

import Control.Monad
import Control.Applicative
-- import Control.Monad.Trans
import Control.Monad.Error
-- import Control.Monad.Identity


import Unbound.LocallyNameless

program =
   [prog|
    data Unit = Unit ;
    data Bool = False | True ;
    data Maybe a = Nothing | Just a ;
    data Either a b = Left a | Right b ;
    data Pair a b = Pair a b ;
    data N r = Z | S r ;
    data L a r = N | C a r ;
    data P r a = PN | PC a (r (Pair a a)) ;
    data MM = MM (Mu N);
    data MMM a = MMM (Mu P a);
    id = \x -> x ;
    x = id;
    z = {True -> True; False -> False};
    z2 = {Nothing -> False; Just x -> True};
    b = True ;
    c = x b;
    p = Pair ;
    z3 = Pair True False;
    zero = In 0 Z ;
    succ = \n -> In 0 (S n) ;
    nil = In 0 N ;
    cons = \x -> \xs -> In 0 (C x xs) ;
    pnil = In 1 PN ;
    pcons = \x -> \xs -> In 1 (PC x xs) ;
    -- ppnil = In 0 PN ;
    one = succ zero ;
    two = succ one ;
    three = succ two ;
    z5 = cons nil nil ;
    z6 = cons True nil ;
    z7 = pcons True (pcons (Pair False True) pnil) ;
    z8 = pcons one (pcons (Pair two three) pnil) ;
    flip = \f -> \x -> \y -> f y x;
    plus = mpr add cast { Z   -> \m -> m
                        ; S n -> \m -> succ (add n m) } ;
    length = mpr len cast { N -> zero; C x xs -> succ (len xs) } ;
    psum = mpr sum cast { a . (a -> Mu N) -> Mu N }
            { PN      -> \f -> zero
            ; PC x xs -> \f -> plus (f x)
                                    (sum xs {Pair a b -> plus (f a) (f b)} )
            } ;
    n4 = plus (plus one one) (plus one one) ;
    n5 = length z6 ;
    n6 = length z5 ;
    n7 = psum z8 id ;
    n8 = flip psum
   |]

k1 = [kind| * -> * -> * |]
k2 = [kind| * -> k -> * |]

t1 = [term| \ x -> x |]
t2 = [term| { a . a -> b } { PN -> zero ; PC x xs -> four } |]

t2' = term2Tm t2

t2'' = subst (string2Name "b") (type2Ty [type| a -> a |]) t2'


data CmdArgs = CmdArgs
  { flagKi :: Bool
  , flagTi :: Bool
  , flagEv :: Bool
  , flagAll :: Bool
  , argFilePath :: Maybe String
  }

cmdArgs = CmdArgs <$> kiFlag <*> tiFlag <*> evFlag <*> allFlag <*> filepathArg
  where
  kiFlag = switch
     $ long "kind" <> short 'k'
    <> help "Kind Inference for type constructors"
  tiFlag = switch
     $ long "type" <> short 't'
    <> help "Type Inference for data constructors and definitions"
  evFlag = switch
     $ long "eval" <> short 'e'
    <> help "Evaluate definitions"
  allFlag = switch
     $ long "all" <> short 'a'
    <> help "Kind Infer, Type Infer, and Evaluate the program"
  filepathArg = optional $ argument str
     $ metavar "FILE"
    <> help "File path argument"




--exeMain :: IO ()
--exeMain = do
--  putStrLn $ show t2
--  putStrLn $ printTree t2
--  print t2'
--  print t2''
--  putStrLn $ show k1
--  putStrLn $ printTree k1
--  putStrLn $ show k2
--  putStrLn $ printTree k2
--  putStrLn $ show program
--  putStrLn $ printTree program



tiProg (Prog ds) = (kctx,ictx)
  where
  (kctx,ictx)
      = case (runTI $ do { (kctx,ictx,env) <- tiDecs ds ([],[],[])
                         ; return (kctx,ictx) }) of
            Left errMsg -> error errMsg
            Right (kctx,ictx) -> (kctx,ictx)

evProg (Prog ds) = do
  mapM_ putStrLn
      $ reverse [show x++" = "++ printTree t ++ " ;" | (x,t) <- evctx]
  return evctx
  where
    evctx = case (runFreshMT $ evDecs [] ds) of
              Left x -> error x
              Right x -> x


-- The default entry point
exeMain = execParser opts >>= greet
  where
    opts = info (helper <*> cmdArgs)
             (  fullDesc
             <> progDesc "mininax command line program"
             <> header "miniax - command line program for the mininax langauge"
             )

greet :: CmdArgs -> IO ()
greet (CmdArgs{..}) = do
  h <- maybe (return stdin) (\s -> openFile s ReadMode) argFilePath
  mp <- hProg h
  let program = case mp of { Ok p -> p; Bad msg -> error msg }
  let (kctx,ctx) = tiProg program
  -- print "================================"
  -- putStrLn ("length kctx = "++show(length kctx))
  -- mapM_ print (reverse $ kctx)
  -- print "================================"
  -- putStrLn ("length ctx = "++show(length ctx))
  -- mapM_ print (reverse $ ctx)
  -- print "================================"
  -- let uapply_u = uapply u
  when (flagAll || flagKi || (not flagEv && not flagTi))
     $ do { mapM_ putStrLn
                $ reverse [ show x++" : "++
                            (renderN 1 . prt 1)
                            -- (show . ty2Type)
                               ({- uapply_u $ -} unbindSch k )
                           | (x,k) <- kctx ]
          ; putStrLn ""
          }
  when (flagAll || flagTi || (not flagKi && not flagEv))
     $ do { mapM_ putStrLn
                $ reverse [ show x++" : "++
                            (renderN 1 . prt 1)
                            -- (show . ty2Type)
                               ({- uapply_u $ -} unbindSch t )
                           | (x,t) <- ctx ]
          ; putStrLn ""
          }

  when (flagAll || flagEv)
       (evProg program >> putStrLn "")



mygr file = greet $ CmdArgs{flagKi=True,flagTi=True,flagEv=False,flagAll=False
                           ,argFilePath=Just file}

mygr2 file = greet $ CmdArgs{flagKi=True,flagTi=True,flagEv=True,flagAll=True
                            ,argFilePath=Just file}






-- This is a clunky, but portable, way to use the same Main module file
-- for both an application and for unit tests.
-- MAIN_FUNCTION is preprocessor macro set to exeMain or testMain.
-- That way we can use the same file for both an application and for tests.
#ifndef MAIN_FUNCTION
#define MAIN_FUNCTION exeMain
#else
-- Entry point for unit tests.
testMain = do
    allPass <- $quickCheckAll -- Run QuickCheck on all prop_ functions
    unless allPass exitFailure
#endif
main = MAIN_FUNCTION


-- just a dummy QuickCheck property
prop_dummy b = not(not b) == b


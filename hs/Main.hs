{-# LANGUAGE CPP #-}
module Main where

import Pattern
import Grammar
import Parse
import Show
#if __GLASGOW_HASKELL__ >= 700
import System.Environment
#else
import System
#endif
import System.IO
import Data.Char (isSpace)
import Data.List (stripPrefix, span)

{- TODO:
 -   proper arg parsing
 -   pre-compute bodyWrap
 -   hook up wf checks
 -   check production table for duplicates
 -   extend model to handle duplicate atomic vars
 -}

data Command = Desugar SortName String
             | Resugar SortName String

commands = [("desugar ", Desugar),
            ("resugar ", Resugar)]

output str = do
  putStrLn str
  hFlush stdout
succeed t = output ("success: " ++ show t)
failure msg = output ("failure: " ++ msg)
problem msg = output ("error: " ++ msg)

getCommand line =
  tryCommands commands
  where
    tryCommands [] = Nothing
    tryCommands ((cmd, con):rest) =
      case stripPrefix cmd line of
        Nothing -> tryCommands rest
        Just s ->
          let (sn, s') = span (not . isSpace) s
              (_, s'') = span isSpace s' in
          Just (con (SortN sn) s'')

readTerm str (CompiledLanguage g) sn = do
  case parseTerm "(input)" str of
    Left err -> do
      problem ("invalid term" ++ show err)
      return Nothing
    Right t -> if termConforms g (SortName sn) t
               then return (Just t)
               else do
                 problem ("Nonconformant term: " ++ str)
                 return Nothing

showResult :: Either ResugarFailure Term -> IO ()
showResult (Left (ResugarError err)) = problem (show err)
showResult (Left msg) = failure (show msg)
showResult (Right t) = succeed t

mainLoop :: CompiledModule -> IO ()
mainLoop m@(CompiledModule l1 l2 ms) = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  line <- getLine
  case getCommand line of
    Nothing -> problem "invalid command"
    Just (Desugar sn s) -> do
      t <- readTerm s l2 sn
      case t of
        Nothing -> return ()
        Just t -> case expand ms t of
          Left err -> showResult (Left err)
          Right t ->
            let CompiledLanguage gt = l1 in
            if termConforms gt (SortName sn) t
            then succeed t
            else problem ("Your desugaring rules are incomplete on term: "
                          ++ showTerm False t "")
    Just (Resugar sn s) -> do
      t <- readTerm s l1 sn
      case t of
        Nothing -> return ()
        Just t -> showResult (unexpand ms t)
  mainLoop m

main = do
  -- TODO: proper arg parsing
  [filename] <- getArgs
  src <- readFile filename
  case parseModule filename src of
    Left err -> do
      problem ("Parse error in module: " ++ show err)
    Right m -> case compileModule m of
      Left err -> problem (show err)
      Right m -> mainLoop m

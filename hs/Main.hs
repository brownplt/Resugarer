module Main where

import Pattern
import Grammar
import Parse
import Show
import System
import System.IO
import Data.List (stripPrefix)

data Command = Desugar String
             | Resugar String

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
        Just s -> Just (con s)

readTerm str (g, s) = do
  case parseTerm "(input)" str of
    Left err -> do
      problem ("invalid term" ++ show err)
      return Nothing
    Right t -> if termConforms g (SortName s) t
               then return (Just t)
               else do
                 problem "nonconformant term!"
                 return Nothing

showResult (Left (ResugarError err)) = problem (show err)
showResult (Left msg) = failure (show msg)
showResult (Right t) = succeed t

mainLoop ms l1 l2 = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  line <- getLine
  case getCommand line of
    Nothing -> problem "invalid command"
    Just (Desugar s) -> do
      t <- readTerm s l2
      case t of
        Nothing -> return ()
        Just t -> showResult (expand ms t)
    Just (Resugar s) -> do
      t <- readTerm s l1
      case t of
        Nothing -> return ()
        Just t -> showResult (unexpand ms t)
  mainLoop ms l1 l2

main = do
  -- TODO: proper arg parsing
  [filename] <- getArgs
  src <- readFile filename
  case parseModule filename src of
    Left err -> do
      problem ("Parse error in module: " ++ show err)
    Right (Module (Language g1 s1) (Language g2 s2) rs) -> do
      hPutStr stderr "Checking your desugaring for completeness... "
      -- TODO: Implement completeness check.
      hPutStrLn stderr "Well, I'm sure it'll be fine."
      mainLoop (rulesToMacros rs)
               (grammarToConstructorTable g1, s1)
               (grammarToConstructorTable g2, s2)


module Main where

import Pattern
import Grammar
import Parse
import Show
import System
import Data.List (stripPrefix)

data Command = Desugar String
             | Resugar String

commands = [("desugar ", Desugar),
            ("resugar ", Resugar)]

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
      putStrLn "!invaid term: " >> putStrLn (show err)
      return Nothing
    Right t -> if termConforms g (SortName s) t
               then return (Just t)
               else do
                 putStrLn "!nonconformant term!"
                 return Nothing

mainLoop ms l1 l2 = do
  line <- getLine
  case getCommand line of
    Nothing -> putStrLn "!invalid command"
    Just (Desugar s) -> do
      t <- readTerm s l2
      case t of
        Nothing -> return ()
        Just t -> putStrLn (show (expand ms t))
    Just (Resugar s) -> do
      t <- readTerm s l1
      case t of
        Nothing -> return ()
        Just t -> putStrLn (show (unexpand ms t))
  mainLoop ms l1 l2

main = do
  -- TODO: proper arg parsing
  [filename] <- getArgs
  src <- readFile filename
  case parseModule filename src of
    Left err -> do
      putStrLn "Parse error in module:"
      putStrLn (show err)
    Right (Module (Language g1 s1) (Language g2 s2) rs) -> do
      putStr "Checking your desugaring for completeness... "
      -- TODO: Implement completeness check.
      putStrLn "Well, I'm sure it'll be fine."
      mainLoop (rulesToMacros rs)
               (grammarToConstructorTable g1, s1)
               (grammarToConstructorTable g2, s2)

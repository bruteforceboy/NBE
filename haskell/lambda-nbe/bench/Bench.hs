{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.DeepSeq (deepseq)
import Control.Monad (forM_, zipWithM)
import Control.Monad.Foil (emptyScope)
import Criterion.Main (Benchmark, bgroup, defaultMain)
import Data.Char (isAlpha, isAlphaNum, isDigit)
import Data.List (isSuffixOf)
import Data.String (fromString)
import Language.Lambda.Impl.FreeFoilTH
  ( benchTerm,
    nf,
  )
import System.CPUTime (getCPUTime)
import System.Directory (listDirectory)
import System.FilePath (replaceExtension, takeBaseName, (</>))

-- | Replace every occurrence of “\var.” with “λvar. ”,
--   where var is a name starting with a letter and
--   followed by zero or more letters or digits.
preprocess :: String -> String
preprocess [] = []
preprocess ('\\' : xs) =
  let (var, rest) = span isAlphaNum xs
   in if not (null var)
        && isAlpha (head var)
        && rest /= []
        && head rest == '.'
        then
          "λ" ++ var ++ ". " ++ preprocess (tail rest)
        else
          '\\' : preprocess xs
preprocess (c : cs) = c : preprocess cs

-- | Time an NF computation (in seconds) and return (normalizedTerm, time)
timeNF :: String -> IO (String, Double)
timeNF ln = do
  let term = fromString ln
      nfTerm = nf emptyScope term
      out = show nfTerm
  start <- getCPUTime
  out `deepseq` return ()
  end <- getCPUTime
  let diffPs = fromIntegral (end - start)
      secs = diffPs / 1e12
  return (out, secs)

main :: IO ()
main = do
  files <- listDirectory "bench"
  let nfFiles = filter (".nf.lam" `isSuffixOf`) files

  forM_ nfFiles $ \inFile -> do
    putStrLn $ "Processing file: " ++ inFile
    rawLines <- lines <$> readFile ("bench" </> inFile)
    let cleaned = map preprocess rawLines
    forM_ (zip [1 ..] cleaned) $ \(i, ln) ->
      putStrLn $ "  Line " ++ show i ++ ": " ++ ln

  groups <- mapM processFile nfFiles
  defaultMain [bgroup "nf-benchmarks" groups]
  where
    processFile :: FilePath -> IO Benchmark
    processFile inFile = do
      let inPath = "bench" </> inFile
          base = takeBaseName inFile
          outPath = "bench" </> replaceExtension base ".lam"

      rawLines <- lines <$> readFile inPath
      let cleaned = map preprocess rawLines

      results <-
        zipWithM
          ( \i ln -> do
              (out, t) <- timeNF ln
              return $
                unlines
                  [ "-- line " ++ show i,
                    out,
                    "-- time(s): " ++ show t
                  ]
          )
          [1 ..]
          cleaned

      writeFile outPath (concat results)

      let benches =
            zipWith
              ( \i ln ->
                  benchTerm
                    emptyScope
                    (base ++ "-line" ++ show i)
                    (fromString ln)
              )
              [1 ..]
              cleaned

      pure $ bgroup base benches

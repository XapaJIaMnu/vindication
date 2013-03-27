module Main( main ) where
import System.Environment
import System.IO.Unsafe
import Data.Char
import Parser
import Runme

main :: IO ()
main = do
  args <- getArgs
  x <- doall args
  return x
  
doall :: [String] -> IO ()
doall args = process_init prop filename
  where
    filename = head args
    prop = head $ tail args
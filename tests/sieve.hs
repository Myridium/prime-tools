import PrimeTools.Main
import PrimeTools.PQTrials
import System.Environment
import Control.DeepSeq
import Data.List

main :: IO()
main = do
        args <- getArgs
        let numprimes = read $ head args :: Integer
        let primeList  = genericTake numprimes primes

        let sol   = {-# SCC solAssignment #-} deepseq primeList "Test done."
        putStrLn(sol)
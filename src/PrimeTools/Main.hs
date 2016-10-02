

module PrimeTools.Main ( module PrimeTools.Base,
                         module PrimeTools.PQTrials,
                         module PrimeTools.MathStuff,
                         primesUpTo,
                         primeGaps,
                         nextprime,
                         mylcm,
                         mygcd,
                         numFactors,
                         factors
                       )
   where
import qualified Math.NumberTheory.Powers.Squares as Squares
import Data.List

--import qualified Data.Numbers.Primes as PP

import PrimeTools.Base
import PrimeTools.Factors
import PrimeTools.PQTrials
import PrimeTools.MathStuff



primesUpTo :: Integer -> [Integer]
primesUpTo nmax = takeWhile (\x -> x <= nmax) primes

-- Returns a list of the gaps between primes
primeGaps :: [Integer]
primeGaps = zipWith (\a b -> a-b-1) (drop 1 $ prs) prs
  where
    prs = primes
-- Returns a list of the gaps between primes, starting from the input number
primeGapsFrom  :: Integer -> [Integer]
primeGapsFrom start = zipWith (\a b -> a-b-1) (drop 1 $ primesByTrial) primesByTrial
  where
    primesByTrial = filter primeQ [start..]


-- I used to generate primes until I found the one that was greater than the number
-- However, it is better to use primeQ for single searches like this because it only needs to generate primes
-- up to at most sqrt(n)
nextprime :: Integer -> Integer
nextprime num
  | num < 2 = 2
nextprime num = case find primeQ [num+1..] of
                  Nothing -> -1 --This should never, ever happen.
                  Just  p -> p

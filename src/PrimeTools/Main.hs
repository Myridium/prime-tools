{-|
Module      : PrimeTools.Main
Description : A collection of the most useful functions from the other modules.
Copyright   : (c) Murdock Grewar, 2016
License     : MIT
Stability   : experimental
Portability : POSIX

A collection of the most useful functions from the other modules, with some auxiliary methods thrown in.
-}
module PrimeTools.Main ( module PrimeTools.Base,
                         module PrimeTools.PQTrials,
                         module PrimeTools.MathStuff,
                         module PrimeTools.Factors,
                         primesTo,
                         primesFrom,
                         primeGaps,
                         nextprime
                       )
   where
import qualified Math.NumberTheory.Powers.Squares as Squares
import Data.List

--import qualified Data.Numbers.Primes as PP

import PrimeTools.Base
import PrimeTools.Factors
import PrimeTools.PQTrials
import PrimeTools.MathStuff



primesTo :: Integer     -- ^The inclusive upper bound.
         -> [Integer]   -- ^The list of primes in the specified range.

-- |Yields the list of primes which terminates just before its values exceed the specified upper bound.
primesTo nmax = takeWhile (\x -> x <= nmax) primes

primesFrom :: Integer   -- ^The inclusive lower bound.
           -> [Integer] -- ^The list of primes in the specified range.

-- |An infinite list of primes no smaller than the given lower bound.
--
-- Unlike 'primesTo', this method does not use 'primes' to sieve for primes all the way from 2, and so this function
-- is usable for extremely large numbers where generating primes up to this point is an intractible task. Instead, this method
-- uses 'primeQ' to check consecutive integers iteratively.
primesFrom start = filter primeQ [start..]


-- Returns a list of the gaps between primes
primeGaps :: [Integer]

-- |An infinite list of the gaps between consecutive primes. The first gap, from 2 to 3, is given as 0.
primeGaps = zipWith (\a b -> a-b-1) (drop 1 $ prs) prs
  where
    prs = primes
-- Returns a list of the gaps between primes, starting from the input number

primeGapsFrom  :: Integer   -- ^The inclusive smaller bound.
               -> [Integer] -- ^The list of prime gaps in the specified range.

-- |An infinite list of the gaps between consecutive primes no smaller than the given lower bound.
--
-- Unlike 'primeGaps', this method does not use 'primes' to sieve for primes all the way from 2, and so this function
-- is usable for extremely large numbers where generating primes up to this point is an intractible task. Instead, this method
-- uses 'primeQ' to check consecutive integers iteratively.
primeGapsFrom start = zipWith (\a b -> a-b-1) (drop 1 $ primesByTrial) primesByTrial
  where
    primesByTrial = filter primeQ [start..]


-- I used to generate primes until I found the one that was greater than the number
-- However, it is better to use primeQ for single searches like this because it only needs to generate primes
-- up to at most sqrt(n)

nextprime :: Integer -- ^The 'Integer' from which to begin a search for a prime.
          -> Integer -- ^The first prime strictly greater than the former 'Integer'.

-- |Returns the first prime strictly greater than the given 'Integer'. This is optimised for large inputs.
--
-- It is essentially implemented as follows:
--
-- > nextprime num = head $ primesFrom $ num+1
nextprime num
  | num < 2 = 2
nextprime num = head $ primesFrom $ num+1
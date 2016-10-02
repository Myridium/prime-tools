{-|
Module      : PrimeTools.Factors
Description : Tools for factorising Integers and performing related functions.
Copyright   : (c) Murdock Grewar, 2016
License     : MIT
Stability   : experimental
Portability : POSIX

Tools for factorising 'Integer's and performing related functions.

Some of these functions are refined versions of ones hidden within "PrimeTools.Base".
-}
module PrimeTools.Factors (
                           pfactor,
                           cprimes,
                           tot,
                           factors,
                           numFactors,
                           mygcd,
                           mylcm
                          )
  where

import PrimeTools.Base
import PrimeTools.PQTrials
import PrimeTools.MathStuff
import qualified Math.NumberTheory.Powers.Squares as Squares
import qualified Data.PQueue.Prio.Min as PQ
import Data.List

-- Improved version of hidden Base methods:
pfactor :: Integer             -- ^The 'Integer' to factorise.
        -> [(Integer,Integer)] -- ^A list of tuples of the form (prime,power) ordered by increasing prime.

-- |WARNING: This function is currently very poorly optimised. It simply uses a combination of trial division and primality checking.
--
-- 'pfactor' will find the prime factorisation of an 'Integer'.
pfactor num = pfactorstartfromprimeindex 0 num
  where
  pfactorstartfromprimeindex :: Integer -> Integer -> [(Integer,Integer)]
  pfactorstartfromprimeindex pind num =
    case lowestPrime of
      Nothing -> if (num==1) then [] else [(num,1)]
      Just p  -> ((p,power) : (pfactorstartfromprimeindex) (pind+1) redNum)
        where
           (power,redNum) = powReduce p (0,num)
             where
               powReduce :: Integer -> (Integer, Integer) -> (Integer, Integer)
               powReduce p (pow,num) = if (num `rem` p == 0) then (powReduce p (pow+1, num `div` p)) else (pow,num)
           
      where
        upperBound = Squares.integerSquareRoot num
        --lowestPrime = find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))
        --Added a primeQ check. The primeQ starts with trial division, meaning that trial division is essentially performed multiple times...
        --This method is inefficient for factorising small numbers, but may perform better for larger/more prime numbers. I need to figure out a way to do this more efficiently.
        lowestPrime
          | pind > 10000 = if (primeQ num) then Nothing else find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))
          | otherwise  = find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))

cprimes :: [Integer] -- ^ A list of 'Integer' for whom coprime 'Integer's will be found.
        -> [Integer] -- ^ The list of coprime 'Integer's.

-- |'cprimes' will generate a list of 'Integer's coprime to the given list.
cprimes relnums = cprimes' simplifiedRelNums
  where
    simplifiedRelNums = map fst (pfactor (product relnums))
    cprimes' relnums  = zipWith (+) offset wheelio
      where
        reducedRelList = map fst (pfactor $ product relnums)
        primeProd      = product reducedRelList
        wheelio      = cycle $ firstCycle
        firstCycle   = tsieve reducedRelList [1..primeProd]
        period       = genericLength firstCycle
        offset       = concatMap (replicate period) [0,primeProd..]
        tsieve ps [] = []
        tsieve ps xs = tsieve' xs (insertprimes ps xs)
          where
            -- Insert at key value p*p the prime number 'p' multiplied all elements of xs.
            insertprimes [] xs          = PQ.empty
            insertprimes (p:ps) xs      = PQ.insert (p) (map (*p) xs) (insertprimes ps xs)
            tsieve' []     table = []
            tsieve' (x:xs) table
              | nextComposite <= x    = tsieve' xs (adjust table) --'x' needs to be checked for whether it's composite
              | otherwise             = x : (tsieve' xs table) --'x' is definitely prime
                where
                  nextComposite = fst $ PQ.findMin table
                  adjust table
                      | n <= x    = {-# SCC insertAndDeleteMin #-} adjust (PQ.insert n' ns $  PQ.deleteMin table)
                      | otherwise = table
                    where
                      (n, n':ns) = PQ.findMin table

tot :: Integer -- ^The <Integer> to apply Euler's Totient function to.
    -> Integer -- ^The number of integers in the range '[2,input]' which are coprime to the input.

-- |Euler's Totient function.
tot n = genericLength $ takeWhile (\a -> a < n) (cprimes [n])

--------------------------

mylcm :: [Integer] -- ^The list of 'Integer's whose lowest common multiple is to be found.
      -> Integer   -- ^The lowest common denominator of the given 'Integer's.


-- |WARNING: This function is currently very poorly optimised, since it relies on 'pfactor' which is itself poorly optimised.
--
-- 'mylcm' will find the lowest common multiple of a list of 'Integer's.
mylcm numList = punfactor (incorporateFactors [] (factorLists numList))
  where
    factorLists :: [Integer] -> [[(Integer,Integer)]]
    factorLists listofnums = map pfactor listofnums
    incorporateFactors :: [(Integer,Integer)] -> [[(Integer,Integer)]] -> [(Integer,Integer)]
    incorporateFactors currentList [] = currentList
    incorporateFactors currentList (next:rm) = incorporateFactors currNextList rm
      where
        currNextList = (map (\pair -> (fst pair, max (snd pair) (nextPower $ fst pair))) currentList) ++ 
                       [(b,p) | (b,p) <- next, find (\pair -> (fst pair) == b) currentList == Nothing] -- Inefficient! We shouldn't have to check them all again.
          where
            nextPower :: Integer -> Integer
            nextPower base = 
              case (find (\pair -> (fst pair) == base) next) of
                Nothing -> 0
                Just (b,p) -> p

mygcd :: [Integer] -- ^The list of 'Integer's whose greatest common divisor is to be found.
      -> Integer   -- ^The greatest common divisor of the given 'Integer's.

-- |WARNING: This function is currently very poorly optimised, since it relies on 'pfactor' which is itself poorly optimised.
--
-- 'mygcd' will find the greatest common divisor of a list of 'Integer's.
mygcd []            = 1
mygcd ns            = punfactor (gcdFactorLists $ map pfactor ns)
  where
    gcdFactorLists :: [[(Integer,Integer)]] -> [(Integer,Integer)]
    gcdFactorLists [n]           = n
    gcdFactorLists (n:nn:ns)       = gcdFactorLists $ (pairgcdFactorLists n nn):ns
      where
        -- pfactor returns an ORDERED list of prime factors, so we can use this
        pairgcdFactorLists na nb = orderedPairGcdFactorLists na nb []
          where
            -- Need to make sure that the result is also ordered
            orderedPairGcdFactorLists na [] table = reverse table
            orderedPairGcdFactorLists [] nb table = reverse table
            orderedPairGcdFactorLists (nap:na) (nbp:nb) table
              | (fst nap < fst nbp) = orderedPairGcdFactorLists na       (nbp:nb) table
              | (fst nbp < fst nap) = orderedPairGcdFactorLists (nap:na) nb table
              | otherwise           = (orderedPairGcdFactorLists na nb ((fst nap, min (snd nap) (snd nbp)):table))

numFactors :: Integer -- ^The 'Integer' whose number of factors is to be determined.
           -> Integer -- ^The number of factors.

-- |WARNING: This function is currently very poorly optimised, since it relies on 'pfactor' which is itself poorly optimised.
--
-- 'numFactors' will compute the number of factors of a given 'Integer' (including 1 and itself).
--
-- This function may or may not be faster than instead using 'genericLength' and 'factors' like so:
--
-- > genericLength.factors
--
-- In any case, it is certainly not slower, and so should be used when the explicit factors themselves are not required.
numFactors num = product $ map (\pair -> 1 + (snd pair)) (pfactor num)

factors :: Integer   -- ^The 'Integer' to factorise.
        -> [Integer] -- ^The complete list of factors.

-- |WARNING: This function is currently very poorly optimised, since it relies on 'pfactor' which is itself poorly optimised.
--
-- 'factors' will output the complete list of factors of a given 'Integer' (including 1 and itself) in no particular order.
factors num = map punfactor factoredLists
  where
    factoredLists = map (\(baseList,expList) -> (zipWith (\b e -> (b,e)) baseList expList)) (baseexponentlistpairs num)
      where
        factoredNum = pfactor num
        baseexponentlistpairs num = map (\littleExpList -> (baseList,littleExpList)) allExpList
          where
            baseList   = map (\pair -> fst pair) factoredNum
            bigExpList = map (\pair -> snd pair) factoredNum
            allExpList = sequence [[0..maxExponent] | maxExponent <- bigExpList]


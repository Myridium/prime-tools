{-|
Module      : PrimeTools.Base
Description : Implements the Sieve of Eratosthenes.
Copyright   : (c) Murdock Grewar, 2016
License     : MIT
Stability   : experimental
Portability : POSIX

Implements the /Sieve of Eratosthenes/ as demonstrated by Melissa E. O\'Neill in the paper __The Genuine Sieve of Eratosthenes__.
-}
module PrimeTools.Base (
                        primes,
                        primesw
                        --pfactor,
                        --cprimes,
                        --tot
                       )
  where

-- This whole thing is pretty well optimised --
import qualified Math.NumberTheory.Powers.Squares as Squares
import qualified Data.PQueue.Prio.Min as PQ
import qualified Data.MemoCombinators as Memo
import Data.List
import PrimeTools.MathStuff

-- Coprimality check --

-- Memoisation is NOT WORTH IT!! The Garbage Collection time more than offsets the ~32% saving of computation time (1 - 6/pi^2)
cprimes :: [Integer] -- ^ A list of integers for whom coprime integers will be found.
        -> [Integer] -- ^ The list of coprime integers.
--cprimes relnums       = cprimetables (map fst (pfactor (product relnums)))
--cprimetables = (Memo.list Memo.integral) cprimes'

-- |cprimes will generate a list of Integers coprime to the given list.
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

-- The default prime generation; wheel size 4 --

primes  :: [Integer]

-- |An infinite list of the primes.
--
-- This default method is equivalent to 'primesw' supplied with an input of 4.
primes  = 2:3:5:7:(sieve $ spin wheel2357 11)
  where
  -- This wheel starts from 11 --
  wheel2357 =  2:4:2:4:6:2:6:4:2:4:6:6:2:6:4:2:6:4:6:8:4:2:4:2:4:8
               :6:4:6:2:4:6:2:6:6:4:2:4:6:2:6:4:2:4:2:10:2:10:wheel2357
  spin (x:xs) n = n : spin xs (n + x)
  
  sieve [] = []
  sieve (x:xs) = x : sieve' xs (insertprime x xs PQ.empty)
    where
    -- Insert at key value p*p the prime number 'p' multiplied all elements of xs.
      insertprime p xs table = PQ.insert (p*p) (map (*p) xs) table
      sieve' []     table = []
      sieve' (x:xs) table
        | nextComposite <= x    = sieve' xs (adjust table) --'x' needs to be checked for whether it's composite
        | otherwise             = x : sieve' xs (insertprime x xs table) --'x' is definitely prime
          where
            nextComposite = fst $ PQ.findMin table
            adjust table
                | n <= x    = adjust (PQ.insert n' ns $ PQ.deleteMin table)
                | otherwise = table
              where
                (n, n':ns) = PQ.findMin table

tot n = length $ takeWhile (\a -> a < n) (cprimes [n])

-- Wheel generation --
-- Wheels tell us the differences between coprime elements, starting with the distance from `1' to the first coprime element --
wheel size = cycle $ zipWith (-) (tail clist) (init clist)
  where
    primeList      = take size primes
    primeProd      = product primeList
    clist = takeWhile (\x -> x <= 1 + primeProd) (cprimes primeList)


-- Primes generated by a given size wheel --
primesw :: Int       -- ^The number of primes incorporated into the /wheel/ which is used to increment candidates in the sieving process.
                     --The RAM and capital processing time required rise explosively for larger values, but this increases the efficiency of the sieve (with rapidly diminishing returns).
                     --Reccommended values are /4-7/. Note that 'primes' uses a value of 4.
        -> [Integer] -- ^The list of primes generated by this sieving method.

-- |'primesw' generates the list of primes via the /Sieve of Eratosthenes/. An 'Integer' input is required, specifying the number of primes used to create a /wheel/ which optimises the process. See Melissa O\'Neill\'s __The Genuine Sieve of Eratosthenes__ for more information.
primesw wheelsize = (take wheelsize primes) ++ (sieve $ spin wheelio nextPrime)
  where
  nextPrime = primes!!wheelsize
  -- This wheel needs to start from the next prime --
  -- This line could in theory never terminate! But the next prime is coprime to the previous ones, so it should.--
  turn n pos diffList = if (pos == nextPrime) then (diffList) else (turn (n+1) (pos + (head diffList)) (tail diffList))
  wheelio = turn 0 1 $ wheel wheelsize
  spin (x:xs) n = n : spin xs (n + x)
  
  sieve [] = []
  sieve (x:xs) = x : sieve' xs (insertprime x xs PQ.empty)
    where
    -- Insert at key value p*p the prime number 'p' multiplied all elements of xs.
      insertprime p xs table = PQ.insert (p*p) (map (*p) xs) table
      sieve' []     table = []
      sieve' (x:xs) table
        | nextComposite <= x    = sieve' xs (adjust table) --'x' needs to be checked for whether it's composite
        | otherwise             = x : sieve' xs (insertprime x xs table) --'x' is definitely prime
          where
            nextComposite = fst $ PQ.findMin table
            adjust table
                | n <= x    = {-# SCC insertAndDeleteMin #-} adjust ({-# SCC insert #-} PQ.insert n' ns $  {-# SCC deleteMin #-} PQ.deleteMin table)
                | otherwise = table
              where
                (n, n':ns) = PQ.findMin table

pfactor :: Integer -> [(Integer,Integer)]
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
        lowestPrime = find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))



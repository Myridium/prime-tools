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
import qualified Math.NumberTheory.Powers.Squares as Squares
import qualified Data.PQueue.Prio.Min as PQ
import Data.List

-- Improved version of hidden Base methods:

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
        --lowestPrime = find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))
        --Added a primeQ check. The primeQ starts with trial division, meaning that trial division is essentially performed multiple times...
        --This method is inefficient for factorising small numbers, but may perform better for larger/more prime numbers. I need to figure out a way to do this more efficiently.
        lowestPrime
          | pind > 10000 = if (primeQ num) then Nothing else find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))
          | otherwise  = find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) (genericDrop pind primes))

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

tot n = length $ takeWhile (\a -> a < n) (cprimes [n])

--------------------------

mylcm :: [Integer] -> Integer
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

mygcd :: [Integer] -> Integer
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

-- Poorly optimized: --
numFactors :: Integer -> Integer
numFactors num = product $ map (\pair -> 1 + (snd pair)) (pfactor num)
factors :: Integer -> [Integer]
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


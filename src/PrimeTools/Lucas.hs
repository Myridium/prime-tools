{-|
Module      : PrimeTools.Lucas
Description : Exposes functions related to determining whether an Integer is a Lucas pseudoprime.
Copyright   : (c) Murdock Grewar, 2016
License     : MIT
Stability   : experimental
Portability : POSIX

Exposes functions related to determining whether an Integer is a Lucas pseudoprime.
-}
module PrimeTools.Lucas (
                         lucasStrongPseudoPrime,
                         jacobiSymbol
                        )
  where

import qualified Data.MemoCombinators as Memo
import qualified Math.NumberTheory.Powers.Squares as Squares
import Math.NumberTheory.Powers
import PrimeTools.Base
import Data.List
import Debug.Trace

fst' (a,_,_)   = a
snd' (_,b,_)   = b
thd' (_,_,c)   = c

-- Assumes k > 0
-- Will only work for odd 'modbase' as we need to use the inverse of 2 in the finite field
lucasmod :: Integer -> Integer -> Integer -> Integer -> (Integer,Integer, Integer)
lucasmod p q modbase k = lucasmodbin p q modbase (binList k)
  where
    binList 0 = []
    binList k = (snd kdivmod):(binList (fst kdivmod))
      where
        kdivmod = {-# SCC kdivmod #-} k `divMod` 2
    lucasmodbin :: Integer -> Integer -> Integer -> [Integer] -> (Integer,Integer, Integer)
    lucasmodbin p q modbase binlist = genUV (q,1,p) (drop 1 $ reverse binlist)
      where
        halffactor :: Integer
        halffactor = ((modbase + 1) `div` 2)
        doubleit :: (Integer, Integer, Integer) -> (Integer, Integer, Integer)
        doublePlusOne :: (Integer, Integer, Integer) -> (Integer, Integer, Integer)
        --Be very careful here: note that this does not apply `mod` to V! As a result, we need to finish this procedure by modding everything after we're done.
        doubleit      (qk,u,v) = ( {-# SCC lucasQk2 #-} (qk^2)     `mod` modbase,   {-# SCC lucasU2 #-} u*v `mod` modbase, {-# SCC lucasV2 #-}((mod (v*v) modbase) -2*(qk)) ) --`mod` modbase)
        -- This one below is actually slower! I suspect it's because u and v become quite large, and squaring them is very computationally taxing.
        --doublePlusOne (k,qk,u,v) = (2*k+1,(qk^2 * q) `mod` modbase, (halffactor*(p*u^2 + v^2)) `mod` modbase, (halffactor*((p^2-4*q)*u^2 + p*v^2)) `mod` modbase)
        doublePlusOne (qk,u,v)  =
          ({-# SCC lucasQk2p1 #-} (qkqk * q) `mod` modbase, {-# SCC lucasU2p1 #-} (halffactor*(p*uu+vv)) `mod` modbase, {-# SCC lucasV2p1 #-} (halffactor*((p^2-4*q)*uu + p*vv)) `mod` modbase)
          where
            (qkqk,uu,vv) = doubleit (qk,u,v)
        genUV (qk,uCurr,vCurr) [] = (qk,uCurr,mod vCurr modbase) --mod needed here because "V" wasn't strictly modded in the "doubleit" procedure.
        genUV (qk,uCurr,vCurr) (o:opList) = 
          if (o == 1) then 
            (genUV (doublePlusOne (qk,uCurr,vCurr)) opList) 
          else 
            (genUV (doubleit (qk,uCurr,vCurr)) opList)


lucasStrongPseudoPrime :: Integer -- ^The Lucas __P__ parameter.
                       -> Integer -- ^The Lucas __Q__ parameter.
                       -> Integer -- ^The candidate number.
                       -> Bool    -- ^Whether the number is a Lucas pseudoprime with respect to the given Lucas parameters __P__ and __Q__.
-- This test is only valid if 'num' does not divide '2q'.
-- So if 'num' is indeed prime and greater than 2 (what we're trying to check) then this test will only
-- confirm this if q is not a multiple of num. We ensure this by just aborting if q >= num

-- |Will accept arguments in the form __P Q candidate__ and determine whether __candidate__ is a Lucas pseudoprime with respect to these parameters.
-- Behaviour of this function is undefined for negative integers.
lucasStrongPseudoPrime p q num
  | num == 2         = True
  | num `mod` 2 == 0 = False
lucasStrongPseudoPrime p q num = if (q >= num) then (error "Must choose Q < n") else
  case not (snd' (lucasmod p q num dn) == 0) of
    True  -> False 
    False -> if (crit1 || crit2) 
              then True 
              else False
  where
    d = p^2 - 4*q
    j   = jacobiSymbol d num
    dn  = num - j             -- delta(n)
    -- Now we factor dn into (a * 2^r)
    factorsOf2 (x,f) = result
      where 
        xdivmod = x `divMod` 2
        result = if (snd xdivmod == 0) then (factorsOf2 (fst xdivmod, f+1)) else (x,f)

    pair= factorsOf2 (dn,0)
    a   = fst pair
    r   = snd pair
    -- The criteria, any of which is sufficient to be a strong Lucas pseudoprime
    --crit1 = ((lucasU p q a) `rem` num) == 0
    crit1 = snd' (lucasmod p q num a) == 0
    crit2 = foldl (||) False truthList
      where
        --truthList = map (\s -> thd' (lucasmod p q num (a*(2^s)) ) == 0) [0..r-1]
        truthList = [thd' (lucasmod p q num (a*(2^s))) == 0 | s <- [0..r-1]]
    
reduceFactorsof2 n
  |  n `mod` 2 == 0 = reduceFactorsof2 (n `div` 2)
  |  otherwise      = n

jacobiSymbol :: Integer -- ^__D__
             -> Integer -- ^__n__
             -> Integer -- ^The __Jacobi Symbol (D/n)__

-- Assumes odd d and positive n. Works well when the smaller argument is easily factorisable
-- Also assumes that 'n' is positive!!
-- Note that this -1 case works because 'n' is always odd!
-- |Compute the __Jacobi Symbol__ (D/n).
jacobiSymbol (-1) n
  | n `rem` 2 == 0 = jacobiSymbol (-1) (reduceFactorsof2 n)
  | n `rem` 4 == 1 = 1
  | otherwise      = -1
jacobiSymbol d n
  | d   < 0   = (jacobiSymbol (-1) n)*(jacobiSymbol (-d)  n )
  | d   < n   = switchFactor * (jacobiSymbol n d)
  | otherwise = product $ zipWith (^) reducedSymbols powers
    where
      switchFactor = if ((d `rem` 4 == 3) && (n `rem` 4 == 3)) then (-1) else 1
      facNum  = pfactor n
      primesF = map fst facNum
      powers  = map snd facNum
      reducedSymbols = map (legendreSymbol d) primesF

-- Memoizing this just slowed things down MASSIVELY!
--legendreSymbol = Memo.memo2 Memo.integral Memo.integral legendreTable
legendreSymbol a b = legendreTable a b
-- This is from the definition of the Kronecker Symbol which is a generalisation.
-- This is necessary.
legendreTable d 2 = case (d `mod` 8) of
  0 -> 0
  1 -> 1
  2 -> 0
  3 ->(-1)
  4 -> 0
  5 ->(-1)
  6 -> 0
  7 -> 1

legendreTable dd pp
  | dd `mod` pp == 0 = 0
  | otherwise        = if squareInMod pp dd then 1 else (-1)

squareInMod p d = (d `rem` p) `elem` (fieldSquares p)

fieldSquares = Memo.arrayRange (1,1000) fieldSquaresTable
fieldSquaresTable p = map (\x -> (x^2) `rem` p) [1..p `div` 2]
---------------------------


--"Factors" module relies on this module indirectly, and implements a *better* version of pfactor using primeQ. We need to implement a more rudimentary version of pfactor by forced trial division.

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



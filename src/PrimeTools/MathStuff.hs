{-|
Module      : PrimeTools.MathStuff
Description : Convenience methods for use in other modules.
Copyright   : (c) Murdock Grewar, 2016
License     : MIT
Stability   : experimental
Portability : POSIX

Convenience methods for use in other modules.
-}
{-# LANGUAGE BangPatterns #-}
module PrimeTools.MathStuff (
                  maximals,
                  powmod,
                  pow2mododd,
                  punfactor
                 )
  where

import Data.List


maximals :: [Integer] -> [(Integer,Integer)]

-- |Takes in a list, and outputs the list of maximal elements in the form [(index, maximalElement)].
maximals (x:xs) = (0,x):(nextmaximal x (1,xs))
  where
    nextmaximal :: Integer -> (Integer,[Integer]) -> [(Integer,Integer)]
    nextmaximal _         (_,[])    = []
    nextmaximal maxsofar (currIndex,(x:xs))
      | maxsofar < x = (currIndex,x):(nextmaximal x (currIndex+1,xs))
      | otherwise    =         nextmaximal maxsofar (currIndex+1,xs)


binarizee k
  | k ==0 = []
  | k > 0 = (snd kdivmod):(binarizee (fst kdivmod))
  where
    kdivmod = k `divMod` 2

binarizeE :: Integer -> [Int]
binarizeE k = binarizeETab k []
  where
    binarizeETab :: Integer -> [Int] -> [Int]
    binarizeETab 0 xs  = xs
    binarizeETab k xs = binarizeETab (kdiv) (kmod:xs)
      where
        kdivmod :: (Integer, Integer)
        kdivmod = k `divMod` 2
        kdiv    = fst kdivmod
        kmod    :: Int
        kmod    = fromIntegral $ snd kdivmod

baserizeE base k = baserizeETab k []
  where
    baserizeETab 0 xs = xs
    baserizeETab k xs = baserizeETab (fst kdivmod) ((snd kdivmod):xs)
      where
        kdivmod = k `divMod` base

-- I don't understand why, but the NAF always has a leading 1. This makes things easy.
naf :: Integer -> [Int]
naf num = nafTab num []
  where
    nafTab :: Integer -> [Int] -> [Int]
    nafTab 0   xs    = xs
    nafTab num xs
      | mod2 == 0    = nafTab (div2)  (0     :xs)
      | otherwise    = nafTab ((num - redVal) `div` 2) ((fromIntegral redVal):xs)
        where
          redVal :: Integer
          (div2, mod2) = num `divMod` 2
          redVal       = 2 - (num `mod` 4)

powmod :: Integer -- ^The exponential base __b__.
       -> Integer -- ^The exponent __e__.
       -> Integer -- ^The modular base __n__.
       -> Integer -- ^The result @b^e mod n@ as a positively signed 'Integer'.

-- |Efficiently computes @b^e mod n@ for large values of each.
powmod num pow modbase = (foldl' operate (num `rem` modbase) opList) `mod` modbase
  where
    opList :: [Int]
    opList = drop 1 $ {-# SCC binarizeE #-} binarizeE pow
    operate :: Integer -> Int -> Integer
    operate k 0 = (k*k)      `rem` modbase
    operate k 1 = (k*k*num)  `rem` modbase

pow2mododd :: Integer -- ^The exponent __e__.
       -> Integer -- ^The modular base __n__.
       -> Integer -- ^The result @2^e mod n@ as a positively signed 'Integer'.


log2Ceil :: Integer -> Integer
log2Ceil !x
  | x == 0    = 0
  | otherwise = 1 + (log2Ceil $ x `div` 2)

-- |Efficiently computes @2^e mod n@ for large values of each. Only works for odd @n@ and positive @e@ and @n@. Faster than 'powmod'. Undefined behaviour for even @n@ or nonpositive parameters.
pow2mododd pow modbase = ((powmod x a modbase) * (powmod 2 b modbase)) `rem` modbase
  where

    n     :: Integer
    x     :: Integer
    n     = log2Ceil modbase
    x     = 2^n - modbase

    a     :: Integer
    b     :: Integer
    (a,b) = pow `quotRem` n



-- This method is left in as a methodological object of interest. The method above for large modular powers is slightly more efficient, but the method below allows for it to be implemented in an arbitrary base.
lpm num pow modbase base = (foldl' operate (beginNum) (drop 1 $ expansionList)) `mod` modbase
  where
    expansionList = baserizeE base pow
    beginNum      = ({-# SCC startNum #-} num^(expansionList!!0)) `rem` modbase
    operate k m   = ({-# SCC powMultiply #-} (k^base * num^m))    `rem` modbase


punfactor :: [(Integer,Integer)] -- ^A list of bases with their respective exponents: @[(base,exponent)]@.
          -> Integer             -- ^The product of each base raised to its respective exponent.

-- |'punfactor' is a convenience method implemented precisely as follows:
--
-- > punfactor facList = product [b^e | (b,e) <- facList]
--
-- It acts as the inverse of 'PrimeTools.Factors.pfactor' provided in "PrimeTools.Factors".
punfactor facList = product [b^e | (b,e) <- facList]
module PrimeTools.MathStuff (
                  maximals,
                  powmod
                 )
  where

import Data.List

--Takes in a list, and outputs the list of maximal elements in the form [(index, maximalElement)]
maximals :: [Integer] -> [(Integer,Integer)]
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

-- Doing `rem` and then ending with a final `mod` may make an incredibly minute improvement for large numbers...
powmod :: Integer -> Integer -> Integer -> Integer
powmod num pow modbase = (foldl' operate num opList) `mod` modbase
  where
    opList :: [Int]
    opList = drop 1 $ {-# SCC binarizeE #-} binarizeE pow
    operate :: Integer -> Int -> Integer
    operate k 0 = (k*k)      `rem` modbase
    operate k 1 = (k*k*num)  `rem` modbase

-- This method is left in as a methodological object of interest. The method above for large modular powers is slightly more efficient, but the method below allows for it to be implemented in an arbitrary base.
lpm num pow modbase base = (foldl' operate (beginNum) (drop 1 $ expansionList)) `mod` modbase
  where
    expansionList = baserizeE base pow
    beginNum      = ({-# SCC startNum #-} num^(expansionList!!0)) `rem` modbase
    operate k m   = ({-# SCC powMultiply #-} (k^base * num^m))    `rem` modbase

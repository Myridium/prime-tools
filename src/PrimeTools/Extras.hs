module PrimeTools.Extras ( npartitions,
                           nzpartitions,
                           partitions,
                           zpartitions,
                           compositions,
                           ncompositions,
                           nztupleCompositions,
                           nztuplePartitions,
                           cartesianProductWith,
                           nmultParts
                          )
                          where

import PrimeTools.Factors
import Data.List
npartitions :: Integer -> Integer -> Integer
npartitions 1 _ = 1
npartitions k n
  | k > n  = 0
  | k == n = 1
  | otherwise = (npartitions (k-1) (n-1)) + (npartitions k (n-k))

nzpartitions :: Integer -> Integer -> Integer
nzpartitions k n = npartitions k (n+k)

partitions :: Integer -> Integer -> [[Integer]]
partitions 1 n = [[n]]
partitions k n
  | k > n  = []
  | k == n = [genericReplicate n 1]
  | otherwise = concatMap (\first -> (map (\list -> (first:list)) $ partitionsWithMax (k-1) (n-first) first)) [1..(n-(k-1))]

partitionsWithMax :: Integer -> Integer -> Integer -> [[Integer]]
partitionsWithMax 1 n myMax
  | myMax < n = []
  | otherwise = [[n]]
partitionsWithMax k n myMax
  | k > n  = []
  | k == n = [genericReplicate n 1]
  | otherwise = concatMap (\first -> (map (\list -> (first:list)) $ partitionsWithMax (k-1) (n-first) first)) [1..(minimum [(n-(k-1)),myMax])]

zpartitions :: Integer -> Integer -> [[Integer]]
zpartitions k n = map (\part -> zipWith (-) part subtractList) (partitions k (n+k))
  where
    subtractList = genericReplicate k 1

choose :: Integer -> Integer -> Integer
choose n 0 = 1
choose 0 k = 0
choose n k = choose (n-1) (k-1) * n `div` k

-- Each composition is listed as a sum of integers from highest to lowest. This is important!
compositions :: Integer -> Integer -> [[Integer]]
compositions 1 n = [[n]]
compositions k n
  | k > n  = []
  | k == n = [genericReplicate n 1]
  | otherwise = concatMap (\first -> (map (\list -> (first:list)) $ compositions (k-1) (n-first))) [1..(n-(k-1))]

ncompositions :: Integer -> Integer -> Integer
ncompositions 1 n = 1
ncompositions k n
  | k > n  = 0
  | k == n = 1
  | otherwise = choose (n-1) (k-1)

zcompositions :: Integer -> Integer -> [[Integer]]
zcompositions k n = map (\part -> zipWith (-) part subtractList) (compositions k (n+k))
  where
    subtractList = genericReplicate k 1

nzcompositions :: Integer -> Integer -> Integer
nzcompositions k n = ncompositions k (n+k)

-- Assumes that duplicates are bunched.
countOrdDupes :: [Integer] -> [Integer]
countOrdDupes [] = []
countOrdDupes (n:list) = countOrdDupes' list n 1
  where
    countOrdDupes' :: [Integer] -> Integer -> Integer -> [Integer]
    countOrdDupes' [] _ reps = [reps]
    countOrdDupes' (n:list) lastVal reps
      | n == lastVal = countOrdDupes' list lastVal (reps+1)
      | otherwise    = ((countOrdDupes' list n 1)++[reps])

nztupleCompositions :: Integer -> [Integer] -> Integer
nztupleCompositions k list = product $ map (\i -> nzcompositions k i) list

cartesianProduct :: [[a]] -> [[a]]
cartesianProduct [] = []
cartesianProduct (only:[]) = [[x] | x <- only]
cartesianProduct (first:lists) = cartesianProduct' first (cartesianProduct lists)
  where
    cartesianProduct' :: [a] -> [[a]] -> [[a]]
    cartesianProduct' list1 listsOther = [x:listOther | x <- list1, listOther <- listsOther]

cartesianProductWith :: (a -> a -> a) -> [[a]] -> [a]
cartesianProductWith _ (first:[]) = first
cartesianProductWith op (first:lists) = foldr (cartesianProductWith' op) first lists
  where
    cartesianProductWith' :: (a -> a -> a) -> [a] -> [a] -> [a]
    cartesianProductWith' op list1 list2 = [op e1 e2 | e1 <- list1, e2 <-list2]

nztuplePartitions :: Integer -> [Integer] -> Integer
nztuplePartitions k []       = -1
nztuplePartitions k [n]      = nzpartitions k n
nztuplePartitions k (n:m:list) = sum $ map (nztuplePartitions' k (m:list)) dupeTallies
  where

    tally :: (Ord a) => [a] -> [(a,Integer)]
    tally xs = [ (c, genericLength g) | g@(c:_) <- group xs]

    firstPartitions :: [[Integer]]
    firstPartitions = zpartitions k n

    dupeTallies :: [([Integer],Integer)]
    dupeTallies = tally $ map (sort.countOrdDupes) firstPartitions

    -- Looks at the dupeTallies.
    nztuplePartitions' :: Integer -> [Integer] -> ([Integer],Integer) -> Integer
    nztuplePartitions' k [] dupTall = snd dupTall
    nztuplePartitions' k (nextn:restn) dupTall
      | and $ map (==1) (fst dupTall) = (snd dupTall)*(nztupleCompositions k (nextn:restn)) --Trivial case of (1,1,1,1) etc
      | otherwise                     = (snd dupTall)*(sum $ map (nztuplePartitions' k restn) nextDupeTallies)--Need to sum over the different compositions
        where
          groupCompositions   :: [[Integer]]
          groupCompositions    = zcompositions (genericLength $ fst dupTall) nextn
          groupLengthSumLists :: [[(Integer,Integer)]]
          groupLengthSumLists  = map (\groupComp -> zip (fst dupTall) groupComp) groupCompositions
          nextPartitions      :: [[Integer]]
          nextPartitions       = concatMap (\groupLengthSumList -> cartesianProductWith (++) (map (\gls -> zpartitions (fst gls) (snd gls)) groupLengthSumList)) groupLengthSumLists

          nextDupeTallies :: [([Integer],Integer)]
          nextDupeTallies = tally $ map (sort.countOrdDupes) nextPartitions

-- This function can benefit greatly from an efficient `pfactor`
nmultParts :: Integer -> Integer -> Integer
nmultParts k n = nztuplePartitions k $ map snd $ pfactor n
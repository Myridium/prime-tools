-- A module for primality testing --

module PrimeTools.PQTrials (
                            primeQ
                           )
  where

import PrimeTools.Base
import PrimeTools.Lucas
import PrimeTools.MathStuff
import Data.List
import Debug.Trace
import qualified Data.MemoCombinators as Memo
import qualified Math.NumberTheory.Powers.Squares as Squares
import qualified Math.NumberTheory.Powers as Powers

-- A TypeClass of different methods by which to check a prime --
data TrialMethodD = TrialDivisionD | APR
data PResult      = Composite | Prime | ProbablePrime | Unknown 
  deriving (Show,Eq)
data TrialMethodP = 
                  PSW
                  | TrialDivisionP TrialDivisionParams
                  | Lucas          LucasParams
                  | MillerRabin    MillerRabinParams
                  | Fermat         FermatParams
-- Each of these methods is a datatype which stores the parameters with which to test --
data TrialDivisionParams = TrialDivPrimes Integer   -- Max number of primes with which to test
data FermatParams        = FermatUpperBound Integer -- The upper bound of 'a' in (a^(p-1) = 1 mod p)
data LucasParams         = LucasPQ Integer Integer
data MillerRabinParams   = MRWitness Integer

-- Will just perform trial division on all primes up to the square root of the number --

-- The default method for checking primality --
primeQ  :: Integer -> Bool
primeQ num = (result == ProbablePrime) || (result == Prime)
  where
    result = {-# SCC primeQ_PSW #-} (primeQP PSW num)
-----------------------------------------------

-- "P" meaning probabilistic; "D" meaning deterministic

primeQD :: TrialMethodD -> Integer -> Bool
primeQD _ 1   = False
primeQD TrialDivisionD num = primeQTrialDivD num

-- We trial a series of 'D' values to find one which produces a jacobi symbol of -1. 
-- There's one list from which to trial initially. If something doesn't pass, then it may be a square.
-- We check this, and if it isn't, we continue searching from the remaining D values.
trialDs1 :: [Integer]
trialDs2 :: [Integer]
-- I'm not sure, but I think that a non-square number will always have a D which yields a Jacobi Symbol of -1. So I don't truncate the second list.
(trialDs1,trialDs2) = splitAt 30 (zipWith (*) (cycle [1,-1]) [5,7..])
primeQP :: TrialMethodP -> Integer -> PResult
primeQP _ 1   = Composite
primeQP (TrialDivisionP (TrialDivPrimes nop)) num = primeQTrialDivP num nop
primeQP (Fermat (FermatUpperBound upperBound)) num = 
  case (find (\a -> not (fermatTest a num)) [2..upperBound]) of
    Nothing -> ProbablePrime
    Just a  -> Composite
    where
      fermatTest a num = (a^num `mod` num) == a
primeQP (Lucas (LucasPQ p q)) num = case (lucasStrongPseudoPrime p q num) of
  True -> ProbablePrime
  False-> Composite
primeQP (MillerRabin (MRWitness a)) num = mrtest a num
primeQP PSW num 
  | num == 2 = Prime
  | {-# SCC trialDivisionTestPSW #-} (trialDivResult == Composite) || (trialDivResult == Prime) = trialDivResult
  | {-# SCC millerRabinTestPSW #-} primeQP (MillerRabin (MRWitness 2)) num == Composite  = Composite
  | dChoice1  /= Nothing = lucasTest dChoice1
  | isSquareTF           = Composite
  | dChoice2  /= Nothing = lucasTest dChoice2
  | otherwise = Unknown
    where
      trialDivResult = primeQP (TrialDivisionP (TrialDivPrimes 1000)) num
      dChoice1   = find (\d -> jacobiSymbol d num == (-1)) trialDs1
      dChoice2   = find (\d -> jacobiSymbol d num == (-1)) trialDs2
      isSquareTF = (Squares.exactSquareRoot num /= Nothing)
      lucasTest (Just dchoice) = {-#SCC lucasTestPSW#-} case lucasStrongPseudoPrime 1 ((1-dchoice) `div` 4) num of
        True -> if (num < 2^64) then (Prime) else (ProbablePrime)
        False-> Composite


mrtest :: Integer -> Integer -> PResult
mrtest _ n 
  | n == 2 = Prime
  | n == 1 = Composite
  | n <  1 = Unknown
mrtest w n
  | w >= n = Unknown
mrtest witness number = case test of
    False -> ProbablePrime
    True  -> Composite
 where
    (d,r) = factorsOf2 (number-1,0)
    ad   = {-# SCC "powmod_2^d" #-} powmod witness d number
    test = (1/=ad) && (otherTest (0,ad))
    otherTest (s,mw)
      | s < r = ((number-1)/=mw) && otherTest ((s+1,mw^2 `mod` number))
      | otherwise = True
    --otherTests = map ((number-1)/=) $ take r (iterate (\x -> x*2 `mod` number) ad)
    factorsOf2 (x,f) = result
      where 
        xdivmod = x `divMod` 2
        result = if (snd xdivmod == 0) then (factorsOf2 (fst xdivmod, f+1)) else (x,f)

-- Two methods for Trial Division. ------------------------------
-- One returns a PResult after attempting, --
-- the other returns a Bool, but in unspecified time...
primeQTrialDivP :: Integer -> Integer -> PResult
primeQTrialDivP num np = nextp num (0,primes)
  where
    upperBound = Squares.integerSquareRoot num
    nextp :: Integer -> (Integer, [Integer]) -> PResult
    nextp num (ind,(p:ps))
      | num `rem` p == 0 = Composite
      | p > upperBound   = Prime
      | ind > np         = ProbablePrime
      | otherwise        = nextp num ((ind+1),ps)

primeQTrialDivD :: Integer -> Bool
primeQTrialDivD num =
    case lowestPrime of
      Nothing -> True
      Just p  -> False
      where
        primeCheckList = primes
        upperBound = Squares.integerSquareRoot num
        lowestPrime = find (\p -> num `rem` p == 0) (takeWhile (\p -> p <= upperBound) primeCheckList)
--------------------------------------------------------------------------------------




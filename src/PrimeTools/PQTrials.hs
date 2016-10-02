{-|
Module      : PrimeTools.PQTrials
Description : Functions for testing the (pseudo)primality of an Integer.
Copyright   : (c) Murdock Grewar, 2016
License     : MIT
Stability   : experimental
Portability : POSIX

Functions for testing the (pseudo)primality of an 'Integer'.

The function of greatest interest is probably 'primeQ'.
-}
module PrimeTools.PQTrials (
                            primeQ,
                            primeQD,
                            primeQP,

                            PResult(..),
                            TrialMethodD(..),
                            TrialMethodP(..),
                            TrialDivisionParams(..),
                            FermatParams(..),
                            LucasParams(..),
                            MillerRabinParams(..)
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

-- |A __datatype__ representing a method of deterministic primality checking.
data TrialMethodD = TrialDivisionD -- ^Basic __Trial Division__. This method will not terminate in any reasonable time for sufficiently large 'Integer's.
-- APR


-- |A __datatype__ representing the outcome of probabilistic primality check.
data PResult      = Composite     -- ^The candidate is certainly composite.
                  | Prime         -- ^The candidate is certainly prime.
                  | ProbablePrime -- ^The candidate passed the primality check, but may be a pseudoprime.
                  | Unknown       -- ^An unspecified issue occurred when attempting the primality check.
  deriving (Show,Eq)

-- |A __datatype__ representing a method of probabilistic primality checking.
data TrialMethodP =
                  -- |The __Baillie-PSW__ algorithm.
                  PSW
                  -- |An attempt at __Trial Division__ which terminates at some upper bound specified by the provided 'TrialDivisionParams'.
                  | TrialDivisionP TrialDivisionParams
                  -- |A __strong__ Lucas pseudoprimality test with the parameters specified by the provided 'LucasParams'.
                  | Lucas          LucasParams
                  -- |A __Miller-Rabin__ primality check with respect to the modular base (a.k.a. \"Witness\") specified by 'MillerRabinParams'.
                  | MillerRabin    MillerRabinParams
                  -- |A __Fermat__ primality check against exponential bases from 2 up to an upper bound specified by 'FermatParams'.
                  | Fermat         FermatParams
-- Each of these methods is a datatype which stores the parameters with which to test --
-- |Parameters for the 'TrialDivisionD' constructor of 'TrialMethodD'.
data TrialDivisionParams = TrialDivPrimes Integer   -- ^The 'Integer' specifies the maximum number of primes with which to trial divide.

-- |Parameters for the 'Fermat' constructor of 'TrialMethodP'.
data FermatParams        = FermatUpperBound Integer -- ^The 'Integer' is the upper bound of 'a' in (a^(p-1) = 1 mod p)

-- |Parameters for the 'Lucas' constructor of 'TrialMethodP'.
data LucasParams         = LucasPQ Integer Integer  -- ^The parameter __P__ followed by __Q__.

-- |Parameters for the 'MillerRabin' constructor of 'TrialMethodP'.
data MillerRabinParams   = MRWitness Integer        -- ^The 'Integer' is the \"Witness\".


primeQ  :: Integer -> Bool
-- |The default method for checking primality. It perfoms a Baillie-PSW primality test using 'primeQP' and assumes a 'ProbablePrime' to be 'Prime'.
--
-- As such, it is equivalent to using 'primeQP' with the 'PSW' constructor of 'TrialMethodP', except for /assuming/ that something which is a 'ProbablePrime' according to this test is indeed a genuine prime.
primeQ num = (result == ProbablePrime) || (result == Prime)
  where
    result = {-# SCC primeQ_PSW #-} (primeQP PSW num)
-----------------------------------------------

-- "P" meaning probabilistic; "D" meaning deterministic

primeQD :: TrialMethodD -- ^A 'TrialMethodD' datatype specifying a deterministic primality-checking method.
        -> Integer      -- ^The 'Integer' whose primality is in question.
        -> Bool         -- ^A 'Bool' indicating whether the tested 'Integer' is prime.

-- |'primeQD' accepts a 'TrialMethodD' by which to test the primality of a given 'Integer'. It then returns 'True' if the integer is prime, and 'False' if it is composite.
primeQD _ 1   = False
primeQD TrialDivisionD num = primeQTrialDivD num

-- We trial a series of 'D' values to find one which produces a jacobi symbol of -1. 
-- There's one list from which to trial initially. If something doesn't pass, then it may be a square.
-- We check this, and if it isn't, we continue searching from the remaining D values.
trialDs1 :: [Integer]
trialDs2 :: [Integer]
-- I'm not sure, but I think that a non-square number will always have a D which yields a Jacobi Symbol of -1. So I don't truncate the second list.
(trialDs1,trialDs2) = splitAt 30 (zipWith (*) (cycle [1,-1]) [5,7..])

primeQP :: TrialMethodP -- ^A 'TrialMethodP' datatype specifying a probabilistic primality-checking method.
        -> Integer      -- ^The 'Integer' whose primality is in question.
        -> PResult      -- ^A 'PResult' datatype indicating what is determined about the primality.

-- |'primeQP' uses a given 'TrialMethodP' to determine the primality of a given 'Integer'.
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




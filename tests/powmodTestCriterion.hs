import PrimeTools.Main
import PrimeTools.PQTrials
import Criterion.Main
import Text.Printf (printf)

main :: IO()
main = defaultMain [
  bgroup "powmod" $
    flip map ([1,3..9] ++ [9999]) $ \i ->
      bench (printf "10^1000 + %d" i) $
        let n = 10^1000 + i :: Integer
        in whnf (powmod 2 ((n - 1) `div` 2)) n
  ]
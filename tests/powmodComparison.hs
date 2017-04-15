import PrimeTools.Main
import PrimeTools.PQTrials
import System.Environment
import Control.DeepSeq

main :: IO()
main = do
        let trialNs   = [10^1000 + 1, 10^1000 + 3.. 10^1000 + 9999]
        let modTest1 n = powmod 2 ((n-1) `div` 2) n
        let test1      = map modTest1 trialNs
        let modTest2 n = pow2mododd ((n-1) `div` 2) n
        let test2      = map modTest2 trialNs

        let sol   = {-# SCC powmod #-} deepseq test1 "First test done."
        putStrLn(sol)
        let sol   = {-# SCC pow2mododd #-} deepseq test2 "Second test done."
        putStrLn(sol)
import PrimeTools.Main
import PrimeTools.PQTrials
import System.Environment
import Control.DeepSeq
import qualified Control.Parallel.Strategies as Parallel

main :: IO()
main = do
        let trialNs   = [10^12..10^12+10^5]
        let test1     = {-# SCC parallelEvaluation #-} Parallel.withStrategy (Parallel.parListChunk 4 Parallel.rdeepseq) (map pfactor trialNs)

        let sol   = {-# SCC solAssignment #-} deepseq test1 "Test done."
        putStrLn(sol)
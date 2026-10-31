module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)

import qualified EDPL
import qualified PLA
import qualified PLASafe
import qualified SEDPL

-- | The checks each module's @main@ prints. EEDPL's are in EEDPLSpec.
checks :: [(String, Bool)]
checks =
  [ ("PLA", PLA.test)
  , ("PLASafe", PLASafe.test)
  , ("EDPL", EDPL.test)
  , ("SEDPL ex", SEDPL.agree SEDPL.ex)
  , ("SEDPL ez", SEDPL.agree SEDPL.ez)
  , ("SEDPL ew", SEDPL.agree SEDPL.ew)
  , ("SEDPL sh", SEDPL.agree SEDPL.sh)
  ]

main :: IO ()
main = do
  mapM_ (\(name, ok) -> putStrLn (name ++ ": " ++ show ok)) checks
  unless (all snd checks) exitFailure

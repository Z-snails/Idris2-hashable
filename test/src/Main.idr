||| Test runner for the hashable SipHash refactor.
module Main

import Hedgehog
import SipHash
import SipHashV2
import System

%default total

main : IO ()
main = do
  siphash   <- checkGroup SipHash.suite
  siphashv2 <- checkGroup SipHashV2.suite
  buffers   <- SipHashV2.bufferTests
  when (not siphash || not siphashv2 || not buffers) $
    exitFailure

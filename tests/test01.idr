
import Data.Hashable

main : IO ()
main = go max_n 0
  where
    max_n : Int
    max_n = 1000000

    go : Int -> Bits64 -> IO ()
    go 0 acc = printLn acc
    go n acc = do
        str <- getLine
        go (n - 1) (acc + hash str)

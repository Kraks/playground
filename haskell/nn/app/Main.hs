module Main where

import Text.Printf
import Nn

main :: IO ()
main = do
  network <- new [2, 2, 1] -- two inputs, two hidden layers, one output

  -- Train a AND operator
  let nn_and = train 0.01 network [ ([0, 0], [0])
                                  , ([0, 1], [0])
                                  , ([1, 0], [0])
                                  , ([1, 1], [1])]
  let r00 = predict nn_and [0, 0]
  let r01 = predict nn_and [0, 1]
  let r10 = predict nn_and [1, 0]
  let r11 = predict nn_and [1, 1]

  putStrLn $ "AND Result: "
  putStrLn $ printf "  0 0 -> %.2f" (head r00)
  putStrLn $ printf "  0 1 -> %.2f" (head r01)
  putStrLn $ printf "  1 0 -> %.2f" (head r10)
  putStrLn $ printf "  1 1 -> %.2f" (head r11)

  -- Train a XOR operator
  let nn_xor = train 0.01 network [ ([0, 0], [0])
                                  , ([0, 1], [1])
                                  , ([1, 0], [1])
                                  , ([1, 1], [0])]
  let r00 = predict nn_xor [0, 0]
  let r01 = predict nn_xor [0, 1]
  let r10 = predict nn_xor [1, 0]
  let r11 = predict nn_xor [1, 1]
  putStrLn $ "XOR Result: "
  putStrLn $ printf "  0 0 -> %.2f" (head r00)
  putStrLn $ printf "  0 1 -> %.2f" (head r01)
  putStrLn $ printf "  1 0 -> %.2f" (head r10)
  putStrLn $ printf "  1 1 -> %.2f" (head r11)

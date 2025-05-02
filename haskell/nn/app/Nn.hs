module Nn where

import Data.List (find, transpose)
import Data.List.Split (chunksOf)
import Data.Maybe
import System.Random (StdGen, getStdGen, randomRs)

type Network = Network' ()
type Network' a = [Layer a]
type Layer a = [(Neuron, a)]
data Neuron = Neuron
  { inputWeights :: [Double]
  , activate     :: Double -> Double
  , activate'    :: Double -> Double
  }
data Forward = Forward
  { output         :: Double
  , sumInputWeight :: Double
  , inputs         :: [Double]
  }
type Neuron' = [Double]

sigmoid :: Double -> Double
sigmoid x = 1.0 / (1 + exp(-x))

sigmoid' :: Double -> Double
sigmoid' x = sigmoid x * (1 - sigmoid x)

sigmoidNeuron :: Neuron' -> Neuron
sigmoidNeuron ws = Neuron ws sigmoid sigmoid'

outputNeuron :: Neuron' -> Neuron
outputNeuron ws = Neuron ws id (const 1)

biasNeuron :: Int -> Neuron
biasNeuron i = Neuron (replicate i 1) (const 1) (const 0)

createLayer :: Functor f => f t -> (t -> a) -> f (a, ())
createLayer n x = (\p -> (x p, ())) <$> n

sigmoidLayer :: [Neuron'] -> Layer ()
sigmoidLayer n = (biasNeuron x, ()) : createLayer n sigmoidNeuron
  where x = length $ head n

new :: [Int] -> IO Network
new n = newGen n <$> getStdGen

outputLayer :: [Neuron'] -> Layer ()
outputLayer n = createLayer n outputNeuron

newGen :: [Int] -> StdGen -> Network
newGen n g = (sigmoidLayer <$> init wss) ++ [outputLayer (last wss)]
  where rest                 = init n
        hiddenIcsNcs         = zip ((+1) <$> rest) (tail rest)
        (outputIc, outputNc) = (snd (last hiddenIcsNcs)+1, last n)
        rs                   = randomRs (-1, 1) g
        (hidden, rs')        = foldl
          (\(wss', rr') (ic, nc) ->
             let (sl, rs'') = pack ic nc rr' in (wss' ++ [sl], rs''))
          ([], rs)
          hiddenIcsNcs
        (outputWss, _)       = pack outputIc outputNc rs'
        wss                  = hidden ++ [outputWss]
        pack ic nc ws        = (take nc $ chunksOf ic ws, drop (ic * nc) ws)

backProp :: Network -> ([Double], [Double]) -> Network
backProp nw (xs, ys) = weightUpdate (forwardLayer nw xs) ys

rate :: Double
rate = 0.5

forwardLayer :: Network -> [Double] -> Network' Forward
forwardLayer nw xs = reverse . fst $ foldl pf ([], 1 : xs) nw
  where pf (nw', xs') l = (l' : nw', xs'')
          where l' = (\(n, _) -> (n, forwardNeuron n xs')) <$> l
                xs'' = (output . snd) <$> l'

forwardNeuron :: Neuron -> [Double] -> Forward
forwardNeuron n xs = Forward
  { output         = activate n net'
  , sumInputWeight = net'
  , inputs         = xs
  }
  where net' = calcNet xs (inputWeights n)

calcNet :: [Double] -> [Double] -> Double
calcNet xs ws = sum $ zipWith (*) xs ws

weightUpdate :: Network' Forward -> [Double] -> Network
weightUpdate fpnw ys = fst $ foldr updateLayer ([], ds) fpnw
  where ds = zipWith (-) ys ((output . snd) <$> last fpnw)

updateLayer :: Layer Forward -> (Network, [Double]) -> (Network, [Double])
updateLayer fpl (nw, ds) = (l' : nw, ds')
  where (l, es) = unzip $ zipWith updateNeuron fpl ds
        ds' = map sum . transpose $ map (\(n, e) -> (* e) <$> inputWeights n) (zip l es)
        l' = (\n -> (n, ())) <$> l

updateNeuron :: (Neuron, Forward) -> Double -> (Neuron, Double)
updateNeuron (n, fpi) d = (n { inputWeights = ws' }, e)
  where e   = activate' n (sumInputWeight fpi) * d
        ws' = zipWith (\x w -> w + (rate * e * x)) (inputs fpi) (inputWeights n)

train :: Double -> Network -> [([Double], [Double])] -> Network
train eps nw samples = fromJust
  $ find (\x -> globalQuadError x samples < eps) (trainUl nw samples)

trainUl :: Network -> [([Double], [Double])] -> [Network]
trainUl nw samples = iterate (\x -> foldl backProp x samples) nw

globalQuadError :: Network -> [([Double], [Double])] -> Double
globalQuadError nw samples = sum $ quadErrorNet nw <$> samples

quadErrorNet :: Network -> ([Double], [Double]) -> Double
quadErrorNet nw (xs, ys) =
  sum $ zipWith (\o y -> (y - o) ** 2) (predict nw xs) ys

predict :: Network -> [Double] -> [Double]
predict nw xs = foldl calculateLayer (1 : xs) nw
  where calculateLayer s = map (\(n, _) -> activate n (calcNet s (inputWeights n)))

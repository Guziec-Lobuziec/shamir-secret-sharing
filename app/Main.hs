{-# language KindSignatures, RankNTypes, LambdaCase,
    TypeApplications, DataKinds, ScopedTypeVariables,
    OverloadedStrings
  #-}
module Main where

--import Formatting
--import Formatting.Clock
--import System.Clock

import Crypto.Number.Prime
import Crypto.Number.Generate
import Crypto.Number.Basic
import Data.Bits
import Data.Modular as Mod
import Data.Reflection
import GHC.TypeLits
import Data.Proxy
import Control.Monad

evalPolly poll x =
  let step x ai ac = ai + x*ac
  in foldr (step x) 0 poll


evalSecret shares =
  let step s a@(i,ai) ac =
        let substep (j,_) (i,_) | j /= i = i `div` (i - j)
                                | otherwise = 1
        in ac + ai*(foldr (\x bc -> bc * (substep a x)) 1 s)
  in foldr (step shares) 0 shares

evalShares poll =
  map (\x -> (x,evalPolly poll x)) $ iterate (+1) 1

sharesReifiedRealm :: forall (n::Nat) . KnownNat n => [Integer] -> Proxy n -> [(Integer,Integer)]
sharesReifiedRealm coeff (_ :: Proxy n) =
  map (\(i,ai) -> (unMod i, unMod ai)) $ evalShares $ map (flip modVal (Proxy :: Proxy n)) coeff

secretReifiedRealm :: forall (n::Nat) . KnownNat n => [(Integer,Integer)] -> Proxy n -> Integer
secretReifiedRealm shares (_ :: Proxy n) =
  let pairIntToPairMod (i,ai) =
        (flip modVal (Proxy :: Proxy n) i, flip modVal (Proxy :: Proxy n) ai)
  in unMod $ evalSecret $ map (pairIntToPairMod) shares

xorSecretSplit secret parts =
  (foldr xor secret parts) : parts

generateCoefficient threshold size =
  mapM (\x -> generateParams size Nothing False) $ take threshold $ repeat 0

sharingCryptoSetup primeSize sharesNum threshold secret = do
  prime <- generatePrime primeSize
  coeff <- fmap ( (:) secret ) $ generateCoefficient (threshold-1) (primeSize-1)
  return (prime, take sharesNum $ reifyNat prime (sharesReifiedRealm coeff))

multipartySharingCryptoSetup primeSize secret sidesConfig = do
  secretParts <- fmap (xorSecretSplit secret) (generateCoefficient ((length sidesConfig) - 1) primeSize)
  zipWithM
    (\part (sharesNum, threshold) -> sharingCryptoSetup primeSize sharesNum threshold part)
    secretParts
    sidesConfig

multipartySecret parts =
  foldr xor 0 $
  map (\(prime,shares) -> reifyNat prime (secretReifiedRealm shares)) parts

getInt = fmap (\s -> read s :: Int) getLine
getInteger = fmap (\s -> read s :: Integer) getLine

prettyPrint site (prime,shares) = do
  putStrLn ("Site nr: "++(show site))
  putStrLn ("Prime used: "++(show prime))
  putStrLn "Shares: "
  putStrLn $ show shares
  return $ site+1

main :: IO ()
main = do
  let config = [(6,3),(4,3),(10,6)]
  putStrLn "Shamir's Secret Sharing"
  putStrLn "Supply secret:"
  secret <- getInteger
  putStrLn "Description: [(primeUsedInModulo,[(shareNumber,share)])]"
  --start <- getTime Monotonic
  parts <- multipartySharingCryptoSetup 256 secret config
  --end <- getTime Monotonic
  --fprint (timeSpecs % "\n") start end
  foldM_ prettyPrint 1 parts
  putStrLn "Secret rebuilt: "
  --start <- getTime Monotonic
  putStrLn $ show $ multipartySecret parts
  --end <- getTime Monotonic
  --fprint (timeSpecs % "\n") start end

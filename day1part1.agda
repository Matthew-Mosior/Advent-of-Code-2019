{-# OPTIONS --guardedness #-}


module day1 where

open import IO
open import Data.Char hiding (show)
open import Data.List hiding (_++_)
open import Data.Integer hiding (show) 
open import Data.Maybe hiding (map;_>>=_)
open import Data.Nat
open import Data.Nat.Show 
open import Data.String hiding (show)
open import Data.Rational hiding (_-_;∣_∣;show)
open import Data.Rational.Unnormalised hiding (_÷_;_-_;floor;∣_∣)
open import Function 

main : Main
main = run do
  contents ← readFiniteFile "input.txt"
  let linescontents   = lines contents
  let linescontentsₙ  = map (λ x → readMaybe 10 x) linescontents
  let linescontentsₙₚ = map (λ x → case x of λ where
                                     nothing   → fromℚᵘ $ mkℚᵘ (+ 1)  1
                                     (just xₚ) → fromℚᵘ $ mkℚᵘ (+ xₚ) 1
                            ) linescontentsₙ
  let divlist = map (λ x → ⌊ x ÷ (fromℚᵘ $ mkℚᵘ (+ 3) 1) ⌋ - (+ 2)
                    ) linescontentsₙₚ
  let divlistₙₐₜ = map (λ x → ∣ x ∣
                       ) divlist
  let sumdivlistₙₐₜ = sum divlistₙₐₜ
  putStrLn ("The answer to advent of code 2019, day 1 is: " ++ show sumdivlistₙₐₜ)

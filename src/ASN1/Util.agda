module ASN1.Util where

open import Data.Word8 using (Word8) renaming (primWord8fromNat to to𝕎; primWord8toNat to from𝕎)
open import Data.Nat using (ℕ; _+_; _*_; _≤?_)
open import Data.Nat.DivMod using (_divMod_; result)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)

-- TODO: use WF induction
{-# TERMINATING #-}
base256 : ℕ → List Word8
base256 n with n ≤? 255
... | yes _ = to𝕎 n ∷ []
... | no _ with n divMod 256
... | result quotient remainder _ = to𝕎 (toℕ remainder) ∷ base256 quotient

fromBase256 : List Word8 → ℕ
fromBase256 [] = 0 -- this should not be the case, as 0 is encoded as (0 ∷ [])
fromBase256 (x ∷ ns) = from𝕎 x + 256 * fromBase256 ns

{-
base256-prop : ∀ n → n ≡ fromBase256 (base256 n)
base256-prop n with n ≤? 255
base256-prop n | yes p = {!!}
base256-prop n | no ¬p = {!!}
-}

{-# TERMINATING #-}
base128 : ℕ → List Word8
base128 n with n ≤? 127
... | yes _ = to𝕎 n ∷ []
... | no _ with n divMod 128
... | result quotient remainder _ = to𝕎 (128 + toℕ remainder) ∷ base128 quotient


module ASN1.BER where

open import Data.Word8 using (Word8; _==_) renaming (primWord8fromNat to to𝕎; primWord8toNat to from𝕎)
open import Data.ByteString using (ByteString; Strict; Lazy; null; pack; unpack; fromChunks; toStrict; unsafeHead; unsafeTail; unsafeSplitAt) renaming (length to BSlength)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _∸_; _≤?_)
open import Data.List using (List; []; _∷_; length; reverse; concatMap; foldl; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (case_of_; const)

open import ASN1.Util
open import ASN1.Untyped

-- encode
module _ where
  encodeLen : Len → List Word8
  encodeLen n with n ≤? 127
  encodeLen n | yes p = to𝕎 n ∷ []
  encodeLen n | no ¬p = to𝕎 (128 + length ns) ∷ reverse ns where
    ns : List Word8
    ns = base256 n

  -- TODO: use WF induction
  {-# TERMINATING #-}
  encode : AST → List (ByteString Strict)
  encode (tlv t (constr vs)) = pack (constructed t ∷ encodeLen l) ∷ evs where
    evs : List (ByteString Strict)
    evs = concatMap encode vs
    l : ℕ
    l = foldl _+_ 0 (map BSlength evs)
  encode (tlv t (prim octets)) = pack (t ∷ encodeLen (BSlength octets)) ∷ octets ∷ []

  encode′ : AST → ByteString Lazy
  encode′ ast = fromChunks (encode ast)

  encode″ : AST → ByteString Strict
  encode″ ast = toStrict (encode′ ast)


-- decode
module _ where

  Stream = ByteString Strict

  StateT : (Set → Set) → Set → Set → Set
  StateT M S A = S → M (A × S)

  E : Set → Set
  E A = String ⊎ A

  M = StateT E Stream
  -- TODO: use std monad

  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  ma >>= f = λ st → case ma st of λ
    { (inj₁ err) → inj₁ err
    ; (inj₂ (a , st′)) → f a st′
    }
  _>>_ : ∀ {A B} → M A → M B → M B
  ma >> mb = ma >>= (const mb)

  return : ∀ {A : Set} → A → M A
  return a = λ st → inj₂ (a , st)

  get : M Stream
  get st = inj₂ (st , st)

  error : ∀ {A : Set} → String → M A
  error e = λ _ → inj₁ e

  head : M Word8
  head st with null st
  head st | false = inj₂ (unsafeHead st , unsafeTail st)
  head st | true = inj₁ "stream is empty"

  take : ℕ → M (ByteString Strict)
  take n st with n ≤? BSlength st
  take n st | yes _ = inj₂ (unsafeSplitAt n st)
  take n st | no _ = inj₁ "stream is small"

  getTag : M Tag
  getTag = head

  getLen : M Len
  getLen = do
    n ← head
    let n′ = from𝕎 n
    no _ ← return (n′ ≤? 127) where
      yes _ → return n′
    let k = n′ ∸ 128
    ns ← take k
    let n″ = (fromBase256 (unpack ns))
    no _ ← return (n″ ≤? 127) where
      yes _ → error "invalid len"
    return n″

  decode : M AST

  {-# TERMINATING #-}
  decodeTLVs : M (List AST)
  decodeTLVs = do
    st ← get
    false ← return (null st) where
      true → return []
    h ← decode
    t ← decodeTLVs
    return (h ∷ t)

  getValue : Tag → Len → M Value
  getValue tag len = do
    bs ← take len
    true ← return (is-constructed tag) where
      false → return (prim bs)
    inj₂ (vs , _) ← return (decodeTLVs bs) where
      inj₁ e → error e
    return (constr vs) 

  decode = do
    t ← getTag
    l ← getLen
    v ← getValue t l
    return (tlv t v)
  -- TODO: check for non-empty stream tail after decode

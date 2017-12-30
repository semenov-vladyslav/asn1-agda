module btls-certs where

open import Data.Word8 using (Word8) renaming (primWord8fromNat to to𝕎)
open import Data.ByteString using (ByteString; Strict; Lazy; pack)
open import Data.ByteString.Primitive using (∣List∣≡∣Strict∣)
open import Data.ByteVec using (ByteVec)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _≤?_; _∸_)
open import Data.Nat.DivMod using (_divMod_; result)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.List using (List; []; _∷_; length; _++_; take)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Data.ByteString.IO as BSIO
open import IO
open import Function using (_∘_)

open import ASN1.Util using (base256)
import ASN1.BER as BER
import ASN1.X509

open import Bee2.Crypto.Belt using (beltHash)
open import Bee2.Crypto.Bign using (Pri; Pub; Sig; bignCalcPubkey; bignSign2)

b : ℕ → List Word8
b n = toList (tabulate {n} (to𝕎 ∘ toℕ))

b256 = b 256

x : (len : ℕ) → ℕ → Σ (List Word8) (λ l → len ≡ length l)
x zero n = [] , refl
x (suc len) n with n divMod 256
... | result q r _ with x len q
... | ns , refl = (to𝕎 (toℕ r) ∷ ns) , refl

mkPri : ℕ → Pri
mkPri n with x 32 n
... | (ns , prf) = (pack ns) , sym (trans (∣List∣≡∣Strict∣ ns (p prf 32<2³¹)) (sym prf)) where
  p : ∀ {u v k} → (u≡v : u ≡ v) → u < k → v < k
  p refl u<k = u<k
  32<2³¹ : 32 < _
  32<2³¹ =
    s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (
    s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (
    s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (
    s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (
    s≤s z≤n))))))))))))))))))))))))))))))))

ca-pri : Pri
ca-pri = mkPri 17

ca-pub : Pub
ca-pub = bignCalcPubkey ca-pri

sign : Pri → ByteString Strict → ByteString Strict
sign pri = proj₁ ∘ bignSign2 pri ∘ beltHash

ca-cert : ByteString Lazy
ca-cert = BER.encode′ cert where
  open ASN1.X509.mkCert "issuer" "subject" "20170101000000Z" "20190101000000Z" (proj₁ ca-pub) (sign ca-pri)

main = run (BSIO.writeBinaryFile "ca.pkc" ca-cert)

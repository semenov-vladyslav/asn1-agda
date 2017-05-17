module btls-certs where

open import asn1
open import Data.Word using (Word8) renaming (Word8fromNat to to𝕎)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.List using (List)
open import Data.ByteString using (ByteString; Strict; Lazy; pack)
import Data.ByteString.IO as BSIO
open import IO

fin256 : Fin 256 → Word8
fin256 f = to𝕎 (toℕ f)

b256 : List Word8
b256 = toList (tabulate {256} fin256)

b : ℕ → List Word8
b n = toList (tabulate {n} (λ f → to𝕎 (toℕ f)))

pub : ByteString Strict
pub = pack (b 64)
sign : ByteString Strict → ByteString Strict
sign tbs = pack (b 48)

cert-ca : ByteString Lazy
cert-ca = DER.encode′ cert where
  open asn1.mkCert "issuer" "subject" "20170101000000Z" "20190101000000Z" pub sign

main = run (BSIO.writeBinaryFile "ca.der" cert-ca)

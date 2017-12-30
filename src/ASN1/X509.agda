module ASN1.X509 where

open import Data.Word8 using (Word8; _and_; _or_; _==_) renaming (primWord8fromNat to to𝕎; primWord8toNat to from𝕎)
open import Data.ByteString using (ByteString; Strict; pack; fromChunks; toStrict)
open import Data.ByteString.Utf8 using (packStrict)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.List using (List; []; _∷_; foldl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

open import ASN1.Untyped
import ASN1.BER as BER


AlgorithmIdentifier : List ℕ → AST → AST
AlgorithmIdentifier oid params = SEQUENCE (OBJECT-IDENTIFIER oid ∷ params ∷ [])

AttributeTypeAndValue : List ℕ → AST → AST
AttributeTypeAndValue type value = SEQUENCE (OBJECT-IDENTIFIER type ∷ value ∷ [])

id-at-commonName : List ℕ
id-at-commonName = 2 ∷ 5 ∷ 4 ∷ 3 ∷ []

CommonName : String → AST
CommonName cn = AttributeTypeAndValue id-at-commonName (UTF8String cn)

RDN : String → AST
RDN cn = SET (CommonName cn ∷ [])

RDNSequence : String → AST
RDNSequence cn = SEQUENCE (RDN cn ∷ [])

Name : String → AST
Name cn = RDNSequence cn

Validity : (from to : String) → AST
Validity from to = SEQUENCE (GeneralizedTime from ∷ GeneralizedTime to ∷ [])


bign-with-hbelt-oid : List ℕ
bign-with-hbelt-oid = 1 ∷ 2 ∷ 112 ∷ 0 ∷ 2 ∷ 0 ∷ 34 ∷ 101 ∷ 45 ∷ 12 ∷ []

bign-pubkey-oid : List ℕ
bign-pubkey-oid = 1 ∷ 2 ∷ 112 ∷ 0 ∷ 2 ∷ 0 ∷ 34 ∷ 101 ∷ 45 ∷ 2 ∷ 1 ∷ []

bign-curve256v1-oid : List ℕ
bign-curve256v1-oid = 1 ∷ 2 ∷ 112 ∷ 0 ∷ 2 ∷ 0 ∷ 34 ∷ 101 ∷ 45 ∷ 3 ∷ 1 ∷ []

SubjectPublicKeyInfo : ByteString Strict → AST
SubjectPublicKeyInfo pub = SEQUENCE
  ( AlgorithmIdentifier bign-pubkey-oid (OBJECT-IDENTIFIER bign-curve256v1-oid)
  ∷ BIT-STRING 0 pub ∷ [])

Extension : OID → (critical : Bool) → ByteString Strict → AST
Extension oid true value = SEQUENCE (OBJECT-IDENTIFIER oid ∷ BOOLEAN true ∷ OCTET-STRING value ∷ [])
Extension oid false value = SEQUENCE (OBJECT-IDENTIFIER oid ∷ OCTET-STRING value ∷ [])

module mkCert
  (issuer-cn : String)
  (subject-cn : String)
  (validity-from : String)
  (validity-to : String)
  (pub : ByteString Strict)
  (sign : ByteString Strict → ByteString Strict) -- tbs → sig
  where

  sa version serial issuer validity subject spki : AST
  sa = AlgorithmIdentifier bign-with-hbelt-oid NULL
  version = EXPLICIT (to𝕎 0) (INTEGER 2) -- v3
  serial = INTEGER 1
  issuer = Name issuer-cn
  validity = Validity validity-from validity-to
  subject = Name subject-cn
  spki = SubjectPublicKeyInfo pub
  {-
  ku
  eku
  skid
  ikid
  -- id-ce = 2 ∷ 5 ∷ 29 ∷ []
  -}
  id-ce-arc : OID → OID
  id-ce-arc tail = 2 ∷ 5 ∷ 29 ∷ tail
  id-kp-arc : OID → OID
  id-kp-arc tail = 1 ∷ 3 ∷ 6 ∷ 1 ∷ 5 ∷ 5 ∷ 7 ∷ 3 ∷ tail

  ku-oid : OID
  ku-oid = id-ce-arc (15 ∷ [])
  data KeyUsage : Set where
    digitalSignature nonRepudation keyEncipherment dataEncipherment
      keyAgreement keyCertSign cRLSign encipherOnly decipherOnly : KeyUsage
  pattern contentCommitment = nonRepudation
  ku : List KeyUsage → AST
  ku kus = Extension ku-oid true (BER.encode″ (BIT-STRING 7 (pack (w₀ ∷ w₁ ∷ [])))) where
    kuIdx : KeyUsage → ℕ
    kuIdx digitalSignature = 0
    kuIdx nonRepudation = 1
    kuIdx keyEncipherment = 2
    kuIdx dataEncipherment = 3
    kuIdx keyAgreement = 4
    kuIdx keyCertSign = 5
    kuIdx cRLSign = 6
    kuIdx encipherOnly = 7
    kuIdx decipherOnly = 8

    i₀ i₁ : KeyUsage → Word8
    i₀ digitalSignature = to𝕎 0x80
    i₀ nonRepudation = to𝕎 0x40
    i₀ keyEncipherment = to𝕎 0x20
    i₀ dataEncipherment = to𝕎 0x10
    i₀ keyAgreement = to𝕎 0x08
    i₀ keyCertSign = to𝕎 0x04
    i₀ cRLSign = to𝕎 0x02
    i₀ encipherOnly = to𝕎 0x01
    i₀ decipherOnly = to𝕎 0
    i₁ digitalSignature = to𝕎 0
    i₁ nonRepudation = to𝕎 0
    i₁ keyEncipherment = to𝕎 0
    i₁ dataEncipherment = to𝕎 0
    i₁ keyAgreement = to𝕎 0
    i₁ keyCertSign = to𝕎 0
    i₁ cRLSign = to𝕎 0
    i₁ encipherOnly = to𝕎 0
    i₁ decipherOnly = to𝕎 0x80

    f₀ f₁ : Word8 → KeyUsage → Word8
    f₀ w u = w or (i₀ u)
    f₁ w u = w or (i₁ u)
    w₀ w₁ : Word8
    w₀ = foldl f₀ (to𝕎 0) kus
    w₁ = foldl f₁ (to𝕎 0) kus


  id-kp-serverAuth id-kp-clientAuth : OID
  id-kp-serverAuth = id-kp-arc (1 ∷ [])
  id-kp-clientAuth = id-kp-arc (2 ∷ [])

  eku-oid : OID
  eku-oid = id-ce-arc (37 ∷ [])
  eku : AST
  eku = Extension eku-oid false (BER.encode″ (SEQUENCE (OBJECT-IDENTIFIER id-kp-serverAuth ∷ OBJECT-IDENTIFIER id-kp-clientAuth ∷ [])))
  
  bc-oid : OID
  bc-oid = id-ce-arc (19 ∷ [])
  bc : AST
  bc = Extension bc-oid true (BER.encode″ (SEQUENCE (BOOLEAN is-ca-true ∷ []))) where
    is-ca-true : Bool
    is-ca-true = true

  exts : AST
  exts = EXPLICIT (tag 3) (SEQUENCE (bc ∷ ku (keyAgreement ∷ []) ∷ eku ∷ []))

  tbs : AST
  tbs = SEQUENCE (version ∷ serial ∷ sa ∷ issuer ∷ validity ∷ subject ∷ spki ∷ exts ∷ [])
  tbs′ : ByteString Strict
  tbs′ = toStrict (fromChunks (BER.encode tbs))
  sig : ByteString Strict
  sig = sign tbs′

  sv : AST
  sv = BIT-STRING 0 sig
  cert : AST
  cert = SEQUENCE (tbs ∷ sa ∷ sv ∷ [])

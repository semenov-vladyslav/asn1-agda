module asn1 where

open import Data.Word using (Word8; _or_) renaming (Word8fromNat to to𝕎)
open import Data.Bool using (Bool; true; false)
import Data.ByteString as BS
open BS using (ByteString; Strict)
import Data.ByteString.Utf8 as BSU
import Data.Nat as Nat
open Nat using (ℕ)

open import Data.Nat.DivMod using (_divMod_; result)
open import Data.Fin using (toℕ)
import Data.List as L
open L using (List; _∷_; [])
open import Relation.Nullary using (Dec; yes; no)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)

module _ where
  open Nat using (_+_; _*_; _≤?_)
  
  -- TODO: use WF induction
  {-# TERMINATING #-}
  base256 : ℕ → List Word8
  base256 n with n ≤? 255
  ... | yes _ = to𝕎 n ∷ []
  ... | no _ with n divMod 256
  ... | result quotient remainder _ = to𝕎 (toℕ remainder) ∷ base256 quotient
  {-# TERMINATING #-}
  base128 : ℕ → List Word8
  base128 n with n ≤? 127
  ... | yes _ = to𝕎 n ∷ []
  ... | no _ with n divMod 128
  ... | result quotient remainder _ = to𝕎 (128 + toℕ remainder) ∷ base128 quotient


module ASN1 where
  open Nat using (_+_; _*_)
  open L using (List; []; _∷_; length; reverse; concatMap; map; foldl)
  open BS using (ByteString; Strict)

  data TLV : Set where
  Tag = Word8
  Len = ℕ

  data AST : Set where
    tlv : (t : Tag) → (vs : List AST) → AST
    prim : (octets : ByteString Strict) → AST

  constructed : Tag → Tag
  constructed = _or (to𝕎 0x20)
  context-specific : Tag → Tag
  context-specific = _or (to𝕎 0x80)
  universal : ℕ
  universal = 0
  tag : ℕ → Tag
  tag = to𝕎

  open BS using (pack; fromChunks; toStrict)

  EXPLICIT : Tag → AST → AST
  EXPLICIT t v = tlv (context-specific (constructed t)) (v ∷ [])
  IMPLICIT : Tag → AST → AST
  IMPLICIT t (tlv _ vs) = tlv t vs
  IMPLICIT _ (prim octets) = prim octets

  NULL : AST
  NULL = tlv (tag 5) []
  BOOLEAN : Bool → AST
  BOOLEAN b = tlv (tag 1) (prim (pack (bv b ∷ [])) ∷ []) where
    bv : Bool → Word8
    bv b with b
    ... | true = to𝕎 0xff
    ... | false = to𝕎 0
  INTEGER : ℕ → AST
  INTEGER n = tlv (to𝕎 2) (prim (pack (base256 n)) ∷ [])
  SEQUENCE : List AST → AST
  SEQUENCE vs = tlv (constructed (tag 16)) vs
  SET : List AST → AST
  SET vs = tlv (constructed (tag 17)) vs
  BIT-STRING : ℕ → ByteString Strict → AST
  BIT-STRING unused os = tlv (tag 3) (prim (pack (to𝕎 unused ∷ [])) ∷ prim os ∷ [])
  OCTET-STRING : ByteString Strict → AST
  OCTET-STRING os = tlv (tag 4) (prim os ∷ [])
  OID = List ℕ
  OBJECT-IDENTIFIER : OID → AST
  OBJECT-IDENTIFIER oid = tlv (to𝕎 6) (prim (pack (packOID oid)) ∷ []) where
    packOID : List ℕ → List Word8
    packOID [] = [] -- invalid oid
    packOID (n ∷ []) = to𝕎 n ∷ [] -- invalid oid
    packOID (n ∷ n′ ∷ ns) = concatMap base128 ((40 * n + n′) ∷ ns) where
  UTF8String : String → AST
  UTF8String s = tlv (to𝕎 12) (prim (BSU.packStrict s) ∷ [])
  GeneralizedTime : String → AST
  GeneralizedTime yyyymmddhhz = tlv (to𝕎 24) (prim (BSU.packStrict yyyymmddhhz) ∷ [])

module DER where
  open ASN1
  open Nat using (_+_; _*_; _≤?_)
  open L using (List; []; _∷_; length; reverse; concatMap; map; foldl)
  open BS using (ByteString; Strict; pack; fromChunks; toStrict)

  encodeLen : Len → List Word8
  encodeLen n with n ≤? 127
  encodeLen n | yes p = to𝕎 n ∷ []
  encodeLen n | no ¬p = to𝕎 (128 + length ns) ∷ reverse ns where
    ns : List Word8
    ns = base256 n

  -- TODO: use WF induction
  {-# TERMINATING #-}
  encode : AST → List (ByteString Strict)
  encode (tlv t vs) = pack (t ∷ encodeLen l) ∷ evs where
    evs : List (ByteString Strict)
    evs = concatMap encode vs
    l : ℕ
    l = foldl _+_ 0 (map BS.length evs)
  encode (prim octets) = octets ∷ []

  encode′ : AST → ByteString BS.Lazy
  encode′ ast = fromChunks (encode ast)
  encode″ : AST → ByteString BS.Strict
  encode″ ast = toStrict (encode′ ast)

  -- decode : ByteString Strict → String ⊎ AST
  -- decode bs = {!!}

module X509 where
  open ASN1
  open BS using (ByteString; Strict; pack; fromChunks; toStrict)

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
  open ASN1
  open X509
  open BS using (pack; fromChunks; toStrict)

  sa : AST
  sa = AlgorithmIdentifier bign-with-hbelt-oid NULL
  version serial issuer validity subject spki : AST
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
  ku kus = Extension ku-oid true (DER.encode″ (BIT-STRING 7 (pack (w₀ ∷ w₁ ∷ [])))) where
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
    w₀ = L.foldl f₀ (to𝕎 0) kus
    w₁ = L.foldl f₁ (to𝕎 0) kus


  id-kp-serverAuth id-kp-clientAuth : OID
  id-kp-serverAuth = id-kp-arc (1 ∷ [])
  id-kp-clientAuth = id-kp-arc (2 ∷ [])

  eku-oid : OID
  eku-oid = id-ce-arc (37 ∷ [])
  eku : AST
  eku = Extension eku-oid false (DER.encode″ (SEQUENCE (OBJECT-IDENTIFIER id-kp-serverAuth ∷ OBJECT-IDENTIFIER id-kp-clientAuth ∷ [])))
  
  bc-oid : OID
  bc-oid = id-ce-arc (19 ∷ [])
  bc : AST
  bc = Extension bc-oid true (DER.encode″ (SEQUENCE (BOOLEAN is-ca-true ∷ []))) where
    is-ca-true : Bool
    is-ca-true = true

  exts : AST
  exts = EXPLICIT (tag 3) (SEQUENCE (bc ∷ ku (keyAgreement ∷ []) ∷ eku ∷ []))

  tbs : AST
  tbs = SEQUENCE (version ∷ serial ∷ sa ∷ issuer ∷ validity ∷ subject ∷ spki ∷ exts ∷ [])
  tbs′ : ByteString Strict
  tbs′ = toStrict (fromChunks (DER.encode tbs))
  sig : ByteString Strict
  sig = sign tbs′

  sv : AST
  sv = BIT-STRING 0 sig
  cert : AST
  cert = SEQUENCE (tbs ∷ sa ∷ sv ∷ [])

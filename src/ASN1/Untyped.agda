module ASN1.Untyped where

open import Data.Word8 using (Word8; _and_; _or_; _==_) renaming (primWord8fromNat to to𝕎; primWord8toNat to from𝕎)
open import Data.ByteString using (ByteString; Strict; empty; pack; fromChunks; toStrict)
open import Data.ByteString.Utf8 using (packStrict)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)

open import ASN1.Util


-- only short (8-bit) tags are supported
Tag = Word8

-- length can be arbitrary big; TODO: restrict to Int64?
Len = ℕ


data Value : Set
data AST : Set

data Value where
  prim : (octets : ByteString Strict) → Value
  constr : (vs : List AST) → Value

data AST where
  tlv : (t : Tag) → (v : Value) → AST


private
  constructed-flag : Word8
  constructed-flag = to𝕎 0x20
  context-specific-flag : Word8
  context-specific-flag = to𝕎 0x80

constructed : Tag → Tag
constructed = _or constructed-flag

is-constructed : Tag → Bool
is-constructed t = (t and constructed-flag) == constructed-flag

context-specific : Tag → Tag
context-specific = _or context-specific-flag

is-context-specific : Tag → Bool
is-context-specific t = (t and context-specific-flag)  == context-specific-flag

universal : ℕ
universal = 0

tag : ℕ → Tag
tag = to𝕎

OID = List ℕ


-- basic asn.1 types
module _ where
  EXPLICIT : Tag → AST → AST
  EXPLICIT t v = tlv (context-specific t) (constr (v ∷ []))

  IMPLICIT : Tag → AST → AST
  IMPLICIT t (tlv _ vs) = tlv t vs


  NULL : AST
  NULL = tlv (tag 5) (prim empty)

  BOOLEAN : Bool → AST
  BOOLEAN b = tlv (tag 1) (prim (pack (bv b ∷ []))) where
    bv : Bool → Word8
    bv b with b
    ... | true = to𝕎 0xff
    ... | false = to𝕎 0

  INTEGER : ℕ → AST
  INTEGER n = tlv (to𝕎 2) (prim (pack (base256 n)))

  SEQUENCE : List AST → AST
  SEQUENCE vs = tlv (tag 16) (constr vs)

  SET : List AST → AST
  SET vs = tlv (tag 17) (constr vs)

  BIT-STRING : ℕ → ByteString Strict → AST
  BIT-STRING unused os = tlv (tag 3) (prim (toStrict (fromChunks ((pack (to𝕎 unused ∷ [])) ∷ os ∷ []))))

  OCTET-STRING : ByteString Strict → AST
  OCTET-STRING os = tlv (tag 4) (prim os)

  OBJECT-IDENTIFIER : OID → AST
  OBJECT-IDENTIFIER oid = tlv (to𝕎 6) (prim (pack (packOID oid))) where
    packOID : List ℕ → List Word8
    packOID [] = [] -- invalid oid
    packOID (n ∷ []) = to𝕎 n ∷ [] -- invalid oid
    packOID (n ∷ n′ ∷ ns) = concatMap base128 ((40 * n + n′) ∷ ns) where

  UTF8String : String → AST
  UTF8String s = tlv (to𝕎 12) (prim (packStrict s))

  GeneralizedTime : String → AST
  GeneralizedTime yyyymmddhhz = tlv (to𝕎 24) (prim (packStrict yyyymmddhhz))

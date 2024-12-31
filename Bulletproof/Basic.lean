/- some mathlib, batteries, aesop imports -/
import Aesop
import Mathlib
import Batteries

open Mathlib
open Batteries
/- here goes definition of bulletproof -/





end pedersen
section bulletproofdefinition


  variable {G : Type*} {F : Type*}
    [AddCommGroup G] [DecidableEq G]
    [Field F] [DecidableEq F]
    [Module F G]


  /-
   Pedersen commitment abstracted in vector space notation.
   (It closely matches with Elliptic curve notation)
  -/
  def pedersen_commitment (g h : G) (m r : F) : G :=
    m • g + r • h

  /-
    Committing a vector of Group elements to a vector of group elements.
  -/
  def pedersen_commitment_vector (g : Vector G n)
    (h : G) (m : Vector F n) (r : F) : G :=
     Array.foldl (fun acc ((mi, gi) : F × G) ↦ acc + mi • gi)
     (r • h) (Array.zipWith m.toArray g.toArray (fun mi gi => (mi, gi)))

  /-
    Inner product of two scalors vectors.
  -/
  def inner_product (a b : Vector F n) : F :=
    Array.foldl (fun acc (ab : F × F) ↦ acc + ab.1 * ab.2) (0 : F)
      (Array.zipWith a.toArray b.toArray (fun ai bi => (ai, bi)))

  /-
  (Logarithmic size) proof for inner product argument.
  -/
  structure InnerProductProof where
    L : Vector G n
    R : Vector G n
    a : F
    b : F


  #print InnerProductProof
/-

This function encodes inner product argument

The inputs to the inner-product argument are independent generators g, h : Vector G n, a
scalar c : Zp, and P : G. The argument lets the prover convince a verifier that the
prover knows two vectors a, b : Vector Zp n such that P := g^a * h^b . u^<a.b> .

Important: Throughout the section we assume that the
dimension n is a power of 2.

a and b are the secret witness vectors that the prover wants to prove knowledge of.
g and h are the public generators of the argument.
P is the public commitment that the prover wants to prove knowledge of the discrete logarithm.

More precisely, we design a proof system for the relation defined by the following predicate:
{(g h : Vector G n) (u : G) (P : G) (a b : Vector F n) | P = g^a * h^b . u^<a.b>}

-/
  def innerproduct_argument {n : Nat} (a b : Vector F (2^n))
    (g h : Vector G (2^n))  (u P : G) : Prop := True -- dummy definition

end bulletproofdefinition

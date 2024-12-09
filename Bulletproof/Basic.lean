/- some mathlib, batteries, aesop imports -/
import Aesop
import Mathlib
import Batteries.Data.Vector

open Batteries
/- here goes definition of bulletproof -/
section bulletproofdefinition


  variable {G : Type*} {F : Type*}
    [AddCommGroup G] [DecidableEq G]
    [Field F] [DecidableEq F]
    [Module F G]

  /- this function encodes inner product argument -/
  /-

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

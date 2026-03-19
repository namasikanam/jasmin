From mathcomp Require Import ssreflect ssrfun.

Require Import expr.

Axiom (mkvar : string -> gvar).
Axiom (mkvar_inj : injective mkvar).
Axiom (mkfunname : string -> funname).
Axiom (mkfunname_inj : injective mkfunname).

(* ========================================================================= *)
(* Notation system for Jasmin expressions.                                   *)
(*                                                                           *)
(* Syntax mirrors Jasmin: +64u, *32u, ==64u, <64s, etc.                      *)
(* Variables are written as string literals: "x", "y".                       *)
(* Integer operators use an 'i' suffix: +i, -i, *i, ==i, etc.               *)
(* Boolean operators: &&, ||, !                                              *)
(*                                                                           *)
(* Precedence levels (higher = binds more loosely):                          *)
(*   2  : unary !, -, ~                                                      *)
(*   3  : *, /, %        (multiplicative)                                    *)
(*   4  : +, -           (additive)                                          *)
(*   5  : <<, >>, <<r, >>r (shifts/rotations)                               *)
(*   6  : &              (bitwise AND)                                       *)
(*   7  : ^              (bitwise XOR)                                       *)
(*   8  : |              (bitwise OR)                                        *)
(*   9  : <, <=, >, >=  (comparison)                                        *)
(*  10  : ==, !=         (equality)                                          *)
(*  11  : &&             (logical AND)                                       *)
(*  12  : ||             (logical OR)                                        *)
(*  13  : ? :            (ternary conditional)                               *)
(* ========================================================================= *)

Declare Custom Entry expr.

Module ExpressionNotations.

Declare Scope expr_scope.
Open Scope expr_scope.

(* --- Entry and exit --- *)

Notation "expr:( e )" :=
  (e)
  (e custom expr at level 0,
   format "'expr:(' e ')'")
  : expr_scope.

Notation "coq:( e )" :=
  (e)
  (in custom expr at level 0,
   e constr at level 0)
  : expr_scope.

Notation "( e )" :=
  (e)
  (in custom expr at level 0, e custom expr)
  : expr_scope.

(* --- Atoms --- *)

(* Variables are string literals, mapped through mkvar. *)
Notation "x" := (mkvar x)
  (in custom expr at level 0, x constr at level 0)
  : expr_scope.

(* Integer constants: #3 means Pconst 3. *)
Notation "# z" :=
  (Pconst z)
  (in custom expr at level 0, z constr at level 0,
   format "# z")
  : expr_scope.

(* Boolean constants. *)
Notation "'true'"  := (Pbool true)  (in custom expr at level 0) : expr_scope.
Notation "'false'" := (Pbool false) (in custom expr at level 0) : expr_scope.

(* ========================================================================= *)
(* Unary operators (level 2).                                                *)
(* ========================================================================= *)

(* Boolean negation: ! e *)
Notation "! e" :=
  (Papp1 Onot e)
  (in custom expr at level 2)
  : expr_scope.

(* Integer negation: -i e *)
Notation "'-i' e" :=
  (Papp1 (Oneg Op_int) e)
  (in custom expr at level 2)
  : expr_scope.

(* Word negation: -Nu e *)
Notation "- 8 'u' e"   := (Papp1 (Oneg (Op_w U8)) e)   (in custom expr at level 2) : expr_scope.
Notation "- 16 'u' e"  := (Papp1 (Oneg (Op_w U16)) e)  (in custom expr at level 2) : expr_scope.
Notation "- 32 'u' e"  := (Papp1 (Oneg (Op_w U32)) e)  (in custom expr at level 2) : expr_scope.
Notation "- 64 'u' e"  := (Papp1 (Oneg (Op_w U64)) e)  (in custom expr at level 2) : expr_scope.
Notation "- 128 'u' e" := (Papp1 (Oneg (Op_w U128)) e) (in custom expr at level 2) : expr_scope.
Notation "- 256 'u' e" := (Papp1 (Oneg (Op_w U256)) e) (in custom expr at level 2) : expr_scope.

(* Bitwise NOT: ~Nu e *)
Notation "~ 8 'u' e"   := (Papp1 (Olnot U8) e)   (in custom expr at level 2) : expr_scope.
Notation "~ 16 'u' e"  := (Papp1 (Olnot U16) e)  (in custom expr at level 2) : expr_scope.
Notation "~ 32 'u' e"  := (Papp1 (Olnot U32) e)  (in custom expr at level 2) : expr_scope.
Notation "~ 64 'u' e"  := (Papp1 (Olnot U64) e)  (in custom expr at level 2) : expr_scope.
Notation "~ 128 'u' e" := (Papp1 (Olnot U128) e) (in custom expr at level 2) : expr_scope.
Notation "~ 256 'u' e" := (Papp1 (Olnot U256) e) (in custom expr at level 2) : expr_scope.

(* Word-of-int cast: (cast Nu) e *)
(* Cannot use Jasmin's (Nu) syntax because it conflicts with ( e ) grouping. *)
Notation "'(cast' 8 'u' ')' e"   := (Papp1 (Oword_of_int U8) e)   (in custom expr at level 2) : expr_scope.
Notation "'(cast' 16 'u' ')' e"  := (Papp1 (Oword_of_int U16) e)  (in custom expr at level 2) : expr_scope.
Notation "'(cast' 32 'u' ')' e"  := (Papp1 (Oword_of_int U32) e)  (in custom expr at level 2) : expr_scope.
Notation "'(cast' 64 'u' ')' e"  := (Papp1 (Oword_of_int U64) e)  (in custom expr at level 2) : expr_scope.
Notation "'(cast' 128 'u' ')' e" := (Papp1 (Oword_of_int U128) e) (in custom expr at level 2) : expr_scope.
Notation "'(cast' 256 'u' ')' e" := (Papp1 (Oword_of_int U256) e) (in custom expr at level 2) : expr_scope.

(* ========================================================================= *)
(* Multiplicative operators (level 3, left associativity).                   *)
(* ========================================================================= *)

(* Integer multiplication: e1 *i e2 *)
Notation "e1 '*i' e2" :=
  (Papp2 (Omul Op_int) e1 e2)
  (in custom expr at level 3, left associativity)
  : expr_scope.

(* Word multiplication: e1 *Nu e2 *)
Notation "e1 * 8 'u' e2"   := (Papp2 (Omul (Op_w U8)) e1 e2)   (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 * 16 'u' e2"  := (Papp2 (Omul (Op_w U16)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 * 32 'u' e2"  := (Papp2 (Omul (Op_w U32)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 * 64 'u' e2"  := (Papp2 (Omul (Op_w U64)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 * 128 'u' e2" := (Papp2 (Omul (Op_w U128)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 * 256 'u' e2" := (Papp2 (Omul (Op_w U256)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.

(* Unsigned word division: e1 /Nu e2 *)
Notation "e1 / 8 'u' e2"   := (Papp2 (Odiv Unsigned (Op_w U8)) e1 e2)   (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 16 'u' e2"  := (Papp2 (Odiv Unsigned (Op_w U16)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 32 'u' e2"  := (Papp2 (Odiv Unsigned (Op_w U32)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 64 'u' e2"  := (Papp2 (Odiv Unsigned (Op_w U64)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 128 'u' e2" := (Papp2 (Odiv Unsigned (Op_w U128)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 256 'u' e2" := (Papp2 (Odiv Unsigned (Op_w U256)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.

(* Signed word division: e1 /Ns e2 *)
Notation "e1 / 8 's' e2"   := (Papp2 (Odiv Signed (Op_w U8)) e1 e2)   (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 16 's' e2"  := (Papp2 (Odiv Signed (Op_w U16)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 32 's' e2"  := (Papp2 (Odiv Signed (Op_w U32)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 64 's' e2"  := (Papp2 (Odiv Signed (Op_w U64)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 128 's' e2" := (Papp2 (Odiv Signed (Op_w U128)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 256 's' e2" := (Papp2 (Odiv Signed (Op_w U256)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.

(* Unsigned word modulo: e1 %Nu e2 *)
Notation "e1 % 8 'u' e2"   := (Papp2 (Omod Unsigned (Op_w U8)) e1 e2)   (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 16 'u' e2"  := (Papp2 (Omod Unsigned (Op_w U16)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 32 'u' e2"  := (Papp2 (Omod Unsigned (Op_w U32)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 64 'u' e2"  := (Papp2 (Omod Unsigned (Op_w U64)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 128 'u' e2" := (Papp2 (Omod Unsigned (Op_w U128)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 256 'u' e2" := (Papp2 (Omod Unsigned (Op_w U256)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.

(* Signed word modulo: e1 %Ns e2 *)
Notation "e1 % 8 's' e2"   := (Papp2 (Omod Signed (Op_w U8)) e1 e2)   (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 16 's' e2"  := (Papp2 (Omod Signed (Op_w U16)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 32 's' e2"  := (Papp2 (Omod Signed (Op_w U32)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 64 's' e2"  := (Papp2 (Omod Signed (Op_w U64)) e1 e2)  (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 128 's' e2" := (Papp2 (Omod Signed (Op_w U128)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 256 's' e2" := (Papp2 (Omod Signed (Op_w U256)) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.

(* ========================================================================= *)
(* Additive operators (level 4, left associativity).                         *)
(* ========================================================================= *)

(* Integer addition: e1 +i e2 *)
Notation "e1 '+i' e2" :=
  (Papp2 (Oadd Op_int) e1 e2)
  (in custom expr at level 4, left associativity)
  : expr_scope.

(* Word addition: e1 +Nu e2 *)
Notation "e1 + 8 'u' e2"   := (Papp2 (Oadd (Op_w U8)) e1 e2)   (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 + 16 'u' e2"  := (Papp2 (Oadd (Op_w U16)) e1 e2)  (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 + 32 'u' e2"  := (Papp2 (Oadd (Op_w U32)) e1 e2)  (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 + 64 'u' e2"  := (Papp2 (Oadd (Op_w U64)) e1 e2)  (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 + 128 'u' e2" := (Papp2 (Oadd (Op_w U128)) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 + 256 'u' e2" := (Papp2 (Oadd (Op_w U256)) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.

(* Integer subtraction: e1 -i e2 *)
Notation "e1 '-i' e2" :=
  (Papp2 (Osub Op_int) e1 e2)
  (in custom expr at level 4, left associativity)
  : expr_scope.

(* Word subtraction: e1 -Nu e2 *)
Notation "e1 - 8 'u' e2"   := (Papp2 (Osub (Op_w U8)) e1 e2)   (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 - 16 'u' e2"  := (Papp2 (Osub (Op_w U16)) e1 e2)  (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 - 32 'u' e2"  := (Papp2 (Osub (Op_w U32)) e1 e2)  (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 - 64 'u' e2"  := (Papp2 (Osub (Op_w U64)) e1 e2)  (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 - 128 'u' e2" := (Papp2 (Osub (Op_w U128)) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 - 256 'u' e2" := (Papp2 (Osub (Op_w U256)) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.

(* ========================================================================= *)
(* Shift and rotation operators (level 5, left associativity).               *)
(* ========================================================================= *)

(* Left shift: e1 <<Nu e2 *)
Notation "e1 << 8 'u' e2"   := (Papp2 (Olsl (Op_w U8)) e1 e2)   (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 << 16 'u' e2"  := (Papp2 (Olsl (Op_w U16)) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 << 32 'u' e2"  := (Papp2 (Olsl (Op_w U32)) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 << 64 'u' e2"  := (Papp2 (Olsl (Op_w U64)) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 << 128 'u' e2" := (Papp2 (Olsl (Op_w U128)) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 << 256 'u' e2" := (Papp2 (Olsl (Op_w U256)) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.

(* Logical right shift: e1 >>Nu e2 *)
Notation "e1 >> 8 'u' e2"   := (Papp2 (Olsr U8) e1 e2)   (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 16 'u' e2"  := (Papp2 (Olsr U16) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 32 'u' e2"  := (Papp2 (Olsr U32) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 64 'u' e2"  := (Papp2 (Olsr U64) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 128 'u' e2" := (Papp2 (Olsr U128) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 256 'u' e2" := (Papp2 (Olsr U256) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.

(* Arithmetic right shift: e1 >>Ns e2 *)
Notation "e1 >> 8 's' e2"   := (Papp2 (Oasr (Op_w U8)) e1 e2)   (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 16 's' e2"  := (Papp2 (Oasr (Op_w U16)) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 32 's' e2"  := (Papp2 (Oasr (Op_w U32)) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 64 's' e2"  := (Papp2 (Oasr (Op_w U64)) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 128 's' e2" := (Papp2 (Oasr (Op_w U128)) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 >> 256 's' e2" := (Papp2 (Oasr (Op_w U256)) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.

(* Rotate left: e1 <<r Nu e2 *)
Notation "e1 '<<r' 8 'u' e2"   := (Papp2 (Orol U8) e1 e2)   (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '<<r' 16 'u' e2"  := (Papp2 (Orol U16) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '<<r' 32 'u' e2"  := (Papp2 (Orol U32) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '<<r' 64 'u' e2"  := (Papp2 (Orol U64) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '<<r' 128 'u' e2" := (Papp2 (Orol U128) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '<<r' 256 'u' e2" := (Papp2 (Orol U256) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.

(* Rotate right: e1 >>r Nu e2 *)
Notation "e1 '>>r' 8 'u' e2"   := (Papp2 (Oror U8) e1 e2)   (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '>>r' 16 'u' e2"  := (Papp2 (Oror U16) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '>>r' 32 'u' e2"  := (Papp2 (Oror U32) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '>>r' 64 'u' e2"  := (Papp2 (Oror U64) e1 e2)  (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '>>r' 128 'u' e2" := (Papp2 (Oror U128) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.
Notation "e1 '>>r' 256 'u' e2" := (Papp2 (Oror U256) e1 e2) (in custom expr at level 5, left associativity) : expr_scope.

(* ========================================================================= *)
(* Bitwise operators.                                                        *)
(* ========================================================================= *)

(* Bitwise AND (level 6): e1 &Nu e2 *)
Notation "e1 & 8 'u' e2"   := (Papp2 (Oland U8) e1 e2)   (in custom expr at level 6, left associativity) : expr_scope.
Notation "e1 & 16 'u' e2"  := (Papp2 (Oland U16) e1 e2)  (in custom expr at level 6, left associativity) : expr_scope.
Notation "e1 & 32 'u' e2"  := (Papp2 (Oland U32) e1 e2)  (in custom expr at level 6, left associativity) : expr_scope.
Notation "e1 & 64 'u' e2"  := (Papp2 (Oland U64) e1 e2)  (in custom expr at level 6, left associativity) : expr_scope.
Notation "e1 & 128 'u' e2" := (Papp2 (Oland U128) e1 e2) (in custom expr at level 6, left associativity) : expr_scope.
Notation "e1 & 256 'u' e2" := (Papp2 (Oland U256) e1 e2) (in custom expr at level 6, left associativity) : expr_scope.

(* Bitwise XOR (level 7): e1 ^Nu e2 *)
Notation "e1 ^ 8 'u' e2"   := (Papp2 (Olxor U8) e1 e2)   (in custom expr at level 7, left associativity) : expr_scope.
Notation "e1 ^ 16 'u' e2"  := (Papp2 (Olxor U16) e1 e2)  (in custom expr at level 7, left associativity) : expr_scope.
Notation "e1 ^ 32 'u' e2"  := (Papp2 (Olxor U32) e1 e2)  (in custom expr at level 7, left associativity) : expr_scope.
Notation "e1 ^ 64 'u' e2"  := (Papp2 (Olxor U64) e1 e2)  (in custom expr at level 7, left associativity) : expr_scope.
Notation "e1 ^ 128 'u' e2" := (Papp2 (Olxor U128) e1 e2) (in custom expr at level 7, left associativity) : expr_scope.
Notation "e1 ^ 256 'u' e2" := (Papp2 (Olxor U256) e1 e2) (in custom expr at level 7, left associativity) : expr_scope.

(* Bitwise OR (level 8): e1 |Nu e2 *)
Notation "e1 | 8 'u' e2"   := (Papp2 (Olor U8) e1 e2)   (in custom expr at level 8, left associativity) : expr_scope.
Notation "e1 | 16 'u' e2"  := (Papp2 (Olor U16) e1 e2)  (in custom expr at level 8, left associativity) : expr_scope.
Notation "e1 | 32 'u' e2"  := (Papp2 (Olor U32) e1 e2)  (in custom expr at level 8, left associativity) : expr_scope.
Notation "e1 | 64 'u' e2"  := (Papp2 (Olor U64) e1 e2)  (in custom expr at level 8, left associativity) : expr_scope.
Notation "e1 | 128 'u' e2" := (Papp2 (Olor U128) e1 e2) (in custom expr at level 8, left associativity) : expr_scope.
Notation "e1 | 256 'u' e2" := (Papp2 (Olor U256) e1 e2) (in custom expr at level 8, left associativity) : expr_scope.

(* ========================================================================= *)
(* Comparison operators (level 9, no associativity).                         *)
(* ========================================================================= *)

(* Integer comparisons. *)
Notation "e1 '<i' e2"  := (Papp2 (Olt Cmp_int) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '<=i' e2" := (Papp2 (Ole Cmp_int) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '>i' e2"  := (Papp2 (Ogt Cmp_int) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '>=i' e2" := (Papp2 (Oge Cmp_int) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.

(* Unsigned word comparisons: <Nu, <=Nu, >Nu, >=Nu *)
Notation "e1 < 8 'u' e2"    := (Papp2 (Olt (Cmp_w Unsigned U8)) e1 e2)    (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 16 'u' e2"   := (Papp2 (Olt (Cmp_w Unsigned U16)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 32 'u' e2"   := (Papp2 (Olt (Cmp_w Unsigned U32)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 64 'u' e2"   := (Papp2 (Olt (Cmp_w Unsigned U64)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 128 'u' e2"  := (Papp2 (Olt (Cmp_w Unsigned U128)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 256 'u' e2"  := (Papp2 (Olt (Cmp_w Unsigned U256)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.

Notation "e1 <= 8 'u' e2"   := (Papp2 (Ole (Cmp_w Unsigned U8)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 16 'u' e2"  := (Papp2 (Ole (Cmp_w Unsigned U16)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 32 'u' e2"  := (Papp2 (Ole (Cmp_w Unsigned U32)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 64 'u' e2"  := (Papp2 (Ole (Cmp_w Unsigned U64)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 128 'u' e2" := (Papp2 (Ole (Cmp_w Unsigned U128)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 256 'u' e2" := (Papp2 (Ole (Cmp_w Unsigned U256)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.

Notation "e1 > 8 'u' e2"    := (Papp2 (Ogt (Cmp_w Unsigned U8)) e1 e2)    (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 16 'u' e2"   := (Papp2 (Ogt (Cmp_w Unsigned U16)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 32 'u' e2"   := (Papp2 (Ogt (Cmp_w Unsigned U32)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 64 'u' e2"   := (Papp2 (Ogt (Cmp_w Unsigned U64)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 128 'u' e2"  := (Papp2 (Ogt (Cmp_w Unsigned U128)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 256 'u' e2"  := (Papp2 (Ogt (Cmp_w Unsigned U256)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.

Notation "e1 >= 8 'u' e2"   := (Papp2 (Oge (Cmp_w Unsigned U8)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 16 'u' e2"  := (Papp2 (Oge (Cmp_w Unsigned U16)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 32 'u' e2"  := (Papp2 (Oge (Cmp_w Unsigned U32)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 64 'u' e2"  := (Papp2 (Oge (Cmp_w Unsigned U64)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 128 'u' e2" := (Papp2 (Oge (Cmp_w Unsigned U128)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 256 'u' e2" := (Papp2 (Oge (Cmp_w Unsigned U256)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.

(* Signed word comparisons: <Ns, <=Ns, >Ns, >=Ns *)
Notation "e1 < 8 's' e2"    := (Papp2 (Olt (Cmp_w Signed U8)) e1 e2)    (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 16 's' e2"   := (Papp2 (Olt (Cmp_w Signed U16)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 32 's' e2"   := (Papp2 (Olt (Cmp_w Signed U32)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 64 's' e2"   := (Papp2 (Olt (Cmp_w Signed U64)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 128 's' e2"  := (Papp2 (Olt (Cmp_w Signed U128)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 < 256 's' e2"  := (Papp2 (Olt (Cmp_w Signed U256)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.

Notation "e1 <= 8 's' e2"   := (Papp2 (Ole (Cmp_w Signed U8)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 16 's' e2"  := (Papp2 (Ole (Cmp_w Signed U16)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 32 's' e2"  := (Papp2 (Ole (Cmp_w Signed U32)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 64 's' e2"  := (Papp2 (Ole (Cmp_w Signed U64)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 128 's' e2" := (Papp2 (Ole (Cmp_w Signed U128)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 256 's' e2" := (Papp2 (Ole (Cmp_w Signed U256)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.

Notation "e1 > 8 's' e2"    := (Papp2 (Ogt (Cmp_w Signed U8)) e1 e2)    (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 16 's' e2"   := (Papp2 (Ogt (Cmp_w Signed U16)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 32 's' e2"   := (Papp2 (Ogt (Cmp_w Signed U32)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 64 's' e2"   := (Papp2 (Ogt (Cmp_w Signed U64)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 128 's' e2"  := (Papp2 (Ogt (Cmp_w Signed U128)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 256 's' e2"  := (Papp2 (Ogt (Cmp_w Signed U256)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.

Notation "e1 >= 8 's' e2"   := (Papp2 (Oge (Cmp_w Signed U8)) e1 e2)   (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 16 's' e2"  := (Papp2 (Oge (Cmp_w Signed U16)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 32 's' e2"  := (Papp2 (Oge (Cmp_w Signed U32)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 64 's' e2"  := (Papp2 (Oge (Cmp_w Signed U64)) e1 e2)  (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 128 's' e2" := (Papp2 (Oge (Cmp_w Signed U128)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 256 's' e2" := (Papp2 (Oge (Cmp_w Signed U256)) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.

(* ========================================================================= *)
(* Equality operators (level 10, no associativity).                          *)
(* ========================================================================= *)

(* Integer equality. *)
Notation "e1 '==i' e2" :=
  (Papp2 (Oeq Op_int) e1 e2)
  (in custom expr at level 10, no associativity)
  : expr_scope.

Notation "e1 '!=i' e2" :=
  (Papp2 (Oneq Op_int) e1 e2)
  (in custom expr at level 10, no associativity)
  : expr_scope.

(* Word equality: ==Nu, !=Nu *)
Notation "e1 == 8 'u' e2"   := (Papp2 (Oeq (Op_w U8)) e1 e2)   (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 == 16 'u' e2"  := (Papp2 (Oeq (Op_w U16)) e1 e2)  (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 == 32 'u' e2"  := (Papp2 (Oeq (Op_w U32)) e1 e2)  (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 == 64 'u' e2"  := (Papp2 (Oeq (Op_w U64)) e1 e2)  (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 == 128 'u' e2" := (Papp2 (Oeq (Op_w U128)) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 == 256 'u' e2" := (Papp2 (Oeq (Op_w U256)) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.

Notation "e1 != 8 'u' e2"   := (Papp2 (Oneq (Op_w U8)) e1 e2)   (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 != 16 'u' e2"  := (Papp2 (Oneq (Op_w U16)) e1 e2)  (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 != 32 'u' e2"  := (Papp2 (Oneq (Op_w U32)) e1 e2)  (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 != 64 'u' e2"  := (Papp2 (Oneq (Op_w U64)) e1 e2)  (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 != 128 'u' e2" := (Papp2 (Oneq (Op_w U128)) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 != 256 'u' e2" := (Papp2 (Oneq (Op_w U256)) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.

(* Boolean equality. *)
Notation "e1 '==b' e2" :=
  (Papp2 Obeq e1 e2)
  (in custom expr at level 10, no associativity)
  : expr_scope.

(* ========================================================================= *)
(* Logical operators.                                                        *)
(* ========================================================================= *)

(* Logical AND (level 11): e1 && e2 *)
Notation "e1 && e2" :=
  (Papp2 Oand e1 e2)
  (in custom expr at level 11, left associativity)
  : expr_scope.

(* Logical OR (level 12): e1 || e2 *)
Notation "e1 || e2" :=
  (Papp2 Oor e1 e2)
  (in custom expr at level 12, left associativity)
  : expr_scope.

(* ========================================================================= *)
(* Ternary conditional (level 13).                                           *)
(* Pif requires an atype: e1 ?Nu e2 : e3 for word, ?bool / ?int for others. *)
(* ========================================================================= *)

(* Word-typed ternary: e1 ?Nu e2 : e3 *)
Notation "e1 ? 8 'u' e2 ':' e3"   := (Pif (aword U8) e1 e2 e3)   (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.
Notation "e1 ? 16 'u' e2 ':' e3"  := (Pif (aword U16) e1 e2 e3)  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.
Notation "e1 ? 32 'u' e2 ':' e3"  := (Pif (aword U32) e1 e2 e3)  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.
Notation "e1 ? 64 'u' e2 ':' e3"  := (Pif (aword U64) e1 e2 e3)  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.
Notation "e1 ? 128 'u' e2 ':' e3" := (Pif (aword U128) e1 e2 e3) (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.
Notation "e1 ? 256 'u' e2 ':' e3" := (Pif (aword U256) e1 e2 e3) (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.

(* Bool/int-typed ternary. *)
Notation "e1 '?bool' e2 ':' e3" := (Pif abool e1 e2 e3) (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.
Notation "e1 '?int' e2 ':' e3"  := (Pif aint e1 e2 e3)  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13) : expr_scope.

(* Generic fallback with explicit atype: e1 ?[ty] e2 : e3 *)
Notation "e1 '?[' ty ']' e2 ':' e3" :=
  (Pif ty e1 e2 e3)
  (in custom expr at level 13, ty constr at level 0,
   e2 custom expr, e3 custom expr at level 13)
  : expr_scope.

(* ========================================================================= *)
(* Integer operators: +i, -i, *i (Op_int variants).                         *)
(* ========================================================================= *)

Notation "e1 '+i' e2" := (Papp2 (Oadd Op_int) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 '-i' e2" := (Papp2 (Osub Op_int) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 '*i' e2" := (Papp2 (Omul Op_int) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 '==i' e2" := (Papp2 (Oeq Op_int) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 '!=i' e2" := (Papp2 (Oneq Op_int) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 '<i' e2" := (Papp2 (Olt Cmp_int) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '<=i' e2" := (Papp2 (Ole Cmp_int) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '>i' e2" := (Papp2 (Ogt Cmp_int) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '>=i' e2" := (Papp2 (Oge Cmp_int) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 '/i' e2" := (Papp2 (Odiv Unsigned Op_int) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 '/si' e2" := (Papp2 (Odiv Signed Op_int) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 '%i' e2" := (Papp2 (Omod Unsigned Op_int) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 '%si' e2" := (Papp2 (Omod Signed Op_int) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.

(* Integer negation: (-i e) *)
Notation "'(-i' e ')'" := (Papp1 (Oneg Op_int) e) (in custom expr at level 0, e custom expr) : expr_scope.

(* ========================================================================= *)
(* Wint (ui64) operators: +64ui, -64ui, *64ui, etc.                         *)
(* Maps to Owi2 Unsigned U64 WIxxx / Owi1 Unsigned WIxxx                    *)
(* ========================================================================= *)

Notation "e1 + 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIadd) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 - 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIsub) e1 e2) (in custom expr at level 4, left associativity) : expr_scope.
Notation "e1 * 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WImul) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 / 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIdiv) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 % 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WImod) e1 e2) (in custom expr at level 3, left associativity) : expr_scope.
Notation "e1 == 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIeq) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 != 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIneq) e1 e2) (in custom expr at level 10, no associativity) : expr_scope.
Notation "e1 < 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIlt) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 <= 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIle) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 > 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIgt) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.
Notation "e1 >= 64 'ui' e2" := (Papp2 (Owi2 Unsigned U64 WIge) e1 e2) (in custom expr at level 9, no associativity) : expr_scope.

(* Wint cast: (64ui) e → Owi1 Unsigned (WIwint_of_int U64) *)
Notation "'(' 64 'ui' ')' e" := (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) e) (in custom expr at level 2) : expr_scope.

(* ========================================================================= *)
(* Memory load: [:uN e]                                                      *)
(* ========================================================================= *)

Notation "'[:u8' e ']'" := (Pload Aligned U8 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u16' e ']'" := (Pload Aligned U16 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u32' e ']'" := (Pload Aligned U32 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u64' e ']'" := (Pload Aligned U64 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u128' e ']'" := (Pload Aligned U128 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u256' e ']'" := (Pload Aligned U256 e) (in custom expr at level 0, e custom expr) : expr_scope.

(* ========================================================================= *)
(* Array access: x[:uN e]                                                    *)
(* Maps to Pget Aligned AAscale UN (mkvar x) e                               *)
(* ========================================================================= *)

Notation "x '[:u8' e ']'"   := (Pget Aligned AAscale U8 (mkvar x) e)   (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u16' e ']'"  := (Pget Aligned AAscale U16 (mkvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u32' e ']'"  := (Pget Aligned AAscale U32 (mkvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u64' e ']'"  := (Pget Aligned AAscale U64 (mkvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u128' e ']'" := (Pget Aligned AAscale U128 (mkvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u256' e ']'" := (Pget Aligned AAscale U256 (mkvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.

(* ========================================================================= *)
(* Array slice: x[:uN e : len]                                                *)
(* Maps to Psub AAscale UN len (mkvar x) e                                    *)
(* ========================================================================= *)

Notation "x '[:u8' e ':' n ']'"   := (Psub AAscale U8 n (mkvar x) e)   (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u16' e ':' n ']'"  := (Psub AAscale U16 n (mkvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u32' e ':' n ']'"  := (Psub AAscale U32 n (mkvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u64' e ':' n ']'"  := (Psub AAscale U64 n (mkvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u128' e ':' n ']'" := (Psub AAscale U128 n (mkvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u256' e ':' n ']'" := (Psub AAscale U256 n (mkvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.

(* ========================================================================= *)
(* Untyped ternary conditional (level 13).                                   *)
(* The compiler's coq mode prints: e1 ? e2 : e3 without type annotation.    *)
(* We default to aint; the type can be refined from the assignment context.  *)
(* ========================================================================= *)

Notation "e1 '?' e2 ':' e3" :=
  (Pif aint e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13)
  : expr_scope.

(* ========================================================================= *)
(* Combine flags: _EQ(...), _uLT(...), _sLT(...), etc.                      *)
(* Maps to PappN (Ocombine_flags cf) [:: e1; e2; e3; e4]                     *)
(* ========================================================================= *)

Notation "'_EQ' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags CF_EQ) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_NEQ' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags CF_NEQ) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_uLT' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_LT Unsigned)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_uLE' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_LE Unsigned)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_uGE' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_GE Unsigned)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_uGT' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_GT Unsigned)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_sLT' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_LT Signed)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_sLE' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_LE Signed)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_sGE' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_GE Signed)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

Notation "'_sGT' ( e1 , e2 , e3 , e4 )" :=
  (PappN (Ocombine_flags (CF_GT Signed)) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

(* ========================================================================= *)
(* Pack expressions: (4u2)[e1, e2, e3, e4]                                   *)
(* Maps to PappN (Opack ws pe) [:: e1; e2; ...]                             *)
(* ========================================================================= *)

Notation "'(4u2)' '[' e1 , e2 , e3 , e4 ']'" :=
  (PappN (Opack U8 PE2) [:: (e1:pexpr); (e2:pexpr); (e3:pexpr); (e4:pexpr)])
  (in custom expr at level 0, e1 custom expr, e2 custom expr, e3 custom expr, e4 custom expr) : expr_scope.

End ExpressionNotations.

(* ========================================================================= *)
(* Instructions, functions, and programs.                                    *)
(*                                                                           *)
(* Instruction notations use custom entries instr/cmd/fundecl/prog           *)
(* to mirror jasminc -pcstexp -until_cstexp output.                          *)
(*                                                                           *)
(* Instruction syntax (in custom instr):                                     *)
(*   "x" = e ; /* uN */         word assignment                              *)
(*   "x" = e ; /* bool */       bool assignment                              *)
(*   "x" = e ; /* int */        int assignment                               *)
(*   return ("r") ;             return (copy variable to itself)             *)
(*   if e { c } else { c }     conditional                                   *)
(*   while (e) { c }            while loop                                   *)
(*   for "i" = (e) to (e) { c } for loop (up)                               *)
(*   for "i" = (e) downto (e) { c } for loop (down)                        *)
(*                                                                           *)
(* Command (in custom jcmd):                                                  *)
(*   i c       concatenation (right recursive)                               *)
(*   i         singleton                                                     *)
(*                                                                           *)
(* Functions (in custom fundecl):                                            *)
(*   fn "name" () { cmd }                                                    *)
(*   fn "name" (reg u64 "x") -> (reg u64) { cmd }                          *)
(*   fn "name" (reg u64 "x" , reg u64 "y") -> (reg u64) { cmd }            *)
(*   fn "name" (reg u64 "x" , reg u64 "y" , reg u64 "z")                   *)
(*       -> (reg u64) { cmd }                                                *)
(*                                                                           *)
(* Programs (in custom prog):                                                *)
(*   f p       concatenation (right recursive)                               *)
(*   f         singleton                                                     *)
(*                                                                           *)
(* Entry/exit:                                                               *)
(*   prog:( p )    enters the prog custom entry                              *)
(* ========================================================================= *)

Require Import sopn.

Axiom (mklvar : string -> var_i).

(* Parametric axiom for intrinsic names. *)
Axiom mkopn : forall {asm_op : Type} {asmop : asmOp asm_op}, string -> @sopn asm_op asmop.

(* Wraps instr_r with dummy info. Polymorphic to survive section boundaries. *)
Definition mkI' {asm_op : Type} {asmop : asmOp asm_op}
  (ir : @instr_r asm_op asmop) : @instr asm_op asmop :=
  MkI dummy_instr_info ir.

(* Build a unit fundef (pre-stack-allocation). *)
Definition mkfundef {asm_op : Type} {asmop : asmOp asm_op}
  (tyin : seq atype) (params : seq var_i)
  (body : seq (@instr asm_op asmop)) (tyout : seq atype) (res : seq var_i)
  : _fundef unit :=
  {| f_info := FunInfo.witness;
     f_contract := None;
     f_tyin := tyin;
     f_params := params;
     f_body := body;
     f_tyout := tyout;
     f_res := res;
     f_extra := tt |}.

(* Build a program from a list of function declarations. *)
Definition mkprog {asm_op : Type} {asmop : asmOp asm_op}
  (fds : seq (_fun_decl unit)) : _prog unit unit :=
  {| p_funcs := fds; p_globs := [::]; p_extra := tt |}.

(* ========================================================================= *)
(* Custom entries for instructions, commands, functions, and programs.       *)
(* ========================================================================= *)

Declare Custom Entry instr.
Declare Custom Entry jcmd.
Declare Custom Entry fundecl.
Declare Custom Entry prog.

Module InstructionNotations.

Import ExpressionNotations.
Open Scope expr_scope.

(* --- cmd entry and exit --- *)

Notation "'cmd:(' c ')'" :=
  (c)
  (c custom jcmd at level 2,
   format "'cmd:(' c ')'")
  : expr_scope.

(* A command is a sequence of instructions, built right-recursively.        *)
(* Both rules are at the same level so the parser tries the longer (cons)   *)
(* rule first, and falls back to the shorter (singleton) on failure.        *)
Notation "i" :=
  (cons i nil)
  (in custom jcmd at level 2,
   i custom instr at level 10)
  : expr_scope.

Notation "i c" :=
  (i :: c)
  (in custom jcmd at level 2,
   i custom instr at level 10,
   c custom jcmd at level 2)
  : expr_scope.

(* --- Function call: "x" = "f"("a", "b"); /* call */ --- *)
(* MUST be defined BEFORE assignments so that assignments (defined later)    *)
(* take priority in Coq's parser.                                           *)

Notation "x = 'call' f () ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [:: Lvar (mklvar x)] (mkfunname f) [::]))
  (in custom instr at level 10, x constr at level 0, f constr at level 0) : expr_scope.

Notation "x = 'call' f ( a ) ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [:: Lvar (mklvar x)] (mkfunname f) [:: (a : pexpr)]))
  (in custom instr at level 10, x constr at level 0, f constr at level 0,
   a custom expr) : expr_scope.

Notation "x = 'call' f ( a , b ) ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [:: Lvar (mklvar x)] (mkfunname f) [:: (a : pexpr); (b : pexpr)]))
  (in custom instr at level 10, x constr at level 0, f constr at level 0,
   a custom expr, b custom expr) : expr_scope.

Notation "x = 'call' f ( a , b , c ) ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [:: Lvar (mklvar x)] (mkfunname f) [:: (a : pexpr); (b : pexpr); (c : pexpr)]))
  (in custom instr at level 10, x constr at level 0, f constr at level 0,
   a custom expr, b custom expr, c custom expr) : expr_scope.

(* --- Memory store: [:uN e1] = e2 ; /* uN */ --- *)

Notation "'[:u8' e1 ']' = e2 ; '/*' 'u8' '*/'" :=
  (mkI' (Cassgn (Lmem Aligned U8 dummy_var_info e1) AT_none (aword U8) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u16' e1 ']' = e2 ; '/*' 'u16' '*/'" :=
  (mkI' (Cassgn (Lmem Aligned U16 dummy_var_info e1) AT_none (aword U16) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u32' e1 ']' = e2 ; '/*' 'u32' '*/'" :=
  (mkI' (Cassgn (Lmem Aligned U32 dummy_var_info e1) AT_none (aword U32) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u64' e1 ']' = e2 ; '/*' 'u64' '*/'" :=
  (mkI' (Cassgn (Lmem Aligned U64 dummy_var_info e1) AT_none (aword U64) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u128' e1 ']' = e2 ; '/*' 'u128' '*/'" :=
  (mkI' (Cassgn (Lmem Aligned U128 dummy_var_info e1) AT_none (aword U128) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u256' e1 ']' = e2 ; '/*' 'u256' '*/'" :=
  (mkI' (Cassgn (Lmem Aligned U256 dummy_var_info e1) AT_none (aword U256) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.

(* --- Array lval assignment: "x"[:uN e1] = e2 ; /* uN */ --- *)

Notation "x '[:u8' e1 ']' = e2 ; '/*' 'u8' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U8 (mklvar x) e1) AT_none (aword U8) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x '[:u16' e1 ']' = e2 ; '/*' 'u16' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U16 (mklvar x) e1) AT_none (aword U16) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x '[:u32' e1 ']' = e2 ; '/*' 'u32' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U32 (mklvar x) e1) AT_none (aword U32) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x '[:u64' e1 ']' = e2 ; '/*' 'u64' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U64 (mklvar x) e1) AT_none (aword U64) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x '[:u128' e1 ']' = e2 ; '/*' 'u128' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U128 (mklvar x) e1) AT_none (aword U128) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x '[:u256' e1 ']' = e2 ; '/*' 'u256' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U256 (mklvar x) e1) AT_none (aword U256) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.

(* --- Array lval assignment with int index: "x"[e1] = e2 ; /* uN */ --- *)
(* Used for inline int indices, e.g., "rkeys"[#0] = "key"; /* u128 */ *)

Notation "x [ e1 ] = e2 ; '/*' 'u8' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U8 (mklvar x) e1) AT_none (aword U8) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x [ e1 ] = e2 ; '/*' 'u16' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U16 (mklvar x) e1) AT_none (aword U16) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x [ e1 ] = e2 ; '/*' 'u32' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U32 (mklvar x) e1) AT_none (aword U32) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x [ e1 ] = e2 ; '/*' 'u64' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U64 (mklvar x) e1) AT_none (aword U64) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x [ e1 ] = e2 ; '/*' 'u128' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U128 (mklvar x) e1) AT_none (aword U128) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.
Notation "x [ e1 ] = e2 ; '/*' 'u256' '*/'" :=
  (mkI' (Cassgn (Laset Aligned AAscale U256 (mklvar x) e1) AT_none (aword U256) e2))
  (in custom instr at level 10, x constr at level 0, e1 custom expr, e2 custom expr) : expr_scope.

(* --- Intrinsic calls (Copn): coq_copn [lvals] (mkopn "name") [args] ; --- *)
(* Generic notation that handles ALL intrinsic patterns.                      *)
(* lvals and args are raw Coq terms (seq lval and seq pexpr).                *)

Notation "'coq_copn' lvs name args ;" :=
  (mkI' (Copn lvs AT_none name args))
  (in custom instr at level 10,
   lvs constr at level 0, name constr at level 0, args constr at level 0)
  : expr_scope.

(* --- Function calls (Ccall): coq_ccall [lvals] (mkfunname "name") [args] ; --- *)
(* Generic notation that handles ALL function call patterns.                  *)

Notation "'coq_ccall' lvs fname args ;" :=
  (mkI' (Ccall lvs fname args))
  (in custom instr at level 10,
   lvs constr at level 0, fname constr at level 0, args constr at level 0)
  : expr_scope.

(* --- Array initialization: ArrayInit("x"); /* arr_init */ --- *)
(* Cassgn with Parr_init: we use a dummy Parr_init value since the type     *)
(* information is erased in the notation.                                     *)

Notation "'ArrayInit' ( x ) ; '/*' 'arr_init' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U8 1%positive) (Parr_init U8 1%positive)))
  (in custom instr at level 10, x constr at level 0) : expr_scope.

(* --- Function calls with more return values --- *)

(* 2 returns, 2 args *)
Notation "r1 , r2 = 'call' f ( a , b ) ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [:: Lvar (mklvar r1); Lvar (mklvar r2)] (mkfunname f) [:: (a : pexpr); (b : pexpr)]))
  (in custom instr at level 10,
   r1 constr at level 0, r2 constr at level 0, f constr at level 0,
   a custom expr, b custom expr) : expr_scope.

(* 2 returns, 3 args *)
Notation "r1 , r2 = 'call' f ( a , b , c ) ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [:: Lvar (mklvar r1); Lvar (mklvar r2)] (mkfunname f) [:: (a : pexpr); (b : pexpr); (c : pexpr)]))
  (in custom instr at level 10,
   r1 constr at level 0, r2 constr at level 0, f constr at level 0,
   a custom expr, b custom expr, c custom expr) : expr_scope.

(* 0 returns, 0 args *)
Notation "'call' f () ; '/*' 'call' '*/'" :=
  (mkI' (Ccall [::] (mkfunname f) [::]))
  (in custom instr at level 10, f constr at level 0) : expr_scope.

(* --- Assignment instructions: "x" = e ; /* uN */ --- *)

Notation "x = e ; /* 'u8' */"    := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U8) e))    (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u16' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U16) e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u32' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U32) e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u64' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U64) e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u128' */"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U128) e))  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u256' */"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U256) e))  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.

Notation "x = e ; /* 'bool' */"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none abool e))  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'int' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none aint e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.

(* --- Return instruction: return ("r") ; --- *)

Notation "'return' ( r ) ; /* 'u8' */"   := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U8)   (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.
Notation "'return' ( r ) ; /* 'u16' */"  := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U16)  (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.
Notation "'return' ( r ) ; /* 'u32' */"  := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U32)  (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.
Notation "'return' ( r ) ; /* 'u64' */"  := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U64)  (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.
Notation "'return' ( r ) ; /* 'u128' */" := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U128) (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.
Notation "'return' ( r ) ; /* 'u256' */" := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U256) (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.

Notation "'return' ( r ) ; /* 'bool' */" := (mkI' (Cassgn (Lvar (mklvar r)) AT_none abool (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.
Notation "'return' ( r ) ; /* 'int' */"  := (mkI' (Cassgn (Lvar (mklvar r)) AT_none aint  (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.

(* Untyped return: defaults to u64 *)
Notation "'return' ( r ) ;" := (mkI' (Cassgn (Lvar (mklvar r)) AT_none (aword U64) (Plvar (mklvar r)))) (in custom instr at level 10, r constr at level 0) : expr_scope.

(* Empty return: return (); *)
Notation "'return' () ;" := (mkI' (Cassgn (Lnone dummy_var_info abool) AT_none abool (Pbool true)))
  (in custom instr at level 10) : expr_scope.

(* Multi-value return: return ("a", "b"); *)
Notation "'return' ( r1 , r2 ) ;" :=
  (mkI' (Cassgn (Lvar (mklvar r1)) AT_none (aword U64) (Plvar (mklvar r1))))
  (in custom instr at level 10, r1 constr at level 0, r2 constr at level 0) : expr_scope.

(* 3-value return: return ("a", "b", "c"); *)
Notation "'return' ( r1 , r2 , r3 ) ;" :=
  (mkI' (Cassgn (Lvar (mklvar r1)) AT_none (aword U64) (Plvar (mklvar r1))))
  (in custom instr at level 10, r1 constr at level 0, r2 constr at level 0, r3 constr at level 0) : expr_scope.

(* --- Assignment with array type: x = e ; /* uN[len] */ --- *)
Notation "x = e ; '/*' 'u8' '[' n ']' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U8 n) e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13, n constr at level 0) : expr_scope.
Notation "x = e ; '/*' 'u16' '[' n ']' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U16 n) e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13, n constr at level 0) : expr_scope.
Notation "x = e ; '/*' 'u32' '[' n ']' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U32 n) e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13, n constr at level 0) : expr_scope.
Notation "x = e ; '/*' 'u64' '[' n ']' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U64 n) e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13, n constr at level 0) : expr_scope.
Notation "x = e ; '/*' 'u128' '[' n ']' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U128 n) e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13, n constr at level 0) : expr_scope.
Notation "x = e ; '/*' 'u256' '[' n ']' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U256 n) e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13, n constr at level 0) : expr_scope.

(* --- Assignment with /* int:i */ type comment (inline int) --- *)
Notation "x = e ; '/*' 'int:i' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none aint e))
  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.

(* --- Control flow --- *)

(* If without else *)
Notation "'if' e { c }" :=
  (mkI' (Cif e c [::]))
  (in custom instr at level 10,
   e custom expr at level 13,
   c custom jcmd at level 2)
  : expr_scope.

Notation "'if' e { c1 } 'else' { c2 }" :=
  (mkI' (Cif e c1 c2))
  (in custom instr at level 10,
   e custom expr at level 13,
   c1 custom jcmd at level 2,
   c2 custom jcmd at level 2)
  : expr_scope.

Notation "'while' ( e ) { c }" :=
  (mkI' (Cwhile NoAlign [::] e dummy_instr_info c))
  (in custom instr at level 10,
   e custom expr at level 13,
   c custom jcmd at level 2)
  : expr_scope.

(* While with pre-body: while { c1 } (e) *)
Notation "'while' { c1 } ( e )" :=
  (mkI' (Cwhile NoAlign c1 e dummy_instr_info [::]))
  (in custom instr at level 10,
   c1 custom jcmd at level 2,
   e custom expr at level 13)
  : expr_scope.

(* While with pre-body and post-body: while { c1 } (e) { c2 } *)
Notation "'while' { c1 } ( e ) { c2 }" :=
  (mkI' (Cwhile NoAlign c1 e dummy_instr_info c2))
  (in custom instr at level 10,
   c1 custom jcmd at level 2,
   e custom expr at level 13,
   c2 custom jcmd at level 2)
  : expr_scope.

Notation "'for' v = ( e1 ) 'to' ( e2 ) { c }" :=
  (mkI' (Cfor (mklvar v) (UpTo, e1, e2) c))
  (in custom instr at level 10,
   v constr at level 0,
   e1 custom expr at level 13,
   e2 custom expr at level 13,
   c custom jcmd at level 2)
  : expr_scope.

Notation "'for' v = ( e1 ) 'downto' ( e2 ) { c }" :=
  (mkI' (Cfor (mklvar v) (DownTo, e2, e1) c))
  (in custom instr at level 10,
   v constr at level 0,
   e1 custom expr at level 13,
   e2 custom expr at level 13,
   c custom jcmd at level 2)
  : expr_scope.

(* --- Function declarations (custom entry fundecl) --- *)

(* 0 params, 0 returns *)
Notation "'fn' name () { c }" :=
  (mkfunname name, mkfundef [::] [::] c [::] [::])
  (in custom fundecl at level 0,
   name constr at level 0,
   c custom jcmd at level 2)
  : expr_scope.

(* 1 u64 param, 1 u64 return *)
Notation "'fn' name ( 'reg' 'u64' p ) -> ( 'reg' 'u64' ) { c }" :=
  (mkfunname name, mkfundef
    [:: aword U64] [:: mklvar p]
    c
    [:: aword U64] [:: mklvar p])
  (in custom fundecl at level 0,
   name constr at level 0,
   p constr at level 0,
   c custom jcmd at level 2)
  : expr_scope.

(* 2 u64 params, 1 u64 return *)
Notation "'fn' name ( 'reg' 'u64' p1 , 'reg' 'u64' p2 ) -> ( 'reg' 'u64' ) { c }" :=
  (mkfunname name, mkfundef
    [:: aword U64; aword U64] [:: mklvar p1; mklvar p2]
    c
    [:: aword U64] [:: mklvar p1])
  (in custom fundecl at level 0,
   name constr at level 0,
   p1 constr at level 0,
   p2 constr at level 0,
   c custom jcmd at level 2)
  : expr_scope.

(* 3 u64 params, 1 u64 return *)
Notation "'fn' name ( 'reg' 'u64' p1 , 'reg' 'u64' p2 , 'reg' 'u64' p3 ) -> ( 'reg' 'u64' ) { c }" :=
  (mkfunname name, mkfundef
    [:: aword U64; aword U64; aword U64]
    [:: mklvar p1; mklvar p2; mklvar p3]
    c
    [:: aword U64] [:: mklvar p1])
  (in custom fundecl at level 0,
   name constr at level 0,
   p1 constr at level 0,
   p2 constr at level 0,
   p3 constr at level 0,
   c custom jcmd at level 2)
  : expr_scope.

(* 0 params, 1 u32 return *)
Notation "'fn' name () -> ( 'reg' 'u32' ) { c }" :=
  (mkfunname name, mkfundef [::] [::] c [:: aword U32] [::])
  (in custom fundecl at level 0, name constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 0 params, 1 u64 return *)
Notation "'fn' name () -> ( 'reg' 'u64' ) { c }" :=
  (mkfunname name, mkfundef [::] [::] c [:: aword U64] [::])
  (in custom fundecl at level 0, name constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 0 params, 2 u64 returns *)
Notation "'fn' name () -> ( 'reg' 'u64' , 'reg' 'u64' ) { c }" :=
  (mkfunname name, mkfundef [::] [::] c [:: aword U64; aword U64] [::])
  (in custom fundecl at level 0, name constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 2 ui64 params, 1 ui64 return *)
Notation "'fn' name ( 'reg' 'ui64' p1 , 'reg' 'ui64' p2 ) -> ( 'reg' 'ui64' ) { c }" :=
  (mkfunname name, mkfundef
    [:: aword U64; aword U64] [:: mklvar p1; mklvar p2]
    c [:: aword U64] [:: mklvar p1])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 4 ui64 params, no return *)
Notation "'fn' name ( 'reg' 'ui64' p1 , 'reg' 'ui64' p2 , 'reg' 'ui64' p3 , 'reg' 'ui64' p4 ) -> () { c }" :=
  (mkfunname name, mkfundef
    [:: aword U64; aword U64; aword U64; aword U64]
    [:: mklvar p1; mklvar p2; mklvar p3; mklvar p4]
    c [::] [::])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0,
   p3 constr at level 0, p4 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* --- Additional function signatures --- *)

(* 0 params, no return *)
Notation "'fn' name () -> () { c }" :=
  (mkfunname name, mkfundef [::] [::] c [::] [::])
  (in custom fundecl at level 0, name constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u32 param, 1 u32 return *)
Notation "'fn' name ( 'reg' 'u32' p ) -> ( 'reg' 'u32' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U32] [:: mklvar p] c [:: aword U32] [:: mklvar p])
  (in custom fundecl at level 0, name constr at level 0, p constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u64 param, 1 u8 return *)
Notation "'fn' name ( 'reg' 'u64' p ) -> ( 'reg' 'u8' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U64] [:: mklvar p] c [:: aword U8] [:: mklvar p])
  (in custom fundecl at level 0, name constr at level 0, p constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u64 param, 1 u32 return *)
Notation "'fn' name ( 'reg' 'u64' p ) -> ( 'reg' 'u32' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U64] [:: mklvar p] c [:: aword U32] [:: mklvar p])
  (in custom fundecl at level 0, name constr at level 0, p constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u64 param, no return *)
Notation "'fn' name ( 'reg' 'u64' p ) -> () { c }" :=
  (mkfunname name, mkfundef [:: aword U64] [:: mklvar p] c [::] [::])
  (in custom fundecl at level 0, name constr at level 0, p constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 2 u64 params, no return *)
Notation "'fn' name ( 'reg' 'u64' p1 , 'reg' 'u64' p2 ) -> () { c }" :=
  (mkfunname name, mkfundef [:: aword U64; aword U64] [:: mklvar p1; mklvar p2] c [::] [::])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 3 u64 params, no return *)
Notation "'fn' name ( 'reg' 'u64' p1 , 'reg' 'u64' p2 , 'reg' 'u64' p3 ) -> () { c }" :=
  (mkfunname name, mkfundef [:: aword U64; aword U64; aword U64]
   [:: mklvar p1; mklvar p2; mklvar p3] c [::] [::])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, p3 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 2 u128 params, 1 u128 return *)
Notation "'fn' name ( 'reg' 'u128' p1 , 'reg' 'u128' p2 ) -> ( 'reg' 'u128' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U128; aword U128] [:: mklvar p1; mklvar p2]
   c [:: aword U128] [:: mklvar p1])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u128 param, 1 u128 return *)
Notation "'fn' name ( 'reg' 'u128' p ) -> ( 'reg' 'u128' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U128] [:: mklvar p] c [:: aword U128] [:: mklvar p])
  (in custom fundecl at level 0, name constr at level 0, p constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 2 u128 params, 2 u128 returns *)
Notation "'fn' name ( 'reg' 'u128' p1 , 'reg' 'u128' p2 ) -> ( 'reg' 'u128' , 'reg' 'u128' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U128; aword U128] [:: mklvar p1; mklvar p2]
   c [:: aword U128; aword U128] [:: mklvar p1; mklvar p2])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 3 u128 params, 2 u128 returns *)
Notation "'fn' name ( 'reg' 'u128' p1 , 'reg' 'u128' p2 , 'reg' 'u128' p3 ) -> ( 'reg' 'u128' , 'reg' 'u128' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U128; aword U128; aword U128] [:: mklvar p1; mklvar p2; mklvar p3]
   c [:: aword U128; aword U128] [:: mklvar p1; mklvar p2])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, p3 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* inline int param, inline int return *)
Notation "'fn' name ( 'inline' 'int' p ) -> ( 'inline' 'int' ) { c }" :=
  (mkfunname name, mkfundef [:: aint] [:: mklvar p] c [:: aint] [:: mklvar p])
  (in custom fundecl at level 0, name constr at level 0, p constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* inline int param + u128 param, u128 + u128 returns *)
Notation "'fn' name ( 'inline' 'int' p1 , 'reg' 'u128' p2 , 'reg' 'u128' p3 ) -> ( 'reg' 'u128' , 'reg' 'u128' ) { c }" :=
  (mkfunname name, mkfundef [:: aint; aword U128; aword U128] [:: mklvar p1; mklvar p2; mklvar p3]
   c [:: aword U128; aword U128] [:: mklvar p2; mklvar p3])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, p3 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u128 param + u128[11] param, 1 u128 return (cipher) *)
Notation "'fn' name ( 'reg' 'u128' p1 , 'reg' 'u128' '[' n ']' p2 ) -> ( 'reg' 'u128' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U128; aword U128] [:: mklvar p1; mklvar p2]
   c [:: aword U128] [:: mklvar p1])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, n constr at level 0, p2 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 1 u128 param, reg u128[N] return (keys_expand) *)
Notation "'fn' name ( 'reg' 'u128' p ) -> ( 'reg' 'u128' '[' n ']' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U128] [:: mklvar p] c [:: aword U128] [:: mklvar p])
  (in custom fundecl at level 0, name constr at level 0,
   p constr at level 0, n constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* 2 u64 params, 2 u64 returns *)
Notation "'fn' name ( 'reg' 'u64' p1 , 'reg' 'u64' p2 ) -> ( 'reg' 'u64' , 'reg' 'u64' ) { c }" :=
  (mkfunname name, mkfundef [:: aword U64; aword U64] [:: mklvar p1; mklvar p2]
   c [:: aword U64; aword U64] [:: mklvar p1; mklvar p2])
  (in custom fundecl at level 0, name constr at level 0,
   p1 constr at level 0, p2 constr at level 0, c custom jcmd at level 2)
  : expr_scope.

(* Generic: fn name WITH tyin params body tyout res *)
Notation "'fn' name 'WITH' tyin params 'BODY' body 'TYOUT' tyout 'RES' res" :=
  (mkfunname name, mkfundef tyin params body tyout res)
  (in custom fundecl at level 0,
   name constr at level 0, tyin constr at level 0, params constr at level 0,
   body constr at level 0, tyout constr at level 0, res constr at level 0)
  : expr_scope.

(* --- Program entry and exit --- *)

(* Generic function declaration: FN name WITH tyin params tyout res { body } *)
Notation "'FN' name 'WITH' tyin params tyout res { c }" :=
  (mkfunname name, mkfundef tyin params c tyout res)
  (in custom fundecl at level 0,
   name constr at level 0,
   tyin constr at level 0,
   params constr at level 0,
   tyout constr at level 0,
   res constr at level 0,
   c custom jcmd at level 2)
  : expr_scope.

Notation "'prog:(' p ')'" :=
  (mkprog p)
  (p custom prog at level 2,
   format "'prog:(' p ')'")
  : expr_scope.

(* A program is a sequence of function declarations, built right-recursively. *)
Notation "f" :=
  (cons f nil)
  (in custom prog at level 2,
   f custom fundecl at level 0)
  : expr_scope.

Notation "f p" :=
  (f :: p)
  (in custom prog at level 2,
   f custom fundecl at level 0,
   p custom prog at level 2)
  : expr_scope.

End InstructionNotations.

(* ========================================================================= *)
(* Also keep the old constr-level notations for backwards compatibility.     *)
(* ========================================================================= *)

Module ConstrNotations.

Import ExpressionNotations.
Open Scope expr_scope.

(* --- Assignment instructions: ASSIGN "x" <<-Nu e --- *)

Notation "'ASSIGN' x '<<-' 8 'u' e"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U8) e))   (at level 200, x at level 0, e custom expr at level 13) : expr_scope.
Notation "'ASSIGN' x '<<-' 16 'u' e"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U16) e))  (at level 200, x at level 0, e custom expr at level 13) : expr_scope.
Notation "'ASSIGN' x '<<-' 32 'u' e"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U32) e))  (at level 200, x at level 0, e custom expr at level 13) : expr_scope.
Notation "'ASSIGN' x '<<-' 64 'u' e"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U64) e))  (at level 200, x at level 0, e custom expr at level 13) : expr_scope.
Notation "'ASSIGN' x '<<-' 128 'u' e" := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U128) e)) (at level 200, x at level 0, e custom expr at level 13) : expr_scope.
Notation "'ASSIGN' x '<<-' 256 'u' e" := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U256) e)) (at level 200, x at level 0, e custom expr at level 13) : expr_scope.

Notation "'ASSIGN' x '<<-' 'bool' e" := (mkI' (Cassgn (Lvar (mklvar x)) AT_none abool e)) (at level 200, x at level 0, e custom expr at level 13) : expr_scope.
Notation "'ASSIGN' x '<<-' 'int' e"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none aint e))  (at level 200, x at level 0, e custom expr at level 13) : expr_scope.

(* --- Control flow --- *)

Notation "'IF' e 'THEN' c1 'ELSE' c2" :=
  (mkI' (Cif e c1 c2))
  (at level 200, e custom expr at level 13,
   c1 at level 200, c2 at level 200) : expr_scope.

Notation "'WHILE' e 'DO' c" :=
  (mkI' (Cwhile NoAlign [::] e dummy_instr_info c))
  (at level 200, e custom expr at level 13, c at level 200) : expr_scope.

Notation "'FOR' v 'FROM' e1 'TO' e2 'DO' c" :=
  (mkI' (Cfor (mklvar v) (UpTo, e1, e2) c))
  (at level 200, v at level 0,
   e1 custom expr at level 13, e2 custom expr at level 13,
   c at level 200) : expr_scope.

Notation "'FOR' v 'FROM' e1 'DOWNTO' e2 'DO' c" :=
  (mkI' (Cfor (mklvar v) (DownTo, e2, e1) c))
  (at level 200, v at level 0,
   e1 custom expr at level 13, e2 custom expr at level 13,
   c at level 200) : expr_scope.

(* --- Function call --- *)
Notation "'CALL' f args 'RETURNING' lvs" :=
  (mkI' (Ccall (map (fun x => Lvar (mklvar x)) lvs) (mkfunname f) args))
  (at level 200, f at level 0, args at level 0, lvs at level 0) : expr_scope.

(* --- Function notation: common arities --- *)

Notation "'FN' name '(' ')' '{' body '}'" :=
  (mkfunname name, mkfundef [::] [::] body [::] [::])
  (at level 200, name at level 0, body at level 200) : expr_scope.

Notation "'FN' name '(' p ':' 'u64' ')' '->' 'u64' '{' body '}' 'RETURNING' r" :=
  (mkfunname name, mkfundef
    [:: aword U64] [:: mklvar p]
    body
    [:: aword U64] [:: mklvar r])
  (at level 200, name at level 0, p at level 0, r at level 0,
   body at level 200) : expr_scope.

Notation "'FN' name '(' p1 ':' 'u64' ',' p2 ':' 'u64' ')' '->' 'u64' '{' body '}' 'RETURNING' r" :=
  (mkfunname name, mkfundef
    [:: aword U64; aword U64] [:: mklvar p1; mklvar p2]
    body
    [:: aword U64] [:: mklvar r])
  (at level 200, name at level 0, p1 at level 0, p2 at level 0,
   r at level 0, body at level 200) : expr_scope.

Notation "'FN' name '(' p1 ':' 'u64' ',' p2 ':' 'u64' ',' p3 ':' 'u64' ')' '->' 'u64' '{' body '}' 'RETURNING' r" :=
  (mkfunname name, mkfundef
    [:: aword U64; aword U64; aword U64]
    [:: mklvar p1; mklvar p2; mklvar p3]
    body
    [:: aword U64] [:: mklvar r])
  (at level 200, name at level 0, p1 at level 0, p2 at level 0,
   p3 at level 0, r at level 0, body at level 200) : expr_scope.

(* Generic: explicit type/param/result lists *)
Notation "'FN' name 'WITH' tyin params body tyout res" :=
  (mkfunname name, mkfundef tyin params body tyout res)
  (at level 200, name at level 0, tyin at level 0, params at level 0,
   body at level 0, tyout at level 0, res at level 0) : expr_scope.

End ConstrNotations.

(* ========================================================================= *)
(* Tests                                                                     *)
(* ========================================================================= *)

Import ExpressionNotations.
Open Scope expr_scope.
Unset Printing Notations.

(* ---- Expression tests ---- *)
Section ExprTests.
Check expr:( "x" +64u "y" ).
Check expr:( "z" *64u "x" +64u #3 ).
Check expr:( true ?32u "x" &32u "y" : "z" ).
Check expr:( "y" <<r 64u "z" ).
Check expr:( "y" <<64u "y" ).
Check expr:( "y" >>64u "y" ).
Check expr:( "x" ==64u "y" ).
Check expr:( "b" && "x" <=64u "y" ).
Check expr:( "x" !=64u "y" || "x" <64u "y" ).
Check expr:( #5 -i #2 ).
Check expr:( true || false && (#1 -i #10) ==i false ).
Check expr:( (cast 64u) #3 ).
Check expr:( "x" ^64u "y" ).
Check expr:( "x" |64u "y" ).
Check expr:( "x" <64s "y" ).
Check expr:( "x" /64u "y" ).
Check expr:( "x" /64s "y" ).
Check expr:( "x" %64u "y" ).
Check expr:( "x" >>64s "y" ).
Check expr:( ~64u "x" ).
Check expr:( -64u "x" ).
End ExprTests.

(* ---- Constr-level instruction and program tests ---- *)
Section ConstrTests.
Context {asm_op : Type} {asmop : asmOp asm_op}.
Import ConstrNotations.
Open Scope expr_scope.

(* Single assignment *)
Check (ASSIGN "r" <<- 64u "x" +64u "y").

(* Instruction sequence using [:: ; ] *)
Check [:: ASSIGN "r" <<- 64u "x" +64u "y"
       ;  ASSIGN "r" <<- 64u "r" -64u #1 ].

(* If/else *)
Check (IF "x" ==64u "y"
       THEN [:: ASSIGN "r" <<- 64u "x" ]
       ELSE [:: ASSIGN "r" <<- 64u "y" ]).

(* While loop *)
Check (WHILE "x" <64u "y"
       DO [:: ASSIGN "x" <<- 64u "x" +64u #1 ]).

(* For loop *)
Check (FOR "i" FROM #0 TO #10
       DO [:: ASSIGN "x" <<- 64u "x" +64u #1 ]).

(* Function: fn add(x : u64, y : u64) -> u64 *)
Check (FN "add" ("x" : u64, "y" : u64) -> u64 {
         [:: ASSIGN "r" <<- 64u "x" +64u "y" ]
       } RETURNING "r").

(* Program with two functions *)
Check (mkprog [::
  FN "add" ("x" : u64, "y" : u64) -> u64 {
    [:: ASSIGN "r" <<- 64u "x" +64u "y" ]
  } RETURNING "r"
; FN "sub" ("x" : u64, "y" : u64) -> u64 {
    [:: ASSIGN "r" <<- 64u "x" -64u "y" ]
  } RETURNING "r"
]).

End ConstrTests.

(* ---- Custom-entry instruction and program tests ---- *)
Section ProgTests.
Context {asm_op : Type} {asmop : asmOp asm_op}.
Import InstructionNotations.
Open Scope expr_scope.

(* Single command: assignment *)
Check cmd:(
  "r" = ("x" +64u "y") ; /* u64 */
).

(* Multiple instructions *)
Check cmd:(
  "r" = ("x" +64u "y") ; /* u64 */
  "r" = ("r" -64u #1) ; /* u64 */
).

(* Return instruction *)
Check cmd:(
  return ("r") ;
).

(* If/else *)
Check cmd:(
  if ("x" ==64u "y") {
    "r" = "x" ; /* u64 */
  } else {
    "r" = "y" ; /* u64 */
  }
).

(* While loop *)
Check cmd:(
  while ("x" <64u "y") {
    "x" = ("x" +64u #1) ; /* u64 */
  }
).

(* For loop with parens around bounds *)
Check cmd:(
  for "i" = (#0) to (#10) {
    "x" = ("x" +64u #1) ; /* u64 */
  }
).

(* Full program matching jasminc output:
     fn add (reg u64 x, reg u64 y) -> (reg u64) {
       r = (x +64u y);  // u64
       return (r);
     }
*)
Check prog:(
  fn "add" (reg u64 "x" , reg u64 "y") -> (reg u64) {
    "r" = ("x" +64u "y") ; /* u64 */
    return ("r") ;
  }
).

(* Program with two functions *)
Check prog:(
  fn "add" (reg u64 "x" , reg u64 "y") -> (reg u64) {
    "r" = ("x" +64u "y") ; /* u64 */
    return ("r") ;
  }
  fn "sub" (reg u64 "x" , reg u64 "y") -> (reg u64) {
    "r" = ("x" -64u "y") ; /* u64 */
    return ("r") ;
  }
).

(* No-arg function *)
Check prog:(
  fn "nop" () {
    "x" = (cast 64u) #0 ; /* u64 */
  }
).

(* ---- Tests from real jasminc -coq output ---- *)

(* extraction-unit-tests/exp.jazz: exp2 function *)
Check prog:(
  fn "exp2" (reg u64 "x.200" , reg u64 "y.201") -> (reg u64) {
    "z.202" = "x.200" +64u "y.201" ; /* u64 */
    return ("z.202") ;
  }
).

(* extraction-unit-tests/exp.jazz: exp function (uses ui64 operators) *)
Check prog:(
  fn "exp" (reg ui64 "x.203" , reg ui64 "y.204") -> (reg ui64) {
    "a.206" = "x.203" +64ui "y.204" ; /* u64 */
    "b.207" = "x.203" -64ui "y.204" ; /* u64 */
    "c.205" = "a.206" *64ui "b.207" ; /* u64 */
    return ("c.205") ;
  }
).

(* extraction-unit-tests/loops.jazz: forty function *)
Check prog:(
  fn "forty" () -> (reg u32) {
    "j.205" = #0 ; /* int */
    for "i.206" = (#10) downto (#5) {
      "j.205" = "j.205" +i "i.206" ; /* int */
    }
    "r.204" = (cast 32u) "j.205" ; /* u32 */
    return ("r.204") ;
  }
).

(* extraction-unit-tests/sdiv.jazz: main function (multi-return) *)
Check prog:(
  fn "main" () -> (reg u64 , reg u64) {
    "a.192" = (cast 64u) #1 ; /* u64 */
    "b.193" = (cast 64u) (-i #1) ; /* u64 */
    "c.190" = "a.192" /64s "b.193" ; /* u64 */
    "d.194" = (cast 64u) (-i #4) ; /* u64 */
    "e.195" = (cast 64u) #3 ; /* u64 */
    "f.191" = "d.194" %64s "e.195" ; /* u64 */
    return ("c.190" , "f.191") ;
  }
).

(* extraction-unit-tests/gcd.jazz: euclid function (while loop, wint cast) *)
Check prog:(
  fn "euclid" (reg ui64 "a.196" , reg ui64 "b.197") -> (reg ui64) {
    while ("a.196" !=64ui (64ui) #0) {
      "r.198" = "b.197" %64ui "a.196" ; /* u64 */
      "b.197" = "a.196" ; /* u64 */
      "a.196" = "r.198" ; /* u64 */
    }
    return ("b.197") ;
  }
).

(* extraction-unit-tests/gcd.jazz: gcd function (function call with /* call */) *)
Check prog:(
  fn "gcd" (reg ui64 "x.194" , reg ui64 "y.195") -> (reg ui64) {
    "y.195" = "y.195" ; /* u64 */
    "x.194" = call "euclid" ("x.194" , "y.195") ; /* call */
    return ("x.194") ;
  }
).

(* extraction-unit-tests/add_in_mem.jazz: memory load/store, empty return *)
Check prog:(
  fn "add_mem" (reg ui64 "out.194" , reg ui64 "in1.195" , reg ui64 "in2.196" , reg ui64 "len.197") -> () {
    "i.198" = (64ui) #0 ; /* u64 */
    while ("i.198" <64ui "len.197") {
      "x.199" = [:u64 (cast 64u) ("in1.195" +64ui (64ui) #8 *64ui "i.198")] ; /* u64 */
      "y.200" = [:u64 (cast 64u) ("in2.196" +64ui (64ui) #8 *64ui "i.198")] ; /* u64 */
      "d.201" = "x.199" +64u "y.200" ; /* u64 */
      [:u64 (cast 64u) ("out.194" +64ui (64ui) #8 *64ui "i.198")] = "d.201" ; /* u64 */
      "i.198" = "i.198" +64ui (64ui) #1 ; /* u64 */
    }
    return () ;
  }
).

(* ---- Tests for new notations ---- *)

(* extraction-unit-tests/string.jazz: array access in expression *)
Check prog:(
  fn "main" () -> (reg u32) {
    "x.183" = "@ " ; /* u8 */
    "r.182" = (cast 32u) #0 ; /* u32 */
    "r.182" = "r.182" +32u (cast 32u) "x.183"[:u8 #0] ; /* u32 */
    "r.182" = "r.182" <<32u (cast 8u) #8 ; /* u32 */
    "r.182" = "r.182" +32u (cast 32u) "x.183"[:u8 #1] ; /* u32 */
    return ("r.182") ;
  }
).

(* Memory store with different sizes *)
Check cmd:(
  [:u8 "p"] = "x" ; /* u8 */
).

Check cmd:(
  [:u16 "p"] = "x" ; /* u16 */
).

Check cmd:(
  [:u32 "p"] = "x" ; /* u32 */
).

Check cmd:(
  [:u128 "p"] = "x" ; /* u128 */
).

Check cmd:(
  [:u256 "p"] = "x" ; /* u256 */
).

(* Array lval assignment *)
Check cmd:(
  "rkeys"[:u128 #0] = "key" ; /* u128 */
).

Check cmd:(
  "t"[:u64 "i"] = (cast 64u) "i" ; /* u64 */
).

(* Array lval with int index *)
Check cmd:(
  "rkeys"[#0] = "key" ; /* u128 */
).

(* If without else *)
Check cmd:(
  if "x" !=64u (cast 64u) #0 {
    "result" = "x" ; /* u64 */
  }
).

(* While with pre-body *)
Check cmd:(
  while { "x" = "y" ; /* u64 */ } ("x" !=64u (cast 64u) #0)
).

(* While with pre-body and post-body *)
Check cmd:(
  while { "x" = "y" ; /* u64 */ } ("x" !=64u (cast 64u) #0) { "y" = "z" ; /* u64 */ }
).

(* 3-value return *)
Check cmd:(
  return ("a", "b", "c") ;
).

(* Untyped ternary *)
Check expr:( "e" ? "x" : "y" ).

(* Combine flags *)
Check expr:( _EQ("a", "b", "c", "d") ).
Check expr:( _uLT("a", "b", "c", "d") ).
Check expr:( _sLT("a", "b", "c", "d") ).

(* Intrinsic calls using coq_copn *)
Check cmd:(
  coq_copn [:: Lvar (mklvar "x")] (mkopn "MOV_32") [:: (expr:("y") : pexpr)] ;
).

Check cmd:(
  coq_copn [:: Lvar (mklvar "x")] (mkopn "ADD_64") [:: (expr:("y") : pexpr); (expr:("z") : pexpr)] ;
).

Check cmd:(
  coq_copn [:: Lvar (mklvar "x")] (mkopn "SHLD_16") [:: (expr:("a") : pexpr); (expr:("b") : pexpr); (expr:((cast 8u) #3) : pexpr)] ;
).

Check cmd:(
  coq_copn [:: Lvar (mklvar "x")] (mkopn "set0_128") [::] ;
).

Check cmd:(
  coq_copn [:: Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lvar (mklvar "x")] (mkopn "ADD_8") [:: (expr:("a") : pexpr); (expr:("b") : pexpr)] ;
).

(* Function call with 2 returns *)
Check cmd:(
  "a", "b" = call "key_combine"("x", "y", "z") ; /* call */
).

(* opsizes.jazz tests *)
Check prog:(
  fn "reg32_test" (reg u32 "x.295") -> (reg u32) {
    "y.296" = "x.295" ; /* u32 */
    "y.296" = "y.296" +32u "x.295" ; /* u32 */
    return ("y.296") ;
  }
).

Check prog:(
  fn "pluseq" (reg u64 "x.279") -> (reg u8) {
    "c.281" = (cast 32u) #0 ; /* u32 */
    "c.281" = "c.281" *32u "x.279" ; /* u32 */
    "b.282" = (cast 16u) #0 ; /* u16 */
    "a.280" = (cast 8u) #0 ; /* u8 */
    "b.282" = "b.282" -16u "c.281" ; /* u16 */
    "a.280" = "a.280" +8u "b.282" ; /* u8 */
    return ("a.280") ;
  }
).

(* ifelse.jazz test *)
Check prog:(
  fn "test" (reg u64 "x.184" , reg u64 "y.185") -> (reg u64) {
    if "x.184" !=64u (cast 64u) #0 {
      "result.186" = "x.184" ; /* u64 */
    } else {
      if "y.185" !=64u (cast 64u) #0 {
        "result.186" = "y.185" ; /* u64 */
      } else {
        "result.186" = (cast 64u) #0 ; /* u64 */
      }
    }
    return ("result.186") ;
  }
).

(* aes.jazz: AddRoundKey function *)
Check prog:(
  fn "AddRoundKey" (reg u128 "state.306" , reg u128 "rk.307") -> (reg u128) {
    "state.306" = "state.306" ^128u "rk.307" ; /* u128 */
    return ("state.306") ;
  }
).

(* aes.jazz: inline int function *)
Check prog:(
  fn "RCON" (inline int "i.308") -> (inline int) {
    "c.309" =
      "i.308" ==i #1 ? #1 : ("i.308" ==i #2 ? #2 : ("i.308" ==i #3 ? #4 : ("i.308" ==i #4 ? #8 : ("i.308" ==i #5 ? #16 : ("i.308" ==i #6 ? #32 : ("i.308" ==i #7 ? #64 : ("i.308" ==i #8 ? #128 : ("i.308" ==i #9 ? #27 : #54)))))))); /* int */
    return ("c.309") ;
  }
).

(* aes.jazz: cipher function with array param *)
Check prog:(
  fn "cipher" (reg u128 "in.302" , reg u128[11] "rks.303") -> (reg u128) {
    "state.304" = "in.302" ; /* u128 */
    "state.304" = "state.304" ^128u "rks.303"[:u128 #0] ; /* u128 */
    for "round.305" = (#1) to (#10) {
      coq_copn [:: Lvar (mklvar "state.304")] (mkopn "AESENC") [:: (expr:("state.304") : pexpr); (expr:("rks.303"[:u128 "round.305"]) : pexpr)] ;
    }
    coq_copn [:: Lvar (mklvar "state.304")] (mkopn "AESENCLAST") [:: (expr:("state.304") : pexpr); (expr:("rks.303"[:u128 #10]) : pexpr)] ;
    return ("state.304") ;
  }
).

(* aes.jazz: key_combine with 2 returns *)
Check prog:(
  fn "key_combine" (reg u128 "rkey.299" , reg u128 "temp1.300" , reg u128 "temp2.301") -> (reg u128 , reg u128) {
    coq_copn [:: Lvar (mklvar "temp1.300")] (mkopn "VPSHUFD_128")
      [:: (expr:("temp1.300") : pexpr);
          ((PappN (Opack U8 PE2) [:: (expr:(#3) : pexpr); (expr:(#3) : pexpr); (expr:(#3) : pexpr); (expr:(#3) : pexpr)]) : pexpr)] ;
    "rkey.299" = "rkey.299" ^128u "temp2.301" ; /* u128 */
    "rkey.299" = "rkey.299" ^128u "temp1.300" ; /* u128 */
    return ("rkey.299", "temp2.301") ;
  }
).

(* shift.jazz: memory store with u16 *)
Check cmd:(
  [:u16 "p" +64u (cast 64u) #0] = "a" ; /* u16 */
).

(* loops.jazz: for_nest function *)
Check prog:(
  fn "for_nest" () -> (reg u32) {
    "k.201" = #0 ; /* int */
    for "i.203" = (#0) to (#10 +i #10) {
      for "j.202" = (#0) to (#10 *i #10) {
        "k.201" = "k.201" +i #1 ; /* int */
      }
    }
    "r.200" = (cast 32u) "k.201" ; /* u32 */
    return ("r.200") ;
  }
).

(* aes.jazz: key_expand with inline int + u128 params *)
Check prog:(
  fn "key_expand" (inline int "rcon.295" , reg u128 "rkey.296" , reg u128 "temp2.297") -> (reg u128 , reg u128) {
    coq_copn [:: Lvar (mklvar "temp1.298")] (mkopn "VAESKEYGENASSIST") [:: (expr:("rkey.296") : pexpr); (expr:((cast 8u) "rcon.295") : pexpr)] ;
    "rkey.296", "temp2.297" = call "key_combine"("rkey.296", "temp1.298", "temp2.297") ; /* call */
    return ("rkey.296", "temp2.297") ;
  }
).

(* aes.jazz: keys_expand with u128 return and array set *)
Check prog:(
  fn "keys_expand" (reg u128 "key.290") -> (reg u128[11]) {
    "rkeys.291"[#0] = "key.290" ; /* u128 */
    coq_copn [:: Lvar (mklvar "temp2.292")] (mkopn "set0_128") [:: ] ;
    for "i.293" = (#1) to (#11) {
      "rcon.294" = call "RCON"("i.293") ; /* call */
      "key.290", "temp2.292" = call "key_expand"("rcon.294", "key.290", "temp2.292") ; /* call */
      "rkeys.291"["i.293"] = "key.290" ; /* u128 */
    }
    return ("rkeys.291") ;
  }
).

(* aes.jazz: aes_enc with 3 u64 params, no return *)
Check prog:(
  fn "aes_enc" (reg u64 "pkey.280" , reg u64 "pin.281" , reg u64 "pout.282") -> () {
    "in.283" = [:u128 "pin.281"] ; /* u128 */
    "key.284" = [:u128 "pkey.280"] ; /* u128 */
    "out.285" = call "_aes_enc"("key.284", "in.283") ; /* call */
    [:u128 "pout.282"] = "out.285" ; /* u128 */
    return () ;
  }
).

(* test_add.jazz: test3 with function call returning 0 results *)
Check prog:(
  fn "test3" () -> (reg u64) {
    "tmp.205" = call "test1"() ; /* call */
    "j.204" = (cast 64u) "tmp.205" ; /* u64 */
    "i.206" = call "test2"() ; /* call */
    while ("j.204" <=64u (cast 64u) #12) {
      "j.204" = "j.204" +64u "i.206" ; /* u64 */
    }
    return ("j.204") ;
  }
).

(* opsizes.jazz: primop_test with intrinsics *)
Check prog:(
  fn "primop_test" (reg u64 "x.283") -> (reg u8) {
    "d.285" = "x.283" ; /* u64 */
    coq_copn [:: Lvar (mklvar "c.286")] (mkopn "MOV_32") [:: (expr:("d.285") : pexpr)] ;
    coq_copn [:: Lvar (mklvar "b.287")] (mkopn "MOV_16") [:: (expr:("c.286") : pexpr)] ;
    coq_copn [:: Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lnone dummy_var_info abool; Lvar (mklvar "a.284")] (mkopn "ADD_8") [:: (expr:("b.287") : pexpr); (expr:("b.287") : pexpr)] ;
    return ("a.284") ;
  }
).

(* opsizes.jazz: test_immediate with u256 ops *)
Check prog:(
  fn "test_immediate" () -> (reg u32) {
    "r.276" = (cast 256u) #42 &256u (cast 256u) #10 ; /* u32 */
    return ("r.276") ;
  }
).

(* test_casts.jazz *)
Check prog:(
  fn "opsize_test" (reg u64 "x.184") -> (reg u8) {
    "y.186" = "x.184" ; /* u32 */
    "y.186" = "y.186" +32u "x.184" ; /* u32 */
    "y.186" = "y.186" <32u (cast 32u) #0 ? "x.184" : "y.186" ; /* u32 */
    "x.184" = "x.184" >>64u (cast 8u) #32 ; /* u64 */
    "x.184" = "x.184" >>64s (cast 8u) #8 ; /* u64 */
    "r.185" = "x.184" ; /* u8 */
    "r.185" = "r.185" >>8u (cast 8u) #1 ; /* u8 */
    "r.185" = "r.185" ^8u "y.186" ; /* u8 */
    return ("r.185") ;
  }
).

Check prog:(
(* fn "sipround" (reg u64[4] "v.229") -> (reg u64[4]) *)
FN "sipround" WITH
[:: (aarr U64 4%positive)]
[:: mklvar "v.229"]
[:: (aarr U64 4%positive)]
[:: mklvar "v.229"]
{
  "v.229"[:u64 #0] = "v.229"[:u64 #0] +64u "v.229"[:u64 #1]; /* u64 */
  "v.229"[:u64 #1] = "v.229"[:u64 #1] <<r 64u (cast 8u) #13; /* u64 */
  "v.229"[:u64 #1] = "v.229"[:u64 #1] ^64u "v.229"[:u64 #0]; /* u64 */
  "v.229"[:u64 #0] = "v.229"[:u64 #0] <<r 64u (cast 8u) #32; /* u64 */
  "v.229"[:u64 #2] = "v.229"[:u64 #2] +64u "v.229"[:u64 #3]; /* u64 */
  "v.229"[:u64 #3] = "v.229"[:u64 #3] <<r 64u (cast 8u) #16; /* u64 */
  "v.229"[:u64 #3] = "v.229"[:u64 #3] ^64u "v.229"[:u64 #2]; /* u64 */
  "v.229"[:u64 #0] = "v.229"[:u64 #0] +64u "v.229"[:u64 #3]; /* u64 */
  "v.229"[:u64 #3] = "v.229"[:u64 #3] <<r 64u (cast 8u) #21; /* u64 */
  "v.229"[:u64 #3] = "v.229"[:u64 #3] ^64u "v.229"[:u64 #0]; /* u64 */
  "v.229"[:u64 #2] = "v.229"[:u64 #2] +64u "v.229"[:u64 #1]; /* u64 */
  "v.229"[:u64 #1] = "v.229"[:u64 #1] <<r 64u (cast 8u) #17; /* u64 */
  "v.229"[:u64 #1] = "v.229"[:u64 #1] ^64u "v.229"[:u64 #2]; /* u64 */
  "v.229"[:u64 #2] = "v.229"[:u64 #2] <<r 64u (cast 8u) #32; /* u64 */
  return ("v.229");
}

End ProgTests.

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
  (in custom expr at level 0, z constr,
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

(* Additional cast sizes: (cast 8u), (cast 16u), (cast 32u), (cast 128u), (cast 256u) *)
(* (cast 64u) is already defined above *)

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
(* Modeled as assignment of the variable to itself with u64 type. *)

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

(* --- Control flow --- *)

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

(* --- Program entry and exit --- *)

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

(* extraction-unit-tests/gcd.jazz: gcd function — skipped, needs function call notation *)

End ProgTests.

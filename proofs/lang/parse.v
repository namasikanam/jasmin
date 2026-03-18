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

End ExpressionNotations.

(* ========================================================================= *)
(* Tests                                                                     *)
(* ========================================================================= *)

Import ExpressionNotations.
Open Scope expr_scope.
Unset Printing Notations.

Section Tests.

(* --- Jasmin: x +64u y --- *)
Check expr:( "x" +64u "y" ).
(* Papp2 (Oadd (Op_w U64)) (mkvar "x") (mkvar "y") *)

(* --- Jasmin: z *64u x +64u 3 --- *)
Check expr:( "z" *64u "x" +64u #3 ).
(* Papp2 (Oadd (Op_w U64)) (Papp2 (Omul (Op_w U64)) (mkvar "z") (mkvar "x")) (Pconst 3) *)

(* --- Jasmin: true ? x &32u y : z --- *)
Check expr:( true ?32u "x" &32u "y" : "z" ).
(* Pif (aword U32) (Pbool true) (Papp2 (Oland U32) (mkvar "x") (mkvar "y")) (mkvar "z") *)

(* --- Jasmin: y <<r 64u z (rotate left) --- *)
Check expr:( "y" <<r 64u "z" ).
(* Papp2 (Orol U64) (mkvar "y") (mkvar "z") *)

(* --- Jasmin: y <<64u y --- *)
Check expr:( "y" <<64u "y" ).
(* Papp2 (Olsl (Op_w U64)) (mkvar "y") (mkvar "y") *)

(* --- Jasmin: y >>64u y --- *)
Check expr:( "y" >>64u "y" ).
(* Papp2 (Olsr U64) (mkvar "y") (mkvar "y") *)

(* --- Jasmin: x ==64u y --- *)
Check expr:( "x" ==64u "y" ).
(* Papp2 (Oeq (Op_w U64)) (mkvar "x") (mkvar "y") *)

(* --- Jasmin: b && x <=64u y --- *)
Check expr:( "b" && "x" <=64u "y" ).
(* Papp2 Oand (mkvar "b") (Papp2 (Ole (Cmp_w Unsigned U64)) (mkvar "x") (mkvar "y")) *)

(* --- Jasmin: x !=64u y || x <64u y --- *)
Check expr:( "x" !=64u "y" || "x" <64u "y" ).
(* Papp2 Oor (Papp2 (Oneq (Op_w U64)) ...) (Papp2 (Olt (Cmp_w Unsigned U64)) ...) *)

(* --- Integer arithmetic --- *)
Check expr:( #5 -i #2 ).
(* Papp2 (Osub Op_int) 5 2 *)

(* --- Mixed boolean/integer --- *)
Check expr:( true || false && (#1 -i #10) ==i false ).

(* --- Word-of-int cast: (cast 64u) #3 --- *)
Check expr:( (cast 64u) #3 ).
(* Papp1 (Oword_of_int U64) (Pconst 3) *)

(* --- Bitwise operations --- *)
Check expr:( "x" ^64u "y" ).
Check expr:( "x" |64u "y" ).

(* --- Signed comparison --- *)
Check expr:( "x" <64s "y" ).

(* --- Unsigned/signed division and modulo --- *)
Check expr:( "x" /64u "y" ).
Check expr:( "x" /64s "y" ).
Check expr:( "x" %64u "y" ).

(* --- Arithmetic right shift --- *)
Check expr:( "x" >>64s "y" ).

(* --- Bitwise NOT and word negation --- *)
Check expr:( ~64u "x" ).
Check expr:( -64u "x" ).

End Tests.

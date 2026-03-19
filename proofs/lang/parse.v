(* Notations to parse Jasmin programs.

   We assume the programs are well typed and elaborated.
   This means that every operator has type annotations, that assignments have
   type annotations, etc.
   Variables are strings.
   Integer constants are prefixed with #, e.g. #3.
*)

From mathcomp Require Import ssreflect ssrfun.

Require Import expr.

Axiom (mkvar : string -> var).
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
Open Scope string_scope.

Notation mkgvar := (fun x => mk_gvar (mk_var_i (mkvar x))) (only parsing).

(* --- Entry and exit --- *)

Notation "expr:( e )" :=
  (e)
  (e custom expr at level 0,
   format "'expr:(' e ')'")
  : expr_scope.

Notation "rocq:( e )" :=
  (e)
  (in custom expr at level 0,
   e constr at level 0)
  : expr_scope.

Notation "( e )" :=
  (e)
  (in custom expr at level 0, e custom expr)
  : expr_scope.

(* --- Atoms --- *)

(* Variables are string literals, mapped through mkgvar. *)
Notation "x" := (mkgvar x)
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

(* Wrong: it's ! *)
(* Bitwise NOT: ~Nu e *)
Notation "! 8 'u' e"   := (Papp1 (Olnot U8) e)   (in custom expr at level 2) : expr_scope.
Notation "! 16 'u' e"  := (Papp1 (Olnot U16) e)  (in custom expr at level 2) : expr_scope.
Notation "! 32 'u' e"  := (Papp1 (Olnot U32) e)  (in custom expr at level 2) : expr_scope.
Notation "! 64 'u' e"  := (Papp1 (Olnot U64) e)  (in custom expr at level 2) : expr_scope.
Notation "! 128 'u' e" := (Papp1 (Olnot U128) e) (in custom expr at level 2) : expr_scope.
Notation "! 256 'u' e" := (Papp1 (Olnot U256) e) (in custom expr at level 2) : expr_scope.

(* What about all the other casts? *)

(* ---- Casts between all types ---- *)

(* Oword_of_int: int → word. Syntax: (cast Nu) e *)
Notation "'(cast' 8 'u' ')' e"   := (Papp1 (Oword_of_int U8) e)   (in custom expr at level 2) : expr_scope.
Notation "'(cast' 16 'u' ')' e"  := (Papp1 (Oword_of_int U16) e)  (in custom expr at level 2) : expr_scope.
Notation "'(cast' 32 'u' ')' e"  := (Papp1 (Oword_of_int U32) e)  (in custom expr at level 2) : expr_scope.
Notation "'(cast' 64 'u' ')' e"  := (Papp1 (Oword_of_int U64) e)  (in custom expr at level 2) : expr_scope.
Notation "'(cast' 128 'u' ')' e" := (Papp1 (Oword_of_int U128) e) (in custom expr at level 2) : expr_scope.
Notation "'(cast' 256 'u' ')' e" := (Papp1 (Oword_of_int U256) e) (in custom expr at level 2) : expr_scope.

(* Ozeroext: word → word (zero-extend). Syntax: (zeroext Nu) e *)
Notation "'(zeroext' 8 'u' ')' e"   := (Papp1 (Ozeroext U8 U8) e)     (in custom expr at level 2) : expr_scope.
Notation "'(zeroext' 16 'u' ')' e"  := (Papp1 (Ozeroext U16 U16) e)   (in custom expr at level 2) : expr_scope.
Notation "'(zeroext' 32 'u' ')' e"  := (Papp1 (Ozeroext U32 U32) e)   (in custom expr at level 2) : expr_scope.
Notation "'(zeroext' 64 'u' ')' e"  := (Papp1 (Ozeroext U64 U64) e)   (in custom expr at level 2) : expr_scope.
Notation "'(zeroext' 128 'u' ')' e" := (Papp1 (Ozeroext U128 U128) e) (in custom expr at level 2) : expr_scope.
Notation "'(zeroext' 256 'u' ')' e" := (Papp1 (Ozeroext U256 U256) e) (in custom expr at level 2) : expr_scope.

(* Osignext: word → word (sign-extend). Syntax: (signext Nu) e *)
Notation "'(signext' 8 'u' ')' e"   := (Papp1 (Osignext U8 U8) e)     (in custom expr at level 2) : expr_scope.
Notation "'(signext' 16 'u' ')' e"  := (Papp1 (Osignext U16 U16) e)   (in custom expr at level 2) : expr_scope.
Notation "'(signext' 32 'u' ')' e"  := (Papp1 (Osignext U32 U32) e)   (in custom expr at level 2) : expr_scope.
Notation "'(signext' 64 'u' ')' e"  := (Papp1 (Osignext U64 U64) e)   (in custom expr at level 2) : expr_scope.
Notation "'(signext' 128 'u' ')' e" := (Papp1 (Osignext U128 U128) e) (in custom expr at level 2) : expr_scope.
Notation "'(signext' 256 'u' ')' e" := (Papp1 (Osignext U256 U256) e) (in custom expr at level 2) : expr_scope.

(* Oint_of_word: word → int. Syntax: (uint) e or (sint) e *)
Notation "'(uint)' e" := (Papp1 (Oint_of_word Unsigned U64) e) (in custom expr at level 2) : expr_scope.
Notation "'(sint)' e" := (Papp1 (Oint_of_word Signed U64) e) (in custom expr at level 2) : expr_scope.

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

(* What? *)
(* Generic fallback with explicit atype: e1 ?[ty] e2 : e3 *)
Notation "e1 '?[' ty ']' e2 ':' e3" :=
  (Pif ty e1 e2 e3)
  (in custom expr at level 13, ty constr at level 0,
   e2 custom expr, e3 custom expr at level 13)
  : expr_scope.

(* ========================================================================= *)
(* Integer operators: +i, -i, *i (Op_int variants).                         *)
(* ========================================================================= *)

(* Isn't this defined in 185? *)
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

(* ---- Wint casts (Owi1) ---- *)

(* WIwint_of_int: int → wint. Syntax: (Nui) or (Nsi) *)
Notation "'(' 8 'ui' ')' e"   := (Papp1 (Owi1 Unsigned (WIwint_of_int U8)) e)   (in custom expr at level 2) : expr_scope.
Notation "'(' 16 'ui' ')' e"  := (Papp1 (Owi1 Unsigned (WIwint_of_int U16)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(' 32 'ui' ')' e"  := (Papp1 (Owi1 Unsigned (WIwint_of_int U32)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(' 64 'ui' ')' e"  := (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(' 128 'ui' ')' e" := (Papp1 (Owi1 Unsigned (WIwint_of_int U128)) e) (in custom expr at level 2) : expr_scope.
Notation "'(' 256 'ui' ')' e" := (Papp1 (Owi1 Unsigned (WIwint_of_int U256)) e) (in custom expr at level 2) : expr_scope.

Notation "'(' 8 'si' ')' e"   := (Papp1 (Owi1 Signed (WIwint_of_int U8)) e)   (in custom expr at level 2) : expr_scope.
Notation "'(' 16 'si' ')' e"  := (Papp1 (Owi1 Signed (WIwint_of_int U16)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(' 32 'si' ')' e"  := (Papp1 (Owi1 Signed (WIwint_of_int U32)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(' 64 'si' ')' e"  := (Papp1 (Owi1 Signed (WIwint_of_int U64)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(' 128 'si' ')' e" := (Papp1 (Owi1 Signed (WIwint_of_int U128)) e) (in custom expr at level 2) : expr_scope.
Notation "'(' 256 'si' ')' e" := (Papp1 (Owi1 Signed (WIwint_of_int U256)) e) (in custom expr at level 2) : expr_scope.

(* WIint_of_wint: wint → int. Syntax: (uint) or (sint) — same as Oint_of_word *)
(* Already handled by (uint) and (sint) above for Oint_of_word. *)
(* For Owi1 variant, these would need distinct keywords but don't appear in examples. *)

(* WIword_of_wint: wint → word. Syntax: (wi2w Nu) *)
Notation "'(wi2w' 8 'u' ')' e"   := (Papp1 (Owi1 Unsigned (WIword_of_wint U8)) e)   (in custom expr at level 2) : expr_scope.
Notation "'(wi2w' 16 'u' ')' e"  := (Papp1 (Owi1 Unsigned (WIword_of_wint U16)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(wi2w' 32 'u' ')' e"  := (Papp1 (Owi1 Unsigned (WIword_of_wint U32)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(wi2w' 64 'u' ')' e"  := (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) e)  (in custom expr at level 2) : expr_scope.
Notation "'(wi2w' 128 'u' ')' e" := (Papp1 (Owi1 Unsigned (WIword_of_wint U128)) e) (in custom expr at level 2) : expr_scope.
Notation "'(wi2w' 256 'u' ')' e" := (Papp1 (Owi1 Unsigned (WIword_of_wint U256)) e) (in custom expr at level 2) : expr_scope.

(* WIwint_of_word: word → wint. Syntax: (w2wi Nui) or (w2wi Nsi) *)
Notation "'(w2wi' 64 'ui' ')' e" := (Papp1 (Owi1 Unsigned (WIwint_of_word U64)) e) (in custom expr at level 2) : expr_scope.
Notation "'(w2wi' 64 'si' ')' e" := (Papp1 (Owi1 Signed (WIwint_of_word U64)) e)   (in custom expr at level 2) : expr_scope.

(* WIwint_ext: wint → wint (resize). Syntax: (wiext Nui) or (wiext Nsi) *)
Notation "'(wiext' 64 'ui' ')' e" := (Papp1 (Owi1 Unsigned (WIwint_ext U64 U64)) e) (in custom expr at level 2) : expr_scope.
Notation "'(wiext' 64 'si' ')' e" := (Papp1 (Owi1 Signed (WIwint_ext U64 U64)) e)   (in custom expr at level 2) : expr_scope.

(* ========================================================================= *)
(* Memory load: [:uN e]                                                      *)
(* ========================================================================= *)

(* Memory loads: [:uN e] is Unaligned (default), [#aligned :uN e] is Aligned *)
Notation "'[:u8' e ']'" := (Pload Unaligned U8 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u16' e ']'" := (Pload Unaligned U16 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u32' e ']'" := (Pload Unaligned U32 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u64' e ']'" := (Pload Unaligned U64 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u128' e ']'" := (Pload Unaligned U128 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[:u256' e ']'" := (Pload Unaligned U256 e) (in custom expr at level 0, e custom expr) : expr_scope.

(* Aligned memory loads: [#aligned :uN e] *)
Notation "'[#aligned' '[:u8' e ']'" := (Pload Aligned U8 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[#aligned' '[:u16' e ']'" := (Pload Aligned U16 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[#aligned' '[:u32' e ']'" := (Pload Aligned U32 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[#aligned' '[:u64' e ']'" := (Pload Aligned U64 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[#aligned' '[:u128' e ']'" := (Pload Aligned U128 e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "'[#aligned' '[:u256' e ']'" := (Pload Aligned U256 e) (in custom expr at level 0, e custom expr) : expr_scope.

(* ========================================================================= *)
(* Array access: x[:uN e]                                                    *)
(* Maps to Pget Aligned AAscale UN (mkvar x) e                               *)
(* ========================================================================= *)

Notation "x '[:u8' e ']'"   := (Pget Aligned AAscale U8 (mkgvar x) e)   (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u16' e ']'"  := (Pget Aligned AAscale U16 (mkgvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u32' e ']'"  := (Pget Aligned AAscale U32 (mkgvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u64' e ']'"  := (Pget Aligned AAscale U64 (mkgvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u128' e ']'" := (Pget Aligned AAscale U128 (mkgvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.
Notation "x '[:u256' e ']'" := (Pget Aligned AAscale U256 (mkgvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr) : expr_scope.

(* ========================================================================= *)
(* Array slice: x[:uN e : len]                                                *)
(* Maps to Psub AAscale UN len (mkvar x) e                                    *)
(* ========================================================================= *)

Notation "x '[:u8' e ':' n ']'"   := (Psub AAscale U8 n (mkgvar x) e)   (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u16' e ':' n ']'"  := (Psub AAscale U16 n (mkgvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u32' e ':' n ']'"  := (Psub AAscale U32 n (mkgvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u64' e ':' n ']'"  := (Psub AAscale U64 n (mkgvar x) e)  (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u128' e ':' n ']'" := (Psub AAscale U128 n (mkgvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.
Notation "x '[:u256' e ':' n ']'" := (Psub AAscale U256 n (mkgvar x) e) (in custom expr at level 0, x constr at level 0, e custom expr, n constr at level 0) : expr_scope.

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

(* Variables: handled by mkgvar (string -> gvar) notation.
   Variable types are NOT tracked in the notation — they come from the
   function signature (tyin/tyout) and assignment type comments (/* u64 */).
   A typed variable axiom mkvar : string -> var is assumed. *)

(* Alignment conventions:
   - Memory loads/stores: [:uN e] = Unaligned (default), [#aligned :uN e] = Aligned
   - Array accesses: x[:uN e] = Aligned (default for arrays)
   - Unaligned array access (x[#unaligned :uN e]) is not yet needed/supported *)

(* Array accesses: "x"[:uN e] -> Pget, defined above *)
(* Array slices: "x"[:uN e : n] -> Psub, defined above *)

(* Array initializers: handled as ArrayInit("x") instruction in InstructionNotations *)

(* N-ary operators: pack expressions (4u2)[...] are partially handled above;
   larger packs (16u8) and other PappN use rocq:(...) escape in compiler output.
   Combine flags (_EQ, _uLT, etc.) are handled as expression notations. *)

End ExpressionNotations.

(* Lvals: Lvar (mklvar x), Lnone dummy_var_info ty, Laset, Lmem, Lasub
   are handled within coq_copn and call notations as raw Coq terms.
   Direct lval notations for assignments use Lvar (simple variable) and
   Laset/Lmem for array/memory store instructions. *)

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

Notation mklvar := (fun x => mk_var_i (mkvar x)) (only parsing).

(* Placeholder for intrinsic name resolution. Returns Onop; to be replaced
   with proper architecture-specific resolution when needed. *)
Definition mkopn {asm_op : Type} {asmop : asmOp asm_op}
  (s : string) : @sopn asm_op asmop :=
  sopn_nop.

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
Declare Custom Entry jcmd. (* Why not cmd? *)
Declare Custom Entry fundecl.
Declare Custom Entry prog.

Module InstructionNotations.

Export ExpressionNotations.
Open Scope expr_scope.

Notation mklvar := (fun x => mk_var_i (mkvar x)) (only parsing).

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
  ([:: i ])
  (in custom jcmd at level 2,
   i custom instr at level 10)
  : expr_scope.

Notation "i c" :=
  (i :: c)
  (in custom jcmd at level 2,
   i custom instr at level 10,
   c custom jcmd at level 2)
  : expr_scope.

(* Do we really need the keyword CALL? *)
(* Old fixed-arity call notations removed; the generic 'call' notation       *)
(* (defined below) handles ALL function call patterns.                        *)

(* Function calls with more arguments: handled by call notation below,
   which accepts raw Coq lists for lvals and args. *)

(* --- Memory store: [:u64 e1] = e2 ; /* u64 */ --- *)

Notation "'[:u8' e1 ']' = e2 ; '/*' 'u8' '*/'" :=
  (mkI' (Cassgn (Lmem Unaligned U8 dummy_var_info e1) AT_none (aword U8) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u16' e1 ']' = e2 ; '/*' 'u16' '*/'" :=
  (mkI' (Cassgn (Lmem Unaligned U16 dummy_var_info e1) AT_none (aword U16) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u32' e1 ']' = e2 ; '/*' 'u32' '*/'" :=
  (mkI' (Cassgn (Lmem Unaligned U32 dummy_var_info e1) AT_none (aword U32) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u64' e1 ']' = e2 ; '/*' 'u64' '*/'" :=
  (mkI' (Cassgn (Lmem Unaligned U64 dummy_var_info e1) AT_none (aword U64) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u128' e1 ']' = e2 ; '/*' 'u128' '*/'" :=
  (mkI' (Cassgn (Lmem Unaligned U128 dummy_var_info e1) AT_none (aword U128) e2))
  (in custom instr at level 10, e1 custom expr, e2 custom expr) : expr_scope.
Notation "'[:u256' e1 ']' = e2 ; '/*' 'u256' '*/'" :=
  (mkI' (Cassgn (Lmem Unaligned U256 dummy_var_info e1) AT_none (aword U256) e2))
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

(* --- Function calls (Ccall): call [lvals] (mkfunname "name") [args] ; --- *)
(* Generic notation that handles ALL function call patterns.                  *)

Notation "'call' lvs fname args ;" :=
  (mkI' (Ccall lvs fname args))
  (in custom instr at level 10,
   lvs constr at level 0, fname constr at level 0, args constr at level 0)
  : expr_scope.

(* --- Array initialization: ArrayInit("x"); /* arr_init */ --- *)

Notation "'ArrayInit' ( x ) ; '/*' 'arr_init' '*/'" :=
  (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aarr U8 1%positive) (Parr_init U8 1%positive)))
  (in custom instr at level 10, x constr at level 0) : expr_scope.

(* --- Assignment instructions: "x" = e ; /* uN */ --- *)

Notation "x = e ; /* 'u8' */"    := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U8) e))    (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u16' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U16) e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u32' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U32) e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u64' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U64) e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u128' */"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U128) e))  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'u256' */"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none (aword U256) e))  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.

Notation "x = e ; /* 'bool' */"  := (mkI' (Cassgn (Lvar (mklvar x)) AT_none abool e))  (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.
Notation "x = e ; /* 'int' */"   := (mkI' (Cassgn (Lvar (mklvar x)) AT_none aint e))   (in custom instr at level 10, x constr at level 0, e custom expr at level 13) : expr_scope.

(* Wrong: the return statement should be part of the fundef notation, as it determines the return variables. *)

(* Return statements are no longer printed as instructions in coq mode.      *)
(* The return variables are part of the FN ... WITH notation (the res list). *)

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

(* Generic function declaration: FN name WITH tyin params tyout res { body } *)
(* This is the ONLY function notation — it handles all signatures via explicit
   Coq lists for types, parameters, return types, and return variables. *)
(* The compiler outputs this format with -coq flag. *)

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

(* Tests                                                                     *)
(* ========================================================================= *)

Import ExpressionNotations.
Open Scope expr_scope.
Unset Printing Notations.

(* ---- Expression tests ---- *)
Section ExprTests.
Check expr:( true || false && (#1 -i #10) ==i false ).
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
Check expr:( (cast 64u) #3 ).
Check expr:( "x" ^64u "y" ).
Check expr:( "x" |64u "y" ).
Check expr:( "x" <64s "y" ).
Check expr:( "x" /64u "y" ).
Check expr:( "x" /64s "y" ).
Check expr:( "x" %64u "y" ).
Check expr:( "x" >>64s "y" ).
Check expr:( !64u "x" ).
Check expr:( -64u "x" ).
End ExprTests.

(* ---- instruction and program tests ---- *)
Section ProgTests.
Context {asm_op : Type} {asmop : asmOp asm_op}.
Import InstructionNotations.
Open Scope expr_scope.

(* This doesn't work but the notation is in l624 *)

(* Single command: assignment *)
Check cmd:(
  "r" = ("x" +64u "y") ; /* u64 */
).

(* Multiple instructions *)
Check cmd:(
  "r" = ("x" +64u "y") ; /* u64 */
  "r" = ("r" -64u #1) ; /* u64 */
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

(* Full program using FN WITH format *)
Check prog:(
  FN "add" WITH
  [:: (aword U64); (aword U64)]
  [:: mklvar "x"; mklvar "y"]
  [:: (aword U64)]
  [:: mklvar "r"]
  {
    "r" = ("x" +64u "y") ; /* u64 */
  }
).

(* Program with two functions *)
Check prog:(
  FN "add" WITH
  [:: (aword U64); (aword U64)]
  [:: mklvar "x"; mklvar "y"]
  [:: (aword U64)]
  [:: mklvar "r"]
  {
    "r" = ("x" +64u "y") ; /* u64 */
  }
  FN "sub" WITH
  [:: (aword U64); (aword U64)]
  [:: mklvar "x"; mklvar "y"]
  [:: (aword U64)]
  [:: mklvar "r"]
  {
    "r" = ("x" -64u "y") ; /* u64 */
  }
).

(* No-arg, no-return function *)
Check prog:(
  FN "nop" WITH [::] [::] [::] [::] {
    "x" = (cast 64u) #0 ; /* u64 */
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

(* opsizes.jazz tests *)


(* ifelse.jazz test *)

(* aes.jazz: AddRoundKey function *)

(* aes.jazz: inline int function *)

(* aes.jazz: cipher function with array param *)

(* aes.jazz: key_combine with 2 returns *)

(* shift.jazz: memory store with u16 *)
Check cmd:(
  [:u16 "p" +64u (cast 64u) #0] = "a" ; /* u16 */
).

(* loops.jazz: for_nest function *)

(* aes.jazz: key_expand with inline int + u128 params *)

(* aes.jazz: keys_expand with u128 return and array set *)

(* aes.jazz: aes_enc with 3 u64 params, no return *)

(* test_add.jazz: test3 with function call returning 0 results *)

(* opsizes.jazz: primop_test with intrinsics *)

(* opsizes.jazz: test_immediate with u256 ops *)

(* test_casts.jazz *)

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
  }
).

End ProgTests.

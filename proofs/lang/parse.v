From mathcomp Require Import ssreflect ssrfun.

Require Import expr.

Axiom (mkvar : string -> gvar).
Axiom (mkvar_inj : injective mkvar).
Axiom (mkfunname : string -> funname).
Axiom (mkfunname_inj : injective mkfunname).

(* ========================================================================= *)
(* Notation system for Jasmin expressions.                                   *)
(*                                                                           *)
(* Word sizes are specified using bracket syntax: +[U64], *[U32], etc.       *)
(* Integer operators use an 'i' suffix: +i, -i, *i, ==i, etc.               *)
(* Boolean operators use standard symbols: &&, ||, !                         *)
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

(* Variables: any Coq identifier in scope is lifted via coercion.
   If x : gvar, it becomes Pvar x. If x : pexpr, used directly. *)
Notation "x" := (mkvar x)
  (in custom expr at level 0)
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

(* Word negation: -[ws] e *)
(* TODO: try to remove brackets, as Jasmin does not print it *)
Notation "'-[' ws ']' e" :=
  (Papp1 (Oneg (Op_w ws)) e)
  (in custom expr at level 2, ws constr at level 0)
  : expr_scope.

(* Bitwise NOT: ~[ws] e *)
Notation "'~[' ws ']' e" :=
  (Papp1 (Olnot ws) e)
  (in custom expr at level 2, ws constr at level 0)
  : expr_scope.

(* Word-of-int cast: (cast ws) e *)
Notation "'(cast' ws ')' e" :=
  (Papp1 (Oword_of_int ws) e)
  (in custom expr at level 2, ws constr at level 0)
  : expr_scope.

(* ========================================================================= *)
(* Multiplicative operators (level 3, left associativity).                   *)
(* ========================================================================= *)

(* Integer multiplication: e1 *i e2 *)
Notation "e1 '*i' e2" :=
  (Papp2 (Omul Op_int) e1 e2)
  (in custom expr at level 3, left associativity)
  : expr_scope.

(* Word multiplication: e1 *[ws] e2 *)
Notation "e1 '*[' ws ']' e2" :=
  (Papp2 (Omul (Op_w ws)) e1 e2)
  (in custom expr at level 3, ws constr at level 0, left associativity)
  : expr_scope.

(* Unsigned word division: e1 /[ws] e2 *)
Notation "e1 '/[' ws ']' e2" :=
  (Papp2 (Odiv Unsigned (Op_w ws)) e1 e2)
  (in custom expr at level 3, ws constr at level 0, left associativity)
  : expr_scope.

(* Signed word division: e1 /s[ws] e2 *)
Notation "e1 '/s[' ws ']' e2" :=
  (Papp2 (Odiv Signed (Op_w ws)) e1 e2)
  (in custom expr at level 3, ws constr at level 0, left associativity)
  : expr_scope.

(* Unsigned word modulo: e1 %[ws] e2 *)
Notation "e1 '%[' ws ']' e2" :=
  (Papp2 (Omod Unsigned (Op_w ws)) e1 e2)
  (in custom expr at level 3, ws constr at level 0, left associativity)
  : expr_scope.

(* Signed word modulo: e1 %s[ws] e2 *)
Notation "e1 '%s[' ws ']' e2" :=
  (Papp2 (Omod Signed (Op_w ws)) e1 e2)
  (in custom expr at level 3, ws constr at level 0, left associativity)
  : expr_scope.

(* ========================================================================= *)
(* Additive operators (level 4, left associativity).                         *)
(* ========================================================================= *)

(* Integer addition: e1 +i e2 *)
Notation "e1 '+i' e2" :=
  (Papp2 (Oadd Op_int) e1 e2)
  (in custom expr at level 4, left associativity)
  : expr_scope.

(* Word addition: e1 +[ws] e2 *)
Notation "e1 '+[' ws ']' e2" :=
  (Papp2 (Oadd (Op_w ws)) e1 e2)
  (in custom expr at level 4, ws constr at level 0, left associativity)
  : expr_scope.

(* Integer subtraction: e1 -i e2 *)
Notation "e1 '-i' e2" :=
  (Papp2 (Osub Op_int) e1 e2)
  (in custom expr at level 4, left associativity)
  : expr_scope.

(* Word subtraction: e1 -[ws] e2 *)
Notation "e1 '-[' ws ']' e2" :=
  (Papp2 (Osub (Op_w ws)) e1 e2)
  (in custom expr at level 4, ws constr at level 0, left associativity)
  : expr_scope.

(* ========================================================================= *)
(* Shift and rotation operators (level 5, left associativity).               *)
(* ========================================================================= *)

(* Left shift: e1 <<[ws] e2 *)
Notation "e1 '<<[' ws ']' e2" :=
  (Papp2 (Olsl (Op_w ws)) e1 e2)
  (in custom expr at level 5, ws constr at level 0, left associativity)
  : expr_scope.

(* Logical right shift: e1 >>[ws] e2 *)
Notation "e1 '>>[' ws ']' e2" :=
  (Papp2 (Olsr ws) e1 e2)
  (in custom expr at level 5, ws constr at level 0, left associativity)
  : expr_scope.

(* Arithmetic right shift: e1 >>s[ws] e2 *)
Notation "e1 '>>s[' ws ']' e2" :=
  (Papp2 (Oasr (Op_w ws)) e1 e2)
  (in custom expr at level 5, ws constr at level 0, left associativity)
  : expr_scope.

(* Rotate left: e1 <<r[ws] e2 *)
Notation "e1 '<<r[' ws ']' e2" :=
  (Papp2 (Orol ws) e1 e2)
  (in custom expr at level 5, ws constr at level 0, left associativity)
  : expr_scope.

(* Rotate right: e1 >>r[ws] e2 *)
Notation "e1 '>>r[' ws ']' e2" :=
  (Papp2 (Oror ws) e1 e2)
  (in custom expr at level 5, ws constr at level 0, left associativity)
  : expr_scope.

(* ========================================================================= *)
(* Bitwise operators.                                                        *)
(* ========================================================================= *)

(* Bitwise AND (level 6): e1 &[ws] e2 *)
Notation "e1 '&[' ws ']' e2" :=
  (Papp2 (Oland ws) e1 e2)
  (in custom expr at level 6, ws constr at level 0, left associativity)
  : expr_scope.

(* Bitwise XOR (level 7): e1 ^[ws] e2 *)
Notation "e1 '^[' ws ']' e2" :=
  (Papp2 (Olxor ws) e1 e2)
  (in custom expr at level 7, ws constr at level 0, left associativity)
  : expr_scope.

(* Bitwise OR (level 8): e1 |[ws] e2 *)
Notation "e1 '|[' ws ']' e2" :=
  (Papp2 (Olor ws) e1 e2)
  (in custom expr at level 8, ws constr at level 0, left associativity)
  : expr_scope.

(* ========================================================================= *)
(* Comparison operators (level 9, no associativity).                         *)
(* ========================================================================= *)

(* Integer comparisons. *)

Notation "e1 '<i' e2" :=
  (Papp2 (Olt Cmp_int) e1 e2)
  (in custom expr at level 9, no associativity)
  : expr_scope.

Notation "e1 '<=i' e2" :=
  (Papp2 (Ole Cmp_int) e1 e2)
  (in custom expr at level 9, no associativity)
  : expr_scope.

Notation "e1 '>i' e2" :=
  (Papp2 (Ogt Cmp_int) e1 e2)
  (in custom expr at level 9, no associativity)
  : expr_scope.

Notation "e1 '>=i' e2" :=
  (Papp2 (Oge Cmp_int) e1 e2)
  (in custom expr at level 9, no associativity)
  : expr_scope.

(* Unsigned word comparisons. *)

Notation "e1 '<[' ws ']' e2" :=
  (Papp2 (Olt (Cmp_w Unsigned ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '<=[' ws ']' e2" :=
  (Papp2 (Ole (Cmp_w Unsigned ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '>[' ws ']' e2" :=
  (Papp2 (Ogt (Cmp_w Unsigned ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '>=[' ws ']' e2" :=
  (Papp2 (Oge (Cmp_w Unsigned ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

(* Signed word comparisons. *)

Notation "e1 '<s[' ws ']' e2" :=
  (Papp2 (Olt (Cmp_w Signed ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '<=s[' ws ']' e2" :=
  (Papp2 (Ole (Cmp_w Signed ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '>s[' ws ']' e2" :=
  (Papp2 (Ogt (Cmp_w Signed ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '>=s[' ws ']' e2" :=
  (Papp2 (Oge (Cmp_w Signed ws)) e1 e2)
  (in custom expr at level 9, ws constr at level 0, no associativity)
  : expr_scope.

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

(* Word equality. *)
Notation "e1 '==[' ws ']' e2" :=
  (Papp2 (Oeq (Op_w ws)) e1 e2)
  (in custom expr at level 10, ws constr at level 0, no associativity)
  : expr_scope.

Notation "e1 '!=[' ws ']' e2" :=
  (Papp2 (Oneq (Op_w ws)) e1 e2)
  (in custom expr at level 10, ws constr at level 0, no associativity)
  : expr_scope.

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
(* Pif requires an atype annotation: use ? [ty] e2 : e3                     *)
(* ========================================================================= *)

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
Context (x y z b : gvar).

(* --- Jasmin: x +64u y --- *)
(* TODO: U64 -> 64u, no brackets *)
Check expr:( "x" +[U64] "y" ).
(* Papp2 (Oadd (Op_w U64)) x y *)

(* --- Jasmin: z *64u x +64u 3 --- *)
Check expr:( z *[U64] x +[U64] #3 ).
(* Papp2 (Oadd (Op_w U64)) (Papp2 (Omul (Op_w U64)) z x) (Pconst 3) *)

(* --- Jasmin: true ? x &32u y : z --- *)
Check expr:( true ?[aword U32] x &[U32] y : z ).
(* Pif (aword U32) (Pbool true) (Papp2 (Oland U32) x y) z *)

(* --- Jasmin: y <<r64u z (rotate left) --- *)
Check expr:( y <<r[U64] z ).
(* Papp2 (Orol U64) y z *)

(* --- Jasmin: y <<64u y --- *)
Check expr:( y <<[U64] y ).
(* Papp2 (Olsl (Op_w U64)) y y *)

(* --- Jasmin: y >>64u y --- *)
Check expr:( y >>[U64] y ).
(* Papp2 (Olsr U64) y y *)

(* --- Jasmin: x ==64u y --- *)
Check expr:( x ==[U64] y ).
(* Papp2 (Oeq (Op_w U64)) x y *)

(* --- Jasmin: b && x <=u y --- *)
Check expr:( b && x <=[U64] y ).
(* Papp2 Oand b (Papp2 (Ole (Cmp_w Unsigned U64)) x y) *)

(* --- Jasmin: x !=64u y || x <u y --- *)
Check expr:( x !=[U64] y || x <[U64] y ).
(* Papp2 Oor (Papp2 (Oneq (Op_w U64)) x y) (Papp2 (Olt (Cmp_w Unsigned U64)) x y) *)

(* --- Integer arithmetic --- *)
Check expr:( #5 -i #2 ).
(* Papp2 (Osub Op_int) 5 2 *)

(* --- Mixed boolean/integer --- *)
Check expr:( true || false && (#1 -i #10) ==i false ).
(* Papp2 Oor true (Papp2 Oand false (Papp2 (Oeq Op_int) (Papp2 (Osub Op_int) 1 10) false)) *)

(* --- Word-of-int cast --- *)
Check expr:( (cast U64) #3 ).
(* Papp1 (Oword_of_int U64) (Pconst 3) *)

(* --- Bitwise operations --- *)
Check expr:( x ^[U64] y ).
Check expr:( x |[U64] y ).

(* --- Signed comparison --- *)
Check expr:( x <s[U64] y ).

(* --- Division and modulo --- *)
Check expr:( x /[U64] y ).
Check expr:( x /s[U64] y ).
Check expr:( x %[U64] y ).

End Tests.

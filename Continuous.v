Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import QArith.Qpower.
Require Import QArith.Qround.
Require Import ZArith.Znat.
Require Import Psatz.
Require Import Init.Nat.
Require Import Omega.

Definition Continuous (f:Q->Q) := forall x0 e,
e>0 -> {d | 0<d /\ forall x, Qabs (x-x0) < d -> Qabs ( (f x) - (f x0) ) < e}.

Lemma Qabs_extensional : forall q1 q2, q1==q2 -> Qabs q1 == Qabs q2.
Proof.
intros.
destruct q1. destruct q2.
unfold Qabs. unfold Z.abs.
destruct Qnum, Qnum0.
* lra.
* auto.
* assert( not (0 # Qden == Z.neg p # Qden0) ).
** unfold Qeq. assert( (Qnum (0 # Qden) = 0)%Z ) by auto with *.
   rewrite H. auto with *.
** contradiction.
* auto.
* auto. 
* assert( not (Zpos p # Qden == Z.neg p0 # Qden0) ).
** unfold Qeq. auto with *.
** contradiction.
* assert( not (Z.neg p # Qden == 0 # Qden0) ).
** unfold Qeq. auto with *.
** contradiction.
* assert( not ( Z.neg p # Qden == ' p0 # Qden0) ).
** unfold Qeq. auto with *.
** contradiction.
* unfold Qeq. unfold Qeq in H. simpl. simpl in H.
  assert ( (p*Qden0 = p0*Qden)%positive ).
** nia.
** rewrite H0. auto with *.
Qed.


(*Constant function zero.*)
Definition const (x:Q) := 0.
(*Simple linear function.*)
Definition linear (x:Q) := x.
(*Function with "discontinuity" at zero*)
Definition bad (x:Q) := if (Qlt_le_dec 0 x) then 1 else 0.



Theorem const_is_continuous : Continuous const.
Proof.
unfold Continuous.
intros.
exists 1.
intros.
unfold const.
split.
* lra.
* intros. simpl. lra.
Qed.

Theorem linear_is_continuous : Continuous linear.
Proof.
unfold Continuous.
intros.
exists e.
split.
* lra.
* intros. unfold linear. apply H0.
Qed.

(* The function "bad" is not continuous *)
Theorem bad_is_discontinuous : (Continuous bad) -> False.
Proof.
unfold Continuous.
intros.
assert( 0<1#2) by lra.
assert( H1 := H 0 (1#2) H0).
destruct H1.
destruct a.
assert( Hbad := (H2 (x*(1#2)))).
assert( Qabs (x * (1 # 2) - 0) < x ).
{
  assert( Qabs(x * (1#2) - 0) == Qabs (x *(1#2)) ).
  {
    apply Qabs_extensional. lra.
  }
  rewrite H3.
  assert( Qabs( x*(1#2) ) == x*(1#2) ).
  {
    apply Qabs_pos. lra.
  }
  rewrite H4. lra.
}
assert( Hbadbad := Hbad H3 ).
assert(Qabs (bad (x * (1 # 2)) - bad 0) == Qabs 1 ).
{
  unfold bad.
  destruct (Qlt_le_dec 0 (x*(1#2))).
  * destruct (Qlt_le_dec 0 0).
    ** simpl. assert(not (0<0)) by lra. contradiction.
    ** simpl. lra. 
  * destruct (Qlt_le_dec 0 0).
    ** simpl. assert(not (0<0)) by lra. contradiction.
    ** simpl. assert(not ((x * (1#2))<=0) ). lra. contradiction.
}

rewrite H4 in Hbadbad.
assert(not (Qabs 1 < 1#2)).
{
  assert( Qabs 1 == 1 ).
  {
    apply Qabs_pos. lra.
  }
  rewrite H5. lra.

}
contradiction.
Qed.

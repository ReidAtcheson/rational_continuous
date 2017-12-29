Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import QArith.Qpower.
Require Import QArith.Qround.
Require Import ZArith.Znat.
Require Import Psatz.
Require Import Init.Nat.
Require Import ZArith.BinInt.
Require Import ZArith.Zpow_facts.
Require Import PArith.Pnat.
Require Import Omega.

Definition Continuous (f:Q->Q) := forall x0 e,
e>0 -> {d | 0<d /\ forall x, Qabs (x-x0) < d -> Qabs ( (f x) - (f x0) ) < e}.
Definition UniformlyContinuous (f:Q->Q) := forall e, 
e>0 -> {d | 0<d /\ forall x x0, Qabs (x - x0) < d -> Qabs ( (f x) - (f x0) ) < e}.

Definition Difference (f:Q->Q) (x:Q) (h:Q) := (f (x+h) - f x)/h.
Definition Differentiable (f:Q->Q) (x : Q) := forall e, e>0 -> {h | h>0 /\ Qabs(f (x+h) - (f x) - h*(Difference f x h) ) < e}.

Theorem uniformly_continuous_is_continuous : forall (f:Q->Q), UniformlyContinuous f -> Continuous f.
Proof.
intros.
unfold UniformlyContinuous in H. unfold Continuous.
intros.
assert(H1 := (H e H0)).
destruct H1.
destruct a.
exists x.
split.
* lra.
* intros. auto with *.
Qed.

Lemma useful_order_property : forall e r:Q, e>0 -> {r>-e} + {r<=e}.
Proof.
intros.
destruct (Qlt_le_dec 0 r).
* assert( -e < r) by lra. auto.
* assert( r<= e ) by lra. auto.
Defined.

Lemma Qpower_reduction : forall a (n:Z), (n>0)%Z -> a>0 -> a^n == a*(a^(n-1)).
Proof.
intros.
assert(R1: a== a^1) by lra.
remember (a^n) as an. remember ( a^(n-1)) as anm1.
rewrite R1; clear R1.
rewrite Heqan. rewrite Heqanm1.
remember ((n-1)%Z) as nm1.
assert(R: (n = 1 + (n-1))%Z) by auto with *.
rewrite R; clear R.
rewrite Heqnm1.
apply Qpower_plus.
lra.
Qed.


Lemma powertwo_bigger_than_exp_pos : forall (n:nat), (2^Z.of_nat (n+1) > Z.of_nat (n+1))%Z.
Proof.
intros.
induction n.
* simpl. unfold Z.pow_pos. simpl. auto with *.
* remember (Z.of_nat (n+1)) as m.
  assert( (Z.of_nat(S n + 1 ) = m+1)%Z ) by nia.
  rewrite H.
  assert( (m > 0)%Z ) by nia.
  assert( (2^m + 2^m > m + 2^m)%Z ) by nia.
  assert( (m + 2^m > m+m)%Z ) by nia.
  assert( (2^m + 2^m > m+m)%Z ) by nia.
  assert( ((2^m + 2^m) = 2^(m+1))%Z ). {
    assert( ((2^m + 2^m) = 2*2^m)%Z ) by nia.
    rewrite H4.
    assert( ( 2^(m+1) = 2*2^m )%Z ). apply Z.pow_succ_r. auto with *.
    rewrite H5.
    auto.
  }
  rewrite H4 in H3.
  assert( (m+m>=m+1)%Z ) by nia.
  nia.
Qed.



Lemma powertwo_bigger_than_exp : forall (n:nat), (2^(Z.of_nat n) > Z.of_nat n)%Z.
Proof.
intros.
destruct n.
* simpl. auto with *.
* assert( ( S n = n+1)%nat) by auto with *. rewrite H.
  apply powertwo_bigger_than_exp_pos.
Qed.

Lemma powertwo_bigger_than_exp_positive : forall (p:positive), (2^(Zpos p) > Zpos p)%Z.
Proof.
intros.
remember (Pos.to_nat p) as m.
assert( (m>0)%nat ). {
  rewrite Heqm.
  apply Pos2Nat.is_pos.
}
assert( Z.pos p = Z.of_nat m ). {
  rewrite Heqm.
  assert( Z.of_nat (Pos.to_nat p) = Z.pos p) by apply positive_nat_Z.
  rewrite H0. auto.
}
rewrite H0.
apply (powertwo_bigger_than_exp).
Qed.


Lemma powertwo_bigger_than_exp_positive2 : forall (p:positive), (2^p > p)%positive.
Proof.
Admitted.



Theorem smaller_rational_works : forall r, r>0 -> (1#2)^(Zpos (Qden r)) < r.
Proof.
Admitted.
(*
intros.
destruct r.
simpl.
assert( Qpower_positive (1#2) Qden = 1^(Zpos Qden) # 2^Qden ). {
  apply Qpower_decomp.
}
rewrite H0.
assert( (1 ^ Z.pos Qden = 1)%Z ) by apply Zpower_pos_1_l.
rewrite H1.
unfold Qlt. simpl.
assert( (Z.pos (2^Qden) = ( 2^ (Z.pos Qden)))%Z ). {
  destruct Qden.
  * simpl.
}

assert( (Z.pos Qden < Z.pos (2^Qden))%Z ). {
  remember ( (Z.to_nat (Z.pos Qden))) as m.
  assert( Z.pos (2^Qden
  assert( ( 2 ^ (Z.of_nat m) > Z.of_nat m)%Z ). {
    apply powertwo_bigger_than_exp.
  }
}
*)



Lemma qnum_powerhalf_is_1 : forall (n:nat), (Qnum ((1#2) ^ (Z.of_nat n)) = 1)%Z.
Proof.
intros.
unfold Qpower.
destruct n. 
* simpl. auto.
* simpl.
  remember (Pos.of_succ_nat n) as m.
  assert(
    (Qpower_positive (1 # 2)
     m = (1^(Zpos m)) # (2^m))). {
      apply Qpower_decomp.
     }
  rewrite H. simpl. 
  apply Zpower_pos_1_l.
Qed.

Fixpoint bisect_a (f:Q->Q) (a:Q) (b:Q) (e:Q) (He:(e>0)) (m:nat) := match m with
  0%nat => a
|   S p =>
  let mid := (1#2)*(a+b) in
  if (useful_order_property e (f mid) He)
    then (bisect_a f a mid e He p)
    else (bisect_a f mid b e He p)
end.


Fixpoint bisect_b (f:Q->Q) (a:Q) (b:Q) (e:Q) (He:(e>0)) (m:nat) := match m with
  0%nat => b
|   S p =>
  let mid := (1#2)*(a+b) in
  if (useful_order_property e (f mid) He)
    then (bisect_b f a mid e He p)
    else (bisect_b f mid b e He p)
end.


Fixpoint bisect_c (f:Q->Q) (a:Q) (b:Q) (e:Q) (He:(e>0)) (m:nat) := match m with
  0%nat => (1#2)*(a+b)
|   S p =>
  let mid := (1#2)*(a+b) in
  if (useful_order_property e (f mid) He)
    then (bisect_c f a mid e He p)
    else (bisect_c f mid b e He p)
end.


Definition err := 1#100.
Theorem a_pos_err : err>0.
Proof.
unfold err. lra.
Qed.





Definition sqrt_err (x:Q) := x*x-(2#1).

Eval vm_compute in (bisect_c sqrt_err 1 (2#1) err a_pos_err 10).


Lemma exponential_bound : forall (e:Q), e>0 -> {n:Z | (1#2)^n < e}.
Proof.
Admitted.

Lemma bisect_a_works : forall (f:Q->Q) (e:Q) (H:e>0) (n:nat), (f 0) < 0 -> (f 1) > 0 -> 
f (bisect_a f 0 1 e H n) < e.
Proof.
Admitted.

Lemma bisect_b_works : forall (f:Q->Q) (e:Q) (H:e>0) (n:nat), (f 0) < 0 -> (f 1) > 0 -> 
f (bisect_b f 0 1 e H n) > -e.
Proof.
Admitted.

Lemma bisect_c_works : forall (f:Q->Q) (e:Q) (H:e>0) (n:nat), (f 0) < 0 -> (f 1) > 0 -> 
(bisect_c f 0 1 e H n) - (bisect_a f 0 1 e H n) <= (1#2)^(Z.of_nat n) /\
(bisect_b f 0 1 e H n) - (bisect_c f 0 1 e H n) <= (1#2)^(Z.of_nat n).
Proof.
Admitted.

Lemma bisect_c_bounds : forall (f:Q->Q) (e:Q) (H:e>0) (n:nat),
0<bisect_c f 0 1 e H n /\ bisect_c f 0 1 e H n<1.
Proof.
Admitted.

Lemma Qabs_bounds : forall (q:Q) (e:Q), e>0 -> -e<q -> q<e -> Qabs q < e.
Proof.
Admitted.


Theorem intermediate_value_theorem : forall (f:Q->Q) (e:Q), UniformlyContinuous f -> e>0 -> (f 0) < 0 -> (f 1) > 0 ->
{ c | 0<c /\ c<1 /\ Qabs (f c) < e }.
Proof.
intros.

(*First use uniform continuity
  to get a delta to satisfy error*)
unfold UniformlyContinuous in H.
assert( (1#2)*e > 0) by lra.
assert( P0 := (H ((1#2)*e) H3)).
destruct P0.
remember x as delta.
destruct a.
(*Now we have delta, need corresponding 
  natural number n to give bisection
  algorithm*)
assert( P1 := exponential_bound delta H4 ).
destruct P1.
remember x0 as n.
(*Use bisection to compute a,b,c such that
  f a<e/2, f b>-e/2, c-a<delta, b-c<delta *)
remember (bisect_a f 0 1 ((1#2)*e) H3 (Z.to_nat n)) as a.
remember (bisect_b f 0 1 ((1#2)*e) H3 (Z.to_nat n)) as b.
remember (bisect_c f 0 1 ((1#2)*e) H3 (Z.to_nat n)) as c.

(* First show f a<e/2 *)
assert( f a < (1#2)*e ). {
  rewrite Heqa.
  apply bisect_a_works.
  lra. lra.
}
(* Secondly: f b > -(1#2)*e *)
assert( f b > -((1#2)*e)). {
  rewrite Heqb.
  apply bisect_b_works.
  lra. lra.
}
(*Lastly show that the computed
  c satisfies the necessary bounds*)
assert( c-a < (1#2)^n ). {
  admit.
}
assert( b-c < (1#2)^n ). {
  admit.
}

(*With last two bounds we may use the fact that
  fb + (1#2)*e > 0 to get
  0<fb < fb - fc + fc + (1#2)*e < fc + e ->
  -e < fc *)
  assert(-e < (f c) ). {
    admit.
  }
  
(*With first and last bounds we may use the fact that
  fa-(1#2)*e<0 to get
  fc < fc - fa + (1#2)*e < e *)
  assert( (f c) < e ). {
    admit.
  }
  
  
(* The last two results may be combined to get the desired result *)

assert( Qabs (f c) < e ). {
  apply Qabs_bounds. lra. lra. lra.
}

exists c.
assert( 0<c /\ c<1). {
  rewrite Heqc.
  apply bisect_c_bounds.
}

destruct H13.
split.
* auto with *.
* auto with *.


Qed.



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
(*Simple quadratic function.*)
Definition quadratic (x:Q) := x*x.
(*Function with "discontinuity" at zero*)
Definition bad (x:Q) := if (Qlt_le_dec 0 x) then 1 else 0.
Definition worse (x:Q) := if (Qlt_le_dec (2#1) (x*x)) then 1 else 0.







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

Theorem const_is_differentiable : forall x, Differentiable const x.
Proof.
intros.
unfold Differentiable.
unfold const.
intros.
exists 1.
split.
* lra.
* simpl. lra.

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

Theorem linear_is_differentiable : forall x, Differentiable linear x.
Proof.
intros.
unfold Differentiable. unfold linear.
intros.
exists e.
split.
* lra.
* unfold Difference.
  assert( Qabs (x + e - x - e * ((x + e - x) / e))  == Qabs 0 ).
  {
    apply Qabs_extensional. field. lra.
  }
  rewrite H0.
  simpl. lra.
Qed.

Theorem quadratic_difference_formula : forall x h, h>0 -> Difference quadratic x h == (1+1)*x + h.
Proof.
intros.
unfold Difference. unfold quadratic.
field. auto with *.
Qed.

Theorem quadratic_is_differentiable : forall x, Differentiable quadratic x.
Proof.
intros.
unfold Differentiable, quadratic.
intros.
exists (e).
split. 
* nra.
* rewrite quadratic_difference_formula. 
** assert( Qabs( (x + e) * (x + e) - x * x -
   e * ((1 + 1) * x + e)) == Qabs(0) ). {
    apply Qabs_extensional. field.
   }
   rewrite H0. simpl. apply H.
** apply H.
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


Theorem worse_is_continuous : Continuous worse.
Proof.
unfold Continuous.
intros.
Qed.
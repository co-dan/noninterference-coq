Require Import Rushby.
From stdpp Require Import list relations collections fin_collections.

Module ArrayMachine <: Mealy.

Definition state := nat -> nat.
Inductive command :=
  | Write : nat -> nat -> command
  | Read : nat -> command
.
Definition action := command.
Definition out := nat.

Definition extendS (s : state) (n : nat) (m : nat) : state :=
  fun x => if beq_nat x n then m else s x.

Definition preform (s : state) (a : action) : state * out :=
  match a with
    | Write i j => (extendS s i j, 0)
    | Read i => (s, s i)
  end.

Definition step s a := fst (preform s a).
Definition output s a := snd (preform s a).
Definition initial (x : nat) := 0.
End ArrayMachine.

  
Import ArrayMachine.
Module M := Rushby.Rushby ArrayMachine.
Import M.

Eval compute in (do_actions [Write 1 1] 2).

Definition domain := action.
Definition nameA := nat.
Definition valA := nat.
Definition observeA (u : domain) : FinSet nameA :=
  match u with
    | Read i => {[ i ]}
    | Write _ _ => ∅
  end.
Definition alterA (u : domain) : FinSet valA :=
  match u with
    | Read _ => ∅
    | Write i _ => {[ i ]}
  end.


Instance domain_dec : forall (u v : domain), Decision (u = v).
Proof. intros.
unfold Decision.
repeat (decide equality).
Defined.

Instance arraymachine_ss : StructuredState domain := 
  { name := nameA; value := valA; contents s n := s n
  ; observe := observeA; alter := alterA }. 

Definition interference (u v : domain) :=
  (exists (n : nameA), n ∈ alterA u ∧ n ∈ observeA v).

Inductive interferenceR : relation domain :=
  | interference_refl : forall (u : domain), interferenceR u u
  | interference_step : forall (u v: domain), interference u v -> interferenceR u v.

Instance policy_ss : Policy domain := 
  { policy := interferenceR
  ; dom := fun (a : action) => (a : domain) }.
Proof.
intros. unfold Decision. 
destruct v as [i j | i]; destruct w as [m n | m].
- destruct (decide (i = m)). destruct (decide (j = n)); subst; auto.
left. constructor. 
right. intro I. inversion I; subst. apply n0. auto. 
inversion H. unfold observeA in *. destruct H0 as [HH HHH].
apply (not_elem_of_empty x); assumption.
right. intro. inversion H; subst. apply n0. auto. 
inversion H0. unfold alterA, observeA in *. destruct H1.
apply (not_elem_of_empty x); assumption.
- destruct (decide (i = m)); subst. left. right. unfold interference.
  simpl. exists m. split; apply elem_of_singleton; auto.
  right. intro. inversion H; subst. inversion H0. simpl in H1.
  destruct H1. apply elem_of_singleton in H1; apply elem_of_singleton in H2. subst. apply n;auto.
- right. intro. inversion H;subst. inversion H0; subst.
  simpl in H1; inversion H1. apply (not_elem_of_empty x); assumption.
- destruct (decide (i = m)); subst.
  left. constructor.
  right. intro. inversion H; subst. auto.
  inversion H0; subst. simpl in H1; inversion H1. eapply not_elem_of_empty. eassumption.
- intro u. constructor.
Defined.

Check RefMonAssumptions.

Instance rma_yay :  RefMonAssumptions.
Proof. split; simpl; unfold RMA_partition; intros;
       unfold contents in *; simpl in H8.
unfold output. 
 unfold preform. destruct a as [i j | i]; simpl in *. reflexivity. 
 apply H8. apply elem_of_singleton. reflexivity.
       
unfold step, preform. destruct a as [i j | i]. simpl in *.
destruct (decide (i = n)); subst; unfold extendS; simpl. 
replace (beq_nat n n) with true; auto. apply beq_nat_refl.
destruct H9. 
unfold step in H9; simpl in H9. unfold extendS in H9; simpl in H9.
replace (beq_nat n i) with false in *; auto.
congruence. SearchAbout beq_nat false. symmetry. apply beq_nat_false_iff. omega.
unfold step in H9; simpl in H9. unfold extendS in H9; simpl in H9.
replace (beq_nat n i) with false in *; auto.
congruence. symmetry. apply beq_nat_false_iff. omega.

simpl. destruct H9; unfold step, preform in H9; simpl in H9;
       congruence.

unfold step, preform in H8; simpl in H8. destruct a; simpl in *.
unfold extendS in H8. destruct (decide (n = n0)); subst.
apply elem_of_singleton; auto. replace (beq_nat n n0) with false in *; try (congruence). symmetry. apply beq_nat_false_iff. assumption.
congruence.
Defined.

Theorem yay : isecurity.
Proof.
  apply rma_secure_intransitive.
  intros u v n A1 A2. simpl.  right. firstorder.
Qed.


(* rewrite using the view partition relation
TODO *)

Require Import base.
Require Import Mealy.
Require Import Policy.
Require Import ViewPartition.

Class IsSecure {domain : Type}
      `(M : Mealy state action out)
      (P : Policy action domain) :=
  noninterference :
    (forall (ls : list action) (a : action), test ls a = test (purge ls (dom a)) a).
      
Section MealySec.
  Variable (state action out : Type).
  Variable (M : Mealy state action out).
  Variable domain : Type.
  Variable (P : Policy action domain).
  Variable (VP : ViewPartition M domain).
  Lemma output_consist_view_security {OC : OutputConsistent P VP} : (forall ls u,
  (do_actions ls) ≈{u} (do_actions (purge ls u)))
  -> IsSecure M P.
  Proof.
    intros L ls a.  apply output_consistent.
    apply (L _ (dom a)).
  Qed.

Instance unwinding {OC : OutputConsistent P VP} {LRP : LocallyRespectsPolicy P VP} {SC: StepConsistent P VP} : IsSecure M P.
Proof.
  apply output_consist_view_security.
  assert (forall ls v s t, view_partition v s t -> view_partition v (run s ls) (run t (purge ls v))) as General. (* TODO: a simple generalize would not suffice, because we actually need the s ≈ t assumption *)
    induction ls; simpl; auto.    
    intros u s t HI.
    destruct (decide (policy (dom a) u)).
    (* DOESNT WORK (Lexer) : destruct (decide ((dom a) ⇝ u)). *)
    (** Case [(dom a) ~> u] *) 
      eapply IHls. apply step_consistent. assumption.
    (** Case [(dom a) ~/> u] *)      
      eapply IHls. 
      transitivity s; [| assumption]. symmetry. apply locally_respects_policy. assumption.  
  unfold do_actions. intros ls u. eapply General; reflexivity. 
Qed.

Instance unwinding_trans {OC : OutputConsistent P VP} {LRP : LocallyRespectsPolicy P VP} {TP: Transitive policy} {SC: WeakStepConsistent P VP} : IsSecure M P.
Proof.
  apply output_consist_view_security.
  assert (forall ls u s t, (forall v, policy v u -> view_partition v s t) -> (forall v, policy v u -> view_partition v (run s ls) (run t (purge ls v)))) as General. 
    induction ls; simpl; auto.    
    intros u s t S v HI.
    destruct (decide (policy (dom a) v)).
    (** Case [(dom a) ~> u] *) 
      apply IHls with (u:=u); try assumption.
      intros v' Hv'. 
      apply weak_step_consistent; apply S. etransitivity; eassumption.
      assumption.
    (** Case [(dom a) ~/> u] *)      
      apply IHls with (u:=v); try assumption.
      intros v' Hv'.
      transitivity s. symmetry.
      apply locally_respects_policy. intro. 
      apply n. rewrite H. assumption. 
      apply S. rewrite Hv'. assumption. reflexivity.
  unfold do_actions. intros ls u. eapply General; reflexivity. 
Qed.

End MealySec.

Module MSyncSec.
  Variable (state action out : Type).
  Variable (M : MSync state action out).
  Definition M' : Mealy state action out := msync_mealy.
  Variable domain : Type.
  Variable (P : Policy action domain).
  Variable (VP' : ViewPartition M' domain).

  Instance VP: ViewPartition (MSync_as_Mealy (MS:=M)) domain
  :=
    { view_partition := @view_partition _ _ _ _ _ VP'
    ; view_partition_is_equiv := @view_partition_is_equiv _ _ _ _ _ VP'
    }.

  Class SyncPartitioned :=
    { sync_partitioned : forall s t a,  view_partition (dom a) s t  -> (delayed a s <-> delayed a t)
    }.

  
  Global Instance oc2 {SP: SyncPartitioned} (OC: OutputConsistent P VP') :
    OutputConsistent P VP.
  Proof.
    intros a s t L.
    unfold output; simpl.
    destruct (decide (delayed a s)) as [D | ND];
    destruct (decide (delayed a t)) as [D' | ND'];
    try solve
      [erewrite output_consistent by (apply L);
       reflexivity | reflexivity ].
    exfalso. apply ND'. rewrite <- (sync_partitioned s t a L). assumption.
    exfalso. apply ND. rewrite -> (sync_partitioned s t a L). assumption.
  Qed.

Theorem unwinding_sync_trans {SP: SyncPartitioned} {OC : OutputConsistent P VP'} {LRP : LocallyRespectsPolicy P VP'} {TP : Transitive policy} {SC: WeakStepConsistent P VP'} : IsSecure (MSync_as_Mealy (MS:=M)) P.
Proof.
intros.
apply unwinding_trans with (VP:=VP). (* TODO: i want this to be resolved automatically *) apply oc2. assumption.

(* Locally respects policy *)
intros a u s NP. unfold step; simpl. 
destruct (decide (delayed a s)); auto. reflexivity.

(* Transitive policy *) assumption. (* again, can this be picked up automatically? *)

(* Step-consitency *)
intros a s t u Ldom L. unfold step; simpl.
destruct (decide (delayed a s)) as [D | ND];
destruct (decide (delayed a t)) as [D' | ND'];
try assumption.
(* only s is delayed by a *)
exfalso. apply ND'. rewrite sync_partitioned; try eassumption.
symmetry; assumption.
(* similar case, but symmetric *)
exfalso. apply ND. rewrite sync_partitioned; try eassumption.
(* both s and t are delayed by a *)
eapply weak_step_consistent; assumption.
Qed.

End MSyncSec.

Module MApiSec.
  Variable (state action out : Type).
  Variable domain : Type.
  Variable API : Type.
  Variable (P : Policy API domain).
  Variable (M : MApi domain API state action out).
  Definition M' : Mealy state action out := mapi_mealy.
  Variable (VP' : ViewPartition M' domain).

  Definition vpeq : domain -> relation (state * (domain -> list action)) := fun d s1 s2 =>
                          let (s1', f) := s1
                          in let (s2', g) := s2
                          in @view_partition _ _ _ _ _ VP' d s1' s2' /\ f = g.

  Lemma vpeq_eq (d : domain) : Equivalence (vpeq d).
  Proof.
    intros. split; unfold vpeq.
    intros [s ?]. split; reflexivity. 
    
    intros [s ?] [t ?] [? ?]. split; symmetry; auto.

    intros [s ?] [t ?] [z ?] [? ?] [? ?]. split; etransitivity; eassumption.
  Qed.    

  Instance VP: ViewPartition (MApi_as_Mealy (MA:=M)) domain    
  :=
    { view_partition := vpeq
    ; view_partition_is_equiv := vpeq_eq
    }.

  Instance: IsSecure (MApi_as_Mealy (MA:=M)) P.
  Proof. intros. apply unwinding_trans with (VP:=VP).

         (* output consistency *)
         intro. intros [s f] [t g].
         simpl.
         remember (f (dom_api a)) as L1;
         remember (g (dom_api a)) as L2.
         destruct L1;
         destruct L2; try (subst; reflexivity).

         intros [? Z]. exfalso. rewrite Z in  *. 
         rewrite <- HeqL2 in *.
         inversion HeqL1.

         intros [? Z]. exfalso. rewrite Z in  *. 
         rewrite <- HeqL2 in *.
         inversion HeqL1.

         intros [? Z]. f_equal.
         rewrite Z in *.
         rewrite <- HeqL1 in *.
         inversion HeqL2.
         apply output_consistency.
         (* TODO replace dom in policy with the Dom class *)
End MApiSec.

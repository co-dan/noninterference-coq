Require Import Rushby.
Require Import base.

Class MSync (state action out : Type) 
  := {
  msync_mealy : Mealy state action out;
  delayed : action -> (state -> Prop);
  delayed_dec :> forall a s, Decision (delayed a s)
}.
Check @step.
Instance MSync_as_Mealy `{MSync state action out}
  : Mealy state action (option out).
Proof.
split.  exact (@initial _ _ _ msync_mealy).
refine (fun s a => if (decide (delayed a s))
                   then @step _ _ _ msync_mealy s a
                   else s).
refine (fun s a => if (decide (delayed a s))
                   then Some (@output _ _ _ msync_mealy s a)
                   else None).
Qed.
  
Section MealyM.

Variable state action out : Type.
Variable MM : MSync state action out.
Variable domain : Type.
Check Policy.
Variable P : Policy domain.
Variable VP : ViewPartition domain.


Definition sync_separation `{Policy action domain} := forall (s : state) (b : action) (a : action),
   ¬ (delayed a s) ∧ (delayed a (step s a))
   → policy (Rushby.dom b) (Rushby.dom a).

Definition sync_interf `{Policy action domain} `{MMs : MMsync state action out}

Class SyncPartition {domain state action out : Type} (MMs : MMsync state action out) {P : Policy domain} {VP : @ViewPartition state domain} :=  { 
  sync_partitioned : forall s t a,  view_partition (Rushby.dom a) s t  -> (delayed a s <-> delayed a t)
 }.


Section Unwinding.
Context {state action out : Type}.
Context {domain : Type}.
Context {P : @Policy action domain}.
Context {VP : @ViewPartition state domain}.
Context {MMs : MMsync state action out}.
Definition MM := underlyingM.
Definition N := (@MMsync_is_MM domain state action out MMs).

Context {OC : @OutputConsistent _ _ _ MM domain P VP}.
Context {SP : SyncPartition MMs}.
Instance OC' : @OutputConsistent _ _ _ N domain P VP.
Proof.
  intros a s t L.
  unfold output; simpl. 
  destruct (decide (delayed a s)) as [D | ND];
  destruct (decide (delayed a t)) as [D' | ND']; auto;
  try (erewrite output_consistent by (apply L); reflexivity);
   (exfalso; (apply ND' || apply ND);
             (rewrite <- (sync_partitioned s t a L) ||
              rewrite -> (sync_partitioned s t a L)); auto).
Qed.

Theorem unwinding_sync : locally_respects_policy (MM:=MM) -> step_consistent (MM:=MM) -> sync_separation -> security (MM:=N).
Proof. intros.
apply unwinding. 

(* local step consistency *)
intros a u s NP. unfold step; simpl. 
destruct (decide (delayed a s)); auto. reflexivity.
(* TODO auto cannot solve reflexivity? *)

intros a s t u L. unfold step; simpl.
destruct (decide (delayed a s)) as [D | ND];
destruct (decide (delayed a t)) as [D' | ND']; auto.
transitivity t; auto. apply H. apply 

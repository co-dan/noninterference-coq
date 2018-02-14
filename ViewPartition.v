Require Import base.
Require Import Policy.
Require Import Mealy.
(** Formally, a view partition is an assignment of an equivalence
relation [≈{u}] for every domain [u] *)
  
Class ViewPartition `(M : Mealy state action out) (domain : Type) := {
  view_partition :> domain -> relation state;
  view_partition_is_equiv :> forall v, Equivalence (view_partition v)
}.

Notation "S ≈{ U } T" := (view_partition U S T)
                           (at level 70, format "S  ≈{ U }  T").

Class OutputConsistent {domain : Type} `{M : Mealy state action out}
      (P : Policy action domain) (VP: ViewPartition M domain) := 
  output_consistent : (forall a s t, s ≈{dom a} t -> output s a = output t a).

Class LocallyRespectsPolicy {domain : Type} `{M : Mealy state action out}
      (P : Policy action domain) (VP: ViewPartition M domain) :=
  locally_respects_policy : (forall a u s, ¬(policy (dom a) u) -> s ≈{u} (step s a)).

Class WeakStepConsistent {domain : Type} `{M : Mealy state action out}
      (P : Policy action domain) (VP: ViewPartition M domain) :=
  weak_step_consistent : (forall a s t u, s ≈{dom a} t -> s ≈{u} t -> (step s a) ≈{u} (step t a)).

Class StepConsistent {domain : Type} `{M : Mealy state action out}
      (P : Policy action domain) (VP: ViewPartition M domain) :=
  step_consistent : (forall a s t u, s ≈{u} t -> (step s a) ≈{u} (step t a)).

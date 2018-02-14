(** Formalisation of "Noninterference, Transitivity, and Channel-Control Security Policies" by J. Rushby 
    www.csl.sri.com/papers/csl-92-2/
*)

(** printing -> #→# *)
(** printing (policy a b) #a ⇝ b# *)

From stdpp Require Import list relations collections fin_collections.
Parameter FinSet : Type -> Type.
(** begin hide **)
Context `{forall A, ElemOf A (FinSet A)}.
Context `{forall A, Empty (FinSet A)}.
Context `{forall A, Singleton A (FinSet A)}.
Context `{forall A, Union (FinSet A)}.
Context `{forall A, Intersection (FinSet A)}.
Context `{forall A, Difference (FinSet A)}.
Context `{forall A, Elements A (FinSet A)}.
Context `{forall A, Collection A (FinSet A)}.
(* TODO: i wrote this line down so that there is a Collection -> SimpleCollection -> JoinSemiLattice instance for FinSet; how come this is not automatically picked up by the next assumption? *)
Context `{forall A (H : EqDecision A), FinCollection A (FinSet A)}.
(** end hide **)

(** * Mealy machines *)

(** A Mealy machine is a state machine with labels and outputs on arrows *)

Class Mealy (state action out : Type) := {
  initial : state;
  step : state -> action -> state;
  output : state -> action -> out
}.

(** ** Auxiliary functions

We define a [run] of a machine [M], which is an extension of
the [step] function to lists of actions. We use a shortcut
[do_actions] for running the machine from the [initial] state. *)


Fixpoint run `{Mealy state action out} (s : state) (ls : list action) : state :=
  match ls with
    | nil => s
    | a::tl => run (step s a) tl
  end.

Definition do_actions `{Mealy state action out} : list action -> state := run initial.

(** The [test] function runs the required list of actions and examines the output of the resulting state on a specified action. *)
Definition test `{Mealy state action out} (ls : list action) : action -> out := output (do_actions ls).  

Section Rushby.
  
(** We assume for the rest of the formalisation that we have a Mealy
machine [M]. Thus, we parameterize our main development module by a machine [M].  *)


Context `{MM : Mealy state action out}.


(** * Security policies *)
Section Policy.

(** In order to define the notion of security, we assume a type [domain] of security domains. Those can be, e.g. clearance levels. For each action [a] we assign a domain [dom a] of that action. For instance, if we interpret domains as clearance levels, the domain of an action can signify the clearance level required to observe/preform the action.

A *security policy* is defined to be a reflexive decidable relation on the type of domains. For instance, the policy relation can state that the clearance level [u] is below the clearance level [v]. *)
Class Policy (domain : Type) := {
  dom : action -> domain;

  (** Sidenote: I had a lot of issues with Coq not finding relevant
  typeclass instances because the next field was declared as
  [domain_dec : TYPE] instead of [domain_dec :> TYPE]. So we actually
  do need implicit coercions to get automatic resolution of typeclass
  instances. *)

  domain_dec :> EqDecision domain;
  policy :> relation domain;
  policy_dec :> RelDecision policy;
  policy_refl :> Reflexive policy
}.

(** TODO: Make this notation span over different sections? *)
Delimit Scope policy_scope with P.
Open Scope policy_scope.
Infix "⇝" := policy (at level 70) : policy_scope.

(** Quoting Rushby: 

<<
     We wish to define security in terms of information flow, so the
     next step is to capture the idea of the "flow of information"
     formally. The key observation is that information can be said to
     flow from a domain [u] to a domain [v] exactly when the acions
     submitted by domain [u] cause the behavior of the system
     percieved by domain [v] to be different from that perceived when
     those actions are not present.
>>

Hence, we define a function [purge] that removes from the given list
all the actions that are not supposed to "influence" the domain [v].
*)

Fixpoint purge `{Policy domain} (ls : list action) (v : domain) : list action :=
  match ls with
    | [] => []
    | a::tl => if (decide (dom a ⇝ v)) then a::(purge tl v)
               else purge tl v
  end.


(** Then, the system is _secure_ w.r.t. a given policy if for any set
of actions that can be performed, the system cannot tell the
difference between preforming the given actions and only performing
the actions that are supposed to influence the outcome *)

Definition security `{Policy domain} := forall (ls : list action) (a : action),
   test ls a = test (purge ls (dom a)) a.


End Policy.

(** * View partitions

As we have seen, the non-interference notion of security is defined by
quantifying over all the possible paths of the system. We wish to
develop techniques for establishing the security property by putting
conditions on individual state transformations.

As a first step, we define a notion of a "view partition", which is an
equivalence relation on the type of states of the system, siginfying
that two states are "identitcal" or indistinguishable for a given
domain.

*)

Section view_partitions.

(** Formally, a view partition is an assignment of an equivalence
relation [≈{u}] for every domain [u] *)
  
Class ViewPartition (domain : Type) := {
  view_partition :> domain -> relation state;
  view_partition_is_equiv :> forall v, Equivalence (view_partition v)
}.

Notation "S ≈{ U } T" := (view_partition U S T)
                           (at level 70, format "S  ≈{ U }  T") : policy_scope.
Open Scope policy_scope.
(** We say that a system is _output consistent_ if for every two
states [s, t] that are indistinguishable w.r.t. the domain [dom a],
the output of the system [output s a] is the same as [output t a] *)

Class OutputConsistent `{P : Policy domain} `(ViewPartition domain) := 
  output_consistent : (forall a s t, s ≈{dom a} t -> output s a = output t a).

(** Our first lemma states that if we have a view partitioned system
that is output consistent and satisfies

[[(do_actions ls) ≈{u} (do_actions (purge ls u))]]

then the system is secure. *)

(* Lemma 1 *)
Lemma output_consist_security `{P : Policy domain} `{VP : ViewPartition domain} {OC : @OutputConsistent domain P VP} : (forall ls u,
  (do_actions ls) ≈{u} (do_actions (purge ls u)))
  -> security.
Proof.
  intros L ls a.  apply output_consistent.
  apply (L _ (dom a)).
Qed.

(** Note that the conditions of Lemma [output_consist_security] still
require us to quantify over all possible paths of the system. We wish
to replace this condition with the following two "local" conditions.

The first condition, stating that the view partitioned system _locally
respects policy_: if the domain [dom a] is not suppose to interfere
with the domain [u], then, from the point of view of [u], the states
[s] and [step s a] are indistinguishable.
*)

Definition locally_respects_policy `{Policy domain} `{ViewPartition domain} := forall a u s,
  ¬(policy (dom a) u) -> s ≈{u} (step s a).

(** We say that the system is *step consistent*, if the view partition
is closed under the [step] function. *)

Definition step_consistent `{Policy domain} `{ViewPartition domain} := forall a s t u,
  s ≈{u} t -> (step s a) ≈{u} (step t a).

(** Given those two conditions we can prove that the system is secure,
by applying the previous lemma *)

(* Theorem 1 *)
Theorem unwinding `{P: Policy domain} `{VP: ViewPartition domain} `{@OutputConsistent  domain P VP} : locally_respects_policy -> step_consistent -> security.
Proof.
  intros LRP SC. apply output_consist_security.
  assert (forall ls u s t, view_partition u s t -> view_partition u (run s ls) (run t (purge ls u))) as General. (* TODO: a simple generalize would not suffice, because we actually need the s ≈ t assumption *)
    induction ls; simpl; auto.    
    intros u s t HI.
    destruct (decide (policy (dom a) u)).
    (* DOESNT WORK (Lexer) : destruct (decide ((dom a) ⇝ u)). *)
    (** Case [(dom a) ~> u] *) 
      apply IHls. apply SC; assumption.
    (** Case [(dom a) ~/> u] *)      
      apply IHls. 
      transitivity s. symmetry. unfold locally_respects_policy in LRP. apply LRP; assumption. assumption.  
  unfold do_actions. intros ls u. apply General. reflexivity.
Qed.

End view_partitions.

(** * Access control interpretation of the view partition.  *)

Section ACI.

(** In this section we consider a formalisation of the access control mechansisms. 

We say that the machine has _structured state_ if we have a collection
of [name]s and [value]s (the latter being decidable), and some sort of
the memory assigned to each state, which is formally given by the
[contents] function. For each domain [u] we assign sets [observe u]
and [alter u] of names that are allowed to be observed and altered,
respectively, by the domain [u]. *)

Class StructuredState (domain : Type)  := {
  name : Type;
  value : Type;
  contents : state -> name -> value;
  value_dec :> EqDecision value;
  observe : domain -> FinSet name;
  alter : domain -> FinSet name
}.

(** This induces the view partition relation as follows: two state [s]
and [t] are indistinguishable for the given domain, if all the
observable contents at [s] is the same as the observable content at
[t] *)

Definition RMA_partition `{@StructuredState domain} (u : domain) s t := (forall n,  (n ∈ observe u) -> contents s n = contents t n).

Transparent RMA_partition.

Instance RMA `{@StructuredState domain} : ViewPartition domain := { view_partition := RMA_partition }.
(* begin hide *)
  intro u. split; unfold RMA_partition.
  (* Reflexivity *) unfold Reflexive. auto.
  (* Symmetry *) unfold Symmetric. intros x y Sy.
  symmetry. apply Sy. assumption.
  (* Transitivity *) unfold Transitive. intros x y z T1 T2 n.
  transitivity (contents y n); [apply T1 | apply T2]; assumption.
Defined. (* We have to use 'Defined' here instead of 'Qed' so that we can unfold 'RMA' later on *)
(* end hide *)

Hint Resolve RMA.

(** ** Reference monitor assumptions *)
(* TODO: explain those assumptions *)
Class RefMonAssumptions `{Policy domain} `{StructuredState domain} :=
  { rma1 : forall (a : action) s t,
             view_partition (dom a) s t -> output s a = output t a
  ; rma2 : forall a s t n,
             view_partition (dom a) s t ->
             ((contents (step s a) n) ≠ (contents s n)
                ∨ (contents (step t a) n) ≠ (contents t n))
             -> contents (step s a) n = contents (step t a) n
  ; rma3 :  forall a s n,
               contents (step s a) n ≠ contents s n -> n ∈ alter (dom a)
}.                                               
      
(** If the reference monitor assumptions are satisfied, then the system is output-consistent *)
Global Instance OC `{RefMonAssumptions}: OutputConsistent RMA.
exact rma1. Defined.

(** The reference mointor assumptions provide the security for the system, if, furthermore, two additional requirements are satisfied:

- [u ~> v] implies [observe u ⊆ observe v]; that is, if [u] is supposed to interfere with [v], then [v] can observe at least as much as [u]
- if [n ∈ alter u] and [n ∈ observe v], then [u ~> v]; that is, if [u] is allowed to alter a location that is observable by [v], then [u] is allowed to interfere with [v]
*)

(* Theorem 2 *)
Theorem RMA_secutity `{RefMonAssumptions} : 
  (forall u v, (policy u v) → observe u ⊆ observe v)
  -> (forall u v n, (n ∈ alter u) → (n ∈ observe v) → (policy u v))
  -> security.
Proof.
  intros Cond1 Cond2. apply unwinding. 
  (** We apply the unwinding theorem, so we have to verify that
     we locally respect policy and that we have step-consistency *)  
  unfold locally_respects_policy. 
  intros a u s.

  (** In order to prove that the system locally respects the policy
  relation, we first state the contrapositive, which we can prove
  because the policy relation and type of values are decidable *)

  assert ((exists n, (n ∈ observe u ∧ (contents s n ≠ contents (step s a) n))) -> policy (dom a) u) as CP.
    intros opH. destruct opH as [n [??]].
    eapply Cond2. eapply rma3. eauto. assumption.
  intros NPolicy.
  unfold view_partition, RMA, RMA_partition. 
  (* TODO: why can't decide automatically pick the instance value_dec? *)
  intros. destruct (decide (contents s n = contents (step s a) n)) as [e|Ne]. assumption. exfalso. apply NPolicy. apply CP.
  exists n; split; assumption.

  (** In order to prove step-consistency we wish to apply the second
  reference monitor assumption. For that we must distinguish three
  cases: (contents (step s a) n ≠ contents s n), (contents (step t a)
  n ≠ contents t n), or if both of the equalities hold *)
  intros a s t u A.
  unfold view_partition, RMA, RMA_partition in *.
  intros n nO.
  destruct (decide (contents (step s a) n = contents s n)) as [E1 | NE1].
  destruct (decide (contents (step t a) n = contents t n)) as [E2 | NE2].
  (* Both equalities hold *)
  rewrite E1, E2. apply A; assumption.
  (* NE2 *)
  (* We use the Second RM assmption to deal with this case *)
  apply rma2. (* for this we have to show that s ~_(dom a) t *)
  unfold view_partition, RMA, RMA_partition.
  intros m L. apply A. 
  apply Cond1 with (u:=dom a).
  apply Cond2 with (n:=n); [eapply rma3 | ]; eassumption.
  assumption.
  right. auto.
  (* NE1 case is similar *)
  (* TODO: repetition *)
  apply rma2. (* for this we have to show that s ~_(dom a) t *)
  unfold view_partition, RMA, RMA_partition.
  intros m L. apply A. 
  apply Cond1 with (u:=dom a).
  apply Cond2 with (n:=n); [eapply rma3| ]; eassumption.
  assumption.
  left. auto.
Qed.

End ACI.

(** * Intransitive security policy *)
Section Intransitive.

(** Auxiliary  definitions *)
Fixpoint sources `{Policy domain} (ls : list action) (d : domain) : FinSet domain :=
  match ls with
    | [] => {[ d ]}
    | a::tl => let src := sources tl d in
               if (decide (exists (v: domain), ((v ∈ src) ∧ (policy (dom a) v))))
               then src ∪ {[ dom a ]} else src
  end.

(** The two properties of the [sources] function: it is monotone and [d \in sources ls d] *)
Lemma sources_mon `{Policy} : forall a ls d, sources ls d ⊆ sources (a::ls) d.
Proof.
  intros. simpl.
  destruct (decide _); [apply union_subseteq_l |]; auto. 
Qed.

Hint Resolve sources_mon.

Lemma sources_monotone `{Policy} : forall ls js d, sublist ls js → sources ls d ⊆ sources js d.
Proof.
  intros ls js d M.
  induction M. simpl. reflexivity.
  simpl. destruct (decide (∃ v : domain, v ∈ sources l1 d ∧ policy (dom x) v)); destruct (decide (∃ v : domain, v ∈ sources l2 d ∧ policy (dom x) v)).  
  - apply union_mono_r. assumption.
  - exfalso. apply n. destruct e as [v [e1 e2]]. exists v; split; try (apply (IHM v)); assumption.
  - transitivity (sources l2 d). assumption. apply union_subseteq_l.
  - assumption.
  - transitivity (sources l2 d); auto. 
Qed.

Lemma sources_in `{Policy} : forall ls d, d ∈ sources ls d.
Proof.
  intros. induction ls; simpl.  apply elem_of_singleton_2; auto.
  destruct (decide (∃ v : domain, v ∈ sources ls d ∧ policy (dom a) v)); simpl.
  apply elem_of_union_l. assumption. assumption.
Qed.

Hint Resolve sources_in.

(* TODO: why is this not picked up automatically? *)
Instance sources_elem_of_dec `{Policy} (v : domain) ls d : Decision (v ∈ sources ls d).
Proof. apply elem_of_dec_slow. Qed.

Fixpoint ipurge `{Policy} (ls : list action) (d : domain) {struct ls} : list action :=
  match ls with
    | [] => []
    | a::tl => if (decide ((dom a) ∈ sources ls d))
               then a::(ipurge tl d)
               else ipurge tl d
  end.

(** The non-interference notion of security for intransitive policies
is very similar to the transitive case, bu uses the [ipurge] function
instead of [purge] *)

Definition isecurity `{Policy} := forall ls a,
  test ls a = test (ipurge ls (dom a)) a.

(** We can prove lemmas similar to the transitive case *)

Lemma output_consist_isecurity `{P : Policy domain} `{VP : ViewPartition domain} {OC : @OutputConsistent domain P VP} : (forall ls u,
  view_partition u (do_actions ls) (do_actions (ipurge ls u)))
  -> isecurity.
Proof.
  unfold isecurity. intros H ls a.
  unfold test.
  apply output_consistent.
  apply (H ls (dom a)).
Qed.

Definition view_partition_general `{ViewPartition domain} (C : FinSet domain) s t := forall (u: domain), u ∈ C -> view_partition u s t.

Global Instance view_partition_general_equiv `{ViewPartition domain}: 
  forall V, Equivalence (view_partition_general V).
Proof.
  intro V. split.
  intros x v A. reflexivity.
  intros x y A1 v A2. symmetry. apply (A1 v); assumption.
  intros x y z A1 A2 v A3. transitivity y. apply (A1 v); assumption. apply  (A2 v); assumption.
Qed.

Definition weakly_step_consistent `{Policy domain} `{ViewPartition domain} :=
  forall s t u a, view_partition u s t -> view_partition (dom a) s t -> view_partition u (step s a) (step t a).

Ltac exists_inside v := 
  let H := fresh "Holds" in
  let nH := fresh "notHolds" in
  destruct (decide _) as [H | []]; 
  [ try reflexivity | exists v; try auto].

Local Hint Resolve sources_mon.
Local Hint Extern 1 (_ ∈ sources (_::_) _) => eapply sources_mon.
Local Hint Immediate elem_of_singleton.
(* Local Hint Extern 1 (_ ∈ {[ _ ]}) => apply elem_of_singleton; trivial. *)
Local Hint Resolve elem_of_union.

(* Lemma 3 *)
Lemma weakly_step_consistent_general `{Policy domain} `{ViewPartition domain} (s t : state) (a : action) ls (u: domain) : weakly_step_consistent -> locally_respects_policy ->
  view_partition_general (sources (a::ls) u) s t 
  -> view_partition_general (sources ls u) (step s a) (step t a).
Proof.
  intros WSC LRP P v vIn.
  unfold view_partition_general in P.
  unfold locally_respects_policy in LRP.
  destruct (decide (policy (dom a) v)).
  (* Case [dom a ~> v] *)
  apply WSC; apply P. auto. 
  (* we need to show that [dom a ∈ sources (a::ls) v] *)  
  simpl. exists_inside v. apply elem_of_union. right. auto.  apply elem_of_singleton; trivial.
  (* Case [dom a ~/> v] *)
  transitivity s. symmetry. apply LRP; assumption.
  transitivity t. apply P. auto. 
  apply LRP; assumption.
Qed.

(* Lemma 4 *)
Lemma locally_respects_gen `{Policy domain} `{ViewPartition domain} (WSC: weakly_step_consistent) (LRP : locally_respects_policy) s a ls u :
  ¬ ((dom a) ∈ sources (a::ls) u) ->
  view_partition_general (sources ls u) s (step s a).
Proof.
  intros domN v vIn.
  apply LRP. intro.
  (* If [dom a ~> v], then [dom a ∈ sources (a::ls) u], because [v ∈ sources ls u] *) (* again, a clusterfuck *)
  apply domN. simpl.
  exists_inside v; auto. apply elem_of_union; right; apply elem_of_singleton; reflexivity.
Qed.


(* Lemma 5 *)
Lemma unwinding_gen `{Policy domain} `{ViewPartition domain} (WSC: weakly_step_consistent) (LRP : locally_respects_policy) s t ls u :
  view_partition_general (sources ls u) s t
  -> view_partition u (run s ls) (run t (ipurge ls u)).
Proof.
  generalize dependent s.
  generalize dependent t.
  induction ls; intros s t.
  simpl. intro A. apply (A u). apply elem_of_singleton; reflexivity.
  intro VPG. simpl. unfold sources. fold (sources (a::ls) u).
  
  destruct (decide _).
  (** Case [dom a ∈ sources (a::ls) u] *)
  simpl. apply IHls. apply weakly_step_consistent_general; auto.
  (** Case [dom a ∉ sources (a::ls) u] *)
  apply IHls. symmetry. transitivity t. 
  - intros v vIn. symmetry. apply VPG. apply sources_mon; exact vIn.
  - apply locally_respects_gen; try(assumption). 
Qed.


Theorem unwinding_intrans `{P : Policy domain} `{VP : ViewPartition domain}
 `{OC : @OutputConsistent domain P VP} (WSC : weakly_step_consistent) (LRP : locally_respects_policy) : isecurity.
Proof.
  apply output_consist_isecurity.
  intros.
  apply unwinding_gen; try assumption.
  reflexivity.
Qed.

Theorem rma_secure_intransitive `{RefMonAssumptions} : (forall u v n, n ∈ alter u -> n ∈ observe v -> policy u v) -> isecurity.
Proof. intro policyA.
  apply @unwinding_intrans with (VP:=RMA). exact rma1.
  intros s t u a A1 A2.
  unfold view_partition. unfold RMA_partition; simpl. intros n L.
  destruct (decide (contents (step s a) n = contents s n)) as [E1 | NE1].
  destruct (decide (contents (step t a) n = contents t n)) as [E2 | NE2].
  (* Case [contents (step s a) n = contents s n /\ contents (step t a) n = contents t n] *) 
  rewrite E1, E2. apply A1; assumption.
  (* Case [contents (step t a) n ≠ contents t n] *)
  apply rma2; [ | right]; assumption.
  (* Case [contents (step s a) n ≠ contents s n] *)
  apply rma2; [ | left]; assumption.

  intros a u s A.
  assert ((exists n, (n ∈ observe u ∧ (contents s n ≠ contents (step s a) n))) -> policy (dom a) u) as CP.
    intros opH. destruct opH as [n [??]].
    eapply policyA. eapply rma3. eauto. assumption.
  intros n L. destruct (decide (contents s n = contents (step s a) n)). assumption. exfalso. apply A.
  apply CP. exists n. auto.
Qed.

End Intransitive.

End Rushby.

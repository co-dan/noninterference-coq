Require Import base.
Require Import Monoids.

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

Global Instance MealyMRet `{Monoid out op e} : MRet (λ A, (A * out)%type) :=
  fun A x => (x, e).
Global Instance MealyMBind `{Monoid out op e} : MBind (λ A, (A * out)%type) :=
  fun A B (f : A → B * out) (x : A * out) => 
    match x with
      (x₁,x₂) => match f x₁ with
                   (y₁,y₂) => (y₁, op x₂ y₂)
                 end
    end.
Global Instance MealyMonad `{Monoid out op e} `{Mealy state action out} :
  Monad (λ A, (A * out)%type).
Proof. split; intros;
unfold mret, mbind; unfold MealyMRet, MealyMBind.
destruct m. rewrite right_id; auto. 
apply H. (* TODO: why is this not being picked up automatically? *)

destruct (f x). rewrite left_id; auto. apply H.

destruct m. destruct (f a). destruct (g b).
rewrite associative. reflexivity. apply H.
Qed.
About run.

Class MSync (state action out : Type) 
  := {
  msync_mealy : Mealy state action out;
  delayed : action -> (state -> Prop);
  delayed_dec :> forall a s, Decision (delayed a s)
}.

Global Instance MSync_as_Mealy `{MS: MSync state action out}
  : Mealy state action (option out) :=
  { initial := @initial _ _ _ msync_mealy
  ; step := fun s a => if (decide (delayed a s))
                   then s
                   else @step _ _ _ msync_mealy s a
  ; output := fun s a => if (decide (delayed a s))
                   then None
                   else Some (@output _ _ _ msync_mealy s a)
  }.


Class MApi (domain : Type) (API : Type) (state action out : Type) :=
  { mapi_mealy : Mealy state action out
  ; domain_dec :> forall (x y : domain), Decision (x = y)
  ; dom_api : API -> domain
  ; sem_api : API -> list action
  }.

Definition upd `{MApi domain API s a o}
           (f : domain -> list a) a b :=
  fun d => if (decide (a = d)) then b else f d.

Global Instance MApi_as_Mealy `{MA: MApi domain API state action out}
  : Mealy (state * (domain -> list action)) API (option out)
  :=
  { initial := (@initial _ _ _ mapi_mealy, (λ _,[]))
  ; step := fun s a => let (s', f) := s
                       in let step' := @step _ _ _ mapi_mealy
                       in match (f (dom_api a)) with
                          | [] => (s', upd f (dom_api a) (sem_api a))
                          | (x::xs) => (step' s' x, upd f (dom_api a) xs)
                          end
  ; output := fun s a => let (s', f) := s
                         in let output' := @output _ _ _ mapi_mealy
                         in match (f (dom_api a)) with
                          | [] => None
                          | (x::xs) => Some (output' s' x)
                          end
  }.



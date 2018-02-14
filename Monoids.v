Require Import base.

Class Monad M {ret : MRet M} {bind : MBind M} :=
  { ret_unit_1 : forall {A} (m : M A) , m ≫= mret = m
  ; ret_unit_2 : forall {A B} (x : A) (f : A → M B),
      (mret x) ≫= f = f x
  ; bind_assoc : forall {A B C} (m : M A) (f : A → M B) (g : B → M C),
      (m ≫= f) ≫= g = m ≫= (fun x => f x ≫= g)
  }.

Global Instance Join_of_Monad M `{Monad M} : (MJoin M) :=
  fun A (m : M (M A)) => m ≫= id.
Global Instance FMap_of_Monad M `{Monad M} : FMap M :=
  fun A B f ma => ma ≫= (fun x => mret (f x)).

Class Monoid A (op: A → A → A) (e : A) :=
  { op_assoc : Associative (=) op
  ; e_left   : LeftId (=) e op
  ; e_right  : RightId (=) e op
  }.

Definition kleisli {A B C} `{mon : Monad M} (f : A → M B) (g : B → M C) (x : A) : M C := y ← f x; g y.
Notation "f >=> g" := (kleisli f g) (at level 60, right associativity) : C_scope.
Notation "( f >=>)" := (kleisli f) (only parsing) : C_scope.
Notation "(>=> g )" := (fun f => kleisli f g) (only parsing) : C_scope.
Notation "(>=>)" := (fun f g => kleisli f g) (only parsing) : C_scope.
Notation "g <=< f" := (kleisli f g) (at level 60, right associativity) : C_scope.
Notation "( g <=<)" := (fun f => kleisli f g) (only parsing) : C_scope.
Notation "(<=< f )" := (kleisli f) (only parsing) : C_scope.


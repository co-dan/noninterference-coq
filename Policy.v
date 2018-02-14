Require Import base.

Class Policy (action domain : Type) := {
  dom : action -> domain;
  domain_dec :> forall (x y : domain), Decision (x = y);
  policy :> relation domain;
  policy_dec :> (forall v w, Decision (policy v w));
  policy_refl :> Reflexive policy
}.

Infix "⇝" := policy (at level 70).

Fixpoint purge `{Policy action domain} (ls : list action) (v : domain) : list action :=
  match ls with
    | [] => []
    | a::tl => if (decide (dom a ⇝ v)) then a::(purge tl v)
               else purge tl v
  end.


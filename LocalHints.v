(* NOTE(dbp 2017-03-26): Often when inverting, we only want to handle
   cases that are _not_ variables. This will fail if C is a variable
   of type T *)
Ltac not_var C T :=
  match goal with
  |[ C' : T |- _ ] =>
   match C with
   | C' => fail 2
   | _ => fail 1
   end
  | _ => idtac
  end.

Tactic Notation "hint" constr(E) :=
  let H := fresh "Hint" in
  let t := type of E in
  assert (H : t) by exact E.

Tactic Notation "hint" constr(E) "," constr(E1) := hint E; hint E1.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) :=
  hint E; hint E1; hint E2.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) :=
  hint E; hint E1; hint E2; hint E3.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  hint E; hint E1; hint E2; hint E3; hint E4.
Tactic Notation "hint" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) "," constr(E5) :=
  hint E; hint E1; hint E2; hint E3; hint E4; hint E5.


Inductive RR (A : Prop) : Prop :=
| rewrite_rule : forall a : A, RR A.

Definition unRR (A : Prop) (r : RR A) :=
  match r with
  | rewrite_rule rr => rr
  end.

Tactic Notation "hint_rewrite" constr(E) := 
  let H := fresh "Hint" in
  let t := type of E in
  assert (H : RR t) by exact (rewrite_rule E).

Tactic Notation "hint_rewrite" constr(E) "," constr(E1) :=
  hint_rewrite E; hint_rewrite E1.
Tactic Notation "hint_rewrite" constr(E) "," constr(E1) "," constr(E2) :=
  hint_rewrite E; hint_rewrite E1; hint_rewrite E2.
Tactic Notation "hint_rewrite" constr(E) "," constr(E1) "," constr(E2) "," constr(E3) :=
  hint_rewrite E; hint_rewrite E1; hint_rewrite E2; hint_rewrite E3.

Ltac swap_rewrite t :=
  match type of t with
  | ?v1 = ?v2 => constr:(eq_sym t) 
  | forall x : ?T, _ =>
    (* let ret :=  *)constr:(fun x : T => let r := t x in 
                                      ltac:(let r' := swap_rewrite r in
                                            exact r')) (* in *)
    (* let ret' := (eval cbv zeta in ret) in *)
    (* constr:(ret) *)
  end.

Tactic Notation "hint_rewrite" "<-" constr(E) := 
  let H := fresh "Hint" in
  let E' := swap_rewrite E in
  let t := type of E' in
  assert (H : RR t) by exact (rewrite_rule E').


Hint Extern 5 => match goal with
                |[H : RR (_ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *)
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.
Hint Extern 5 => match goal with
                |[H : RR (forall _ _ _ _ _ _ _, _ = _) |- _] =>
                 progress (rewrite (unRR H) in *) 
                end.

Tactic Notation "hint_tactic" constr(name) :=
  let H := fresh "HintEnable" in
  assert (H : name = True) by reflexivity.

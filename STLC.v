Require Import Coq.Unicode.Utf8 Arith FunctionalExtensionality String Coq.Program.Equality.

Load CpdtTactics.

Set Implicit Arguments.

Ltac iauto := try solve [intuition (eauto 3)].
Ltac iauto' := try solve [intuition eauto].
Ltac invert H := inversion H; clear H; try subst.

Tactic Notation "hint" constr(E) :=
  let H := fresh "Hint" in
  let t := type of E in
  assert (H : t) by (exact E).

Tactic Notation "hint_rewrite" constr(E) := hint E.

(* NOTE(dbp 2017-03-25): We want _local_ rewrites, so we use the same strategy
   as local apply - get them into our hypothesis with `hint`, and then rewrite
   based on that. To do that, we have a general rule that tries to rewrite based
   on hypothesis that end in an equality. *)
Hint Extern 5 => match goal with
                |[H : forall _ _ _ _, _ -> _ -> _ = _ |- _] =>
                 progress (rewrite H in *)
                |[H : forall _ _, _ -> forall _, _ = _ |- _] =>
                 progress (rewrite H in *)
                |[H : forall _ _ _ _ _, _ -> _ = _ |- _] =>
                 progress (rewrite H in *)
                |[H : forall _ _ _ _, _ -> _ = _ |- _] =>
                 progress (rewrite H in *)
                |[H : forall _ _ _, _ -> _ = _ |- _] =>
                 progress (rewrite H in *) 
                end.


(**************************************)
(************ 1. SYNTAX ***************)
(**************************************)

(** This section contains the types and terms for
    out simply typed lambda calculus (which has bools,
    if, and pairs).
*)

Inductive ty  : Set :=
| Bool : ty
| Fun : ty -> ty -> ty
| Product : ty -> ty -> ty.

Inductive exp : Set :=
| Var : string -> exp
| Const : bool -> exp
| Abs : string -> ty -> exp -> exp
| App : exp -> exp -> exp
| If : exp -> exp -> exp -> exp
| Pair : exp -> exp -> exp.

Inductive value : exp -> Prop :=
| VBool : forall b, value (Const b)
| VAbs : forall x t e, value (Abs x t e)
| VPair : forall v1 v2, value v1 -> value v2 -> value (Pair v1 v2).

(**************************************)
(**** 2. SUBSTITUTION/ENVIRONMENTS ****)
(**************************************)

(** This section contains definitions of environments,
    extension, substitution, what it means to be
    closed, etc.

    In this presentation, environments are represented
    as lists, _not_ as functions as is sometimes done.
*)

Definition tyenv := list (string * ty).

Definition venv := list (string * exp).

Definition extend {T : Set} (G : list (string * T)) (x:string) (t : T) : list (string * T) :=
  cons (x,t) G.

Fixpoint mextend  {T : Set} (e : list (string * T)) (G : list (string * T)) {struct G} : list (string * T) :=
  match G with
    | nil => e
    | cons (x,v) G' => extend (mextend e G') x v
  end.

Fixpoint lookup {T : Set}
                (E : list (string * T))
                (x:string) : option T :=
  match E with
    |cons (y,t) rest => if string_dec y x then Some t else lookup rest x
    |nil => None
  end.

Fixpoint drop {T : Set}
         (x:string)
         (E : list (string * T)) : list (string * T) :=
  match E with
    | nil => nil
    | cons (y,t) rest => if string_dec x y then drop x rest else cons (y,t) (drop x rest)
  end.

Fixpoint sub (x:string) (e:exp) (e':exp) : exp :=
  match e with
    | Var y => if string_dec y x then e' else e
    | Const b => e
    | Abs y t body => if string_dec y x
                     then e
                     else Abs y t (sub x body e')
    | App e1 e2 => App (sub x e1 e') (sub x e2 e')
    | If ec e1 e2 => If (sub x ec e')
                       (sub x e1 e')
                       (sub x e2 e')
    | Pair e1 e2 => Pair (sub x e1 e') (sub x e2 e')
    end.

Notation "'[' x ':=' s ']' t" := (sub x t s) (at level 20).

Inductive free_in : string -> exp -> Prop :=
| free_var : forall x, free_in x (Var x)
| free_abs : forall x t y e, free_in x e ->
                      x <> y ->
                      free_in x (Abs y t e)
| free_app1 : forall x e1 e2, free_in x e1 ->
                         free_in x (App e1 e2)
| free_app2 : forall x e1 e2, free_in x e2 ->
                         free_in x (App e1 e2)
| free_if1 : forall x e1 e2 e3, free_in x e1 ->
                           free_in x (If e1 e2 e3)
| free_if2 : forall x e1 e2 e3, free_in x e2 ->
                           free_in x (If e1 e2 e3)
| free_if3 : forall x e1 e2 e3, free_in x e3 ->
                           free_in x (If e1 e2 e3)
| free_pair1 : forall x e1 e2, free_in x e1 ->
                          free_in x (Pair e1 e2)
| free_pair2 : forall x e1 e2, free_in x e2 ->
                          free_in x (Pair e1 e2).

Hint Constructors free_in.

Ltac free_invert :=
  match goal with
    |[H : free_in _ _ |- _] => invert H
  end.

Definition closed t := forall x, ~ free_in x t.

Fixpoint closed_env (e:venv) :=
  match e with
    | nil => True
    | cons (_,e1) en => closed e1 /\ closed_env en
  end.

Fixpoint close (Σ : venv) (e : exp) : exp :=
  match Σ with
    |nil => e
    |cons (x,v) Σ' => close Σ' ([x:=v]e)
  end.


(**************************************)
(******** 3. TYPING JUDGEMENT *********)
(**************************************)

(** This section contains the main typing judgement.
*)

Reserved Notation "Γ '|--' e" (at level 10).

Inductive has_type : tyenv -> exp -> ty -> Prop :=
| TConst : forall Γ b, has_type Γ (Const b) Bool
| TVar : forall Γ x t, lookup Γ x = Some t -> has_type Γ (Var x) t
| TAbs : forall Γ x e t t', has_type (extend (drop x Γ) x t) e t' ->
                       has_type Γ (Abs x t e) (Fun t t')
| TApp : forall Γ e e' t1 t2, has_type Γ e (Fun t1 t2) ->
                         has_type Γ e' t1 ->
                         has_type Γ (App e e') t2
| TIf : forall Γ e1 e2 e3 t, has_type Γ e1 Bool ->
                        has_type Γ e2 t ->
                        has_type Γ e3 t ->
                        has_type Γ (If e1 e2 e3) t
| TPair : forall Γ e1 e2 t1 t2, has_type Γ e1 t1 ->
                           has_type Γ e2 t2 ->
                           has_type Γ (Pair e1 e2)
                                      (Product t1 t2)
where "Γ '|--' e" := (has_type Γ e).

Hint Constructors has_type ty exp value.



(**************************************)
(****** 4. EVALUATION RELATION ********)
(**************************************)

(** This section contains the evaluation relation for
    the language, which is based on evaluation contexts.
*)

Inductive context : Set :=
| CHole : context
| CApp1 : context -> exp -> context
| CApp2 : exp -> context -> context
| CIf : context -> exp -> exp -> context
| CPair1 : context -> exp -> context
| CPair2 : exp -> context -> context.

Hint Constructors context.

Inductive plug : context -> exp -> exp -> Prop :=
| PHole : forall e, plug CHole e e
| PApp1 : forall e e' C e2, plug C e e' ->
                       plug (CApp1 C e2) e (App e' e2)
| PApp2 : forall e e' C v, plug C e e' ->
                       value v ->
                       plug (CApp2 v C) e (App v e')
| PIf : forall e e' C e2 e3, plug C e e' ->
                        plug (CIf C e2 e3) e (If e' e2 e3)
| PPair1 : forall e e' C e2, plug C e e' ->
                        plug (CPair1 C e2) e (Pair e' e2)
| PPair2 : forall e e' C v, plug C e e' ->
                       value v ->
                       plug (CPair2 v C) e (Pair v e').

Hint Constructors plug.


Inductive step_prim : exp -> exp -> Prop :=
| SBeta : forall x t e v, value v -> step_prim (App (Abs x t e) v)
                                         ([x:=v]e)
| SIfTrue : forall e1 e2, step_prim (If (Const true) e1 e2) e1
| SIfFalse : forall e1 e2, step_prim (If (Const false) e1 e2) e2.

Hint Constructors step_prim.


Inductive step : exp -> exp -> Prop :=
| Step : forall C e1 e2 e1' e2', plug C e1 e1' ->
                            plug C e2 e2' ->
                            step_prim e1 e2 ->
                            step e1' e2'.

Hint Constructors step.

Inductive multi A (R : A -> A -> Prop) : A -> A -> Prop :=
| MultiRefl : forall x,
  multi R x x
| MultiStep : forall x1 x2 x3,
  R x1 x2
  -> multi R x2 x3
  -> multi R x1 x3.

Hint Constructors multi.

Lemma multi_trans {A} : forall (R : A -> A -> Prop) a b c,
                      multi R a b ->
                      multi R b c ->
                      multi R a c.
Proof.
  intros.
  induction H; iauto.
Qed.

(**************************************)
(******* 5. LOGICAL RELATION **********)
(**************************************)

(** We define the primary relation, which due to
    positivity restrictions is a fixpoint rather than
    an inductive type, and also what it means for a
    substitution to contain values in the relation.
*)

Definition halts  (e:exp) : Prop :=
  exists e', multi step e e' /\  value e'.

Fixpoint SN (T : ty) (t : exp) : Prop :=
  (nil |-- t T) /\ halts t /\
  (match T with
     | Bool => True
     | Fun T1 T2 => forall s, SN T1 s -> SN T2 (App t s)
     | Product T1 T2 => True
   end).

Reserved Notation "Γ '|=' Σ" (at level 40).

Inductive fulfills : tyenv -> venv -> Prop :=
| FNil : fulfills nil nil
| FCons : forall x t e Γ Σ,
            SN t e ->
            fulfills Γ Σ ->
            fulfills (cons (x,t) Γ) (cons (x,e) Σ)
where "Γ '|=' Σ" := (fulfills Γ Σ).

Hint Constructors fulfills.
Hint Extern 5 (_ |= _) => eapply FCons.
(* NOTE(dbp 2017-03-25): If there is an extend (for example) that needs to be
unfolded, the constructor won't match directly, so we try to use it anyway. *)

(**************************************)
(******** 6. MISC. PROPERTIES *********)
(**************************************)

(** This section contains a bunch of intermediate results
    about substition, evaluation contexts, etc.

    These mostly correspond to properties that are
    ellided in paper proofs, or at least, defined as
    proceeding by "straightforward induction on X".

    On first reading, you should probaby skip this
    section, proceeding either to the next section,
    which covers more interesting properties of the
    language (preservation, determinism, anti-reduction),
    etc, or probably skip right to the section titled
    "COMPATIBILITY LEMMAS", as those are the lemmas
    that are motivate all the other intermediate results.
 *)

Ltac plug_invert :=
  try repeat
      match goal with
        |[H : plug CHole _ _ |- _ ] => invert H
        |[H : plug (CApp1 _ _) _ _ |- _ ] => invert H
        |[H : plug (CApp2 _ _) _ _ |- _ ] => invert H
        |[H : plug (CIf _ _ _) _ _ |- _ ] => invert H
        |[H : plug (CPair1 _ _) _ _ |- _ ] => invert H
        |[H : plug (CPair2 _ _) _ _ |- _ ] => invert H
      end.

Ltac use_ih_tac :=
  match goal with
    |[IH : forall x, _ -> ?P x = ?Q x,
        H: ?P ?x = ?y
        |- ?Q ?x = ?y] => rewrite <- (IH x)
    |[IH : forall x, _ -> ?Q x = ?P x,
        H: ?P ?x = ?y
        |- ?Q ?x = ?y] => rewrite (IH x)
    |[IH : forall x y z, ?P x y -> ?Q x z -> y = z,
        H1 : ?P ?x ?y,
        H2 : ?Q ?x ?z
        |- _] => rewrite (IH x y z H1 H2)
    |[IH : forall x, (forall _, _ -> _) -> ?P x _ _ |- ?P ?x _ _] =>
     eapply (IH x)
    |[IH : forall a b, _ -> ?P b ?x a |- ?P ?b ?x ?a] =>
     eapply IH
  end.

Lemma plug_same : forall C x e1 e2,
                    plug C x e1 ->
                    plug C x e2 ->
                    e1 = e2.
Proof.
  intro C.
  induction C;
    intros;
    plug_invert;
    crush;
    use_ih_tac;
    crush.
Qed.

Lemma plug_exists : forall C e e' e1,
                      plug C e e' ->
                      multi step e e1 ->
                      exists e1', plug C e1 e1'.
Proof.
  intro C.
  induction C; intros;
  plug_invert;
  try match goal with
        |[H : plug C _ _ |- _ ] =>
         eapply IHC in H; iauto; inversion H
      end.

  solve [exists e1; iauto].
  solve [exists (App x e); iauto].
  solve [exists (App e x); iauto].
  solve [exists (If x e e0); iauto].
  solve [exists (Pair x e); iauto].
  solve [exists (Pair e x); iauto].
Qed.

Lemma plug_compose : forall C C' e e' e'',
                       plug C e e' ->
                       plug C' e' e'' ->
                       (exists C'', forall e1 e2 e3,
                                 plug C e1 e2 ->
                                 plug C' e2 e3 ->
                                 plug C'' e1 e3).
Proof.
  induction 2;
  try match goal with
    |[IH : context[_:?P -> _],
          H : ?P |- _] => apply IH in H; inversion H
      end;
  [  exists C
   | exists (CApp1 x e2)
   | exists (CApp2 v x)
   | exists (CIf x e2 e3)
   | exists (CPair1 x e2)
   | exists (CPair2 v x)
  ]; intros; plug_invert; iauto.
Qed.

Lemma step_context : forall C e1 e2,
                        step e1 e2 ->
                        forall e1' e2',
                        plug C e1 e1' ->
                        plug C e2 e2' ->
                        step e1' e2'.
Proof.
  intros.
  inversion H; subst.
  destruct (plug_compose H2 H0).
  iauto'.
Qed.

Lemma multi_context : forall C e1 e2,
                        multi step e1 e2 ->
                        forall e1' e2',
                        plug C e1 e1' ->
                        plug C e2 e2' ->
                        multi step e1' e2'.
Proof.
  hint plug_exists.
  hint step_context.
  intros C e1 e2 H.
  induction H; intros.
  rewrite (plug_same H H0); iauto.
  assert (exists ex2, plug C x2 ex2). iauto.
  crush.
  assert (H5: step e1' x); iauto.
Qed.



Lemma close_const : forall Σ b, close Σ (Const b) = (Const b).
Proof.
  intros.
  induction Σ; iauto.
Qed.

Lemma halts_value : forall v, value v -> halts v.
Proof.
  intros. exists v. iauto.
Qed.

Lemma sn_halts : forall t e, SN t e -> halts e.
Proof.
  intros. destruct t; crush.
Qed.

Lemma string_dec_refl : forall T s (t:T) (f:T), (if string_dec s s then t else f) = t.
Proof.
  intros.
  destruct (string_dec s s). eauto. exfalso. eauto.
Qed.

Lemma string_dec_ne : forall T s s' (t:T) (f:T), s <> s' -> (if string_dec s s' then t else f) = f.
Proof.
  intros.
  destruct (string_dec s s'). subst. contradiction H. eauto. reflexivity.
Qed.

Ltac destruct_tac :=
  match goal with
    |[ H : context[string_dec ?x ?y] |- _ ] =>
     destruct (string_dec x y); try subst
    |[ H : _ |- context[string_dec ?x ?y] ] =>
     destruct (string_dec x y); try subst
    |[ a : _ * _ |- _] => destruct a
  end.

Lemma lookup_fulfill_v : forall (Γ:tyenv) (Σ:venv),
                           Γ |= Σ ->
                           forall x (t:ty),
                             lookup Γ x = Some t ->
                             exists v, lookup Σ x = Some v.
Proof.
  Hint Extern 1 => destruct_tac.
  intros Γ Σ H.
  induction H; intros;
  simpl in *; iauto'; crush.
Qed.


Lemma sub_closed : forall x e, ~ free_in x e ->
                          forall e', [x:=e']e = e.
Proof.
  intros.
  induction e; simpl;
  try solve [intuition (eauto; crush)];
  destruct_tac; crush.
Qed.

Lemma close_closed : forall Σ e, closed e -> close Σ e = e.
Proof.
  hint_rewrite sub_closed.
  unfold closed in *;
  intro Σ.
  induction Σ; crush; iauto'.
Qed.

Lemma close_var : forall Σ x e, closed_env Σ ->
                           lookup Σ x = Some e ->
                           close Σ (Var x) = e.
Proof.
  hint close_closed.
  intros.
  induction Σ; crush; repeat destruct_tac; crush.
Qed.

Lemma lookup_fulfill_sn : forall Γ Σ,
                            Γ |= Σ ->
                            forall t x v,
                              lookup Γ x = Some t ->
                              lookup Σ x = Some v ->
                              SN t v.
Proof.
  intros Γ Σ H.
  induction H; intros; [crush|idtac].
  simpl in *; destruct_tac; iauto; crush.
Qed.

Lemma lookup_drop : forall (Γ : list (string * ty)) x y,
                      x <> y ->
                      lookup (drop x Γ) y = lookup Γ y.
Proof.
  hint_rewrite string_dec_ne.
  hint_rewrite string_dec_refl.
  intros.
  induction Γ; simpl in *; repeat destruct_tac; crush.
Qed.

Lemma free_in_context : forall x e t Γ,
                          free_in x e ->
                          Γ |-- e t ->
                              exists t', lookup Γ x = Some t'.
Proof.
  hint_rewrite string_dec_ne.
  hint_rewrite string_dec_refl.

  intros.
  induction H0; free_invert; crush; iauto'.

  rewrite lookup_drop in *; iauto'.
Qed.

Lemma typable_empty_closed : forall e t, nil |-- e t -> closed e.
Proof.
  unfold closed. unfold not. intros.
  destruct (free_in_context H0 H). crush.
Qed.

Lemma sn_typable_empty : forall e t, SN t e -> nil |-- e t.
Proof.
  intros.
  destruct t; crush.
Qed.

Lemma sn_closed : forall t e, SN t e -> closed e.
Proof.
  hint typable_empty_closed.
  hint sn_typable_empty.
  intros. iauto.
Qed.

Lemma fulfill_closed : forall Γ Σ, Γ |= Σ -> closed_env Σ.
Proof.
  hint typable_empty_closed.
  hint sn_typable_empty.
  
  intros.
  induction H; simpl; iauto.
Qed.



Lemma close_abs : forall Σ x t e, close Σ (Abs x t e) =
                             Abs x t (close (drop x Σ) e).
Proof.
  induction Σ; intros; simpl;
  repeat destruct_tac; crush.
Qed.

Lemma context_invariance : forall Γ Γ' e t,
     Γ |-- e t  ->
     (forall x, free_in x e -> lookup Γ x = lookup Γ' x)  ->
     Γ' |-- e t.
Proof.
  intros.
  generalize dependent Γ'.
  induction H; intros; crush;
  try solve [econstructor; use_ih_tac; crush].

  econstructor; use_ih_tac. intros.
  simpl in *. destruct_tac; crush.
  rewrite lookup_drop; iauto.
  rewrite lookup_drop; iauto.
Qed.

Lemma free_closed : forall x v t, (nil |-- v t) ->
                             free_in x v -> False.
Proof.
  intros; destruct (free_in_context H0 H); crush.
Qed.

Ltac has_type_invert :=
  match goal with
    |[HT : (_ |-- _) _ |- _] => inversion HT; clear HT
  end.

Lemma substitution_preserves_typing : forall Γ x t v e t',
     (extend Γ x t') |-- e t  ->
     nil |-- v t'   ->
     Γ |-- ([x:=v]e) t.
Proof.
  hint free_closed.
  hint_rewrite string_dec_ne.
  hint_rewrite string_dec_refl.
  intros.
  generalize dependent Γ.
  generalize dependent t.
  induction e;
    intros; simpl; inversion H; subst;
    try solve[econstructor; iauto];
    try solve[crush; destruct_tac; iauto].

  (* var *)
  simpl in *. destruct_tac; crush.
  eapply context_invariance with (Γ := nil); iauto.
  intros.
  exfalso; iauto.

  (* abs *)
  simpl in *.
  destruct_tac; iauto.
  (* <> *)
  econstructor.
  use_ih_tac.
  eapply context_invariance; iauto.
  intros. simpl. destruct_tac; crush.
Qed.

Lemma sn_types : forall t e, SN t e -> nil |-- e t.
Proof.
  hint sn_typable_empty.

  intros.
  destruct t; iauto.
Qed.


Lemma close_preserves : forall Γ Σ, Γ |= Σ ->
                        forall G e t,
                          (mextend G Γ) |-- e t ->
                          G |-- (close Σ e) t.
Proof.
  hint sn_typable_empty.
  hint substitution_preserves_typing.
  induction 1; intros;
  simpl in *; iauto'.
Qed.

Lemma fulfills_drop : forall Γ Σ,
    Γ |= Σ ->
    forall x, (drop x Γ) |= (drop x Σ).
Proof.
  intros c e V. induction V; intros;
                simpl; try destruct_tac; crush.
Qed.

Lemma extend_drop : forall {T:Set}
                      (Γ : list (string * T))
                      (Γ' : list (string * T)) x x',
  lookup (mextend Γ' (drop x' Γ)) x
  = if string_dec x x'
    then lookup Γ' x
    else lookup (mextend Γ' Γ) x.
Proof.
  intros. induction Γ; simpl in *; destruct_tac;
          repeat (simpl;
                  repeat destruct_tac;
                  repeat iauto).
Qed.

Lemma extend_drop'' : forall Γ x t t' e,
                        (extend (drop x Γ) x t) |-- e t' ->
                        (extend Γ x t) |-- e t'.
Proof.
  hint lookup_drop.
  intros.
  eapply context_invariance; iauto;
  intros;
  free_invert; has_type_invert;
  simpl; destruct_tac; crush.
Qed.

Lemma lookup_same : forall Γ x (t:ty) (t':ty),
                      lookup x Γ = Some t ->
                      lookup x Γ = Some t' ->
                      t = t'.
Proof.
  intros. rewrite H in H0. crush.
Qed.

Lemma typed_hole : forall C e e' t,
                     nil |-- e t ->
                     plug C e' e ->
                     exists t', nil |-- e' t'.
Proof.
  intros.
  generalize dependent t.
  induction H0; intros;
  plug_invert; has_type_invert;
  iauto.
Qed.

Ltac step_invert :=
  match goal with
    |[H : step _ _ |- _] => invert H
  end.

Ltac value_invert :=
  match goal with
    |[H : value _ |- _] => invert H
  end.

Lemma plug_values : forall e v C, plug C e v ->
                             value v ->
                             value e.
Proof.
  intros.
  induction H; inversion H0; iauto.
Qed.

Lemma multi_subst : forall x v1 v2 e,
                      closed v1 -> closed v2 ->
                      [x:=v1]([x:=v2]e) = [x:=v2]e.
Proof.
  intros.
  induction e; iauto; try solve[crush];
  simpl; destruct_tac; iauto; simpl;
  try match goal with
    |[H: closed ?v |- [_ := _]?v = ?v] =>
     rewrite sub_closed; unfold closed in H; iauto
  end;
  destruct_tac; iauto; crush.
Qed.

Ltac closed_tac :=
  match goal with
    |[H: closed ?v |- [_ := _]?v = ?v] =>
     rewrite sub_closed; unfold closed in H; iauto
    |[H: closed ?v |- ?v = [_ := _]?v] =>
     rewrite sub_closed; unfold closed in H; iauto
  end.

Lemma swap_sub : forall x1 x2 v1 v2 e,
                   x1 <> x2 ->
                   closed v1 ->
                   closed v2 ->
                   [x1:=v1]([x2:=v2]e) = [x2:=v2]([x1:=v1]e).
Proof.
  intros.
  induction e;
    simpl;
    repeat destruct_tac; simpl;
    repeat destruct_tac; iauto;
    try closed_tac; iauto;
    repeat destruct_tac; iauto;
    crush.
Qed.

Lemma sub_close: forall Σ x v e,
                      closed v ->
                      closed_env Σ ->
                      close Σ ([x:=v]e) = [x:=v](close (drop x Σ) e).
Proof.
  intro Σ.
  induction Σ; intros; simpl; repeat destruct_tac; iauto;
  repeat destruct_tac; simpl;
  try solve[rewrite multi_subst; iauto; crush];
  try solve[rewrite swap_sub; crush].
Qed.

Lemma multistep_App2 : forall v e e',
                         value v ->
                         multi step e e' ->
                         multi step (App v e) (App v e').
Proof.
  intros.
  eapply multi_context with (e1 := e) (e2 := e'); eauto.
Qed.

Lemma sub_close_extend :
  forall x v e Σ,
    closed v ->
    closed_env Σ ->
    [x:=v](close (drop x Σ) e) =
    close (extend (drop x Σ) x v) e.
Proof.
  intros.
  generalize dependent e.
  simpl.
  induction Σ; intros; iauto;
  destruct_tac;
  simpl; destruct_tac; simpl;
  try rewrite swap_sub; crush.
Qed.

Lemma drop_sub : forall Σ x v e,
                   closed v ->
                   closed_env Σ ->
                   close (drop x Σ) ([x:=v]e) =
                   close Σ ([x:=v]e).
Proof.
  intro Σ.
  induction Σ; intros;
  repeat destruct_tac; iauto; simpl; destruct_tac; simpl;
  try solve [rewrite multi_subst; crush];
  try solve [rewrite swap_sub; crush].
Qed.

Lemma extend_drop' : forall Σ (x:string) (v:exp) e,
                       closed_env Σ ->
                       closed v ->
                       close (extend (drop x Σ) x v) e
                       = close (cons (x,v) Σ) e.
Proof.
  induction Σ; intros; iauto; destruct_tac; simpl;
  destruct_tac; simpl;
  [rewrite drop_sub; iauto;
   try solve [rewrite multi_subst; iauto; crush];
   crush
  |rewrite swap_sub; crush].
Qed.

Lemma lookup_mextend : forall (Γ : list (string * ty)) x x0 t,
                        x <> x0 ->
                        lookup ((x, t) :: Γ) x0 =
                        lookup (mextend (cons (x, t) nil) Γ) x0.
Proof.
  intros.
  simpl.
  destruct_tac; iauto.
  induction Γ; try solve [crush];
  repeat (simpl; destruct_tac; iauto).
Qed.


Lemma close_app : forall Σ e1 e2,
                    close Σ (App e1 e2) =
                    App (close Σ e1) (close Σ e2).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

Lemma close_if : forall Σ e1 e2 e3,
                    close Σ (If e1 e2 e3) =
                    If (close Σ e1) (close Σ e2) (close Σ e3).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

Lemma drop_fulfills : forall Γ Σ x,
                        Γ |= Σ ->
                        drop x Γ |= drop x Σ.
Proof.
  hint fulfills_drop.
  intros.
  induction H; iauto.
Qed.

Lemma close_pair : forall Σ e1 e2,
                    close Σ (Pair e1 e2) =
                    Pair (close Σ e1) (close Σ e2).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

(**************************************)
(**** 7. ANTI-REDUCTION/DETERMINISM ***)
(**************************************)

(** This section contains interesting results about
    the language - primarily, preservation of types (that
    if a well-typed term steps to another term which is
    well typed, at the same type) and also of halting
    (that if a term halts, anything it steps to will
    halt as well), anti-reduction (that if a term
    is well typed and steps to a term that is
    in the logical relation, then the original term
    must have been as well, determinism (that if two
    terms step, they must step to the same term).

    We also show that any well typed term has a unique
    type (which, interesting, is what requires that we
    provide a type binder on Abs), which is needed for
    the type preservation result.

    Of these, the result that perhaps seems the least
    necessary is determinism. But we need it to show
    preservation of halting, as we argue that the
    steps that allows a term e to halt must include
    the term e', and thus e' will halt as well. It's
    likely the result could work without determinism,
    but the definition of halting would probably need
    to change, and since STLC is deterministic, it's a
    reasonable property to check.
*)


Ltac step_prim_invert :=
  match goal with
    |[S : step_prim _ _ |- _] => invert S
  end.

Lemma preservation_prim_step : forall e1 e2 t,
                                 nil |-- e1 t ->
                                 step_prim e1 e2 ->
                                 nil |-- e2 t.
Proof.
  intros.
  step_prim_invert; subst; iauto;
  has_type_invert; subst; iauto;
  eapply substitution_preserves_typing; iauto;
  match goal with
    |[H: (nil |-- _) (Fun _ _) |- _] => inversion H
  end;
  subst; iauto.
Qed.


Lemma unique_typing : forall e Γ t t',
                        Γ |-- e t ->
                        Γ |-- e t' ->
                        t = t'.
Proof.
  hint lookup_same.
  intro e.
  induction e; intros; iauto;
  inversion H; inversion H0; iauto;
  try (apply f_equal); try (apply f_equal2); iauto.

  (* app *)
  assert (EQ : (Fun t1 t) = (Fun t0 t')). iauto.
  inversion EQ; iauto.
Qed.

Lemma preservation_plug : forall C e1 e2 e1' e2' t t',
                            nil |-- e1' t ->
                            nil |-- e1 t' ->
                            nil |-- e2 t' ->
                            plug C e1 e1' ->
                            plug C e2 e2' ->
                            nil |-- e2' t.
Proof.
  intro C.
  induction C; intros; plug_invert;
  iauto; try solve
             [inversion H; subst;
              econstructor;
              iauto].

  (* hole *)
  assert (t = t').
  eapply unique_typing; iauto.
  subst; iauto.
Qed.

Lemma preservation_step : forall e1 e2 t, nil |-- e1 t ->
                                     step e1 e2 ->
                                     nil |-- e2 t.
Proof.
  hint preservation_plug.
  hint preservation_prim_step.
  intros.
  inversion H0; subst.
  match goal with
    |[H1: (_ |-- ?e) _, H2: plug C _ ?e |- _] =>
     destruct (typed_hole H1 H2)
  end;
  iauto.
Qed.

Lemma preservation : forall e1 e2 t, multi step e1 e2 ->
                                nil |-- e1 t ->
                                nil |-- e2 t.
Proof.
  hint preservation_step.
  intros.
  induction H; iauto.
Qed.


Lemma anti_reduct : forall e' e t, multi step e e' ->
                              SN t e' ->
                              nil |-- e t ->
                              SN t e.
Proof.
  hint sn_typable_empty.

  hint @multi_trans.
  intros.
  generalize dependent e.
  generalize dependent e'.
  induction t; intros; unfold SN; crush;
  try solve[match goal with
              |[H: halts _ |- halts _] => invert H
            end;
             crush;
             unfold halts;
             exists x; iauto];
  fold SN in *; intros;
  eapply IHt2; iauto;
  eapply multi_context with (C := CApp1 CHole s);
  iauto.
Qed.

Lemma values_dont_step : forall v e, value v -> ~step v e.
Proof.
  hint plug_values.
  unfold not. intros. step_invert; value_invert;
  match goal with
    |[H: plug _ _ (Const _) |- _] => invert H
    |[H: plug _ _ (Abs _ _ _) |- _] => invert H
    |[H: plug _ _ (Pair _ _) |- _] => invert H
  end; subst; try (assert (value e1) by iauto;
                   inversion H;
                   subst);
  step_prim_invert.
Qed.

Lemma step_prim_deterministic : forall e1 e2 e2',
                                  step_prim e1 e2 ->
                                  step_prim e1 e2' ->
                                  e2 = e2'.
Proof.
  intros. repeat step_prim_invert; iauto.
Qed.

Ltac smash :=
  repeat try match goal with
               |[H: plug _ ?e ?v,
                    H1: value ?v,
                        H2: step_prim ?e _ |- _] =>
                assert (value e) by (eapply plug_values;
                                     iauto);
                  exfalso; eapply values_dont_step; iauto
               |[H : App _ _ = App _ _ |- _] => invert H
               |[H : If _ _ _ = If _ _ _ |- _] => invert H
               |[H : Pair _ _ = Pair _ _ |- _] => invert H
               |[H : plug _ _ _ |- _] => invert H; []
               |[H : plug _ _ ?v, H1 : value ?v |- _] => invert H
               |[H : step_prim _ _ |- _] => invert H
               |[H : value (App _ _) |- _] => invert H
               |[H : value (If _ _ _) |- _] => invert H
               |[H : If _ _ _ = App _ _ |- _] => invert H
               |[H : App _ _ = If _ _ _ |- _] => invert H
               |[H : If _ _ _ = Pair _ _ |- _] => invert H
               |[H : App _ _ = Pair _ _ |- _] => invert H
               |[H : Pair _ _ = If _ _ _ |- _] => invert H
               |[H : Pair _ _ = App _ _ |- _] => invert H
             end.

Lemma plug_step_uniq : forall C e e1 e2,
                         plug C e1 e ->
                         step_prim e1 e2 ->
                         forall C' e1' e2',
                           plug C' e1' e ->
                           step_prim e1' e2' ->
                           C = C' /\ e1' = e1.
Proof.
  intros C e e1 e2 H H0.
  induction H; intros;
  try match goal with
        |[H1: step_prim ?e _, H2: plug _ _ ?e |- _] =>
         invert H1; invert H2; iauto; smash
      end;
  try match goal with
    |[H: value (Pair ?e _), H1: plug _ _ ?e |- _] =>
     invert H; eapply plug_values in H1; invert H1; iauto
    |[H: value (Pair _ ?e), H1: plug _ _ ?e |- _] =>
     invert H; eapply plug_values in H1; invert H1; iauto
  end;
  match goal with
    |[H: plug _ _ (App _ _) |- _] =>
     invert H; try solve [smash]
    |[H: plug _ _ (If _ _ _) |- _] =>
     invert H; try solve [smash]
    |[H: plug _ _ (Pair _ _) |- _] =>
     invert H; try solve [smash]
  end;
  match goal with
    |[H: _ -> forall C _ _, _ -> _ -> ?C0 = C /\ _ |-
       (CApp1 ?C0 ?e0 = CApp1 ?C1 ?e0 /\ ?P)] =>
     assert (C0 = C1 /\ P) by (eapply H; eauto); crush
    |[H: _ -> forall C _ _, _ -> _ -> ?C0 = C /\ _ |-
       (CApp2 ?v0 ?C0 = CApp2 ?v0 ?C1 /\ ?P)] =>
     assert (C0 = C1 /\ P) by (eapply H; eauto); crush
    |[H: _ -> forall C _ _, _ -> _ -> ?C0 = C /\ _ |-
                      (CIf ?C0 _ _ = CIf ?C1 _ _ /\ ?P)] =>
     assert (C0 = C1 /\ P) by (eapply H; eauto); crush
    |[H: _ -> forall C _ _, _ -> _ -> ?C0 = C /\ _ |-
       (CPair1 ?C0 ?e0 = CPair1 ?C1 ?e0 /\ ?P)] =>
     assert (C0 = C1 /\ P) by (eapply H; eauto); crush
    |[H: _ -> forall C _ _, _ -> _ -> ?C0 = C /\ _ |-
       (CPair2 ?v0 ?C0 = CPair2 ?v0 ?C1 /\ ?P)] =>
     assert (C0 = C1 /\ P) by (eapply H; eauto); crush
  end.
Qed.

Lemma step_deterministic : forall e1 e2 e2',
                             step e1 e2 ->
                             step e1 e2' ->
                             e2 = e2'.
Proof.
  induction 1; intros.
  step_invert.
  destruct (plug_step_uniq H H1 H3 H5); subst.
  assert (e2 = e3).
  apply (step_prim_deterministic H1 H5).
  subst.
  destruct (plug_same H4 H0); eauto.
Qed.

Lemma step_preserves_halting : forall e e',
                                 step e e' ->
                                 (halts e <-> halts e').
Proof.
  hint step_deterministic.
  intros. unfold halts.
  split; intros; crush;
  try solve[exists x; iauto].
  match goal with
    |[H: multi step _ _ |- _] => invert H; subst
  end;
  try solve[exfalso; eapply values_dont_step; iauto];
  match goal with
    |[H: value ?x |- _] => exists x; iauto
  end;
  match goal with
    |[H1: multi step ?a _, H2: step ?e ?a,
      H3: step ?e ?b |- multi step ?b _ /\ value _] =>
     assert (a = b) by iauto; subst; iauto
  end.
Qed.

Lemma step_preserves_sn : forall t e e',
                            step e e' ->
                            SN t e ->
                            SN t e'.
Proof.
  hint step_context.
  hint preservation_step.

  induction t; intros e e' H H0; crush; iauto;
  try match goal with
        |[_: halts ?e, _: step ?e ?e' |- halts ?e'] =>
         eapply step_preserves_halting with (e:=e); iauto
      end;
  match goal with
    |[H: forall _ _, _ -> SN ?t _ -> _ |- SN ?t _] => eapply H
  end; iauto'.
Qed.

Lemma multistep_preserves_sn : forall t e e',
                                 multi step e e' ->
                                 SN t e ->
                                 SN t e'.
Proof.
  hint step_preserves_sn.
  intros.
  induction H; iauto.
Qed.


(**************************************)
(****** 8. COMPATIBILITY LEMMAS *******)
(**************************************)

(** This section contains the primary results,
    which show for each term in the language, if
    it is well typed then it is in the logical
    relation.

    The most interesting one is certainly TAbs,
    which proceeds primarily by appealing to
    anti-reduction, but TIf has it's own trick,
    because in order to show that it halts, we have
    to step it to the intermediate term where the head
    position is a (Const b) value, and then handle each
    case separately by appealing to the corresponding
    hypothesis for the then or else branches.
*)


Lemma TConst_compat : forall Γ Σ b,
                        Γ |= Σ ->
                        SN Bool (close Σ (Const b)).
Proof.
  hint close_const.
  hint halts_value.
  crush.
Qed.

Lemma TVar_compat : forall Γ Σ x t,
                      Γ |= Σ ->
                      lookup Γ x = Some t ->
                      SN t (close Σ (Var x)).
Proof.
  hint lookup_fulfill_sn.
  hint fulfill_closed.
  intros.
  destruct (lookup_fulfill_v H x H0); iauto.
  rewrite close_var with (e := x0); iauto.
Qed.

Lemma TAbs_typing : forall Γ Σ x e t t',
                      Γ |= Σ ->
                      (extend (drop x Γ) x t) |-- e t' ->
                      nil |-- (Abs x t (close (drop x Σ) e)) (Fun t t').
Proof.
  hint lookup_drop.
  hint_rewrite string_dec_ne.
  hint_rewrite string_dec_refl.

  intros.
  econstructor. eapply close_preserves.
  eapply fulfills_drop. iauto.
  eapply context_invariance. iauto.
  intros. simpl. rewrite extend_drop.
  repeat destruct_tac. simpl. crush. iauto.
  iauto. unfold extend. rewrite <- lookup_mextend.
  simpl. destruct_tac; iauto. iauto.
Qed.

Lemma TAbs_app : forall x t Σ e xh,
                   value xh ->
                   closed xh ->
                   closed_env Σ ->
                   multi step (App (Abs x t (close (drop x Σ) e)) xh)
                         (close (extend (drop x Σ) x xh) e).
Proof.
  hint_rewrite sub_close_extend.

  intros; iauto'.
Qed.

Lemma TAbs_compat : forall Γ Σ x e t t',
                      Γ |= Σ ->
                      (extend (drop x Γ) x t) |-- e t' ->
                      (forall v, SN t v -> SN t' (close (extend (drop x Σ) x v) e)) ->
                      SN (Fun t t') (close Σ (Abs x t e)).
Proof.
  hint_rewrite close_abs.
  hint TAbs_typing.
  hint lookup_fulfill_sn.
  hint fulfill_closed.
  hint TAbs_app.
  hint halts_value.
  hint sn_typable_empty.
  hint @multi_trans.
  intros.
  crush; iauto.

  assert (HH: halts s) by (hint sn_halts; iauto).
  inversion HH as [xh MS]. crush.
  assert (SN t xh) by (eapply multistep_preserves_sn; iauto).
  assert (closed xh) by (eapply sn_closed; iauto).


  eapply anti_reduct with (e' := close (extend (drop x Σ) x xh) e); try solve [crush]; try solve [iauto'].
  eapply multi_trans with (b := (App (Abs x t (close (drop x Σ) e)) xh)); iauto';
  eapply multi_context with (e1 := s) (e2 := xh); iauto'.
Qed.

Lemma TApp_compat : forall Γ Σ e1 e2 t t',
                      Γ |= Σ ->
                      SN (Fun t t') (close Σ e1) ->
                      SN t (close Σ e2) ->
                      SN t' (close Σ (App e1 e2)).
Proof.
  hint_rewrite close_app.
  intros; crush.
Qed.

Ltac branch boo e ife :=
    eapply anti_reduct with (e' := e); crush;
    eapply multi_trans with (b := ife);
    iauto;
    eapply multi_context; iauto.

Lemma TIf_compat : forall Γ Σ e1 e2 e3 t,
                      Γ |= Σ ->
                      SN Bool (close Σ e1) ->
                      SN t (close Σ e2) ->
                      SN t (close Σ e3) ->
                      SN t (close Σ (If e1 e2 e3)).
Proof.
  hint sn_typable_empty.
  hint preservation.
  hint_rewrite close_if.
  intros; crush;
  match goal with
    |[H : (_ |-- ?e) Bool, H1 : halts ?e |- _] =>
     invert H1
  end;
  crush;
  match goal with
    |[H0: value ?x, H1: multi step _ ?x |- _] =>
     assert (nil |-- x Bool) by iauto;
       destruct x; iauto; try solve [inversion H0]
  end;
  try (match goal with
         |[H : value (Const ?b) |- _] =>
          destruct b
       end;
       match goal with
         |[H: value (Const true) |- SN _ (If _ ?e ?n)] =>
          branch true e (If (Const true) e n)
         |[H: value (Const false) |- SN _ (If _ ?n ?e)] =>
          branch false e (If (Const false) n e)
       end);
  match goal with
    |[H: (nil |-- (Abs _ _ _)) Bool |- _] => invert H
    |[H: (nil |-- (Pair _ _)) Bool |- _] => invert H
  end.
Qed.

Lemma TPair_compat : forall Γ Σ e1 e2 t1 t2,
                      Γ |= Σ ->
                      SN t1 (close Σ e1) ->
                      SN t2 (close Σ e2) ->
                      SN (Product t1 t2)
                         (close Σ (Pair e1 e2)).
Proof.
  hint sn_typable_empty.
  hint_rewrite close_pair.
  intros.

  crush; 
  repeat match goal with
           |[H: SN _ _ |- _] =>
            eapply sn_halts in H; invert H
         end;
  crush;
  match goal with
    |[H1: multi step ?e1 ?v1,
          H2: multi step ?e2 ?v2 |-
      halts (Pair ?e1 ?e2)] => eexists (Pair v1 v2)
  end;
  crush;
  eapply multi_trans with (b := (Pair x0 (close Σ e2)));
  match goal with
    |[H: multi step ?e ?v |-
      multi step (Pair ?e _) (Pair ?v _)] =>
     eapply (multi_context H); iauto
    |[H: multi step ?e ?v |-
      multi step (Pair _ ?e) (Pair _ ?v)] =>
     eapply (multi_context H); iauto
  end.
Qed.


(**************************************)
(****** 9. FUNDAMENTAL THEOREM ********)
(**************************************)

(** The fundamental theorem simply states that
    a well-typed open term, when closed with a
    substitution that contains values that are
    in the logical relation, will be in the logical
    relation.

    We can then apply that (trivially) to an empty
    environment to get that any closed term halts.
*)

Theorem fundamental : forall e t Γ Σ,
                        Γ |-- e t ->
                            Γ |= Σ ->
                            SN t (close Σ e).
Proof.
  hint TConst_compat.
  hint TVar_compat.
  hint TAbs_compat.
  hint TApp_compat.
  hint TIf_compat.
  hint TPair_compat.
  hint fulfills_drop.
  intros.
  generalize dependent Σ.
  induction H; intros; iauto'.
Qed.

Theorem strong_normalization : forall e t,
                                 nil |-- e t ->
                                 halts e.
Proof.
  hint fundamental.
  hint sn_halts.
  intros.
  assert (SN t (close nil e)); iauto.
Qed.
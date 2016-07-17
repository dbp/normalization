Require Import Coq.Unicode.Utf8 Arith FunctionalExtensionality String Coq.Program.Equality.

Set Implicit Arguments.

Ltac iauto := try solve [intuition (eauto 3)].

Ltac iauton n := try solve [intuition (eauto n)].

Inductive ty  : Set :=
| Bool : ty
| Fun : ty -> ty -> ty.

Inductive exp : Set :=
| Var : string -> exp
| Const : bool -> exp
| Abs : string -> ty -> exp -> exp
| App : exp -> exp -> exp
| If : exp -> exp -> exp -> exp.

Inductive value : exp -> Prop :=
| VBool : forall b, value (Const b)
| VAbs : forall x t e, value (Abs x t e).

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
where "Γ '|--' e" := (has_type Γ e).

Hint Constructors has_type ty exp value.


Inductive context : Set :=
| CHole : context
| CApp1 : context -> exp -> context
| CApp2 : exp -> context -> context
| CIf : context -> exp -> exp -> context.

Hint Constructors context.

Inductive plug : context -> exp -> exp -> Prop :=
| PHole : forall e, plug CHole e e
| PApp1 : forall e e' C e2, plug C e e' ->
                       plug (CApp1 C e2) e (App e' e2)
| PApp2 : forall e e' C v, plug C e e' ->
                       value v ->
                       plug (CApp2 v C) e (App v e')
| PIf : forall e e' C e2 e3, plug C e e' ->
                        plug (CIf C e2 e3) e (If e' e2 e3).

Hint Constructors plug.

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
    end.

Notation "'[' x ':=' s ']' t" := (sub x t s) (at level 20).


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


Ltac use_plug_tac :=
  try repeat
      match goal with
        |[H : plug CHole _ _ |- _ ] => inversion H; clear H; subst
        |[H : plug (CApp1 _ _) _ _ |- _ ] => inversion H; clear H; subst
        |[H : plug (CApp2 _ _) _ _ |- _ ] => inversion H; clear H; subst
        |[H : plug (CIf _ _ _) _ _ |- _ ] => inversion H; clear H; subst
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

Ltac use_ex_tac :=
  match goal with
    |[H : exists _, _ |- _] => destruct H
    |[H : _ -> exists _, _ |- _] => destruct H
  end; eauto.


Lemma plug_same : forall C x e1 e2,
                    plug C x e1 ->
                    plug C x e2 ->
                    e1 = e2.
Proof.
  intro C.
  induction C; intros; use_plug_tac;
  try use_ih_tac; iauto.
Qed.

Hint Rewrite plug_same.

Lemma plug_exists : forall C e e' e1,
                      plug C e e' ->
                      multi step e e1 ->
                      exists e1', plug C e1 e1'.
Proof.
  intro C.
  induction C; intros;
  use_plug_tac;
  try match goal with
        |[H : plug C _ _ |- _ ] =>
         eapply IHC in H; iauto; inversion H
      end.

  solve [exists e1; iauto].
  solve [exists (App x e); iauto].
  solve [exists (App e x); iauto].
  solve [exists (If x e e0); iauto].
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
  ]; intros; use_plug_tac; iauto.
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
  iauto.
Qed.

Lemma multi_context : forall C e1 e2,
                        multi step e1 e2 ->
                        forall e1' e2',
                        plug C e1 e1' ->
                        plug C e2 e2' ->
                        multi step e1' e2'.
Proof.
  intros C e1 e2 H.
  induction H; intros.
  rewrite (plug_same H H0); iauto.

  assert (exists ex2, plug C x2 ex2).
  eapply (plug_exists H1); iauto.
  use_ex_tac.

  assert (H5: step e1' x); iauto.
  inversion H. subst. destruct (plug_compose H4 H1).
  iauto.
Qed.

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
                           free_in x (If e1 e2 e3).

Hint Constructors free_in.

Ltac use_free_tac :=
  match goal with
    |[H : free_in _ _ |- _] => inversion H; clear H; subst; iauto
  end.

Definition closed t := forall x, ~ free_in x t.

Fixpoint closed_env (e:venv) :=
  match e with
    | nil => True
    | cons (_,e1) en => closed e1 /\ closed_env en
  end.

Definition halts  (e:exp) : Prop :=  exists e', multi step e e' /\  value e'.

Fixpoint SN (T : ty) (t : exp) : Prop :=
  (nil |-- t T) /\ halts t /\
  (match T with
     | Bool => True
     | Fun T1 T2 => forall s, SN T1 s -> SN T2 (App t s)
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

Fixpoint close (Σ : venv) (e : exp) : exp :=
  match Σ with
    |nil => e
    |cons (x,v) Σ' => close Σ' ([x:=v]e)
  end.

Lemma close_const : forall Σ b, close Σ (Const b) = (Const b).
Proof.
  intros.
  induction Σ; iauto.
Qed.

Hint Rewrite close_const.

Ltac absurdities :=
  match goal with
    |[ H : lookup nil _ = Some _ |- _ ] => inversion H
    |[ H : None = Some _ |- _ ] => inversion H
    |[ H : Some _ = None |- _ ] => inversion H
  end; eauto.

Ltac general :=
  try absurdities;
  try repeat match goal with
        |[ x : _ * _ |- _ ] => destruct x
        |[ x : _ /\ _ |- _ ] => destruct x
        |[ x : Some _ = Some _ |- _ ] => inversion x; clear x
        |[ H : SN Bool _ |- _] => inversion H; clear H
        |[ H : SN (Fun _ _) _ |- _] => inversion H; clear H
  end; iauto.


Lemma halts_value : forall v, value v -> halts v.
Proof.
  intros. exists v. iauto.
Qed.

Lemma sn_halts : forall t e, SN t e -> halts e.
Proof.
  intros. destruct t; general.
Qed.

Hint Resolve halts_value sn_halts.


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

Ltac strings' x y :=
  destruct (string_dec x y);
  subst;
  eauto;
  simpl in *;
  eauto.


Ltac strings :=
  repeat (match goal with
            |[ H : context[string_dec ?x ?y] |- _ ] =>
             strings' x y
            |[ H : _ |- context[string_dec ?x ?y] ] =>
             strings' x y
          end; subst; eauto; simpl in *);
  intuition;
  autorewrite with core;
  intuition.


Hint Rewrite string_dec_ne string_dec_refl.


Lemma TConst_compat : forall Γ Σ b, Γ |= Σ ->
                               SN Bool (close Σ (Const b)).
Proof.
  intros. split;
    autorewrite with core; iauto.
Qed.


Lemma lookup_fulfill_v : forall (Γ:tyenv) (Σ:venv),
                           Γ |= Σ ->
                           forall x (t:ty),
                             lookup Γ x = Some t ->
                             exists v, lookup Σ x = Some v.
Proof.
  intros Γ Σ H.
  induction H; intros; general;
  simpl in *; strings.
Qed.


Lemma sub_closed : forall x e, ~ free_in x e ->
                          forall e', [x:=e']e = e.
Proof.
  intros.
  induction e; simpl; general; strings;
  repeat match goal with
    |[H : ?P = ?Q |- context[?P]] => rewrite H; clear H
  end; iauto.
Qed.

Hint Resolve sub_closed lookup_fulfill_v.

Lemma close_closed : forall Σ e, closed e -> close Σ e = e.
Proof.
  intro Σ.
  induction Σ; general; intros; simpl.
  assert (H1 : [s:=e]e0 = e0). iauto.
  rewrite H1. iauto.
Qed.

Hint Resolve close_closed.

Ltac string_hammer_tac :=
  repeat (simpl in *;
           general;
          strings;
          general;
          subst;
          general).

Lemma close_var : forall Σ x e, closed_env Σ ->
                           lookup Σ x = Some e ->
                           close Σ (Var x) = e.
Proof.
  intros.
  induction Σ; string_hammer_tac.
Qed.

Hint Resolve close_var.

Lemma lookup_fulfill_sn : forall Γ Σ,
                            Γ |= Σ ->
                            forall t x v,
                              lookup Γ x = Some t ->
                              lookup Σ x = Some v ->
                              SN t v.
Proof.
  intros Γ Σ H.
  induction H; intros; string_hammer_tac.
Qed.

Hint Resolve lookup_fulfill_sn.

Lemma lookup_drop : forall (Γ : list (string * ty)) x y,
                      x <> y ->
                      lookup (drop x Γ) y = lookup Γ y.
Proof.
  intros.
  induction Γ; string_hammer_tac.
Qed.

Hint Resolve lookup_drop.

Lemma free_in_context : forall x e t Γ,
                          free_in x e ->
                          Γ |-- e t ->
                              exists t', lookup Γ x = Some t'.
Proof.
  intros.
  induction H0;
    general;
    use_free_tac;
    use_ex_tac;
    simpl in *;
    strings.

  rewrite lookup_drop in *; iauto.
Qed.

Hint Resolve free_in_context.

Lemma typable_empty_closed : forall e t, nil |-- e t -> closed e.
Proof.
  unfold closed. unfold not. intros.
  destruct (free_in_context H0 H). absurdities.
Qed.

Hint Resolve typable_empty_closed.

Lemma sn_typable_empty : forall e t, SN t e -> nil |-- e t.
Proof.
  intros.
  destruct t; general.
Qed.

Hint Resolve sn_typable_empty.

Lemma sn_closed : forall t e, SN t e -> closed e.
Proof.
  intros. iauto.
Qed.

Hint Resolve sn_typable_empty.

Lemma fulfill_closed : forall Γ Σ, Γ |= Σ -> closed_env Σ.
Proof.
  intros.
  induction H; simpl; iauto.
Qed.


Hint Resolve fulfill_closed.

Lemma TVar_compat : forall Γ Σ x t, Γ |= Σ ->
                               lookup Γ x = Some t ->
                                   SN t (close Σ (Var x)).
Proof.
  intros.
  destruct (lookup_fulfill_v H x H0); iauto.
  rewrite close_var with (e := x0); iauto.
Qed.

Lemma close_abs : forall Σ x t e, close Σ (Abs x t e) =
                             Abs x t (close (drop x Σ) e).
Proof.
  induction Σ; intros; string_hammer_tac.
Qed.

Hint Rewrite close_abs.

Lemma context_invariance : forall Γ Γ' e t,
     Γ |-- e t  ->
     (forall x, free_in x e -> lookup Γ x = lookup Γ' x)  ->
     Γ' |-- e t.
Proof.
  intros.
  generalize dependent Γ'.
  induction H; intros; string_hammer_tac;
  econstructor; use_ih_tac; iauto.

  (* abs *)
  intros. strings.
  rewrite lookup_drop; iauto.
  rewrite lookup_drop; iauto.
Qed.

Ltac absurdities' :=
  match goal with
    |[H1 : (nil |-- ?v) _,
           H2 : free_in _ ?v |- _] =>
     destruct (free_in_context H2 H1)
  end; try absurdities.


Ltac use_has_type_tac :=
  match goal with
    |[HT : (_ |-- _) _ |- _] => inversion HT; clear HT
  end.

Lemma substitution_preserves_typing : forall Γ x t v e t',
     (extend Γ x t') |-- e t  ->
     nil |-- v t'   ->
     Γ |-- ([x:=v]e) t.
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent t.
  induction e;
    intros; simpl; inversion H; subst; iauto.

  (* val *)
  use_has_type_tac. simpl in *. strings. general. subst.
  eapply context_invariance with (Γ := nil); iauto.
  intros.
  absurdities'.

  (* abs *)
  simpl in *.
  strings.
  (* <> *)
  eapply TAbs.
  use_ih_tac.
  eapply context_invariance.
  iauto.
  intros. simpl. strings.
Qed.

Hint Resolve substitution_preserves_typing.

Lemma sn_types : forall t e, SN t e -> nil |-- e t.
Proof.
  intros.
  destruct t; iauto.
Qed.

Hint Resolve sn_types.


Lemma close_preserves : forall Γ Σ, Γ |= Σ ->
                        forall G e t,
                          (mextend G Γ) |-- e t ->
                          G |-- (close Σ e) t.
Proof.
  induction 1; intros;
  simpl in *; iauto.
Qed.

Hint Resolve close_preserves.

Lemma fulfills_drop : forall Γ Σ,
    Γ |= Σ ->
    forall x, (drop x Γ) |= (drop x Σ).
Proof.
  intros c e V. induction V; intros; simpl; strings.
Qed.

Hint Resolve fulfills_drop.

Lemma extend_drop : forall {T:Set}
                      (Γ : list (string * T))
                      (Γ' : list (string * T)) x x',
  lookup (mextend Γ' (drop x' Γ)) x
  = if string_dec x x'
    then lookup Γ' x
    else lookup (mextend Γ' Γ) x.
Proof.
  intros. induction Γ; general; simpl in *; strings.
Qed.

Lemma extend_drop'' : forall Γ x t t' e,
                        (extend (drop x Γ) x t) |-- e t' ->
                        (extend Γ x t) |-- e t'.
Proof.
  intros.
  eapply context_invariance; iauto.
  intros.
  use_free_tac; use_has_type_tac; simpl; strings.
Qed.

Ltac use_step_prim_tac :=
  match goal with
    |[S : step_prim _ _ |- _] => inversion S
  end.

Lemma preservation_prim_step : forall e1 e2 t,
                                 nil |-- e1 t ->
                                 step_prim e1 e2 ->
                                 nil |-- e2 t.
Proof.
  intros.
  use_step_prim_tac; subst; iauto;
  use_has_type_tac; subst; iauto.
  eapply substitution_preserves_typing; iauto.
  match goal with
    |[H: (nil |-- _) (Fun _ _) |- _] => inversion H
  end.
  subst; iauto.
Qed.

Lemma lookup_same : forall Γ x (t:ty) (t':ty),
                      lookup x Γ = Some t ->
                      lookup x Γ = Some t' ->
                      t = t'.
Proof.
  intros. rewrite H in H0. general.
Qed.

Hint Resolve lookup_same.

Lemma unique_typing : forall e Γ t t',
                        Γ |-- e t ->
                        Γ |-- e t' ->
                        t = t'.
Proof.
  intro e.
  induction e; intros; iauto; inversion H; inversion H0;
  subst; iauto.

  (* abs *)
  assert (EQ : t'0 = t'1). iauto. subst. iauto.
  (* app *)
  assert (EQ : (Fun t1 t) = (Fun t0 t')). iauto.
  inversion EQ. iauto.
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
  induction C; intros; use_plug_tac;
  iauto.

  (* hole *)
  assert (t = t').
  eapply unique_typing; iauto.
  subst; iauto.

  (* app1 *)
  inversion H; subst;
  econstructor.
  eapply IHC with (e1 := e1) (e2 := e2); iauto.
  iauto.

  (* app2 *)
  inversion H; subst;
  econstructor;
  iauto.

  (* if *)
  inversion H; subst.
  econstructor.
  eapply IHC with (e1 := e1) (e2 := e2); iauto.
  iauto.
  iauto.
Qed.

Lemma typed_hole : forall C e e' t,
                     nil |-- e t ->
                     plug C e' e ->
                     exists t', nil |-- e' t'.
Proof.
  intros.
  generalize dependent t.
  induction H0; intros.
  exists t; eauto.

  inversion H; subst. destruct (IHplug (Fun t1 t) H4).
  exists x; eauto.

  inversion H1; subst. destruct (IHplug t1 H7).
  exists x; eauto.

  inversion H; subst. destruct (IHplug Bool H5).
  exists x; eauto.
Qed.


Lemma preservation_step : forall e1 e2 t, nil |-- e1 t ->
                                     step e1 e2 ->
                                     nil |-- e2 t.
Proof.
  intros.
  inversion H0; subst.
  destruct (typed_hole H H1).
  assert (nil |-- e3 x).
  eapply preservation_prim_step; eauto.
  eapply preservation_plug.
  eapply H. eapply H4. eapply H5. eapply H1. eapply H2.
Qed.

Lemma preservation : forall e1 e2 t, multi step e1 e2 ->
                                nil |-- e1 t ->
                                nil |-- e2 t.
Proof.
  intros.
  induction H; eauto.
  eapply preservation_step in H; eauto.
Qed.


Lemma values_dont_step : forall v e, value v -> ~step v e.
Proof.
  unfold not. intros.
  inversion H0;
  inversion H; subst; inversion H1; subst;
  inversion H3.
Qed.


Ltac invert H := inversion H; clear H; subst.
Ltac invert1 H := invert H; [].

Lemma step_prim_deterministic : forall e1 e2 e2',
                                  step_prim e1 e2 ->
                                  step_prim e1 e2' ->
                                  e2 = e2'.
Proof.
  intros.
  invert H; invert H0; eauto.
Qed.

Ltac smash :=
  repeat try match goal with
               |[H : App _ _ = App _ _ |- _] => invert H
               |[H : If _ _ _ = If _ _ _ |- _] => invert H
               |[H : plug _ _ _ |- _] => invert1 H
               |[H : plug _ _ ?v, H1 : value ?v |- _] => invert H
               |[H : step_prim _ _ |- _] => invert H
               |[H : value (App _ _) |- _] => invert H
               |[H : value (If _ _ _) |- _] => invert H
               |[H : If _ _ _ = App _ _ |- _] => invert H
               |[H : App _ _ = If _ _ _ |- _] => invert H
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
  induction H; intros.
  (* hole *)
  inversion H0; inversion H; eauto; subst; eauto.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.

  (* app1 *)
  inversion H1.
  smash.
  assert (C = C0 /\ e1' = e).
  eapply IHplug; eauto. inversion H8; subst; eauto.
  smash.

  (* app2 *)
  inversion H2.
  smash.
  smash.
  assert (C = C0 /\ e1' = e).
  eapply IHplug; eauto. inversion H10; subst; eauto.

  (* if *)
  inversion H1.
  smash.
  assert (C = C0 /\ e1' = e).
  eapply IHplug; eauto. inversion H9; subst; eauto.
Qed.


Lemma step_deterministic : forall e1 e2 e2',
                             step e1 e2 ->
                             step e1 e2' ->
                             e2 = e2'.
Proof.
  induction 1; intros.
  invert H2.
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
  intros. unfold halts.
  split; intros; inversion H0; clear H0;
  subst; inversion H1; clear H1.
  (* -> *)
  inversion H0; subst. exfalso.
  eapply values_dont_step in H2. eauto.
  assert (x2 = e'). eapply step_deterministic; eauto.
  subst. exists x; eauto.
  (* <- *)
  exists x. split; eauto.
Qed.

Ltac use_sn :=
  match goal with
    | [H : SN _ _ |- _ ] => unfold SN in H; fold SN in H
  end;
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
         end;
  unfold SN; fold SN; intuition.


Ltac use_preservation :=
  match goal with
    | [ H : nil |-- ?e ?t, S : step ?e ?u |- nil |-- ?u ?t ] =>
      eapply preservation; repeat eassumption
  end.

Ltac use_preserve_halting :=
  match goal with
    | [ H : step ?T ?U, H1 : halts ?T |- halts ?U ] =>
      eapply (step_preserves_halting T U); repeat eassumption
    | [ H : multi step ?T ?U, H1 : halts ?T |- halts ?U ] =>
      eapply MultiStep; eauto; eapply (step_preserves_halting T U); repeat eassumption
  end.


Lemma step_preserves_sn : forall t e e',
                            step e e' ->
                            SN t e ->
                            SN t e'.
Proof.
  induction t; intros e e' H H0;

  use_sn; try use_preservation; try use_preserve_halting.

  eapply MultiStep. eapply H; eauto. eauto.
  eapply step_preserves_halting with (e := e); eauto.

  eapply MultiStep. eapply H; eauto. eauto.
  eapply step_preserves_halting with (e := e); eauto.

  eapply IHt2; eauto.

  eapply step_context. eapply H.
  eapply PApp1. eapply PHole.
  eapply PApp1. eapply PHole.
Qed.

Lemma multistep_preserves_sn : forall t e e',
                                 multi step e e' ->
                                 SN t e ->
                                 SN t e'.
Proof.
  intros.
  induction H; eauto.
  eapply IHmulti.
  eapply step_preserves_sn; eauto.
Qed.


Lemma anti_reduct : forall e' e t, multi step e e' ->
                              SN t e' ->
                              nil |-- e t ->
                              SN t e.
Proof.
  intros.
  generalize dependent e.
  generalize dependent e'.
  induction t.
  (* Bool *)
  unfold SN.
  split; eauto. split; eauto.
  (* halting *)
  inversion H0. inversion H3. clear H3 H5.
  unfold halts in *.
  inversion H4. exists x. split. eapply multi_trans. eapply H.
  inversion H3. assumption. inversion H3. assumption.

  (* Fun *)
  unfold SN.
  split; eauto. split.
  (* halting *)
  inversion H0. inversion H3. clear H0 H3.
  unfold halts in *.
  inversion H4. exists x. split. eapply multi_trans. eapply H.
  inversion H0. assumption. inversion H0. assumption.
  (* special *)
  fold SN in *. intros.
  eapply IHt2. inversion H0. inversion H4. clear H0 H4.
  eapply H6. eapply H2. eapply multi_context with (C := CApp1 CHole s). eauto. eapply PApp1. eapply PHole. eapply PApp1. eapply PHole.
  (* typing *)
  eapply TApp; eauto. eapply sn_types in H2; assumption.
Qed.

Lemma anti_reduct' : forall e' e t,
                       nil |-- e t ->
                       multi step e e' ->
                              SN t e' ->
                              SN t e.
Proof.
  intros. eapply anti_reduct; eauto.
Qed.

Lemma multi_subst : forall x v1 v2 e,
                      closed v1 -> closed v2 ->
                      [x:=v1]([x:=v2]e) = [x:=v2]e.
Proof.
  intros.
  induction e.
  simpl.
  destruct (string_dec s x); eauto.
  rewrite sub_closed; eauto.
  simpl. rewrite string_dec_ne; eauto.
  eauto.
  simpl. destruct (string_dec s x); eauto.
  simpl. destruct (string_dec s x); eauto.
  exfalso. eapply n; eapply e0.
  simpl. destruct (string_dec s x); eauto.
  rewrite IHe; eauto.
  simpl. rewrite IHe1. rewrite IHe2. eauto.
  simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. eauto.
Qed.


Lemma swap_sub : forall x1 x2 v1 v2 e,
                   x1 <> x2 ->
                   closed v1 ->
                   closed v2 ->
                   [x1:=v1]([x2:=v2]e) = [x2:=v2]([x1:=v1]e).
Proof.
  intros.
  induction e.
  simpl.
  destruct (string_dec s x1); subst.
  destruct (string_dec x1 x2); subst.
  exfalso; eauto.
  simpl. rewrite string_dec_refl.
  rewrite sub_closed; eauto.
  destruct (string_dec s x2); subst.
  simpl. rewrite string_dec_refl.
  rewrite sub_closed; eauto.
  simpl. rewrite string_dec_ne; eauto.
  rewrite string_dec_ne; eauto.
  eauto.
  simpl.
  destruct (string_dec s x1); subst; eauto.
  destruct (string_dec x1 x2); subst; eauto.
  simpl. rewrite string_dec_refl. rewrite string_dec_refl.
  eauto.
  simpl. rewrite string_dec_refl.
  rewrite string_dec_ne; eauto.
  destruct (string_dec s x2); subst; eauto.
  simpl. rewrite string_dec_ne; eauto.
  rewrite string_dec_refl. reflexivity.
  simpl. rewrite string_dec_ne; eauto.
  rewrite string_dec_ne; eauto.
  rewrite IHe. reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. eauto.
  simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. eauto.
Qed.



Lemma sub_close: forall Σ x v e,
                      closed v ->
                      closed_env Σ ->
                      close Σ ([x:=v]e) = [x:=v](close (drop x Σ) e).
Proof.
  intro Σ.
  induction Σ; intros; eauto.

  destruct a; subst.
  simpl.

  destruct (string_dec s x); subst; eauto.
  rewrite string_dec_refl.
  rewrite multi_subst. eapply IHΣ; eauto.
  inversion H0; eauto. inversion H0; eauto. eauto.

  rewrite string_dec_ne. simpl.
  rewrite swap_sub; eauto.
  eapply IHΣ; eauto.
  inversion H0; eauto. inversion H0; eauto. eauto.
Qed.


Lemma multistep_App2 : forall v e e',
                         value v ->
                         multi step e e' ->
                         multi step (App v e) (App v e').
Proof.
  intros.
  eapply multi_context with (e1 := e) (e2 := e'); eauto.
  eapply PApp2. eapply PHole. eauto.
  eapply PApp2. eapply PHole. eauto.
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
  induction Σ; intros; eauto.
  destruct a.
  simpl. destruct (string_dec x s); eauto.
  eapply IHΣ; eauto.
  inversion H0; eauto.
  simpl.
  rewrite IHΣ.
  rewrite swap_sub; eauto.
  inversion H0; eauto.
  inversion H0; eauto.
Qed.

Lemma drop_sub : forall Σ x v e,
                   closed v ->
                   closed_env Σ ->
                   close (drop x Σ) ([x:=v]e) =
                   close Σ ([x:=v]e).
Proof.
  intro Σ.
  induction Σ; intros; eauto.
  destruct a; eauto.
  simpl.
  destruct (string_dec x s); eauto.
  subst. rewrite multi_subst. eapply IHΣ; eauto.
  inversion H0; eauto. inversion H0; eauto.
  eauto.
  simpl.
  rewrite swap_sub; eauto.
  eapply IHΣ. inversion H0; eauto. inversion H0; eauto.
  inversion H0; eauto.
Qed.

Lemma extend_drop' : forall Σ (x:string) (v:exp) e,
                       closed_env Σ ->
                       closed v ->
                       close (extend (drop x Σ) x v) e = close (cons (x,v) Σ) e.
Proof.
  intros.
  induction Σ; eauto; try (inversion H).
  destruct a.
  simpl.
  destruct (string_dec x s). subst.
  rewrite multi_subst.
  rewrite (sub_close Σ).
  rewrite sub_close_extend. rewrite IHΣ; eauto. simpl.
  rewrite drop_sub; eauto.
  inversion H; eauto.
  inversion H; eauto. eauto.
  inversion H; eauto.
  eauto.
  inversion H; eauto.
  inversion H; eauto.
  eauto.
  simpl.
  rewrite swap_sub; eauto.
  rewrite drop_sub. reflexivity.
  eauto. eauto.
  inversion H; eauto.
  inversion H; eauto.
Qed.

Lemma lookup_mextend : forall (Γ : list (string * ty)) x x0 t,
                        x <> x0 ->
                        lookup ((x, t) :: Γ) x0 =
                        lookup (mextend (cons (x, t) nil) Γ) x0.
Proof.
  intros.
  simpl. rewrite string_dec_ne; eauto.
  induction Γ; simpl.
  rewrite string_dec_ne; eauto.
  destruct a. simpl.
  rewrite IHΓ. reflexivity.
Qed.



Lemma TAbs_compat : forall Γ Σ x e t t',
                      Γ |= Σ ->
                      (extend Γ x t) |-- e t' ->
                      (forall v, SN t v -> SN t' (close (extend (drop x Σ) x v) e)) ->
                      SN (Fun t t') (close Σ (Abs x t e)).
Proof.
  intros.
  assert (WT: nil |-- (Abs x t (close (drop x Σ) e)) (Fun t t')).
    { eapply TAbs. eapply close_preserves.
      { eapply fulfills_drop; eauto. }
      eapply context_invariance.
      { apply H0. }
      intros.
      unfold extend. rewrite extend_drop. destruct (string_dec x0 x).
      + subst. simpl. rewrite string_dec_refl. rewrite string_dec_refl. reflexivity.
      + assert (drop x (nil : list (string * ty)) = nil); eauto. rewrite H3. eapply lookup_mextend; eauto.
    }
    simpl. split. rewrite close_abs.
    auto.
    split.
    apply halts_value. rewrite close_abs. apply VAbs.

    intros.
     destruct (sn_halts t s H2) as [v [P Q]].
     pose proof (multistep_preserves_sn t P H2).
     eapply anti_reduct' with (close (cons (x,v) Σ) e).
     eapply TApp. rewrite close_abs.
     apply sn_types; auto.

     simpl.
     split. eauto. split. eapply halts_value. eauto.
     intros.
     assert (halts s0). eapply sn_halts. eapply H4.
     inversion H5.
     eapply anti_reduct' with (e' := close (extend (drop x Σ) x x0) e).
     eapply TApp. eapply WT. eapply sn_types; eauto.
     eapply multi_trans with (b := (App (Abs x t (close (drop x Σ) e)) x0)).
     inversion H6. clear H6.
     eapply multi_context with (e1 := s0) (e2 := x0); eauto.
     eapply PApp2. eapply PHole. eauto. eapply PApp2. eapply PHole. eauto.
     eapply MultiStep. eapply Step. eapply PHole. eapply PHole. eapply SBeta. inversion H6; eauto.
     rewrite sub_close_extend. eapply MultiRefl.
     eapply sn_closed. eapply multistep_preserves_sn.
     inversion H6.
     eapply H7. eauto.

     eapply fulfill_closed; eauto.

     eapply H1. eapply multistep_preserves_sn.
     inversion H6.
     eapply H7. eauto.

     eapply sn_types. eapply H2.

     eapply multi_trans.  eapply multistep_App2; eauto.

     rewrite close_abs. eapply VAbs.

     eapply MultiStep.
     eapply Step. eapply PHole. eapply PHole.
     rewrite close_abs.
     eapply SBeta. eauto. simpl.
     rewrite sub_close. eapply MultiRefl.
     eapply sn_closed; eauto.
     eapply fulfill_closed; eauto.

     rewrite <- extend_drop'.
     eapply H1. assumption.
     eapply fulfill_closed; eauto.
     eapply sn_closed; eauto.
Qed.

Lemma close_app : forall Σ e1 e2,
                    close Σ (App e1 e2) =
                    App (close Σ e1) (close Σ e2).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

Lemma TApp_compat : forall Γ Σ e1 e2 t t',
                      Γ |= Σ ->
                      SN (Fun t t') (close Σ e1) ->
                      SN t (close Σ e2) ->
                      SN t' (close Σ (App e1 e2)).
Proof.
  intros.
  rewrite close_app.
  destruct H0. destruct H2. eapply H3; eauto.
Qed.

Lemma close_if : forall Σ e1 e2 e3,
                    close Σ (If e1 e2 e3) =
                    If (close Σ e1) (close Σ e2) (close Σ e3).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

Lemma TIf_compat : forall Γ Σ e1 e2 e3 t,
                      Γ |= Σ ->
                      SN Bool (close Σ e1) ->
                      SN t (close Σ e2) ->
                      SN t (close Σ e3) ->
                      SN t (close Σ (If e1 e2 e3)).
Proof.
  intros.
  rewrite close_if.
  (* need to get a boolean, so we know how to step *)
  inversion H0. inversion H4. inversion H5. inversion H7. eapply preservation with (e2 := x) (t := Bool) in H8. inversion H8. inversion H7.
  destruct b; subst.
  (* true *)
  eapply anti_reduct with (e' := close Σ e2); eauto.
  eapply multi_trans with (b := (If (Const true) (close Σ e2) (close Σ e3))).
  eapply multi_context.
  eauto.
  eapply PIf. eapply PHole. eapply PIf. eapply PHole.
  eapply MultiStep. eapply Step with (C := CHole). eapply PHole. eapply PHole. eapply SIfTrue. eapply MultiRefl.
  (* typing *)
  eapply TIf; eauto. eapply sn_types in H1; eauto.
  eapply sn_types in H2; eauto.
  (* false *)
  eapply anti_reduct with (e' := close Σ e3); eauto.
  eapply multi_trans with (b := (If (Const false) (close Σ e2) (close Σ e3))).
  eapply multi_context.
  eauto.
  eapply PIf. eapply PHole. eapply PIf. eapply PHole.
  eapply MultiStep. eapply Step with (C := CHole). eapply PHole. eapply PHole. eapply SIfFalse. eapply MultiRefl.
  (* typing *)
  eapply TIf; eauto. eapply sn_types in H1; eauto.
  eapply sn_types in H2; eauto.

  subst. inversion H9. subst. inversion H9. subst. inversion H9. eapply sn_types; eauto.

Qed.


Lemma drop_fulfills : forall Γ Σ x,
                        Γ |= Σ ->
                        drop x Γ |= drop x Σ.
Proof.
  intros.
  induction H. econstructor.
  simpl.
  destruct (string_dec x x0); eauto.
  econstructor. eauto. eassumption.
Qed.

Theorem fundamental : forall e t Γ Σ,
                        Γ |-- e t ->
                            Γ |= Σ ->
                            SN t (close Σ e).
Proof.
  intros.
  generalize dependent Σ.
  induction H; intros.

  eapply TConst_compat; eauto.

  eapply TVar_compat; eauto.

  eapply TAbs_compat; eauto.
  eapply extend_drop'' in H. eauto.
  intros. eapply IHhas_type. eapply FCons; eauto.
  eapply drop_fulfills; eauto.

  eapply TApp_compat; eauto.

  eapply TIf_compat; eauto.
Qed.

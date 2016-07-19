Require Import Coq.Unicode.Utf8 Arith FunctionalExtensionality String Coq.Program.Equality.

Load CpdtTactics.

Set Implicit Arguments.

Ltac iauto := try solve [intuition (eauto 3)].
Ltac iauto' := try solve [intuition eauto].
Ltac invert H := inversion H; clear H; try subst.

(**************************************)
(********* 1. SOURCE SYNTAX ***********)
(**************************************)

Inductive s_ty  : Set :=
| S_TUnit : s_ty
| S_TFun : s_ty -> s_ty -> s_ty
| S_TRef : s_ty -> s_ty.

Inductive s_exp : Set :=
| S_Var : string -> s_exp
| S_Unit : s_exp
| S_Abs : string -> s_ty -> s_exp -> s_ty -> s_exp
| S_App : s_exp -> s_exp -> s_exp
| S_Ref : s_exp -> s_exp
| S_Assign : s_exp -> s_exp -> s_exp
| S_Bang : s_exp -> s_exp
| S_Loc : string -> s_exp.

Inductive s_value : s_exp -> Prop :=
| S_VUnit : s_value S_Unit
| S_VAbs : forall x t b bt, s_value (S_Abs x t b bt)
| S_VLoc : forall l, s_value (S_Loc l).

(**************************************)
(********** 2. ENVIRONMENTS  **********)
(**************************************)

Definition s_tyenv := list (string * s_ty).

Definition s_venv := list (string * s_exp).

Definition s_store := list (string * s_exp).

Definition extend {T : Set}
           (G : list (string * T))
           (x:string)
           (t : T) : list (string * T) :=
  cons (x,t) G.

Fixpoint mextend  {T : Set}
         (e : list (string * T))
         (G : list (string * T))
         {struct G} : list (string * T) :=
  match G with
    | nil => e
    | cons (x,v) G' => extend (mextend e G') x v
  end.

Fixpoint lookup {T : Set}
                (E : list (string * T))
                (x:string) : option T :=
  match E with
    |cons (y,t) rest =>
     if string_dec y x then Some t else lookup rest x
    |nil => None
  end.

Fixpoint lookup' (E : list string)
                 (x:string) : bool :=
  match E with
    |cons y rest =>
     if string_dec y x then true else false
    |nil => false
  end.

Fixpoint drop {T : Set}
         (x:string)
         (E : list (string * T)) : list (string * T) :=
  match E with
    | nil => nil
    | cons (y,t) rest =>
      if string_dec x y
      then drop x rest
      else cons (y,t) (drop x rest)
  end.

Fixpoint drop'
         (x:string)
         (E : list string) : list string :=
  match E with
    | nil => nil
    | cons y rest =>
      if string_dec x y
      then drop' x rest
      else cons y (drop' x rest)
  end.


(**************************************)
(****** 3. SOURCE SUBSTITUTION  *******)
(**************************************)

Fixpoint s_sub (x:string) (e:s_exp) (e':s_exp) : s_exp :=
  match e with
    | S_Var y => if string_dec y x then e' else e
    | S_Unit => e
    | S_Loc _ => e
    | S_Abs y t body bodyt =>
      if string_dec y x
      then e
      else S_Abs y t (s_sub x body e') bodyt
    | S_App e1 e2 => S_App (s_sub x e1 e') (s_sub x e2 e')
    | S_Ref e => S_Ref (s_sub x e e')
    | S_Bang e => S_Bang (s_sub x e e')
    | S_Assign e1 e2 => S_Assign (s_sub x e1 e')
                                (s_sub x e2 e')
    end.

Notation "'[s' x ':=' s ']' t" := (s_sub x t s) (at level 20).

Inductive s_free_in : string -> s_exp -> Prop :=
| s_free_var : forall x, s_free_in x (S_Var x)
| s_free_abs : forall x t y b bt, s_free_in x b ->
                             x <> y ->
                             s_free_in x (S_Abs y t b bt)
| s_free_app1 : forall x e1 e2, s_free_in x e1 ->
                           s_free_in x (S_App e1 e2)
| s_free_app2 : forall x e1 e2, s_free_in x e2 ->
                         s_free_in x (S_App e1 e2)
| s_free_ref : forall x e, s_free_in x e ->
                      s_free_in x (S_Ref e)
| s_free_bang : forall x e, s_free_in x e ->
                       s_free_in x (S_Bang e)
| s_free_assign1 : forall x e1 e2,
                     s_free_in x e1 ->
                     s_free_in x (S_Assign e1 e2)
| s_free_assign2 : forall x e1 e2,
                     s_free_in x e2 ->
                     s_free_in x (S_Assign e1 e2).

Hint Constructors s_free_in.

Ltac s_free_invert :=
  match goal with
    |[H : s_free_in _ _ |- _] => invert H
  end.

Definition s_closed t := forall x, ~ s_free_in x t.

Fixpoint s_closed_env (Σ:s_venv) :=
  match Σ with
    | nil => True
    | cons (_,e1) en => s_closed e1 /\ s_closed_env en
  end.

Fixpoint s_close (Σ : s_venv) (e : s_exp) : s_exp :=
  match Σ with
    |nil => e
    |cons (x,v) Σ' => s_close Σ' ([s x:=v]e)
  end.

(**************************************)
(********* 3. SOURCE TYPING  **********)
(**************************************)

Reserved Notation "Γ '|s-' e" (at level 10).

Inductive s_has_type : s_tyenv -> s_exp -> s_ty -> Prop :=
| S_HTUnit : forall Γ, s_has_type Γ S_Unit S_TUnit
| S_HTVar : forall Γ x t, lookup Γ x = Some t ->
                     s_has_type Γ (S_Var x) t
| S_HTAbs : forall Γ x e t t',
              s_has_type (extend (drop x Γ) x t) e t' ->
              s_has_type Γ (S_Abs x t e t') (S_TFun t t')
| S_HTApp : forall Γ e e' t1 t2, s_has_type Γ e (S_TFun t1 t2) ->
                            s_has_type Γ e' t1 ->
                            s_has_type Γ (S_App e e') t2
| S_HTRef : forall Γ e t, s_has_type Γ e t ->
                     s_has_type Γ (S_Ref e) (S_TRef t)
| S_HTBang : forall Γ e t, s_has_type Γ e (S_TRef t) ->
                      s_has_type Γ (S_Bang e) t
| S_HTAssign : forall Γ e1 e2 t, s_has_type Γ e1 (S_TRef t) ->
                            s_has_type Γ e2 t ->
                            s_has_type Γ (S_Assign e1 e2)
                                       S_TUnit
where "Γ '|s-' e" := (s_has_type Γ e).

Hint Constructors s_has_type s_ty s_exp s_value.

(**************************************)
(****** 4. SOURCE EVALUATION  *********)
(**************************************)

Inductive s_context : Set :=
| S_CHole : s_context
| S_CApp1 : s_context -> s_exp -> s_context
| S_CApp2 : s_exp -> s_context -> s_context
| S_CRef : s_context -> s_context
| S_CBang : s_context -> s_context
| S_CAssign1 : s_context -> s_exp -> s_context
| S_CAssign2 : s_exp -> s_context -> s_context.

Hint Constructors s_context.

Inductive s_plug : s_context -> s_exp -> s_exp -> Prop :=
| S_PHole : forall e, s_plug S_CHole e e
| S_PApp1 : forall e e' C e2,
              s_plug C e e' ->
              s_plug (S_CApp1 C e2) e (S_App e' e2)
| S_PApp2 : forall e e' C v,
              s_plug C e e' ->
              s_value v ->
              s_plug (S_CApp2 v C) e (S_App v e')
| S_PRef : forall e e' C,
             s_plug C e e' ->
             s_plug (S_CRef C) e (S_Ref e')
| S_PBang : forall e e' C,
              s_plug C e e' ->
              s_plug (S_CBang C) e (S_Bang e')
| S_PAssign1 : forall e e' C e2,
                 s_plug C e e' ->
                 s_plug (S_CAssign1 C e2) e
                        (S_Assign e' e2)
| S_PAssign2 : forall e e' C v,
                 s_plug C e e' ->
                 s_value v ->
                 s_plug (S_CAssign2 v C) e
                        (S_Assign v e').

Hint Constructors s_plug.


Inductive s_step_prim : s_store ->
                        s_exp ->
                        s_store * s_exp -> Prop :=
| SBeta : forall S x t b bt v,
            s_value v ->
            s_step_prim S (S_App (S_Abs x t b bt) v)
                        (S, [s x:=v]b)
| SAlloc : forall S l v, s_value v ->
                    lookup S l = None ->
                    s_step_prim S (S_Ref v)
                                (extend S l v, S_Loc l)
| SDeref : forall S l v, lookup S l = Some v ->
                    s_step_prim S (S_Bang (S_Loc l))
                                (S, v)
| SSet : forall S l v _e,
           s_value v ->
           lookup S l = Some _e ->
           s_step_prim S (S_Assign (S_Loc l) v)
                       (extend (drop l S) l v, S_Unit).

Hint Constructors s_step_prim.


Inductive s_step : s_store ->
                   s_exp ->
                   (s_store * s_exp) -> Prop :=
| S_Step : forall S S' C e1 e2 e1' e2',
             s_plug C e1 e1' ->
             s_plug C e2 e2' ->
             s_step_prim S e1 (S', e2) ->
             s_step S e1' (S', e2').

Hint Constructors s_step.

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

Hint Resolve multi_trans.

(**************************************)
(********* 5. TARGET SYNTAX ***********)
(**************************************)

Inductive t_ty  : Set :=
| T_TUnit : t_ty
| T_TFun : t_ty -> t_ty -> t_ty
| T_TRef : t_ty -> t_ty
| T_TProd : t_ty -> t_ty -> t_ty
| T_TVar : string -> t_ty
| T_TForall : string -> t_ty -> t_ty
| T_TExists : string -> t_ty -> t_ty.

Inductive t_exp : Set :=
| T_Var : string -> t_exp
| T_Unit : t_exp
| T_Abs : string -> t_ty -> t_exp -> t_ty -> t_exp
| T_App : t_exp -> t_exp -> t_exp
| T_Ref : t_exp -> t_exp
| T_Assign : t_exp -> t_exp -> t_exp
| T_Bang : t_exp -> t_exp
| T_Loc : string -> t_exp
| T_Pair : t_exp -> t_exp -> t_exp
| T_Forall : string -> t_exp -> t_exp
| T_TyApp : t_exp -> t_ty -> t_exp
| T_Pack : t_exp -> string -> t_ty -> t_exp
| T_Unpack : t_exp -> string -> t_exp -> t_exp
| T_Let : t_exp -> string -> string -> t_exp -> t_exp.

Inductive t_value : t_exp -> Prop :=
| T_VUnit : t_value T_Unit
| T_VAbs : forall x t b bt, t_value (T_Abs x t b bt)
| T_VLoc : forall l, t_value (T_Loc l)
| T_VPair : forall v1 v2,
              t_value v1 ->
              t_value v2 ->
              t_value (T_Pair v1 v2)
| T_VPack : forall v a t,
              t_value (T_Pack v a t)
| T_VForall : forall a e,
                t_value (T_Forall a e).

(**************************************)
(****** 6. TARGET SUBSTITUTION  *******)
(**************************************)

Definition t_tyenv := list (string * t_ty).

Definition t_tvarenv := list string.

Definition t_venv := list (string * t_exp).

Definition t_store := list (string * t_exp).


Fixpoint t_sub (x:string) (e:t_exp) (e':t_exp): t_exp :=
  match e with
    | T_Var y => if string_dec y x then e' else e
    | T_Unit => e
    | T_Loc _ => e
    | T_Abs y t body bodyt =>
      if string_dec y x
      then e
      else T_Abs y t (t_sub x body e') bodyt
    | T_App e1 e2 => T_App (t_sub x e1 e') (t_sub x e2 e')
    | T_Ref e => T_Ref (t_sub x e e')
    | T_Bang e => T_Bang (t_sub x e e')
    | T_Assign e1 e2 => T_Assign (t_sub x e1 e')
                                (t_sub x e2 e')
    | T_Pair e1 e2 => T_Pair (t_sub x e1 e')
                            (t_sub x e2 e')
    | T_Forall a e => T_Forall a (t_sub x e e')
    | T_TyApp e t => T_TyApp (t_sub x e e') t
    | T_Pack v a t => T_Pack (t_sub x v e') a t
    | T_Unpack e1 y e2 => T_Unpack (t_sub x e1 e')
                                  y
                                  (if string_dec y x
                                   then e2
                                   else t_sub x e2 e')
    | T_Let e1 x1 x2 e2 =>
      T_Let (t_sub x e1 e')
            x1 x2
            (if string_dec x x1
             then e2
             else (if string_dec x x2
                   then e2
                   else t_sub x e2 e'))
    end.

Fixpoint tsub (x:string) (t:t_ty) (t':t_ty) : t_ty :=
  match t' with
    | T_TUnit => t'
    | T_TFun td ty => T_TFun (tsub x t td) (tsub x t ty)
    | T_TRef ty => T_TRef (tsub x t ty)
    | T_TProd t1 t2 => T_TProd (tsub x t t1) (tsub x t t2)
    | T_TVar y => if string_dec x y then t' else t'
    | T_TForall y ty => if string_dec x y then t' else T_TForall y (tsub x t ty)
    | T_TExists y ty => if string_dec x y then t' else T_TExists y (tsub x t ty)
  end.

Notation "'[t' x ':=' s ']' t" := (t_sub x t s) (at level 20).

Inductive t_free_in : string -> t_exp -> Prop :=
| t_free_var : forall x, t_free_in x (T_Var x)
| t_free_abs : forall x t y b bt, t_free_in x b ->
                             x <> y ->
                             t_free_in x (T_Abs y t b bt)
| t_free_app1 : forall x e1 e2, t_free_in x e1 ->
                           t_free_in x (T_App e1 e2)
| t_free_app2 : forall x e1 e2, t_free_in x e2 ->
                           t_free_in x (T_App e1 e2)
| t_free_ref : forall x e, t_free_in x e ->
                      t_free_in x (T_Ref e)
| t_free_bang : forall x e, t_free_in x e ->
                       t_free_in x (T_Bang e)
| t_free_assign1 : forall x e1 e2,
                     t_free_in x e1 ->
                     t_free_in x (T_Assign e1 e2)
| t_free_assign2 : forall x e1 e2,
                     t_free_in x e2 ->
                     t_free_in x (T_Assign e1 e2)
| t_free_pair1 : forall x e1 e2,
                   t_free_in x e1 ->
                   t_free_in x (T_Pair e1 e2)
| t_free_pair2 : forall x e1 e2,
                   t_free_in x e2 ->
                   t_free_in x (T_Pair e1 e2)
| t_free_forall : forall a x e,
                    t_free_in x e ->
                    t_free_in x (T_Forall a e)
| t_free_tyapp : forall t x e,
                   t_free_in x e ->
                   t_free_in x (T_TyApp e t)
| t_free_pack : forall x e a t,
                  t_free_in x e ->
                  t_free_in x (T_Pack e a t)
| t_free_unpack1 : forall x y e1 e2,
                     t_free_in x e1 ->
                     t_free_in x (T_Unpack e1 y e2)
| t_free_unpack2 : forall x y e1 e2,
                     t_free_in x e2 ->
                     x <> y ->
                     t_free_in x (T_Unpack e1 y e2)
| t_free_let1 : forall x y1 y2 e1 e2,
                  t_free_in x e1 ->
                  t_free_in x (T_Let e1 y1 y2 e2)
| t_free_let2 : forall x y1 y2 e1 e2,
                  t_free_in x e2 ->
                  x <> y1 -> x <> y2 ->
                  t_free_in x (T_Let e1 y1 y2 e2).

Hint Constructors t_free_in.

Ltac t_free_invert :=
  match goal with
    |[H : t_free_in _ _ |- _] => invert H
  end.

Definition t_closed t := forall x, ~ t_free_in x t.

Fixpoint t_closed_env (Σ:t_venv) :=
  match Σ with
    | nil => True
    | cons (_,e1) en => t_closed e1 /\ t_closed_env en
  end.

Fixpoint t_close (Σ : t_venv) (e : t_exp) : t_exp :=
  match Σ with
    |nil => e
    |cons (x,v) Σ' => t_close Σ' ([t x:=v]e)
  end.



(**************************************)
(********* 7. TARGET TYPING  **********)
(**************************************)

Inductive t_wf : t_tvarenv -> t_ty -> Prop :=
| T_WFUnit : forall Γt, t_wf Γt T_TUnit
| T_WFFun : forall Γt dom ran, t_wf Γt dom ->
                          t_wf Γt ran ->
                          t_wf Γt (T_TFun dom ran)
| T_WFRef : forall Γt t, t_wf Γt t ->
                    t_wf Γt (T_TRef t)
| T_WFProd : forall Γt t1 t2, t_wf Γt t1 ->
                         t_wf Γt t2 ->
                         t_wf Γt (T_TProd t1 t2)
| T_WFVar : forall Γt a t, lookup' Γt a = true ->
                      (* NOTE(dbp 2016-07-19): is this
                       allowing recursively defined types?
                       is that a problem? *)
                      t_wf Γt t ->
                      t_wf Γt (T_TVar a)
| T_WFForall : forall Γt a t, t_wf (cons a Γt) t ->
                         t_wf Γt (T_TForall a t)
| T_WFExists : forall Γt a t, t_wf (cons a Γt) t ->
                         t_wf Γt (T_TExists a t).


Reserved Notation "Γ '|t-' e" (at level 10).

Inductive t_has_type : t_tvarenv -> t_tyenv -> t_exp -> t_ty -> Prop :=
| T_HTUnit : forall Γt Γ, t_has_type Γt Γ T_Unit T_TUnit
| T_HTVar : forall Γt Γ x t, lookup Γ x = Some t ->
                        t_has_type Γt  Γ (T_Var x) t
| T_HTAbs : forall Γt Γ x e t t',
              t_has_type Γt (extend (drop x Γ) x t) e t' ->
              t_has_type Γt Γ (T_Abs x t e t')
                         (T_TFun t t')
| T_HTApp : forall Γt Γ e e' t1 t2,
              t_has_type Γt Γ e (T_TFun t1 t2) ->
              t_has_type Γt Γ e' t1 ->
              t_has_type Γt Γ (T_App e e') t2
| T_HTRef : forall Γt Γ e t,
              t_has_type Γt Γ e t ->
              t_has_type Γt Γ (T_Ref e) (T_TRef t)
| T_HTBang : forall Γt Γ e t, t_has_type Γt Γ e (T_TRef t) ->
                         t_has_type Γt Γ (T_Bang e) t
| T_HTAssign : forall Γt Γ e1 e2 t,
                 t_has_type Γt Γ e1 (T_TRef t) ->
                 t_has_type Γt Γ e2 t ->
                 t_has_type Γt Γ (T_Assign e1 e2)
                            T_TUnit
| T_HTPair : forall Γt Γ e1 e2 t1 t2,
               t_has_type Γt Γ e1 t1 ->
               t_has_type Γt Γ e2 t2 ->
               t_has_type Γt Γ (T_Pair e1 e2)
                          (T_TProd t1 t2)
| T_HTForall : forall Γt Γ x e t,
                 t_has_type (cons x Γt) Γ e t ->
                 t_has_type Γt Γ (T_Forall x e) t
| T_HTTyApp : forall Γt Γ x e t t',
                t_wf Γt t ->
                t_has_type Γt Γ e (T_TForall x t') ->
                t_has_type Γt Γ (T_TyApp e t)
                           (tsub x t t')
| T_HTPack : forall Γt Γ x e t t',
               t_wf Γt t' ->
               t_has_type Γt Γ e (tsub x t' t) ->
               t_has_type Γt Γ (T_Pack e x t)
                          (T_TExists x t)
| T_HTUnpack : forall Γt Γ a e e' t t',
                 t_wf Γt t' ->
                 t_has_type Γt Γ e' (T_TExists a t) ->
                 t_has_type (cons a Γt) Γ e t' ->
                 t_has_type Γt Γ (T_Unpack e' a e)
                            t'
| T_HTLet : forall Γt Γ x1 x2 e e' t1 t2 t',
              t_has_type Γt Γ e (T_TProd t1 t2) ->
              x1 <> x2 ->
              t_has_type Γt
                         (extend (extend Γ x1 t1) x2 t2)
                         e' t' ->
              t_has_type Γt Γ (T_Let e x1 x2 e') t'

where "Γ '|t-' e" := (t_has_type Γ e).

Hint Constructors t_wf t_has_type t_ty t_exp t_value.


(**************************************)
(****** 8. TARGET EVALUATION  *********)
(**************************************)

Inductive t_context : Set :=
| T_CHole : t_context
| T_CApp1 : t_context -> t_exp -> t_context
| T_CApp2 : t_exp -> t_context -> t_context
| T_CRef : t_context -> t_context
| T_CBang : t_context -> t_context
| T_CAssign1 : t_context -> t_exp -> t_context
| T_CAssign2 : t_exp -> t_context -> t_context
| T_CPair1 : t_context -> t_exp -> t_context
| T_CPair2 : t_exp -> t_context -> t_context
| T_CTyApp : t_context -> t_ty -> t_context
| T_CUnpack : t_context -> string -> t_exp -> t_context
| T_CLet : t_context -> string -> string -> t_exp -> t_context.


Hint Constructors t_context.

Inductive t_plug : t_context -> t_exp -> t_exp -> Prop :=
| T_PHole : forall e, t_plug T_CHole e e
| T_PApp1 : forall e e' C e2,
              t_plug C e e' ->
              t_plug (T_CApp1 C e2) e (T_App e' e2)
| T_PApp2 : forall e e' C v,
              t_plug C e e' ->
              t_value v ->
              t_plug (T_CApp2 v C) e (T_App v e')
| T_PRef : forall e e' C,
             t_plug C e e' ->
             t_plug (T_CRef C) e (T_Ref e')
| T_PBang : forall e e' C,
              t_plug C e e' ->
              t_plug (T_CBang C) e (T_Bang e')
| T_PAssign1 : forall e e' C e2,
                 t_plug C e e' ->
                 t_plug (T_CAssign1 C e2) e
                        (T_Assign e' e2)
| T_PAssign2 : forall e e' C v,
                 t_plug C e e' ->
                 t_value v ->
                 t_plug (T_CAssign2 v C) e
                        (T_Assign v e')
| T_PPair1 : forall e e' C e2,
               t_plug C e e' ->
               t_plug (T_CPair1 C e2) e
                      (T_Pair e' e2)
| T_PPair2 : forall e e' C v,
               t_plug C e e' ->
               t_value v ->
               t_plug (T_CPair2 v C) e
                      (T_Pair v e')
| T_PTyApp : forall e e' C t,
              t_plug C e e' ->
              t_plug (T_CTyApp C t) e (T_TyApp e' t)
| T_PUnpack : forall e e' C a e2,
              t_plug C e e' ->
              t_plug (T_CUnpack C a e2) e
                     (T_Unpack e' a e2)
| T_PLet : forall e e' C x1 x2 e2,
              t_plug C e e' ->
              t_plug (T_CLet C x1 x2 e2) e
                     (T_Let e' x1 x2 e2).

Hint Constructors t_plug.


Inductive t_step_prim : t_store ->
                        t_exp ->
                        t_store * t_exp -> Prop :=
| TBeta : forall S x t b bt v,
            t_value v ->
            t_step_prim S (T_App (T_Abs x t b bt) v)
                        (S, [t x:=v]b)
| TAlloc : forall S l v, t_value v ->
                    lookup S l = None ->
                    t_step_prim S (T_Ref v)
                                (extend S l v, T_Loc l)
| TDeref : forall S l v, lookup S l = Some v ->
                    t_step_prim S (T_Bang (T_Loc l))
                                (S, v)
| TSet : forall S l v _e,
           t_value v ->
           lookup S l = Some _e ->
           t_step_prim S (T_Assign (T_Loc l) v)
                       (extend (drop l S) l v, T_Unit)
| TLet : forall S v1 v2 x1 x2 e,
           t_value v1 ->
           t_value v2 ->
           t_step_prim S (T_Let (T_Pair v1 v2)
                                x1 x2
                                e)
                       (S, [t x1:=v1][t x2:=v2]e).

Hint Constructors t_step_prim.


Inductive t_step : t_store ->
                   t_exp ->
                   (t_store * t_exp) -> Prop :=
| T_Step : forall S S' C e1 e2 e1' e2',
             t_plug C e1 e1' ->
             t_plug C e2 e2' ->
             t_step_prim S e1 (S', e2) ->
             t_step S e1' (S', e2').

Hint Constructors t_step.

(**************************************)
(********* 9. COMPILATION  ************)
(**************************************)

Fixpoint tcompile (st:s_ty) : t_ty :=
  match st with
    | S_TUnit => T_TUnit
    | S_TFun dom ran => T_TFun (tcompile dom)
                              (tcompile ran)
    | S_TRef t => T_TRef (tcompile t)
  end.

Fixpoint free_vars
         (bound:list string)
         (Γ:t_tyenv)
         (e:s_exp) : list (string * t_ty) :=
  match e with
    | S_Var x =>
      if lookup' bound x then nil else
        match lookup Γ x with
          |Some t => cons (x,t) nil
          |None => nil
        end
    | S_Unit => nil
    | S_Abs x t b bt =>
      free_vars (cons x bound) Γ b
    | S_App e1 e2 =>
      free_vars bound Γ e1 ++ free_vars bound Γ e2
    | S_Ref e' => free_vars bound Γ e'
    | S_Assign e1 e2 =>
      free_vars bound Γ e1 ++ free_vars bound Γ e2
    | S_Bang e' => free_vars bound Γ e'
    | S_Loc l => nil
  end.

Fixpoint mk_pairs (ps : list (string * t_ty)) : t_exp * t_ty :=
  match ps with
    | nil => (T_Unit, T_TUnit)
    | cons (x,xt) xs => let (vs, t) := mk_pairs xs in
                       (T_Pair (T_Var x) vs,
                        T_TProd xt t)
  end.

Definition env_ident (b:bool) : string :=
  if b then "env0" else "env1".

Definition b_not (b:bool) : bool :=
  if b then false else true.

Fixpoint unwrap b (ps : list (string * t_ty)) body {struct ps}: t_exp :=
  match ps with
    |nil => body
    |cons (exp,_) rest =>
     let next_ident := b_not b in
     T_Let (T_Var (env_ident b))
           exp
           (env_ident next_ident)
           (unwrap next_ident rest body)
  end.

Fixpoint compile Γ (e:s_exp) : t_exp :=
  match e with
    | S_Abs y t body bodyt =>
      let body' := compile (extend Γ y t) body in
      let bodyt' := tcompile bodyt in
      let fvs := free_vars (cons y (map fst Γ)) nil body in
      let (pairs, tpairs) := mk_pairs fvs in
      T_Pack (T_Pair pairs
                     (T_Abs "pack" (T_TProd tpairs (tcompile t))
                            (T_Let (T_Var "pack")
                                   (env_ident true)
                                   y
                                   (unwrap false fvs body'))
                            bodyt'))
             "env"
             (T_TProd
                (T_TVar "env")
                (T_TFun
                   (T_TProd (T_TVar "env") (tcompile t))
                   bodyt'))
    | S_App e1 e2 =>
      T_Unpack (compile Γ e1) "fc"
               (T_Let (T_Var "fc")
                      "env"
                      "f"
                      (T_App (T_Var "f")
                             (T_Pair (T_Var "env")
                                     (compile Γ e2))))


    | S_Var y => T_Var y
    | S_Unit => T_Unit
    | S_Loc l => T_Loc l
    | S_Ref e' => T_Ref (compile Γ e')
    | S_Bang e' => T_Bang (compile Γ e')
    | S_Assign e1 e2 => T_Assign (compile Γ e1)
                                (compile Γ e2)
  end.

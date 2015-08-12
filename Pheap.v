(** Implementation of a pairing heap in Coq.
  * (C) 2015 Christoph-Simon Senjak
  *   Require Import String.
  *   Eval compute in ("css" ++ "@" ++ "uxul" ++ "." ++ "de")%string.
  * See LICENSE for licensing information.
  **)

Require Import List.

Inductive pheap A : Type :=
| Empty : pheap A
| Heap : A -> list (pheap A) -> pheap A.

Arguments Empty [_].
Arguments Heap [_] _ _.

Inductive pheap_in {A} : A -> pheap A -> Prop :=
| H_in : forall a l, pheap_in a (Heap a l)
| L_in : forall a b h l, In h l -> pheap_in a h -> pheap_in a (Heap b l).

Lemma not_in_empty : forall {A} (b : A), ~ pheap_in b Empty.
Proof.
  intros A b phi.
  inversion phi.
Qed.

Inductive pheap_correct {A} (cmp : A -> A -> bool) : pheap A -> Prop :=
| E_correct : pheap_correct cmp Empty
| H_correct : forall b l, Forall (pheap_correct cmp) l ->
                          (forall c, pheap_in c (Heap b l)-> cmp b c = true) ->
                          pheap_correct cmp (Heap b l).

Definition find_min {A} (h : pheap A) : option A :=
  match h with
    | Empty => None
    | Heap a _ => Some a
  end.

Definition cmp_ordering {A} (cmp : A -> A -> bool) :=
  (forall a, cmp a a = true) /\
  (forall a b c, cmp a b = true -> cmp b c = true -> cmp a c = true) /\
  (forall a b, cmp a b = true -> cmp b a = true -> a = b) /\
  (forall a b, cmp a b = true \/ cmp b a = true).

Lemma find_min_spec : forall {A} (b : A) cmp h,
                           cmp_ordering cmp ->
                           pheap_correct cmp h ->
                           pheap_in b h ->
                           exists a,
                             Some a = find_min h /\
                             cmp a b = true.
Proof.
  intros A b cmp h [refl [trans [antisym comp]]] corr b_in.

  inversion corr as [| B C D E G];
    [ contradict b_in;
      replace h with (@Empty A);
      apply not_in_empty
    | exists B;
      split;
      [ auto
      | apply E;
        rewrite -> G;
        auto ]].
Qed.

Function merge {A} (cmp : A -> A -> bool) (g h : pheap A) :=
  match g with
    | Empty => h
    | Heap a g2 =>
      match h with
        | Empty => g
        | Heap b h2 =>
          match cmp a b with
            | true => Heap a (h :: g2)
            | false => Heap b (g :: h2) 
          end
      end
  end.
  
Lemma merge_spec : forall {A} cmp (b : A) g h,
                     (pheap_in b g \/ pheap_in b h) <->
                     pheap_in b (merge cmp g h).
Proof.
  intros A cmp b g h.
  split.
  intro bgh.
  destruct bgh as [bg | bh].  
  destruct bg as [g' g''|B C D].
  destruct h as [|h' h''].
  simpl.
  econstructor.
  simpl.
  destruct (cmp g' h').
  econstructor.
  econstructor.
  econstructor.
  eauto.
  econstructor.
  destruct h as [|h' h''] eqn:hd.
  simpl.
  econstructor.
  eauto.
  eauto.
  simpl.
  destruct (cmp C h') eqn:ch.
  eapply L_in.
  apply in_cons.
  eauto.
  eauto.

  eapply L_in.
  eapply in_eq.
  eapply L_in.
  eauto.
  eauto.

  (* TODO: without copypaste *)
  destruct bh as [h' h''|B C D].
  destruct g as [|g' g''].
  simpl.
  econstructor.
  simpl.
  destruct (cmp g' h').
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  destruct g as [|g' g''] eqn:gd.
  simpl.
  econstructor.
  eauto.
  eauto.
  simpl.
  destruct (cmp g' C) eqn:gc.
  eapply L_in.
  apply in_eq.
  econstructor.
  eauto.
  eauto.

  eapply L_in.
  apply in_cons.
  eauto.
  eauto.

  intro phbgh.
  destruct g as [|g' g''].
  simpl in phbgh.
  auto.

  destruct h as [|h' h''].
  simpl in phbgh.
  auto.

  simpl in phbgh.
  destruct (cmp g' h') eqn:gh.
  inversion phbgh.
  apply or_introl.
  constructor.

  match goal with
    | Q : In h _ |- _ => inversion Q
  end.
  match goal with
    | Q : Heap h' h'' = h, R : pheap_in _ h |- _ => rewrite <- Q in R; auto
  end.

  apply or_introl.
  eapply L_in.
  eauto.
  eauto.
  
  inversion phbgh.
  apply or_intror.
  econstructor.

  match goal with
    | Q : In h _ |- _ => inversion Q
  end.
  match goal with
    | Q : Heap g' g'' = h, R : pheap_in _ h |- _ => rewrite <- Q in R; auto
  end.
  
  apply or_intror.
  eapply L_in.
  eauto.
  eauto.
Qed.

Lemma merge_correct : forall {A} cmp (g h : pheap A),
                        cmp_ordering cmp ->
                        pheap_correct cmp g ->
                        pheap_correct cmp h ->
                        pheap_correct cmp (merge cmp g h).
Proof.
  intros A cmp g h [refl [trans [antisym comp]]] cor_g cor_h.
  destruct g as [|g' g''].
  auto.
  destruct h as [|h' h''].
  auto.
  simpl.
  destruct (cmp g' h') eqn:gh.
  apply H_correct.
  apply Forall_cons.
  auto.

  inversion cor_g as [|x l corr_g' ing [xg' lg'']]; auto.

  intros c cin;
  inversion cin as [a l ac [cg' lhp]|a b php lphp inph phc ac [bg' lhp]];
  [ auto
  | inversion inph as [X | X];
    [ rewrite <- X in phc;
      inversion phc as [d lpa dc [ch' lpah'']|
                        d e pha lpa inh'' phin dc [eh' phah'']];
      [ auto
      | apply (trans g' h' c);
        [ auto
        | inversion cor_h as [|x l corr_h' ing [xh' lh'']];
          apply ing; econstructor; eauto ]]
    | inversion phc as [d lpa dc [ch' lpah'']|
                        d e pha lpa inh'' phin dc [eh' phah'']];
      ( inversion cor_g as [|x l corr_g' ing [xg' lg'']];
        [ apply ing;
          econstructor;
          eauto ] ) ]].

  constructor;
    [ constructor; [auto | inversion cor_h; auto]
    | assert (cmphg : cmp h' g' = true);
      [  destruct (comp h' g') as [|Y];
        [ trivial
        | rewrite -> Y in gh; inversion gh]  
       | intros c cin;
         inversion cin as [a l ac [cg' lhp]|a b php lphp inph phc ac [bg' lhp]];
         [ auto
         | inversion inph as [X | X];
           [ rewrite <- X in phc;
             inversion phc as [d lpa dc [ch' lpah'']|
                               d e pha lpa inh'' phin dc [eh' phah'']];
             [ auto
             | apply (trans h' g' c);
               [ auto
               | inversion cor_g as [|x l corr_g' ing [xg' lg'']];
                 [ apply ing; econstructor; eauto ]]]
           | inversion cor_h as [|x l corr_h' ing [xh' lh'']];
             apply ing; econstructor; eauto ]]]].
Qed.

Function insert {A} (cmp : A -> A -> bool) (b : A) (h : pheap A) :=
  merge cmp (Heap b nil) h.

Lemma insert_spec :
  forall {A} (cmp : A -> A -> bool) (a b : A) (h : pheap A),
    cmp_ordering cmp ->
    (pheap_in a (insert cmp b h) <-> (a = b \/ pheap_in a h)).
Proof.
  intros ? ? a b ? ord.
  split;
    [ intro ain;
      destruct (proj2 (merge_spec cmp a (Heap b nil) h) ain) as [X | X];
      [ apply or_introl;
        inversion X;
        [ reflexivity
        | match goal with | Q : In _ nil |- _ => inversion Q end ]
      | auto ]
    | intro x;
      assert (k : pheap_in a (Heap b nil) \/ pheap_in a h);
      [ destruct x as [ab | ah];
        [ apply or_introl;
          rewrite -> ab;
          constructor
        | auto ]
      | apply merge_spec;
        auto ]].
Qed.  

Lemma insert_correct :
  forall {A} (cmp : A -> A -> bool) (b : A) (h : pheap A),
    cmp_ordering cmp ->
    pheap_correct cmp h ->
    pheap_correct cmp (insert cmp b h).
Proof.
  intros ? ? ? ? ord ?.
  apply merge_correct.
  auto.
  econstructor.
  econstructor.
  intros c cin.
  inversion cin.
  destruct ord.
  auto.
  match goal with
    | Q : In _ nil |- _ => inversion Q
  end.
  auto.
Qed.  

Fixpoint merge_pairs {A} (cmp : A -> A -> bool) (l : list (pheap A)) :=
  match l with
    | nil => Empty
    | (a :: nil) => a
    | (a :: b :: l') => merge cmp (merge cmp a b) (merge_pairs cmp l')
  end.

Lemma merge_pairs_correct :
  forall {A} (cmp : A -> A -> bool) (l : list (pheap A)),
    cmp_ordering cmp ->
    Forall (pheap_correct cmp) l -> pheap_correct cmp (merge_pairs cmp l).
Proof.
  intros A cmp l cmpo.
  revert l.
  refine (fix f l All :=
            match l as L return (l=L->_) with
              | nil => fun eq => _
              | (a :: nil) => fun eq => _
              | (a :: b :: l') => fun eq => _
            end eq_refl);
    [ simpl;
      constructor
    | idtac
    | idtac ].

  simpl.
  rewrite -> eq in All.
  inversion All.
  auto.

  rewrite -> eq in All.
  inversion All.
  match goal with
    | H : Forall (pheap_correct cmp) (b :: l') |- _ =>
      inversion H
  end.
  simpl.
  eapply merge_correct.
  auto.
  eapply merge_correct.
  auto.
  auto.
  auto.
  apply f.
  auto.
Qed.

Lemma merge_pairs_lemma :
  forall {A} (cmp : A -> A -> bool) (l : list (pheap A)) b,
    Exists (pheap_in b) l -> pheap_in b (merge_pairs cmp l).
Proof.
  intros A cmp.
  
  refine (fix f l b x :=
            match l as L return l=L->_ with
              | nil => fun eq => _
              | (a :: nil) => fun eq => _
              | (a :: b :: l') => fun eq => _
            end eq_refl);
    [ rewrite -> eq in x;
      inversion x
    | simpl;
      rewrite -> eq in x;
      inversion x;
      [ auto
      | match goal with | X : Exists _ nil |- _ => inversion X end ]
    | idtac].
  
  simpl;
  erewrite <- merge_spec;
  erewrite <- merge_spec;
  rewrite -> eq in x.

  
  inversion x;
  [ auto
  | match goal with | X : Exists _ (?B :: l') |- _ => inversion X end;
    auto;
    apply or_intror;
    apply f;
    auto ].
Qed.

Function delete_min {A} (cmp : A -> A -> bool) (h : pheap A) :=
  match h with
    | Empty => None
    | Heap a b => Some (merge_pairs cmp b)
  end.

Lemma delete_min_spec_2 : forall {A} cmp (g : pheap A),
                            None = delete_min cmp g -> g = Empty.
Proof.
  intros A cmp g none.
  destruct g.
  reflexivity.
  inversion none.
Qed.

Lemma cmp_eqdec : forall {A} (cmp : A -> A -> bool),
                    cmp_ordering cmp ->
                    forall (a b : A), {a = b} + {a <> b}.
Proof.
  intros A cmp [refl [trans [antisym comp]]].
  intros a b.
  destruct (cmp a b) eqn:ab.
  destruct (cmp b a) eqn:ba.
  apply left.
  apply antisym; auto.
  apply right.
  intro Q.
  rewrite -> Q in ba.
  rewrite -> refl in ba.
  inversion ba.
  apply right.
  intro Q.
  rewrite -> Q in ab.
  rewrite -> refl in ab.
  inversion ab.
Qed.

Lemma delete_min_spec_1 : forall {A} (cmp : A -> A -> bool) g h,
                            cmp_ordering cmp ->
                            pheap_correct cmp h ->
                            Some g = delete_min cmp h ->
                            forall b, pheap_in b h ->
                                      (pheap_in b g \/ Some b = find_min h).
Proof.
  intros A cmp g h ord cor_ha gdm b hin.

  destruct h as [|a l].
  inversion hin.
  destruct (cmp_eqdec cmp ord a b) as [abeq | abneq];
    [ rewrite -> abeq; auto | idtac ].

  apply or_introl.
  inversion gdm.
  inversion hin.
  contradict abneq.
  auto.

  apply merge_pairs_lemma.
  apply Exists_exists.
  eexists; split; eauto.
Qed.

Lemma delete_min_correct : forall {A} cmp (g h : pheap A),
                        cmp_ordering cmp ->
                        pheap_correct cmp h ->
                        Some g = delete_min cmp h ->
                        pheap_correct cmp g.
Proof.
  intros A cmp g h ord ch gh.
  destruct h.
  inversion gh.
  inversion gh.
  apply merge_pairs_correct.
  auto.
  inversion ch.
  auto.
Qed.
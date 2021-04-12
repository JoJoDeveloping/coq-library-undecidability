(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10UPC H10UPC_undec.
From Undecidability.FOL Require Import Util.Syntax Util.Deduction Util.Tarski Util.Kripke Util.Syntax_facts.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.


(* ** Validity *)

(**
Idea: The special star (#) has the following properties:
n ~ p: n is left component of p
p ~ n: p is right component of p
p ~ p: the special relationship of H10UPC
n ~ m: n = m. Special case n=0, m=1: 
          The instance h10 of H10UPC is a yes-instance.
          This is to facilitate Friedman translation
*)


Set Default Proof Using "Type".
Set Default Goal Selector "!".

Inductive syms_func : Type := .

Instance sig_func : funcs_signature :=
  {| syms := syms_func; ar_syms := fun f => match f with end|}.

Inductive syms_pred := sPr.

Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := fun P => 2 |}.

Notation Pr t t' := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).


Section Utils.

  Definition c2_full (x:nat) : {y:nat | x * S x = y+y}.
  Proof. 
    induction x as [|x [y' IH]].
    - exists 0. lia.
    - exists (y'+x+1). nia.
  Defined.

  Definition c2 (x:nat) := match (c2_full x) with exist _ y _ => y end.

  Definition c2_descr (x:nat) : x * S x = c2 x + c2 x.
  Proof.
  unfold c2. now destruct (c2_full x).
  Qed. 

  Definition h10upc_sem_direct (c : h10upc) :=
    match c with 
      | ((x, y), (z1, z2)) => 
          1 + x + y = z1 /\ y * (1 + y) = z2 + z2
    end.

  Lemma h10upc_inv (a b c d : nat) : h10upc_sem_direct ((a,S b),(c,d)) -> 
           {c':nat & {d':nat & h10upc_sem_direct ((a,b),(c',d')) 
                               /\ S c' = c /\ d' + b + 1 = d}}.
  Proof.
  intros [Hl Hr].
  exists (a + S b). exists (c2 b).
  repeat split.
  - lia.
  - apply c2_descr.
  - lia.
  - enough (2*(c2 b + b + 1) = d+d) by nia. rewrite <- Hr.
    cbn. rewrite Nat.mul_comm. cbn. symmetry.
    pose (c2_descr b) as Hb. nia.
  Qed.

  Lemma h10_rel_irref (p:nat*nat) : ~ (h10upc_sem_direct (p,p)).
  Proof.
  intros H. destruct p as [a b]. cbn in H. lia.
  Qed.

  Definition highest_var (x:h10upc) := match x with ((a,b),(c,d)) => Nat.max a (Nat.max b (Nat.max c d)) end.
  Lemma highest_var_descr (x:h10upc) : let hv := highest_var x in match x with ((a,b),(c,d)) => a <= hv /\ b <= hv /\ c <= hv /\ d <= hv end.
  Proof.
  destruct x as [[a b] [c d]]. cbn. repeat split; lia.
  Qed.

  Fixpoint highest_var_list (x:list h10upc) := match x with nil => 0 | x::xr => Nat.max (highest_var x) (highest_var_list xr) end.
  Lemma highest_var_list_descr (x:list h10upc) (h:h10upc) : In h x ->  highest_var h <= highest_var_list x.
  Proof.
  induction x as [|hh x IH].
  - intros [].
  - intros [hhh|hx].
    + cbn. rewrite hhh. lia.
    + cbn. specialize (IH hx). lia.
  Qed.

  Fixpoint highest_num (env: nat -> nat) (n:nat) : nat := match n with 0 => env 0 | S n => Nat.max (env (S n)) (highest_num env n) end.
  Lemma highest_num_descr (env:nat -> nat) (n:nat) (m:nat) : m <= n -> env m <= highest_num env n.
  Proof.
  induction n as [|n IH].
  - intros Hm. assert (m=0) as Hm0. 1:lia. cbn. rewrite Hm0. lia.
  - intros HmSn. cbn. destruct (Nat.eq_dec (S n) m) as [Heq|Hneq].
    + rewrite <- Heq. lia.
    + assert (m <= n) as Hmn. 1:lia. specialize (IH Hmn). lia.
  Qed.

  Lemma it_shift (X:Type) (f:X->X) v n : it f (S n) v = it f n (f v).
  Proof.
  induction n as [|n IH].
  - easy.
  - cbn. f_equal. apply IH.
  Qed.

  Lemma it_add (X:Type) (f:X->X) v n m : it f n (it f m v) = it f (n+m) v.
  Proof.
  induction n as [|n IH].
  - easy.
  - cbn. f_equal. apply IH.
  Qed.
End Utils.

Section validity.

  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  (* All are placed in a context where $0 is the 0 constant and $1, $2 are arbitrary but fixed *)
  (** We do a Friedman translation, where this represents falsity *)
  Definition wFalse t:= Pr $t $(S t).
  (** We use a stronger version of falsity, which is <-> False in our standart model, to ease writing eliminators *)
  Definition sFalse := ∀ ∀ Pr $0 $1.
  (** Friedman not *)
  Definition Not k t := k --> wFalse t.
  (** $k is a number *)
  Definition N k := Pr $k $k.
  (** $k is a pair *)
  Definition P' k := (N k) --> sFalse.
  (** If $k is a pair ($l,$r), where $l, $r are numbers, then t. *)
  Definition P k l r c := P' k --> N l --> N r --> Pr $l $k --> Pr $k $r --> c.
  (** if the pairs $pl = ($a,$b), $pr = ($c,$d) are in relation, then t *)
  Definition rel pl pr a b c d t := P pl a b (P pr c d (Pr $pl $pr --> t)).
  (** There exist (Friedman translated) pairs relating ($a,$b) to ($c,$d) *)
  Definition erel a b c d t := Not (∀ ∀ P 0 (2+a) (2+b) 
                                        (P 1 (2+c) (2+d)  
                                         (Pr $0 $1 --> wFalse (2+t)))) t.
  (** Axiom 1 - zero is a number *)
  Definition F_zero := N 0.
  (** Axiom 2 - we can build (left) successors: for each pair (a,0) we have a pair (S a, 0) *)
  Definition F_succ_left := ∀ N 0 --> Not (∀ ∀ ∀ P 2 3 4
                                                 (P 0 1 4
                                                  (Pr $2 $0 --> wFalse 5))) 2.
  (** Axiom 3 - we can build right successors: (x,y)#(a,b) -> (x,S y)#(S a,S (b+y)) *)
  Definition F_succ_right := ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀         (*8 pairs *)
                             ∀ ∀ ∀ ∀ ∀ ∀ ∀           (* 0 x 1 y 2 a 3 b 4 c 5 y' 6 a' 15 zero-const*)
                             rel 7 8 0 1 2 3      (* (x,y) # (a,b) *)
                            (rel 9 10 3 1 4 3     (* (b,y) # (c,b) *)
                            (rel 11 12 1 15 5 15  (* (y,0) # (y',0) *)
                            (rel 13 14 2 15 6 15  (* (a,0) # (a'0) *)
                            (erel 0 5 6 4 16))))     (* (x,y') # (a',c) *).
  (** Generate n all quantifiers around i *)
  Definition emplace_forall (n:nat) (i:form) := it (fun k => ∀ k) n i.

  (** Translate our formula, one relation at a time *) 
  Definition translate_single (h:h10upc) nv := 
          match h with ((a,b),(c,d)) => 
            erel a b c d nv end.
  (** Translate an entire instance of H10UPC, assuming a proper context *)
  Fixpoint translate_rec (t:form) (nv:nat) (l:list h10upc) := 
          match l with nil => t
                     | l::lr => translate_single l nv --> translate_rec t nv lr end.
  (** Actually translate the instance of H10UPC, by creating a proper context *)
  Definition translate_constraints (x:list h10upc) := 
    let nv := S (highest_var_list x)
    in (emplace_forall nv (translate_rec (Pr $(S nv) $(2+nv)) (S nv) x)) --> Pr $1 $2.

  (** The actual reduction instance. If h10 is a yes-instance of H10UPC, this formula is valid and vice-versa
      The 3 variables are the zero constant and two arbitrary values which define the atomic predicate for 
      Friedman translation. *)
  Definition F := ∀ ∀ ∀ F_zero --> F_succ_left --> F_succ_right --> translate_constraints h10.

  Section Transport.
    (** The solution to cs *)
    Context (φ: nat -> nat). 
    (** Proof that it actually is a solution *)
    Context (Hφ : forall c, In c h10 -> h10upc_sem φ c). 
    Class model := {
      D : Type;
      I : interp D;
      rho : env D;
      zero : D; cr1 : D; cr2 : D;
      vF_zero : (zero .: cr2 .: cr1 .: rho) ⊨ F_zero;
      vF_succ_left : (zero .: cr2 .: cr1 .: rho) ⊨ F_succ_left;
      vF_succ_right : (zero .: cr2 .: cr1 .: rho) ⊨ F_succ_right;
    }.
    Context (valid_in : model).
    Instance model_II : interp D. exact I. Defined.
    Notation i_Pr i i' :=
      (@i_atom _ _ _ I sPr (Vector.cons _ i _ (Vector.cons _ i' _ (Vector.nil _)))).
    
    Definition isNum (d:D) := i_Pr d d.
    Definition D_wFalse := i_Pr cr2 cr1.
    Definition D_Not k := k -> D_wFalse.
    Definition isPair' d := (isNum d) -> forall a b, i_Pr b a.
    Definition isPair (p l r:D) := isNum l /\ isNum r /\ isPair' p /\ i_Pr l p /\ i_Pr p r.
    
    Definition repr_nums f n := f 0 = zero /\ forall m:nat, m < n -> 
              (exists (pl pr:D), isNum (f (S m)) /\ isPair pl (f m) zero /\ isPair pr (f (S m)) zero /\ i_Pr pl pr).

    Definition constr_nums (n:nat) : D_Not (forall f:nat -> D, repr_nums f n -> D_wFalse).
    Proof.
    induction n as [|n IH]; intros H.
    - apply (H (fun _ => zero)). split. 1: easy. intros m HH. exfalso. lia.
    - apply IH. intros f [IH0 IHfs].
      apply (@vF_succ_left valid_in (f n)); fold sat.
      + destruct n as [|n].
        * rewrite IH0. apply vF_zero.
        * destruct (IHfs n) as [pl [pr [HH _]]]. 1:lia. easy.
      + cbn. intros pl sn pr Ppl Nfn Nz Pfnl Plz Ppr Nsn Nz' Psnr Prz Pplpr.
        pose (fun m => if m =? S n then sn else f m) as f'.
        apply (H f'). split.
        * easy.
        * intros m Hm. destruct (Nat.eq_dec n m) as [Heq|Hneq].
          -- exists pl, pr. rewrite <- Heq.
             assert (f' (S n) = sn) as ->. 1: unfold f'; assert (S n =? S n = true) as ->. 
             1:apply Nat.eqb_eq; lia. 1:easy.
             assert (f' n = f n) as  ->. 1:unfold f'; assert (n =? S n = false) as ->. 
             1:apply Nat.eqb_neq; lia. 1:easy.
             now repeat split.
          -- destruct (IHfs m) as [pl' [pr' Hplplr']]. 1:lia.
             exists pl', pr'.
             assert (f' (S m) = f (S m)) as ->. 1: unfold f'; assert (S m =? S n = false) as ->.
             1:apply Nat.eqb_neq; lia. 1:easy.
             assert (f' m = f m) as  ->. 1:unfold f'; assert (m =? S n = false) as ->.
             1:apply Nat.eqb_neq; lia. 1:easy.
             easy. 
    Qed. 

    Lemma repr_num_isNum (f:nat -> D) (n:nat) (m:nat) : repr_nums f n -> m <= n -> isNum (f m).
    Proof.
    intros [Hzero Hrepr] Hnm.
    destruct m as [|m].
    - rewrite Hzero. apply vF_zero.
    - destruct (Hrepr m Hnm) as [pl [pr [H _]]]. apply H.
    Qed.

    Lemma constr_rel (a b c d : nat) (f:nat -> D) (n:nat) : 
        repr_nums f n 
     -> b <= n -> a <= n -> c <= n -> d <= n
     -> h10upc_sem_direct ((a,b),(c,d)) 
     -> D_Not (forall pl pr, isPair pl (f a) (f b) 
                         -> isPair pr (f c) (f d) 
                         -> i_Pr pl pr -> D_wFalse).
    Proof.
    intros Hreprnums Hbn.
    pose proof Hreprnums as Hrepr_nums.
    destruct Hreprnums as [Zrepr Hrepr].
    induction b as [|b IH] in a,c,d|-*; intros Han Hcn Hdn Habcd.
    - cbn in Habcd. assert (c = S a /\ d = 0) as [Hc Hd]. 1:lia.
      rewrite Hc, Hd, !Zrepr in *.
      destruct (Hrepr a) as [pl [pr [Ha [Hpl Hpr]]]]. 1:lia. 
      intros Hcr. now apply (Hcr pl pr).
    - destruct (@h10upc_inv a b c d Habcd) as [c' [d' [Habcd' [Hc' Hd']]]].
      rewrite <- Hc', <- Hd' in *. 
      assert (h10upc_sem_direct ((d',b),(d'+b+1,d'))) as Hdb.
      + split. 1: now lia. apply Habcd'.
      + intros Hcr.
        apply (IH a c' d'). 1-3: lia. 1: easy. 
        intros pab pc'd' Hpab Hpc'd' Hpabc'd'.
        apply (IH d' (d'+b+1) d'). 1-3: lia. 1: easy. 
        intros pd'b pd'bd' Hpd'b Hpd'bd' Hpd'bd'bd'.
        destruct (Hrepr b) as [pb [pb' [Nsb [Hpb [Hpb' Hpbpb']]]]]. 1:lia.
        destruct (Hrepr c') as [pc [pc' [Nsc [Hpc [Hpc' Hpcpc']]]]]. 1:lia.
        pose proof (@vF_succ_right valid_in pc' pc pb' pb pd'bd' pd'b pc'd' pab
                    (f (S c')) (f (S b)) (f(d' + b + 1)) (f d') (f c') (f b) (f a)) as sr.
        apply sr; cbn; fold isNum.
        1-5: now destruct Hpab as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpc'd' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        1-5: now destruct Hpd'b as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpd'bd' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        1-5: now destruct Hpb as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpb' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        1-5: now destruct Hpc as [H'l [H'r [H'p [H'pl H'pr]]]].
        1-5: now destruct Hpc' as [H'l [H'r [H'p [H'pl H'pr]]]].
        1: easy.
        intros pScsum paSb HpaSb H'a H'Sb HlpaSb HrpaSb HpScsum H'Sc H'dsum HlpScsum HrpScsum Hprel.
        apply (Hcr paSb pScsum). all: now repeat split.
    Qed.
    
    Lemma prove_emplace_forall (n:nat) (i:form) (r:env D) :
    r ⊨ emplace_forall n i
    -> forall f, (fun v => if v <? n then f v else r (v-n)) ⊨ i.
    Proof.
    induction n as [|n IH] in r|-*.
    - cbn. intros H f. apply (sat_ext I (rho := r) (xi:=fun v => r(v-0)) i).
      + intros x. now rewrite Nat.sub_0_r.
      + easy.
    - intros H f. cbn. cbn in H. specialize (H (f n)). specialize (IH (f n .: r) H f). 
      eapply (Tarski.sat_ext I (xi := (fun v : nat => if v <? n then f v else (f n .: r) (v - n))) i).
      + intros x. destruct (Nat.eq_dec x n) as [Hxn|Hnxn].
        * destruct (Nat.leb_le x n) as [_ Hr]. specialize (Hr ltac:(lia)). rewrite Hr. 
          destruct (Nat.ltb_ge x n) as [_ Hr2]. specialize (Hr2 ltac:(lia)). rewrite Hr2.
          assert (x-n=0) as Hxn0. 1:lia. rewrite Hxn0. cbn. now f_equal.
        * destruct (x <? n) as [|] eqn:Hxn.
          -- apply (Nat.ltb_lt) in Hxn. assert (x <=? n = true) as Hxn2. 1: apply Nat.leb_le; lia.
             rewrite Hxn2. easy.
          -- apply (Nat.ltb_ge) in Hxn. assert (x <=? n = Datatypes.false) as Hxn2. 1: apply Nat.leb_gt; lia.
             rewrite Hxn2. assert (x-n = S(x-S n))  as Hxn3. 1:lia. rewrite Hxn3. cbn. easy.
      + easy.
    Qed.

    Lemma prove_constraints : (zero .: cr2 .: cr1 .: rho) ⊨ translate_constraints h10.
    Proof using φ Hφ.
    pose (S (highest_var_list h10)) as h10vars.
    unfold translate_constraints. fold h10vars.
    pose (highest_num φ h10vars) as h10max.
    pose (@constr_nums h10max) as Hcons.
    intros HH. cbn.
    pose proof (prove_emplace_forall HH) as H. clear HH.
    apply Hcons. intros f Hrepr. specialize (H (fun t => f (φ t))).
    pose ((fun v : nat => if v <? h10vars then (fun t : nat => f (φ t)) v else (zero .: cr2 .: cr1 .: rho) (v - h10vars))) as newenv.
    assert (newenv (S h10vars) = cr2) as Hne1.
    1: {unfold newenv. assert (S h10vars <? h10vars = false) as ->. 1: apply Nat.leb_gt; now lia.
        assert (S h10vars - h10vars = 1) as ->. 1:now lia. easy. }
    assert (newenv (S (S h10vars)) = cr1) as Hne2.
    1: {unfold newenv. assert (S (S h10vars) <? h10vars = false) as ->. 1: apply Nat.leb_gt;lia.
        assert (S (S h10vars) - h10vars = 2) as ->. 1:now lia. easy. }
    fold newenv in H.
    assert (forall c:h10upc, In c h10 -> newenv ⊨ translate_single c (S h10vars)) as Hmain.
    - intros [[a b][c d]] Hin. 
      pose (@highest_var_list_descr h10 ((a,b),(c,d)) Hin) as Habcdmax.
      cbn in Habcdmax. intros HH. 
      cbn. rewrite Hne1, Hne2.
      apply (@constr_rel (φ a) (φ b) (φ c) (φ d) f h10max). 1:easy.
      1-4: eapply highest_num_descr; lia.
      1: apply (@Hφ ((a,b),(c,d)) Hin).
      intros pab pcd [Ha [Hb [Hab [Haab Hbab]]]] [Hc [Hd [Hcd [Hccd Hdcd]]]] Hpp. 
      assert (forall k:nat, k < h10vars -> newenv k = f (φ k)) as Hvars.
      1:{ unfold newenv, h10vars. intros k Hk. destruct (Nat.ltb_lt k h10vars) as [_ Hr]. 
          fold h10vars. now rewrite Hr. }
      cbn in HH. rewrite Hne1, Hne2, (Hvars a), (Hvars b), (Hvars c), (Hvars d) in HH.
      2-5: unfold h10vars;lia.
      now apply (@HH pcd pab).
    - induction h10 as [|hx hr IH] in H,Hmain|-*.
      + cbn in H. rewrite Hne1,Hne2 in H. apply H.
      + apply IH. 
        * cbn in H. apply H. apply Hmain. now left.
        * intros c Hhr. apply Hmain. now right. 
    Qed.
  End Transport.

  Lemma transport : H10UPC_SAT h10 -> valid F.
  Proof.
    intros [φ Hφ].
    intros D I rho.
    intros cr1 cr2 zero.
    intros H_zero H_succ_left H_succ_right.
    eapply (@prove_constraints φ Hφ (Build_model H_zero H_succ_left H_succ_right)).
  Qed. 

  Section InverseTransport.

    Inductive dom : Type := Num : nat -> dom | Pair : nat  -> nat -> dom.
    Definition dom_rel (a : dom) (b:dom) : Prop := match (a,b) with
    | (Num  0, Num  1) => H10UPC_SAT h10
    | (Num n1, Num n2) => n1 = n2
    | (Num n1, Pair x2 y2) => n1 = x2
    | (Pair x1 y1, Num n2) => n2 = y1
    | (Pair x1 y1, Pair x2 y2) => h10upc_sem_direct ((x1, y1), (x2, y2))
    end.

    Global Instance IB : interp (dom).
    Proof using h10.
      split; intros [] v.
      exact (dom_rel (Vector.hd v) (Vector.hd (Vector.tl v))).
    Defined.

    Lemma IB_sFalse rho : rho ⊨ (∀ ∀ Pr $0 $1) <-> False.
    Proof.
    split.
    * intros H. specialize (H (Num 0) (Num 1)). cbn in H. congruence.
    * intros [].
    Qed.
    Opaque sFalse.

    Lemma IB_sNot rho f : rho ⊨ (f --> sFalse) <-> ~ (rho ⊨ f).
    Proof.
    split.
    * intros H. cbn in H. now rewrite IB_sFalse in H.
    * intros H. cbn. now rewrite IB_sFalse.
    Qed.

    Lemma IB_wFalse rho t : rho ⊨ wFalse t <-> dom_rel (rho t) (rho (S t)).
    Proof.
    split.
    * intros H. apply H.
    * intros H. apply H.
    Qed.
    Opaque wFalse.

    Lemma IB_Not rho f t : rho ⊨ Not f t <-> ((rho ⊨ f) -> rho ⊨ wFalse t).
    Proof.
    split.
    * intros H. cbn in H. now rewrite IB_wFalse in H.
    * intros H. cbn. now rewrite IB_wFalse.
    Qed.
    Opaque Not.

    Definition rho_canon (rho : nat -> dom) := rho 0 = Num 0.

    Lemma IB_F_zero rho : rho_canon rho -> rho ⊨ F_zero.
    Proof.
      intros H0. cbn. now rewrite !H0.
    Qed.


    Lemma IB_N_e rho i n : rho i = n -> rho ⊨ N i -> {m:nat | Num m = n}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * now exists m.
    * exfalso. cbn in H. rewrite Hrho in H. apply (@h10_rel_irref (a,b) H).
    Qed.

    Lemma IB_N_i rho i n : rho i = Num n -> (rho) ⊨ N i.
    Proof. cbn. intros ->. now destruct n as [|n'] eqn:Heq.
    Qed.
    Opaque N.

    Lemma IB_P'_e rho i n : rho i = n -> rho ⊨ P' i -> {a:nat & {b:nat & n = Pair a b}}.
    Proof.
    intros Hrho H. destruct n as [m|a b].
    * exfalso. unfold P' in H. rewrite IB_sNot in H. eapply H, IB_N_i, Hrho.
    * now exists a, b.
    Qed.

    Lemma IB_P'_i rho i a b : rho i = (Pair a b) -> rho ⊨ P' i.
    Proof.
    unfold P'. rewrite IB_sNot. intros Hrho H. destruct (@IB_N_e rho i (Pair a b)). 
    1-2:easy. congruence.
    Qed.
    Opaque P'.

    Lemma IB_P_e rho p l r ip il ir c :
        rho ip = p -> rho il = l -> rho ir = r
     -> rho ⊨ P ip il ir c -> {a:nat & {b:nat & p = Pair a b /\ l = Num a /\ r = Num b}} 
     -> rho ⊨ c.
    Proof.
    intros Hp Hl Hr H [a [b [Hp' [Hl' Hr']]]]. cbn in H. 
    rewrite Hp, Hl, Hr, Hp', Hl', Hr' in H. cbn in H. apply H.
    - eapply IB_P'_i. now rewrite Hp, Hp'.
    - eapply IB_N_i. now rewrite Hl, Hl'.
    - eapply IB_N_i. now rewrite Hr, Hr'.
    - now destruct a.
    - easy.
    Qed.

    Lemma IB_P_i rho ip il ir c : (forall a b, rho ip = (Pair a b) 
                                 -> rho il = (Num a) -> rho ir = (Num b) -> rho ⊨ c)
                                 -> rho ⊨ P ip il ir c.
    Proof.
    intros Hplrc. intros [pa [pb Hp]]%(IB_P'_e (n:=rho ip))
                         [la Ha]%(IB_N_e (n:=rho il))
                         [rb Hb]%(IB_N_e (n:=rho ir)) Hpl Hpr. 2-4: easy.
    cbn in Hpl, Hpr. rewrite Hp,<-Ha,<-Hb  in *. apply (@Hplrc la rb); destruct la; congruence.
    Qed.
    Opaque P.

    Lemma IB_F_succ_left rho : rho_canon rho -> rho ⊨ F_succ_left.
    Proof.
      intros H0. unfold F_succ_left. intros n [m Hnm]%(IB_N_e (n:=n)). 2:easy. 
      rewrite IB_Not. cbn. intros Hc.
      specialize (Hc (Pair m 0) (Num (S m)) (Pair (S m) 0)).
      eapply IB_P_e in Hc. 2-4:easy. 2: exists m, 0; cbn; auto.
      eapply IB_P_e in Hc. 2-4:easy. 2: exists (S m), 0; cbn; auto.
      rewrite IB_wFalse. unfold scons.
      cbn in Hc. rewrite IB_wFalse in Hc. unfold scons in Hc.
      apply Hc; split; lia.
    Qed.

    Lemma IB_rel_e rho ipl ipr ia ib ic id t : rho ⊨ rel ipl ipr ia ib ic id t 
                -> {a&{b&{c&{d|rho ipl=Pair a b
                            /\ rho ipr = Pair c d
                            /\ rho ia=Num a
                            /\ rho ib=Num b
                            /\ rho ic=Num c
                            /\ rho id=Num d
                            /\ h10upc_sem_direct ((a,b),(c,d))}}}} 
                -> rho ⊨ t.
    Proof.
    intros H [a [b [c [d [Hpl [Hpr [Ha [Hb [Hc [Hd Habcd]]]]]]]]]].
    unfold rel in H.
    eapply IB_P_e in H. 2-4: easy. 2: exists a, b; cbn; auto.
    eapply IB_P_e in H. 2-4: easy. 2: exists c, d; cbn; auto.
    apply H. cbn. rewrite Hpl, Hpr. easy.
    Qed.

    Lemma IB_rel_i rho ipl ipr ia ib ic id t :
                ({a&{b&{c&{d|rho ipl=Pair a b
                            /\ rho ipr = Pair c d
                            /\ rho ia=Num a
                            /\ rho ib=Num b
                            /\ rho ic=Num c
                            /\ rho id=Num d
                            /\ h10upc_sem_direct ((a,b),(c,d))}}}} -> rho ⊨ t)
             -> rho ⊨ rel ipl ipr ia ib ic id t.
    Proof.
    intros H.
    apply IB_P_i. intros a b Hpl Ha Hb.
    apply IB_P_i. intros c d Hpr Hc Hd.
    intros Habcd. apply H. exists a,b,c,d. cbn in Habcd. rewrite Hpl, Hpr in Habcd. now repeat split.
    Qed.

    Lemma IB_F_succ_right rho : rho_canon rho -> rho ⊨ F_succ_right.
    Proof.
      intros H0. unfold F_succ_right. intros p1 p2 p3 p4 p5 p6 p7 p8 a' y' c b a y x.
      apply IB_rel_i. cbn. intros [nx [ny [na [nb [Hp8 [Hp7 [Hx [Hy [Ha [Hb [Hr1l Hr1r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [nb' [ny' [nc [nb'' [Hp6 [Hp5 [Hb' [Hy' [Hc [Hb'' [Hr2l Hr2r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [ny'' [z [n'y [z' [Hp4 [Hp3 [Hy'' [Hz [H'y [Hz' [Hr3l Hr3r]]]]]]]]]]].
      apply IB_rel_i. cbn. intros [na' [z'' [n'a [z''' [Hp2 [Hp1 [Ha' [Hz'' [H'a [Hz''' [Hr4l Hr4r]]]]]]]]]]].
      unfold erel. cbn.
      rewrite IB_Not. intros H.
      rewrite H0 in *.
      specialize (H (Pair n'a (nc)) (Pair nx n'y)).
      eapply IB_P_e in H. 2-4: easy. 2: exists nx, n'y; cbn; firstorder.
      eapply IB_P_e in H. 2-4: easy. 2: exists n'a, nc; cbn; firstorder.
      cbn in H. rewrite IB_wFalse in H. apply H.
      assert (z=0 /\ z' = 0 /\ z'' = 0 /\ z''' = 0) as [Hz0 [Hz01 [Hz02 Hz03]]].
      1:firstorder;congruence. cbn -[dom_rel] in H.
      rewrite Hz0, Hz01, Hz02, Hz03 in *. split.
      - assert (ny'' = ny /\ na' = na) as [HHy HHa].
        1:firstorder;congruence. lia.
      - assert (nb' = nb /\ ny' = ny /\ ny'' = ny /\ na'=na) as [HHb [HHy [HHHy HHa]]].
        1:firstorder;congruence. lia.
    Qed.

    Definition rho_descr_phi rho (φ:nat->nat) n :=
         forall k, k < n -> match rho k with Num n => n = (φ k) | _ => True end.
    Lemma IB_single_constr rho φ (n:nat) (h:h10upc) : rho_descr_phi rho φ n 
                                           -> highest_var h < n
                                           -> rho ⊨ translate_single h (S n)
                                           -> (h10upc_sem φ h -> dom_rel (rho (1+n)) (rho (2+n)))
                                           -> dom_rel (rho (1+n)) (rho (2+n)).
    Proof.
      intros Hrhophi Hmaxhall. 
      destruct h as [[a b][c d]]. unfold translate_single. cbn in Hmaxhall.
      intros Htr Hcon. unfold erel in Htr. rewrite IB_Not in Htr.
      apply Htr.
      intros p2 p1.
      apply IB_P_i. cbn. intros na nb Hp1 Ha Hb.
      apply IB_P_i. cbn. intros nc nd Hp2 Hc Hd. rewrite Hp1, Hp2.
      intros Habcd.
      apply Hcon.
      assert (na = φ a) as ->. 1: pose (@Hrhophi a) as Hp; rewrite Ha in Hp; apply Hp; lia.
      assert (nb = φ b) as ->. 1: pose (@Hrhophi b) as Hp; rewrite Hb in Hp; apply Hp; lia.
      assert (nc = φ c) as ->. 1: pose (@Hrhophi c) as Hp; rewrite Hc in Hp; apply Hp; lia.
      assert (nd = φ d) as ->. 1: pose (@Hrhophi d) as Hp; rewrite Hd in Hp; apply Hp; lia.
      apply Habcd.
    Qed. 

    Lemma IB_emplace_forall rho n i : 
        (forall f, (fun k => if k <? n then f (k) else rho (k-n)) ⊨ i)
     -> rho ⊨ emplace_forall n i.
    Proof.
      intros H.
      induction n as [|n IH] in rho,H|-*.
      - cbn. eapply (sat_ext IB (rho := rho) (xi:=fun k => rho(k-0))).
        2: apply (H (fun _ => Num 0)).
        intros x. now rewrite Nat.sub_0_r.
      - intros d.
        specialize (IH (d.:rho)). apply IH. intros f.
        eapply (sat_ext IB (xi:=fun k => if k <? S n
                                         then (fun kk => if kk =? n then d
                                         else f kk) k else (rho) (k - S n))).
        2: eapply H.
        intros x.
        destruct (Nat.eq_dec x n) as [Hxn|Hnxn].
        + destruct (Nat.ltb_ge x n) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
          destruct (Nat.ltb_lt x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt. cbn.
          assert (x-n=0) as ->. 1: lia. cbn. destruct (Nat.eqb_eq x n) as [_ HH]. now rewrite HH.
        + destruct (x <? n) eqn:Hneq.
          * destruct (Nat.ltb_lt x n) as [Hlt _]. apply Hlt in Hneq. clear Hlt.
            destruct (Nat.ltb_lt x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
            cbn. destruct (Nat.eqb_neq x n) as [_ HH]. rewrite HH. 1: easy. lia.
          * destruct (Nat.ltb_ge x n) as [Hlt _]. apply Hlt in Hneq. clear Hlt.
            destruct (Nat.ltb_ge x (S n)) as [_ Hlt]. rewrite Hlt. 2:lia. clear Hlt.
            assert (x-n=S(x-S n)) as ->. 1:lia. easy.
    Qed.
    Opaque emplace_forall. 

    Lemma IB_translate_rec rho phi f e hv : rho_descr_phi rho phi hv 
                            -> (rho ⊨ f <-> dom_rel (rho (1+hv)) (rho (2+hv)))
                            -> highest_var_list e < hv 
                            -> ((forall c, In c e -> h10upc_sem phi c) -> rho ⊨ f)
                            -> rho ⊨ translate_rec f (S hv) e.
    Proof.
    intros Hrhophi Hsat Hhv H.
    induction e as [|eh er IH] in H,Hsat,Hhv|-*.
    - apply H. intros l [].
    - cbn. intros Hts. apply IH.
      + easy.
      + cbn in Hhv. lia.
      + intros HH. rewrite Hsat. eapply (IB_single_constr (h:=eh)).
        * exact Hrhophi.
        * pose proof (@highest_var_list_descr (eh::er) eh ltac:(now left)). lia.
        * easy.
        * intros Hsem. rewrite <- Hsat. apply H. intros c [il|ir]. 2:now apply HH. congruence.
    Qed.

    Lemma IB_aux_transport rho : rho 0 = Num 0
                              -> rho 1 = Num 0
                              -> rho 2 = Num 1
                              -> rho ⊨ translate_constraints h10
                              -> H10UPC_SAT h10.
    Proof.
      intros Hrho0 Hrho1 Hrho2.
      pose ((S (highest_var_list h10))) as h10vars. 
      unfold translate_constraints. fold h10vars. intros H.
      cbn in H. rewrite Hrho1, Hrho2 in H.
      apply H. 
      apply IB_emplace_forall. intros f.
      pose (fun n => match (f n) with (Num k) => k | _ => 0 end) as phi.
      eapply (IB_translate_rec (e:=h10) (hv:=h10vars) (phi:= phi)).
      - intros x HH. destruct (Nat.ltb_lt x h10vars) as [_ Hr]. rewrite Hr. 2:easy.
        unfold phi. now destruct (f x).
      - cbn -[dom_rel Nat.leb Nat.sub]. easy.
      - lia.
      - intros HG. cbn -[dom_rel Nat.leb Nat.sub].
        destruct (Nat.ltb_ge (S h10vars) h10vars) as [_ H1]. rewrite H1. 2:lia.
        destruct (Nat.ltb_ge (S (S h10vars)) h10vars) as [_ H2]. rewrite H2. 2:lia.
        assert (S h10vars-h10vars = 1) as ->. 1:lia. 
        assert (S(S h10vars)-h10vars = 2) as ->. 1:lia.
        rewrite Hrho1, Hrho2. cbn. exists phi. easy.
    Qed.

    Lemma IB_fulfills rho : rho ⊨ F -> H10UPC_SAT h10.
    Proof.
      intros H. unfold F in H. pose (Num 0 .: Num 0 .: Num 1 .: rho) as nrho.
      assert (rho_canon nrho) as nrho_canon.
      1: split; easy.
      apply (@IB_aux_transport nrho), H. 
      - easy.
      - easy.
      - easy.
      - now apply IB_F_zero.
      - now apply IB_F_succ_left.
      - now apply IB_F_succ_right.
    Qed.
  End InverseTransport.

  Lemma inverseTransport : valid F -> H10UPC_SAT h10.
  Proof.
    intros H. apply (@IB_fulfills (fun b => Num 0)). apply H.
  Qed.

End validity.

Section provability.
  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.
  Section ProvabilityTransport.
    (** The solution to cs *)
    Context (φ: nat -> nat). 
    (** Proof that it actually is a solution *)
    Context (Hφ : forall c, In c h10 -> h10upc_sem φ c). 

    Instance lt_dec (n m : nat) : dec (n < m). Proof. 
    apply Compare_dec.lt_dec.
    Defined.
    Instance le_dec (n m : nat) : dec (n <= m). Proof. 
    apply Compare_dec.le_dec.
    Defined. 

    Ltac var_eq := cbn; f_equal; lia.

    Lemma emplace_forall_subst (n:nat) (i:form) sigma : (emplace_forall n i)[sigma] = 
          emplace_forall n (i[it up n sigma]).
    Proof.
    induction n as [|n IH] in sigma|-*.
    - easy.
    - cbn. f_equal. now rewrite IH, <- it_shift.
    Qed.

    Ltac var_comp := (unfold up,scons,funcomp).
    Ltac var_cbn := repeat (unfold up,scons,funcomp; cbn).

    Fixpoint specialize_n (n:nat) (f:nat->nat) (k:nat) := 
          match n with 0 => $k 
                     | S n => match k with 0 => $(f 0)
                                         | S k => specialize_n n (fun l => (f (S l))) k end end.

    Lemma emplace_forall_elim (n:nat) (i:form) (pos:nat->nat) A : 
        A ⊢I emplace_forall n i -> A ⊢I (i[specialize_n n pos]).
    Proof.
    intros Hpr. induction n as [|n IH] in i,pos,Hpr|-*.
    - cbn. now rewrite subst_id.
    - cbn in Hpr. enough (i[up (specialize_n n (fun l=> (pos(S l))))][$(pos 0)..] = i[specialize_n (S n) pos]) as <-.
      + apply AllE. specialize (IH (∀ i) (fun l => (pos (S l)))). apply IH.
        unfold emplace_forall. rewrite <- it_shift. cbn. apply Hpr.
      + rewrite subst_comp. apply subst_ext. intros [|k].
        * easy.
        * var_cbn. rewrite subst_term_comp. var_cbn. now rewrite subst_term_id.
    Qed.

    Definition findNum (r n:nat) := match n with 0 => r | S n => r - 2 - 3*n end.
    Definition findPairLow (r n:nat) := findNum r n + 1.
    Definition findPairHigh (r n:nat) := findNum r n - 1.
    Fixpoint chain_at (r n:nat) := 
      match n with 0 => N(findNum r n) :: nil
          | S n => N(findNum r (S n)) :: P' (findPairLow r (S n)) :: P' (findPairHigh r (S n)) :: 
                   Pr $(findPairLow r (S n)) $(findNum r 0) :: Pr $(findNum r n) $(findPairLow r (S n)) ::
                   Pr $(findPairHigh r (S n)) $(findNum r 0) :: Pr $(findNum r (S n)) $(findPairHigh r (S n)) ::
                   Pr $(findPairLow r (S n)) $(findPairHigh r (S n)) :: chain_at r n end.
    Ltac doAllE s t := match goal with [ |- ?A ⊢I ?P] => assert (P = t[s..]) as ->; [idtac|eapply AllE] end.

    Definition iter_up := it (subst_form ↑).

    Lemma iter_up_merge_r k A : map (iter_up k) (map (subst_form ↑) A) = map (iter_up (S k)) A.
    Proof.
    rewrite map_map. apply map_ext. intros a. unfold iter_up. now rewrite it_shift.
    Qed.

    Lemma iter_up_merge_l k A : map (subst_form ↑) (map (iter_up k) A) = map (iter_up (S k)) A.
    Proof.
    now rewrite map_map.
    Qed.

    Lemma iter_up_merge_plus k1 k2 A : map (iter_up k1) (map (iter_up k2) A) = map (iter_up (k1+k2)) A.
    Proof.
    rewrite map_map. apply map_ext. intros a. unfold iter_up. now rewrite it_add.
    Qed.

    Lemma iter_up_merge_z A : map (iter_up 0) A = A.
    Proof.
    now rewrite map_id.
    Qed.

    Lemma iter_up_resolve_l f k : iter_up k f = f[fun n => $(k+n)].
    Proof.
    induction k as [|k IH].
    - cbn. symmetry. apply subst_id. easy.
    - cbn. rewrite IH, subst_comp. apply subst_ext. easy.
    Qed.

    Lemma iter_up_resolve_r f k : iter_up k f = f[fun n => $(n+k)].
    Proof.
    rewrite iter_up_resolve_l. apply subst_ext. intros n. now rewrite Nat.add_comm.
    Qed.

    Lemma findNum_raise (a b c:nat) : b >= 3*c -> a + findNum b c = findNum (a + b) c.
    Proof.
    unfold findNum. induction a as [|a IH]; destruct c; lia.
    Qed.

    Lemma chain_at_raise (a b c : nat) : b >= 3 * c -> map (iter_up a) (chain_at b c) = chain_at (a+b) c.
    Proof.
    intros H. induction a as [|a IH].
    - now rewrite map_id.
    - rewrite <- iter_up_merge_l, IH. induction c as [|c IHc] in H|-*.
      + easy.
      + cbn [chain_at map]. rewrite IHc. 2:lia.
        let rec f n := match n with 0 => f_equal| S ?n' => f_equal;[idtac|f n'] end in f 7.
        4,6-8: cbn; do 3 f_equal; unfold up,funcomp; var_eq.
        * change (S a+b) with (1+(a+b)). rewrite <- (findNum_raise 1); [easy|lia].
        * cbn. unfold P',sFalse,up,funcomp,N. do 4 f_equal. 1:lia. var_eq.
        * cbn. unfold P',sFalse,up,funcomp,N. do 4 f_equal. 1:lia. var_eq.
        * cbn. do 3 f_equal; unfold up,funcomp. 2:var_eq.
          change (S (a+b)) with (1+(a+b)). rewrite (findNum_raise 1); [easy|lia].
    Qed.

    Lemma in_incl_map (X Y :Type) (f:X->Y) a l1 l2 : In a (map f l1) -> incl l1 l2 -> In a (map f l2).
    Proof.
    intros [x [Hfx Hx]]%in_map_iff l1l2. apply in_map_iff. exists x. auto.
    Qed.

    Ltac partial_map := apply incl_tl, incl_map; auto.
    Ltac iter_up_find0 := match goal with [ |- context[map (subst_form ↑) ?k] ] => rewrite <- (iter_up_merge_z k) | _ => idtac end.
    Ltac fold_iter_up := iter_up_find0; rewrite ! iter_up_merge_l, ! iter_up_merge_r.
    Definition intros_defs (a b c e f g:nat) : list form:= Pr $e $g :: Pr $f $e :: N g :: N f :: P' e :: Pr $a $c :: Pr $b $a :: N c :: N b :: P' a :: nil.
    Definition intros_P (A:list form) (a b c e f g : nat) (i:form) :
    (intros_defs a b c e f g ++ map (iter_up 2) A)  ⊢I i -> (A ⊢I ∀ ∀ P a b c (P e f g i)).
    Proof.
    intros H.
    apply AllI,AllI. fold_iter_up. 
    do 10 apply II. exact H.
    Qed.

    Lemma construct_chain_at (n:nat) HH : (n>0)
    -> incl (F_succ_right :: F_succ_left :: F_zero :: nil) HH
    -> (chain_at (3*n) n ++  map (iter_up (3*n)) HH) ⊢I wFalse (1+(3*n))
    -> HH ⊢I wFalse (1).
    Proof.
    intros Hn HHH H. induction n as [|n IH].
    - exfalso. lia. 
    - destruct n as [|n].
      + clear IH. apply (IE (phi:=(∀ (∀ (∀ P 2 (3+findNum (0) 0) (3+findNum (0) 0) (P 0 1 (3+findNum (0) 0) (Pr $2 $0 --> wFalse (4)))))))).
        * eapply (IE (phi:=N (findNum (0) 0))).
          2: apply Ctx,HHH; do 2 right; now left.
          doAllE ($(findNum 0 0)) (N 0 --> (∀ (∀ (∀ P 2 3 (4+findNum (0) 0) (P 0 1 (4+findNum 0 0) (Pr $2 $0 --> wFalse 5))))) --> wFalse (2)).
          1: easy.
          apply Ctx,HHH. right. now left.
        * apply AllI, intros_P.
          fold_iter_up. apply II.
          eapply Weak. 1:exact H. apply incl_app.
          2: do 11 apply incl_tl; reflexivity.
          cbn -[map]. 
          intros f [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[]]]]]]]]]]; rewrite <- Hf;
          let rec find n 
              := match n with 0 => now left
                            | S ?nn => (now left) + (right; find nn) end
          in find 11.
      + apply IH; [lia|clear IH].
        eapply (IE (phi:=(∀ (∀ (∀ P 2 (3+findNum (3*S n) (S n)) (3+findNum (3*S n) 0)  
                                 (P 0 1 (3+findNum (3*S n) 0) (Pr $2 $0 --> wFalse (4+3*S n)))))))). 
        * unfold F_succ_left. unfold Not. eapply IE.
          2: apply Ctx; now left.
          doAllE ($(findNum (3 * S n) (S n))) (N 0 --> 
                      (∀ (∀ (∀ P 2 3 (4+(findNum (3 * S n) 0))
                              (P 0 1 (4+(findNum (3 * S n) 0)) (Pr $2 $0 --> wFalse (5+3*S n))))))
                  --> wFalse (2+3*S n)).
          -- easy.
          -- apply Ctx. apply in_or_app. right. eapply in_incl_map. 2:exact HHH. right. left.
             rewrite iter_up_resolve_r. easy.
        * apply AllI, intros_P.
          fold_iter_up. apply II.
          assert (1+3*S(S n) = (4+3*S n)) as <- by lia.
          eapply Weak. 1:exact H. apply incl_app.
          1:  pose (S n) as n'; fold n';
              cbn -[map Nat.add Nat.sub Nat.mul n' iter_up];
              intros f [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|Hin]]]]]]]].
          1-8: rewrite <- Hf.
          -- do 4 right. left. var_eq.
          -- do 10 right. left. var_eq.
          -- do 5 right. left. var_eq.
          -- do 6 right. left. assert (3+3*n' = 3*S n') as -> by lia. repeat f_equal. cbn;lia.
          -- do 7 right. left. do 3 f_equal. 2:var_eq. erewrite findNum_raise. 2:unfold n';lia. f_equal. lia.
          -- do 1 right. left. do 3 f_equal. 2:var_eq. cbn;lia.
          -- do 2 right. left. do 3 f_equal. 1:lia. var_eq.
          -- do 0 right. left. do 3 f_equal; cbn. 2:var_eq. lia.
          -- do 11 right. rewrite map_app. apply in_or_app. left.
             1:erewrite (chain_at_raise 3). 2:lia. 1: now assert (3* S n' = 3+3*n') as <- by lia.
          -- do 11 apply incl_tl. rewrite map_app. apply incl_appr.
             rewrite iter_up_merge_plus. now assert (3 * S (S n) = (3+(3*S n))) as -> by lia.
    Qed. 
    
    Lemma chain_lower (r a b:nat) : a <= b -> 3*b <= r -> incl (chain_at r a) (chain_at r b).
    Proof.
    intros Ha Hb. assert (b=a+(b-a)) as H by lia. rewrite H in *. clear Ha. generalize dependent (b-a).
    intros ab Ha _. induction ab as [|ab IH].
    - rewrite Nat.add_0_r; reflexivity.
    - rewrite Nat.add_succ_r. cbn. do 8 apply incl_tl. apply IH; nia.
    Qed.

    Lemma chain_N (r h a : nat) : a <= h -> 3*h <= r -> In (N(findNum r a)) (chain_at r h).
    Proof.
    intros Ha Hr. apply (@chain_lower r a h). 1-2:lia. destruct a; now left. 
    Qed.

    Lemma chain_rel (r h a : nat) : a > 0 -> a <= h -> 3*h <= r -> In (Pr $(findPairLow r a) $(findPairHigh r a)) (chain_at r h).
    Proof.
    intros Ha0 Ha Hr. destruct a. 1:exfalso;lia.
    apply (@chain_lower r (S a) h). 1-2:lia. do 7 right; now left.
    Qed.

    Lemma chain_PLow (r h a : nat) A f : S a <= h -> 3*h <= r -> incl (chain_at r h) A -> A ⊢I P (findPairLow r (S a)) (findNum r a) (findNum r 0) f -> A ⊢I f.
    Proof.
    intros Ha Hr HA Hpr. 
    unfold P in Hpr.
    eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE.
    1: apply Hpr.
    all: apply Ctx, HA, (@chain_lower r (S a) h); [lia|lia|idtac].
    2,3: apply chain_N; lia.
    all: cbn [chain_at].
    - right. now left.
    - do 4 right. now left.
    - do 3 right. now left.
    Qed.

    Lemma chain_PHigh (r h a : nat) A f : S a <= h -> 3*h <= r -> incl (chain_at r h) A -> A ⊢I P (findPairHigh r (S a)) (findNum r (S a)) (findNum r 0) f -> A ⊢I f.
    Proof.
    intros Ha Hr HA Hpr. 
    unfold P in Hpr.
    eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE. 1:eapply IE.
    1: apply Hpr.
    all: apply Ctx, HA, (@chain_lower r (S a) h); [lia|lia|idtac].
    2,3: apply chain_N; lia.
    all: cbn [chain_at].
    - do 2 right. now left.
    - do 6 right. now left.
    - do 5 right. now left.
    Qed.

    Lemma chain_E_rel (r h a : nat) A f : S a <= h -> 3*h <= r -> incl (chain_at r h) A -> A ⊢I rel (findPairLow r (S a)) (findPairHigh r (S a)) (findNum r a) (findNum r 0) (findNum r (S a)) (findNum r 0) f -> A ⊢I f.
    Proof.
    intros Ha Hr HA Hpr.
    eapply IE.
    2: eapply Ctx, HA, (@chain_rel _ _ (S a)); lia.
    unfold rel in Hpr.
    apply (@chain_PHigh r h a). 1-2:lia. 1:easy.
    apply (@chain_PLow r h a). 1-2:lia. 1:easy.
    exact Hpr.
    Qed.


    Definition erel_i (a b c d t : nat) := (∀ ∀ P 0 (2+a) (2+b) 
                                            (P 1 (2+c) (2+d)
                                             (Pr $0 $1 --> wFalse (2+t)))).
    Lemma erel_II (a b c d t : nat) A : (erel_i a b c d t :: A) ⊢I wFalse t -> A ⊢I erel a b c d t.
    Proof. intros H. apply II. exact H. Qed.

    Definition erel_findNum (a b c d r:nat) := erel_i (findNum r a) (findNum r b) (findNum r c) (findNum r d) (1+r).
    Lemma erel_findNum_II (a b c d r : nat) A : (erel_findNum a b c d r :: A) ⊢I wFalse (1+r) -> A ⊢I erel (findNum r a) (findNum r b) (findNum r c) (findNum r d) (1+r).
    Proof. intros H. apply erel_II. exact H. Qed.
    Definition erel_findNum_H (a b c d pl pr rr : nat) :list form := 
         Pr $pl $pr
      :: Pr $pr $(findNum (rr) d)
      :: Pr $(findNum (rr) c) $pr
      :: N (findNum (rr) d)
      :: N (findNum (rr) c)
      :: P' pr
      :: Pr $pl $(findNum (rr) b)
      :: Pr $(findNum (rr) a) $pl
      :: N (findNum (rr) b)
      :: N (findNum (rr) a)
      :: P' pl :: nil.

    Ltac doAllI n := apply AllI; let H := fresh "H" in 
       match goal with [ |- map (subst_form ↑) ?A ⊢I ?phi ] => edestruct (@nameless_equiv_all _ _ _ intu A phi) as [n H]; rewrite H; clear H end.

    Lemma erel_findNum_ExI (a b c d r : nat) A :
    r >= 3*a -> r >= 3*b -> r >= 3*c -> r >= 3*d -> 
    (forall pl pr, (erel_findNum_H a b c d pl pr r ++ A) ⊢I wFalse (S r)) -> A ⊢I erel_findNum a b c d r .
    Proof.
    intros Ha Hb Hc Hd Hpr. unfold erel_findNum, erel_i.
    doAllI pr. cbn [subst_form]. doAllI pl.
    cbn.
    do 11 apply II. eapply Weak. 1: apply (Hpr pl pr).
    apply incl_app.
    - unfold erel_findNum_H. now repeat apply ListAutomation.incl_shift.
    - now do 11 apply incl_tl.
    Qed.

    Lemma erel_findNum_raise (a b c d r p : nat) : 
    r >= 3*a -> r >= 3*b -> r >= 3*c -> r >= 3*d ->
    iter_up p (erel_findNum a b c d r) = erel_findNum a b c d (p+r).
    Proof.
    intros Ha Hb Hc Hd. unfold erel_findNum,erel_i,P. rewrite iter_up_resolve_l. cbn [subst_form Vector.map].
    rewrite <- ! findNum_raise. 2-5:lia. cbn. rewrite ! (Nat.add_succ_r p). easy.
    Qed.

    Lemma erel_findNum_H_raise (a b c d pl pr rr p : nat) : 
    rr >= 3*a -> rr >= 3*b -> rr >= 3*c -> rr >= 3*d ->
    map (iter_up p) (erel_findNum_H a b c d pl pr rr) = erel_findNum_H a b c d (p+pl) (p+pr) (p+rr).
    Proof.
    intros Ha Hb Hc Hd. cbn. rewrite ! iter_up_resolve_l. cbn -[Nat.add]. unfold erel_findNum_H.
    rewrite ! findNum_raise. 2-5:lia. easy.
    Qed.

    Lemma erel_findNum_H_E (a b c d pl pr rr : nat) A f : 
    rr >= 3*a -> rr >= 3*b -> rr >= 3*c -> rr >= 3*d
    -> incl (erel_findNum_H a b c d pl pr rr) A 
    -> A ⊢I rel pl pr (findNum (rr) a) (findNum (rr) b) (findNum (rr) c) (findNum (rr) d) f
    -> A ⊢I f.
    Proof.
    intros Ha Hb Hc Hd HA Hpr.
    let rec rep n := match n with 0 => now left | S ?nn => right; rep nn end in
    let rec f n k := match n with 0 => apply Hpr | S ?nn => eapply IE; [f nn (S k)|apply Ctx, HA; rep k] end in f 11 0.
    Qed.

    Lemma rel_subst (p q a b c d:nat) f s ss : (forall n,s n = $(ss n)) -> (rel p q a b c d f)[s] = rel (ss p) (ss q) (ss a) (ss b) (ss c) (ss d) f[s].
    Proof.
    intros H.
    unfold rel,P,N,P'. cbn. rewrite ! H. easy.
    Qed.
    
    Lemma erel_i_subst (a b c d t:nat) s ss : (forall n,s n = $(ss n)) -> (ss (S t)) = S(ss t) -> (erel_i a b c d t --> wFalse t)[s] = erel_i (ss a) (ss b) (ss c) (ss d) (ss t) --> wFalse (ss t).
    Proof.
    intros H Hs. cbn. unfold erel_i,P,N,P',funcomp. rewrite ! H. do 20 f_equal. all: cbn; rewrite Hs; easy.
    Qed.

    Lemma erel_ereli (a b c d t:nat) : erel a b c d t = erel_i a b c d t --> wFalse t.
    Proof. easy. Qed.

    Fixpoint subst_list (l:list nat) (n:nat) := match l with nil => n | lx::lr => match n with 0 => lx | S n => subst_list lr n end end.

    Lemma emplace_forall_shift (n : nat) (f:form) : emplace_forall n (∀ f) = emplace_forall (S n) f.
    Proof. unfold emplace_forall. now rewrite it_shift. Qed.

    Lemma specialize_list (H f:form) (l:list nat) (n:nat) : 
       length l = n
    -> (H[subst_list l >> var]:: nil) ⊢I f
    -> (emplace_forall n H::nil) ⊢I f.
    Proof.
    induction l as [|lx lr IH] in n,H|-*.
    - intros <-. cbn. now erewrite subst_id.
    - intros <- Hpr. cbn [length]. specialize (IH (∀ H) (length lr) eq_refl).
      cbn in IH. rewrite emplace_forall_shift in IH.
      eapply IH, IE.
      + apply Weak with nil. 2:easy. apply II, Hpr.
      + assert (H[up (subst_list lr >> var)][$lx..] = H[subst_list (lx :: lr) >> var]) as <-.
        * rewrite subst_comp. apply subst_ext. now intros [|n].
        * apply AllE, Ctx. now left.
    Qed.
      
    Lemma prove_single (a b c d r hv: nat): 
       b <= hv -> a <= hv -> c <= hv -> d <= hv -> 3*hv <= r
    -> h10upc_sem_direct ((a,b),(c,d))
    -> (chain_at r hv ++ map (iter_up r) (F_succ_right :: F_succ_left :: F_zero :: nil)) ⊢I Not (erel_findNum a b c d r) (1+r) .
    Proof.
    intros Hb. induction b as [|b IH] in r,a,c,d,Hb|-*; intros Ha Hc Hd Hr Habcd.
    - cbn in Habcd. assert (c = S a /\ d = 0) as [Hc' Hd']. 1:lia.
      rewrite Hc', Hd'. apply II. rewrite Hc' in Hc.
      apply (@chain_E_rel r hv a). 1-2:lia.
      1: now apply incl_tl,incl_appl.
      eapply Weak with (erel_findNum a 0 (S a) 0 r::nil). 2:auto.
      unfold erel_findNum, erel_i. change (∀∀ ?e) with (emplace_forall 2 e).
      eapply specialize_list with (findPairLow r (S a)::findPairHigh r (S a)::nil).
      1:easy. apply Ctx. now left.
    - destruct (@h10upc_inv a b c d Habcd) as [c' [d' [Habcd' [Hc' Hd']]]].
      rewrite <- Hc', <- Hd' in *. 
      assert (h10upc_sem_direct ((d',b),(d'+b+1,d'))) as Hdb.
      1: split; [now lia|apply Habcd'].
      apply erel_findNum_II. eapply IE.
      1: eapply Weak; [apply (@IH a c' d' r); easy + lia | now apply incl_tl].
      apply erel_findNum_ExI. 1-4: lia. intros pab pc'd'. 
      eapply IE.
      1: eapply Weak; [apply (@IH d' (d'+b+1) d' r); lia + easy|idtac]. 
      1: now apply incl_appr; apply incl_tl.
      apply erel_findNum_ExI. 1-4: lia. intros pd'b psd'.
      apply (IE (phi:=erel_findNum a (S b) (S c') (d' + b + 1) r)).
      2: apply Ctx, in_or_app; right; apply in_or_app; right; now left.
      apply (@chain_E_rel r hv c'). 1-2:lia.
      1: now apply incl_appr, incl_appr, incl_tl, incl_appl.
      apply (@chain_E_rel r hv b). 1-2:lia.
      1: now apply incl_appr, incl_appr, incl_tl, incl_appl.
      apply (@erel_findNum_H_E d' b (d' + b + 1) d' pd'b psd' r).
      1-4: lia.
      1: now apply incl_appl.
      apply (@erel_findNum_H_E a b c' d' pab pc'd' r).
      1-4: lia.
      1: now apply incl_appr, incl_appl.
      apply Weak with (iter_up r F_succ_right::nil).
      2: cbn [map]; apply incl_appr, incl_appr, incl_tl, incl_appr; intros k [->|[]]; now left.
      unfold F_succ_right. rewrite erel_ereli.
      change (∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀ ?a) with (emplace_forall 15 a).
      erewrite iter_up_resolve_l, emplace_forall_subst.
      erewrite ! (@rel_subst _ _ _ _ _ _ _ _ (fun k => if Dec (k < 15) then k else 15 +((r + (k - 15))))).
      1: erewrite ! (@erel_i_subst _ _ _ _ _ _ (fun k => if Dec (k < 15) then k else 15 +((r + (k - 15))))).
      2,4-7: intros n; destruct (Dec _); let rec f k := match k with 0 => cbn;unfold funcomp; var_eq | S ?kk => destruct n as [|n]; [cbn;(easy+exfalso;lia)|f kk] end
           in f 15.
      2: cbn; lia.
      cbn -[subst_form findNum Nat.add emplace_forall].
      pose (
        (findNum r a)
      ::(findNum r b)
      ::(findNum r c')
      ::(findNum r d')
      ::(findNum r (d'+b+1))
      ::(findNum r (S b))
      ::(findNum r (S c'))
      ::pab::pc'd'::pd'b::psd'
      ::(findPairLow r (S b))::(findPairHigh r (S b))
      ::(findPairLow r (S c'))::(findPairHigh r (S c'))::nil) as mylist.
      eapply specialize_list with mylist.
      1:easy.
      erewrite ! (@rel_subst _ _ _ _ _ _ _ _ (subst_list mylist)).
      1: erewrite ! (@erel_i_subst _ _ _ _ _ _ (subst_list mylist)).
      2,4-7: intros n; easy.
      2: cbn; lia.
      cbn [subst_list mylist].
      change (15+?e) with (S(S(S(S(S(S(S(S(S(S(S(S(S(S(S e))))))))))))))).
      apply Ctx. left. do 3 f_equal. 1-2: cbn;lia.
      f_equal. 1-2: cbn;lia.
      unfold erel_findNum.
      do 2 f_equal; lia.
    Qed.

    Lemma it_up_resolve_hi a f b : it up a f (b+a) = it (subst_term ↑) a (f b).
    Proof.
    induction a as [|a IH].
    - var_eq.
    - rewrite Nat.add_succ_r. cbn. unfold funcomp. rewrite IH. easy.
    Qed.

    Lemma it_up_specialize_n n f b : (it (subst_term ↑) n $b)`[specialize_n n f] = $b.
    Proof.
    induction n as [|n IH] in f|-*.
    - easy.
    - erewrite <- IH at 2. cbn. rewrite subst_term_comp. apply subst_term_ext.
      cbn. easy.
    Qed.

    Lemma it_up_specialize_n_resolve n f1 f2 a : (it up n f1 >> subst_term (specialize_n n f2)) a
                                                = if Dec (a < n) then $(f2 a) else f1 (a-n).
    Proof.
    induction n as [|n IH] in f2,a|-*.
    - cbn. rewrite Nat.sub_0_r. now apply subst_term_id.
    - cbn. unfold up. fold up. destruct a as [|a].
      + easy.
      + cbn. unfold funcomp. rewrite subst_term_comp. unfold funcomp. cbn.
        unfold funcomp in IH. change (fun x => ?e x) with e.
        rewrite IH. do 2 destruct (Dec _). 2,3: exfalso;lia. all:var_eq.
    Qed.


    Lemma transport_prove : nil ⊢I F (h10:=h10).
    Proof using Hφ φ.
    unfold F. do 3 apply AllI. cbn. do 4 apply II. 
    pose ((S (highest_var_list h10))) as h10vars. fold h10vars.
    pose (highest_num φ h10vars) as h10max.
    pose proof (@highest_num_descr φ h10vars) as Hvars.
    fold h10max in Hvars.
    eapply (@construct_chain_at (S h10max)).
    1:lia. 1:now apply incl_tl.
    cbn [map]. rewrite iter_up_resolve_l, emplace_forall_subst. 
    epose proof (@emplace_forall_elim h10vars _ (fun k => findNum (3*S h10max) (φ k))) as Hpr.
    eapply IE. 2:eapply Hpr. 2:auto.
    eapply Weak. 2: apply incl_app; [apply incl_appl;reflexivity|apply incl_appr,incl_tl;reflexivity].
    apply II. clear Hpr.
    assert (h10vars >= S( highest_var_list h10)) as Hless.
    1: lia.
    induction h10 as [|h h10' IHh] in Hvars,Hφ,Hless|-*.
    - apply Ctx. left. unfold translate_rec, wFalse, subst_form,Vector.map. do 3 f_equal.
      1: change(S h10vars) with (1+h10vars).
      all: cbn [subst_term]; rewrite it_up_resolve_hi,it_up_specialize_n; var_eq. 
    - cbn -[Nat.mul h10vars chain_at subst_form].
      apply II in IHh.
      2: intros c Hc; apply Hφ; now right.
      2: exact Hvars.
      2: cbn in Hless; lia.
      eapply IE. 1: eapply Weak. 1: exact IHh.
      1: now apply incl_tl. 
      eapply IE. 1: apply Ctx; left; now cbn [subst_form].
      eapply Weak. 2: apply incl_tl; reflexivity.
      unfold translate_single. destruct h as [[a b][c d]].
      rewrite erel_ereli. clear IHh.
      rewrite subst_comp. 
      unfold Not. erewrite (@erel_i_subst _ _ _ _ _ _ (fun k : nat => if Dec (k < h10vars) then findNum (3 * S h10max) (φ k) else ((k - h10vars) + 3 * S h10max))).
      3: repeat destruct Dec; (exfalso;lia) + lia. 
      2: intros n; rewrite it_up_specialize_n_resolve; destruct (Dec _); (exfalso;lia)+var_eq.
      destruct (highest_var_descr ((a,b),(c,d))) as [Hlessa [Hlessb [Hlessc Hlessd]]]. cbn in Hless.
      do 4 (destruct Dec as [htr|hff]; [clear htr|exfalso;lia]).
      do 1 (destruct Dec; [exfalso;lia|idtac]). 
      assert (forall a,S a - a=1) as -> by (intros;lia).
      eapply Weak.
      1: eapply (prove_single (hv:=S h10max)).
      + specialize (Hvars b ltac:(lia)). lia.
      + specialize (Hvars a ltac:(lia)). lia.
      + specialize (Hvars c ltac:(lia)). lia.
      + specialize (Hvars d ltac:(lia)). lia.
      + lia.
      + apply (@Hφ ((a,b),(c,d))). now left.
      + easy.
  Qed.
  End ProvabilityTransport.


  Lemma proofTransport : H10UPC_SAT h10 -> nil ⊢I F (h10:=h10).
  Proof.
  intros [φ Hφ]. eapply transport_prove. exact Hφ.
  Qed.


  Lemma transport' : H10UPC_SAT h10 -> valid (F (h10:=h10)).
  Proof.
    intros Hh10.
    intros D I rho.
    eapply soundness.
    - now apply proofTransport.
    - easy.
  Qed.


  Lemma inverseProofTransport : nil ⊢I F (h10:=h10) -> H10UPC_SAT h10.
  Proof.
  intros H%soundness. apply inverseTransport. intros D I rho.
  apply H. easy.
  Qed.
End provability.

Section kripke_validity.
  Context {ff : falsity_flag}. 
  Context {h10 : list h10upc}.

  Lemma kripkeTransport : H10UPC_SAT h10 -> kvalid (F (h10:=h10)).
  Proof.
  intros H. 
  intros D M u rho. eapply ksoundness with nil.
  - now apply proofTransport.
  - intros a [].
  Qed.

  Lemma kripkeInverseTransport : kvalid (F (h10:=h10)) -> H10UPC_SAT h10.
  Proof.
  intros H. apply inverseTransport.
  intros D I rho. apply kripke_tarski. apply H.
  Qed.
End kripke_validity.

















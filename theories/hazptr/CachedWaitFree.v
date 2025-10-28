Require Import iris.program_logic.atomic.

From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap gset list lib.mono_nat.
From smr.lang Require Import lang proofmode notation lib.array.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.

(* plus specific modules that carry instances you need *)
Import derived_laws.bi.
Require Import Coq.ZArith.Zquot.
Require Import iris.bi.interface.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(* Begin hooks to make `lia` work witrefines_right_CG_dequeueh Nat.modulo and Nat.div *)
From Coq Require Import Arith ZArith ZifyClasses ZifyInst Lia.

Global Program Instance Op_Nat_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_Nat_mod.

Global Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

From stdpp Require Import base tactics option list gmap sorting.

From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

Notation version_off := 0 (only parsing).
Notation backup_off := 1 (only parsing).
Notation domain_off := 2 (only parsing).
Notation cache_off := 3 (only parsing).

Section code.

  Variable (hazptr : hazard_pointer_code).

  Definition new_big_atomic (n : nat) : val :=
    λ: "src" "domain",
      let: "dst" := AllocN #(S (S (S n))) #0 in
      "dst" +ₗ #backup_off <- array_clone "src" #n;;
      "dst" +ₗ #domain_off <- "domain";;
      array_copy_to ("dst" +ₗ #cache_off) "src" #n;;
      "dst".

  Definition is_valid : val :=
    λ: "l", tag "l" = #0.

  Definition read (n : nat) : val :=
    λ: "l",
      let: "ver" := !("l" +ₗ #version_off) in
      let: "data" := array_clone ("l" +ₗ #cache_off) #n in
      let: "p" := NewProph in
      let: "backup" := !("l" +ₗ #backup_off) in
      if: is_valid "backup" && (Resolve !"l" "p" #() = "ver") then (
        "data"
      ) else (
        let: "domain" := !("l" +ₗ #domain_off) in
        let: "shield" := hazptr.(shield_new) "domain" in
        let: "backup'" := hazptr.(shield_protect) "shield" ("l" +ₗ #backup_off) in
        array_copy_to "data" (untag "backup'") #n;;
        hazptr.(shield_drop) "shield";;
        "data"
      ).

  Definition array_equal : val :=
    rec: "array_equal" "l" "l'" "n" :=
      if: "n" ≤ #0 then #true
      else
        (!"l" = !"l'") && ("array_equal" ("l" +ₗ #1) ("l'" +ₗ #1) ("n" - #1)).

  Definition try_validate (n : nat) : val :=
    λ: "l" "ver" "desired" "backup'",
      if: ("ver" `rem` #2 = #0) && (CAS "l" "ver" (#1 + "ver")) then
        (* Lock was successful *)
        (* Perform update *)
        array_copy_to ("l" +ₗ #cache_off) "desired" #n;;
        (* Unlock *)
        "l" <- #2 + "ver";;
        CmpXchg ("l" +ₗ #1) "backup'" (untag "backup'");;
        #()
      else #().

  (* Definition cas (n : nat) : val :=
    λ: "l" "expected" "desired",
      let: "old" := read' n "l" in
      if: array_equal (Fst (Fst "old")) "expected" #n then 
        if: array_equal "expected" "desired" #n then #true
        else
          let: "backup'" := tag (array_clone "desired" #n) in
          let: "backup" := (Snd (Fst "old")) in
          if: (CAS ("l" +ₗ #backup) "backup" "backup'") || (CAS ("l" +ₗ #backup) (untag "backup") ("backup'")) then
            try_validate n "l" (Snd "old") "desired" "backup'";;
            #true
          else #false
      else #false. *)

End code.

Definition log := gmap nat $ agree $ (loc * list val)%type.

Definition index := gmap nat $ agree nat.

Definition indexUR := authUR $ gmapUR nat (agreeR gnameO).

Definition logUR := authUR $ gmapUR gname $ agreeR $ listO valO.

Definition requestReg := gmap nat $ agree (gname * gname * loc).
Definition requestRegUR := authUR $ gmapUR nat $ agreeR $ prodO (prodO gnameO gnameO) gname.

Definition validatedUR := authUR $ gsetUR $ gnameO.
Definition invalidUR := authUR $ gmapUR gnameO $ agreeR natO.
Definition orderUR := authUR $ gmapUR gnameO $ agreeR natO.

Definition abstractionUR := authUR $ gmapUR gnameO $ agreeR blkO.

Class cached_wfG (Σ : gFunctors) := {
  cached_wf_heapGS :: heapGS Σ;
  cached_wf_logUR :: inG Σ logUR;
  cached_wf_indexUR :: inG Σ indexUR;
  cached_wf_requestRegUR :: inG Σ requestRegUR;
  cached_wf_mono_natG :: mono_natG Σ;
  cached_wf_ghost_varG_bool :: ghost_varG Σ bool;
  cached_wf_ghost_varG_loc_val :: ghost_varG Σ (gname * list val);
  cached_wf_tokenG :: tokenG Σ;
  cached_wf_invalidUR :: inG Σ invalidUR;
  cached_wf_orderUR :: inG Σ orderUR;
  cached_wf_validatedUR :: inG Σ validatedUR;
  cached_wf_abstractonUR :: inG Σ abstractionUR;
}.

Section cached_wf.
  Context `{!cached_wfG Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition cached_wfN := N .@ "cached_wf".

  Definition casN := N .@ "cas".

  Definition readN := N .@ "read".

  Definition hazptrN := N .@ "hazptr".

  Variable (hazptr : hazard_pointer_spec Σ hazptrN).

  Lemma wp_array_equal (l l' : loc) (dq dq' : dfrac) (vs vs' : list val) :
    length vs = length vs' → Forall2 vals_compare_safe vs vs' →
    {{{ l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}
      array_equal #l #l' #(length vs)
    {{{ RET #(bool_decide (vs = vs')); l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}.
    iIntros (Hlen Hsafe Φ) "[Hl Hl'] HΦ".
    Proof.
    iInduction vs as [|v vs] "IH" forall (l l' vs' Hsafe Hlen) "HΦ".
    - wp_rec. wp_pures.
      apply symmetry, length_zero_iff_nil in Hlen as ->.
      iModIntro.
      rewrite bool_decide_eq_true_2; last done.
      iApply "HΦ". iFrame.
    - wp_rec. wp_pures.
      destruct vs' as [| v' vs']; first discriminate.
      inv Hlen. inv Hsafe.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hlrest]".
      iDestruct "Hl'" as "[Hl' Hlrest']".
      do 2 wp_load.
      wp_pures.
      destruct (decide (v = v')) as [-> | Hne].
      + rewrite (bool_decide_eq_true_2 (v' = v')); last done.
        wp_pures.
        rewrite Z.sub_1_r.
        rewrite -Nat2Z.inj_pred /=; last lia.
        iApply ("IH" $! _ _ vs' with "[//] [//] [$] [$]").
        iIntros "!> [Hlrest Hlrest']".
        iSpecialize ("HΦ" with "[$]").
        destruct (decide (vs = vs')) as [-> | Hne].
        * rewrite bool_decide_eq_true_2; last done.
          by rewrite bool_decide_eq_true_2.
        * rewrite bool_decide_eq_false_2.
          -- by rewrite bool_decide_eq_false_2.
          -- by intros [=].
      + rewrite (bool_decide_eq_false_2 (v = v')); last done.
        iSpecialize ("HΦ" with "[$]").
        wp_pures.
        destruct (decide (vs = vs')) as [-> | Hne'];
        rewrite bool_decide_eq_false_2; auto; by intros [=].
  Qed.

  (* Definition gmap_auth_own `{Countable K} {V} (γ : gname) (q : Qp) (m : gmap K V) := own (A:=gmapUR K (agreeR V)) γ (●{#q} (fmap (M:=gmap K) to_agree m)). *)

  Definition index_auth_own γᵢ (q : Qp) (index : list gname) := own γᵢ (●{#q} map_seq 0 (to_agree <$> index)).

  Definition index_frag_own' γ (index : list gname) := own γ (◯ map_seq 0 (to_agree <$> index)).

  Definition log_auth_own (γᵥ : gname) (q : Qp) (log : gmap gname (list val)) := own γᵥ (●{#q} fmap (M:=gmap gname) to_agree log).

  Definition vers_auth_own (γᵥ : gname) (q : Qp) (log : gmap gname nat) := own γᵥ (●{#q} fmap (M:=gmap gname) to_agree log).

  Definition value γ (backup : gname) (vs : list val) : iProp Σ := ghost_var γ (1/2) (backup, vs).

  Definition log_frag_own γₕ l (value : list val) := own γₕ (◯ {[l := to_agree value ]}).

  Definition vers_frag_own γ (l : gname) (ver : nat) := own γ (◯ {[l := to_agree ver]}).

  Definition index_frag_own γᵢ (i : nat) (l : gname) := own γᵢ (◯ {[i := to_agree l]}).

  Definition validated_auth_own (γ : gname) (q : Qp) (validated : gset gname) := own γ (●{#q} validated).

  Definition validated_frag_own (γ : gname) (l : gname) := own γ (◯ {[ l ]}).

  Definition abstraction_auth_own (γᵥ : gname) (q : Qp) (log : gmap gname blk) := own γᵥ (●{#q} fmap (M:=gmap gname) to_agree log).

  (* Maximum value over a map *)
  Definition map_max `{Countable K} (m : gmap K nat) : nat :=
    map_fold (λ _ ver acc, max ver acc) 0 m.

  Lemma le_max_iff_nat (x y z : nat) :
    x ≤ Nat.max y z ↔ x ≤ y ∨ x ≤ z.
  Proof.
    split.
    - intros H.
      destruct (le_ge_dec y z) as [Hyz|Hzy].
      + rewrite (Nat.max_r y z) // in H. auto.
      + rewrite (Nat.max_l y z) in H; auto with lia.
    - intros [Hy|Hz].
      + eapply Nat.le_trans; first done. apply Nat.le_max_l.
      + eapply Nat.le_trans; first done. apply Nat.le_max_r.
  Qed.

  Lemma map_max_spec {K} `{Countable K} (m : gmap K nat) k v :
    m !! k = Some v → v ≤ map_max m.
  Proof.
    unfold map_max.
    intros Hlookup.
    induction m using map_first_key_ind.
    - done.
    - rewrite map_fold_insert_first_key //.
      destruct (decide (i = k)) as [<- | Hne].
      + rewrite lookup_insert in Hlookup.
        simplify_eq. rewrite le_max_iff_nat. auto.
      + rewrite lookup_insert_ne // in Hlookup.
        rewrite le_max_iff_nat. auto.
  Qed.

  Lemma index_auth_update (l : gname) γ (index : list gname) :
    index_auth_own γ 1 index ==∗
      index_auth_own γ 1 (index ++ [l]) ∗ index_frag_own γ (length index) l.
  Proof.
    iIntros "H●".
    rewrite /index_auth_own /index_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length index)
          (x := to_agree l).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length index) with (O + length (to_agree <$> index)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma index_frag_alloc i l γ index q :
    index !! i = Some l →
      index_auth_own γ q index ==∗
        index_auth_own γ q index ∗ index_frag_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma index_frag_alloc' i l γ index q :
    index !! i = Some l →
      index_auth_own γ q index ==∗ index_frag_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma validated_auth_update (l : gname) (γ : gname) (validated : gset gname) :
    validated_auth_own γ 1 validated ==∗
      validated_auth_own γ 1 ({[ l ]} ∪ validated) ∗ validated_frag_own γ l.
  Proof.
    iIntros "H●".
    (* rewrite /validated_auth_own /log_frag_own. *)
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply (gset_local_update _ _ ({[ l ]} ∪ validated)). set_solver. }
    iFrame. iModIntro.
    rewrite /validated_frag_own.
    iPoseProof (own_mono with "H◯") as "H"; last done.
    apply auth_frag_mono. set_solver.
  Qed.

  Lemma validated_auth_frag_alloc (l : gname) (γ : gname) (q : Qp) (validated : gset gname) :
    l ∈ validated →
      validated_auth_own γ q validated ==∗ validated_auth_own γ q validated ∗ validated_frag_own γ l.
  Proof.
    iIntros (Hfresh) "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (auth_update_dfrac_alloc _ _ {[ l ]}). set_solver. }
    by iFrame.
  Qed.

  Lemma validated_auth_frag_dup (γ : gname) (q : Qp) (validated : gset gname) :
    validated_auth_own γ q validated ==∗ validated_auth_own γ q validated ∗ own γ (◯ validated).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := validated).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma validated_auth_frag_agree γ dq l validated :
    validated_auth_own γ dq validated -∗
      validated_frag_own γ l -∗
        ⌜l ∈ validated⌝.
  Proof.
    iIntros "●H ◯H".
    iCombine "●H ◯H" gives %(_ & H & _)%auth_both_dfrac_valid_discrete.
    set_solver.
  Qed.

  (* Lemma validated_auth_alloc_empty : |==> ∃ γ, validated_auth_own γ 1 ∅)%I. *)

  Lemma log_auth_update (l : gname) (value : list val) (γₕ : gname) (log : gmap gname (list val)) :
    log !! l = None →
      log_auth_own γₕ 1 log ==∗
        log_auth_own γₕ 1 (<[l := value]>log) ∗ log_frag_own γₕ l value.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /log_auth_own /log_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := l)
          (x := to_agree value).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite fmap_insert.
    by iFrame.
  Qed.

  Lemma vers_auth_update (l : gname) (ver : nat) (γ : gname) (log : gmap gname nat) :
    log !! l = None →
      vers_auth_own γ 1 log ==∗
        vers_auth_own γ 1 (<[l := ver]>log) ∗ vers_frag_own γ l ver.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /log_auth_own /log_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := l)
          (x := to_agree ver).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite -fmap_insert.
    by iFrame.
  Qed.

  Lemma vers_frag_alloc_singleton vers l i γ q :
    vers !! l = Some i →
      vers_auth_own γ q vers ==∗
        vers_auth_own γ q vers ∗ vers_frag_own γ l i.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[ l := to_agree i ]}).
      { apply _. }
      apply singleton_included_l with (i := l).
      exists (to_agree i). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma log_frag_alloc i value γₕ log q :
    log !! i = Some value →
      log_auth_own γₕ q log ==∗
        log_auth_own γₕ q log ∗ log_frag_own γₕ i value.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree value]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree value). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma log_auth_frag_agree γₕ q log i value : 
    log_auth_own γₕ q log -∗
      log_frag_own γₕ i value -∗
        ⌜log !! i = Some value⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

  Lemma index_auth_frag_agree (γ : gname) (i : nat) (l : gname) (index : list gname) (q : Qp) : 
    index_auth_own γ q index -∗
      index_frag_own γ i l -∗
        ⌜index !! i = Some l⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Lemma prefix_lookup {A} (xs ys : list A) :
    (∀ i x, xs !! i = Some x → ys !! i = Some x) → xs `prefix_of` ys.
  Proof.
    rewrite /prefix. generalize dependent ys.
    induction xs as [| x xs IH].
    - eauto.
    - intros ys Hpoint. simpl.
      destruct ys as [| y ys].
      { specialize (Hpoint 0 x). intuition. discriminate. }
      epose proof (IH ys _) as [ys' ->]. Unshelve.
      + specialize (Hpoint 0 x). simpl in *.
        intuition. simplify_eq. eauto.
      + intros i x' Hlookup.
        specialize (Hpoint (S i) x').
        auto.
  Qed.

  Lemma map_seq_0_included {A} (l l' : list A) :
    map_seq (M := gmap nat A) O l ⊆ map_seq O l' →
      l `prefix_of` l'.
  Proof.
    intros Hincl.
    rewrite map_subseteq_spec in Hincl.
    apply prefix_lookup.
    intros i x.
    do 2 rewrite -lookup_map_seq_0.
    apply Hincl.
  Qed.

  Lemma fmap_to_agree_included_subseteq (m m' : gmap gname (gname * list val)) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma fmap_to_agree_included_subseteq' (m m' : gmap gname nat) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma fmap_to_agree_included_subseteq'' (m m' : gmap nat gname) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma index_auth_frag_agree' (γ : gname) (q : Qp) (index index' : list gname) : 
    index_auth_own γ q index -∗
      index_frag_own' γ index' -∗
        ⌜index' `prefix_of` index⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & Hvalid & _)%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply map_seq_0_included, fmap_to_agree_included_subseteq''.
    by repeat rewrite fmap_map_seq.
  Qed.

  Definition registry γᵣ (requests : list (gname * gname * gname)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  (* Fragmental ownership over a single request *)
  Definition registered γᵣ i (γₗ γₑ l : gname) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, γₑ, l)]})).

  Lemma registry_update γₗ γₑ l γ requests : 
    registry γ requests ==∗ 
      registry γ (requests ++ [(γₗ, γₑ, l)]) ∗ registered γ (length requests) γₗ γₑ l.
  Proof.
    iIntros "H●".
    rewrite /registry /registered.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length requests)
          (x := to_agree (γₗ, γₑ, l)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  (* The authoritative view of the request registry must agree with its fragment *)
  Lemma registry_agree γᵣ (requests : list (gname * gname * gname)) (i : nat) γₗ γₑ ver :
    registry γᵣ requests -∗
      registered γᵣ i γₗ γₑ ver -∗
        ⌜requests !! i = Some (γₗ, γₑ, ver)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Definition log_tokens (log : gmap gname (list val)) : iProp Σ :=
    [∗ map] γ ↦ _ ∈ log, token γ.

  Definition read_inv (γ γᵥ γₕ γᵢ γ_val γz γ_abs : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (log : gmap gname (list val)) (abstraction : gmap gname blk) (actual cache : list val) (γ_backup γ_backup' : gname) (backup backup' : blk) (index : list gname) (validated : gset gname) (t : nat),
      (* Physical state of version *)
      (l +ₗ version_off) ↦ #ver ∗
      (* backup, consisting of boolean to indicate whether cache is valid, and the backup pointer itself *)
      (l +ₗ backup_off) ↦{# 1/2} #(Some (Loc.blk_to_loc backup) &ₜ t) ∗
      (* Half ownership of logical state *)
      ghost_var γ (1/4) (γ_backup, actual) ∗
      (* Every value of BigAtomic is unboxed *)
      ⌜Forall val_is_unboxed actual⌝ ∗
      (* Shared read ownership of backup *)
      hazptr.(Managed) γz backup γ_backup len (λ (p : blk) lv γ_p, ⌜lv = actual⌝) ∗
      (* The most recent version is associated with some other backup pointer *)
      ⌜last index = Some γ_backup'⌝ ∗
      (* If the backup is validated, then the cache is unlocked, the logical state is equal to the cache,
         and the backup pointer corresponding to the most recent version is up to date *)
      ⌜if (decide (t = 0)) then Nat.Even ver ∧ actual = cache ∧ γ_backup = γ_backup' else True⌝ ∗
      (* Big atomic is of fixed size *)
      ⌜length actual = len⌝ ∗ 
      ⌜length cache = len⌝ ∗
      (* Every logged value is of correct length *)
      ⌜map_Forall (λ _  value, length value = len) log⌝ ∗
      (* The version number is twice (or one greater than twice) than number of versions *) 
      (* For every pair of (backup', cache') in the log, we have ownership of the corresponding points-to *)
      log_tokens log ∗
      (* The last item in the log corresponds to the currently installed backup pointer *)
      ⌜log !! γ_backup = Some actual⌝ ∗
      (* Store half authoritative ownership of the log in the read invariant *)
      log_auth_own γₕ (1/2) log ∗
      (* Auth ownership of abstraction mapping physical to logical pointers *)
      abstraction_auth_own γ_abs 1 abstraction ∗
      ⌜abstraction !! γ_backup = Some backup⌝ ∗
      ⌜is_Some (abstraction !! γ_backup')⌝ ∗
      (* The is a mapping in the index for every version *)
      ⌜length index = S (Nat.div2 (S ver))⌝ ∗
      (* Because the mapping from versions to log entries is injective, the index should not contain duplicates *)
      ⌜NoDup index⌝ ∗
      (* Moreover, every index should be less than the length of the log (to ensure every version
         corresponds to a valid entry) *)
      ⌜Forall (.∈ dom log) index⌝ ∗
      (* Ownership of at least half of the index *)
      index_auth_own γᵢ (1/4) index ∗
      (* Ownership of at least half of the counter *)
      mono_nat_auth_own γᵥ (1/4) ver ∗
      (* Ownership of at least half of the physical state of the cache *)
      (l +ₗ 2) ↦∗{# 1/2} cache ∗
      (* If the version is even, the the value of the backup corresponding to the 
         stores the cache. Otherwise it must not be valid *)
      ⌜if Nat.even ver then log !! γ_backup' = Some cache else t ≠ 0⌝ ∗
      (* If the version is even, we have full ownership of index and logical state of version *)
      (if Nat.even ver then index_auth_own γᵢ (1/4) index ∗ mono_nat_auth_own γᵥ (1/4) ver ∗(l +ₗ 2) ↦∗{# 1/2} cache else True) ∗
      (* Auth ownership of all pointers that have been validated *)
      validated_auth_own γ_val 1 validated ∗
      (* The backup pointer is in the set of validated pointer iff it has actually been validated *)
      ⌜γ_backup ∈ validated ↔ t = 0⌝ ∗
      (* All pointers validated have also been logged *)
      ⌜validated ⊆ dom log⌝ ∗
      ⌜dom log = dom abstraction⌝.

  Definition AU_cas (Φ : val → iProp Σ) γ (expected desired : list val) (lexp ldes : loc) dq dq' : iProp Σ :=
       AU <{ ∃∃ backup actual, value γ backup actual }>
            @ ⊤ ∖ ↑N, ∅
          <{ if bool_decide (actual = expected) then ∃ backup', value γ backup' desired else value γ backup actual,
             COMM lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #(bool_decide (actual = expected)) }>.

  (* Definition log_tokens (log : gmap gname (list val)) : iProp Σ :=
    [∗ map] γ ↦ _ ∈ log, token γ. *)

  (* Definition cas_inv (Φ : val → iProp Σ) (γ γₑ γₗ γₜ γ_p : gname) γd (lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val) s p R size : iProp Σ :=
      ((lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #false) ∗ (∃ b : bool, ghost_var γₑ (1/2) b) ∗ ghost_var γₗ (1/2) false) (* The failing write has already been linearized and its atomic update has been consumed *)
    ∨ (£ 1 ∗ AU_cas Φ γ expected desired lexp ldes dq dq' ∗ ghost_var γₑ (1/2) true ∗ ghost_var γₗ (1/2) true ∗ Shield hazptr γd s (Validated p γ_p R size))
    ∨ (token γₜ ∗ (∃ b : bool, ghost_var γₑ (1/2) b) ∗ ∃ b : bool, ghost_var γₗ (1/2) b).  The failing write has linearized and returned *)

  (* Lemma log_tokens_impl log l γ :
    fst <$> log !! l = Some γ → log_tokens log -∗ token γ.
  Proof.
    rewrite -lookup_fmap lookup_fmap_Some.
    iIntros (([? values] & <- & Hbound)) "Hlog".
    iPoseProof (big_sepM_lookup with "Hlog") as "H /=".
    { done. }
    done. 
  Qed. *)

  Lemma log_tokens_impl log l value :
    log !! l = Some value → log_tokens log -∗ token l.
  Proof.
    iIntros (Hbound) "Hlog".
    iPoseProof (big_sepM_lookup with "Hlog") as "H /=".
    { done. }
    done. 
  Qed.

  Lemma log_tokens_singleton l  value :
    log_tokens {[ l := value ]} ⊣⊢ token l.
  Proof.
    rewrite /log_tokens big_sepM_singleton //.
  Qed.
(* 
  Definition request_inv (γ γₗ γₑ γ_exp : gname) (lactual : loc) (actual : list val) (abstraction : gmap gname loc) : iProp Σ :=
    ∃ lexp, ⌜abstraction !! γ_exp = Some lexp⌝ ∗
      ghost_var γₗ (1/2) (bool_decide (lactual = lexp)) ∗
      ∃ (Φ : val → iProp Σ) (γₜ : gname) (lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val),
        ghost_var γₑ (1/2) (bool_decide (actual = expected)) ∗
        inv casN (cas_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired). *)

  (* Definition registry_inv γ γ_actual lactual actual (requests : list (gname * gname * loc)) (used : gset loc) : iProp Σ :=
    [∗ list] '(γₗ, γₑ, lexp) ∈ requests, ∃ (γ_exp : gname), 
    request_inv γ γₗ γₑ lactual lexp actual used. *)

  (* Lemma registry_inv_mono γ backup expected requests used used' : 
    used ⊆ used' →
      registry_inv γ backup expected requests used -∗
        registry_inv γ backup expected requests used'.
  Proof.
    iIntros (Hsub) "Hreginv".
    iInduction requests as [|[[γₗ γₑ] lexp] requests] "IH".
    - done.
    - rewrite /registry_inv /=.
      iDestruct "Hreginv" as "[Hreqinv Hreginv]".
      iPoseProof ("IH" with "Hreginv") as "$".
      rewrite /request_inv.
      iDestruct "Hreqinv" as "(%Hin & $ & $)".
      iPureIntro. set_solver.
  Qed. *)

  Lemma array_frac_add l dq dq' vs vs' : length vs = length vs' → l ↦∗{dq} vs -∗ l ↦∗{dq'} vs' -∗ l ↦∗{dq ⋅ dq'} vs ∗ ⌜vs = vs'⌝.
  Proof.
    iIntros (Hlen) "Hl Hl'".
    iInduction vs as [|v vs] "IH" forall (l vs' Hlen).
    - symmetry in Hlen. rewrite length_zero_iff_nil in Hlen. simplify_list_eq. by iSplit.
    - destruct vs' as [|v' vs']; simplify_list_eq.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hls]".
      iDestruct "Hl'" as "[Hl' Hls']".
      iPoseProof (pointsto_combine with "Hl Hl'") as "[Hl ->]".
      iFrame.
      iPoseProof ("IH" with "[//] [$] [$]") as "[Hl <-]".
      by iFrame.
  Qed.

  Lemma array_pointsto_valid l dq vs : length vs > 0 → l ↦∗{dq} vs -∗ ⌜✓ dq⌝.
  Proof.
    iIntros (Hpos) "Hl".
    destruct vs as [|v vs].
    { inv Hpos. }
    rewrite array_cons.
    iDestruct "Hl" as "[Hl _]".
    iApply (pointsto_valid with "Hl").
  Qed.

  Lemma array_pointsto_pointsto_persist l vs vs' :
    length vs = length vs' → length vs > 0 → 
      l ↦∗ vs -∗ l ↦∗□ vs' -∗ False.
  Proof.
    iIntros (Hlensame Hlenpos) "Hl Hl'".
    iPoseProof (array_frac_add with "Hl Hl'") as "[Hl %HJ]".
    { done. }
    by iDestruct (array_pointsto_valid with "Hl") as %Hvalid.
  Qed.

  Definition gmap_injective {K A} `{Countable K} (m : gmap K A) :=
    ∀ i j v, m !! i = Some v → m !! j = Some v → i = j.
(* 
  Definition read_inv (γ γᵥ γₕ γᵢ γ_val : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (log : gmap loc (gname * list val)) (actual cache : list val) (marked_backup : val) (backup backup' : loc) (index : list gname) (validated : gset loc),
      (* Physical state of version *)
      l ↦ #ver ∗
      (* backup, consisting of boolean to indicate whether cache is valid, and the backup pointer itself *)
      (l +ₗ 1) ↦{# 1/2} marked_backup ∗
      (* Half ownership of logical state *)
      ghost_var γ (1/4) (backup, actual) ∗
      (* Every value of BigAtomic is unboxed *)
      ⌜Forall val_is_unboxed actual⌝ ∗
      (* Shared read ownerhip of backup *)
      backup ↦∗□ actual ∗
      (* The most recent version is associated with some other backup pointer *)
      ⌜last index = Some backup'⌝ ∗
      (* If the backup is validated, then the cache is unlocked, the logical state is equal to the cache,
         and the backup pointer corresponding to the most recent version is up to date *)
      ⌜marked_backup = InjLV #backup ∨ marked_backup = InjRV #backup ∧ Nat.Even ver ∧ actual = cache ∧ backup = backup'⌝ ∗
      (* Big atomic is of fixed size *)
      ⌜length actual = len⌝ ∗ 
      ⌜length cache = len⌝ ∗
      (* Every logged value is of correct length *)
      ⌜map_Forall (λ _ '(_, value), length value = len) log⌝ ∗
      (* The version number is twice (or one greater than twice) than number of versions *) 
      (* For every pair of (backup', cache') in the log, we have ownership of the corresponding points-to *)
      log_tokens log ∗
      (* The last item in the log corresponds to the currently installed backup pointer *)
      ⌜snd <$> log !! backup = Some actual⌝ ∗
      (* Store half authoritative ownership of the log in the read invariant *)
      log_auth_own γₕ (1/2) log ∗
      (* The is a mapping in the index for every version *)
      ⌜length index = S (Nat.div2 (S ver))⌝ ∗
      (* Because the mapping from versions to log entries is injective, the index should not contain duplicates *)
      ⌜NoDup index⌝ ∗
      (* Moreover, every index should be less than the length of the log (to ensure every version
         corresponds to a valid entry) *)
      ⌜Forall (.∈ dom log) index⌝ ∗
      (* Ownership of at least half of the index *)
      index_auth_own γᵢ (1/4) index ∗
      (* Ownership of at least half of the counter *)
      mono_nat_auth_own γᵥ (1/4) ver ∗
      (* Ownership of at least half of the physical state of the cache *)
      (l +ₗ 2) ↦∗{# 1/2} cache ∗
      (* If the version is even, the the value of the backup corresponding to the 
         stores the cache. Otherwise it must not be valid *)
      ⌜if Nat.even ver then snd <$> log !! backup' = Some cache else marked_backup = InjLV #backup⌝ ∗
      (* If the version is even, we have full ownership of index and logical state of version *)
      (if Nat.even ver then index_auth_own γᵢ (1/4) index ∗ mono_nat_auth_own γᵥ (1/4) ver ∗(l +ₗ 2) ↦∗{# 1/2} cache else True) ∗
      (* Auth ownership of all pointers that have been validated *)
      validated_auth_own γ_val 1 validated ∗
      (* The backup pointer is in the set of validated pointer iff it has actually been validated *)
      ⌜if bool_decide (backup ∈ validated) then marked_backup = InjRV #backup else marked_backup = InjLV #backup⌝ ∗
      (* All pointers validated have also been logged *)
      ⌜validated ⊆ dom log⌝. *)

  (* Definition gmap_mono (order : gmap gname nat) (loc loc' : loc) :=
    ∀ i j, 
      order !! loc = Some i → 
        order !! loc' = Some j →
          i < j. *)

  (* Lemma gmap_mono_alloc (l : loc) (i : nat) (order : gmap gname nat) (index : list gname) :
    l ∉ index →
      StronglySorted (gmap_mono order) index →
        StronglySorted (gmap_mono (<[l := i]>order)) index.
  Proof.
    induction index as [|loc' index IH].
    - intros. constructor.
    - intros [Hne Hnmem]%not_elem_of_cons Hsorted.
      inv Hsorted.
      constructor.
      + auto.
      + clear IH H1.
        induction index as [| loc'' index IH'].
        * constructor.
        * inv H2. rewrite not_elem_of_cons in Hnmem.
          destruct Hnmem as [Hne' Hnmem].
          constructor.
          { rewrite /gmap_mono.
            intros j k.
            do 2 rewrite lookup_insert_ne //. auto. }
          { auto. }
  Qed.

  Lemma StronglySorted_subseteq (order order' : gmap gname nat) (index : list gname) :
    order ⊆ order' →
      Forall (.∈ dom order) index →
        StronglySorted (gmap_mono order) index →
          StronglySorted (gmap_mono order') index.
  Proof.
    intros Hsub Hdom Hssorted.
    induction index as [| l index IH].
    - constructor.
    - inv Hdom. inv Hssorted. constructor.
      + auto.
      + clear IH H3.
        induction index as [| l' index IH].
        * constructor.
        * inv H2. inv H4.
          constructor.
          { intros i j Hi Hj.
            apply elem_of_dom in H1 as [i' Hi'].
            apply elem_of_dom in H3 as [j' Hj'].
            rewrite map_subseteq_spec in Hsub.
            apply Hsub in Hi' as Hi''.
            apply Hsub in Hj' as Hj''.
            simplify_eq.
            by apply H2. }
          { auto. }
  Qed.

  Lemma StronglySorted_impl {A} (Q R : A → A → Prop) (l : list A) :
    (∀ x y, Q x y → R x y) →
      StronglySorted Q l →
        StronglySorted R l.
  Proof.
    intros Hweak Hsorted.
    induction Hsorted.
    - constructor.
    - constructor.
      + done.
      + eapply Forall_impl; eauto.
  Qed. 

  Lemma StronglySorted_snoc {A} (R : A → A → Prop) (xs : list A) (y : A) :
    StronglySorted R xs →
      Forall (λ x, R x y) xs →
        StronglySorted R (xs ++ [y]).
  Proof.
    induction xs as [|x xs IH]; intros Hssorted Hord.
    - repeat constructor.
    - inv Hssorted. inv Hord. simpl. constructor.
      + by apply IH.
      + rewrite Forall_app; auto.
  Qed. *)

  (* Definition cached_wf_inv (γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ : gname) (l : loc) : iProp Σ :=
    ∃ (ver : nat) log (actual : list val) (marked_backup : val) (backup : loc) requests (vers : gmap gname nat) (index : list gname) (order : gmap gname nat) (idx : nat),
      (* Ownership of remaining quarter of logical counter *)
      mono_nat_auth_own γᵥ (1/2) ver ∗
      (* Ownership of the backup location *)
      (l +ₗ 1) ↦{# 1/2} marked_backup ∗
      (* Owernship of the logical state *)
      ghost_var γ (1/4) (backup, actual) ∗
      (* Backup is exactly the logical state  *)
      ⌜snd <$> log !! backup = Some actual⌝ ∗
      (* Own other half of log in top-level invariant *)
      log_auth_own γₕ (1/2) log ∗
      (* Other 1/4 of logical state in top-level invariant *)
      (* Ownership of request registry *)
      registry γᵣ requests ∗
      (* State of request registry *)
      registry_inv γ backup actual requests (dom log) ∗
      (* Auth ownership of version mapping *)
      vers_auth_own γ_vers 1 vers ∗
      (* domain of versions is contained in domain of log *)
      ⌜dom vers ⊂ dom log⌝ ∗
      (* Only atomics after the first have read in invalid version after being swapped in *)
      ⌜if bool_decide (1 < size log) then
        (∃ ver' : nat,
          (* Version at which backup was swapped in *)
          vers !! backup = Some ver' ∧
          (* It is a lower bound on the current version *)
          ver' ≤ ver ∧
          (* The version at which the current backup was swapped in is an upper bound on the versions of all previous backups *)
          map_Forall (λ _ ver'', ver'' ≤ ver') vers ∧
          (* If the version at which the backup was swapped in is the current version, then the backup cannot be validated *)
          if bool_decide (ver = ver') then marked_backup = InjLV #backup else True)
      else vers = ∅⌝ ∗
      (* Own other half of index *)
      index_auth_own γᵢ (1/2) index ∗
      (* Most recently cached backup *)
      (* ⌜last index = Some backup'⌝ ∗ *)
      (* Auth ownership of order sequence *)
      vers_auth_own γₒ 1 order ∗
      (* The ordering binds every logged backup *)
      ⌜dom order = dom log⌝ ∗
      (* The order is injective, establishing a total order on backup pointers *)
      ⌜gmap_injective order⌝ ∗
      (* The current backup is ordered *)
      ⌜order !! backup = Some idx⌝ ∗
      (* And so is the old backup corresponding to the cache *)
      (* ⌜order !! backup' = Some idx'⌝ ∗
      (* The current backup is indeed more recent than the cached backup *)
      ⌜idx' ≤ idx⌝ ∗ *)
      (* Cache versions are associated with monotonically increasing backups *)
      ⌜StronglySorted (gmap_mono order) index⌝ ∗
      (* The order of the current backup is an upper bound on all others *)
      ⌜map_Forall (λ _ idx', idx' ≤ idx) order⌝. *)

  Global Instance pointsto_array_persistent l vs : Persistent (l ↦∗□ vs).
  Proof.
    rewrite /Persistent.
    iIntros "P".
    iInduction vs as [|v vs] "IH" forall (l).
    - rewrite array_nil. by iModIntro.
    - rewrite array_cons.
      iDestruct "P" as "[#Hl Hrest]".
      iPoseProof ("IH" with "Hrest") as "Hvs".
      by iFrame "#".
  Qed.

  Lemma backup_logged `{Countable K} {V} (log : gmap K V) (index : list K) (backup' : K) : Forall (.∈ dom log) index → last index = Some backup' → is_Some (log !! backup').
  Proof.
    rewrite Forall_lookup last_lookup.
    intros Hrange Hindex.
    by eapply elem_of_dom, Hrange.
  Qed.

  Lemma wp_array_copy_to' γ γᵥ γₕ γᵢ γ_val γz γ_abs (dst src : loc) (n i : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    i ≤ n → length vdst = n - i →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ 2 +ₗ i) #(n - i)
          {{{ vers vdst', RET #(); 
              (* the destination array contains some values [vdst'] *)
              (dst +ₗ i) ↦∗ vdst' ∗
              ⌜length vdst' = n - i⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] j ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ γ_l vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') γ_l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ γ_l vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! (i + j)%nat = Some v⌝)) }}}.
  Proof.
    iIntros "%Hle %Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
    iLöb as "IH" forall (i vdst ver Hle Hvdst) "Hlb".
    wp_rec.
    wp_pures.
    case_bool_decide as Hdone.
    - wp_pures.
      assert (i = n)%Z as -> by lia. clear Hdone. simplify_eq/=.
      rewrite Nat.sub_diag length_zero_iff_nil in Hvdst.
      clear Hle. subst.
      iApply ("HΦ" $! [] []). iFrame.
      iModIntro.
      iSplit; first rewrite Nat.sub_diag //.
      by repeat (iSplit; first by iPureIntro; constructor).
    - wp_pures.
      destruct vdst as [| v vdst].
      { simplify_list_eq. lia. }
      clear Hdone. simpl in *. rewrite array_cons.
      iDestruct "Hdst" as "[Hhd Htl]".
      wp_bind (! _)%E. 
      iInv readN as "(%ver' & %log & %abstraction & %actual & %cache & %γ_backup & %γ_backup' & %backup & %backup' & %index & %validated & %t & >Hver & >Hbackup_ptr & >Hγ & >%Hunboxed & Hbackup_managed & >%Hindex & >%Htag & >%Hlenactual & >%Hlencache & >%Hloglen & Hlog & >%Hlogged & >●Hlog & >●Hγ_abs & >%Habs_backup & >%Habs_backup' & >%Hlenᵢ & >%Hnodup & >%Hrange & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons & Hlock & >●Hγ_val & >%Hvalidated_iff & >%Hvalidated_sub & >%Hdom_eq)" "Hcl".
      wp_apply (wp_load_offset with "Hcache").
      { apply list_lookup_lookup_total_lt. lia. }
      iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
      { by rewrite last_lookup Hlenᵢ in Hindex. }
      iIntros "Hsrc".
      iPoseProof (mono_nat_lb_own_valid with "●Hγᵥ Hlb") as "[%Ha %Hord]".
      iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb'".
      eapply backup_logged in Hrange as Hbackup_logged; last done.
      destruct Hbackup_logged as [backup'vs Hbackup'vs].
      iMod (log_frag_alloc γ_backup' with "●Hlog") as "[●Hlog #◯Hlog]".
      { done. }
      iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
      { iExists ver', log, abstraction, actual, cache, γ_backup, γ_backup', backup, backup', index, validated, t. iFrame "∗ # %". }
      iModIntro.
      wp_store.
      wp_pures.
      rewrite -Z.sub_add_distr.
      do 2 rewrite Loc.add_assoc.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_add Nat.add_1_r.
      wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
      { iPureIntro. lia. }
      { iPureIntro. lia. }
      iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
      iApply "HΦ".
      replace (S i) with (i + 1) by lia.
      rewrite Nat2Z.inj_add -Loc.add_assoc.
      iCombine "Hhd Hdst" as "Hdst".
      rewrite -array_cons.
      iFrame. repeat iSplit.
      { iIntros "!% /=". lia. }
      { iPureIntro. by eapply SSorted_cons. }
      { iPureIntro. constructor; first done.
        eapply Forall_impl; eauto. lia. }
      { iSplitR "Hcons".
        - iSplitR; first done.
          iIntros "%Heven'".
          rewrite Nat.Odd_div2; first last.
          { rewrite Nat.Odd_succ //. }
          rewrite -Nat.even_spec in Heven'.
          rewrite Heven' in Hcons.
          iExists γ_backup', _.
          iFrame "∗ # %".
          rewrite Nat.add_0_r.
          rewrite list_lookup_lookup_total_lt //.
          * iPureIntro. do 2 f_equal.
            simpl in *. congruence.
          * rewrite /map_Forall in Hloglen.
            apply Hloglen in Hbackup'vs as ->. lia.
        - rewrite big_sepL2_mono; first done.
          iIntros (k ver''' v') "_ _ H".
          rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
  Qed.

  Lemma log_auth_auth_agree γₕ p q (log log' : gmap gname (list val)) :
    log_auth_own γₕ p log -∗
      log_auth_own γₕ q log'  -∗
        ⌜log = log'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma index_auth_auth_agree γₕ p q (index index' : list gname) :
    index_auth_own γₕ p index -∗
      index_auth_own γₕ q index'  -∗
        ⌜index = index'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply list_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    do 2 rewrite -lookup_map_seq_0 -lookup_fmap fmap_map_seq //.
  Qed.

  Lemma vers_auth_auth_agree γₕ p q (log log' : gmap gname nat) :
    vers_auth_own γₕ p log -∗
      vers_auth_own γₕ q log'  -∗
        ⌜log = log'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma vers_auth_frag_agree γₕ q log i value : 
    vers_auth_own γₕ q log -∗
      vers_frag_own γₕ i value -∗
        ⌜log !! i = Some value⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

  (* Lemma log_auth_auth_op γₕ p q (log log' : gmap loc (gname * list val)) :
    log_auth_own γₕ p log -∗
      log_auth_own γₕ q log  -∗
        log_auth_own γₕ (p ⋅ q) log.
  Proof.
    iIntros "H H'".
    rewrite /log_auth_own.
    rewrite -auth_auth_dfrac_op.
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed. *)

  Lemma wp_array_copy_to_wk γ γᵥ γₕ γᵢ γ_val γz γ_abs (dst src : loc) (n : nat) vdst ver :
    (* Length of destination matches that of source (bigatomic) *)
    length vdst = n →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #(src +ₗ 2) #n
          {{{ vers vdst', RET #(); 
              (* the destination array contains some values [vdst'] *)
              dst ↦∗ vdst' ∗
              ⌜length vdst' = n⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ γ_l vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') γ_l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ γ_l vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝ ))}}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     rewrite -(Loc.add_0 (src +ₗ 2)).
     rewrite -(Loc.add_0 dst).
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' _ _ _ _ _ _ _ _ _ _ _ vdst _ with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     rewrite Nat.sub_0_r //.
  Qed.

  Lemma wp_array_clone_wk γ γᵥ γₕ γᵢ γ_val γz γ_abs (src : loc) (n : nat) ver :
    n > 0 →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ True }}}
            array_clone #(src +ₗ 2) #n
          {{{ vers vdst (dst : loc), RET #dst; 
              (* the destination array contains some values [vdst'] *)
              dst ↦∗ vdst ∗
              ⌜length vdst = n⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst, 
                  mono_nat_lb_own γᵥ ver' ∗
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                    (* Then there exists some list of values associated with that version *)
                    ∃ γ_l vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') γ_l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ γ_l vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
    iIntros "%Hpos #Hinv #Hlb %Φ !# _ HΦ".
    rewrite /array_clone.
    wp_pures.
    wp_alloc dst as "Hdst" "†Hdst".
    { lia. }
    wp_pures.
    wp_apply (wp_array_copy_to_wk with "[//] [//] [$Hdst]").
    { rewrite length_replicate. lia. }
    iIntros (vers vdst') "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "[$Hdst $Hcons]").
    by iPureIntro.
  Qed.

  Lemma Even_inj n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma Odd_inj n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.

  (* Definition cached_wf_inv (γ γᵥ γₕ γᵣ γᵢ : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ log (actual : list val) requests,
      (* Own other half of log in top-level invariant *)
      log_auth_own γₕ (1/2) log ∗
      (* Other 1/4 of logical state in top-level invariant *)
      ghost_var γ (1/4) actual ∗
      (* Ownership of request registry *)
      registry γᵣ requests ∗
      (* State of request registry *)
      registry_inv γ (l +ₗ 1) actual requests (dom log). *)

  (* Lemma wp_array_copy_to_half' γ γᵥ γₕ γᵢ γ_val dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv readN (read_inv γ γᵥ γₕ γᵢ γ_val dst n) -∗
            {{{ (dst +ₗ 2 +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
              array_copy_to #(dst +ₗ 2 +ₗ i) #(src +ₗ i) #(n - i)%nat
            {{{ RET #(); (dst +ₗ 2 +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
  Proof.
    iIntros (Hle Hlen Hmatch) "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    iLöb as "IH" forall (i vs vs' Hlen Hle Hmatch).
    wp_rec.
    wp_pures.
    case_bool_decide.
    - wp_pures.
      simpl in *.
      assert (i = n) as -> by lia.
      rewrite Nat.sub_diag in Hlen.
      rewrite Hlen in Hmatch.
      symmetry in Hmatch.
      rewrite length_zero_iff_nil in Hlen.
      rewrite length_zero_iff_nil in Hmatch.
      subst.
      repeat rewrite array_nil.
      by iApply "HΦ".
    - wp_pures.
      assert (length vs > 0) by lia.
      destruct vs as [| v vs].
      { simplify_list_eq. lia. }
      destruct vs' as [| v' vs']; first simplify_list_eq.
      do 2 rewrite array_cons.
      iDestruct "Hdst" as "[Hdst Hdst']".
      iDestruct "Hsrc" as "[Hsrc Hsrc']".
      wp_load.
      wp_bind (_ <- _)%E.
      iInv readN as "(%ver & %log & %actual & %cache & %marked_backup & %backup & %backup' & %index & %validated & >Hver & >Hbackup & >Hγ & >%Hunboxed & >#□Hbackup & >%Hindex & >%Hvalidated & >%Hlenactual & >%Hlencache & >%Hloglen & Hlog & >%Hlogged & >●Hlog & >%Hlenᵢ & >%Hnodup & >%Hrange & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons & Hlock & Hval)" "Hcl".
      assert (i < length cache) as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγᵢ' & Hγᵥ' & Hcache') /=".
        iCombine "Hcache Hcache'" as "Hcache".
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache _]".
        { done. }
        by iCombine "Hdst Hcache" gives %[Hfrac%dfrac_valid_own_r <-].
      + simplify_eq.
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache Hacc]".
        { done. }
        iCombine "Hdst Hcache" as "Hcache".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hcache" as "[Hcache Hcache']".
        iPoseProof ("Hacc" with "Hcache") as "Hcache".
        (* $Hregistry $Hreginv $Hver Hγᵢ Hγᵥ Hcache *)
        simplify_eq.
        iMod ("Hcl" with "[-Hcache' Hdst' Hsrc Hsrc' HΦ]") as "_".
        { iExists ver, log, actual, (<[i:=v']> cache), (InjLV #backup), backup, backup', index.
          iFrame "∗ # %".
          rewrite Heven. iFrame.
          iNext. repeat iSplit; try done.
          { iPureIntro. auto. }
          by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        rewrite (Loc.add_assoc (dst +ₗ 2)) /=.
        rewrite (Loc.add_assoc src) /=.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_comm /=.
        rewrite <- Nat2Z.inj_sub by lia.
        simplify_list_eq.
        wp_apply ("IH" $! (S i) vs vs' with "[] [] [//] [$] [$]").
        * iPureIntro. lia.
        * iPureIntro. lia.
        * iIntros "[Hdst' Hsrc']".
          iApply "HΦ". iFrame.
          rewrite (Loc.add_assoc (dst +ₗ 2)) /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed. *)

  (* Lemma wp_array_copy_to_half γ γᵥ γₕ γᵢ γ_val dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv readN (read_inv γ γᵥ γₕ γᵢ γ_val dst n) -∗
          {{{ (dst +ₗ 2) ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 2) #src #n
          {{{ RET #(); (dst +ₗ 2) ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    rewrite -(Loc.add_0 (dst +ₗ 2)).
    rewrite -(Loc.add_0 src).
    change 0%Z with (Z.of_nat 0).
    rewrite -{2}(Nat.sub_0_r n).
    wp_apply (wp_array_copy_to_half' _ _ _ _ _ _ _ vs vs' with "[$] [$] [$]").
    - lia.
    - lia.
    - done.
  Qed. *)

  Lemma even_iff_not_odd n : Nat.Even n ↔ ¬ (Nat.Odd n).
  Proof.
    split.
    - rewrite /not. apply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma odd_iff_not_even n : Nat.Odd n ↔ ¬ (Nat.Even n).
  Proof.
    split.
    - rewrite /not. intros. by eapply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma div2_def n : Nat.div2 (S (S n)) = S (Nat.div2 n).
  Proof. done. Qed.

  (* Definition is_cached_wf (v : val) (γ : gname) (n : nat) : iProp Σ :=
    ∃ (dst : loc) (γₕ γᵥ γᵣ γᵢ γₒ γ_vers γ_val : gname),
      ⌜v = #dst⌝ ∗
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val dst n) ∗
      inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ dst). *)

  Lemma array_persist l vs : l ↦∗ vs ==∗ l ↦∗□ vs.
  Proof.
    iInduction vs as [| v vs] "IH" forall (l).
    - by iIntros.
    - do 2 rewrite array_cons. iIntros "[Hl Hrest]".
      iSplitL "Hl".
      + iApply (pointsto_persist with "Hl").
      + iApply ("IH" with "Hrest").
  Qed.

  Lemma gmap_injective_singleton `{Countable K} {V} (k : K) (v : V) :
    gmap_injective {[k := v]}.
  Proof.
    rewrite /gmap_injective.
    intros i j v'. do 2 rewrite lookup_singleton_Some.
    by intros [<- <-] [<- _].
  Qed.

Lemma gmap_injective_insert `{Countable K, Countable V} (k : K) (v : V) (m : gmap K V) :
  v ∉ map_img (SA:=gset V) m →
    gmap_injective m →
      gmap_injective (<[k := v]>m).
  Proof.
    rewrite /gmap_injective. intros Hfresh Hinj.
    intros i j v'.
    destruct (decide (i = k)) as [-> | Hne]; destruct (decide (j = k)) as [-> | Hne'].
    - rewrite lookup_insert //.
    - rewrite lookup_insert lookup_insert_ne //.
      intros [=<-] Hmj. by apply not_elem_of_map_img_1 with (i := j) in Hfresh.
    - rewrite lookup_insert lookup_insert_ne //.
      intros Hsome [=<-]. by apply not_elem_of_map_img_1 with (i := i) in Hfresh.
    - do 2 rewrite lookup_insert_ne //. apply Hinj.
  Qed.    

  (* Lemma new_big_atomic_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 → Forall val_is_unboxed vs →
      {{{ src ↦∗{dq} vs }}}
        new_big_atomic n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ is_cached_wf v γ n ∗ ∃ backup, value γ backup vs  }}}.
  Proof.
    iIntros "%Hlen %Hpos %Hunboxed %Φ Hsrc HΦ".
    wp_rec.
    wp_pures.
    wp_alloc l as "Hl".
    { done. }
    wp_pures.
    rewrite Nat2Z.id /= array_cons array_cons.
    iDestruct "Hl" as "(Hversion & Hvalidated & Hcache)".
    rewrite Loc.add_assoc /=.
    change (1 + 1)%Z with 2%Z.
    wp_apply (wp_array_clone with "Hsrc").
    { auto. }
    { lia. }
    iIntros (backup) "[Hbackup Hsrc]".
    wp_store.
    wp_smart_apply (wp_array_copy_to _ _ _ _ (replicate n #0) vs with "[$]").
    { by rewrite length_replicate. }
    { auto. }
    iIntros "[[Hcache Hcache'] Hsrc]". wp_pures.
    iMod (ghost_var_alloc (backup, vs)) as "(%γ & Hγ & Hγ' & Hγ'')".
    iMod (mono_nat_own_alloc 0) as "(%γᵥ & (Hγᵥ & Hγᵥ' & Hγᵥ'') & _)".
    iMod (own_alloc (● map_seq O (to_agree <$> [backup]))) as "(%γᵢ & Hγᵢ & Hγᵢ' & Hγᵢ'')".
    { by apply auth_auth_valid, singleton_valid. }
    replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
    iMod token_alloc as "[%γₜ Hγₜ]".
    iMod (own_alloc (● {[ backup := to_agree (γₜ, vs) ]})) as "(%γₕ & Hγₕ & Hγₕ')".
    { by apply auth_auth_valid, singleton_valid. }
    rewrite -map_fmap_singleton.
    iMod (own_alloc (● map_seq O (to_agree <$> []))) as "[%γᵣ Hγᵣ]".
    { by apply auth_auth_valid. }
    iMod (array_persist with "Hbackup") as "#Hbackup".
    iDestruct "Hvalidated" as "[Hvalidated Hvalidated']".
    replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
    iMod (own_alloc (● {[ backup ]})) as "[%γ_val Hγ_val]".
    { by apply auth_auth_valid. }
    iMod (inv_alloc readN _ (read_inv γ γᵥ γₕ γᵢ γ_val l n) with "[$Hvalidated $Hγ' $Hγᵥ' Hγᵥ'' Hγ_val $Hγₕ Hγᵢ' $Hγᵢ'' $Hcache Hcache' Hγₜ $Hversion $Hbackup]") as "#Hreadinv".
    { iExists backup, {[ backup ]}. iFrame "∗ # %".
      simpl.
      iSplit; first done.
      iNext. iSplit.
      { iPureIntro. right. split.
        { done. }
        { rewrite -Nat.even_spec /= //. } }
      iSplit.
      { rewrite map_Forall_singleton //. }
      iSplitL "Hγₜ".
      { rewrite log_tokens_singleton. iFrame "∗ #". }
      iSplit.
      { rewrite lookup_singleton_eq //=. }
      iSplit.
      { done. }
      iSplit.
      { iPureIntro. apply NoDup_singleton. }
      iSplit.
      { iPureIntro. rewrite Forall_singleton. set_solver. }
      rewrite bool_decide_eq_true_2; last set_solver.
      rewrite lookup_singleton_eq //=. repeat iSplit; try done. iPureIntro. set_solver. }
    iMod (own_alloc (● (∅ : gmap _ _))) as "[%γ_vers Hγ_vers]".
    { by apply auth_auth_valid. }
    iMod (own_alloc (● {[ backup := to_agree O ]})) as "[%γₒ Hγₒ]".
    { by apply auth_auth_valid, singleton_valid. }
    iMod (inv_alloc cached_wfN _ (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) with "[$Hγ'' $Hγₕ' $Hγᵣ $Hvalidated' $Hγᵥ Hγ_vers Hγₒ $Hγᵢ]") as "#Hinv".
    { iExists ∅, {[ backup := O ]}, O. 
      rewrite /registry_inv /vers_auth_own map_fmap_singleton lookup_singleton_eq /=. iFrame.
      rewrite bool_decide_eq_false_2; first last.
      { rewrite map_size_singleton. lia. }
      iPureIntro. repeat split; auto with set_solver.
      - set_solver.
      - set_solver.
      - apply gmap_injective_singleton.
      - rewrite lookup_insert_eq //.
      - repeat constructor.
      - rewrite map_Forall_singleton //. }
    iModIntro.
    iApply "HΦ".
    by iFrame "∗ #".
  Qed. *)

  Lemma div2_mono x y : x ≤ y → Nat.div2 x ≤ Nat.div2 y.
  Proof.
    intros Hle. induction Hle as [| y Hle IH].
    - done.
    - destruct (Nat.Even_Odd_dec y).
      + by rewrite -Nat.Even_div2.
      + rewrite <- Nat.Odd_div2 by done. by constructor.
  Qed.

  Lemma even_odd_negb n b : Nat.even n = b ↔ Nat.odd n = negb b.
  Proof.
    split; destruct b; simpl.
    - intros Heven%Nat.even_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Hodd%Nat.odd_spec.
      by eapply Nat.Even_Odd_False.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec. 
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + contradiction.
      + done.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec. 
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + done.
      + contradiction.
    - intros Hodd%Nat.odd_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Heven%Nat.even_spec.
      by eapply Nat.Even_Odd_False.
  Qed.

  Lemma odd_even_negb n b : Nat.odd n = b ↔ Nat.even n = negb b.
  Proof.
    rewrite even_odd_negb negb_involutive //.
  Qed.

  Lemma even_inj n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec Even_inj in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec Even_inj in H.
  Qed.

  Lemma odd_inj n : Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    destruct (Z.odd n) eqn:H, (Nat.odd n) eqn:H'; auto.
    - rewrite Z.odd_spec -Odd_inj in H.
      by rewrite -not_true_iff_false Nat.odd_spec in H'.
    - rewrite Nat.odd_spec in H'.
      by rewrite -not_true_iff_false Z.odd_spec -Odd_inj in H.
  Qed.

  Lemma twp_array_copy_to_persistent stk E (dst src : loc) vdst vsrc (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
      [[{ dst ↦∗ vdst ∗ src ↦∗□ vsrc }]]
        array_copy_to #dst #src #n @ stk; E
      [[{ RET #(); dst ↦∗ vsrc }]].
  Proof.
    iIntros (Hvdst Hvsrc Φ) "[Hdst Hsrc] HΦ".
    iInduction vdst as [|v1 vdst] "IH" forall (n dst src vsrc Hvdst Hvsrc);
      destruct vsrc as [|v2 vsrc]; simplify_eq/=; try lia; wp_rec; wp_pures.
    { iApply "HΦ". auto with iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv1 Hdst]".
    iDestruct (array_cons with "Hsrc") as "[Hv2 #Hsrc]".
    wp_load; wp_store.
    wp_smart_apply ("IH" with "[%] [%] Hdst Hsrc") as "Hvdst"; [ lia .. | ].
    iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_array_copy_to_persistent stk E (dst src : loc) vdst vsrc (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    {{{ dst ↦∗ vdst ∗ src ↦∗□ vsrc }}}
      array_copy_to #dst #src #n @ stk; E
    {{{ RET #(); dst ↦∗ vsrc }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_copy_to_persistent with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.
(* 
  Lemma twp_array_clone_persistent stk E l vl n :
    Z.of_nat (length vl) = n → (0 < n)%Z →
      [[{ l ↦∗□ vl }]]
        array_clone #l #n @ stk; E
      [[{ l', RET #l'; l' ↦∗ vl }]].
  Proof.
    iIntros (Hvl Hn Φ) "Hvl HΦ".
    wp_lam.
    wp_alloc dst as "Hdst"; first by auto.
    wp_smart_apply (twp_array_copy_to_persistent with "[$Hdst $Hvl]") as "Hdst".
    - rewrite length_replicate Z2Nat.id; lia.
    - auto.
    - wp_pures.
      iApply "HΦ". by iFrame.
  Qed. *)

  Definition extract_bool (vs : list (val * val)) : option bool :=
    match vs with
    | (LitV (LitBool b), _) :: _ => Some b
    | _ => None
    end.

  Lemma read'_spec (γ γᵥ γₕ γᵢ γ_val γz γ_abs : gname) (l : loc) (n : nat) :
    n > 0 →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs l n) -∗
        <<{ ∀∀ γ_backup vs, value γ γ_backup vs  }>> 
          read' n #l @ ↑readN
        <<{ ∃∃ (t : nat) (copy : loc) (backup : blk) (ver : nat), value γ γ_backup vs | 
            RET (#copy, #(Some (Loc.blk_to_loc backup) &ₜ t), #ver)%V; 
            copy ↦∗ vs ∗ ⌜Forall val_is_unboxed vs⌝ ∗ ⌜length vs = n⌝ ∗ log_frag_own γₕ γ_backup vs ∗ mono_nat_lb_own γᵥ ver ∗ ((⌜t = 0⌝ ∗ validated_frag_own γ_val γ_backup ∗ ∃ ver', mono_nat_lb_own γᵥ ver' ∗ ⌜ver ≤ ver'⌝ ∗ index_frag_own γᵢ (Nat.div2 ver') γ_backup) ∨ ⌜t ≠ 0⌝) }>>.
  Proof.
    iIntros (Hpos) "#Hinv %Φ AU".
    wp_rec.
    wp_bind (! _)%E.
    iInv readN as "(%ver & %log & %abstraction & %actual & %cache & %γ_backup & %γ_backup' & %backup & %backup' & %index & %validated & %t & >Hver & >Hbackup_ptr & >Hγ & >%Hunboxed & >Hbackup_managed & >%Hindex & >%Htag & >%Hlenactual & >%Hlencache & >%Hloglen & Hlog & >%Hlogged & >●Hlog & >●Hγ_abs & >%Habs_backup & >%Habs_backup' & >%Hlenᵢ & >%Hnodup & >%Hrange & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons & Hlock & >●Hγ_val & >%Hvalidated_iff & >%Hvalidated_sub & >%Hdom_eq)" "Hcl".
    wp_load.
    iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb".
    eapply backup_logged in Hrange as Hbackup_logged; last done.
    destruct Hbackup_logged as [[γₜ backup'vs] Hbackup'vs].
    iMod (log_frag_alloc backup' with "●Hlog") as "[●Hlog #◯Hlog]".
    { eassumption. }
    iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
    { by rewrite last_lookup Hlenᵢ in Hindex. }
    iMod ("Hcl" with "[-AU]") as "_".
    { rewrite /cached_wf_inv.
      iExists ver, log, actual, cache, marked_backup, backup, backup', index.
      iFrame "∗ # %". }
    iModIntro.
    wp_smart_apply (wp_array_clone_wk with "[//] [//] [//]").
    { done. }
    iIntros (vers vdst dst) "(Hdst & %Hlen' & %Hsorted & %Hbound & #Hcons)".
    wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp".
    wp_pures.
    wp_bind (! _)%E.
    iInv readN as "(%ver' & %log' & %abstraction' & %actual' & %cache' & %γ_backup₁ & %γ_backup₁' & %backup₁ & %backup₁' & %index' & %validated₁ & %t' & >Hver & >Hbackup & >Hγ & >%Hunboxed₁ & >#□Hbackup₁ & >%Hindex' & >%Hvalidated' & >%Hlenactual' & >%Hlencache' & >%Hloglen' & Hlog & >%Hlogged' & >●Hlog & >%Hlenᵢ' & >%Hnodup' & >%Hrange' & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons' & Hlock & >●Hγ_val & >%Hvalagree₁ & >%Hvaldom₁ & >%Habsagree₁ & >%Habsdom₁)" "Hcl".
    wp_load.
    destruct Hvalidated' as [-> | (-> & HEven & <- & <-)].
    - iMod ("Hcl" with "[-AU Hdst Hp]") as "_".
      { rewrite /cached_wf_inv.
        iExists ver', log', abstraction', actual', cache', γ_backup₁, γ_backup₁', backup₁, backup₁', index', validated₁, t'.
        iFrame "∗ # %". auto. }
      iModIntro.
      rewrite /is_valid.
      wp_pures.
      wp_bind (! _)%E.
      iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlog & >%Hlogged₂ & >●Hlog & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hvalagree₂ & >%Hvaldom₂ & >%Habsagree₂ & >%Habsdom₂)" "Hcl".
      wp_load.
      pose proof Hlogged₂ as Hlogged₂'.
      rewrite -lookup_fmap lookup_fmap_Some in Hlogged₂'.
      destruct Hlogged₂' as ([γₜ₂ actual₂'] & Heq & Hlookup₂).
      simpl in Heq. simplify_eq.
      iMod (log_frag_alloc backup₂ with "●Hlog") as "[●Hlog #◯Hlog₂]".
      { done. }
      iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ']".
      { by rewrite last_lookup Hlenᵢ₂ in Hindex₂. }
      iDestruct (mono_nat_lb_own_valid with "●Hγᵥ Hlb") as %[_ Hle].
      iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb₂".
      iMod "AU" as (backup'' vs') "[Hγ' [_ Hconsume]]".
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      iMod ("Hconsume" $! marked_backup₂ dst backup₂ ver with "Hγ'") as "HΦ".
      destruct Hvalidated₂ as [-> | (-> & HEven₂ & <- & <-)].
      * iMod ("Hcl" with "[-HΦ Hdst Hp]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂.
          iFrame "∗ # %". auto. }
        iModIntro.
        rewrite /strip.
        wp_pures.
        wp_apply (wp_array_copy_to_persistent with "[$Hdst $□Hbackup₂]").
        { lia. }
        { lia. }
        iIntros "Hdst".
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$Hdst]").
        iFrame "∗ # %".
        by iRight.
      * apply Nat.even_spec in HEven₂ as Heven₂.
        destruct (decide (backup₂ ∈ validated₂)) as [Hinval | Hninval]; first last.
        { rewrite bool_decide_eq_false_2 // in Hvalagree₂. }
        iMod (validated_auth_frag_alloc with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₂]".
        { done. } 
        iMod ("Hcl" with "[-HΦ Hdst Hp]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver₂, log₂, abstraction₂, actual₂, actual₂, γ_backup₂, γ_backup₂, backup₂, backup₂, index₂, validated₂, t₂.
          iFrame "∗ # %". iRight. auto. }
        iModIntro.
        rewrite /strip.
        wp_pures.
        wp_apply (wp_array_copy_to_persistent with "[$Hdst $□Hbackup₂]").
        { lia. }
        { lia. }
        iIntros "Hdst".
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$Hdst]").
        rewrite -(Nat.Even_div2 ver₂) //.
        simpl.
        iFrame "∗ # %".
        by iLeft.
    - destruct (extract_result vs) as [ver_proph|] eqn:Hextract; first last.
      { (* Some other value is prophecied: impossible *)
        iMod ("Hcl" with "[-Hp]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver', log', abstraction', actual', actual', γ_backup₁, γ_backup₁, backup₁, backup₁, index', validated₁, t'.
          iFrame "∗ # %". by iRight. }
        iModIntro.
        rewrite /is_valid.
        wp_pures.
        wp_bind (Resolve _ _ _)%E.
        iInv readN as "(%ver'' & %log'' & %abstraction'' & %actual'' & %cache'' & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index'' & %validated₂ & %t'' & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex'' & >%Hvalidated'' & >%Hlenactual'' & >%Hlencache'' & >%Hloglen'' & Hlog & >%Hlogged'' & >●Hlog & >%Hlenᵢ'' & >%Hnodup'' & >%Hrange'' & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons'' & Hlock & >●Hγ_val & >%Hval₁ & >%Habsagree'' & >%Habsdom'')" "Hcl".
        wp_apply (wp_resolve with "Hp").
        { done. }
        wp_load.
        iIntros "!> %pvs' -> _".
        simplify_eq. }
      destruct (decide (Z.of_nat ver = ver_proph)) as [<- | Hneq].
      + iMod "AU" as (backup'' vs') "[Hγ' [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        pose proof Hlogged' as Hlogged₁'.
        rewrite -lookup_fmap lookup_fmap_Some in Hlogged'.
        destruct Hlogged' as ([γₜ₁ ?] & Heq & Hlogged').
        simpl in Heq. subst.
        iMod ("Hconsume" $! (InjRV #backup₁) dst backup₁ ver γₜ₁ with "Hγ'") as "HΦ".
        iPoseProof (log_auth_frag_agree with "●Hlog ◯Hlog") as "%Hlookup".
        iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ']".
        { by rewrite last_lookup Hlenᵢ' in Hindex'. }
        iDestruct (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hindexagree".
        iMod (log_frag_alloc backup₁ with "●Hlog") as "[●Hlog #◯Hlog']".
        { eassumption. }
        iDestruct (mono_nat_lb_own_valid with "●Hγᵥ Hlb") as %[_ Hle].
        iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb'".
        destruct (decide (backup₁ ∈ validated₁)) as [Hinval | Hninval]; first last.
        { rewrite bool_decide_eq_false_2 // in Hvalagree₁. }
        iMod (validated_auth_frag_alloc with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₁]".
        { done. } 
        iMod ("Hcl" with "[-HΦ Hdst Hp]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver', log', abstraction', actual', actual', γ_backup₁, γ_backup₁, backup₁, backup₁, index', validated₁, t'.
          iFrame "∗ # %". by iRight. }
        iModIntro.
        rewrite /is_valid.
        wp_pures.
        wp_bind (Resolve _ _ _)%E.
        iInv readN as "(%ver'' & %log'' & %abstraction'' & %actual'' & %cache'' & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index'' & %validated₂ & %t'' & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex'' & >%Hvalidated'' & >%Hlenactual'' & >%Hlencache'' & >%Hloglen'' & Hlog & >%Hlogged'' & >●Hlog & >%Hlenᵢ'' & >%Hnodup'' & >%Hrange'' & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons'' & Hlock & >●Hγ_val & >%Hval₁ & >%Habsagree'' & >%Habsdom'')" "Hcl".
        wp_apply (wp_resolve with "Hp").
        { done. }
        iDestruct (mono_nat_lb_own_valid with "●Hγᵥ Hlb'") as %[_ Hle'].
        iPoseProof (log_auth_frag_agree with "●Hlog ◯Hlog") as "%Hlookup'".
        iDestruct (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hindexagree'".
        wp_load.
        iIntros "!> %pvs' -> Hp".
        simpl in Hextract. simplify_eq.
        rewrite last_lookup Hlenᵢ in Hindex.
        rewrite last_lookup Hlenᵢ' in Hindex'.
        pose proof Hindex'' as Hindex'''.
        rewrite last_lookup Hlenᵢ'' in Hindex''.
        replace ver' with ver in * by lia.
        clear Hle Hle'.  
        simplify_eq.
        pose proof Hcons'' as Hcons'''.
        apply Nat.even_spec in HEven as Heven.
        rewrite Heven -lookup_fmap lookup_fmap_Some in Hcons.
        rewrite Heven -lookup_fmap lookup_fmap_Some in Hcons'.
        rewrite Heven -lookup_fmap lookup_fmap_Some in Hcons''.
        destruct Hcons as ([? ?] & <- & Hcons).
        destruct Hcons' as ([? ?] & <- & Hcons').
        destruct Hcons'' as ([? ?] & <- & Hcons'').
        rewrite Nat.Odd_div2; first last.
        { rewrite Nat.Odd_succ //. }
        rewrite Nat.Odd_div2 in Hlenᵢ Hlenᵢ' Hindexagree Hindexagree' Hindex Hlenᵢ''; first last.
        { rewrite Nat.Odd_succ //. }
        simpl in *.
        rewrite Hcons'' in Hlookup'.
        rewrite Hcons' in Hlookup.
        simplify_eq.
        simpl in *.
        iFrame "∗ # ∗".
        iAssert (⌜backup'vs = vdst⌝)%I with "[●Hγᵥ]" as "<-".
        { iApply pure_mono.
          { by apply list_eq_same_length. }
          rewrite big_sepL2_forall.
          iDestruct "Hcons" as "[%Heq #Hcons]".
          iIntros (i v v' Hlt Hv Hv').
          assert (i < length vers) as [ver''' Hver''']%lookup_lt_is_Some by lia.
          iPoseProof ("Hcons" with "[//] [//]") as "[#Hlb'' #Hfrag]".
          assert (ver ≤ ver''') as Hle by (by eapply Forall_lookup).
          iPoseProof (mono_nat_lb_own_valid with "●Hγᵥ Hlb''") as "[%Hq %Hge]".
          assert (ver = ver''') as <- by lia.
          clear Hge Hle.
          iPoseProof ("Hfrag" with "[]") as "(%l' & %γₜ' & %vs' & #◯Hindex' & #◯Hlog''' & %Hlookup')".
          { by rewrite -Nat.even_spec. }
          iCombine "◯Hγᵢ ◯Hindex'" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as <-.
          iCombine "◯Hlog ◯Hlog'''" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as [=<-<-].
          by simplify_eq. }
        iMod ("Hcl" with "[-HΦ Hdst]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver, log'', abstraction'', actual'', backup'vs, γ_backup₂, γ_backup₂', backup₂, backup', index'', validated₂, t''.
          iFrame "∗ # %". rewrite Nat.Odd_div2 // Nat.Odd_succ //. }
        iModIntro.
        wp_pures.
        rewrite bool_decide_eq_true_2; last done.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame "∗ % #".
        auto.
      + iMod ("Hcl" with "[-AU Hdst Hp]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver', log', actual', actual', (InjRV #backup₁), backup₁, backup₁, index'.
          iFrame "∗ # %". by iRight. }
        iModIntro.
        rewrite /is_valid.
        wp_pures.
        wp_bind (Resolve _ _ _)%E.
        iInv readN as "(%ver₂ & %log₂ & %actual₂ & %cache₂ & %marked_backup₂ & %backup₂ & %backup₂' & %index₂ & %validated₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlog & >%Hlogged₂ & >●Hlog & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hvalagree₂ & >%Hvaldom₂)" "Hcl".
        wp_apply (wp_resolve with "Hp").
        { done. }
        wp_load.
        iIntros "!> %pvs' -> Hp".
        iMod ("Hcl" with "[-AU Hdst]") as "_".
        { rewrite /cached_wf_inv.
          iExists ver₂, log₂, actual₂, cache₂, marked_backup₂, backup₂, backup₂', index₂.
          iFrame "∗ # %". }
        iModIntro.
        simpl in Hextract. simplify_eq.
        wp_pures.
        rewrite bool_decide_eq_false_2; last naive_solver.
        wp_pures.
        wp_bind (! _)%E.
        iInv readN as "(%ver₃ & %log₃ & %actual₃ & %cache₃ & %marked_backup₃ & %backup₃ & %backup₃' & %index₃ & %validated₃ & >Hver & >Hbackup & >Hγ & >%Hunboxed₃ & >#□Hbackup₃ & >%Hindex₃ & >%Hvalidated₃ & >%Hlenactual₃ & >%Hlencache₃ & >%Hloglen₃ & Hlog & >%Hlogged₃ & >●Hlog & >%Hlenᵢ₃ & >%Hnodup₃ & >%Hrange₃ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₃ & Hlock & >●Hγ_val & >%Hvalagree₃ & >%Hvaldom₃)" "Hcl".
        wp_load.
        pose proof Hlogged₃ as Hlogged₃'.
        rewrite -lookup_fmap lookup_fmap_Some in Hlogged₃'.
        destruct Hlogged₃' as ([γₜ₂ actual₃'] & Heq & Hlookup₃).
        simpl in Heq. simplify_eq.
        iMod (log_frag_alloc backup₃ with "●Hlog") as "[●Hlog #◯Hlog₃]".
        { done. }
        iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ']".
        { by rewrite last_lookup Hlenᵢ₃ in Hindex₃. }
        iDestruct (mono_nat_lb_own_valid with "●Hγᵥ Hlb") as %[_ Hle].
        iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb₂".
        iMod "AU" as (backup'' vs') "[Hγ' [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        iMod ("Hconsume" $! marked_backup₃ dst backup₃ ver with "Hγ'") as "HΦ".
        destruct Hvalidated₃ as [-> | (-> & HEven₃ & <- & <-)].
        * iMod ("Hcl" with "[-HΦ Hdst]") as "_".
          { rewrite /cached_wf_inv.
            iExists ver₃, log₃, actual₃, cache₃, (InjLV #backup₃), backup₃, backup₃', index₃.
            iFrame "∗ # %". auto. }
          iModIntro.
          rewrite /strip.
          wp_pures.
          wp_apply (wp_array_copy_to_persistent with "[$Hdst $□Hbackup₃]").
          { lia. }
          { lia. }
          iIntros "Hdst".
          wp_pures.
          iModIntro.
          iApply ("HΦ" with "[$Hdst]").
          iFrame "∗ # %".
          by iRight.
        * apply Nat.even_spec in HEven₃ as Heven₃.
          destruct (decide (backup₃ ∈ validated₃)) as [Hinval | Hninval]; first last.
          { rewrite bool_decide_eq_false_2 // in Hvalagree₃. }
          iMod (validated_auth_frag_alloc with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₂]".
          { done. } 
          iMod ("Hcl" with "[-HΦ Hdst]") as "_".
          { rewrite /cached_wf_inv.
            iExists ver₃, log₃, actual₃, actual₃, (InjRV #backup₃), backup₃, backup₃, index₃.
            iFrame "∗ # %". iRight. auto. }
          iModIntro.
          rewrite /strip.
          wp_pures.
          wp_apply (wp_array_copy_to_persistent with "[$Hdst $□Hbackup₃]").
          { lia. }
          { lia. }
          iIntros "Hdst".
          wp_pures.
          iModIntro.
          iApply ("HΦ" with "[$Hdst]").
          rewrite -(Nat.Even_div2 ver₃) //.
          simpl.
          iFrame "∗ # %".
          by iLeft.
  Qed.

  (* It is possible to linearize pending writers while maintaing the registry invariant *)
  Lemma linearize_cas γ (lactual lactual' : loc) (actual actual' : list val) requests (log : gmap loc (gname * list val)) (γₜ : gname) :
    length actual > 0 →
    (* The current and previous logical state should be distinct if swapping backup pointer *)
    actual ≠ actual' →
    (* Both the current and new logical state are comprised of the same number of bytes *)
    length actual = length actual' → 
    (* The current backup pointer has been logged *)
    fst <$> log !! lactual' = None →
    (* Points-to predicate of every previously logged backup *)
    log_tokens log -∗
    (* The logical state has not yet been updated to the new state *)
    ghost_var γ (1/2) (lactual', actual') -∗
    (* The registry invariant is satisfied for the current logical state *)
    registry_inv γ lactual actual requests (dom log)
    (* We can take frame-preserving updated that linearize the successful CAS,
       alongside all of the other failing CAS's *)
    ={⊤ ∖ ↑readN ∖ ↑cached_wfN}=∗
      (* Points-to predicate of every previously logged backup *)
      log_tokens log ∗
      (* Update new logical state to correspond to logical CAS *)
      ghost_var γ (1/2) (lactual', actual') ∗
      (* Invariant corresponding to new logical state *)
      registry_inv γ lactual' actual' requests (dom log).
  Proof.
    iIntros (Hpos Hne Hlen Hlogged) "Hlog Hγ Hreqs".
    iInduction requests as [|[[γₗ γₑ] lexp] reqs'] "IH".
    - by iFrame.
    - rewrite /registry_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(%Hfresh & Hlin & %Φ & %γₜ' & %lexp' & %ldes & %dq & %dq' & %expected & %desired & Hγₑ & #Hwinv) Hreqs']".
      iMod ("IH" with "Hlog Hγ Hreqs'") as "(Hlog & Hγ & Hreqinv)".
      iInv casN as "[(HΦ & [%b >Hγₑ'] & >Hlin') | [(>Hcredit & AU & >Hγₑ' & >Hlin') | (>Htok & [%b >Hγₑ'] & [%b' >Hlin'])]]" "Hclose".
      + iCombine "Hlin Hlin'" gives %[_ ->].
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']". 
        (* rewrite bool_decide_eq_false in Hneq. *)
        iMod ("Hclose" with "[HΦ Hγₑ Hlin]") as "_".
        { iLeft. iFrame. }
        destruct (decide (lactual' = lexp)) as [-> | Hneq].
        * apply elem_of_dom in Hfresh as [[γₜ'' value] Hvalue].
          by destruct (log !! lexp).
        * iFrame "∗ # %".
          rewrite /request_inv.
          replace (bool_decide (lactual' = lexp)) with false.
          { by iFrame. }
          { by rewrite bool_decide_eq_false_2. }
      + iCombine "Hlin Hlin'" gives %[_ ->%bool_decide_eq_true].
        iCombine "Hγₑ Hγₑ'" gives %[_ ->%bool_decide_eq_true].
        iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
        iMod "AU" as (backup'' actual'') "[Hγ' [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        rewrite (bool_decide_eq_false_2 (actual' = expected)); last done.
        destruct (decide (lactual' = lexp)) as [-> | Hdiff].
        * apply elem_of_dom in Hfresh as [[γₜ'' value] Hvalue].
          iPoseProof (log_tokens_impl with "Hlog") as "[Hactual' _]".
          { done. }
          by destruct (log !! lexp).
        * iFrame "∗ # %".
          rewrite (bool_decide_eq_false_2 (lactual' = lexp)); last done.
          iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
          iMod ("Hconsume" with "[$]") as "HΦ".
          iFrame.
          iMod ("Hclose" with "[-]") as "_".
          { iLeft. iFrame. }
          done.
      + iMod (ghost_var_update_halves (bool_decide (lactual' = lexp)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
        iFrame "∗ # %".
        iMod ("Hclose" with "[-]") as "_".
        { do 2 iRight. iFrame. }
        done.
  Qed.

  Lemma log_tokens_update log l γ vs :
    log !! l = None →
      log_tokens log -∗
        token γ -∗
          l ↦∗□ vs -∗
            log_tokens (<[l := (γ, vs)]> log).
  Proof.
    iIntros (Hlog) "Hlogtokens Htok #Hl".
    rewrite /log_tokens.
    rewrite big_sepM_insert; last done.
    iFrame "∗ #".
  Qed.

  (* Lemma foo (x : nat) (X Y : gset nat) : x ∉ Y → X ⊂ Y → {[ x ]} ∪ X ⊂ {[ x ]} ∪ Y.
  Proof.
    intros. set_solver. *)

  Lemma own_auth_split_self (dq : dfrac) (γ : gname) (m : gmap loc (agree (gname * list val))) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma own_auth_split_self' (dq : dfrac) (γ : gname) (m : gmap loc (agree nat)) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma own_auth_split_self'' (dq : dfrac) (γ : gname) (m : gmap nat (agree loc)) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma map_Forall_subseteq `{Countable K} {V} (m m' : gmap K V) P :
    m ⊆ m' → map_Forall P m' → map_Forall P m.
  Proof.
    rewrite /map_Forall. 
    intros Hsub HP k v Hsome.
    by eapply HP, lookup_weaken.
  Qed.

  Lemma even_succ_negb k : Nat.even (S k) = negb (Nat.even k).
  Proof.
    destruct (Nat.even (S k)) eqn:Hsucc; destruct (Nat.even k) eqn:H.
    - exfalso. apply (Nat.Even_Odd_False k).
      + rewrite -Nat.even_spec //.
      + rewrite -Nat.Even_succ -Nat.even_spec //.
    - done.
    - done.
    - exfalso. apply (Nat.Even_Odd_False k).
      + rewrite -Nat.Odd_succ -Nat.odd_spec odd_even_negb //.
      + rewrite -Nat.odd_spec odd_even_negb //.
  Qed.

Lemma NoDup_lookup_ne {A} (l : list A) i j x y :
  NoDup l →
  i ≠ j →
  l !! i = Some x →
  l !! j = Some y →
  x ≠ y.
Proof.
  intros Hnd Hij Hi Hj ->. eapply Hij, NoDup_lookup; eauto.
Qed.

  
  Lemma even_odd_negb_eq n : Nat.odd n = negb (Nat.even n).
  Proof.
    by apply even_odd_negb.
  Qed.

  (* The “strict” version: no extra assumptions on R *)
  Lemma StronglySorted_lookup_lt {A} (R : A → A → Prop) l i j x y :
    StronglySorted R l →
    i < j →
    l !! i = Some x →
    l !! j = Some y →
    R x y.
  Proof.
    revert i j x y.
    induction l as [|a l IH]; intros i j x y Hsorted Hij Hix Hjy.
    - now rewrite lookup_nil in Hix.
    - destruct i as [| i], j as [| j].
      + lia.
      + simpl in *. simplify_eq. inv Hsorted.
        eapply Forall_lookup_1; eauto.
      + lia.
      + simpl in *. inv Hsorted. apply (IH i j); auto. lia.
  Qed.

  Lemma already_linearized Φ γ γₗ γₑ γᵣ γₜ (backup lexp lexp' ldes : loc) expected desired actual (dq dq' : dfrac) i used :
    lexp' ≠ backup →
      (* inv readN (read_inv γ γᵥ γₕ γᵢ l (length expected)) -∗
        inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗ *)
      inv casN (cas_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired) -∗
        lexp ↦∗{dq} expected -∗
          ldes ↦∗{dq'} desired -∗
            registered γᵣ i γₗ γₑ lexp' -∗
              request_inv γ γₗ γₑ backup lexp' actual used -∗
                token γₜ -∗
                  £ 1 ={⊤ ∖ ↑readN ∖ ↑cached_wfN}=∗
                    Φ #false ∗ request_inv γ γₗ γₑ backup lexp' actual used.
  Proof.
    iIntros (Hne) "#Hcasinv Hlexp Hldes #Hregistered Hreqinv Hγₜ Hcredit".
    rewrite /request_inv.
    iDestruct "Hreqinv" as "(%Hused & Hlin & %Φ' & %γₜ' & %lexp'' & %ldes' & %dq₁ & %dq₁' & %expected' & %desired' & Hγₑ & _)".
    iInv casN as "[(HΦ & [%b >Hγₑ'] & >Hlin') | [(>Hcredit' & AU & >Hγₑ' & >Hlin') | (>Htok & [%b >Hγₑ'] & [%b' >Hlin'])]]" "Hclose".
    + iCombine "Hlin Hlin'" gives %[_ Heq].
      iMod (ghost_var_update_halves (bool_decide (actual = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']". 
      iMod ("Hclose" with "[Hγₜ Hγₑ Hlin]") as "_".
      { rewrite /cas_inv. do 2 iRight. iFrame. }
      iMod (lc_fupd_elim_later with "Hcredit HΦ") as "HΦ".
      iModIntro.
      iPoseProof ("HΦ" with "[$]") as "HΦ".
      iFrame "∗ # %".
      rewrite bool_decide_eq_false_2 //.
    + rewrite bool_decide_eq_false_2 //.
      iCombine "Hlin Hlin'" gives %[_ [=]].
    + iCombine "Hγₜ Htok" gives %[].
  Qed.

  Global Instance GMapFMap`{EqDecision K, Countable K} `{V} : FMap (gmap K).
  Proof. apply _. Qed.

  Lemma wp_try_validate (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ γₚ' : gname) (l ldes ldes' : loc) (dq : dfrac)
                        (expected desired : list val) (ver ver₂ idx₂ : nat) (index₂ : list gname)
                        (order₂ : gmap gname nat) :
    length expected > 0 → length expected = length desired → ver ≤ ver₂ → length index₂ = S (Nat.div2 (S ver₂)) →
      StronglySorted (gmap_mono order₂) index₂ → Forall (.∈ dom order₂) index₂ → map_Forall (λ _ idx, idx ≤ idx₂) order₂ →
        order₂ !! ldes' = None →
          inv readN (read_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
            inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
              mono_nat_lb_own γᵥ ver₂ -∗
                own γᵢ (◯ map_seq O (to_agree <$> index₂)) -∗
                  log_frag_own γₕ ldes' γₚ' desired -∗
                    vers_frag_own γₒ ldes' (S idx₂) -∗
                      own γₒ (◯ (fmap (M := gmap loc) to_agree order₂)) -∗
                        vers_frag_own γ_vers ldes' ver₂ -∗
                          {{{ ldes ↦∗{dq} desired }}}
                            try_validate (length expected) #l #ver #ldes #ldes'
                          {{{ RET #(); ldes ↦∗{dq} desired }}}.
  Proof.
    iIntros (Hlenexp Hlenmatch Hle Hlenᵢ₂ Hindexordered Hmono Hubord₂ Hldes'fresh) "#Hreadinv #Hinv #◯Hγᵥ #◯Hγᵢ #◯Hγₕ #◯Hγₒ #◯Hγₒcopy #◯Hγ_vers %Φ !# Hldes HΦ".
    rewrite /try_validate. wp_pures.
    destruct (Nat.even ver) eqn:Heven.
    - rewrite Zrem_even even_inj Heven /=.
      wp_pures.
      wp_bind (CmpXchg _ _ _).
      iInv readN as "(%ver₃ & %log₃ & %actual₃ & %cache₃ & %marked_backup₃ & %backup₃ & %backup₃' & %index₃ & %validated₃ & >Hver & >Hbackup & >Hγ & >%Hunboxed & >#□Hbackup₃ & >%Hindex₃ & >%Hvalidated₃ & >%Hlenactual₃ & >%Hlencache₃ & >%Hloglen₃ & Hlogtokens & >%Hlogged₃ & >●Hγₕ & >%Hlenᵢ₃ & >%Hnodup₃ & >%Hrange₃ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₃ & Hlock & >●Hγ_val & >%Hval₃ & >%Hvallogged₃)" "Hcl".
      iInv cached_wfN as "(%ver'' & %log₃' & %actual₃' & %marked_backup₃' & %backup₃'' & %requests₃ & %vers₃ & %index₃' & %order₃ & %idx₃ & >●Hγᵥ' & >Hbackup₃' & >Hγ' & >%Hcons₃' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₃ & >%Hvers₃ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₃ & >%Hinj₃ & >%Hidx₃ & >%Hmono₃ & >%Hubord₃)" "Hcl'".
      iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iCombine "●Hγₕ ●Hγₕ'" gives %G.
      destruct (decide (ver₃ = ver)) as [-> | Hneq]; first last.
      { wp_cmpxchg_fail.
        { intros [=]. lia. }
        iMod ("Hcl'" with "[$Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγᵥ' $●Hγ_vers $Hbackup₃' $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame "%". }
        iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hbackup $Hver $●Hγₕ $□Hbackup₃ $●Hγ_val]") as "_".
        { iFrame "%". }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$]"). } 
      wp_cmpxchg_suc.
      iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ") as %[_ Hle₃].
      (* assert (ver₁ = ver) as -> by lia. *)
      assert (ver₂ = ver) as -> by lia.
      rewrite Heven.
      iDestruct "Hlock" as "(●Hγᵢ'' & ●Hγᵥ'' & Hcache₂)".
      iCombine "●Hγᵥ ●Hγᵥ''" as "●Hγᵥ". rewrite Qp.quarter_quarter.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
      iCombine "●Hγᵥ ●Hγᵥ'" as "●Hγᵥ".
      iPoseProof (vers_auth_frag_agree with "●Hγ_vers ◯Hγ_vers") as "%Hagreevers".
      (* iCombine "●Hγ_vers ◯Hγ_verscopy" gives %(_ & Hvalid%fmap_to_agree_included_subseteq' & _)%auth_both_dfrac_valid_discrete. *)
      destruct (decide (1 < size log₃)) as [Hless | Hge]; first last.
      { rewrite bool_decide_eq_false_2 // in Hvers₃. simplify_eq. }
      rewrite bool_decide_eq_true_2 // in Hvers₃.
      iMod (mono_nat_own_update (S ver) with "●Hγᵥ") as "[(●Hγᵥ & ●Hγᵥ' & ●Hγᵥ'') #Hlb']".
      { lia. }
      (* iCombine "●Hγₕ ◯Hγₕ" gives %(_ & Hvalid%fmap_to_agree_included_subseteq%map_subseteq_size & _)%auth_both_dfrac_valid_discrete. *)
      destruct Hvers₃ as (ver'' & Hvers₃lookup & Hlevers₃ & Hub₃ & Hinvalid).
      eapply map_Forall_lookup_1 in Hagreevers as Hvalid; eauto.
      simpl in Hvalid.
      assert (ver'' = ver) as -> by lia.
      rewrite bool_decide_eq_true_2 // in Hinvalid.
      simplify_eq.
      iCombine "●Hγᵢ ●Hγᵢ''" as "●Hγᵢ".
      rewrite Qp.quarter_quarter.
      iCombine "●Hγᵢ ●Hγᵢ'" as "●Hγᵢ".
      (* rewrite Nat.Odd_div2 /= in Hlenᵢ₁ Hlenᵢ₂ Hlenᵢ₃; first last.
      { rewrite Nat.Odd_succ -Nat.even_spec //. } *)
      iPoseProof (index_auth_frag_agree' with "●Hγᵢ ◯Hγᵢ") as "%Hprefix".
      apply prefix_length_eq in Hprefix as <-; last lia.
      (* iPoseProof (index_auth_frag_agree' with "●Hγᵢ ◯Hγᵢ₂") as "%Hprefix". *)
      (* apply prefix_length_eq in Hprefix as <-; last lia. *)
      iCombine "●Hγₒ ◯Hγₒcopy" gives %(_ & Hvalidₒ'%fmap_to_agree_included_subseteq' & _)%auth_both_dfrac_valid_discrete.
      (* iCombine "●Hγᵢ ◯Hγᵢ" gives %(_ & Hvalidindex%fmap_to_agree_included_subseteq'' & _)%auth_both_dfrac_valid_discrete. *)
      iMod (index_auth_update ldes' with "●Hγᵢ") as "[(●Hγᵢ & ●Hγᵢ' & ●Hγᵢ'') ◯Hγᵢ₃]".
      iCombine "Hbackup Hbackup₃'" gives %[_ ->].
      replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
      iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ".
      (* assert (order₁ ⊆ order₃) by by etransitivity. *)
      iMod ("Hcl'" with "[$Hbackup₃' $Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ $●Hγᵢ $●Hγₒ]") as "_".
      { iFrame "%". iSplit; first last.
        { iPureIntro. apply StronglySorted_snoc.
          - apply (StronglySorted_subseteq order₂).
            { done. }
            { done. }
            { done. }
          - rewrite Forall_forall.
            intros l' Hmem i j Hts Hts'.
            simplify_eq.
            rewrite Forall_forall in Hmono.
            apply Hmono in Hmem.
            rewrite elem_of_dom in Hmem.
            destruct Hmem as [ts' Hts''].
            rewrite map_subseteq_spec in Hvalidₒ'.
            apply Hvalidₒ' in Hts'' as ?.
            simplify_eq. 
            apply Hubord₂ in Hts''. lia. }
        rewrite bool_decide_eq_true_2 //.
        iPureIntro. exists ver. repeat split; auto.
        rewrite bool_decide_eq_false_2 //. }
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_add /=.
      (* iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ₁") as "%H'". *)
      destruct Hvalidated₃ as [-> | ([=] & _ & _ & _)].
      (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
      iModIntro.
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ' $●Hγᵥ'' $Hcache $Hbackup $Hver $●Hγₕ $□Hbackup₃ $●Hγ_val]") as "_".
      { rewrite even_succ_negb Heven /= last_snoc.
        iExists ldes'. iFrame "%". iPureIntro.
        repeat split; auto.
        - rewrite length_app /= Nat.add_1_r Hlenᵢ₃. do 2 f_equal. rewrite -Nat.Even_div2 // -Nat.even_spec //.
        - apply NoDup_app. repeat split; first done.
          + intros l' Hl'. intros ->%list_elem_of_singleton.
            rewrite Forall_forall in Hmono.
            apply Hmono in Hl'.
            rewrite elem_of_dom in Hl'.
            destruct Hl' as [ts Hts]. simplify_eq.
          + apply NoDup_singleton.
        - rewrite Forall_app. split; first done. rewrite Forall_singleton.
          rewrite -Hdomord₃ elem_of_dom. eauto.
        - destruct (decide (backup₃ ∈ validated₃)) as [Hval' | Hnval].
          { rewrite bool_decide_eq_true_2 // in Hval₃. }
          rewrite bool_decide_eq_false_2 //. }
      iModIntro.
      wp_pures.
      wp_bind (array_copy_to _ _ _).
      wp_apply (wp_array_copy_to_half _ _ _ _ _ _ _ cache₃ desired with "[//] [$] [-]"); try done.
      { lia. }
      iIntros "!> [Hdst Hsrc]".
      wp_pures.
      wp_bind (_ <- _)%E.
      iInv readN as "(%ver₄ & %log₄ & %actual₄ & %cache₄ & %marked_backup₄ & %backup₄ & %backup₄' & %index₄ & %validated₄ & >Hver & >Hbackup & >Hγ & >%Hunboxed₄ & >#□Hbackup₄ & >%Hindex₄ & >%Hvalidated₄ & >%Hlenactual₄ & >%Hlencache₄ & >%Hloglen₄ & Hlogtokens & >%Hlogged₄ & >●Hγₕ & >%Hlenᵢ₄ & >%Hnodup₄ & >%Hrange₄ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₄ & Hlock & >●Hγ_val & >%Hvallogged₄)" "Hcl".
      iInv cached_wfN as "(%ver'' & %log₄' & %actual₄' & %marked_backup₄' & %backup₄'' & %requests₄ & %vers₄ & %index₄' & %order₄ & %idx₄ & >●Hγᵥ'' & >Hbackup₄' & >Hγ' & >%Hcons₄' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₄ & >%Hvers₄ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₄ & >%Hinj₄ & >%Hidx₄ & >%Hmono₄ & >%Hubord₄)" "Hcl'".
      wp_store.
      change 2%Z with (Z.of_nat 2). simplify_eq.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ ->].
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ' ●Hγᵥ''") as %[_ <-].
      iCombine "●Hγᵥ ●Hγᵥ'" as "●Hγᵥ".
      rewrite Qp.quarter_quarter.
      iCombine "●Hγᵥ ●Hγᵥ''" as "●Hγᵥ".
      iMod (mono_nat_own_update (S (S ver)) with "●Hγᵥ") as "[(●Hγᵥ & ●Hγᵥ' & ●Hγᵥ'') #Hlb₃]".
      { lia. }
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ''") as %<-.
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
      iPoseProof (array_frac_add with "Hcache Hdst") as "[Hcache ->]".
      { lia. }
      rewrite dfrac_op_own Qp.half_half.
      iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
      iMod ("Hcl'" with "[$Hbackup₄' $Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame "%". iPureIntro.
        destruct (decide (1 < size log₄)).
        - rewrite bool_decide_eq_true_2 //. 
          rewrite bool_decide_eq_true_2 // in Hvers₄.
          destruct Hvers₄ as (ver₄' & Hver₄' & Hle₄ & Hub₄ & Hinvalid₄).
          exists ver₄'. repeat split; auto.
          rewrite bool_decide_eq_false_2 //. lia.
        - rewrite bool_decide_eq_false_2 //. 
          rewrite bool_decide_eq_false_2 // in Hvers₄. }
      rewrite -Nat2Z.inj_add /=.
      destruct Hvalidated₄ as [-> | (_ & HOdd%Nat.Even_succ & _ & _)]; first last.
      { exfalso. apply (Nat.Even_Odd_False ver).
        - rewrite -Nat.even_spec //.
        - done. }
      iDestruct "Hcache" as "[Hcache Hcache']".
      simpl in Hlenᵢ₄.
      iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ₃") as "%Hagreeᵢ".
      iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hbackup₃".
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ ●Hγᵢ'' $●Hγᵥ' ●Hγᵥ'' $Hcache Hcache' $Hbackup $Hver $●Hγₕ $□Hbackup₄ $●Hγ_val]") as "_".
      { iFrame "%".
        iSplit; first auto.
        rewrite Nat.Odd_div2; first last.
        { rewrite Nat.Odd_succ Nat.Even_succ Nat.Odd_succ -Nat.even_spec //. }
        simpl.
        simpl in Hlenᵢ₄.
        rewrite last_lookup Hlenᵢ₄ /= in Hindex₄.
        rewrite Hlenᵢ₃ -Nat.Even_div2 // in Hagreeᵢ; first last.
        { rewrite -Nat.even_spec //. }
        simplify_eq. iFrame "%".
        rewrite Heven.
        iFrame. rewrite Hbackup₃ //. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      rewrite /strip.
      wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iClear "Hlock".
      iInv readN as "(%ver₅ & %log₅ & %actual₅ & %cache₅ & %marked_backup₅ & %backup₅ & %backup₅' & %index₅ & %validated₅ & >Hver & >Hbackup & >Hγ & >%Hunboxed₅ & >#□Hbackup₅ & >%Hindex₅ & >%Hvalidated₅ & >%Hlenactual₅ & >%Hlencache₅ & >%Hloglen₅ & Hlogtokens & >%Hlogged₅ & >●Hγₕ & >%Hlenᵢ₅ & >%Hnodup₅ & >%Hrange₅ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₅ & Hlock & ●Hγ_val & >%Hvallogged₅)" "Hcl".
      iInv cached_wfN as "(%ver'' & %log₅' & %actual₅' & %marked_backup₅' & %backup₅'' & %requests₅ & %vers₅ & %index₅' & %order₅ & %idx₅ & >●Hγᵥ'' & >Hbackup₅' & >Hγ' & >%Hcons₅' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₅ & >%Hvers₅ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₅ & >%Hinj₅ & >%Hidx₅ & >%Hmono₅ & >%Hubord₅)" "Hcl'".
      iCombine "Hbackup Hbackup₅'" gives %[_ <-].
      destruct (decide (marked_backup₅ = InjLV #ldes')) as [-> | Hneq]; first last.
      { wp_cmpxchg_fail.
        iMod ("Hcl'" with "[$Hbackup₅' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ'' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame "%". }
        iMod ("Hcl" with "[$Hγ $□Hbackup₅ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
        { iFrame "%". }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        rewrite /strip.
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$]"). }
      iCombine "Hbackup Hbackup₅'" as "Hbackup".
      wp_cmpxchg_suc.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ''") as %[_ <-].
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
      iCombine "Hγ Hγ'" gives %[_ [=->->]].
      destruct Hvalidated₅ as [[=<-] | ([=] & _ & _)].
      iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ₄". simplify_eq.
      iDestruct (mono_nat_lb_own_valid with "●Hγᵥ Hlb₃") as %[_ Hless₃].
      iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ₃") as "%Hagreeᵢ₂₄".
      rewrite Hlenᵢ₂ -Nat.Even_div2 in Hagreeᵢ₂₄; first last.
      { rewrite -Nat.even_spec //. }
      destruct (decide (S (S ver) = ver₅)) as [<- | Hneq]; first last.
      { iExFalso.
        destruct ver₅ as [|[|[|ver₄]]]; try lia.
        simpl in Hlenᵢ₅.
        rewrite last_lookup Hlenᵢ₅ /= in Hindex₅.
        assert (Nat.div2 ver < S (Nat.div2 ver₄)) as Hnever.
        { assert (ver ≤ ver₄) as Hmono'%div2_mono by lia. lia. }
        (* apply NoDup_lookup_ne with (i := S (Nat.div2 ver)) (x := ldes') in Hindex₄ as Hneqq; auto; first last.
        { intros [=Heq]. assert (ver ≤ ver₄) as Hmono%div2_mono by lia. lia. } *)
        eapply StronglySorted_lookup_lt with (i := S (Nat.div2 ver)) (j := S (S (Nat.div2 ver₄))) in Hmono₅; eauto; last lia.
        rewrite /gmap_mono in Hmono₄.
        assert (is_Some (order₅ !! backup₅')) as [ts₅ Hts₅].
        { rewrite -elem_of_dom Hdomord₅.
          rewrite Forall_forall in Hrange₅.
          apply Hrange₅. rewrite list_elem_of_lookup.
          eauto. }
        pose proof (Hmono₅ _ _ Hidx₅ Hts₅) as Hle'.
        rewrite map_Forall_lookup in Hubord₄. 
        apply Hubord₅ in Hts₅. lia. }
      iDestruct "Hbackup" as "[Hbackup Hbackup']".
      iPoseProof (vers_auth_frag_agree with "●Hγ_vers ◯Hγ_vers") as "%Hagreever".
      iMod ("Hcl'" with "[$Hbackup $Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ'' $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame "%". iPureIntro.
        destruct (decide (1 < size log₅)).
        { rewrite bool_decide_eq_true_2 //.
          rewrite bool_decide_eq_true_2 // in Hvers₅.
          destruct Hvers₅ as (ver'' & Hvers₅ & Hlever' & Hubvers₅ & Hinvalid).
          simplify_eq.
          exists ver. repeat split; auto.
          rewrite bool_decide_eq_false_2 //. lia. }
        { rewrite bool_decide_eq_false_2 //.
          rewrite bool_decide_eq_false_2 // in Hvers₅. } }
      iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hldes₅".
      rewrite Hldes₅ /= in Hlogged₅.
      simplify_eq.
      simpl in Hcons₅.
      rewrite Heven in Hcons₅.
      pose proof Hindex₅ as Hindex₅'.
      rewrite last_lookup Hlenᵢ₅ Nat.Odd_div2 /= in Hindex₅; first last.
      { rewrite Nat.Odd_succ Nat.Even_succ Nat.Odd_succ -Nat.even_spec //. }
      simplify_eq.
      rewrite Hldes₅ /= in Hcons₅.
      simplify_eq.
      iMod (validated_auth_update ldes' with "●Hγ_val") as "[●Hγ_val _]".
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hbackup' $Hver $●Hγₕ $□Hbackup₅ $Hlock $●Hγ_val]") as "_".
      { iFrame "%". iPureIntro.
        - repeat split; auto.
          + right. rewrite Nat.Even_succ Nat.Odd_succ -Nat.even_spec //.
          + rewrite Hldes₅ //=.
          + simpl. rewrite Heven Hldes₅ //=.
          + rewrite bool_decide_eq_true_2 //. set_solver.
          + assert (ldes' ∈ dom log₅).
            { rewrite elem_of_dom //. }
            set_solver. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      rewrite /strip.
      wp_pures.
      iModIntro.
      iApply ("HΦ" with "[$]").
    - rewrite Zrem_odd odd_inj even_odd_negb_eq Heven /=.
      destruct ver as [|ver].
      { done. }
      simpl. wp_pures.
      iApply ("HΦ" with "[$]").
  Qed.

  Lemma fupd_split_right `{!invGS Σ} (E1 E2 E3 : coPset) (P : iProp Σ) :
    E2 ⊆ E3 →
    (|={E1,E3}=> P) ⊢ |={E1,E2}=> |={E2,E3}=> P.
  Proof.
    iIntros (HE) "H".
    iApply (fupd_trans E1 E3 E2).
    (* Goal: |={E1,E3}=> |={E3,E2}=> |={E2,E3}=> P *)
    iApply (fupd_mono with "H").
    iIntros "HP".
    iApply (fupd_mask_intro_subseteq E3 E2); first done.
    iExact "HP".
  Qed.

  Lemma execute_lp 
    (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ : gname)
    (l lexp ldes ldes' : loc)
    (dq dq' : dfrac)
    (expected desired cache : list val)
    (Φ : val → iProp Σ)
    (log₁ : gmap loc (gname * list val))
    (backup backup' copy : loc)
    (requests₁ : list (gname * gname * loc))
    (vers₁ order₁ : gmap gname nat)
    (index₁ : list gname)
    (validated : gset loc)
    (idx₁ ver ver₁ ver' i : nat)
    (γₚ γₑ γₗ γₜ : gname) :
    length expected > 0 →
    length expected = length desired →
    length cache = length expected →
    expected ≠ desired →
    last index₁ = Some backup' →
    (if Nat.even ver₁ then snd <$> log₁ !! backup' = Some cache else True) →
    map_Forall (λ _ '(_, value), length value = length expected) log₁ →
    length index₁ = S (Nat.div2 (S ver₁)) →
    NoDup index₁ →
    Forall (.∈ dom log₁) index₁ →
    validated ⊆ dom log₁ →
    dom order₁ = dom log₁ →
    (if bool_decide (1 < size log₁) then
      ∃ ver' : nat, ver' ≤ ver₁ ∧ map_Forall (λ _ ver'', ver'' ≤ ver') vers₁
    else vers₁ = ∅) →
    dom vers₁ ⊂ dom log₁ →
    gmap_injective order₁ →
    order₁ !! backup = Some idx₁ →
    StronglySorted (gmap_mono order₁) index₁ →
    map_Forall (λ _ idx', idx' ≤ idx₁) order₁ →
    Forall val_is_unboxed desired →
    (* Persistent hypotheses *)
    inv readN (read_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
    inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
    inv casN (cas_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired) -∗
    registered γᵣ i γₗ γₑ backup -∗
    log_frag_own γₕ backup γₚ expected -∗
    backup ↦∗□ expected -∗
    (* Spatial hypotheses *)
    token γₜ -∗
    ldes' ↦∗ desired -∗
    l ↦ #ver₁ -∗
    log_tokens log₁ -∗
    mono_nat_auth_own γᵥ (1/4) ver₁ -∗
    (l +ₗ 2) ↦∗{#1/2} cache -∗
    (if Nat.even ver₁ then
      index_auth_own γᵢ (1/4) index₁ ∗
      mono_nat_auth_own γᵥ (1/4) ver₁ ∗
      (l +ₗ 2) ↦∗{#1/2} cache
    else True) -∗
    (▷ read_inv γ γᵥ γₕ γᵢ γ_val l (length expected) ={⊤ ∖ ↑readN, ⊤}=∗ emp) -∗
    mono_nat_auth_own γᵥ (1/2) ver₁ -∗
    registry γᵣ requests₁ -∗
    registry_inv γ backup expected requests₁ (dom log₁) -∗
    vers_auth_own γ_vers 1 vers₁ -∗
    index_auth_own γᵢ (1/2) index₁ -∗
    vers_auth_own γₒ 1 order₁ -∗
    (▷ cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l ={⊤ ∖ ↑readN ∖ ↑cached_wfN, ⊤ ∖ ↑readN}=∗ emp) -∗
    own γᵢ (●{#1/4} map_seq 0 (to_agree <$> index₁)) -∗
    validated_auth_own γ_val 1 validated -∗
    ghost_var γ (1/2) (backup, expected) -∗
    (l +ₗ 1) ↦ InjLV #ldes' -∗
    own γₕ (● (fmap (M:=gmap loc) to_agree log₁))
    ={⊤ ∖ ↑readN ∖ ↑cached_wfN, ⊤}=∗
      ⌜log₁ !! ldes' = None⌝ ∗
      (lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #true) ∗
      vers_frag_own γ_vers ldes' ver₁ ∗
      (∃ γₚ', log_frag_own γₕ ldes' γₚ' desired) ∗
      ldes' ↦∗□ desired ∗
      vers_frag_own γₒ ldes' (S idx₁).
  Proof.
    iIntros (Hpos Hleneq Hlencache Hne Hindex₁ Hcache₁ Hloglen₁ Hlenᵢ₁ Hnodup₁ Hrange₁ 
            Hvallogged Hdomord Hvers₁ Hdomvers₁ Hinj₁ Hidx₁ Hmono₁ Hubord₁ Hunboxed).
    iIntros "#Hreadinv #Hinv #Hcasinv #◯Hγᵣ #◯Hγₕ #□Hbackup".
    iIntros "Hγₜ Hldes' Hver Hlogtokens ●Hγᵥ Hcache".
    iIntros "Hlock Hcl ●Hγᵥ' ●Hγᵣ Hreginv ●Hγ_vers ●Hγᵢ' ●Hγₒ Hcl' ●Hγᵢ ●Hγ_val Hγ Hbackup₁ ●Hγₕ".
    simplify_eq.
    (* Derive agreement facts from auth-frag combinations *)
    iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hagree".
    iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogged₁'".
    (* Derive the snd projection fact from Hlogged₁' *)
    assert (snd <$> log₁ !! backup = Some expected) as Hlogged₁.
    { rewrite Hlogged₁' //. }
    (* The new backup pointer cannot be logged, as we have persistent pointsto for all of the previous backup pointers, and full pointsto for the new backup *)
    iAssert (⌜log₁ !! ldes' = None⌝)%I as "%Hldes'fresh".
    { destruct (log₁ !! ldes') eqn:Hbound; last done.
      iExFalso.
      iPoseProof (big_sepM_lookup with "Hlogtokens") as "Hlogged".
      { done. }
      destruct p.
      iDestruct "Hlogged" as "[_ Hldes'₁]".
      iApply (array_pointsto_pointsto_persist with "Hldes' Hldes'₁").
      { rewrite map_Forall_lookup in Hloglen₁.
        apply Hloglen₁ in Hbound. lia. }
      lia. }
    (* Split the registry invariant into three parts
        1) That corresponds to requests before this CAS
        2) That corresponding to this CAS
        3) Any following this CAS *)
    rewrite -(take_drop_middle _ _ _ Hagree).
    rewrite /registry_inv big_sepL_app big_sepL_cons /request_inv.
    iDestruct "Hreginv" as "(Hlft & (%Hbackupin & Hγₗ & %Φ' & %γₜ' & %lexp' & %ldes'' & %dq₁ & %dq₂ & %expected' & %desired' & Hγₑ & ?) & Hrht)".
    iInv casN as "[(HΦ & [%b >Hγₑ'] & >Hγₗ') | [(>Hcredit & AU & >Hγₑ' & >Hγₗ') | (>Htok & [%b >Hγₑ'] & [%b' >Hγₗ'])]]" "Hclose".
    (* Assumes we have already returned, which is impossible *)
    3: iCombine "Hγₜ Htok" gives %[].
    { (* Assumes we have already linearized, which again is impossible *)
    by iCombine "Hγₗ Hγₗ'" gives %[_ ?%bool_decide_eq_false]. }
    iCombine "Hγₑ Hγₑ'" gives %[_ <-%bool_decide_eq_true].
    iMod (ghost_var_update_halves false with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
    rewrite bool_decide_eq_true_2; last done.
    (* Now update the ghost state. This CAS will linearize first, invalidating all other pending CAS's and causing them to fail *)
    iMod (ghost_var_update_halves false with "Hγₗ Hγₗ'") as "[Hlin Hlin']".
    (* Execute our LP *)
    iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
    iMod "AU" as (vs' backup''') "[Hγ' [_ Hconsume]]".
    rewrite /value.
    iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
    iMod (ghost_var_update_halves (ldes', desired) with "Hγ Hγ'") as "[Hγ Hγ']".
    simplify_eq.
    rewrite bool_decide_eq_true_2; last done.
    iMod ("Hconsume" with "[$Hγ']") as "HΦ".
    iMod ("Hclose" with "[Hγₜ Hlin' Hγₑ']") as "_".
    { do 2 iRight. iFrame. }
    (* Now linearize all other CAS's (in arbitrary order) *)
    iMod (linearize_cas with "Hlogtokens Hγ Hlft") as "(Hlogtokens & Hγ & Hlft)".
    { done. }
    { done. }
    { done. }
    { done. }
    { by destruct (log₁ !! ldes'). }
    iMod (linearize_cas with "Hlogtokens Hγ Hrht") as "(Hlogtokens & [Hγ Hγ'] & Hrht)".
    { done. }
    { done. }
    { done. }
    { done. }
    { by destruct (log₁ !! ldes'). }
    replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
    (* We now will insert this backup into the log *)
    (* First, we allocate a token representing the pointsto for the backup *)
    iMod token_alloc as "[%γₚ' Hγₚ']".
    (* Now update the log *)
    iMod (log_auth_update ldes' desired γₚ' with "●Hγₕ") as "[[●Hγₕ ●Hγₕ'] #◯Hγₕ₁]".
    { done. }
    iDestruct "Hbackup₁" as "[Hbackup₁ Hbackup₁']".
    assert (O < size log₁) as Hlogsome₁.
    { assert (size log₁ ≠ 0); last lia.
      rewrite map_size_ne_0_lookup.
      naive_solver. }
    assert (ldes' ∉ dom log₁) as Hldes'freshdom.
    { rewrite not_elem_of_dom //. }
    iMod (vers_auth_update ldes' ver₁ with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_vers]".
    { rewrite -not_elem_of_dom. set_solver. }
    (* iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy]". *)
    (* iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy]". *)
    assert (size (<[ldes':=(γₚ', desired)]> log₁) > 1) as Hvers₁multiple.
    { rewrite map_size_insert_None //. lia. }
    iMod (own_auth_split_self with "●Hγₕ") as "[●Hγₕ ◯Hγₕcopy]".
    assert (map_Forall (λ _ ver'', ver'' ≤ ver₁) (<[ldes':=ver₁]> vers₁)) as Hub₁.
    { destruct (decide (size log₁ = 1)) as [Hsing | Hsing].
      - rewrite bool_decide_eq_false_2 in Hvers₁; last lia.
        subst. rewrite insert_empty map_Forall_singleton //.
      - rewrite bool_decide_eq_true_2 in Hvers₁; last lia.
        rewrite map_Forall_insert.
        destruct Hvers₁ as (ver_invalid₁ & Hver_invalid_le₁ & Hub).
        split; first done.
        eapply map_Forall_impl; first done.
        intros l' ver''.
        simpl. lia.
        rewrite -not_elem_of_dom. set_solver. }
    iMod (vers_auth_update ldes' (S idx₁) with "●Hγₒ") as "[●Hγₒ ◯Hγₒ]".
    { rewrite -not_elem_of_dom. set_solver. }
    iMod ("Hcl'" with "[$●Hγ_vers $●Hγᵥ' $●Hγᵣ $●Hγₕ $Hbackup₁ $Hγ Hlft Hrht Hlin Hγₑ $●Hγₒ $●Hγᵢ']") as "_".
    { rewrite lookup_insert_eq. iExists (S idx₁).
      rewrite (take_drop_middle _ _ _ Hagree).
      rewrite bool_decide_eq_true_2; last lia.
      iSplit.
      { done. }
      iNext. iSplit.
      { iApply (registry_inv_mono _ _ _ _ (dom log₁)).
        { set_solver. }
        rewrite -{3}(take_drop_middle _ _ _ Hagree) /registry_inv.
        iFrame.
        rewrite /request_inv.
        iFrame "% #".
        rewrite bool_decide_eq_false_2; last first.
        { intros <-. congruence. }
        rewrite bool_decide_eq_false_2; last done.
        iFrame. }
        iSplit.
        { iPureIntro. do 2 rewrite dom_insert. set_solver. }
        iPureIntro.
        split.
        - exists ver₁.
          rewrite lookup_insert_eq.
          repeat split; auto.
          rewrite bool_decide_eq_true_2 //.
        - repeat split.
          { set_solver. }
          { apply gmap_injective_insert; last done.
            intros [loc Hcontra]%elem_of_map_img.
            eapply map_Forall_lookup_1 in Hcontra; last done.
            simpl in Hcontra. lia. }
          { rewrite lookup_insert_eq //. }
          { apply gmap_mono_alloc; last done.
            rewrite Forall_forall in Hrange₁. auto. }
          { rewrite map_Forall_insert. split; first done.
            eapply map_Forall_impl; eauto.
            rewrite -not_elem_of_dom. set_solver. } }
    iAssert (⌜backup ≠ ldes'⌝)%I as "%Hnoaba".
    { iIntros (->). 
      iApply (array_pointsto_pointsto_persist with "Hldes' □Hbackup"); first done.
      lia. }
    assert (backup' ≠ ldes') as Hnoaba'.
    { intros ->. 
      apply last_Some_elem_of in Hindex₁.
      rewrite Forall_forall in Hrange₁.
      apply Hrange₁ in Hindex₁.
      rewrite elem_of_dom in Hindex₁.
      destruct Hindex₁.
      congruence. }
    iMod (array_persist with "Hldes'") as "#Hldes'".
    iPoseProof (log_tokens_update with "Hlogtokens Hγₚ' Hldes'") as "Hlogtokens".
    { done. }
    iMod ("Hcl" with "[$Hγ' $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hbackup₁' $Hver $●Hγₕ' $●Hγ_val]") as "_".
    { iFrame "% # ∗". repeat iSplit; auto.
      (* { iPureIntro. left. split; first done. set_solver. } *)
      { rewrite map_Forall_insert //. }
      { rewrite lookup_insert_eq //=. }
      { iPureIntro. eapply Forall_impl; first done.
        simpl. set_solver. }
      { iPureIntro. destruct (Nat.even ver₁) eqn:Heven₁; last done.
        rewrite lookup_insert_ne; auto. }
      { rewrite bool_decide_eq_false_2 //. set_solver. }
      { rewrite dom_insert. iPureIntro. set_solver. } }
    iModIntro.
    iFrame "% # ∗".
  Qed.


  Lemma Forall2_symmetric {A} (R : relation A) :
    Symmetric R → Symmetric (Forall2 R).
  Proof.
    intros Hsym xs ys Hxy.
    induction Hxy; by constructor.
  Qed.

  Lemma all_vals_compare_safe vs vs' :
    Forall val_is_unboxed vs →
      length vs = length vs' →
        Forall2 vals_compare_safe vs vs'.
  Proof.
    revert vs'. induction vs as [| v vs IH].
    - intros vs' Hunboxed Hlen. 
      symmetry in Hlen. 
      rewrite length_zero_iff_nil in Hlen. simplify_eq. constructor.
    - intros vs' Hunboxed Hlen.
      destruct vs' as [|v' vs'].
      { done. }
      simplify_eq. inv Hunboxed. constructor.
      + by left.
      + auto.
  Qed.

  Lemma cas_spec (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ : gname) (l lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val) :
    length expected > 0 → length expected = length desired → Forall val_is_unboxed expected → Forall val_is_unboxed desired → 
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
        inv cached_wfN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
          lexp ↦∗{dq} expected -∗
            ldes ↦∗{dq'} desired -∗
              <<{ ∀∀ backup actual, value γ backup actual  }>> 
                cas (length expected) #l #lexp #ldes @ ↑N
              <<{ if bool_decide (actual = expected) then ∃ backup', value γ backup' desired else value γ backup actual |
                  RET #(bool_decide (actual = expected)); lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired }>>.
    Proof.
      iIntros (Hpos Hleneq Hexpunboxed Hdesunboxed) "#Hreadinv #Hinv Hlexp Hldes %Φ AU". 
      wp_rec.
      wp_pure credit:"Hcredit".
      wp_pures.
      awp_apply (read'_spec with "[//]").
      { done. }
      rewrite /atomic_acc /=.
      iInv cached_wfN as "(%ver' & %log & %actual & %marked_backup & %backup & %requests & %vers & %index & %order & %idx & ●Hγᵥ' & >Hvalidated & >Hγ & >%Hcons & >●Hγₕ & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hvers & Hord)" "Hcl".
      iMod "AU" as (backup'' actual') "[Hγ' Hlin]".
      rewrite /value.
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      iExists backup, actual.
      iFrame "Hγ'".
      iModIntro.
      iSplit.
      { iIntros "Hγ'".
        iDestruct "Hlin" as "[Hclose _]".
        iMod ("Hclose" with "Hγ'") as "AU".
        iMod ("Hcl" with "[-Hlexp Hldes AU Hcredit]") as "_".
        { iFrame "∗ %". }
        by iFrame. }
      iIntros (marked_backup' copy backup' ver γₚ) "Hγ'".
      iCombine "Hγ Hγ'" gives %[_ [=<-]].
      destruct (decide (actual = expected)) as [-> | Hne]; first last.
      { iDestruct "Hlin" as "[_ Hconsume]".
        rewrite bool_decide_eq_false_2; last done.
        iMod ("Hconsume" with "Hγ'") as "HΦ".
        iMod ("Hcl" with "[-Hlexp Hldes HΦ]") as "_".
        { iFrame "∗ %". }
        iModIntro.
        iIntros "(Hcopy & %Hunboxed & %Hcopylen & Hbackup & ◯Hγᵥ & Hcons)".
        wp_pures.
        rewrite -Hcopylen.
        wp_apply (wp_array_equal with "[$Hcopy $Hlexp]").
        { done. }
        { by apply all_vals_compare_safe. }
        iIntros "[Hcopy Hlexp]".
        rewrite bool_decide_eq_false_2; last done.
        wp_pures. iApply ("HΦ" with "[$]"). }
      destruct (decide (expected = desired)) as [-> | Hne].
      { iDestruct "Hlin" as "[_ Hconsume]".
        rewrite bool_decide_eq_true_2; last done.
        iFrame.
        iMod ("Hconsume" with "[$Hγ']") as "HΦ".
        iMod ("Hcl" with "[-Hlexp Hldes HΦ]") as "_".
        { iFrame "∗ %". }
        iModIntro. iIntros "(Hcopy & %Hcopylen & Hbackup & #◯Hγᵥ & Hcons)".
        wp_pures.
        wp_apply (wp_array_equal with "[$Hcopy $Hlexp]").
        { done. }
        { by apply all_vals_compare_safe. }
        iIntros "[Hcopy Hlexp]".
        rewrite bool_decide_eq_true_2; last done.
        wp_pures.
        wp_apply (wp_array_equal with "[$Hlexp $Hldes]").
        { done. }
        { by apply all_vals_compare_safe. }
        iIntros "[Hlexp Hldes]".
        rewrite bool_decide_eq_true_2; last done.
        wp_pures.
        iApply ("HΦ" with "[$]"). }
      iMod (ghost_var_alloc true) as "(%γₑ & Hγₑ & Hγₑ')".
      iMod (ghost_var_alloc true) as "(%γₗ & Hγₗ & Hγₗ')".
      iMod token_alloc as "[%γₜ Hγₜ]".
      iMod (registry_update γₗ γₑ backup with "●Hγᵣ") as "[●Hγᵣ #◯Hγᵣ]". 
      iDestruct "Hlin" as "[Hclose _]".
      iMod ("Hclose" with "Hγ'") as "AU".
      iMod (inv_alloc casN _ (cas_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired) with "[Hγₑ' Hγₗ' AU Hcredit]") as "#Hcasinv".
      { iRight. iLeft. iFrame. }
      iMod ("Hcl" with "[-Hlexp Hldes Hγₜ]") as "_".
      { rewrite /cached_wf_inv.
        iFrame "∗ %".
        rewrite big_sepL_singleton /request_inv bool_decide_eq_true_2; last done.
        iFrame.
        iSplit.
        { iPureIntro. rewrite elem_of_dom /is_Some. rewrite -lookup_fmap lookup_fmap_Some in Hcons.
          destruct Hcons as ([? ?] & <- & ?). eauto. }
        iExists Φ, γₜ, lexp, ldes, dq, dq', expected, desired.
        rewrite bool_decide_eq_true_2; last done.
        iFrame "∗ #". }
      iIntros "!> (Hcopy & %Hunboxed & _ & #◯Hγₕ & #◯Hγᵥ & Hpost)".
      wp_pures.
      wp_apply (wp_array_equal with "[$Hcopy $Hlexp]").
      { done. }
      { by apply all_vals_compare_safe. }
      iIntros "[Hcopy Hlexp]".
      rewrite bool_decide_eq_true_2; last done.
      wp_pures.
      wp_apply (wp_array_equal with "[$Hlexp $Hldes]").
      { done. }
      { by apply all_vals_compare_safe. }
      iIntros "[Hlexp Hldes]".
      rewrite bool_decide_eq_false_2; last done.
      wp_pures.
      wp_apply (wp_array_clone with "[$]").
      { lia. }
      { lia. }
      iIntros (ldes') "[Hldes' Hldes]".
      wp_pure credit:"Hcredit".
      wp_pure credit:"Hcredit'".
      wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iInv readN as "(%ver₁ & %log₁ & %actual₁ & %cache₁ & %marked_backup₁ & %backup₁ & %backup₁' & %index₁ & %validated & >Hver & >Hbackup₁ & >Hγ & >%Hunboxed₁ & >#□Hbackup & >%Hindex₁ & >%Hvalidated₁ & >%Hlenactual₁ & >%Hlencache₁ & >%Hloglen₁ & Hlogtokens & >%Hlogged₁ & >●Hγₕ & >%Hlenᵢ₁ & >%Hnodup₁ & >%Hrange₁ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₁ & Hlock & >●Hγ_val & >%Hval & >%Hvallogged)" "Hcl".
      iInv cached_wfN as "(%ver'' & %log₁' & %actual₁' & %marked_backup₁' & %backup₁'' & %requests₁ & %vers₁ & %index₁' & %order₁ & %idx₁ & >●Hγᵥ' & >Hbackup₁' & >Hγ' & >%Hcons₁' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₁ & >%Hvers₁ & >●Hγᵢ' & >●Hγₒ & >%Hdomord & >%Hinj₁ & >%Hidx₁ & >%Hmono₁ & >%Hubord₁)" "Hcl'".
      iPoseProof (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as "<-".
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
      iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
      iMod (validated_auth_frag_dup with "●Hγ_val") as "[●Hγ_val ◯Hγ_val₁]".
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      iCombine "Hbackup₁ Hbackup₁'" gives %[_ <-].
      iPoseProof (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as "<-".
      iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₁".
      iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ") as %[_ Hle₁].
      (* iCombine "●Hγₕ ●Hγₕ'" as "●Hγₕ". *)
      (* rewrite dfrac_op_own Qp.half_half Qp.quarter_quarter. *)
      clear Hvers ver'.
      iDestruct "Hpost" as "[(-> & ◯Hγ_val & %ver' & #◯Hγᵥ' & %Hle & ◯Hγᵢ') | ->]";
      destruct Hvalidated₁ as [-> | (-> & Heven%Nat.even_spec & -> & ->)].
      - (* Old backup was validated, but current backup is not *)
        wp_cmpxchg_fail.
        iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ #◯Hγₒcopy]".
        iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers #◯Hγ_verscopy]".
        (* iDestruct "Hγ" as "[Hγ Hγ']". *)
        (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
        (* iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']". *)
        destruct (decide (backup₁ ∈ validated)) as [Hmem | Hnmem].
        { rewrite bool_decide_eq_true_2 // in Hval. }
        iMod ("Hcl'" with "[$Hbackup₁' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame "%". }
        iMod ("Hcl" with "[$Hγ $□Hbackup $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup₁ $●Hγ_val]") as "_".
        { iFrame "%". auto. }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        rewrite /strip.
        wp_pures.
        wp_bind (CmpXchg _ _ _).
        (* Consider the case where the next CAS succeeds or fails *)
        iInv readN as "(%ver₂ & %log₂ & %actual₂ & %cache₂ & %marked_backup₂ & %backup₂ & %backup₂' & %index₂ & %validated₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlogtokens & >%Hlogged₂ & >●Hγₕ & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hval₂ & >%Hvallogged₂)" "Hcl".
        iInv cached_wfN as "(%ver'' & %log₂' & %actual₂' & %marked_backup₂' & %backup₂'' & %requests₂ & %vers₂ & %index₂' & %order₂ & %idx₂ & >●Hγᵥ' & >Hbackup₂' & >Hγ' & >%Hcons₂' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₂ & >%Hvers₂ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₂ & >%Hinj₂ & >%Hidx₂ & >%Hmono₂ & >%Hubord₂)" "Hcl'".
        iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
        iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₂".
        iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
        iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₂].
        iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₂]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        iCombine "Hbackup Hbackup₂'" gives %[_ <-].
        iCombine "●Hγₕ ●Hγₕ'" as "●Hγₕ".
        (* Note: Hpost was already destructed in the outer case, so we reuse ver' and ◯Hγᵢ' *)
        destruct Hvalidated₂ as [-> | (-> & Heven%Nat.even_spec & -> & ->)].
        + (* Old backup was validated, but current backup is not *)
          destruct (decide (backup₂ ∈ validated₂)) as [Hmem₂ | Hnmem₂].
          { rewrite bool_decide_eq_true_2 // in Hval₂. }
          wp_cmpxchg_fail.
          rewrite /registry_inv /registered.
          iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
          iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
          { done. }
          simpl.
          iPoseProof (validated_auth_frag_agree with "●Hγ_val ◯Hγ_val") as "%Hmem".
          iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
          { intros <-. set_solver. }
          iPoseProof ("Hreginv" with "[$]") as "Hreginv".
          (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
          iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']".
          iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
          { iFrame "%". }
          iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
          { iFrame "%". auto. }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          rewrite /strip.
          by wp_pures.
        + (* Both the current and expected backup are validated *)
          iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree".
          iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₁'].
          (* Consider whether the current and expected backup pointers are equal *)
          destruct (decide (backup₂' = backup)) as [-> | Hneq].
          * (* The CAS will succeed, swapping in the new backup  *)
            rewrite -lookup_fmap lookup_fmap_Some in Hcons₂'.
            destruct Hcons₂' as ([? ?] & <- & Hlogged₂').
            rewrite Hlogged₂' in Hlogagree.
            iCombine "Hbackup Hbackup₂'" as "Hbackup".
            wp_cmpxchg_suc.
            simplify_eq. simpl in *.
            iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
            iCombine "Hγ Hγ'" as "Hγ".
            rewrite Qp.quarter_quarter.
            iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy']".
            iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy']".
            iMod (execute_lp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ expected _ _ backup backup copy with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "(%Hfresh & HΦ & #◯Hγ_vers & [%γₚ' #◯Hγₕ₁] & #Hldes' & #◯Hγₒ)"; try done.
            { rewrite Heven //. }
            { destruct (decide (1 < size log₂)).
              - rewrite bool_decide_eq_true_2 //.
                rewrite bool_decide_eq_true_2 // in Hvers₂.
                destruct Hvers₂ as (? & ? & ? & ? & ?).
                eexists. eauto.
              - rewrite bool_decide_eq_false_2 //.
                rewrite bool_decide_eq_false_2 // in Hvers₂.  }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            wp_pures.
            wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ index₂ order₂ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]").
            { done. }
            { done. }
            { lia. }
            { done. }
            { done. }
            { eapply Forall_impl; eauto. simpl. intros l' Hl'. set_solver. }
            { done. }
            { rewrite -not_elem_of_dom Hdomord₂ not_elem_of_dom //. }
            iIntros "Hldes".
            wp_pures.
            iApply ("HΦ" with "[$]").
          * wp_cmpxchg_fail.
            rewrite /registry_inv /registered.
            iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
            iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
            { done. }
            simpl.
            iPoseProof (validated_auth_frag_agree with "●Hγ_val ◯Hγ_val") as "%Hmem".
            iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
            { intros <-. set_solver. }
            iPoseProof ("Hreginv" with "[$]") as "Hreginv".
            (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
            iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']".
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". iPureIntro. rewrite -Nat.even_spec. auto. } 
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
      - (* Both the current and expected backup are validated *)
        (* The CAS may succeed, depending on the actual value *)
        iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree".
        iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₁'].
        (* Consider whether the current and expected backup pointers are equal *)
        destruct (decide (backup₁' = backup)) as [-> | Hneq].
        + (* The first CAS will succeed, swapping in the new backup  *)
          rewrite -lookup_fmap lookup_fmap_Some in Hcons₁'.
          destruct Hcons₁' as ([? ?] & <- & Hlogged₁').
          rewrite Hlogged₁' in Hlogagree.
          iCombine "Hbackup₁ Hbackup₁'" as "Hbackup₁".
          wp_cmpxchg_suc.
          simplify_eq.
          simpl.
          iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy']".
          iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy']".
          iCombine "Hγ Hγ'" as "Hγ".
          iCombine "●Hγₕ ●Hγₕ'" as "●Hγₕ".
          rewrite Qp.quarter_quarter.
          iMod (execute_lp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ expected _ _ backup backup copy with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "(%Hfresh & HΦ & #◯Hγ_vers & [%γₚ' #◯Hγₕ₁] & #Hldes' & #◯Hγₒ)"; try done.
          { rewrite Heven //. }
          { destruct (decide (1 < size log₁)).
            - rewrite bool_decide_eq_true_2 //.
              rewrite bool_decide_eq_true_2 // in Hvers₁.
              destruct Hvers₁ as (? & ? & ? & ? & ?).
              eexists. eauto.
            - rewrite bool_decide_eq_false_2 //.
              rewrite bool_decide_eq_false_2 // in Hvers₁.  }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          wp_pures.
          (* wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ index₁ order₁ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]"). *)
          wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ver₁ _ index₁ order₁ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]").
          { done. }
          { done. }
          { lia.  }
          { done. }
          { done. }
          { eapply Forall_impl; eauto. simpl. intros l' Hl'. set_solver. }
          { done. }
          { rewrite -not_elem_of_dom Hdomord not_elem_of_dom //. }
          iIntros "Hldes".
          wp_pures.
          iModIntro. iApply ("HΦ" with "[$]").
        + wp_cmpxchg_fail.
          iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ #◯Hγₒcopy]".
          iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers #◯Hγ_verscopy]".
          iMod ("Hcl'" with "[$Hbackup₁ $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
          { iFrame "%". }
          iMod ("Hcl" with "[$Hγ $□Hbackup $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup₁' $●Hγ_val]") as "_".
          { iFrame "%". auto. rewrite -Nat.even_spec. iPureIntro. auto. }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          rewrite /strip.
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          (* Consider the case where the next CAS succeeds or fails *)
          iInv readN as "(%ver₂ & %log₂ & %actual₂ & %cache₂ & %marked_backup₂ & %backup₂ & %backup₂' & %index₂ & %validated₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlogtokens & >%Hlogged₂ & >●Hγₕ & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hval₂ & >%Hvallogged₂)" "Hcl".
          iInv cached_wfN as "(%ver'' & %log₂' & %actual₂' & %marked_backup₂' & %backup₂'' & %requests₂ & %vers₂ & %index₂' & %order₂ & %idx₂ & >●Hγᵥ' & >Hbackup₂' & >Hγ' & >%Hcons₂' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₂ & >%Hvers₂ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₂ & >%Hinj₂ & >%Hidx₂ & >%Hmono₂ & >%Hubord₂)" "Hcl'".
          iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
          iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₂".
          iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
          iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₂].
          iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₂]".
          iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
          iCombine "Hbackup Hbackup₂'" gives %[_ <-].
          iCombine "●Hγₕ ●Hγₕ'" as "●Hγₕ".
          (* Note: Hpost was already destructed in the outer case, so we reuse ver' and ◯Hγᵢ' *)
          destruct Hvalidated₂ as [-> | (-> & Heven₂%Nat.even_spec & -> & ->)].
          * (* Old backup was validated, but current backup is not *)
            destruct (decide (backup₂ ∈ validated₂)) as [Hmem₂ | Hnmem₂].
            { rewrite bool_decide_eq_true_2 // in Hval₂. }
            wp_cmpxchg_fail.
            rewrite /registry_inv /registered.
            iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
            iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
            { done. }
            simpl.
            iPoseProof (validated_auth_frag_agree with "●Hγ_val ◯Hγ_val") as "%Hmem".
            iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
            { intros <-. set_solver. }
            iPoseProof ("Hreginv" with "[$]") as "Hreginv".
            (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
            iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']".
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". auto. }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
          * (* Both the current and expected backup are validated *)
            iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree₂".
            (* iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₂']. *)
            (* Consider whether the current and expected backup pointers are equal *)
            destruct (decide (backup₂' = backup)) as [-> | Hneq₂].
            -- (* The CAS will succeed, swapping in the new backup  *)
              rewrite -lookup_fmap lookup_fmap_Some in Hcons₂'.
              destruct Hcons₂' as ([? ?] & <- & Hlogged₂').
              rewrite Hlogged₂' in Hlogagree₂.
              iCombine "Hbackup Hbackup₂'" as "Hbackup".
              wp_cmpxchg_suc.
              simplify_eq. simpl in *.
              iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
              iCombine "Hγ Hγ'" as "Hγ".
              rewrite Qp.quarter_quarter.
              iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy']".
              iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy']".
              iMod (execute_lp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ expected _ _ backup backup copy with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "(%Hfresh & HΦ & #◯Hγ_vers & [%γₚ' #◯Hγₕ₁] & #Hldes' & #◯Hγₒ)"; try done.
              { rewrite Heven₂ //. }
              { destruct (decide (1 < size log₂)).
                - rewrite bool_decide_eq_true_2 //.
                  rewrite bool_decide_eq_true_2 // in Hvers₂.
                  destruct Hvers₂ as (? & ? & ? & ? & ?).
                  eexists. eauto.
                - rewrite bool_decide_eq_false_2 //.
                  rewrite bool_decide_eq_false_2 // in Hvers₂. }
              iApply fupd_mask_intro.
              { set_solver. }
              iIntros ">_ !>".
              wp_pures.
              wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ index₂ order₂ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]").
              { done. }
              { done. }
              { lia. }
              { done. }
              { done. }
              { eapply Forall_impl; eauto. simpl. intros l' Hl'. set_solver. }
              { done. }
              { rewrite -not_elem_of_dom Hdomord₂ not_elem_of_dom //. }
              iIntros "Hldes".
              wp_pures.
              iApply ("HΦ" with "[$]").
            -- wp_cmpxchg_fail.
              rewrite /registry_inv /registered.
              iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
              iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
              { done. }
              simpl.
              iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
              { intros <-. set_solver. }
              iPoseProof ("Hreginv" with "[$]") as "Hreginv".
              (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
              iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']".
              iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
              { iFrame "%". }
              iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
              { iFrame "%". iPureIntro. rewrite -Nat.even_spec. auto. } 
              iApply fupd_mask_intro.
              { set_solver. }
              iIntros ">_ !>".
              rewrite /strip.
              by wp_pures.
      - (* Both the current and expected backup are validated *)
        (* The CAS may succeed, depending on the actual value *)
        iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree".
        (* iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₁']. *)
        (* Consider whether the current and expected backup pointers are equal *)
        destruct (decide (backup₁ = backup)) as [-> | Hneq].
        + (* The first CAS will succeed, swapping in the new backup  *)
          rewrite -lookup_fmap lookup_fmap_Some in Hcons₁'.
          destruct Hcons₁' as ([? ?] & <- & Hlogged₁').
          (* rewrite Hlogged₁' in Hlogagree. *)
          iCombine "Hbackup₁ Hbackup₁'" as "Hbackup₁".
          wp_cmpxchg_suc.
          simpl.
          iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy']".
          iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy']".
          iCombine "Hγ Hγ'" as "Hγ".
          iCombine "●Hγₕ ●Hγₕ'" as "●Hγₕ".
          rewrite Qp.quarter_quarter.
          rewrite Hlogagree in Hlogged₁'.
          injection Hlogged₁' as [=<-<-].
          simplify_eq. simpl in *.
          iMod (execute_lp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cache₁ _ _ backup backup₁' copy with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "(%Hfresh & HΦ & #◯Hγ_vers & [%γₚ' #◯Hγₕ₁] & #Hldes' & #◯Hγₒ)"; try done.
          { by destruct (Nat.even ver₁). }
          { destruct (decide (1 < size log₁)).
            - rewrite bool_decide_eq_true_2 //.
              rewrite bool_decide_eq_true_2 // in Hvers₁.
              destruct Hvers₁ as (? & ? & ? & ? & ?).
              eexists. eauto.
            - rewrite bool_decide_eq_false_2 //.
              rewrite bool_decide_eq_false_2 // in Hvers₁.  }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          wp_pures.
          (* wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ index₁ order₁ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]"). *)
          wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ver₁ _ index₁ order₁ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]").
          { done. }
          { done. }
          { lia.  }
          { done. }
          { done. }
          { eapply Forall_impl; eauto. simpl. intros l' Hl'. set_solver. }
          { done. }
          { rewrite -not_elem_of_dom Hdomord not_elem_of_dom //. }
          iIntros "Hldes".
          wp_pures.
          iModIntro. iApply ("HΦ" with "[$]").
        + wp_cmpxchg_fail.
          iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ #◯Hγₒcopy]".
          iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers #◯Hγ_verscopy]".
          rewrite /registry_inv /registered.
          iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
          iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
          { done. }
          simpl.
          iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
          { done. }
          iPoseProof ("Hreginv" with "[$]") as "Hreginv".
          assert (is_Some (order₁ !! backup)) as [ts Hts].
          { rewrite -elem_of_dom Hdomord elem_of_dom //. }
          apply Hubord₁ in Hts as Hts'.
          assert (ts ≠ idx₁) as Hdifftime.
          { intros ->. assert (backup = backup₁); last done.
            by eapply Hinj₁. }
          assert (ts < idx₁) as Hlesstime by lia.
          iMod (vers_frag_alloc_singleton _ backup₁ idx₁ with "●Hγₒ") as "[●Hγₒ ◯Hγₒ₁]".
          { done. }
          iMod (vers_frag_alloc_singleton _ backup ts with "●Hγₒ") as "[●Hγₒ ◯Hγₒ]".
          { done. }
          (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
          iMod ("Hcl'" with "[$Hbackup₁ $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
          { iFrame "%". }
          iMod ("Hcl" with "[$Hγ $□Hbackup $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup₁' $●Hγ_val]") as "_".
          { iFrame "%". auto. }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          rewrite /strip.
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          (* Consider the case where the next CAS succeeds or fails *)
          iInv readN as "(%ver₂ & %log₂ & %actual₂ & %cache₂ & %marked_backup₂ & %backup₂ & %backup₂' & %index₂ & %validated₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlogtokens & >%Hlogged₂ & >●Hγₕ & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hval₂ & >%Hvallogged₂)" "Hcl".
          iInv cached_wfN as "(%ver'' & %log₂' & %actual₂' & %marked_backup₂' & %backup₂'' & %requests₂ & %vers₂ & %index₂' & %order₂ & %idx₂ & >●Hγᵥ' & >Hbackup₂' & >Hγ' & >%Hcons₂' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₂ & >%Hvers₂ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₂ & >%Hinj₂ & >%Hidx₂ & >%Hmono₂ & >%Hubord₂)" "Hcl'".
          iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
          iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₂".
          iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
          iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₂].
          iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₂]".
          iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
          iCombine "Hbackup Hbackup₂'" gives %[_ <-].
          (* Note: Hpost was already destructed in the outer case, so we reuse ver' and ◯Hγᵢ' *)
          destruct Hvalidated₂ as [-> | (-> & Heven₂%Nat.even_spec & -> & ->)].
          * (* Old backup was validated, but current backup is not *)
            wp_cmpxchg_fail.
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". auto. }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
          * (* Should always fail, ow ABA*)
            (* Both the current and expected backup are validated *)
            iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree₂".
            (* iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₂']. *)
            (* Consider whether the current and expected backup pointers are equal *)
            destruct (decide (backup₂' = backup)) as [-> | Hneq₂].
            { iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ₁") as "%Hagreeₒ₁₂".
              iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ₂".
              simplify_eq.
              eapply Hubord₂ in Hagreeₒ₁₂. lia. }
            wp_cmpxchg_fail.
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". rewrite -Nat.even_spec. iPureIntro. right. auto. }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
      - (* Old backup was not validated, but current backup is *)
        wp_cmpxchg_fail.
        iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ #◯Hγₒcopy]".
        iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers #◯Hγ_verscopy]".
        destruct (decide (backup₁' ∈ validated)) as [Hmem | Hnmem]; first last.
        { rewrite bool_decide_eq_false_2 // in Hval. }
        iMod (validated_auth_frag_alloc with "●Hγ_val") as "[●Hγ_val ◯Hγ_val]".
        { done. }
        destruct (decide (backup₁' = backup)) as [-> | Hne'].
        + (* If the current backup is equal to the one that we have read, then it has been validated *)
            (* We cannot linearize now *)
          iMod ("Hcl'" with "[$Hbackup₁' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
          { iFrame "%". }
          iMod ("Hcl" with "[$Hγ $□Hbackup $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup₁ $●Hγ_val]") as "_".
          { iFrame "%". rewrite -Nat.even_spec. iPureIntro. right. auto. }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          rewrite /strip.
          wp_pure credit:"Hcredit".
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          (* Consider the case where the next CAS succeeds or fails *)
          iInv readN as "(%ver₂ & %log₂ & %actual₂ & %cache₂ & %marked_backup₂ & %backup₂ & %backup₂' & %index₂ & %validated₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlogtokens & >%Hlogged₂ & >●Hγₕ & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hval₂ & >%Hvallogged₂)" "Hcl".
          iInv cached_wfN as "(%ver'' & %log₂' & %actual₂' & %marked_backup₂' & %backup₂'' & %requests₂ & %vers₂ & %index₂' & %order₂ & %idx₂ & >●Hγᵥ' & >Hbackup₂' & >Hγ' & >%Hcons₂' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₂ & >%Hvers₂ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₂ & >%Hinj₂ & >%Hidx₂ & >%Hmono₂ & >%Hubord₂)" "Hcl'".
          iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
          iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₂".
          iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
          iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₂].
          iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₂]".
          iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
          iCombine "Hbackup Hbackup₂'" gives %[_ <-].
          iCombine "●Hγₕ ●Hγₕ'" as "●Hγₕ".
          (* Note: Hpost was already destructed in the outer case, so we reuse ver' and ◯Hγᵢ' *)
          destruct Hvalidated₂ as [-> | (-> & Heven₂%Nat.even_spec & -> & ->)].
          * (* Old backup was validated, but current backup is not *)
            destruct (decide (backup₂ ∈ validated₂)) as [Hmem₂ | Hnmem₂].
            { rewrite bool_decide_eq_true_2 // in Hval₂. }
            wp_cmpxchg_fail.
            rewrite /registry_inv /registered.
            iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
            iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
            { done. }
            simpl.
            iPoseProof (validated_auth_frag_agree with "●Hγ_val ◯Hγ_val") as "%Hmem'".
            iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
            { intros <-. set_solver. }
            iPoseProof ("Hreginv" with "[$]") as "Hreginv".
            (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
            iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']".
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". auto. }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
          * (* Both the current and expected backup are validated *)
            iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree".
            (* iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₁']. *)
            (* Consider whether the current and expected backup pointers are equal *)
            destruct (decide (backup₂' = backup)) as [-> | Hneq].
            -- (* The CAS will succeed, swapping in the new backup  *)
              rewrite -lookup_fmap lookup_fmap_Some in Hcons₂'.
              destruct Hcons₂' as ([? ?] & <- & Hlogged₂').
              rewrite Hlogged₂' in Hlogagree.
              iCombine "Hbackup Hbackup₂'" as "Hbackup".
              wp_cmpxchg_suc.
              simplify_eq. simpl in *.
              iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
              iCombine "Hγ Hγ'" as "Hγ".
              rewrite Qp.quarter_quarter.
              iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy']".
              iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy']".
              iMod (execute_lp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ expected _ _ backup backup copy with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "(%Hfresh & HΦ & #◯Hγ_vers & [%γₚ' #◯Hγₕ₁] & #Hldes' & #◯Hγₒ)"; try done.
              { rewrite Heven₂ //. }
              { destruct (decide (1 < size log₂)).
                - rewrite bool_decide_eq_true_2 //.
                  rewrite bool_decide_eq_true_2 // in Hvers₂.
                  destruct Hvers₂ as (? & ? & ? & ? & ?).
                  eexists. eauto.
                - rewrite bool_decide_eq_false_2 //.
                  rewrite bool_decide_eq_false_2 // in Hvers₂. }
              iApply fupd_mask_intro.
              { set_solver. }
              iIntros ">_ !>".
              wp_pures.
              wp_apply (wp_try_validate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ index₂ order₂ with "[$] [$] [$] [$] [$] [$] [$] [$] [$]").
              { done. }
              { done. }
              { lia. }
              { done. }
              { done. }
              { eapply Forall_impl; eauto. simpl. intros l' Hl'. set_solver. }
              { done. }
              { rewrite -not_elem_of_dom Hdomord₂ not_elem_of_dom //. }
              iIntros "Hldes".
              wp_pures.
              iApply ("HΦ" with "[$]").
            -- wp_cmpxchg_fail.
              rewrite /registry_inv /registered.
              iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
              iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
              { done. }
              simpl.
              iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
              { done. }
              iPoseProof ("Hreginv" with "[$]") as "Hreginv".
              (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
              iDestruct "●Hγₕ" as "[●Hγₕ ●Hγₕ']".
              iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
              { iFrame "%". }
              iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
              { iFrame "%". iPureIntro. rewrite -Nat.even_spec. auto. } 
              iApply fupd_mask_intro.
              { set_solver. }
              iIntros ">_ !>".
              rewrite /strip.
              by wp_pures.
        + iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree". 
          rewrite /registry_inv /registered.
          iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
          iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
          { done. }
          simpl.
          iMod (already_linearized with "[$] [$] [$] [$] [$] [$] [$]") as "[HΦ Hreq]".
          { done. }
          iPoseProof ("Hreginv" with "[$]") as "Hreginv".
          assert (is_Some (order₁ !! backup)) as [ts Hts].
          { rewrite -elem_of_dom Hdomord elem_of_dom //. }
          apply Hubord₁ in Hts as Hts'.
          assert (ts ≠ idx₁) as Hdifftime.
          { intros ->. assert (backup = backup₁'); last done.
            by eapply Hinj₁. }
          assert (ts < idx₁) as Hlesstime by lia.
          iMod (vers_frag_alloc_singleton _ backup₁' idx₁ with "●Hγₒ") as "[●Hγₒ ◯Hγₒ₁]".
          { done. }
          iMod (vers_frag_alloc_singleton _ backup ts with "●Hγₒ") as "[●Hγₒ ◯Hγₒ]".
          { done. }
          (* replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done. *)
          iMod ("Hcl'" with "[$Hbackup₁ $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
          { iFrame "%". }
          iMod ("Hcl" with "[$Hγ $□Hbackup $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup₁' $●Hγ_val]") as "_".
          { iFrame "%". rewrite -Nat.even_spec. iPureIntro. auto. }
          iApply fupd_mask_intro.
          { set_solver. }
          iIntros ">_ !>".
          rewrite /strip.
          wp_pures.
          wp_bind (CmpXchg _ _ _).
          (* Consider the case where the next CAS succeeds or fails *)
          iInv readN as "(%ver₂ & %log₂ & %actual₂ & %cache₂ & %marked_backup₂ & %backup₂ & %backup₂' & %index₂ & %validated₂ & >Hver & >Hbackup & >Hγ & >%Hunboxed₂ & >#□Hbackup₂ & >%Hindex₂ & >%Hvalidated₂ & >%Hlenactual₂ & >%Hlencache₂ & >%Hloglen₂ & Hlogtokens & >%Hlogged₂ & >●Hγₕ & >%Hlenᵢ₂ & >%Hnodup₂ & >%Hrange₂ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₂ & Hlock & >●Hγ_val & >%Hval₂ & >%Hvallogged₂)" "Hcl".
          iInv cached_wfN as "(%ver'' & %log₂' & %actual₂' & %marked_backup₂' & %backup₂'' & %requests₂ & %vers₂ & %index₂' & %order₂ & %idx₂ & >●Hγᵥ' & >Hbackup₂' & >Hγ' & >%Hcons₂' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₂ & >%Hvers₂ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₂ & >%Hinj₂ & >%Hidx₂ & >%Hmono₂ & >%Hubord₂)" "Hcl'".
          iDestruct (log_auth_auth_agree with "●Hγₕ ●Hγₕ'") as %<-.
          iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₂".
          iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
          iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₂].
          iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₂]".
          iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
          iCombine "Hbackup Hbackup₂'" gives %[_ <-].
          (* Note: Hpost was already destructed in the outer case, so we reuse ver' and ◯Hγᵢ' *)
          destruct Hvalidated₂ as [-> | (-> & Heven₂%Nat.even_spec & -> & ->)].
          * (* Old backup was validated, but current backup is not *)
            wp_cmpxchg_fail.
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". auto. }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
          * (* Should always fail, ow ABA*)
            (* Both the current and expected backup are validated *)
            iPoseProof (log_auth_frag_agree with "●Hγₕ ◯Hγₕ") as "%Hlogagree₂".
            (* iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ'") as %[_ Hle₂']. *)
            (* Consider whether the current and expected backup pointers are equal *)
            destruct (decide (backup₂' = backup)) as [-> | Hneq₂].
            { iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ₁") as "%Hagreeₒ₁₂".
              iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ₂".
              simplify_eq.
              eapply Hubord₂ in Hagreeₒ₁₂. lia. }
            wp_cmpxchg_fail.
            iMod ("Hcl'" with "[$Hbackup₂' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
            { iFrame "%". }
            iMod ("Hcl" with "[$Hγ $□Hbackup₂ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
            { iFrame "%". rewrite -Nat.even_spec. iPureIntro. right. auto. }
            iApply fupd_mask_intro.
            { set_solver. }
            iIntros ">_ !>".
            rewrite /strip.
            by wp_pures.
  Qed.
End cached_wf.

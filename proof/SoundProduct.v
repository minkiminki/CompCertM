Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.

Require Import ModSem.
Require Import Skeleton.
Require Import System.
Require Import Sound Preservation.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ChoiceFacts.

Set Implicit Arguments.
Section SOUNDPRODUCT.

  Variable I: Type.
  Variable SU: I -> Sound.class.

  (* Local Obligation Tactic := idtac. *)

  Global Program Instance sound_class_product: Sound.class :=
    { Sound.t := forall i, (SU i).(@Sound.t);
      Sound.mle su0 m0 m1 := forall i, (SU i).(@Sound.mle) (su0 i) m0 m1;
      Sound.lepriv su0 su1 := forall i, (SU i).(@Sound.lepriv) (su0 i) (su1 i);
      Sound.hle su0 su1 := forall i, (SU i).(@Sound.hle) (su0 i) (su1 i);
      Sound.wf su0 := forall i, (SU i).(@Sound.wf) (su0 i);
      Sound.val su0 v := forall i, (SU i).(@Sound.val) (su0 i) v;
      Sound.mem su0 m := forall i, (SU i).(@Sound.mem) (su0 i) m;
      Sound.skenv su0 m ske := forall i, (SU i).(@Sound.skenv) (su0 i) m ske;
    }
  .
  Next Obligation.
    econs; eauto; ii; ss; des.
    - esplits; eauto; refl.
    - esplits; eauto; etrans; eauto.
  Qed.
  Next Obligation.
    econs; eauto; ii; ss; des.
    - esplits; eauto; refl.
    - esplits; eauto; etrans; eauto.
  Qed.
  Next Obligation.
    econs; eauto; ii; ss; des.
    - esplits; eauto; refl.
    - esplits; eauto; etrans; eauto.
  Qed.
  (* Next Obligation. *)
  (*   ii; ss. des. *)
  (*   (* destruct su0, su1; ss. *) *)
  (*   esplits; ss; eauto. *)
  (*   - eapply Sound.hle_le; et. *)
  (*   - eapply Sound.hle_le; et. *)
  (* Qed. *)
  Next Obligation.
    ii; ss. esplits; ss; eauto; eapply Sound.hle_lepriv; et.
  Qed.
  Next Obligation.
    ii; ss. esplits; ss; eauto; eapply Sound.hle_mle; et.
  Qed.
  Next Obligation.
    ii; ss. des. esplits; ss; eauto;  eapply Sound.hle_val; et.
  Qed.
  Next Obligation.
    assert (EXISTS:
              forall i,
              exists su_init_i,
                (<<SUARGS: (SU i).(@Sound.args) su_init_i (Args.mk (Genv.symbol_address (Sk.load_skenv sk_link) (prog_main sk_link) Ptrofs.zero) [] m_init)>>) /\
                (<<SUSKE: (SU i).(@Sound.skenv) su_init_i m_init (Sk.load_skenv sk_link)>>)).
    { i. exploit (@Sound.init_spec (SU i)); eauto. }
    eapply (non_dep_dep_functional_choice choice) in EXISTS. des. exists f.
    ss. esplits.
    - ii. specialize (EXISTS i). des. eauto.
    - econs.
    - ii. specialize (EXISTS i). des. eauto.
    - ii. specialize (EXISTS i). des. eauto.
    - ii. specialize (EXISTS i). des. eauto.
  Qed.
  Next Obligation.
    ss. ii. esplits; eauto; eapply Sound.skenv_lepriv; eauto.
  Qed.
  Next Obligation.
    ss. ii. esplits; eauto; eapply Sound.skenv_mle; eauto.
  Qed.
  Next Obligation.
    ss. ii. esplits; eauto; eapply Sound.skenv_project; eauto.
  Qed.
  Next Obligation.
    ss. rr. esplits; ii; des.
    - erewrite <- ! (Sound.system_skenv) in *; eauto.
    - specialize (H i). erewrite <- (Sound.system_skenv) in H; eauto.
  Qed.
  Next Obligation.
    assert (EXISTS:
              forall i,
              exists su1_i,
                <<LE: (SU i).(@Sound.hle) (su0 i) su1_i>> /\ <<RETV: su1_i.(Sound.retv) (Retv.mk v_ret m_ret)>> /\ <<MLE: (su0 i).(Sound.mle) args0.(Args.m) m_ret>>).
    { i. exploit (@Sound.system_axiom (SU i)); et.
      unfold Sound.args. des_ifs; ss. des. splits; auto.
      eapply Forall_impl; try apply VALS. ss. }
    eapply (non_dep_dep_functional_choice choice) in EXISTS. des. exists f.
    ss. esplits.
    - ii. specialize (EXISTS i). des. eauto.
    - ii. specialize (EXISTS i). des. eauto.
    - ii. specialize (EXISTS i). des. eauto.
    - ii. specialize (EXISTS i). des. eauto.
    - ii. specialize (EXISTS i). des. eauto.
  Qed.

  Lemma sound_args_iff
        su args:
      (forall i, <<ARGS: @Sound.args (SU i) (su i) args>>) <-> (@Sound.args sound_class_product su args)
  .
  Proof.
    unfold Sound.args. unfold Sound.vals. ss.
    des_ifs.
    - split; ii; des; esplits; eauto; i.
      + spc H. des. auto.
      + rewrite Forall_forall. i. spc H. des.
        rewrite Forall_forall in *. auto.
      + spc H. des. auto.
      + spc H. des. auto.
      + rewrite Forall_forall. i. rewrite Forall_forall in *. auto.
    - split; ii; des; esplits; eauto; ii; try (spc H; des; eauto).
      eapply REGSET.
  Qed.

  Lemma sound_skenv_iff
        su m ske
    :
      (forall i, <<SKENV: @Sound.skenv (SU i) (su i) m ske>>) <-> (@Sound.skenv sound_class_product su m ske)
  .
  Proof.
    split; ii; des; esplits; ss; des; eauto. eapply H.
  Qed.

  Lemma sound_retv_iff
        su retv:
      (forall i, <<RETV: @Sound.retv (SU i) (su i) retv>>) <-> (@Sound.retv sound_class_product su retv)
  .
  Proof.
    unfold Sound.retv. ss.
    des_ifs.
    - split; ii; des; esplits; eauto; ii; spc H; des; auto.
    - split; ii; des; esplits; eauto; ii; try (spc H); des; ss; eauto. eapply REGSET.
  Qed.

  Theorem preservation_product
          ms sound_state
          (PRSV: forall i, @local_preservation (SU i) ms (sound_state i))
    :
      <<PRSV: @local_preservation sound_class_product ms
                                  (fun su m st => forall i, (sound_state i) (su i) m st)>>.
  Proof.
    econs; eauto.
    - ii. spc PRSV. inv PRSV. ss.
      eapply INIT0; eauto. eapply sound_args_iff in SUARG; eauto.
    - ii. spc PRSV. inv PRSV. ss.
      eapply STEP0; eauto.
    - ii. split.
      + ii. spc PRSV. inv PRSV. exploit CALL; eauto. i. des. eauto.
      + assert (EXISTS: forall i, exists su_gr_i,
                     (<<ARGS: Sound.args su_gr_i args>>) /\
                     (<<LE: Sound.lepriv (su0 i) su_gr_i>>) /\
                     (<<K: forall su_ret retv st1
                                  (LE: Sound.hle su_gr_i su_ret)
                                  (RETV: su_ret.(Sound.retv) retv)
                                  (MLE: Sound.mle su_gr_i args.(Args.get_m) retv.(Retv.get_m))
                                  (AFTER: ms.(ModSem.after_external) st0 retv st1)
                       ,
                         (<<SUST: sound_state _ (su0 i) m_arg st1>>)>>)).
        { ii. spc PRSV. inv PRSV.
          exploit CALL; eauto. i. des. esplits; eauto. }
        eapply (non_dep_dep_functional_choice choice) in EXISTS. des. exists f.
        ss. esplits.
        * rewrite <- sound_args_iff. ii. spc EXISTS. des. auto.
        * ii. spc EXISTS. des. auto.
        * ii. spc EXISTS. des. eapply K; eauto.
          rewrite <- sound_retv_iff in RETV. eapply RETV.
    - i.
      assert (EXISTS: forall i, exists su_ret_i,
                   (<<LE: Sound.hle (su0 i) su_ret_i>>) /\
                   (<<RETV: su_ret_i.(Sound.retv) retv>>) /\ (<<MLE: (su0 i).(Sound.mle) m_arg retv.(Retv.get_m)>>)).
      { i. spc PRSV. inv PRSV. eapply RET; eauto. }
      eapply (non_dep_dep_functional_choice choice) in EXISTS. des. exists f.
      ss. esplits.
      + i. spc EXISTS. des. auto.
      + rewrite <- sound_retv_iff. i. spc EXISTS. des. auto.
      + i. spc EXISTS. des. auto.
  Qed.

End SOUNDPRODUCT.

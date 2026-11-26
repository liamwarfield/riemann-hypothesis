module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqWeightsOfTraceEPowerHighestWeightValueEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TieSame

theorem bsH_val_congr {e e' : Formalism.HC.Frame} (he : e = e') (h t : e.A) (h' t' : e'.A)
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (Arith.bsH h t).val = (Arith.bsH h' t').val := by
  subst he
  have h1 := Formalism.HC.Frame.A.val_injective _ hh
  have h2 := Formalism.HC.Frame.A.val_injective _ ht
  rw [h1, h2]

theorem mem_iff_val_mem {e : Formalism.HC.Frame} (T : Finset e.A) (t : e.A) :
    t ∈ T ↔ t.val ∈ T.image Formalism.HC.Frame.A.val := by
  constructor
  · intro h; exact Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    rwa [← Formalism.HC.Frame.A.val_injective _ hst]

theorem kapISet_congr {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R) (hs : L.sc = L'.sc) (hS : L.Sc = L'.Sc)
    (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = G.kapISet L' K p n' TT a b := by
  have hk : D.R.k = D'.R.k := by rw [hR]
  have hc : G.cG L = G.cG L' := by unfold G.cG; rw [hS]
  have hD : G.DIf K L p n' = G.DIf K L' p n' := by unfold G.DIf; rw [hs, hk]
  have h6 : G.c6f K L p n' = G.c6f K L' p n' := by unfold G.c6f; rw [hD, hs, hk, hc]
  have ht : G.tIf K L p n' TT a b = G.tIf K L' p n' TT a b := by unfold G.tIf; rw [h6, hs, hk, hc]
  unfold G.kapISet
  rw [hc, hD, ht, hk]

theorem nonempty_place (D : D7) : Nonempty D.what₂.places.Pl := by
  haveI := D.nfLL
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem off_lift {C : FC} {cD ch : ℝ} (p : Pt C) (hv : Val C cD ch p.L) (j : ℕ) (hj : j ∈ SizeData₂.lifts p.D) (t : G.HH p.D) :
    p.ta.Gx.off j (false, t) =
      (if t ∈ p.D.host.TT then ((⌊p.L.sc.b' / p.L.sc.x⌋ : ℤ) : ℝ) else ((⌈p.L.sc.w'' p.D.R.n⌉ : ℤ) : ℝ)) +
        ((j - 1 : ℕ) : ℝ) * (h0v p.L.sc ch : ℝ) + (h0v p.L.sc ch : ℝ) / 2 := by
  obtain ⟨w⟩ := nonempty_place p.D
  have hP := factPlaces p.D.R.toFrame
  have hmem : p.D.R.tau1 t ∈ p.D.R.Psi := (hP.1 _).2 (Or.inl ⟨t, rfl⟩)
  set τ := p.D.eTau.symm ⟨_, hmem⟩ with hτ
  have hτe : (p.D.eTau τ : p.D.R.GG) = p.D.R.tau1 t := by rw [hτ, Equiv.apply_symm_apply]
  have hf := (p.ta.fills w).1 j hj τ (false, t) (by rw [hτe]; rfl)
  have hjm : j - 1 < p.D.R.m := by
    have := Finset.mem_Icc.1 hj
    omega
  obtain ⟨-, -, ⟨b1, hb, htop, -, hthin⟩, -⟩ := hv.hc
  obtain ⟨hb1, hb2⟩ := hb τ ⟨j - 1, hjm⟩
  unfold wj at hf
  rw [dite_eq_left hjm, hb2, hb1] at hf
  unfold G.fill at hf
  by_cases ht : t ∈ p.D.host.TT
  · have h1 := htop τ ⟨t, ht⟩ hτe
    rw [if_pos ⟨rfl, ht⟩, h1] at hf
    rw [if_pos ht]
    unfold G.bL at hf
    rw [dite_eq_left ht] at hf
    push_cast at hf ⊢
    linarith
  · have h1 := hthin τ (by
      show p.D.host.IsThin (p.D.eTau τ : p.D.R.GG)
      rw [hτe]
      refine ⟨hmem, ?_, ?_⟩
      · intro h
        obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
        have : s = t := p.D.R.iota_bijective.1 (congrArg Prod.snd hst)
        exact ht (this ▸ hs)
      · intro h
        obtain ⟨s, -, hst⟩ := Finset.mem_image.1 h
        exact hP.2 _ _ hst.symm)
    rw [if_neg (fun h => ht h.2), h1] at hf
    rw [if_neg ht]
    push_cast at hf ⊢
    linarith

theorem same_of_from : ∀ (C : FC) (cD ch : ℝ) (p p' : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 u0' : ℕ), p.L.sc = p'.L.sc → Val C cD ch p.L → Val C cD ch p'.L → p.From H a b c u0 → p'.From H a b c u0' → CanonInst p.ta.Gx → CanonInst p'.ta.Gx → p.Same p' := by
  intro C cD ch p p' R H a b M c u0 u0' hs hv hv' hF hF' hC hC'
  have hQS := hF.QS_eq.trans hF'.QS_eq.symm
  have hart := hF.art_eq.trans hF'.art_eq.symm
  have hrd := hF.rd_eq.trans hF'.rd_eq.symm
  obtain ⟨hR, hTT, hT2, hq, hd, hg, hp1, hp2, -, -, hh, hw, -⟩ := hF
  obtain ⟨hR', hTT', hT2', hq', hd', hg', hp1', hp2', -, -, hh', hw', -⟩ := hF'
  have hRR : p.D.R = p'.D.R := hR.trans hR'.symm
  have hT : p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val := hTT.trans hTT'.symm
  have hSc : p.L.Sc = p'.L.Sc := by rw [p.L.Sc_eq, p'.L.Sc_eq, hv.Del_eq, hv'.Del_eq, hs, hRR]
  have hmem : ∀ (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → (t ∈ p.D.host.TT ↔ t' ∈ p'.D.host.TT) := by
    intro t t' htt
    rw [mem_iff_val_mem p.D.host.TT t, mem_iff_val_mem p'.D.host.TT t', hT, htt]
  have hn : p.D.R.n = p'.D.R.n := by rw [hRR]
  refine ⟨hRR, hT, hT2.trans hT2'.symm, hq.trans hq'.symm, hd.trans hd'.symm, hg.trans hg'.symm, hp1.trans hp1'.symm,
    hp2.trans hp2'.symm, ?_, hSc, fun l => (hh l).trans (hh' l).symm, ?_, ?_, ?_, ?_, ?_, hQS, hart, hrd⟩
  · rw [hv.eta_eq, hv'.eta_eq, hs, hRR]
  · intro h t h' t' e1 e2
    rw [hC.1, hC'.1]
    exact bsH_val_congr (by rw [hRR]) h t h' t' e1 e2
  · intro j t t' htt
    have hm := hmem t t' htt
    have hl : SizeData₂.lifts p.D = SizeData₂.lifts p'.D := by unfold SizeData₂.lifts; rw [hRR]
    by_cases hj : j ∈ SizeData₂.lifts p.D
    · rw [off_lift p hv j hj t, off_lift p' hv' j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
    · rw [hC.2 j hj t, hC'.2 j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
  · funext l n' TT a' b'
    rw [p.xa.ex.kapI_def l n' TT a' b', p'.xa.ex.kapI_def l n' TT a' b', kapISet_congr p.L p'.L hRR hs hSc]
  · funext l
    rw [p.xa.ex.ep_def l, p'.xa.ex.ep_def l, hs, hRR]
  · intro t t' htt
    have hlt : (t : p.D.R.A).val < R.ord := by
      have := Formalism.HC.Frame.A.val_lt (t : p.D.R.A)
      rwa [show R.ord = p.D.R.ord by rw [hR]]
    have hv0 : (R.ofNat (t : p.D.R.A).val).val = (t : p.D.R.A).val :=
      R.toFrame.val_ofNat_of_lt hlt
    obtain ⟨e1, e2⟩ := hw t _ hv0.symm
    obtain ⟨e3, e4⟩ := hw' t' _ (htt.symm.trans hv0.symm)
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

end GlobalTheory.EX.TieSame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open TensorProduct Formalism.UG Formalism.UG.P

noncomputable section

namespace GlobalTheory.SuppIdele

section Base

variable {F : Type} [Field F] [NumberField F]

theorem exists_int_mul (a : 𝓞 F) (ha : a ≠ 0) (z : FiniteAdeleRing (𝓞 F) F)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (z w) ≤ w.intValuation a) :
    ∃ x ∈ intAd F, z = (a : F) • x := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  refine ⟨(a : F)⁻¹ • z, fun w => ?_, by rw [smul_smul, mul_inv_cancel₀ ha', one_smul]⟩
  rw [afsplit_smul_apply, HeightOneSpectrum.mem_adicCompletionIntegers, Algebra.smul_def, map_mul, map_inv₀, map_inv₀]
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)
  rw [h1, inv_mul_le_iff₀ (zero_lt_iff.2 (w.intValuation_ne_zero a ha)), mul_one]
  exact hz w

theorem val_algebraMap (w : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)

theorem intVal_eq_one (w : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F} (h : a ∉ w.asIdeal) : w.intValuation a = 1 :=
  le_antisymm (w.intValuation_le_one a) (not_lt.1 fun h' => h ((w.intValuation_lt_one_iff_mem a).1 h'))

theorem exists_notMem {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : ∃ c ∈ w.asIdeal, c ∉ v.asIdeal := by
  by_contra H
  push Not at H
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top H))

theorem eps_dvd (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ x ∈ intAd F, afsplitI v 1 = (c : F) • x := by
  refine exists_int_mul c (by rintro rfl; exact hc (zero_mem _)) _ fun w => ?_
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, map_one, intVal_eq_one w hc]
  · rw [afsplitI_ne v w h, map_zero]
    exact zero_le

theorem one_sub_eps (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ v.asIdeal ^ 2, ∃ r ∈ v.asIdeal ^ 2, ∃ x ∈ intAd F,
      1 - afsplitI v 1 = (a : F) • x + (r : F) • (1 - afsplitI v 1) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero 2 v.ne_bot)
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {a}) (by simpa using ha0) v.asIdeal
  have hc : IsCoprime (v.asIdeal ^ 2) Q := (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left
  obtain ⟨r, hr, q, hq, hrq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨x, hx, hxe⟩ := exists_int_mul a ha0 ((q : F) • (1 - afsplitI v 1)) fun w => by
    rw [afsplit_smul_apply, afsplit_sub_apply, afsplit_one_apply]
    by_cases h : w = v
    · subst h
      rw [afsplitI_self, sub_self, smul_zero, map_zero]
      exact zero_le
    · rw [afsplitI_ne v w h, sub_zero, Algebra.smul_def, mul_one, val_algebraMap]
      obtain ⟨t, ht, htw⟩ := exists_notMem (Ne.symm h)
      have hm := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht
        (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})))) hq
      rw [← hI, Ideal.mem_span_singleton'] at hm
      obtain ⟨s, hs⟩ := hm
      have := congrArg w.intValuation hs
      rw [map_mul, map_mul, map_pow, intVal_eq_one w htw, one_pow, one_mul] at this
      rw [← this]
      exact mul_le_of_le_one_left' (w.intValuation_le_one s)
  refine ⟨a, ha, r, hr, x, hx, ?_⟩
  rw [← hxe, ← add_smul]
  have : (q : F) + (r : F) = 1 := by
    rw [add_comm]; exact_mod_cast congrArg (fun t : 𝓞 F => (t : F)) hrq
  rw [this, one_smul]

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (E) in
def ofInt (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) : RInt F E :=
  ⟨(1 : E) ⊗ₜ[F] x, Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)⟩

theorem coe_toRInt (b : 𝓞 E) : (toRInt F E b : AfE F E) = (b : E) ⊗ₜ[F] 1 := rfl

theorem tmul_smul_eq (a : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) :
    (1 : E) ⊗ₜ[F] ((a : F) • x) = ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx : RInt F E) : AfE F E) := by
  rw [Subring.coe_mul, coe_toRInt, ofInt, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rfl

theorem eps_int (v : HeightOneSpectrum (𝓞 F)) : afsplitI v 1 ∈ intAd F := afsplitI_mem_intAd v 1 (one_mem _)

theorem exists_crt (I Q : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hQ : Q ≠ ⊥) (h : IsCoprime I Q) (b : 𝓞 E) :
    ∃ b' : 𝓞 E, b' ≠ 0 ∧ b' - b ∈ I ∧ b' - 1 ∈ Q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 h
  have h1 : b * q + p - b ∈ I := by
    have : b * q + p - b = (1 - b) * p := by linear_combination b * hpq
    rw [this]; exact I.mul_mem_left _ hp
  have h2 : b * q + p - 1 ∈ Q := by
    have : b * q + p - 1 = (b - 1) * q := by linear_combination hpq
    rw [this]; exact Q.mul_mem_left _ hq
  by_cases h0 : b * q + p = 0
  · obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mul_ne_zero hI hQ)
    rw [h0] at h1 h2
    refine ⟨t, ht0, ?_, ?_⟩
    · have h3 : t ∈ I := Ideal.mul_le_inf ht |>.1
      rw [show t - b = t + (0 - b) by ring]
      exact I.add_mem h3 h1
    · have h3 : t ∈ Q := Ideal.mul_le_inf ht |>.2
      rw [show t - 1 = t + (0 - 1) by ring]
      exact Q.add_mem h3 h2
  · exact ⟨_, h0, h1, h2⟩

theorem exists_supported_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ (y : (AfE F E)ˣ) (y₀ : RInt F E), (y₀ : AfE F E) = (y : AfE F E) ∧ y ∈ suppAt E v ∧
      y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  haveI := P.isMaximal
  have hv0 : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hv0 P.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hv0 (by rw [hI, Ideal.mul_bot])
  obtain ⟨b', hb0, hb1, hb2⟩ := exists_crt (P.asIdeal ^ 2) Q (pow_ne_zero 2 P.ne_bot) hQ0
    (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left b
  have hb0' : (b' : E) ≠ 0 := by simpa using hb0
  set e : RInt F E := ofInt E (afsplitI v 1) (eps_int v) with he
  have hee : (e : AfE F E) = afsplitEps E v := rfl
  set ι := inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hid := afsplit_eps_idem (E := E) v
  have hinv : ι b' * ι (b' : E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hb0', map_one]
  have hmul : (1 + (ι b' - 1) * afsplitEps E v) * (1 + (ι (b' : E)⁻¹ - 1) * afsplitEps E v) = 1 := by
    linear_combination (ι b' - 1) * (ι (b' : E)⁻¹ - 1) * hid + afsplitEps E v * hinv
  refine ⟨⟨_, _, hmul, by rw [mul_comm, hmul]⟩, 1 + (toRInt F E b' - 1) * e, rfl, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w hw
    apply Units.ext
    show prV (E := E) w (1 + (ι b' - 1) * afsplitEps E v) = 1
    rw [map_add (f := _), map_mul, afsplit_prV_eps_ne v w hw, mul_zero, add_zero, map_one]
  · obtain ⟨a, ha, r, hr, x, hx, hxe⟩ := one_sub_eps v
    have hle : ∀ c ∈ v.asIdeal ^ 2, toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      intro c hc
      apply Ideal.mem_map_of_mem
      have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hc
      rw [Ideal.map_pow] at h1
      refine Ideal.pow_right_mono ?_ 2 h1
      rw [← hPv]; exact Ideal.map_comap_le
    have hx' : 1 - afsplitI v 1 ∈ intAd F := sub_mem (one_mem _) (eps_int v)
    have h1 : 1 - e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx +
        toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ofInt E _ hx' := by
      apply Subtype.ext
      rw [Subring.coe_add, ← tmul_smul_eq, ← tmul_smul_eq, ← TensorProduct.tmul_add, ← hxe, TensorProduct.tmul_sub]
      rfl
    have h2 : 1 - e ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      rw [h1]
      exact add_mem (Ideal.mul_mem_right _ _ (hle a ha)) (Ideal.mul_mem_right _ _ (hle r hr))
    have h3 : 1 + (toRInt F E b' - 1) * e - toRInt F E b = toRInt F E (b' - b) + (1 - toRInt F E b') * (1 - e) := by
      rw [map_sub]; ring
    rw [h3]
    exact add_mem (Ideal.mem_map_of_mem _ hb1) (Ideal.mul_mem_left _ _ h2)
  · intro P' hP'
    rw [add_sub_cancel_left]
    by_cases hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P'.asIdeal
    · rw [hI] at hle
      have hQP : Q ≤ P'.asIdeal := by
        rcases P'.isPrime.mul_le.1 hle with h | h
        · haveI := P'.isPrime
          exact absurd (HeightOneSpectrum.ext (P.isMaximal.eq_of_le P'.isPrime.ne_top
            (Ideal.IsPrime.le_of_pow_le h))).symm hP'
        · exact h
      have := Ideal.mem_map_of_mem (toRInt F E) (hQP hb2)
      rw [map_sub, map_one] at this
      exact Ideal.mul_mem_right _ _ this
    · have hc : ∃ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ∈ P'.asIdeal ∧ c ∉ v.asIdeal := by
        by_contra H
        push Not at H
        haveI := P'.isMaximal
        have hm : (P'.asIdeal.under (𝓞 F)).IsMaximal := inferInstance
        apply hle
        rw [← hm.eq_of_le v.isPrime.ne_top (fun c hc => H c hc)]
        exact Ideal.map_comap_le
      obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨x, hx, hxe⟩ := eps_dvd v c hc2
      have h1 : e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) * ofInt E x hx := by
        apply Subtype.ext
        rw [← tmul_smul_eq, ← hxe]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc1))

end GlobalTheory.SuppIdele
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadCharacterBound
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField


open Classical in
def BadOfBase (B : Arith.Base) (h : ℕ → B.H) (Cb : ℝ) : Prop :=
  let PR := (Finset.range ⌈B.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ))
  ∑ p ∈ PR, Real.log p / p *
      ((B.TT.filter (fun t => ¬ Arith.Loc.Good B (h p) (Arith.bsH (Arith.Loc.stepP B (h p) p) t))).card : ℝ) ≤
    4 * (Cb * B.sc.x ^ (-2 : ℝ)) * B.sc.delta1 * B.R.n * ∑ p ∈ PR, Real.log p / p

theorem badOK_iff_badOfBase {R : Ranks} (s : Scale) (Cb : ℝ) (H : Host R) :
    BadOK s Cb H ↔ BadOfBase (baseOf s 0 0 H) (hPH H) Cb := Iff.rfl

theorem chBad_iff_badOfBase {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (hX : ∀ h t, X.bs h t = Arith.bsH h t) (Cb : ℝ) :
    ChBad_at X Cb ↔ BadOfBase (baseOf L.sc 0 0 D.host) (G.hP D) Cb := by
  have hb : X.bs = fun h t => Arith.bsH h t := funext fun h => funext fun t => hX h t
  unfold ChBad_at badTops
  obtain ⟨bs, h1, h2, off, h3, h4, h5, kap, ep⟩ := X
  dsimp only at hb
  subst hb
  exact Iff.rfl

theorem badOfBase_of_host {R R' : Ranks} (hR : R' = R) (s : Scale) (H : Host R) (H' : Host R')
    (h : ℕ → R.A) (h' : ℕ → R'.A) (Cb : ℝ)
    (hT : H'.TT.image Formalism.HC.Frame.A.val = H.TT.image Formalism.HC.Frame.A.val) (hq : H'.q = H.q) (hd : H'.d = H.d)
    (hc : H'.cls = H.cls)
    (hh : ∀ l, (h' l).val = (h l).val) (hb : BadOfBase (baseOf s 0 0 H) h Cb) :
    BadOfBase (baseOf s 0 0 H') h' Cb := by
  subst hR
  have hT' : H'.TT = H.TT := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hT
  have hh' : h' = h := funext fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  subst hh'
  unfold baseOf at hb ⊢
  rw [hT', hq, hd, hc]
  exact hb

theorem chBad_of_from : ∀ (C : FC) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ)
    (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ) (Cb : ℝ),
    p.From H a b c u0 → CanonInst p.ta.Gx → BadOK p.L.sc Cb H → ChBad_at p.ta.Gx Cb := by
  intro C p R H a b M c u0 Cb hF hC hB
  have hc := hF.cls_eq
  obtain ⟨hR, hT, -, hq, hd, -, -, -, -, -, hh, -⟩ := hF
  exact (chBad_iff_badOfBase _ hC.1 Cb).2
    (badOfBase_of_host hR p.L.sc H p.D.host (hPH H) (G.hP p.D) Cb hT hq hd hc hh ((badOK_iff_badOfBase _ _ _).1 hB))

end GlobalTheory.EX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeyl
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeyl
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, rowW, rowDeg, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Pi.single_apply]

theorem hw_mem_of_lt : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  intro p hp k _ _ N ν hν hal M M' hM hM' hlt hle
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p := by
    intro h
    refine ⟨(hal h).1, ?_, (hal h).2⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq p hp k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

end GlobalTheory.Alc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeylStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  first | exact @GlobalTheory.Alc.hw_mem_of_lt | exact GlobalTheory.Alc.hw_mem_of_lt | (intros; apply GlobalTheory.Alc.hw_mem_of_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem int_mul_mem_lamOf (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, int_mul_mem_lamOf a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem qIntAll_of_latAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  intro D cc δ B h N N' L L' hA x hx
  have hsd := (h.1 N N' L L' hA).1
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hw := int_smul_mem_La L L' a hx
  rw [ha] at hw
  have hw' : StandardLatticesGL3.w0 D • x ∈ dualLat (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') := by
    rw [hsd]; exact hw
  obtain ⟨m, hm⟩ := hw' x hx
  have him : (TaylorLogMetric.Hf D B.tor x x).im = 0 := by
    have : starRingEnd ℂ (TaylorLogMetric.Hf D B.tor x x) = TaylorLogMetric.Hf D B.tor x x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [TaylorLogMetric.Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
    exact Complex.conj_eq_iff_im.1 this
  have h1 : (StandardLatticesGL3.w0 D).re = 1 / 2 := by simp [StandardLatticesGL3.w0]
  have h2 : (StandardLatticesGL3.w0 D).im = Real.sqrt D.host.d / 2 := by simp [StandardLatticesGL3.w0]
  have h3 : formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = TaylorLogMetric.Hf D B.tor x x := rfl
  refine ⟨m, ?_⟩
  rw [← hm, altE, LinearMap.map_smul₂, h3, smul_eq_mul, Complex.mul_im, h1, h2, him]
  ring

end GlobalTheory.ThetaMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLatticesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  first | exact @GlobalTheory.ThetaMove.qIntAll_of_latAll | exact GlobalTheory.ThetaMove.qIntAll_of_latAll | (intros; apply GlobalTheory.ThetaMove.qIntAll_of_latAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnderEqIffMapLe
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem under_eq_iff_map_le (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro rfl
    exact le_rfl
  · intro h
    apply HeightOneSpectrum.ext
    exact (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top h).symm

theorem under_eq_iff (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ (Q = P ∨ Q = P') := by
  rw [under_eq_iff_map_le, h, Q.isPrime.mul_le]
  refine or_congr ⟨fun h => ?_, fun h => h ▸ le_rfl⟩ ⟨fun h => ?_, fun h => h ▸ le_rfl⟩
  · exact HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
  · exact HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h).symm

theorem not_mul_le_sq (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P') :
    ¬ P.asIdeal * P'.asIdeal ≤ P.asIdeal ^ 2 := by
  intro h
  rw [← Ideal.dvd_iff_le, sq, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at h
  exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h).symm)

theorem val_eq_inv_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)),
    χ.TrivOn F → χ.UnrAt P → χ.UnrAt P' → P ≠ P' →
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal → χ.val P' = (χ.val P)⁻¹ := by
  intro F E _ _ _ _ _ χ v P P' hχ h1 h2 hne hv
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hab : aboveF (L := E) F v = {P, P'} := by
    ext Q
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff v P P' hv Q
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → χ.UnrAt Q →
      ¬ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal ^ 2 →
      χ.locK Q (upF F (Units.mk0 π h0)) = χ.val Q := by
    intro Q hQ hunr hu
    refine χ.val_eq hunr _ ?_
    subst hQ
    show Valued.v ((algebraMap F E π : E) : Q.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.MuConj.valuation_up Q hu, hπ]
  have h := hχ.1 v (Units.mk0 π h0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hne,
    key P ((under_eq_iff v P P' hv _).2 (Or.inl rfl)) h1 (hv ▸ not_mul_le_sq P P' hne),
    key P' ((under_eq_iff v P P' hv _).2 (Or.inr rfl)) h2
      (by rw [hv, mul_comm]; exact not_mul_le_sq P' P hne.symm)] at h
  exact eq_inv_of_mul_eq_one_right h

end GlobalTheory.HeckeSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVDetLat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.CharVal.DetFrame

theorem maxV_detLat (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n))
    (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n)
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) :
    MaxV P (detLat N) (P.valuation E ((LinearEquiv.det f : Eˣ) : E)) := by
  classical
  rw [LinearEquiv.coe_det]
  refine ⟨val_le_of_span ?_, ?_⟩
  · rintro a ⟨A, hA, rfl⟩
    let g : Sp E n →ₗ[E] Sp E n := Matrix.toLin' A
    have hg : ∀ x ∈ stdAt E n P, ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x ∈ stdAt E n P := by
      intro x hx
      rw [← hf]
      obtain ⟨s, hs, hx⟩ := (mem_locP P _ _).1 hx
      refine (mem_locP P _ _).2 ⟨s, hs, ?_⟩
      have h1 := hA _ hx
      have h2 : A.mulVec (s • x) = s • f (((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rw [Matrix.mulVec_smul]
        rfl
      rwa [h2] at h1
    have h := GlobalTheory.Survey.StandardDeterminantUnits.val_det_le_one _ hg
    have h3 : LinearMap.det (f : Sp E n →ₗ[E] Sp E n) *
        LinearMap.det ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) = A.det := by
      rw [LinearMap.det_comp, ← mul_assoc, LinearEquiv.det_mul_det_symm, one_mul]
      exact LinearMap.det_toLin' A
    rw [← h3, map_mul]
    exact mul_le_of_le_one_right' h
  · have h1 : ∀ i : Fin n, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • f (Pi.single i (1 : E)) ∈ N := fun i =>
      (mem_locP P _ _).1 ((hf _).2 (le_locP P _ (by simpa using single_mem_stdLat (E := E) i 1)))
    choose s hs hs' using h1
    set t : 𝓞 E := ∏ i, s i with ht
    have htP : t ∉ P.asIdeal := by
      intro hm
      obtain ⟨i, -, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs i h
    have ht' : ∀ i, t • f (Pi.single i (1 : E)) ∈ N := by
      intro i
      rw [ht, ← Finset.prod_erase_mul _ s (Finset.mem_univ i), mul_smul]
      exact N.smul_mem _ (hs' i)
    let g : Sp E n →ₗ[E] Sp E n := (algebraMap (𝓞 E) E t) • (f : Sp E n →ₗ[E] Sp E n)
    refine ⟨(LinearMap.toMatrix' g).det, Submodule.subset_span ⟨LinearMap.toMatrix' g, ?_, rfl⟩, ?_⟩
    · intro v hv
      have h2 : (LinearMap.toMatrix' g).mulVec v = t • f v := by
        rw [LinearMap.toMatrix'_mulVec]
        simp [g]
      rw [h2]
      clear h2
      rw [stdLat_eq_span] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ht' i
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact N.add_mem hx hy
      | smul r x _ hx =>
        rw [← algebraMap_smul E r x, map_smul, algebraMap_smul, smul_comm]
        exact N.smul_mem r hx
    · rw [LinearMap.det_toMatrix', LinearMap.det_smul, map_mul, map_pow,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 htP, one_pow, one_mul]

end GlobalTheory.CharVal.DetFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

abbrev baseOfParams {D : D7} (L : SizeData₂ D) : Arith.Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

theorem kapISet_eq_loc {D : D7} (L : SizeData₂ D) (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = Arith.Loc.kapISet (baseOfParams L) K p n' TT a b := rfl

theorem sig_eq_loc {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (hk : G.KapIDef X K)
    (hb : ∀ h t, X.bs h t = Arith.bsH h t) (a b : G.HH D → ℤ) (p : ℕ) :
    G.Sig X K a b p =
      Arith.Loc.Sig (baseOfParams L) (Arith.ins (baseOfParams L) K 1) K a b (G.hP D p) p := by
  have hb' : X.bs = Arith.bsH := by funext h t; exact hb h t
  have hk' : X.kapI = (Arith.ins (baseOfParams L) K 1).kapI := by
    funext p n' TT a b
    rw [hk p n' TT a b, kapISet_eq_loc]; rfl
  unfold G.Sig G.goodReps G.reps G.kapv G.kapLoc
  rw [hb', hk']
  rfl

theorem wreq_of_wok : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  intro C cD ch p R H a b M c u0 _ hV hF hC h0 hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, hw, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  have ha : G.aL p.L = a := by
    funext t
    unfold G.aL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).1
    · exact (h0 t (hTT' ▸ h)).1.symm
  have hb : G.bL p.L = b := by
    funext t
    unfold G.bL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).2
    · exact (h0 t (hTT' ▸ h)).2.symm
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
      p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
      (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
       open Classical in
       ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
        (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l then (1 : ℝ) else 0) +
          4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) →
      Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK a b := by
    intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6 hW
    obtain rfl : G.hP p.D = hf := funext e6
    subst e1 e2 e0 e3 e4 e5
    unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands
    simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1]
    exact hW
  rw [ha, hb]
  exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh' hW

end GlobalTheory.EX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternating
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternating
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.DualCount

theorem relIndex_le_of_selfDual (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hanti : ∀ x y, ω x y = -ω y x)
    (h₁ : ∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n)
    (h₂ : ∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n)
    (hfin : Λ₁.relIndex Λ₂ ≠ 0) : Λ₂.relIndex Λ₁ ≤ Λ₁.relIndex Λ₂ := by
  classical
  have hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z := by
    intro x y z
    rw [hanti x (y + z), hadd, hanti x y, hanti x z]; ring
  have hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z := by
    intro x y z
    have := hadd (x - y) y z
    rw [sub_add_cancel] at this
    linarith
  have hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  let φ : H → (Λ₂ →+ UnitAddCircle) := fun x =>
    AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by
      intro a b
      simp only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])
  have hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker := by
    intro x y hy
    rw [AddMonoidHom.mem_ker]
    exact (hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))
  let ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle) := fun x =>
    QuotientAddGroup.lift _ (φ x) (hφ x)
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle := fun x =>
    (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)
  have hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂ := by
    intro a b hab
    rw [h₂]
    intro y hy
    have h := DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)
    have h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle)
        = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle) := h
    have h'' := AddCircle.injective_toCircle (T := 1) one_ne_zero h'
    rw [← hint, hsub, AddCircle.coe_sub, h'', sub_self]
  haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin
  haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
  let f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ := fun q =>
    AddChar.circleEquivComplex (χ q.out)
  have hf : Function.Injective f := by
    intro p q hpq
    have h := hχ _ _ (AddChar.circleEquivComplex.injective hpq)
    rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    exact h
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ)
      = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [hc] at hle
  exact hle

theorem relIndex_eq_of_selfDual : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) →
    (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) →
    Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  intro H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂
  exact le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂)
    (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)

end GlobalTheory.MomT.DualCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternatingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_eq_of_selfDual_alternating : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ) (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) → (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) → Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  first | exact @GlobalTheory.MomT.DualCount.relIndex_eq_of_selfDual | exact GlobalTheory.MomT.DualCount.relIndex_eq_of_selfDual | (intros; apply GlobalTheory.MomT.DualCount.relIndex_eq_of_selfDual <;> assumption)
end
end

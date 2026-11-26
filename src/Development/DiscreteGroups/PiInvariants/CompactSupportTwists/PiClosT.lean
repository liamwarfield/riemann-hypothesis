module

public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm

@[expose] public section

section -- merged from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosU
set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele PositivityTheory.Rg.BcB
open scoped ENNReal

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev lg (g : GA E n) : ℝ := logAbs g.val.det

theorem lg_eq (g : GA E n) : lg g = Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (Matrix.GeneralLinearGroup.det g)) := by
  have h := logAbs_eq_log_ideleNorm (Matrix.GeneralLinearGroup.det g)
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

theorem lg_mul (g h : GA E n) : lg (g * h) = lg g + lg h := by
  rw [lg_eq, lg_eq, lg_eq, map_mul, map_mul,
    Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]

def lgHom : GA E n →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (lg g)
  map_one' := by
    have h := lg_mul (1 : GA E n) 1
    rw [mul_one] at h
    simp only [show lg (1 : GA E n) = 0 by linarith, ofAdd_zero]
  map_mul' g h := by rw [lg_mul, ofAdd_add]

theorem lg_zpow (g : GA E n) (m : ℤ) : lg (g ^ m) = m * lg g := by
  have h := map_zpow (lgHom (E := E) (n := n)) g m
  have h2 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow] at h2
  simpa [lgHom, zsmul_eq_mul] using h2

theorem lg_rat (γ : GL (Fin n) E) : lg (ratGL E n γ) = 0 := by
  have hd : GeneralLinearGroup.det (ratGL E n γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [lg_eq, hd, show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _,
    Real.log_one]

theorem lg_e_pos (hn : 1 ≤ n) : 0 < lg (splitCentre E n 1) := by
  rw [lg_eq, det_splitCentre_one, map_pow, Real.log_pow]
  exact mul_pos (by exact_mod_cast hn) (Real.log_pos (one_lt_ideleNorm_eIdele E))

theorem ratRange_le : (ratGL E n).range ≤ latticeGL E n := le_sup_left

instance discreteTopology_ratRange : DiscreteTopology (ratGL E n).range :=
  DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion (ratRange_le (E := E) (n := n)))
    (Continuous.subtype_mk continuous_subtype_val _) (Subgroup.inclusion_injective _)

theorem tsum_indicator (hn : 1 ≤ n) (h : GA E n → ℝ≥0∞) (hh : LeftInv (latticeGL E n) h) (v : ℝ → ℝ≥0∞)
    (y : GA E n) :
    ∑' γ : latticeGL E n, (stdDom (ratGL E n).range).indicator (fun g => h g * v (lg g)) ((γ : GA E n) * y) =
      h y * ∑' m : ℤ, v (lg y + m * lg (splitCentre E n 1)) := by
  set Γ₀ := (ratGL E n).range with hΓ₀
  set e := splitCentre E n 1 with he
  have hc : lg e ≠ 0 := (lg_e_pos hn).ne'
  let r : ℤ → Γ₀ := fun m => (existsUnique_stdDom Γ₀ (e ^ m * y)).choose
  have hr : ∀ m, ((r m : Γ₀) : GA E n) * (e ^ m * y) ∈ stdDom Γ₀ := fun m =>
    (existsUnique_stdDom Γ₀ (e ^ m * y)).choose_spec.1
  have hrlg : ∀ m, lg ((r m : Γ₀) : GA E n) = 0 := fun m => by
    obtain ⟨γ, hγ⟩ := (r m).2
    rw [← hγ]
    exact lg_rat γ
  let g : ℤ → latticeGL E n := fun m =>
    ⟨((r m : Γ₀) : GA E n) * e ^ m, mul_mem (ratRange_le (r m).2) (zpow_mem_latticeGL m)⟩
  have hlgg : ∀ m : ℤ, lg (((g m : latticeGL E n) : GA E n) * y) = lg y + m * lg e := fun m => by
    change lg (((r m : Γ₀) : GA E n) * e ^ m * y) = _
    rw [lg_mul, lg_mul, hrlg, lg_zpow]
    ring
  have hinj : Function.Injective g := fun m m' hmm => by
    have h1 := congrArg (fun γ : latticeGL E n => lg ((γ : GA E n) * y)) hmm
    simp only [hlgg] at h1
    have h2 : (m : ℝ) * lg e = m' * lg e := by linarith
    exact_mod_cast mul_right_cancel₀ hc h2
  rw [← hinj.tsum_eq, ← ENNReal.tsum_mul_left]
  · refine tsum_congr fun m => ?_
    have hmem : ((g m : latticeGL E n) : GA E n) * y ∈ stdDom Γ₀ := by
      change ((r m : Γ₀) : GA E n) * e ^ m * y ∈ stdDom Γ₀
      rw [mul_assoc]
      exact hr m
    rw [indicator_of_mem hmem]
    change h (((g m : latticeGL E n) : GA E n) * y) * v (lg (((g m : latticeGL E n) : GA E n) * y)) = _
    rw [hlgg, hh _ (g m).2 y]
  · intro γ hγ
    have hin : (γ : GA E n) * y ∈ stdDom Γ₀ := by
      by_contra hc'
      exact hγ (indicator_of_notMem hc' _)
    obtain ⟨γ₁, m, hγe⟩ := mem_latticeGL_iff.1 γ.2
    refine ⟨m, Subtype.ext ?_⟩
    have h3 : ((⟨ratGL E n γ₁, γ₁, rfl⟩ : Γ₀) : GA E n) * (e ^ m * y) ∈ stdDom Γ₀ := by
      change ratGL E n γ₁ * (e ^ m * y) ∈ stdDom Γ₀
      rw [← mul_assoc, hγe]
      exact hin
    have hu := (existsUnique_stdDom Γ₀ (e ^ m * y)).unique (hr m) h3
    change ((r m : Γ₀) : GA E n) * e ^ m = γ
    rw [hu]
    exact hγe

theorem lintegral_unfold (μ : Measure (GA E n)) [μ.IsMulLeftInvariant] (hn : 1 ≤ n) (h : GA E n → ℝ≥0∞)
    (hh : LeftInv (latticeGL E n) h) (hm : AEMeasurable h μ) (v : ℝ → ℝ≥0∞) (hv : Measurable v) :
    ∫⁻ g in stdDom (ratGL E n).range, h g * v (lg g) ∂μ =
      ∫⁻ q, h q.out * ∑' m : ℤ, v (lg q.out + m * lg (splitCentre E n 1)) ∂quotMeasure (latticeGL E n) μ := by
  have hS := measurableSet_stdDom (ratGL E n).range
  have hf : AEMeasurable ((stdDom (ratGL E n).range).indicator fun g => h g * v (lg g)) μ :=
    (hm.mul (hv.comp_aemeasurable continuous_logAbs_det.measurable.aemeasurable)).indicator hS
  rw [← lintegral_indicator hS, lintegral_eq_lintegral_tsum (Γ := latticeGL E n) hf]
  exact lintegral_congr fun q => tsum_indicator hn h hh v q.out

end DiscreteGroups.T1.G
end
end

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem borelSpace_H : BorelSpace (H E n 0) := ⟨rfl⟩

attribute [local instance] borelSpace_H

theorem GL_zero_subsingleton (a b : GA E 0) : a = b := Units.ext (Matrix.ext fun i => Fin.elim0 i)

def eH : GA E n ≃ₜ* H E n 0 where
  toFun g := (g, 1)
  invFun x := x.1
  left_inv g := rfl
  right_inv x := Prod.ext rfl (GL_zero_subsingleton _ _)
  map_mul' g h := Prod.ext rfl (mul_one 1).symm
  continuous_toFun := continuous_id.prodMk continuous_const
  continuous_invFun := continuous_fst

def muG (D : Dom E n 0) : Measure (GA E n) := D.μ.map (eH (E := E) (n := n)).symm

theorem measurable_eH : Measurable (eH (E := E) (n := n)) := (eH (E := E) (n := n)).continuous.measurable

theorem measurable_eH_symm : Measurable (eH (E := E) (n := n)).symm :=
  (eH (E := E) (n := n)).symm.continuous.measurable

theorem mp_fst (D : Dom E n 0) : MeasurePreserving (fun x : H E n 0 => x.1) D.μ (muG D) :=
  ⟨measurable_eH_symm, rfl⟩

theorem mp_eH (D : Dom E n 0) : MeasurePreserving (eH (E := E) (n := n)) (muG D) D.μ := by
  refine ⟨measurable_eH, ?_⟩
  rw [muG, Measure.map_map measurable_eH measurable_eH_symm]
  have : (eH (E := E) (n := n)) ∘ (eH (E := E) (n := n)).symm = id := funext fun x => (eH (E := E) (n := n)).apply_symm_apply x
  rw [this, Measure.map_id]

theorem isHaar_D (D : Dom E n 0) : D.μ.IsHaarMeasure := by
  obtain ⟨h1, h2, h3, h4⟩ := D.haar
  exact { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ _ h4, toIsMulLeftInvariant := h1, toIsOpenPosMeasure := h3 }

instance muG_haar (D : Dom E n 0) : (muG D).IsHaarMeasure := by
  haveI := isHaar_D D
  exact (eH (E := E) (n := n)).symm.isHaarMeasure_map D.μ

instance muG_right (D : Dom E n 0) : (muG D).IsMulRightInvariant := by
  haveI := D.haar.2.1
  refine ⟨fun g => ?_⟩
  rw [muG, Measure.map_map (continuous_mul_const g).measurable measurable_eH_symm]
  have e : (fun x => x * g) ∘ (eH (E := E) (n := n)).symm =
      (eH (E := E) (n := n)).symm ∘ fun x => x * eH g := funext fun x => by
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
  rw [e, ← Measure.map_map measurable_eH_symm (continuous_mul_const _).measurable, map_mul_right_eq_self]

def eR (δ : ratH E n 0) : (ratGL E n).range :=
  ⟨(δ : H E n 0).1, by
    obtain ⟨p, hp⟩ := δ.2
    exact ⟨p.1, congrArg Prod.fst hp⟩⟩

theorem eR_bijective : Function.Bijective (eR (E := E) (n := n)) := by
  refine ⟨fun δ δ' h => Subtype.ext (Prod.ext (congrArg Subtype.val h) (GL_zero_subsingleton _ _)), fun γ => ?_⟩
  obtain ⟨γ₁, hγ⟩ := γ.2
  refine ⟨⟨((γ : GA E n), 1), ⟨(γ₁, 1), Prod.ext hγ (GL_zero_subsingleton _ _)⟩⟩, rfl⟩

theorem isFundamentalDomain_pre (D : Dom E n 0) :
    IsFundamentalDomain (ratGL E n).range ((eH (E := E) (n := n)) ⁻¹' D.F) (muG D) :=
  D.fd.preimage_of_equiv (mp_eH D).quasiMeasurePreserving eR_bijective fun δ x => by
    change (((δ : H E n 0).1 * x, 1) : H E n 0) = (δ : H E n 0) * (x, 1)
    exact Prod.ext rfl (GL_zero_subsingleton _ _)

theorem lintegral_nu (D : Dom E n 0) (Φ : GA E n → ℝ≥0∞) (hΦ : ∀ γ ∈ (ratGL E n).range, ∀ g, Φ (γ * g) = Φ g) :
    ∫⁻ x, Φ x.1 ∂D.ν = ∫⁻ g in stdDom (ratGL E n).range, Φ g ∂muG D := by
  let eM : GA E n ≃ᵐ H E n 0 := (eH (E := E) (n := n)).toHomeomorph.toMeasurableEquiv
  have hm : (muG D).map eM = D.μ := (mp_eH D).map_eq
  rw [Dom.ν, ← hm, eM.restrict_map, lintegral_map_equiv]
  haveI : SMulInvariantMeasure (ratGL E n).range (GA E n) (muG D) :=
    ⟨fun γ s _ => measure_preimage_mul (muG D) (γ : GA E n) s⟩
  refine (isFundamentalDomain_pre D).setLIntegral_eq (isFundamentalDomain_stdDom _ _) (fun g => Φ g) fun γ g => ?_
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hΦ γ γ.2 g

theorem lg_rat_mul (γ : GA E n) (hγ : γ ∈ (ratGL E n).range) (g : GA E n) : lg (γ * g) = lg g := by
  obtain ⟨γ₁, rfl⟩ := hγ
  rw [lg_mul, lg_rat, zero_add]

theorem tsum_shift_le (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ s : ℝ, ∑' m : ℤ, ‖u (s + m * c)‖ₑ ^ (2 : ℝ) ≤ K := by
  obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  let N : ℕ := ⌈2 * |R| / c⌉₊ + 1
  refine ⟨N * ENNReal.ofReal M ^ (2 : ℝ), by finiteness, fun s => ?_⟩
  let a : ℤ := ⌈(-|R| - s) / c⌉
  let S : Finset ℤ := Finset.Icc a (a + ⌈2 * |R| / c⌉₊)
  have hz : ∀ m ∉ S, ‖u (s + m * c)‖ₑ ^ (2 : ℝ) = 0 := fun m hm => by
    have hu0 : u (s + m * c) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun ht => hm ?_
      have h1 := hR ht
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at h1
      have hR' : R ≤ |R| := le_abs_self R
      rw [Finset.mem_Icc]
      constructor
      · refine Int.ceil_le.2 ?_
        rw [div_le_iff₀ hc]
        linarith
      · have h2 : ((m : ℝ) - a) * c ≤ 2 * |R| := by
          have ha : (a : ℝ) ≥ (-|R| - s) / c := Int.le_ceil _
          rw [ge_iff_le, div_le_iff₀ hc] at ha
          nlinarith
        have h3 : ((m : ℝ) - a) ≤ 2 * |R| / c := by rw [le_div_iff₀ hc]; linarith
        have h4 : (2 * |R| / c) ≤ (⌈2 * |R| / c⌉₊ : ℝ) := Nat.le_ceil _
        have h5 : ((m - a : ℤ) : ℝ) ≤ ((⌈2 * |R| / c⌉₊ : ℕ) : ℤ) := by push_cast; linarith
        have h6 := Int.cast_le.1 h5
        omega
    rw [hu0, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz]
  have hb : ∀ m ∈ S, ‖u (s + m * c)‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal M ^ (2 : ℝ) := fun m _ =>
    ENNReal.rpow_le_rpow (by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM _)) (by norm_num)
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr
  have : S.card = ⌈2 * |R| / c⌉₊ + 1 := by
    simp only [S, Int.card_Icc]
    omega
  rw [this]
  try simp [N]

variable (D : Dom E n 0)

def Tf (u : ℝ → ℂ) (F : L2 (latticeGL E n) (muG D)) : H E n 0 → ℂ :=
  fun x => lift (latticeGL E n) F x.1 * u (ldet x)

theorem ldet_eq (x : H E n 0) : ldet x = lg x.1 := rfl

theorem aesm_Tf (u : ℝ → ℂ) (hu : Continuous u) (F : L2 (latticeGL E n) (muG D)) :
    AEStronglyMeasurable (Tf D u F) D.ν := by
  have h1 : AEStronglyMeasurable (lift (latticeGL E n) F) (muG D) :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : AEStronglyMeasurable (fun x : H E n 0 => lift (latticeGL E n) F x.1) D.μ :=
    h1.comp_measurePreserving (mp_fst D)
  exact (h2.mul (hu.comp continuous_ldet).aestronglyMeasurable).restrict

theorem lintegral_Tf (hn : 1 ≤ n) (u : ℝ → ℂ) (hu : Continuous u) (F : L2 (latticeGL E n) (muG D)) :
    ∫⁻ x, ‖Tf D u F x‖ₑ ^ (2 : ℝ) ∂D.ν =
      ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) * ∑' m : ℤ, ‖u (lg q.out + m * lg (splitCentre E n 1))‖ₑ ^ (2 : ℝ)
        ∂quotMeasure (latticeGL E n) (muG D) := by
  have e1 : ∀ x : H E n 0, ‖Tf D u F x‖ₑ ^ (2 : ℝ) =
      (fun g => ‖lift (latticeGL E n) F g‖ₑ ^ (2 : ℝ) * ‖u (lg g)‖ₑ ^ (2 : ℝ)) x.1 := fun x => by
    simp only [Tf, enorm_mul, ldet_eq]
    exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  refine (lintegral_congr e1).trans ((lintegral_nu D _ fun γ hγ g => ?_).trans
    ((lintegral_unfold (muG D) hn (fun g => ‖lift (latticeGL E n) F g‖ₑ ^ (2 : ℝ))
      (fun γ hγ g => by simp only [(memL2_lift F).1 γ hγ g])
      ((aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)).enorm.pow_const _)
      (fun s => ‖u s‖ₑ ^ (2 : ℝ)) (hu.measurable.enorm.pow_const _)).trans
      (lintegral_congr fun q => ?_)))
  · simp only [lg_rat_mul γ hγ g, (memL2_lift F).1 γ (ratRange_le hγ) g]
  · simp only [lift, Quotient.out_eq]

theorem exists_bound (hn : 1 ≤ n) (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ F : L2 (latticeGL E n) (muG D),
      MemLp (Tf D u F) 2 D.ν ∧ eLpNorm (Tf D u F) 2 D.ν ≤ ENNReal.ofReal k * eLpNorm F 2 (quotMeasure (latticeGL E n) (muG D)) := by
  obtain ⟨K, hK, hKs⟩ := tsum_shift_le u hu hs _ (lg_e_pos (E := E) hn)
  refine ⟨Real.sqrt K.toReal, Real.sqrt_nonneg _, fun F => ?_⟩
  have hk : ENNReal.ofReal (Real.sqrt K.toReal) ^ (2 : ℝ) = K := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  have hle : ∫⁻ x, ‖Tf D u F x‖ₑ ^ (2 : ℝ) ∂D.ν ≤
      ∫⁻ q, ‖(Real.sqrt K.toReal : ℂ) • F q‖ₑ ^ (2 : ℝ) ∂quotMeasure (latticeGL E n) (muG D) := by
    rw [lintegral_Tf D hn u hu F]
    refine lintegral_mono fun q => ?_
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_comm]
    gcongr
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hk]
    exact hKs _
  have key : eLpNorm (Tf D u F) 2 D.ν ≤ eLpNorm (fun q => (Real.sqrt K.toReal : ℂ) • F q) 2
      (quotMeasure (latticeGL E n) (muG D)) := by
    have hm : AEStronglyMeasurable (fun q => (Real.sqrt K.toReal : ℂ) • F q)
        (quotMeasure (latticeGL E n) (muG D)) := by
      convert (Lp.aestronglyMeasurable F).const_smul (Real.sqrt K.toReal : ℂ) using 1
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (aesm_Tf D u hu F),
      eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_le_rpow hle (by norm_num)
  have key2 : eLpNorm (fun q => (Real.sqrt K.toReal : ℂ) • F q) 2 (quotMeasure (latticeGL E n) (muG D)) =
      ENNReal.ofReal (Real.sqrt K.toReal) * eLpNorm F 2 (quotMeasure (latticeGL E n) (muG D)) := by
    change eLpNorm ((Real.sqrt K.toReal : ℂ) • (F : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E n) → ℂ)) 2 _ = _
    rw [eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [key2] at key
  exact ⟨key.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top F)), key⟩

end DiscreteGroups.T1.G

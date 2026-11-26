module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExpStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExp
open Filter Topology

namespace GlobalTheory

theorem one_sub_unit_mul_exp_ne_zero (L : ℝ) (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) (t : ℝ)
    (ht : t ≠ 0) : 1 - χ * Complex.exp (-((L : ℂ) * (t : ℂ))) ≠ 0 := by
  intro h
  have h1 : χ * Complex.exp (-((L : ℂ) * (t : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, hχ, one_mul, Complex.norm_exp, norm_one] at h2
  have h3 : (-((L : ℂ) * (t : ℂ))).re = 0 := by
    have := Real.exp_eq_one_iff _ |>.mp h2
    exact this
  simp at h3
  rcases h3 with h3 | h3
  · exact hL.ne' h3
  · exact ht h3

theorem exists_analytic_sub_one_div_one_sub_unit_mul_exp :
    ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  intro L hL χ hχ
  by_cases h1 : χ = 1
  · subst h1
    set f : ℂ → ℂ := fun w => 1 - Complex.exp (-((L : ℂ) * w)) with hf
    have hfd : Differentiable ℂ f := by
      rw [hf]; fun_prop
    have hkd : Differentiable ℂ (dslope f 0) := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hfd.differentiableOn
    have hk : ∀ w : ℂ, w ≠ 0 → dslope f 0 w = f w / w := by
      intro w hw
      rw [dslope_of_ne _ hw, slope_def_field]
      simp [hf]
    have hk0 : dslope f 0 0 = L := by
      rw [dslope_same]
      have : HasDerivAt f (0 - Complex.exp (-((L : ℂ) * 0)) * (-((L : ℂ) * 1))) 0 :=
        (hasDerivAt_const _ _).sub (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).neg.cexp)
      rw [this.deriv]; simp
    refine ⟨fun s => (dslope f 0 (s - 1))⁻¹, ?_, ?_, fun h => absurd rfl h⟩
    · intro x _
      have hd : Differentiable ℂ (fun s : ℂ => dslope f 0 (s - 1)) :=
        hkd.comp (differentiable_id.sub_const 1)
      refine (hd.analyticAt _).inv ?_
      by_cases hx : x = 1
      · subst hx
        show dslope f 0 (((1 : ℝ) : ℂ) - 1) ≠ 0
        rw [Complex.ofReal_one, sub_self, hk0]
        exact_mod_cast hL.ne'
      · have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
        have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
        show dslope f 0 ((x : ℂ) - 1) ≠ 0
        rw [hk _ hx'']
        refine div_ne_zero ?_ hx''
        have := one_sub_unit_mul_exp_ne_zero L hL 1 hχ (x - 1) hx'
        simpa [hf] using this
    · intro x hx
      have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx.ne'
      have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
      show (dslope f 0 ((x : ℂ) - 1))⁻¹ = _
      rw [hk _ hx'', inv_div, one_mul]
  · refine ⟨fun s => (s - 1) / (1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))), ?_, fun _ _ => rfl,
      fun _ => by simp⟩
    intro x _
    have hd : Differentiable ℂ (fun s : ℂ => 1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))) := by
      fun_prop
    have hn : Differentiable ℂ (fun s : ℂ => s - 1) := by fun_prop
    refine (hn.analyticAt _).div (hd.analyticAt _) ?_
    by_cases hx : x = 1
    · subst hx
      simpa [sub_eq_zero] using fun h => h1 (Eq.symm h)
    · have := one_sub_unit_mul_exp_ne_zero L hL χ hχ (x - 1) (sub_ne_zero.mpr hx)
      simpa using this

end GlobalTheory
end

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_sub_one_div_one_sub_mul_exp : ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  first | exact @GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp | exact GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp | (intros; apply GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGL
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ShellFD

theorem isFundamentalDomain_shell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hT0 : 0 < T := one_pos.trans hT1
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hTe : Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) = T ^ (-1 : ℤ) := by
    rw [hT, Real.exp_one_pow, _root_.zpow_neg_one, ← Real.exp_neg]
    push_cast
    rfl
  have hcomm : ∀ (n : ℤ) g, splitCentre E a 1 ^ n * g = g * splitCentre E a 1 ^ n := fun n g => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
    exact GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ g
  have hTadd : ∀ m n : ℤ, T ^ m * T ^ n = T ^ (m + n) := fun m n => (zpow_add₀ hT0.ne' m n).symm
  rw [hTe]
  refine
    { nullMeasurableSet := h𝓕.nullMeasurableSet.inter
        ((measurableSet_lt measurable_const hδc.measurable).inter
          (measurableSet_le hδc.measurable measurable_const)).nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have hN := ae_iff.1 h𝓕.ae_covers
    have hB : μ (⋃ n : ℤ, (fun x => splitCentre E a 1 ^ n * x) ⁻¹'
        {x | ¬∃ γ : (ratGL E a).range, γ • x ∈ 𝓕}) = 0 :=
      measure_iUnion_null fun n => (measurePreserving_mul_left μ _).quasiMeasurePreserving.preimage_null hN
    refine Filter.mem_of_superset (compl_mem_ae_iff.2 hB) fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq, not_exists, not_not] at hx
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow (hδ0 x) hT1
    obtain ⟨γ, hγ⟩ := not_forall_not.1 (hx (-(m + 1)))
    obtain ⟨γ0, hγ0⟩ := γ.2
    refine ⟨⟨(γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)),
      mul_mem (Subgroup.mem_sup_left γ.2) (GlobalTheory.CuspRep.CuspidalL2GL.zpow_mem_latticeGL _)⟩, ?_, ?_, ?_⟩
    · rw [Subgroup.smul_def]
      simpa only [Subgroup.smul_def, smul_eq_mul, mul_assoc] using hγ
    · rw [Subgroup.smul_def]
      change T ^ (-1 : ℤ) < δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x)
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-1 : ℤ) = T ^ (-(m + 1)) * T ^ m := by rw [hTadd]; ring_nf
        _ < T ^ (-(m + 1)) * δ x := mul_lt_mul_of_pos_left hm1 (zpow_pos hT0 _)
    · rw [Subgroup.smul_def]
      change δ ((γ : GA E a) * splitCentre E a 1 ^ (-(m + 1)) * x) ≤ 1
      rw [mul_assoc, ← hγ0, hδr, hδz]
      calc T ^ (-(m + 1)) * δ x ≤ T ^ (-(m + 1)) * T ^ (m + 1) := mul_le_mul_of_nonneg_left hm2 (zpow_pos hT0 _).le
        _ = 1 := by rw [hTadd]; simp
  · intro g1 g2 hne
    have key : ∀ (g : latticeGL E a) (γ : GL (Fin a) E) (n : ℤ),
        ratGL E a γ * splitCentre E a 1 ^ n = g → ∀ y ∈ g • (𝓕 ∩ {g | T ^ (-1 : ℤ) < δ g ∧ δ g ≤ 1}),
        T ^ (n - 1) < δ y ∧ δ y ≤ T ^ n ∧
          y ∈ splitCentre E a 1 ^ n • ((⟨ratGL E a γ, γ, rfl⟩ : (ratGL E a).range) • 𝓕) := by
      rintro g γ n hg y ⟨x, ⟨hx, hx1, hx2⟩, rfl⟩
      have hy : g • x = splitCentre E a 1 ^ n * (ratGL E a γ * x) := by
        rw [Subgroup.smul_def, smul_eq_mul, ← hg, hcomm n (ratGL E a γ * x)]
        simp only [mul_assoc, hcomm n x]
      beta_reduce
      rw [hy]
      refine ⟨?_, ?_, Set.smul_mem_smul_set (Set.smul_mem_smul_set hx)⟩
      · rw [hδz, hδr]
        calc T ^ (n - 1) = T ^ n * T ^ (-1 : ℤ) := by rw [hTadd]; ring_nf
          _ < T ^ n * δ x := mul_lt_mul_of_pos_left hx1 (zpow_pos hT0 _)
      · rw [hδz, hδr]
        calc T ^ n * δ x ≤ T ^ n * 1 := mul_le_mul_of_nonneg_left hx2 (zpow_pos hT0 _).le
          _ = T ^ n := mul_one _
    obtain ⟨γ1, n1, h1⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g1.2
    obtain ⟨γ2, n2, h2⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 g2.2
    by_cases hn : n1 = n2
    · subst hn
      have hγ : (⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) ≠ ⟨ratGL E a γ2, γ2, rfl⟩ := fun h => hne <|
        Subtype.ext (by rw [← h1, ← h2, show ratGL E a γ1 = ratGL E a γ2 from congrArg Subtype.val h])
      have hd : AEDisjoint μ (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ1, γ1, rfl⟩ : (ratGL E a).range) • 𝓕))
          (splitCentre E a 1 ^ n1 • ((⟨ratGL E a γ2, γ2, rfl⟩ : (ratGL E a).range) • 𝓕)) := by
        set_option synthInstance.maxHeartbeats 200000 in
          rw [AEDisjoint, ← Set.smul_set_inter, measure_smul]
        exact h𝓕.aedisjoint hγ
      exact hd.mono (fun y hy => (key g1 γ1 n1 h1 y hy).2.2) (fun y hy => (key g2 γ2 n1 h2 y hy).2.2)
    · refine Disjoint.aedisjoint (Set.disjoint_left.2 fun y hy1 hy2 => ?_)
      obtain ⟨a1, b1, -⟩ := key g1 γ1 n1 h1 y hy1
      obtain ⟨a2, b2, -⟩ := key g2 γ2 n2 h2 y hy2
      rcases lt_or_gt_of_ne hn with h | h
      · exact absurd a2 (not_lt.2 (b1.trans (zpow_le_zpow_right₀ hT1.le (by omega : n1 ≤ n2 - 1))))
      · exact absurd a1 (not_lt.2 (b2.trans (zpow_le_zpow_right₀ hT1.le (by omega : n2 ≤ n1 - 1))))

end GlobalTheory.ShellFD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGLStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalDomain_det_shell_latticeGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  first | (exact @GlobalTheory.ShellFD.isFundamentalDomain_shell) | (exact GlobalTheory.ShellFD.isFundamentalDomain_shell) | (intros; apply GlobalTheory.ShellFD.isFundamentalDomain_shell  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntire
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntire
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.DiffInt

theorem integral_absDet_cpow_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  intro E _ _ _ a μ S hS hμS c hc hδ F hF C hC
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδdef
  have hδc : Continuous δ := GlobalTheory.RSThetaLow.continuous_absDet
  have hae : ∀ᵐ g ∂(μ.restrict S), g ∈ S := ae_restrict_mem₀ hS
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  have key := GlobalTheory.integral_mul_cpow_of_rapid_decay_entire (GA E a) (μ.restrict S) δ F hδc.measurable
    (hae.mono fun g hg => ⟨lt_of_lt_of_le hc (hδ g hg).1, (hδ g hg).2⟩)
    (by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hδc.aestronglyMeasurable ?_
      refine hae.mono fun g hg => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hc.le (hδ g hg).1)]
      exact (hδ g hg).2)
    hF.aestronglyMeasurable
    (by
      intro K
      refine ⟨max C 0 / c ^ K, hae.mono fun g hg => ?_⟩
      have hcK : 0 < c ^ K := pow_pos hc K
      have h1 : c ^ K ≤ δ g ^ K := pow_le_pow_left₀ hc.le (hδ g hg).1 K
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      calc ‖F g‖ * c ^ K ≤ max C 0 * c ^ K :=
            mul_le_mul_of_nonneg_right ((hC g).trans (le_max_left _ _)) hcK.le
        _ ≤ max C 0 * δ g ^ K := mul_le_mul_of_nonneg_left h1 (le_max_right _ _))
  have := key.2.comp (differentiable_id.sub_const (1 : ℂ))
  exact this

end GlobalTheory.DiffInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntireStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_absDet_cpow_bounded_shell_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  first | exact @GlobalTheory.DiffInt.integral_absDet_cpow_entire | exact GlobalTheory.DiffInt.integral_absDet_cpow_entire | (intros; apply GlobalTheory.DiffInt.integral_absDet_cpow_entire; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShells
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShells
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaGeom

theorem integral_low_geometric : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕 F hF C hC hinv χ hχ hχF s hs
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef
  set e : GA E a := splitCentre E a 1 with he
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  have hd0 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  have hL : 0 < L := mul_pos (Nat.cast_pos.2 ha) hd0
  have hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L := by
    rw [Real.exp_one_pow, hLdef]; push_cast; rfl
  have hδk : ∀ (k : ℕ) g, δ (e ^ k * g) = Real.exp (L * k) * δ g := fun k g => by
    have h := GlobalTheory.RSTheta.absDet_zpow_mul (E := E) (a := a) (k : ℤ) g
    rw [zpow_natCast, hTL, zpow_natCast, ← Real.exp_nat_mul, mul_comm (k : ℝ)] at h
    exact h
  have hFk : ∀ (k : ℕ) g, F (e ^ k * g) = χ ^ k * F g := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', mul_assoc, hχF, ih, pow_succ']; ring

  set f : GA E a → ℂ := fun g => F g * ((δ g : ℝ) : ℂ) ^ (s - 1) with hf
  have hfc : Continuous f := hF.mul ((Complex.continuous_ofReal.comp hδc).cpow continuous_const
    fun g => Complex.ofReal_mem_slitPlane.2 (hδ0 g))
  have hfr : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    simp only [hf, hinv, hδr]

  set S : ℕ → Set (GA E a) := fun k => {g | Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))} with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (isOpen_lt continuous_const hδc).measurableSet.inter (isClosed_le hδc continuous_const).measurableSet

  have hSU : (⋃ k, S k) = {g | δ g ≤ 1} := by
    ext g
    simp only [hS, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, -, h2⟩
      exact h2.trans (Real.exp_le_one_iff.2 (by have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith))
    · intro h
      have hl : 0 ≤ -Real.log (δ g) / L := div_nonneg (neg_nonneg.2 (Real.log_nonpos (hδ0 g).le h)) hL.le
      have h1 := Nat.lt_floor_add_one (-Real.log (δ g) / L)
      have h2 := Nat.floor_le hl
      set k := ⌊-Real.log (δ g) / L⌋₊
      refine ⟨k, ?_, ?_⟩
      ·
        rw [div_lt_iff₀ hL] at h1
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_lt_exp.2 (by linarith)
      · rw [le_div_iff₀ hL] at h2
        rw [← Real.exp_log (hδ0 g)]
        exact Real.exp_le_exp.2 (by linarith)
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    have key : ∀ j k : ℕ, j < k → Disjoint (S j) (S k) := by
      intro j k hjk
      refine Set.disjoint_left.2 fun g hj hk => ?_
      have h1 : Real.exp (-(L * k)) ≤ Real.exp (-(L * ((j : ℝ) + 1))) := by
        refine Real.exp_le_exp.2 ?_
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        nlinarith
      exact absurd (hk.2.trans h1) (not_le.2 hj.1)
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h
    · exact (key k j h).symm

  have hint : IntegrableOn f (𝓕 ∩ {g | δ g ≤ 1}) μ := by
    have h0 := (GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ha μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C
    refine h0.mono' hfc.aestronglyMeasurable.restrict (.of_forall fun g => ?_)
    rw [hf, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ0 g)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (hC g) (Real.rpow_nonneg (hδ0 g).le _)
  have hsum1 := hasSum_integral_iUnion (μ := μ.restrict 𝓕) (f := f) hSm hSd
    (by rw [hSU, IntegrableOn, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet,
      Set.inter_comm]; exact hint)
  rw [hSU, Measure.restrict_restrict (isClosed_le hδc continuous_const).measurableSet, Set.inter_comm] at hsum1

  set r : ℂ := starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) with hr
  have hr1 : ‖r‖ < 1 := by
    have hre : (-(((L : ℝ) : ℂ) * (s - 1))).re = -(L * (s.re - 1)) := by simp
    have hpos : 0 < L * (s.re - 1) := mul_pos hL (by linarith)
    rw [hr, norm_mul, Complex.norm_conj, hχ, one_mul, Complex.norm_exp, hre]
    exact (Real.exp_lt_exp.2 (by linarith : -(L * (s.re - 1)) < 0)).trans_eq Real.exp_zero
  have hcancel : ∀ k : ℕ, r ^ k * (χ ^ k * Complex.exp (((L * k : ℝ) : ℂ) * (s - 1))) = 1 := by
    intro k
    have hc : starRingEnd ℂ χ * χ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]; simp
    have he1 : Complex.exp (((L * k : ℝ) : ℂ) * (s - 1)) = Complex.exp (((L : ℝ) : ℂ) * (s - 1)) ^ k := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [he1, ← mul_pow, ← mul_pow, hr]
    have : starRingEnd ℂ χ * Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * (χ * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) =
        (starRingEnd ℂ χ * χ) * (Complex.exp (-(((L : ℝ) : ℂ) * (s - 1))) * Complex.exp (((L : ℝ) : ℂ) * (s - 1))) := by ring
    rw [this, hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; simp

  haveI : Countable (ratGL E a).range := by
    haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
    haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
    exact (ratGL E a).rangeRestrict_surjective.countable
  have hexp : ∀ t : ℝ, ((Real.exp t : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((t : ℝ) : ℂ) * (s - 1)) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
      Real.log_exp]
  have hfd : ∀ k : ℕ, IsFundamentalDomain (ratGL E a).range ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) μ := by
    intro k
    refine h𝓕.preimage_of_equiv (measurePreserving_mul_left μ ((e ^ k)⁻¹)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    have hc0 : Commute e (γ : GA E a) := CuspidalL2GL.splitCentre_comm 1 _
    have hc : Commute ((e ^ k)⁻¹) (γ : GA E a) := (hc0.pow_left k).inv_left
    show (e ^ k)⁻¹ * ((γ : GA E a) * x) = (γ : GA E a) * ((e ^ k)⁻¹ * x)
    rw [← mul_assoc, hc.eq, mul_assoc]
  have hG0 : ∀ (γ : (ratGL E a).range) (x : GA E a), (S 0).indicator f (γ • x) = (S 0).indicator f x := by
    rintro ⟨_, γ, rfl⟩ x
    show (S 0).indicator f (ratGL E a γ * x) = (S 0).indicator f x
    simp only [Set.indicator_apply, hS, Set.mem_setOf_eq, hδr, hfr]
  have hshell : ∀ k : ℕ, ∫ g in S k, f g ∂(μ.restrict 𝓕) = r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) := by
    intro k
    have hX : 0 < Real.exp (L * k) := Real.exp_pos _
    have hmem : ∀ g, g ∈ S k ↔ e ^ k * g ∈ S 0 := by
      intro g
      have e1 : Real.exp (L * k) * Real.exp (-(L * ((k : ℝ) + 1))) = Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have e2 : Real.exp (L * k) * Real.exp (-(L * k)) = Real.exp (-(L * ((0 : ℕ) : ℝ))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      show (Real.exp (-(L * ((k : ℝ) + 1))) < δ g ∧ δ g ≤ Real.exp (-(L * k))) ↔
        (Real.exp (-(L * (((0 : ℕ) : ℝ) + 1))) < δ (e ^ k * g) ∧ δ (e ^ k * g) ≤ Real.exp (-(L * ((0 : ℕ) : ℝ))))
      rw [hδk, ← e1, ← e2, mul_lt_mul_iff_of_pos_left hX, mul_le_mul_iff_of_pos_left hX]
    have hpt : ∀ g, (S k).indicator f g = r ^ k * (S 0).indicator f (e ^ k * g) := by
      intro g
      by_cases hg : g ∈ S k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hmem g).1 hg)]
        simp only [hf, hFk, hδk]
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (hδ0 g).le, hexp]
        linear_combination (-(F g * ((δ g : ℝ) : ℂ) ^ (s - 1))) * hcancel k
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hmem g).2 hg), mul_zero]
    have hpre : (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕) = 𝓕 := by ext x; simp
    rw [← integral_indicator (hSm k), ← integral_indicator (hSm 0), integral_congr_ae (.of_forall hpt),
      integral_const_mul]
    congr 1
    calc ∫ g in 𝓕, (S 0).indicator f (e ^ k * g) ∂μ
        = ∫ g in (fun x => e ^ k * x) ⁻¹' ((fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕), (S 0).indicator f (e ^ k * g) ∂μ := by
          rw [hpre]
      _ = ∫ y in (fun y => (e ^ k)⁻¹ * y) ⁻¹' 𝓕, (S 0).indicator f y ∂μ :=
          (measurePreserving_mul_left μ (e ^ k)).setIntegral_preimage_emb (measurableEmbedding_mulLeft _) _ _
      _ = ∫ y in 𝓕, (S 0).indicator f y ∂μ := by
          set_option synthInstance.maxHeartbeats 200000 in
            exact (hfd k).setIntegral_eq h𝓕 hG0
  have hgeo := (hasSum_geometric_of_norm_lt_one hr1).mul_right (∫ g in S 0, f g ∂(μ.restrict 𝓕))
  have hsum2 : HasSum (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕))
      ((1 - r)⁻¹ * ∫ g in S 0, f g ∂(μ.restrict 𝓕)) := by
    rw [show (fun k : ℕ => ∫ g in S k, f g ∂(μ.restrict 𝓕)) = fun k => r ^ k * ∫ g in S 0, f g ∂(μ.restrict 𝓕) from
      funext hshell]
    exact hgeo
  have hS0 : S 0 = {g | Real.exp (-L) < δ g ∧ δ g ≤ 1} := by
    ext g; simp [hS]
  have hI0 : ∫ g in S 0, f g ∂(μ.restrict 𝓕) = ∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ := by
    rw [Measure.restrict_restrict (hSm 0), Set.inter_comm, hS0]
  show ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, f g ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-L) < δ g ∧ δ g ≤ 1}, f g ∂μ) / (1 - r)
  rw [← hI0, hsum1.unique hsum2, div_eq_inv_mul]

end GlobalTheory.RSThetaGeom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShellsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_det_le_one_eq_geometric_series_shells : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  first | (exact @GlobalTheory.RSThetaGeom.integral_low_geometric) | (exact GlobalTheory.RSThetaGeom.integral_low_geometric) | (intros; apply GlobalTheory.RSThetaGeom.integral_low_geometric  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralChars
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralChars
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.RSResidue

theorem rsHat_zero_props_two : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  intro E _ _ _ a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hc' : ∀ g, rsHat ℓ φ.1 φ'.1 Φ J η g 0 = (∫ u, rsInf ℓ φ.1 φ'.1 Φ g u ∂infMeasure E a) * c := hc
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hc']
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc', norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ g
    have e : rsPsi ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y =>
      rsPsi_ratGL_mul ℓ h.2.1 h'.2.1 Φ J η γ g y
    simp only [rsHat, e]
  · intro z g
    have e : ∀ u, rsInf ℓ φ.1 φ'.1 Φ (GeneralLinearGroup.scalar (Fin a) z * g) u =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * rsInf ℓ φ.1 φ'.1 Φ g u := fun u => by
      simp only [rsInf, mul_assoc (GeneralLinearGroup.scalar (Fin a) z) g, h.2.2.1, h'.2.2.1, map_mul]
      ring
    rw [hc', hc', funext e, integral_const_mul]
    ring

end GlobalTheory.RSResidue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralCharsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_kernel_zero_coeff_two_central_chars : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  first | exact @GlobalTheory.RSResidue.rsHat_zero_props_two | exact GlobalTheory.RSResidue.rsHat_zero_props_two | (intros; apply GlobalTheory.RSResidue.rsHat_zero_props_two; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOne
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section
namespace GlobalTheory.RSThetaCont
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_bddForms_of_mspanR {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) : φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω := by
  have hc0 := CuspSub.hasCentral_iff.2 hπ
  have hu : π.IsUnitary := ⟨ω, hω, hc0⟩
  have hR : φ.1 ∈ GlobalTheory.JSW.mspanR π := hφ.elim (fun h => GlobalTheory.JSW.mem_mspanR_of_mem h) id
  obtain ⟨ψ, hψ, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hu φ.1 hR
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil, hψ] at h0
  have hR' : φ.1 ∈ GlobalTheory.JSW.rspan π := (GlobalTheory.JSW.rspan_eq_mspanR π).symm ▸ hR
  have hZ : GlobalTheory.JSW.rspan π ≤ GlobalTheory.JSW.Central.centralFns E a ω := by
    refine GlobalTheory.JSW.rspan_le (fun ψ hψ z g => hc0.apply hψ z g) (fun F hF h z g => ?_) fun F hF X _ ν _ k γ _ z g => ?_
    · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
      rw [mul_assoc]; exact hF z _
    · change GlobalTheory.JSW.kerInf ν k γ F (GeneralLinearGroup.scalar (Fin a) z * g) = _ * GlobalTheory.JSW.kerInf ν k γ F g
      simp only [GlobalTheory.JSW.kerInf, mul_assoc]
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [hF z]; ring
  exact ⟨h0.cont, GlobalTheory.JSW.rspan_left π hR', hZ hR', h0.bdd⟩

theorem resFn_props {ω ω' : HChar E} (hω : ω.IsUnitary) (hω' : ω'.IsUnitary) {φ φ' : Sm E a}
    (h : φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω) (h' : φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω')
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) :
    Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧
    (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧
    (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 =
      GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧
    ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
      GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  exact GlobalTheory.T.rankinSelberg_kernel_zero_coeff_two_central_chars E a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η

theorem isFundamentalDomain_shell (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
      (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  exact GlobalTheory.T.isFundamentalDomain_det_shell_latticeGL E a ha μ 𝓕 h𝓕

theorem differentiable_setIntegral_cpow (μ : Measure (GA E a)) {S : Set (GA E a)} (hSm : NullMeasurableSet S μ) (hS : μ S < ⊤) {c : ℝ} (hc : 0 < c)
    (hδ : ∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1)
    {F : GA E a → ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ g, ‖F g‖ ≤ C) :
    Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  exact GlobalTheory.T.integral_absDet_cpow_bounded_shell_entire E a μ S hSm hS c hc hδ F hF C hC

theorem integral_low_geometric (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {F : GA E a → ℂ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ g, ‖F g‖ ≤ C) (hrat : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) {χ : ℂ}
    (hχ : ‖χ‖ = 1) (hz : ∀ g, F (splitCentre E a 1 * g) = χ * F g) {s : ℂ} (hs : 1 < s.re) :
    ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ =
      (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
          (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) /
      (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  exact GlobalTheory.T.integral_det_le_one_eq_geometric_series_shells E a ha μ 𝓕 h𝓕 F hF C hC hrat χ hχ hz s hs

theorem exists_analytic_ratio {L : ℝ} (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) : ∃ h : ℂ → ℂ,
    (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧
    (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧
    (χ ≠ 1 → h 1 = 0) := by
  exact GlobalTheory.T.exists_analytic_sub_one_div_one_sub_mul_exp L hL χ hχ

theorem setIntegral_eq_zero_of_scalar (μ : Measure (GA E a)) [μ.IsHaarMeasure] {S : Set (GA E a)}
    (hS : IsFundamentalDomain (latticeGL E a) S μ) {F : GA E a → ℂ} (hinv : ∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g)
    (z : Neutral.B1.Ideles E) {ν : ℂ} (hν : ν ≠ 1) (hz : ∀ g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ν * F g) :
    ∫ g in S, F g ∂μ = 0 := by
  have h1 := GlobalTheory.RSResidue.setIntegral_mul_right hS hinv (GeneralLinearGroup.scalar (Fin a) z)
  have e : ∀ g, F (g * GeneralLinearGroup.scalar (Fin a) z) = ν * F g := fun g => by
    rw [← hz g]
    congr 1
    exact Units.ext (Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq.symm
  simp only [e, integral_const_mul] at h1
  have h2 : (ν - 1) * ∫ g in S, F g ∂μ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hν)


open GlobalTheory.CuspRep.CuspidalL2GL in
theorem theta_integral_continuation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → F (x : ℂ) = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) ∧ (ω = ω' → F 1 = c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ) ∧ (ω ≠ ω' → F 1 = 0) := by
  intro E _ _ _ a ℓ Φ hΦ hcs hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span E a ℓ Φ hΦ hcs hs J η μ 𝓕 𝓕' h𝓕 h𝓕'
  refine ⟨c, hc0, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ'
  have ha : 0 < a := ℓ.pos
  have hb := mem_bddForms_of_mspanR hω hπ hφ
  have hb' := mem_bddForms_of_mspanR hω' hπ' hφ'
  have hu : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩
  have hu' : π'.IsUnitary := ⟨ω', hω', CuspSub.hasCentral_iff.2 hπ'⟩
  have hT : GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ := ⟨hΦ, hcs, hs⟩
  have hR : φ ∈ GlobalTheory.RSThetaLowM.rsm π :=
    show φ.1 ∈ GlobalTheory.JSW.mspanR π from hφ.elim (fun h => GlobalTheory.JSW.mem_mspanR_of_mem h) id
  have hR' : φ' ∈ GlobalTheory.RSThetaLowM.rsm π' :=
    show φ'.1 ∈ GlobalTheory.JSW.mspanR π' from hφ'.elim (fun h => GlobalTheory.JSW.mem_mspanR_of_mem h) id
  have hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    GlobalTheory.RSThetaLow.continuous_absDet
  have hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := fun g => (ideleModule E _).2
  have hlowm : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} :=
    (isClosed_le hδc continuous_const).measurableSet
  have hupm : MeasurableSet {g : GA E a | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)} :=
    (isClosed_le continuous_const hδc).measurableSet

  obtain ⟨r1, ⟨C0, r2⟩, r3, r4⟩ := resFn_props hω hω' hb hb' hT J η
  obtain ⟨z0, hz0⟩ : ∃ z0 : Neutral.B1.Ideles E, splitCentre E a 1 = GeneralLinearGroup.scalar (Fin a) z0 :=
    ⟨_, splitCentre_eq_scalar 1⟩
  set χ : ℂ := ((ω.1 z0 : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z0 : ℂˣ) : ℂ) with hχdef
  have hχ : ‖χ‖ = 1 := by rw [hχdef, norm_mul, Complex.norm_conj, hω z0, hω' z0, one_mul]
  have hzF : ∀ g, GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (splitCentre E a 1 * g) 0 =
      χ * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := fun g => by rw [hz0]; exact r4 z0 g

  have hS := isFundamentalDomain_shell ha μ h𝓕
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hSfin := hS
  replace hSfin : μ (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
      (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) < ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hS]; exact measure_lt_top _ _
  have hL : 0 < (a : ℝ) * (Module.finrank ℚ E : ℝ) :=
    mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)
  set I : ℂ → ℂ := fun s => ∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
      (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
      GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ
    with hIdef
  have hI : Differentiable ℂ I := differentiable_setIntegral_cpow μ hS.nullMeasurableSet hSfin (Real.exp_pos _)
    (fun g hg => ⟨hg.2.1.le, hg.2.2⟩) r1 r2
  have hA : ∀ s : ℂ, 1 < s.re → GlobalTheory.RSThetaLow.partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s = I s /
      (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) :=
    fun s hs => integral_low_geometric ha μ h𝓕 r1 r2 r3 hχ hzF hs
  obtain ⟨h, hh1, hh2, hh3⟩ := exists_analytic_ratio hL (starRingEnd ℂ χ) (by rw [Complex.norm_conj]; exact hχ)

  obtain ⟨-, -, u3, u4, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous
    hcs hs J η μ 𝓕 h𝓕
  obtain ⟨-, -, b3⟩ := GlobalTheory.RSThetaLowM.partB_entire J η hu hu' hR hR' hb.1 hb'.1 hT h𝓕
  set K0 : ℂ := ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)} ∩
      {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) ∂μ
    with hK0
  set G : ℂ → ℂ := fun s => (∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ) +
      GlobalTheory.RSThetaLow.partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s - K0 with hGdef
  have hG : Differentiable ℂ G := (u4.add b3).sub_const K0
  have hFan : ∀ x : ℝ, 0 < x → AnalyticAt ℂ (fun s => (s - 1) * G s + I s * h s) (x : ℂ) := fun x hx =>
    ((analyticAt_id.sub analyticAt_const).mul (hG.analyticAt _)).add ((hI.analyticAt _).mul (hh1 x hx))

  have hFeq : ∀ x : ℝ, 1 < x → ((x : ℂ) - 1) * G x + I x * h x = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕,
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ := by
    intro x hx
    have e1 : ∀ g : GA E a, (((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) : ℂ) =
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) := fun g =>
      Complex.ofReal_cpow (hδ0 g).le x
    simp only [e1]
    have hxre : 1 < (x : ℂ).re := by simpa using hx
    have hlow := GlobalTheory.RSThetaLowM.integral_low_eq J η hu hu' hR hR' hb.1 hb'.1 hT h𝓕 hxre
    have etsum : ∀ g, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := fun g =>
      GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g
    have iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ))
        (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
      simp only [etsum]; exact hlow.1
    have iUp := u3 (x : ℂ)
    have hint : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ))
        𝓕 μ := by
      refine (iLo.union iUp).mono_set fun g hg => ?_
      rcases le_total (ideleModule E (GeneralLinearGroup.det g) : ℝ) 1 with h' | h'
      · exact Or.inl ⟨hg, h'⟩
      · exact Or.inr ⟨hg, h'⟩
    have s1 := integral_inter_add_diff hlowm hint
    have s2 := integral_inter_add_diff hlowm iUp
    have eset : (𝓕 ∩ {g : GA E a | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) \ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} =
        𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} := by
      ext g
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, not_le]
      exact ⟨fun h' => ⟨h'.1.1, h'.2⟩, fun h' => ⟨⟨h'.1, h'.2.le⟩, h'.2⟩⟩
    rw [eset] at s2
    have sK : ∫ g in 𝓕 ∩ {g : GA E a | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)} ∩
        {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
          ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ = K0 := by
      rw [hK0]
      refine integral_congr_ae ?_
      refine (ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_inter_left _ Set.inter_subset_right) (ae_restrict_mem (hupm.inter hlowm))).mono
        fun g hg => ?_
      have h1 : (ideleModule E (GeneralLinearGroup.det g) : ℝ) = 1 := le_antisymm hg.2 hg.1
      simp only [h1, Complex.ofReal_one, Complex.one_cpow, mul_one]
    have sLo : ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
          ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
          ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ =
        GlobalTheory.RSThetaLow.partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 x + GlobalTheory.RSThetaLow.partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 x := by
      simp only [etsum]; exact hlow.2
    rw [← s1, sLo, hA x hxre, hh2 x hx]
    rw [sK] at s2
    have hup : ∫ g in 𝓕 \ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
          ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
          ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ =
        (∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
          (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
            ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
            ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ) - K0 := by
      rw [← s2]; ring
    rw [hup, hGdef]
    push_cast
    ring
  refine ⟨fun s => (s - 1) * G s + I s * h s, hFan, hFeq, ?_, ?_⟩
  ·
    intro hωω
    subst hωω
    obtain ⟨-, ht⟩ := hc π π' ω hω hπ hπ' φ φ' hφ hφ'
    have hcont : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * G x + I x * h x) (𝓝[>] 1)
        (𝓝 (((1 : ℂ) - 1) * G 1 + I 1 * h 1)) := by
      have h1 := (hFan 1 one_pos).continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto 1)
      simp only [Complex.ofReal_one] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique hcont (ht.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx using (hFeq x hx).symm
  ·
    intro hne
    show ((1 : ℂ) - 1) * G 1 + I 1 * h 1 = 0
    rw [sub_self, zero_mul, zero_add]
    by_cases hχ1 : starRingEnd ℂ χ = 1
    · have hχ1' : χ = 1 := by simpa using congrArg (starRingEnd ℂ) hχ1
      obtain ⟨z, hz⟩ : ∃ z, ω.1 z ≠ ω'.1 z := by
        by_contra hall
        push_neg at hall
        exact hne (Subtype.ext (MonoidHom.ext hall))
      have hν : ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) ≠ 1 := by
        intro hν1
        apply hz
        refine Units.ext ?_
        have hw : starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * ((ω'.1 z : ℂˣ) : ℂ) = 1 := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hω' z]; simp
        calc ((ω.1 z : ℂˣ) : ℂ) = ((ω.1 z : ℂˣ) : ℂ) * (starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * ((ω'.1 z : ℂˣ) : ℂ)) := by
              rw [hw, mul_one]
          _ = (((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ)) * ((ω'.1 z : ℂˣ) : ℂ) := by ring
          _ = ((ω'.1 z : ℂˣ) : ℂ) := by rw [hν1, one_mul]
      have hzp : ∀ (n : ℤ) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (splitCentre E a 1 ^ n * g) 0 =
          GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
        intro n
        refine Int.induction_on n ?_ ?_ ?_
        · intro g; rw [zpow_zero, one_mul]
        · intro k ih g
          rw [_root_.zpow_add_one, mul_assoc, ih, hzF, hχ1', one_mul]
        · intro k ih g
          rw [_root_.zpow_sub_one, mul_assoc, ih]
          have := hzF ((splitCentre E a 1)⁻¹ * g)
          rw [← mul_assoc, mul_inv_cancel, one_mul, hχ1', one_mul] at this
          exact this.symm
      have hinv : ∀ γ ∈ latticeGL E a, ∀ g, GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (γ * g) 0 =
          GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
        intro γ hγ g
        obtain ⟨γ', n, rfl⟩ := mem_latticeGL_iff.1 hγ
        rw [mul_assoc, r3, hzp]
      have h0 := setIntegral_eq_zero_of_scalar μ hS (F := fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) hinv z hν (r4 z)
      have hI1 : I 1 = 0 := by
        rw [hIdef]
        simp only [sub_self, Complex.cpow_zero, mul_one]
        exact h0
      rw [hI1, zero_mul]
    · rw [hh3 hχ1, mul_zero]

end GlobalTheory.RSThetaCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOneStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → F (x : ℂ) = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) ∧ (ω = ω' → F 1 = c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ) ∧ (ω ≠ ω' → F 1 = 0) := by
  first | exact @GlobalTheory.RSThetaCont.theta_integral_continuation | exact GlobalTheory.RSThetaCont.theta_integral_continuation | (intros; apply GlobalTheory.RSThetaCont.theta_integral_continuation <;> assumption)
end

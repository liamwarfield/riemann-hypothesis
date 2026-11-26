module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOutsideOfConductor
noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul


open GlobalTheory.CuspRep.CuspidalL2GL in
theorem exists_fundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure],
  ∃ 𝓕₀ : Set (GA E n), IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕₀ μ := by
  intro E _ _ n μ _
  haveI := CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := CuspidalL2GL.t2Space_GA E n
  haveI := CuspidalL2GL.secondCountableTopology_GA E n
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hsub : (GlobalTheory.CellDec.NE E n : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E n) := DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E n).range : Set (GA E n))) hsub
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E n)
  exact ⟨𝓕, h𝓕 _⟩

end GlobalTheory.ZEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergL
noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul.Smooth

theorem zint_eq_mul_partialL_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro E _ _ _ a σ σ' ha hσ hσ' T hTs hψ hT hT'
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ ha hσ T hT
  obtain ⟨α', _ℓ', _Φ', _J', _η', π', ω', _φ', hα', hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ' ha hσ' T hT'
  subst hπ hπ'
  obtain ⟨μ₀, hμ₀, 𝓕₁, h𝓕₁⟩ : ∃ (μ : Measure (GA E (m + 1))) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E (m + 1))),
      IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
    haveI : DiscreteTopology (ratGL E (m + 1)).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E (m + 1)
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E (m + 1)).range
    exact ⟨Measure.haar, inferInstance, 𝓕, h𝓕 _⟩
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α' w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let αe' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α' ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hαe' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe' w.1 = α' w := fun w => dif_pos w.2
  have hsatσ : ∀ (ρ : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hs : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe w.1) = sat (CG.mk π) w.1 := fun w => by
    rw [hαe w]; exact hα w
  have hs' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe' w.1) = sat (CG.mk π') w.1 := fun w => by
    rw [hαe' w]; exact hα' w
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hs ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (αe' w)) := fun w hw => by
    rw [hs' ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨b, hb1, hbN, hbC, hbF⟩ := GlobalTheory.T.exists_bump_shintani_alt E m T hψ
  obtain ⟨φ, hφR, hU, hK, hW⟩ := hbF π αe hsat
  obtain ⟨φ', hφR', hU', hK', hW'⟩ := hbF π' αe' hsat'
  obtain ⟨hφ0, hφ0', N, Φ, hN, hΦc, hΦs, hΦr, hΦp, hC2⟩ := GlobalTheory.ZEul.unfolded_bump_eq E m T hTs hψ b hb1 hbN hbC π π' ω ω' hω hω' hωc hωc' αe αe'
    hsat hsat' φ φ' hφR hφR' hU hK hU' hK' hW hW'
  refine ⟨N, Φ, π, π', φ, φ', rfl, rfl, hφR, hφR', hφ0, hφ0', hN, hΦc, hΦs, ?_, ?_⟩
  · intro ℓ hℓ
    have hl : ℓ = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hl
    exact hΦr
  intro μ hμ 𝓕 h𝓕
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.ZEul.exists_fundamentalDomain_NE E (m + 1) μ
  obtain ⟨c, hc, hC1⟩ := GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker E m μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC2 μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.T.exp_integral_differentiable_real_re_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  refine ⟨fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe' w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α' w i : ℂˣ) : ℂ) := by funext w i; rw [hαe' w]
    have hf1 : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1]; exact hfin x hx
    have hf1' : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe' w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1']; exact hfin' x hx
    obtain ⟨hd, hd', e12, e11, e22⟩ := hid x hx hf1 hf1'
    have z12 := (hC1 π π' ω ω' hω hω' hωc hωc' φ φ' hφR hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd').2
    have z11 := (hC1 π π ω ω hω hω hωc hωc φ φ hφR hφR N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd).2
    have z22 := (hC1 π' π' ω' ω' hω' hω' hωc' hωc' φ' φ' hφR' hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd' hd').2
    have A12 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe' w.1) x hx hq hf1 hf1').tsum_eq
    have A11 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe w.1) x hx hq hf1 hf1).tsum_eq
    have A22 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe' w.1) (fun w => αe' w.1) x hx hq hf1' hf1').tsum_eq
    simp only [hs, hs'] at A12 A11 A22
    refine ⟨?_, ?_, ?_⟩
    · rw [z12, e12, A12]; ring
    · rw [z11, e11, A11]; ring
    · rw [z22, e22, A22]; ring

end GlobalTheory.ZEul.Smooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergLStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | exact GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | (intros; apply GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurableCompInfGLProd
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.MspanROrth

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {ω : HChar E}

theorem measurable_chart_prod {F : GA E a → ℂ} (hF : Continuous F) :
    Measurable fun p : GA E a × Lie E a => chart F p.1 p.2 := by
  classical
  have h1 := GlobalTheory.ConstTermSmooth.continuousOn_chart (E := E) (a := a) hF
  have e : (fun p : GA E a × Lie E a => chart F p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart F p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a))
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      exact dif_neg fun h => hp ⟨Set.mem_univ _, h⟩
  rw [e]
  exact h1.measurable_piecewise continuousOn_const (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun q : GA E a × Lie E a => chart F q.1 q.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem measurable_comp_infGL' {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => F (g * infGL E a (γ x)) :=
  by
  have h := (measurable_comp_infGL_prod hF hγ).comp (measurable_prodMk_left (x := g) (β := X))
  exact h

theorem integrable_of_isRapidInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable k ν := by
  have h := hk.2.2 0
  simp only [pow_zero, mul_one] at h
  exact (integrable_norm_iff hk.1.aestronglyMeasurable).1 h

theorem kerInf_mem_bddForms {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) :
    (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ bddForms E a ω := by
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := integrable_of_isRapidInf hk
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (measurable_comp_infGL' h.1 g hk.2.1)).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.norm.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_id.mul continuous_const)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [mul_assoc, h.2.1]
  · rw [← integral_const_mul]
    beta_reduce
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.norm.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

section Lemmas

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left (hω : ω.IsUnitary) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F ψ : GA E a → ℂ}
    (h : F ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  haveI : SFinite (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨⟨fun n => if n = 0 then μ.restrict (stdDom (latticeGL E a)) else 0,
      fun n => by dsimp only; split_ifs <;> infer_instance,
      Measure.ext fun s hs => by
        rw [Measure.sum_apply _ hs, tsum_eq_single 0 (fun n hn => by simp [hn])]
        simp⟩⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := integrable_of_isRapidInf hk
  have hm : Measurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1) :=
    ((hk.1.comp measurable_snd).mul (measurable_comp_infGL_prod h.1 hk.2.1)).mul
      ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki.norm).mono' hm.aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms hk h) h' hD).2]
  simp only [← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem mul_right_mem_mspanR {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_pet_eq_zero (hω : ω.IsUnitary) {π : CuspSub E a} (hπ : π.HasCentChar ω) (T : Set (GA E a → ℂ))
    (hT : ∀ G ∈ T, G ∈ bddForms E a ω) (hTr : ∀ G ∈ T, ∀ h : GA E a, (fun g => G (g * h)) ∈ T)
    (h0 : ∀ φ ∈ π.V, ∀ G ∈ T, pet (latticeGL E a) μ φ.1 G = 0) {F : GA E a → ℂ} (hF : F ∈ mspanR π) :
    F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0 := by
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun G hG => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hT G hG), hF.2 G hG, hF'.2 G hG, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun G _ => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun G hG => by
        rw [pet_smul_left, hF.2 G hG, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S := fun F hF h =>
    ⟨mul_right_mem_bddForms hF.1 h, fun G hG => by
      rw [pet_mul_right_left μ hω hF.1 (hT G hG) h]; exact hF.2 _ (hTr G hG h⁻¹)⟩
  refine Submodule.mem_sInf.1 hF S ⟨fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun G hG => h0 φ hφ G hG⟩, htr, fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hk hF.1, fun G hG => ?_⟩⟩
  rw [pet_kerInf_left μ hω hk hF.1 (hT G hG)]
  exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 G hG))

end Lemmas

theorem setIntegral_mspanR_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π π'' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π''.HasCentChar ω →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    (∀ φ ∈ π.V, ∀ φ'' ∈ π''.V, GlobalTheory.AutomorphicL2Unitary.pet (latticeGL E a) μ φ.1 φ''.1 = 0) →
    ∀ 𝓕' : Set (GA E a), IsFundamentalDomain (latticeGL E a) 𝓕' μ →
    ∀ F ∈ GlobalTheory.JSW.mspanR π, ∀ F'' ∈ GlobalTheory.JSW.mspanR π'', ∫ g in 𝓕', F g * starRingEnd ℂ (F'' g) ∂μ = 0 := by
  intro E _ _ _ a _ π π'' ω hω hπ hπ'' μ _ h0 𝓕' h𝓕 F hF F'' hF''
  have hB := GlobalTheory.CuspOrth.cuspFormsBounded
  have base : ∀ φ ∈ π.V, ∀ ψ ∈ π''.V, ∀ h : GA E a, pet (latticeGL E a) μ φ.1 (fun g => ψ.1 (g * h)) = 0 := by
    intro φ hφ ψ hψ h
    have e := pet_mul_right_left μ hω (mem_bddForms_of_cuspSub hB hω hπ hφ) (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h⁻¹
    rw [inv_inv] at e
    rw [← e]
    obtain ⟨y, k, e'⟩ : ∃ y k, h⁻¹ = infGL E a y * finGL E a k := ⟨_, _, (infGL_mul_finGL h⁻¹).symm⟩
    rw [e']
    have H := (GlobalTheory.KeepOrth.pet_eq_zero_of_orthogonal hB E a π π'' ω hω hπ hπ'' μ h0).1 (act (.fin k) φ)
      (π.stable (.fin k) φ hφ) ψ hψ y
    refine Eq.trans (congrArg (fun F => pet (latticeGL E a) μ F ψ.1) (funext fun g => ?_)) H
    show φ.1 (g * (infGL E a y * finGL E a k)) = (act (.fin k) φ).1 (g * infGL E a y)
    rw [← mul_assoc]; rfl
  have A1 := fun {F} (hF : F ∈ mspanR π) => mspanR_pet_eq_zero μ hω hπ
    {G | ∃ ψ ∈ π''.V, ∃ h : GA E a, G = fun g => ψ.1 (g * h)}
    (by rintro _ ⟨ψ, hψ, h, rfl⟩; exact mul_right_mem_bddForms (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h)
    (by rintro _ ⟨ψ, hψ, h, rfl⟩ k; exact ⟨ψ, hψ, k * h, funext fun g => by simp only [mul_assoc]⟩)
    (by rintro φ hφ _ ⟨ψ, hψ, h, rfl⟩; exact base φ hφ ψ hψ h) hF
  have A2 := fun {G} (hG : G ∈ mspanR π'') => mspanR_pet_eq_zero μ hω hπ'' (mspanR π : Set (GA E a → ℂ))
    (fun F hF => (A1 hF).1) (fun F hF h => mul_right_mem_mspanR hF h)
    (fun ψ hψ F hF => by
      rw [← conj_pet, (A1 hF).2 _ ⟨ψ, hψ, 1, funext fun g => by rw [mul_one]⟩, map_zero]) hG
  obtain ⟨bF'', h2⟩ := A2 hF''
  rw [← (pet_eq_setIntegral hω (A1 hF).1 bF'' h𝓕).2, ← conj_pet, h2 F hF, map_zero]

end GlobalTheory.MspanROrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfNeOfHasCentChar
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CuspOrth

theorem pet_eq_zero_of_ne_of_hasCentChar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary →
    π.HasCentChar ω → π'.HasCentChar ω → CG.mk π ≠ CG.mk π' →
    ∀ φ ∈ π.V, ∀ φ' ∈ π'.V, pet (latticeGL E a) μ φ.1 φ'.1 = 0 := by
  intro E _ _ _ a μ _ π π' ω hω hπ hπ' hne
  exact pet_eq_zero_of_mk_ne μ hω (CuspSub.hasCentral_iff.2 hπ) (CuspSub.hasCentral_iff.2 hπ') hne

end GlobalTheory.CuspOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFinite
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RSJ

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem valued_natCast_apply (E : Type) [Field E] [NumberField E] (N : ℕ)
    (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v) = v.valuation E (N : E) := by
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N]
  exact valuedAdicCompletion_eq_valuation' v (N : E)

theorem natLat_iff_mem_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) →
      ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  intro E _ _ N hN J hJ x
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hc0 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (N : E) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).2 hN0
  have hc : ∀ v : HeightOneSpectrum (𝓞 E),
      exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) = v.valuation E (N : E) := by
    intro v
    rw [hJ, GroundTheory.Global.count_spanSingleton v hN0, neg_neg, exp_log (hc0 v)]
  rw [GroundTheory.Global.mem_idealFiniteAdeles]
  simp only [hc]
  have hunit : (N : FiniteAdeleRing (𝓞 E) E) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N, ← map_mul, mul_inv_cancel₀ hN0,
      map_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ v
    change Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v * z v) ≤ _
    rw [map_mul, valued_natCast_apply]
    have : Valued.v (z v) ≤ 1 := by
      have h := hz v
      rwa [mem_adicCompletionIntegers] at h
    calc v.valuation E (N : E) * Valued.v (z v) ≤ v.valuation E (N : E) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hx
    refine ⟨algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ * x, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers]
      change Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) v * x v) ≤ 1
      rw [map_mul]
      change Valued.v (((N : E)⁻¹ : E) : v.adicCompletion E) * Valued.v (x v) ≤ 1
      rw [valuedAdicCompletion_eq_valuation' v, map_inv₀]
      exact (GroundTheory.Global.inv_mul_le_one_iff_withZero (hc0 v)).2 (hx v)
    · rw [← mul_assoc, hunit, one_mul]

end GlobalTheory.RSJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFiniteStatement
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) → ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  first | (exact @GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (exact GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (intros; apply GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuation
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.UnitaryBC
  GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.RSNonvan
open scoped nonZeroDivisors

theorem logNorm_eq_log_ideleModule (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) :=
  GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule E d

theorem natLat_iff (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : 0 < N) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (z : FiniteAdeleRing (𝓞 E) E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J :=
  GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles E N hN J hJ z

namespace GlobalTheory.RSNonvan

theorem detPow_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (x : ℝ) (g : GA E a) :
    GlobalTheory.RSJ.detPow E a x g = ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem secInv_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (hℓ : (ℓ : ℕ) + 1 = a)
    (u : Fin a → Cinf E) : GlobalTheory.RSJ.secInv u = (GlobalTheory.RSTheta.rowGL ℓ u)⁻¹ := by
  have hrow : GlobalTheory.RSJ.secRow u = GlobalTheory.RSTheta.rowMat ℓ u := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    have : ((i : ℕ) + 1 = a) ↔ i = ℓ := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; subst h; exact hℓ
    by_cases h : i = ℓ
    · simp [h, hℓ]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  unfold GlobalTheory.RSJ.secInv
  by_cases hu : IsUnit (u ℓ)
  · have hd : IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dite_eq_left hd]
    congr 1
    ext : 1
    rw [GlobalTheory.RSTheta.val_rowGL hu, ← hrow]
    rfl
  · have hd : ¬ IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dite_eq_right hd, GlobalTheory.RSTheta.rowGL, dite_eq_right hu, inv_one]

theorem indN_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (v : Fin a → Af E) :
    GlobalTheory.RSJ.indN N v = (GlobalTheory.ThetaPoisson.latt a J).indicator 1 (v - Pi.single ℓ 1) := by
  have key : (∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) ↔
      v - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J := by
    simp only [GlobalTheory.ThetaPoisson.latt, Set.mem_setOf_eq, Pi.sub_apply]
    refine forall_congr' fun i => ?_
    have e : (if (i : ℕ) + 1 = a then (1 : Af E) else 0) = (Pi.single ℓ (1 : Af E) : Fin a → Af E) i := by
      by_cases h : i = ℓ
      · subst h; simp [hℓ]
      · have : ¬ ((i : ℕ) + 1 = a) := fun h' => h (Fin.ext (by omega))
        simp [this, h]
    rw [e, natLat_iff E N hN J hJ]
  unfold GlobalTheory.RSJ.indN
  by_cases h : ∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N
  · rw [if_pos h, Set.indicator_of_mem (key.1 h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]

theorem zint_eq_thetaZ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (x : ℝ) :
    GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ φ' Φ J (Pi.single ℓ 1) x := by
  unfold GlobalTheory.RSJ.Zint GlobalTheory.RSPole.thetaZ
  congr 1
  funext g
  rw [detPow_eq]
  congr 1
  unfold GlobalTheory.RSJ.thetaSum
  refine tsum_congr fun ξ => ?_
  simp only [GlobalTheory.RSJ.Psi, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, GlobalTheory.RSJ.rowAct, secInv_eq ℓ hℓ, map_inv]
  rw [indN_eq N hN ℓ hℓ J hJ]
  rfl

open GlobalTheory.CuspRep.CuspidalL2GL in
theorem haarFD (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩

theorem samedeg_continuation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (σ ≠ σ' → F 1 = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (F x / ((x : ℂ) - 1)) := by
  intro E _ _ _ a σ σ' ha hσ hσ' T hT hu hu'
  obtain ⟨N, Φ, π, π', φ, φ', hπ, hπ', hφ, hφ', -, -, hN, hΦc, hΦs, hΦr, hZ'⟩ := GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL E a σ σ' ha hσ hσ' T hT.1 hT.2 hu hu'
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := haarFD E a
  obtain ⟨H, hHd, hHpos, hZH⟩ := hZ' μ 𝓕 h𝓕
  obtain ⟨ω, hωu, hω⟩ := id hσ
  obtain ⟨ω', hωu', hω'⟩ := id hσ'
  rw [← hπ] at hω
  rw [← hπ'] at hω'
  rw [CG.hasCentChar_mk] at hω hω'
  set ℓ : Fin a := ⟨a - 1, by omega⟩ with hℓdef
  have hℓ : (ℓ : ℕ) + 1 = a := by simp [ℓ]; omega
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  set J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E))
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hN0) with hJdef
  have hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) := rfl
  have hπu : π.IsUnitary := ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩
  have hπu' : π'.IsUnitary := ⟨ω', hωu', CuspSub.hasCentral_iff.2 hω'⟩
  obtain ⟨φs, -, hφs⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu hφ
  obtain ⟨φs', -, hφs'⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu' hφ'
  have hφs1 : φs.1 = φ := hφs
  have hφs1' : φs'.1 = φ' := hφs'
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne E a ℓ Φ hΦc hΦs (hΦr ℓ hℓ) J (Pi.single ℓ 1) μ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨Fz, hFa, hFx, hF1, hF1'⟩ := hc π π' ω ω' hωu hωu' hω hω' φs φs'
    (Or.inr (hφs1 ▸ hφ)) (Or.inr (hφs1' ▸ hφ'))
  have hH0 : ∀ x : ℝ, H x ≠ 0 := fun x h => by
    have := (hHpos x).1
    rw [h] at this
    simp at this
  refine ⟨fun s => Fz s / H s, fun x hx => (hFa x hx).div (hHd.analyticAt _) (hH0 x), fun hne => ?_, fun x hx => ?_⟩
  · have h1 : Fz 1 = 0 := by
      by_cases hωω : ω = ω'
      · subst hωω
        rw [hF1 rfl]
        have hne' : CG.mk π ≠ CG.mk π' := by rw [hπ, hπ']; exact hne
        have h0 := fun φ hφ φ'' hφ'' =>
          GlobalTheory.CuspOrth.pet_eq_zero_of_ne_of_hasCentChar E a μ π π' ω hωu hω hω' hne' φ hφ φ'' hφ''
        rw [GlobalTheory.MspanROrth.setIntegral_mspanR_eq_zero E a ha π π' ω hωu hω hω' μ h0 𝓕' h𝓕' φs.1
          (hφs1 ▸ hφ) φs'.1 (hφs1' ▸ hφ'), mul_zero]
      · exact hF1' hωω
    simp [h1]
  · obtain ⟨-, hprod⟩ := (GlobalTheory.T.localRankinSelberg_logarithm_formula).2 E a a σ σ' hσ hσ' T hu hu' x hx
    have hx1 : (x : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hx.ne'
    have e : Fz x / H x / ((x : ℂ) - 1) = ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 := by
      rw [hFx x hx]
      have h2 := (hZH x hx).1
      rw [zint_eq_thetaZ μ 𝓕 φ φ' Φ N hN ℓ hℓ J hJ x] at h2
      simp only [GlobalTheory.RSPole.thetaZ] at h2
      rw [hφs1, hφs1', h2]
      simp only [lfac]
      have := hH0 x
      push_cast
      field_simp
    change HasProd _ (Fz x / H x / ((x : ℂ) - 1))
    rw [e]
    exact hprod.tprod_eq ▸ hprod

end GlobalTheory.RSNonvan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuationStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (σ ≠ σ' → F 1 = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (F x / ((x : ℂ) - 1)) := by
  first
  | exact @GlobalTheory.RSNonvan.samedeg_continuation
  | exact GlobalTheory.RSNonvan.samedeg_continuation
  | (intros; apply GlobalTheory.RSNonvan.samedeg_continuation <;> assumption)
end

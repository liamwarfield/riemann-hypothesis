module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LieAlgebraAction
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnitChartOperator
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ConjugationOnUnits
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerBlockIndex
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LatticeLastEntry
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AdelicCharacterCondition
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InverseDerivativeContinuity
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerFunctional
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GoodInverseDenseRange
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FinitePartOfMeet
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PsiDeterminantFlag

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirrorMap
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace MirrorMap

theorem mir_map {R S : Type} [CommRing R] [CommRing S] {a m : ℕ} (p : R →+* S) {γ : GL (Fin a) R}
    (h : Mir m γ) : Mir m (GeneralLinearGroup.map p γ) := by
  intro i k hik
  change p (γ.val i k) = _
  rw [h i k hik, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mirS_mul (h10 : MirabolicColumnBlock) {S : Finset (Pl E)} {x g : GA E a} (hx : Mir (a - 1) x) (hg : MirS S g) :
    MirS S (x * g) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map (pInf E) hx) hg.1
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map ((pLoc E w).comp (pFin E)) hx) (hg.2 w hw)

end MirrorMap

theorem mirror_global_of : MirabolicColumnBlock → G0 → G5 → G9 → PlacewiseToOutsideS → FourierUniquenessMirabolic → WeakApproximationGL → WhittakerVanishingImpliesZero := by
  intro h10 h0 h5 h9 h9b h11 h12 E _ _ _ a ψ hψ S hcond φ hgood hleft hsat hvan
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hproj, -⟩ := h0 E a
  have hcont : Continuous (Wh ψ φ) := ((h5 E a ψ hψ).2.2.2 φ hgood).1
  have step1 : ∀ g, MirS S g → Wh ψ φ g = 0 := by
    intro g hg
    obtain ⟨g₀, e1, e2, e3⟩ := hproj S g
    refine h9b E a S (Wh ψ φ) hcont ?_ g g₀ e1 e2 e3 ?_
    · intro w hw h hh hz u
      obtain ⟨B, hB⟩ := hsat w hw
      exact h9 E a ψ hψ w (hcond w hw) B φ hgood hB h hh hz u
    · refine hvan g₀ ⟨?_, fun w hw => ?_⟩ e3
      · rw [e1]; exact hg.1
      · rw [e2 w hw]; exact hg.2 w hw
  have step2 : ∀ g, MirS S g → φ g = 0 := by
    intro g hg
    refine h11 E a ψ hψ (a - 1) φ (by omega) hgood {g | MirS S g} ?_ ?_ step1 g hg
    · intro γ hγ g hg
      exact MirrorMap.mirS_mul h10 (MirrorMap.mir_map (algebraMap E (Ad E)) hγ) hg
    · intro k hk y g hg
      exact MirrorMap.mirS_mul h10 ((h10 (Ad E) a (a - 1)).2.2.2.2.2.1 k y hk) hg
  have hEq : (⇑φ) = fun _ => (0 : ℂ) := by
    refine Continuous.ext_on (h12 E a S) φ.continuous continuous_const ?_
    rintro x ⟨γ, g, rfl, hg1, hg2⟩
    show φ (ratGL E a γ * g) = 0
    rw [hleft]
    refine step2 g ⟨?_, fun w hw => ?_⟩
    · rw [hg1]; exact (h10 _ a (a - 1)).2.2.1
    · rw [hg2 w hw]; exact (h10 _ a (a - 1)).2.2.1
  ext x
  simpa using congrFun hEq x

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorOrbit
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

theorem smooth_vector_orbit_invariance : G0 → G5 → G5b → G9 → PlacewiseToOutsideS → G8 := by
  intro hAC hSW hSP hWS hWV
  unfold PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE
  intro E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩ := hAC E a
  obtain ⟨hΛ, htr, -, hW⟩ := hSW E a ψ hψ
  obtain ⟨hsmooth, hsph, hsph_smul, -, -⟩ := hSP E a S
  obtain ⟨-, hYtr, hYmir⟩ := hY
  obtain ⟨hWcont, hWne, -⟩ := hW φ (hYmir φ hφY)
  obtain ⟨g, hg⟩ := hWne hφ0
  obtain ⟨g₀, harch, hloc, hsupp⟩ := hreg S g
  have hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0 := by
    intro h0
    refine hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)
    intro w hw h hh h0' u
    obtain ⟨B, hB⟩ := hφeig w hw
    exact hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u
  have hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y := hYtr g₀ hsupp φ hφY
  have hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0 := by
    rw [htr, one_mul]
    exact hg₀
  refine ⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ •
      PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩
  · exact PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)
  · exact hsph_smul _ _ (hsph g₀ φ hφsph)
  · obtain ⟨Λ, hΛ1⟩ := hΛ 1
    rw [← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul,
      inv_mul_cancel₀ hW1]

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PSmoNorm
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

theorem smonorm_of : Meet → CuspidalIrreducibleSubrep → SmoNorm := by
  intro hM hG E _ _ _ a π π' hπ hπ' hS
  let μ : Measure (GA E a) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨H, hH, hf⟩ := hG E a μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E a μ π' hπ'
  have hne : H ⊓ H' ≠ ⊥ := hM E a μ π π' H H' hπ hπ' hH.1 hH'.1
    (fun φ hφ => ⟨hf.finitePartMemL2 φ hφ, hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ))⟩)
    (fun φ hφ => ⟨hf'.finitePartMemL2 φ hφ, hf'.classes_le (toL2_mem_classes hφ (hf'.finitePartMemL2 φ hφ))⟩) hS
  have h1 : H ⊓ H' = H := (hH.2.2 _ inf_le_left (hH.1.inf hH'.1)).resolve_left hne
  have h2 : H ⊓ H' = H' := (hH'.2.2 _ inf_le_right (hH.1.inf hH'.1)).resolve_left hne
  have e : H = H' := h1.symm.trans h2
  subst e
  exact hf.unique hf'

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ExistsLogarithmLinear
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace ExistsLogarithmLinear

theorem exists_log_lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (χ : AddChar V ℂ) (hχ : Continuous χ)
    (h0 : ∀ z, χ z ≠ 0) : ∃ L : V →L[ℝ] ℂ, ∀ z, χ z = Complex.exp (L z) := by
  let f : C(V, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨χ z, h0 z⟩, hχ.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f]))
  have hF' : ∀ z, Complex.exp (F z) = χ z := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', AddChar.map_add_eq_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (h0 _), div_self (h0 _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

end ExistsLogarithmLinear

theorem exists_logarithm_linear : S8 := by
  intro ι _ χ hχ h1
  obtain ⟨L, hL⟩ := ExistsLogarithmLinear.exists_log_lin χ hχ (fun z h => by simpa [h] using h1 z)
  refine ⟨Complex.imCLM.comp L, fun z => ?_⟩
  have hre : (L z).re = 0 := by
    have := h1 z
    rw [hL z, Complex.norm_exp] at this
    exact Real.exp_eq_one_iff _ |>.1 this
  rw [hL z]
  congr 1
  apply Complex.ext <;> simp [hre]

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.HaarPairing
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace HaarPairing

open scoped FourierTransform RealInnerProductSpace Real SchwartzMap

theorem inv_E {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ w, 𝐞 ⟪w, v⟫ • (∫ z, 𝐞 (-⟪z, w⟫) • g z) = g v := by
  have hI : Integrable (𝓕 g) := by
    let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := 𝓕 (hc.toSchwartzMap hg)
    have e : (𝓕 g) = ⇑G := by
      simp only [G, SchwartzMap.fourier_coe]; rfl
    rw [e]; exact G.integrable
  have h := congrFun (hg.continuous.fourierInv_fourier_eq
    (hg.continuous.integrable_of_hasCompactSupport hc) hI) v
  rw [Real.fourierInv_eq] at h
  simpa only [Real.fourier_eq] using h

theorem haar_E {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {d : ℕ}
    (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d) → ℂ,
      ∫ x, h (e x) ∂μ = ((c : ℝ) : ℂ) * ∫ z, h z := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set c := Measure.addHaarScalarFactor (μ.map e) volume with hc
  have hm : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun h => ?_⟩
  have key : ∫ x, h (e x) ∂μ = ∫ z, h z ∂(μ.map e) :=
    (e.toHomeomorph.measurableEmbedding.integral_map h).symm
  rw [key, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem pair {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ T A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x y, β x y = 2 * π * ⟪T x, A y⟫ := by
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let φ : V → StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := fun y =>
    (2 * π)⁻¹ • (β.flip y).comp (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)
  have φadd : ∀ y y', φ (y + y') = φ y + φ y' := by
    intro y y'; simp only [φ, map_add (f := _), ContinuousLinearMap.add_comp, smul_add]
  have φsmul : ∀ (r : ℝ) y, φ (r • y) = r • φ y := by
    intro r y; simp only [φ, map_smul, ContinuousLinearMap.smul_comp, smul_comm r]
  let L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ _).symm (φ y)
      map_add' := fun y y' => by simp only [φadd, map_add (f := _)]
      map_smul' := fun r y => by
        simp only [φsmul, LinearIsometryEquiv.map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }
  have hL : ∀ x y, ⟪T x, L y⟫ = (2 * π)⁻¹ * β x y := by
    intro x y
    rw [real_inner_comm]
    change ⟪(InnerProductSpace.toDual ℝ _).symm (φ y), T x⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp [φ]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hβ
    intro x
    have h1 := hL x y
    rw [hy, inner_zero_right] at h1
    have hp : (2 * π)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hp
  let A := (L.linearEquivOfInjective hinj finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv
  refine ⟨T, A, fun x y => ?_⟩
  have hA : A y = L y := rfl
  rw [hA, hL]
  field_simp

end HaarPairing

theorem haar_measure_pairing : S5 := by
  intro V _ _ _ _ _ μ _ β hβ
  obtain ⟨T, A, hTA⟩ := HaarPairing.pair β hβ
  obtain ⟨c1, hc1, h1⟩ := HaarPairing.haar_E μ T
  obtain ⟨c2, hc2, h2⟩ := HaarPairing.haar_E μ A
  refine ⟨((c1 : ℝ) : ℂ) * ((c2 : ℝ) : ℂ), mul_ne_zero (by exact_mod_cast hc1) (by exact_mod_cast hc2),
    fun f hf hc ξ => ?_⟩
  set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ := f ∘ T.symm with hg_def
  have hgs : ContDiff ℝ ∞ g := hf.comp T.symm.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph T.symm.toHomeomorph
  have hFT : ∀ y, FT μ β f y = ((c1 : ℝ) : ℂ) *
      ∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z := by
    intro y
    rw [FT, ← h1 (fun z => Real.fourierChar (-inner ℝ z (A y)) • g z)]
    congr 1 with x
    simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul, hTA]
    push_cast
    ring_nf
  have step : ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ =
      ((c1 : ℝ) : ℂ) * ∫ y, Real.fourierChar (inner ℝ (A y) (T ξ)) •
        (∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z) ∂μ := by
    rw [← integral_const_mul]
    congr 1 with y
    simp only [hFT, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA, real_inner_comm (A y)]
    push_cast
    ring_nf
  have h2' := h2 (fun w => Real.fourierChar (inner ℝ w (T ξ)) •
    ∫ z, Real.fourierChar (-inner ℝ z w) • g z)
  rw [step, h2', HaarPairing.inv_E g hgs hgc]
  simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  ring

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorsIntertwiner
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace SmoothVectorsIntertwiner

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def rmulₗ (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun M := Matrix.of.symm (Matrix.of M * B)
  map_add' x y := by
    funext i j k
    simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i j k
    simp [Matrix.mul_apply, Finset.mul_sum]

def lmulₗ (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun M := Matrix.of.symm (B * Matrix.of M)
  map_add' x y := by
    funext i j k
    simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i j k
    simp [Matrix.mul_apply, Finset.mul_sum]

def rmulL (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap (rmulₗ B)

def lmulL (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap (lmulₗ B)

theorem rmulL_apply (B : Matrix (Fin a) (Fin a) (ι → ℂ)) (M : LieI ι a) :
    rmulL B M = Matrix.of.symm (Matrix.of M * B) := rfl

theorem lmulL_apply (B : Matrix (Fin a) (Fin a) (ι → ℂ)) (M : LieI ι a) :
    lmulL B M = Matrix.of.symm (B * Matrix.of M) := rfl

theorem isOpen_U : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := by
  have hc : Continuous fun M : LieI ι a => (Matrix.of M).det :=
    Continuous.matrix_det continuous_id
  have e : {M : LieI ι a | IsUnit (Matrix.of M)} =
      (fun M : LieI ι a => (Matrix.of M).det) ⁻¹' {x | IsUnit x} := by
    ext M
    simp [Matrix.isUnit_iff_isUnit_det]
  rw [e]
  exact Units.isOpen.preimage hc

omit [Fintype ι] in
theorem one_mem_U : oneI ι a ∈ {M : LieI ι a | IsUnit (Matrix.of M)} := by
  change IsUnit (Matrix.of (Matrix.of.symm 1))
  rw [Equiv.apply_symm_apply]
  exact isUnit_one

theorem orb_rmul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (g : GL (Fin a) (ι → ℂ)) (v : X)
    (M : LieI ι a) : orb ρ (ρ g v) M = orb ρ v (rmulL g.val M) := by
  rw [rmulL_apply]
  unfold orb
  have hiff : IsUnit (Matrix.of (Matrix.of.symm (Matrix.of M * g.val))) ↔ IsUnit (Matrix.of M) := by
    rw [Equiv.apply_symm_apply]
    exact Units.isUnit_mul_units _ g
  by_cases hM : IsUnit (Matrix.of M)
  · rw [dif_pos hM, dif_pos (hiff.mpr hM), ← ContinuousLinearMap.mul_apply, ← map_mul]
    congr 2
    ext1
    simp only [IsUnit.unit_spec, Units.val_mul, Equiv.apply_symm_apply]
  · rw [dite_eq_right hM, dite_eq_right (mt hiff.mp hM)]

theorem orb_lmul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (M : LieI ι a)
    (hM : IsUnit (Matrix.of M)) (N : LieI ι a) :
    orb ρ v (lmulL (Matrix.of M) N) = ρ hM.unit (orb ρ v N) := by
  rw [lmulL_apply]
  unfold orb
  have hiff : IsUnit (Matrix.of (Matrix.of.symm (Matrix.of M * Matrix.of N))) ↔
      IsUnit (Matrix.of N) := by
    rw [Equiv.apply_symm_apply, ← hM.unit_spec]
    exact Units.isUnit_units_mul _ _
  by_cases hN : IsUnit (Matrix.of N)
  · rw [dif_pos hN, dif_pos (hiff.mpr hN), ← ContinuousLinearMap.mul_apply, ← map_mul ρ]
    congr 2
    ext1
    simp only [IsUnit.unit_spec, Units.val_mul, Equiv.apply_symm_apply]
  · rw [dite_eq_right hN, dite_eq_right (mt hiff.mp hN), map_zero]

omit [Fintype ι] in
theorem orbit_map_intertwiner_comm (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (T : X →L[ℂ] X)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (v : X) :
    orb ρ (T v) = fun M => T (orb ρ v M) := by
  funext M
  unfold orb
  split_ifs with h
  · exact (hT _ _).symm
  · exact (map_zero T).symm

theorem smooth_vector_intertwiner_apply (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (T : X →L[ℂ] X)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (v : X) (hv : SmV ρ v) : SmV ρ (T v) := by
  unfold SmV at *
  rw [orbit_map_intertwiner_comm ρ T hT v]
  exact (T.restrictScalars ℝ).contDiff.comp_contDiffOn hv

end SmoothVectorsIntertwiner

open SmoothVectorsIntertwiner in
theorem smooth_vectors_stable_intertwiner : S2 := by
  intro ι _ a X _ _ _ ρ _
  have hU : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := isOpen_U
  have orb_zero : orb ρ (0 : X) = fun _ => 0 := by
    funext M
    unfold orb
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SmV
    rw [orb_zero]
    exact contDiffOn_const
  · intro v w hv hw
    have e : orb ρ (v + w) = fun M => orb ρ v M + orb ρ w M := by
      funext M
      unfold orb
      split_ifs <;> simp
    unfold SmV at *
    rw [e]
    exact hv.add hw
  · intro c v hv
    have h := smooth_vector_intertwiner_apply ρ (c • ContinuousLinearMap.id ℂ X) (fun g x => by simp) v hv
    simpa using h
  · intro g v hv
    unfold SmV at *
    rw [show orb ρ (ρ g v) = fun M => orb ρ v (rmulL g.val M) from
      funext fun M => orb_rmul ρ g v M]
    refine hv.comp (rmulL g.val).contDiff.contDiffOn ?_
    intro M hM
    simp only [Set.mem_setOf_eq, rmulL_apply, Equiv.apply_symm_apply] at hM ⊢
    exact (Units.isUnit_mul_units _ g).mpr hM
  · exact fun T hT v hv => smooth_vector_intertwiner_apply ρ T hT v hv
  · intro v hv
    have hd : ∀ N ∈ {M : LieI ι a | IsUnit (Matrix.of M)}, DifferentiableAt ℝ (orb ρ v) N :=
      fun N hN => (hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hN)
    refine ⟨fderiv ℝ (orb ρ v) (oneI ι a), (hd _ one_mem_U).hasFDerivAt, fun Z => ?_⟩
    have key : ∀ N (hN : IsUnit (Matrix.of N)),
        ρ hN.unit (fderiv ℝ (orb ρ v) (oneI ι a) Z) =
          fderiv ℝ (orb ρ v) N (rmulL (Matrix.of Z) N) := by
      intro N hN
      have hL : lmulL (Matrix.of N) (oneI ι a) = N := by
        rw [lmulL_apply, oneI, Equiv.apply_symm_apply, mul_one, Equiv.symm_apply_apply]
      have h0 : HasFDerivAt (orb ρ v) (fderiv ℝ (orb ρ v) N) (lmulL (Matrix.of N) (oneI ι a)) := by
        rw [hL]
        exact (hd N hN).hasFDerivAt
      have h1 : HasFDerivAt (fun M => orb ρ v (lmulL (Matrix.of N) M))
          ((fderiv ℝ (orb ρ v) N).comp (lmulL (Matrix.of N))) (oneI ι a) :=
        h0.comp (oneI ι a) (lmulL (Matrix.of N)).hasFDerivAt
      have h2 : HasFDerivAt (fun M => ρ hN.unit (orb ρ v M))
          (((ρ hN.unit).restrictScalars ℝ).comp (fderiv ℝ (orb ρ v) (oneI ι a))) (oneI ι a) :=
        ((ρ hN.unit).restrictScalars ℝ).hasFDerivAt.comp (oneI ι a) (hd _ one_mem_U).hasFDerivAt
      have e : (fun M => orb ρ v (lmulL (Matrix.of N) M)) = fun M => ρ hN.unit (orb ρ v M) :=
        funext fun M => orb_lmul ρ v N hN M
      rw [e] at h1
      have h3 := congrArg (fun D => D Z) (h2.unique h1)
      simpa [lmulL_apply, rmulL_apply] using h3
    unfold SmV
    have hc : ContDiffOn ℝ ∞ (fun N => fderiv ℝ (orb ρ v) N (rmulL (Matrix.of Z) N))
        {M : LieI ι a | IsUnit (Matrix.of M)} :=
      (hv.fderiv_of_isOpen hU (by simp)).clm_apply (rmulL (Matrix.of Z)).contDiff.contDiffOn
    refine hc.congr fun N hN => ?_
    have hw : ∀ w : X, orb ρ w N = ρ (show IsUnit (Matrix.of N) from hN).unit w := by
      intro w
      unfold orb
      exact dif_pos hN
    rw [hw]
    exact key N hN

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FourierIntegralBound
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace FourierIntegralBound

open Real

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) :=
  _root_.UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main t ht N

lemma pi_pow_le {d : ℕ} (z : Fin d → ℝ) (N : ℕ) : ‖z‖ ^ N ≤ 1 + ∑ i, |z i| ^ N := by
  have hs : 0 ≤ ∑ i, |z i| ^ N := Finset.sum_nonneg (fun i _ => by positivity)
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · have : ‖z‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => isEmptyElim i)
    have h0 : ‖z‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) this
    linarith
  · obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |z i|) Finset.univ_nonempty
    have h1 : ‖z‖ ≤ |z i0| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun i => by
      rw [Real.norm_eq_abs]; exact hi0 i (Finset.mem_univ _))
    have h2 : ‖z‖ ^ N ≤ |z i0| ^ N := pow_le_pow_left₀ (norm_nonneg _) h1 N
    have h3 : |z i0| ^ N ≤ ∑ i, |z i| ^ N :=
      Finset.single_le_sum (f := fun i => |z i| ^ N) (fun i _ => by positivity) (Finset.mem_univ i0)
    linarith

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sc (β : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ := (2 * π)⁻¹ • β

lemma sc_apply (β : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) : sc β x y = (2 * π)⁻¹ * β x y := by
  simp [sc]

lemma FT_eq [MeasurableSpace V] {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (μ : Measure V) (β : V →L[ℝ] V →L[ℝ] ℝ) (F : V → X) :
    FT μ β F = VectorFourier.fourierIntegral Real.fourierChar μ (sc β).toLinearMap₁₂ F := by
  ext y
  unfold FT VectorFourier.fourierIntegral
  congr 1
  ext x
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  rw [show (sc β).toLinearMap₁₂ x y = sc β x y from rfl, sc_apply]
  push_cast
  field_simp

lemma exists_strictHenselian_absolutely_closed_local_ring [FiniteDimensional ℝ V] (β : V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ (d : ℕ) (b : Fin d → V) (K : ℝ), 0 ≤ K ∧
      ∀ y, ‖y‖ ≤ K * ‖(fun i => β (b i) y : Fin d → ℝ)‖ := by
  let b := Module.finBasis ℝ V
  let T : V →ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearMap.pi (fun i => ((β (b i) : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ))
  have hT : ∀ y, T y = fun i => β (b i) y := fun y => rfl
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply hβ y
    have h1 : ∀ i, β (b i) y = 0 := fun i => by
      have := congrFun hy i
      rw [hT] at this
      simpa using this
    have h2 : ((β.flip y : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) = 0 :=
      b.ext (fun i => by simpa using h1 i)
    intro x
    have := LinearMap.congr_fun h2 x
    simpa using this
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hker
  refine ⟨_, b, K, K.2, fun y => ?_⟩
  have := hK.le_mul_dist y 0
  rw [map_zero, dist_zero_right, dist_zero_right] at this
  exact this

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [FiniteDimensional ℝ V] in
lemma integ {F : V → X} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (μ : Measure V)
    [IsFiniteMeasureOnCompacts μ] (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow k).mul (hF.continuous_iteratedFDeriv (mod_cast le_top)).norm
  · exact (hc.iteratedFDeriv n).norm.mul_left

lemma pw_bd (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →L[ℝ] V →L[ℝ] ℝ) {F : V → X}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (n : ℕ) :
    ∃ B : ℝ, ∀ v y, |β v y| ^ n * ‖FT μ β F y‖ ≤ ‖v‖ ^ n * B := by
  refine ⟨(2 * π) ^ n * ((2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
      ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ), fun v y => ?_⟩
  have H := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (L := sc β) (μ := μ)
    (K := ⊤) (N := ⊤) hF (fun k n _ _ => integ hF hc μ k n) (k := 0) (n := n) le_top le_top v y
  rw [norm_iteratedFDeriv_zero, ← FT_eq] at H
  have e : |β v y| = 2 * π * |sc β v y| := by
    rw [sc_apply, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
    field_simp
  rw [e, mul_pow, mul_assoc]
  calc (2 * π) ^ n * (|sc β v y| ^ n * ‖FT μ β F y‖)
      ≤ (2 * π) ^ n * (‖v‖ ^ n * (2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
          ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
            ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ) := by gcongr
    _ = _ := by ring

end FourierIntegralBound

open FourierIntegralBound in
theorem valuation_bound_of_three : S4 := by
  unfold S4 ForV
  intro V _ _ _ _ _ μ _ β hβ X _ _ _ F hF hc
  refine ⟨?_, fun N => ?_⟩
  · rw [FT_eq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by apply (sc β).continuous₂) (hF.continuous.integrable_of_hasCompactSupport hc)
  · obtain ⟨d, b, K, hK0, hK⟩ := exists_strictHenselian_absolutely_closed_local_ring β hβ
    obtain ⟨A, hA⟩ := pw_bd μ β hF hc 0
    obtain ⟨B, hB⟩ := pw_bd μ β hF hc N
    refine ⟨2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)), fun y => ?_⟩
    have hA' : ‖FT μ β F y‖ ≤ A := by simpa using hA 0 y
    have hy := pi_pow_le (fun i => β (b i) y) N
    have h1 : ‖y‖ ^ N ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) := by
      calc ‖y‖ ^ N ≤ (K * ‖(fun i => β (b i) y : Fin d → ℝ)‖) ^ N :=
            pow_le_pow_left₀ (norm_nonneg _) (hK y) N
        _ = K ^ N * ‖(fun i => β (b i) y : Fin d → ℝ)‖ ^ N := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have h3 : (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ ≤ A + ∑ i, ‖b i‖ ^ N * B := by
      rw [add_mul, Finset.sum_mul, one_mul]
      exact add_le_add hA' (Finset.sum_le_sum fun i _ => hB (b i) y)
    have hFn := norm_nonneg (FT μ β F y)
    calc (1 + ‖y‖) ^ N * ‖FT μ β F y‖ ≤ 2 ^ N * (1 + ‖y‖ ^ N) * ‖FT μ β F y‖ := by
          gcongr; exact one_add_pow_le _ (norm_nonneg _) N
      _ = 2 ^ N * (‖FT μ β F y‖ + ‖y‖ ^ N * ‖FT μ β F y‖) := by ring
      _ ≤ 2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hA' ?_) (by positivity)
          calc ‖y‖ ^ N * ‖FT μ β F y‖
              ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ := by gcongr
            _ = K ^ N * ((1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖) := by ring
            _ ≤ _ := by gcongr

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PositiveMatrixBlocks
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace PositiveMatrixBlocks

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem posM_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_posM_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem posM_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := posM_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, posM_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blk (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_posM_apply, posM_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

end PositiveMatrixBlocks

theorem positive_matrix_block_product : MirabolicColumnBlock := by
  intro R _ a m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    refine ⟨fun t => γ.val t.1.1 t.1.2, blkU (-(fun t : UnipotentBlockColumnIndex a m m => γ.val t.1.1 t.1.2)) * γ, ?_, ?_⟩
    · intro i k hik
      show ((1 + posM Subtype.val (-(fun t : UnipotentBlockColumnIndex a m m => γ.val t.1.1 t.1.2))) * γ.val) i k = _
      rw [add_mul, one_mul, PositiveMatrixBlocks.posM_mul_row m _ γ.val (fun j k hj => hγ j k (Or.inl hj.ge)),
        Matrix.add_apply, PositiveMatrixBlocks.posM_col]
      split_ifs with hc
      · rcases hik with hi | _
        · omega
        · rw [Matrix.one_apply_ne (fun e => by rw [e] at hc; omega)]
          simp
      · rw [add_zero]
        exact hγ i k (by omega)
    · show γ = blkU _ * (blkU _ * γ)
      rw [← mul_assoc]
      unfold blkU
      rw [← posU_add, add_neg_cancel, posU_zero, one_mul]
  · intro γ hγ
    apply Units.ext
    ext i k
    exact hγ i k (Or.inl (Nat.zero_le _))
  · intro i k _
    rfl
  · intro i k _
    rfl
  · intro γ γ' hγ hγ' i k hik
    show (γ.val * γ'.val) i k = _
    rw [Matrix.mul_apply]
    rcases hik with hi | hk
    · calc ∑ j, γ.val i j * γ'.val j k = ∑ j, (1 : Matrix (Fin a) (Fin a) R) i j * γ'.val j k :=
            Finset.sum_congr rfl fun j _ => by rw [hγ i j (Or.inl hi)]
        _ = ((1 : Matrix (Fin a) (Fin a) R) * γ'.val) i k := Matrix.mul_apply.symm
        _ = _ := by rw [Matrix.one_mul]; exact hγ' i k (Or.inl hi)
    · calc ∑ j, γ.val i j * γ'.val j k = ∑ j, γ.val i j * (1 : Matrix (Fin a) (Fin a) R) j k :=
            Finset.sum_congr rfl fun j _ => by rw [hγ' j k (Or.inr hk)]
        _ = (γ.val * (1 : Matrix (Fin a) (Fin a) R)) i k := Matrix.mul_apply.symm
        _ = _ := by rw [Matrix.mul_one]; exact hγ i k (Or.inr hk)
  · intro k y hkm i l hil
    show (1 + posM Subtype.val y) i l = _
    rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
    intro t _
    rw [Matrix.single_apply, if_neg]
    rintro ⟨e1, e2⟩
    have := t.2
    rw [← e1, ← e2] at hil
    omega
  · intro k γ hkm hγ i l hil
    exact hγ i l (by omega)
  · intro h hB y
    refine ⟨fun t => ∑ s, h.val t.1.1 s.1.1 * y s, ?_, fun t => rfl⟩
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      PositiveMatrixBlocks.posM_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), PositiveMatrixBlocks.mul_posM_blk m y h hB]

end PositivityTheory.jumpWindows

end
end

namespace PositivityTheory.jumpWindows

theorem compositionalInverseSymm : S1 :=
  lie_algebra_action_exists

theorem orthogonalSplitPolarizationVanishes : S2 :=
  smooth_vectors_stable_intertwiner

theorem addPreservesExpCongruence : S3 :=
  unit_chart_operator_bound compositionalInverseSymm

theorem expCongruenceExtendsToSum : S4 :=
  valuation_bound_of_three

theorem hit_valuation_bound : S5 :=
  haar_measure_pairing

theorem smooth_vectors_conjugation_holds : S6 :=
  conjugation_units_open orthogonalSplitPolarizationVanishes expCongruenceExtendsToSum

theorem exists_logarithm_linear_holds : S8 :=
  exists_logarithm_linear

theorem positive_matrix_block_product_holds : MirabolicColumnBlock :=
  positive_matrix_block_product

theorem mirabolic_induction_step_holds : S7 :=
  mirabolic_induction_step_exists orthogonalSplitPolarizationVanishes addPreservesExpCongruence hit_valuation_bound smooth_vectors_conjugation_holds exists_logarithm_linear_holds positive_matrix_block_product_holds

theorem lattice_open_last_entry_holds : S9 :=
  lattice_open_last_entry positive_matrix_block_product_holds

theorem automorphic_basic_setup_holds : G0 :=
  standard_stabiliser_bound

theorem multiplicity_one_holds : G1 :=
  firstGeometricCondition_of_properties compositionalInverseSymm

theorem almost_everywhere_spherical : AlmostEverywhereSpherical :=
  almost_everywhere_spherical_of_G1 multiplicity_one_holds

theorem averaging_projection_linear_holds : G2a :=
  averaging_projection_linear

theorem bounded_invariant_L2_holds : G2b :=
  bounded_invariant_functions_in_L2

theorem hecke_operator_automorphic_holds : G2c :=
  hecke_operator_of_automorphic automorphic_basic_setup_holds

theorem whittaker_functional_exists_holds : G5 :=
  local_group_averaging_tensor

theorem smooth_vectors_regular_holds : G5b :=
  smooth_vectors_regular_representation orthogonalSplitPolarizationVanishes automorphic_basic_setup_holds

theorem whittaker_nondegenerate_holds : G6 :=
  whittaker_nondegenerate_character mirabolic_induction_step_holds positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds

theorem whittaker_expansion_cuspidal_holds : G7 :=
  whittaker_expansion_cuspidal orthogonalSplitPolarizationVanishes lattice_open_last_entry_holds positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds smooth_vectors_regular_holds

theorem whittaker_factorization_places_holds : FourierInductionSteps :=
  whittaker_factorization_places whittaker_nondegenerate_holds whittaker_expansion_cuspidal_holds

theorem whittaker_uniqueness_local_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : G9 :=
  whittaker_uniqueness_local h7 h12 automorphic_basic_setup_holds whittaker_functional_exists_holds

theorem convergence_entries_general_linear_holds : PlacewiseToOutsideS :=
  convergence_entries_general_linear automorphic_basic_setup_holds

theorem smooth_vector_orbit_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : G8 :=
  smooth_vector_orbit_invariance automorphic_basic_setup_holds whittaker_functional_exists_holds smooth_vectors_regular_holds (whittaker_uniqueness_local_holds h7 h12) convergence_entries_general_linear_holds

theorem adelic_character_condition_holds : StandardCharacterExists :=
  adelic_character_holds

theorem local_uniqueness_auxiliary_holds : FourierUniquenessMirabolic :=
  induction_g11_holds

theorem good_inverse_dense_range_holds : WeakApproximationGL :=
  good_inverse_of_G0 automorphic_basic_setup_holds

theorem whittaker_support_theorem_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : WhittakerVanishingImpliesZero :=
  mirror_global_of positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds (whittaker_uniqueness_local_holds h7 h12) convergence_entries_general_linear_holds local_uniqueness_auxiliary_holds good_inverse_dense_range_holds

theorem finite_part_meets_conditions (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : Meet :=
  meet_of orthogonalSplitPolarizationVanishes positive_matrix_block_product_holds automorphic_basic_setup_holds multiplicity_one_holds almost_everywhere_spherical averaging_projection_linear_holds bounded_invariant_L2_holds hecke_operator_automorphic_holds whittaker_functional_exists_holds smooth_vectors_regular_holds whittaker_factorization_places_holds (smooth_vector_orbit_holds h7 h12) adelic_character_condition_holds (whittaker_support_theorem_holds h7 h12)

theorem finite_part_of_meet_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : CuspidalIrreducibleSubrep :=
  finite_part_of_meet (finite_part_meets_conditions h7 h12)

theorem smooth_multiplicity_normalized (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : SmoNorm :=
  smonorm_of (finite_part_meets_conditions h7 h12) (finite_part_of_meet_holds h7 h12)

theorem finite_infinite_product_one_holds : HeckeCharacterRigidity :=
  finite_infinite_product_eq_one

theorem smooth_multiplicity_one_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : Smo :=
  smo_of (smooth_multiplicity_normalized h7 h12) finite_infinite_product_one_holds

theorem cuspidal_multiplicity_one (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : GlobalTheory.Published.CuspidalMultiplicityOne :=
  mean_convergence_of (smooth_multiplicity_one_holds h7 h12)

end PositivityTheory.jumpWindows

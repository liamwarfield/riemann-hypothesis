module

public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreGlobPf
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
noncomputable section

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

section Line

variable {L : Type} [Field L] [NumberField L]

def lineHerm (n : (L →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s) : HermFam L L where
  form s x y := n s * (starRingEnd ℂ (s x) * s y)
  add_right s x y z := by simp [mul_add]
  smul_right s a x y := by simp [mul_left_comm]
  conj_symm s x y := by simp [mul_comm]
  posDef s m v hv := by
    have hli : LinearIndependent L fun i (_ : Fin 1) => v i :=
      hv.map' (LinearEquiv.funUnique (Fin 1) L L).symm.toLinearMap (LinearEquiv.ker _)
    have h := (standardHermitian_gram_posDef L s _ hli).smul (a := (n s : ℂ)) (by exact_mod_cast hn s)
    convert h using 1
    ext i j
    simp

theorem deg_lineHerm (n : (L →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s) {𝔠 : FractionalIdeal (𝓞 L)⁰ L} (h𝔠 : 𝔠 ≠ 0) :
    deg (lineHerm n hn) (𝔠 : Submodule (𝓞 L) L) =
      -Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ L - meanLog L n / 2 := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ 𝔠, a ≠ 0 := by
    simpa [FractionalIdeal.eq_zero_iff] using h𝔠
  have hf : IsFrame L (𝔠 : Submodule (𝓞 L) L) (fun _ : Fin 1 => a) :=
    ⟨fun _ => ha, linearIndependent_unique_iff.mpr ha0, fun x _ => by
      rw [Set.range_const, SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨x / a, div_mul_cancel₀ x ha0⟩⟩
  let 𝔟 := FractionalIdeal.spanSingleton (𝓞 L)⁰ a⁻¹ * 𝔠
  have hm : ∀ x, x ∈ 𝔟 ↔ a * x ∈ 𝔠 := fun x => by
    rw [FractionalIdeal.mem_singleton_mul]
    exact ⟨fun ⟨y, hy, e⟩ => by rwa [e, mul_inv_cancel_left₀ ha0], fun h => ⟨_, h, by field_simp⟩⟩
  have h1 := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one (𝔟 : Submodule (𝓞 L) L)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟) (Submodule.one_le.2 ((hm 1).2 (by simpa using ha)))
  have e1 : (1 : Submodule (𝓞 L) L).toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      (Submodule.span (𝓞 L) (Set.range fun _ : Fin 1 => a)).toAddSubgroup := by
    ext x
    simp [Submodule.mem_span_singleton, Algebra.smul_def, mul_comm]
  have e2 : (𝔟 : Submodule (𝓞 L) L).toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      (𝔠 : Submodule (𝓞 L) L).toAddSubgroup := by
    ext x
    refine ⟨?_, fun h => ⟨a⁻¹ * x, (hm _).2 (by rwa [mul_inv_cancel_left₀ ha0]), mul_inv_cancel_left₀ ha0 x⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact (hm y).1 hy
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft a) _ _ (mul_right_injective₀ ha0),
    e1, e2] at h1
  change FractionalIdeal.absNorm 𝔟 * _ = 1 at h1
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, Algebra.norm_inv, abs_inv] at h1
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha0
  have hc : FractionalIdeal.absNorm 𝔠 ≠ 0 := (map_ne_zero _).2 h𝔠
  have h2 := (eq_inv_of_mul_eq_one_right h1)
  have h3 := congrArg (fun q : ℚ => Real.log (q : ℝ)) h2
  simp only [Rat.cast_natCast, mul_inv, inv_inv, Rat.cast_mul, Rat.cast_inv, Rat.cast_abs] at h3
  rw [Real.log_mul (by simpa using hN) (by simpa using hc), Real.log_inv] at h3
  have h4 : ∀ s, Real.log ((lineHerm n hn).gram s fun _ : Fin 1 => a).det.re =
      Real.log (n s) + Real.log (Complex.normSq (s a)) := fun s => by
    rw [← Real.log_mul (hn s).ne' (by simpa using ha0), Matrix.det_fin_one]
    congr 1
    simp [HermFam.gram, lineHerm, Complex.normSq_apply]
  rw [arakelovDegree_eq_degreeOfFamily _ (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔠) hf, degreeOfFamily, h3, meanLog]
  simp only [h4, Finset.sum_add_distrib, ds_sum_log_normSq_embeddings a ha0]
  ring

end Line

section Norm

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

theorem absNorm_extendedHom [Algebra E L] (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) 𝔞) = FractionalIdeal.absNorm 𝔞 ^ finrank E L := by
  have key : ∀ I : Ideal (𝓞 E), FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L)
      (I : FractionalIdeal (𝓞 E)⁰ E)) = FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 E)⁰ E) ^ finrank E L :=
    fun I => by
      rw [FractionalIdeal.extendedHom_coeIdeal_eq_map, FractionalIdeal.coeIdeal_absNorm,
        FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap,
        ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L, Nat.cast_pow]
  have h := 𝔞.den_mul_self_eq_num'
  rw [← FractionalIdeal.coeIdeal_span_singleton] at h
  have h0 : FractionalIdeal.absNorm ((Ideal.span {(𝔞.den : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    simp
  have h1 := key 𝔞.num
  rw [← h, map_mul, map_mul, map_mul, key, mul_pow] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ h0) h1

theorem exists_fractionalIdeal_eq_span_image (τ : E →+* L) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) :
    ∃ 𝔠 : FractionalIdeal (𝓞 L)⁰ L, 𝔠 ≠ 0 ∧ (𝔠 : Submodule (𝓞 L) L) = Submodule.span (𝓞 L) (τ '' 𝔞) ∧
      Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ L = Real.log (FractionalIdeal.absNorm 𝔞) / finrank ℚ E := by
  let _ := τ.toAlgebra
  refine ⟨FractionalIdeal.extendedHom L (𝓞 L) 𝔞, by rwa [Ne, FractionalIdeal.extendedHom_eq_zero_iff],
    FractionalIdeal.coe_extendedHom_eq_span L (𝓞 L) 𝔞, ?_⟩
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  rw [absNorm_extendedHom, Rat.cast_pow, Real.log_pow, ← finrank_mul_finrank ℚ E L, Nat.cast_mul]
  field_simp

theorem meanLog_comp (j : E →+* L) (n : (E →+* ℂ) → ℝ) : meanLog L (fun s => n (s.comp j)) = meanLog E n := by
  let _ := j.toAlgebra
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have h := ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict (K₁ := L) fun s => Real.log (n s)
  rw [meanLog, meanLog, ← finrank_mul_finrank ℚ E L, Nat.cast_mul, div_eq_iff (by positivity)]
  refine h.trans ?_
  field_simp

theorem log_absNorm_conjFrac [IsCMField E] {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) :
    Real.log (FractionalIdeal.absNorm (conjFrac 𝔞)) = Real.log (FractionalIdeal.absNorm 𝔞) := by
  obtain ⟨𝔠, -, h1, h2⟩ := exists_fractionalIdeal_eq_span_image
    ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E) h𝔞
  have h3 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have e : ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E) '' 𝔞 =
      ((conjFrac 𝔞 : Submodule (𝓞 E) E) : Set E) := by
    ext x
    refine ⟨?_, fun h => ⟨_, mem_conjFrac.1 h, IsCMField.complexConj_apply_apply E x⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact cc_mem_conjFrac.2 hy
  rw [e, Submodule.span_eq, FractionalIdeal.coeToSubmodule_inj] at h1
  rwa [h1, div_left_inj' h3.ne'] at h2

theorem log_rootDiscr_tower [Algebra E L] : Real.log (rootDiscr L) =
    Real.log (Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L))) / finrank ℚ L + Real.log (rootDiscr E) := by
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) L (𝓞 L)
  have h3 : Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L)) ≠ 0 := fun h0 => by
    simp [h0, discr_ne_zero] at h
  have h4 := congrArg (fun m : ℕ => Real.log (m : ℝ)) h
  have p : ∀ m : ℤ, m ≠ 0 → (0 : ℝ) < (|m| : ℤ) := fun m hm => by exact_mod_cast abs_pos.2 hm
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs] at h4
  rw [Real.log_mul (by exact_mod_cast h3) (pow_ne_zero _ (p _ (discr_ne_zero E)).ne'), Real.log_pow] at h4
  rw [rootDiscr_def, rootDiscr_def, Real.log_rpow (p _ (discr_ne_zero L)), Real.log_rpow (p _ (discr_ne_zero E)), h4,
    ← finrank_mul_finrank ℚ E L, Nat.cast_mul]
  field_simp

end Norm

section Different

variable {K E M L : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E]
  [Field M] [NumberField M] [Field L] [NumberField L]

theorem two_mul_deg_lineHerm_different {𝔄 : FractionalIdeal (𝓞 E)⁰ E}
    (h𝔄 : 𝔄 * conjFrac 𝔄 = (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹)
    (n : (M →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s) (j : M →+* L) (τ : E →+* L) :
    2 * deg (lineHerm (fun s => n (s.comp j)) fun _ => hn _)
        (Submodule.span (𝓞 L) (τ '' (𝔄 * differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) =
      -meanLog M n + Real.log (rootDiscr K) - Real.log (rootDiscr E) := by
  have h0 : (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
  have h1 : 𝔄 ≠ 0 := left_ne_zero_of_mul (h𝔄 ▸ inv_ne_zero h0)
  have nz : ∀ {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 → (FractionalIdeal.absNorm 𝔞 : ℝ) ≠ 0 := fun h => by
    simpa using h
  obtain ⟨𝔠, h𝔠, e, h2⟩ := exists_fractionalIdeal_eq_span_image τ (mul_ne_zero h1 h0)
  have h3 := congrArg (fun 𝔞 => Real.log (FractionalIdeal.absNorm 𝔞 : ℚ)) h𝔄
  simp only [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, Real.log_inv] at h3
  rw [Real.log_mul (nz h1) (nz (conjFrac_ne_zero h1)), log_absNorm_conjFrac h1] at h3
  rw [map_mul, Rat.cast_mul, Real.log_mul (nz h1) (nz h0)] at h2
  rw [← e, deg_lineHerm _ _ h𝔠, meanLog_comp, neg_div, h2, log_rootDiscr_tower (E := K) (L := E)]
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h3 ⊢
  linear_combination -h3 / (finrank ℚ E : ℝ)

end Different

section Period

open AlgebraicGeometry CategoryTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

variable {d : ℕ} [NeZero d] {K : Type} [Field K] [NumberField K]

omit [NeZero d] in
theorem rootDiscr_eq_sqrt (h2 : finrank ℚ K = 2) (hD : discr K = -d) : rootDiscr K = √d := by
  rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
  simp

theorem chowla_selberg_of_mean_log (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) {M : Type} [Field M] [NumberField M]
    (n : (M →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s)
    (h : ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
      (∑ s, Real.log (n s)) / finrank ℚ M =
        (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K) :
    ((-meanLog M n : ℝ) : ℂ) =
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (𝔄 : FractionalIdeal (𝓞 E)⁰ E),
      𝔄 * conjFrac 𝔄 = (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ →
      ∀ (L : Type) [Field L] [NumberField L] (j : M →+* L) (τ : E →+* L),
      ((2 * deg (lineHerm (fun s => n (s.comp j)) fun _ => hn _)
          (Submodule.span (𝓞 L) (τ '' (𝔄 * differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) : ℝ) : ℂ) =
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  choose τ hτ using exists_isIdealClassPoint h2 hD σ
  have h1 := chowla_selberg_eta h2 hD hd hχ σ hτ
  have h3 := h σ τ hτ
  rw [Finset.sum_neg_distrib, neg_div, ← neg_eq_iff_eq_neg] at h3
  rw [← h3] at h1
  refine ⟨h1, fun E _ _ _ _ 𝔄 h𝔄 L _ _ j τ => ?_⟩
  have h4 : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have h5 : 0 < rootDiscr E := by
    rw [rootDiscr_def]
    exact Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero E)) _
  rw [two_mul_deg_lineHerm_different h𝔄 n hn, Complex.ofReal_sub, Complex.ofReal_add, meanLog, h1,
    rootDiscr_eq_sqrt h2 hD, Real.log_div (by positivity) h4.ne', Real.log_div (by positivity) h5.ne']
  push_cast
  ring

theorem chowla_selberg_lie_lines (hC : CMCurve) (h7 : 7 ≤ d) (hs : Squarefree d) (h4 : d % 4 = 3)
    (h2 : finrank ℚ K = 2) (hr : ∃ r : K, r ^ 2 = -(d : K)) {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A),
      (w : ℂ) = (1 + Complex.I * √d) / 2 ∧ P.g = 1 ∧ IsLieBasis ![v] ∧
      (∃ (P₀ : Out.PolAV (Sp M)) (φ : P₀.A.left ⟶ P.A.left) (v₀ : epsR M ⟶ P₀.A) (W : P₀.A ⟶ P₀.A),
        IsPolFibre (algebraMap (𝓞 M) M) P P₀ φ ∧ IsVecOver (algebraMap (𝓞 M) M) φ v v₀ ∧ IsLieBasis ![v₀] ∧
        IsMonHom W ∧ (W ≫ W) * (𝟙 P₀.A) ^ ((1 + d) / 4) = W ∧ IsLieComb ![w] ![v₀] (v₀ ≫ W)) ∧
      (∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left),
        IsPolFibre ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) P P' φ → ∀ u : HolUnif P'.A P'.L P'.g,
        ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * (w : ℂ))) ∧
      ∃ (n : (M →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s),
        (∀ s r, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
        ((-meanLog M n : ℝ) : ℂ) =
          (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 ∧
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (𝔄 : FractionalIdeal (𝓞 E)⁰ E),
          𝔄 * conjFrac 𝔄 = (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ →
          ∀ (L : Type) [Field L] [NumberField L] (j : M →+* L) (τ : E →+* L),
          ((2 * deg (lineHerm (fun s => n (s.comp j)) fun _ => hn _)
              (Submodule.span (𝓞 L) (τ '' (𝔄 * differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) : ℝ) : ℂ) =
            (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) : ℝ)
              - deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain ⟨M, _, w, P, v, hw, hg, hv, hW, hΛ, hn, hm⟩ := hC d h7 hs h4 K h2 hr
  obtain ⟨r, hr⟩ := hr
  choose n hn0 hn using hn
  exact ⟨M, inferInstance, w, P, v, hw, hg, hv, hW, hΛ, n, hn0, hn,
    chowla_selberg_of_mean_log h2 (discr_eq_neg_of_sq_eq h2 hs h4 hr) (by omega) hχ n hn0
      (hm n fun s => (hn s _).2 rfl)⟩

end Period

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.DedekindExt

variable {X X' Y S : Scheme.{0}}

def Agree (φ : X' ⟶ X) (f : X' ⟶ Y) {W : Scheme.{0}} (i : W ⟶ X) (g : W ⟶ Y) : Prop :=
  ∀ (T : Scheme.{0}) (u : T ⟶ W) (u' : T ⟶ X'), u ≫ i = u' ≫ φ → u ≫ g = u' ≫ f

theorem Agree.comp {φ : X' ⟶ X} {f : X' ⟶ Y} {W W' : Scheme.{0}} {i : W ⟶ X} {g : W ⟶ Y}
    (h : Agree φ f i g) (c : W' ⟶ W) : Agree φ f (c ≫ i) (c ≫ g) := fun T u u' e => by
  rw [← Category.assoc]
  exact h T _ _ (by rw [Category.assoc, e])

theorem Agree.of_dominant {φ : X' ⟶ X} [Flat φ] {f : X' ⟶ Y} (sX : X ⟶ S) (sY : Y ⟶ S) [IsSeparated sY]
    (hf : f ≫ sY = φ ≫ sX) {W W' : Scheme.{0}} {i : W ⟶ X} {g : W ⟶ Y} (hg : g ≫ sY = i ≫ sX)
    (c : W' ⟶ W) [QuasiCompact c] [IsSchemeTheoreticallyDominant c] (h : Agree φ f (c ≫ i) (c ≫ g)) :
    Agree φ f i g := by
  have key : pullback.fst i φ ≫ g = pullback.snd i φ ≫ f := by
    have : IsSchemeTheoreticallyDominant (pullback.snd c (pullback.fst i φ)) :=
      .of_isPullback (IsPullback.of_hasPullback c (pullback.fst i φ))
    refine ExtUnique.hom_ext_of_dominant sY ?_ (pullback.snd c (pullback.fst i φ)) ?_
    · rw [Category.assoc, Category.assoc, hg, hf, pullback.condition_assoc]
    · rw [← pullback.condition_assoc, ← Category.assoc (pullback.snd _ _)]
      refine h _ _ _ ?_
      rw [pullback.condition_assoc, Category.assoc, pullback.condition]
  intro T u u' e
  rw [← pullback.lift_fst u u' e, Category.assoc, key, pullback.lift_snd_assoc]

theorem exists_open_agree [IsLocallyNoetherian X] {φ : X' ⟶ X} [Flat φ] {f : X' ⟶ Y} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsSeparated sY] [LocallyOfFiniteType sY] (hf : f ≫ sY = φ ≫ sX) (x : X)
    (g : Spec (X.presheaf.stalk x) ⟶ Y) (hg : g ≫ sY = X.fromSpecStalk x ≫ sX)
    (h : Agree φ f (X.fromSpecStalk x) g) :
    ∃ (W : Scheme.{0}) (i : W ⟶ X) (_ : IsOpenImmersion i) (g' : W ⟶ Y),
      x ∈ Set.range i ∧ g' ≫ sY = i ≫ sX ∧ Agree φ f i g' := by
  obtain ⟨U, hxU, g₁, h₁, h₂⟩ := spread_out_of_isGermInjective' sX sY g hg
  obtain ⟨V, hxV, hV, hVU, hinj⟩ := X.exists_le_and_germ_injective x U hxU
  have hr : Set.range hV.fromSpec ⊆ Set.range U.ι := by
    rw [hV.range_fromSpec, Scheme.Opens.range_ι]; exact hVU
  let l := IsOpenImmersion.lift U.ι hV.fromSpec hr
  have hl : l ≫ U.ι = hV.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have hc : Spec.map (X.presheaf.germ V x hxV) ≫ hV.fromSpec = X.fromSpecStalk x :=
    hV.fromSpecStalk_eq_fromSpecStalk hxV
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hinj
  have hg' : (l ≫ g₁) ≫ sY = hV.fromSpec ≫ sX := by rw [Category.assoc, h₂, ← Category.assoc, hl]
  refine ⟨_, hV.fromSpec, inferInstance, l ≫ g₁, by rw [hV.range_fromSpec]; exact hxV, hg',
    Agree.of_dominant sX sY hf hg' (Spec.map (X.presheaf.germ V x hxV)) ?_⟩
  have e : Spec.map (X.presheaf.germ V x hxV) ≫ l = U.fromSpecStalkOfMem x hxU := by
    rw [← cancel_mono U.ι, Category.assoc, hl, hc, Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [hc, ← Category.assoc, e, ← h₁]
  exact h

theorem exists_of_locally {U : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {φ : X' ⟶ X} {p : X' ⟶ U} {f : X' ⟶ Y} (sX : X ⟶ S) [Flat sX] (sY : Y ⟶ S) [IsSeparated sY]
    (hp : IsPullback φ p sX j)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (i : W ⟶ X) (_ : IsOpenImmersion i) (g' : W ⟶ Y),
      x ∈ Set.range i ∧ g' ≫ sY = i ≫ sX ∧ Agree φ f i g') :
    ∃ F : X ⟶ Y, F ≫ sY = sX ∧ φ ≫ F = f := by
  choose W i hι g hx hg ha using h
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X W i (fun x => ⟨x, hx x⟩)
  have : QuasiCompact φ := MorphismProperty.of_isPullback hp.flip ‹_›
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hp.flip
  have hc : ∀ x y, pullback.fst (i x) (i y) ≫ g x = pullback.snd (i x) (i y) ≫ g y := by
    intro x y
    let q := pullback.fst (i x) (i y) ≫ i x
    have : IsSchemeTheoreticallyDominant (pullback.fst q φ) :=
      .of_isPullback (IsPullback.of_hasPullback q φ).flip
    refine ExtUnique.hom_ext_of_dominant sY ?_ (pullback.fst q φ) ?_
    · rw [Category.assoc, Category.assoc, hg, hg, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine (ha x _ _ (pullback.snd q φ) ?_).trans (ha y _ _ (pullback.snd q φ) ?_).symm
      · rw [Category.assoc]; exact pullback.condition
      · rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  have hF : ∀ x, i x ≫ 𝒰.glueMorphisms g hc = g x := fun x => 𝒰.ι_glueMorphisms g hc x
  refine ⟨𝒰.glueMorphisms g hc, 𝒰.hom_ext _ _ fun x : X => ?_,
    Scheme.Cover.hom_ext (𝒰.pullback₁ φ) _ _ fun x : X => ?_⟩
  · change i x ≫ _ = i x ≫ _
    rw [← Category.assoc, hF, hg]
  · change pullback.fst φ (i x) ≫ _ = pullback.fst φ (i x) ≫ _
    rw [pullback.condition_assoc, hF]
    exact ha x _ _ _ pullback.condition.symm

theorem exists_of_stalks [IsLocallyNoetherian X] {U : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [Flat j]
    [IsSchemeTheoreticallyDominant j]
    {φ : X' ⟶ X} {p : X' ⟶ U} {f : X' ⟶ Y} (sX : X ⟶ S) [Flat sX] (sY : Y ⟶ S) [IsSeparated sY]
    [LocallyOfFiniteType sY] (hp : IsPullback φ p sX j) (hf : f ≫ sY = φ ≫ sX)
    (h : ∀ s : S, ∃ (T : Scheme.{0}) (t : T ⟶ S) (a : Spec (S.presheaf.stalk s) ⟶ T) (g : pullback sX t ⟶ Y),
      a ≫ t = S.fromSpecStalk s ∧ g ≫ sY = pullback.fst sX t ≫ sX ∧ Agree φ f (pullback.fst sX t) g) :
    ∃ F : X ⟶ Y, F ≫ sY = sX ∧ φ ≫ F = f := by
  have : Flat φ := MorphismProperty.of_isPullback hp.flip ‹_›
  refine exists_of_locally sX sY hp fun x => ?_
  obtain ⟨T, t, a, g, ha, hg, hA⟩ := h (sX x)
  have e : X.fromSpecStalk x ≫ sX = (Spec.map (sX.stalkMap x) ≫ a) ≫ t := by
    rw [Category.assoc, ha, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h₁ := hA.comp (pullback.lift _ _ e)
  rw [pullback.lift_fst] at h₁
  exact exists_open_agree sX sY hf x _ (by rw [Category.assoc, hg, pullback.lift_fst_assoc]) h₁

theorem exists_spec_factor (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] {A : CommRingCat.{0}} (ψ : CommRingCat.of R ⟶ A) (hu : ∀ y : M, IsUnit (ψ.hom y)) :
    ∃ a : Spec A ⟶ Sp T, a ≫ spMap (algebraMap R T) = Spec.map ψ := by
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (S := T) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact IsLocalization.lift_eq hu r

theorem exists_fromSpecStalk_factor (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] (s : PrimeSpectrum R) (hM : M ≤ s.asIdeal.primeCompl) :
    ∃ a : Spec ((Sp R).presheaf.stalk s) ⟶ Sp T, a ≫ spMap (algebraMap R T) = (Sp R).fromSpecStalk s := by
  have hu : ∀ y : M, IsUnit ((StructureSheaf.toStalk R s).hom y) := fun y =>
    IsLocalization.map_units ((Spec.structureSheaf R).presheaf.stalk s) (⟨y.1, hM y.2⟩ : s.asIdeal.primeCompl)
  obtain ⟨a, ha⟩ := exists_spec_factor R T M (StructureSheaf.toStalk R s) hu
  exact ⟨a, ha.trans (Spec.fromSpecStalk_eq' (CommRingCat.of R) s).symm⟩

theorem exists_agree_of_extend {U T : Scheme.{0}} {k : U ⟶ T} {t : T ⟶ S} [Mono t] {j : U ⟶ S} (hj : k ≫ t = j)
    (G G' : Over S) [GrpObj G] [GrpObj G'] (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (h : ∀ f' : (Over.pullback k).obj ((Over.pullback t).obj G) ⟶ (Over.pullback k).obj ((Over.pullback t).obj G'),
      IsMonHom f' → ∃ F, (Over.pullback k).map F = f') :
    ∃ g : pullback G.hom t ⟶ G'.left, g ≫ G'.hom = pullback.fst G.hom t ≫ G.hom ∧
      Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst G'.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j)
    (((isGrpPullback_pullback _ k).comp (isGrpPullback_pullback G t)).congr hj rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback G' j)
    (((isGrpPullback_pullback _ k).comp (isGrpPullback_pullback G' t)).congr hj rfl)
  obtain ⟨F, hF⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  have hF' : (a.hom ≫ (Over.pullback k).map F).left = (f ≫ b.hom).left := by rw [hF, a.hom_inv_id_assoc]
  have hw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t := Over.w F
  have hw' : a.hom.left ≫ pullback.snd ((Over.pullback t).obj G).hom k = pullback.snd G.hom j := Over.w a.hom
  refine ⟨F.left ≫ pullback.fst G'.hom t, ?_, fun Z u u' e => ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  · have key : (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) ≫ F.left ≫ pullback.fst G'.hom t =
        f.left ≫ pullback.fst G'.hom j := by
      have h₁ := ExtUnique.pullback_map_left_fst k F
      rw [Over.comp_left, Over.comp_left] at hF'
      rw [← hb', ← reassoc_of% hF', reassoc_of% h₁]
      exact Category.assoc _ _ _
    have hfst : (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) ≫ pullback.fst G.hom t =
        pullback.fst G.hom j := (Category.assoc _ _ _).trans ha'
    have hu : u = u' ≫ (a.hom.left ≫ pullback.fst ((Over.pullback t).obj G).hom k) := by
      have : Mono (pullback.fst G.hom t) := inferInstance
      rw [← cancel_mono (pullback.fst G.hom t), e]
      exact (congrArg (u' ≫ ·) hfst.symm).trans (Category.assoc _ _ _).symm
    rw [hu]
    exact (Category.assoc _ _ _).trans (congrArg (u' ≫ ·) key)

end GlobalTheory.DedekindExt

namespace GlobalTheory

open DedekindExt

theorem abelianScheme_hom_extends_dedekind :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f := by
  intro H R K _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG'.proper
  have : IsPreimmersion (spMap (algebraMap R K)) := .of_isLocalization (nonZeroDivisors R)
  have : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hw : f.left ≫ pullback.snd G'.hom _ = pullback.snd G.hom _ := Over.w f
  have hf₀ : (f.left ≫ pullback.fst G'.hom _) ≫ G'.hom = pullback.fst G.hom _ ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  obtain ⟨F, hF, hF'⟩ := exists_of_stalks G.hom G'.hom (IsPullback.of_hasPullback G.hom (spMap (algebraMap R K)))
    hf₀ fun s : PrimeSpectrum R => by
      by_cases hs : s.asIdeal = ⊥
      · obtain ⟨a, ha⟩ := exists_fromSpecStalk_factor R K (nonZeroDivisors R) s fun r hr hr' =>
          nonZeroDivisors.ne_zero hr (by simpa [hs] using hr')
        refine ⟨_, _, a, _, ha, hf₀, fun Z u u' e => ?_⟩
        rw [(cancel_mono _).1 e]
      · let T := Localization.AtPrime s.asIdeal
        have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hs T
        letI : Algebra T K := IsLocalization.localizationAlgebraOfSubmonoidLe T K s.asIdeal.primeCompl
          (nonZeroDivisors R) s.asIdeal.primeCompl_le_nonZeroDivisors
        have : IsScalarTower R T K := IsLocalization.localization_isScalarTower_of_submonoid_le T K _ _ _
        have : IsFractionRing T K :=
          IsFractionRing.isFractionRing_of_isDomain_of_isLocalization s.asIdeal.primeCompl T K
        have : IsPreimmersion (spMap (algebraMap R T)) := .of_isLocalization s.asIdeal.primeCompl
        obtain ⟨a, ha⟩ := exists_fromSpecStalk_factor R T s.asIdeal.primeCompl s le_rfl
        have hj : spMap (algebraMap T K) ≫ spMap (algebraMap R T) = spMap (algebraMap R K) := by
          rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R T K]; rfl
        obtain ⟨g, hg, hA⟩ := exists_agree_of_extend hj G G' f fun f' hf' => by
          obtain ⟨F, hF, -⟩ := H T K _ _
            (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ G hG))
            (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ G' hG')) f' hf'
          exact ⟨F, hF.2⟩
        exact ⟨_, _, a, g, ha, hg, hA⟩
  have e : (Over.pullback (spMap (algebraMap R K))).map (Over.homMk F hF : G ⟶ G') = f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (ExtUnique.pullback_map_left_fst _ _).trans hF'
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨Over.homMk F hF, ⟨ExtUnique.isMonHom_of_pullback _ _ (e ▸ hf), e⟩, fun F' hF'' => ?_⟩
  exact ExtUnique.pullback_map_injective _ G G' (hF''.2.trans e.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalRootReZeroImSq
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ReEqZeroAndImSq
namespace GlobalTheory.SquareEqNegReIm

theorem re_im_of_sq_eq_neg {z : ℂ} {c : ℝ} (hc : 0 ≤ c) (hz : z ^ 2 = -(c : ℂ)) :
    z.re = 0 ∧ z.im ^ 2 = c := by
  have hs : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = (c : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have h : z ^ 2 = (((Real.sqrt c : ℝ) : ℂ) * Complex.I) ^ 2 := by
    rw [mul_pow, hs, Complex.I_sq, hz]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · rw [h]; simp [Real.sq_sqrt hc]
  · rw [h]; simp [Real.sq_sqrt hc]

theorem re_eq_zero_and_im_sq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.rt0.re = (0 : ℝ) ∧ H.rt0.im ^ (2 : ℕ) = (H.d : ℝ) := by
  refine re_im_of_sq_eq_neg (by positivity) ?_
  rw [H.sqrt_neg_disc_sq]; simp

end GlobalTheory.SquareEqNegReIm
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

noncomputable section

namespace GlobalTheory.PrincipalDatum

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem coe_add' (a b : 𝓞 E) : ((a + b : 𝓞 E) : E) = a + b := rfl

omit [NumberField E] in
theorem coe_mul' (a b : 𝓞 E) : ((a * b : 𝓞 E) : E) = a * b := rfl

theorem exists_clear (𝔞 : Submodule (𝓞 E) E) (h : 𝔞.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ ψ : 𝔞 →ₗ[𝓞 E] 𝓞 E, ∀ x, (ψ x : E) = N * (x : E) := by
  obtain ⟨a, ⟨N, hN, rfl⟩, ha⟩ :=
    FractionalIdeal.isFractional_of_fg (S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) h
  choose f hf using ha
  have hf' : ∀ x : 𝔞, ((f x x.2 : 𝓞 E) : E) = N * (x : E) := fun x => by
    have := hf x x.2
    rw [Algebra.smul_def] at this
    simpa using this
  refine ⟨N, nonZeroDivisors.ne_zero hN, ⟨⟨fun x => f x x.2, fun x y => ?_⟩, fun c x => ?_⟩, hf'⟩
  · apply RingOfIntegers.ext
    rw [coe_add', hf', hf', hf', Submodule.coe_add, mul_add]
  · apply RingOfIntegers.ext
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [coe_mul', hf', hf', Submodule.coe_smul, Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring

section Act

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M]






end Act

variable [IsCMField E]

theorem principal_root_re_zero_im_sq (H : Host E) : H.rt0.re = 0 ∧ H.rt0.im ^ 2 = H.d := by
  first
  | exact @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | (apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq ..)

end GlobalTheory.PrincipalDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorLieBasisExists
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct
open GlobalTheory.GrpTangent

namespace GlobalTheory.SerreLie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff (c : R) (v x : epsR R ⟶ G) :
    IsLieComb ![c] ![v] x ↔ x = GrpTangent.epsScale c ≫ v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u 0 = GrpTangent.epsScale c ≫ v := Over.OverMorphism.ext (hu 0)
    simp [h]
  · rintro rfl
    refine ⟨![GrpTangent.epsScale c ≫ v], fun i => ?_, by simp⟩
    fin_cases i
    rfl

variable [IsCommMonObj G] {O : Type} [CommRing O] [Algebra O R]

def multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) : R →ₗ[O] Pts a (epsR R) where
  toFun r := Pts.mk a (GrpTangent.epsScale r ≫ v)
  map_add' r s := Pts.ext (epsScale_add_comp r s hv)
  map_smul' c r := Pts.ext (by
    simp only [Pts.hom_mk, RingHom.id_apply, Pts.hom_smul, Category.assoc, ha]
    rw [epsScale_mul_assoc, Algebra.smul_def, mul_comm])

theorem hom_multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) (r : R) :
    (multiples a hv ha r).hom = GrpTangent.epsScale r ≫ v := rfl

omit [Algebra O R] in
theorem pre_eq_zero_iff (a : OAct O G) (x : Pts a (epsR R)) :
    Pts.pre a (toUnit (epsR R) ≫ epsZero R) x = 0 ↔ IsTangent x.hom := by
  rw [isTangent_iff]
  constructor
  · intro h
    have h1 : (toUnit (epsR R) ≫ epsZero R) ≫ x.hom = 1 := congrArg Pts.hom h
    have h2 := congrArg (epsZero R ≫ ·) h1
    simp only [← Category.assoc, MonObj.comp_one] at h2
    rwa [toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp] at h2
  · intro h
    exact Pts.ext (by rw [Pts.hom_pre, Category.assoc, h, MonObj.comp_one]; rfl)

omit [Algebra O R] in
theorem isTangent_sub_pre (a : OAct O G) (x : Pts a (epsR R)) :
    IsTangent (x - Pts.pre a (toUnit (epsR R) ≫ epsZero R) x).hom := by
  rw [← pre_eq_zero_iff, map_sub, sub_eq_zero]
  apply Pts.ext
  simp only [Pts.hom_pre, ← Category.assoc]
  rw [Category.assoc (toUnit _) (epsZero R) (toUnit _),
    toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.comp_id]

theorem exists_retraction (a : OAct O G) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) :
    ∃ ρ : Pts a (epsR R) →ₗ[O] R, ρ ∘ₗ multiples a (hv.1 0) ha = LinearMap.id ∧
      multiples a (hv.1 0) ha ∘ₗ ρ = LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) := by
  have hinj : Function.Injective (multiples a (hv.1 0) ha) := fun r s h => by
    have h' : GrpTangent.epsScale r ≫ v = GrpTangent.epsScale s ≫ v := congrArg Pts.hom h
    have := (hv.2 _ (isTangent_epsScale r (hv.1 0))).unique
      ((isLieComb_one_iff r v _).2 rfl) ((isLieComb_one_iff s v _).2 h')
    exact congrFun this 0
  have hsur : ∀ x : Pts a (epsR R), ∃ r, multiples a (hv.1 0) ha r =
      (LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) : _ →ₗ[O] _) x := fun x => by
    obtain ⟨c, hc, -⟩ := hv.2 _ (isTangent_sub_pre a x)
    have e : c = ![c 0] := by ext i; fin_cases i; rfl
    rw [e, isLieComb_one_iff] at hc
    exact ⟨c 0, Pts.ext hc.symm⟩
  choose ρ hρ using hsur
  refine ⟨⟨⟨ρ, fun x y => hinj ?_⟩, fun c x => hinj ?_⟩, LinearMap.ext fun r => hinj ?_,
    LinearMap.ext hρ⟩
  · rw [map_add (f := _), hρ, hρ, hρ, map_add (f := _)]
  · simp only [RingHom.id_apply, map_smul, hρ]
  · change multiples a (hv.1 0) ha (ρ _) = _
    rw [hρ, LinearMap.sub_apply, (pre_eq_zero_iff a (multiples a (hv.1 0) ha r)).2
      (isTangent_epsScale r (hv.1 0)), sub_zero]
    rfl

theorem exists_lie_tensor : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] [Algebra O R] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (v : epsR R ⟶ G), IsLieBasis ![v] → (∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) → ∃ Φ : R ⊗[O] M → (epsR R ⟶ A), Function.Injective Φ ∧ (∀ x, IsTangent x ↔ x ∈ Set.range Φ) ∧ (∀ y z, Φ (y + z) = Φ y * Φ z) ∧ (∀ (c : R) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) ∧ (∀ m, Φ (1 ⊗ₜ m) = v ≫ t.tmul m) ∧ ∀ (φ : M →ₗ[O] M) y, Φ (φ.baseChange R y) = Φ y ≫ t.mapLeft t φ := by
  intro R _ G _ _ O _ _ M _ _ _ _ A _ _ a b t v hv ha'
  have ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v :=
    fun c => (isLieComb_one_iff _ _ _).1 (ha' c)
  obtain ⟨ρ, h₁, h₂⟩ := exists_retraction a hv ha
  set j := multiples a (hv.1 0) ha with hj
  let Ψ : R ⊗[O] M →ₗ[O] Pts b (epsR R) :=
    (t.equiv _).toLinearMap ∘ₗ j.lTensor M ∘ₗ (TensorProduct.comm O R M).toLinearMap
  have hΨ : ∀ (r : R) (m : M), (Ψ (r ⊗ₜ m)).hom = GrpTangent.epsScale r ≫ v ≫ t.tmul m := fun r m => by
    simp [Ψ, hj, hom_multiples]
  refine ⟨fun y => (Ψ y).hom, fun y z h => ?_, fun x => ⟨fun hx => ?_, ?_⟩, fun y z => ?_,
    fun c y => ?_, fun m => ?_, fun φ y => ?_⟩
  · have h' : j.lTensor M (TensorProduct.comm O R M y) = j.lTensor M (TensorProduct.comm O R M z) :=
      (t.equiv _).injective (Pts.ext h)
    have h'' := congrArg (ρ.lTensor M) h'
    simp only [← LinearMap.lTensor_comp_apply, h₁, LinearMap.lTensor_id, LinearMap.id_apply] at h''
    exact (TensorProduct.comm O R M).injective h''
  · obtain ⟨z, hz⟩ := (t.equiv (epsR R)).surjective (Pts.mk b x)
    have h0 : (Pts.pre a (toUnit (epsR R) ≫ epsZero R)).lTensor M z = 0 := by
      apply (t.equiv _).injective
      rw [t.natural, hz, map_zero]
      exact (pre_eq_zero_iff b _).2 hx
    refine ⟨(TensorProduct.comm O R M).symm (ρ.lTensor M z), ?_⟩
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.lTensor_comp_apply, h₂, LinearMap.lTensor_sub, LinearMap.sub_apply, h0,
      sub_zero, LinearMap.lTensor_id, LinearMap.id_apply, hz, Pts.hom_mk]
  · rintro ⟨y, rfl⟩
    rw [← pre_eq_zero_iff]
    induction y with
    | tmul r m =>
      rw [pre_eq_zero_iff, hΨ]
      exact isTangent_epsScale r (isTangent_comp (hv.1 0) _)
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
  · simp only [map_add (f := _), Pts.hom_add]
  · rw [isLieComb_one_iff]
    induction y with
    | tmul r m =>
      simp only [TensorProduct.smul_tmul', hΨ, smul_eq_mul]
      rw [epsScale_mul_assoc]
    | add y z hy hz =>
      simp only [smul_add, map_add (f := _), Pts.hom_add, MonObj.comp_mul] at hy hz ⊢
      rw [hy, hz]
  · simp only [hΨ, epsScale_one, Category.id_comp]
  · induction y with
    | tmul r m => simp only [LinearMap.baseChange_tmul, hΨ, Category.assoc, IsTensor.tmul_mapLeft]
    | add y z hy hz =>
      simp only [map_add (f := _), Pts.hom_add, MonObj.mul_comp] at hy hz ⊢
      rw [hy, hz]

end GlobalTheory.SerreLie
end
end

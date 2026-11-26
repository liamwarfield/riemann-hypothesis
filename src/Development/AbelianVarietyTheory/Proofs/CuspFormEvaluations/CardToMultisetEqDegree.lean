module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace Jet

variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']

theorem card_toMultiset_eq_degree (m : σ →₀ ℕ) :
    Multiset.card (Finsupp.toMultiset m) = m.degree := by
  simp only [Finsupp.card_toMultiset]
  rfl

theorem degree_eq_of_mem_support {P : MvPolynomial σ ℂ} {a : ℕ} (hP : P.IsHomogeneous a)
    {m : σ →₀ ℕ} (hm : m ∈ P.support) : m.degree = a := by
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hm) (hP.coeff_eq_zero h)

theorem polyDeriv_eq_sum_monomial (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P u F x =
      ∑ m ∈ P.support, P.coeff m * polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x := by
  simp only [polyDeriv_monomial_one]
  rfl

theorem polyDeriv_add_fun [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F G : W → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (x : W) :
    polyDeriv P u (F + G) x = polyDeriv P u F x + polyDeriv P u G x := by
  unfold polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hF _).contDiffAt
    (contDiff_of_differentiable_fd hG _).contDiffAt]
  simp only [ContinuousMultilinearMap.add_apply]
  ring

theorem polyDeriv_smul_fun [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply (contDiff_of_differentiable_fd hF _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem polyDeriv_sum_fun [FiniteDimensional ℂ W] {κ : Type*} (P : MvPolynomial σ ℂ) (u : σ → W)
    (s : Finset κ) (c : κ → ℂ) (F : κ → W → ℂ) (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x :=
  ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_sum P u s c F
    (fun i hi k => contDiff_of_differentiable_fd (hF i hi) k) x

theorem polyDeriv_comp_equiv (P : MvPolynomial σ ℂ) (u : σ → W) (F : W' → ℂ) (φ : W ≃L[ℂ] W')
    (x : W) : polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := φ.iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (Set.mem_univ (φ x))
    (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [h]
  rfl

theorem polyDeriv_comp_clm [FiniteDimensional ℂ W'] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W' → ℂ} (hF : Differentiable ℂ F) (φ : W →L[ℂ] W') (x : W) :
    polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [φ.iteratedFDeriv_comp_right (contDiff_of_differentiable_fd hF _) x le_rfl]
  rfl

theorem polyDeriv_smul_dir {P : MvPolynomial σ ℂ} {a : ℕ} (hP : P.IsHomogeneous a) (c : ℂ)
    (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P (fun i => c • u i) F x = c ^ a * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ContinuousMultilinearMap.map_smul_univ _ (fun _ => c), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  have h : c ^ Multiset.card (Finsupp.toMultiset m) = c ^ a := by
    rw [card_toMultiset_eq_degree, degree_eq_of_mem_support hP hm]
  rw [h]
  ring

theorem polyDeriv_comp_smul_at [FiniteDimensional ℂ W] {P : MvPolynomial σ ℂ} {a : ℕ}
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) :
    polyDeriv P u (fun v => F (c • v)) x = c ^ a * polyDeriv P u F (c • x) := by
  rw [← polyDeriv_smul_dir hP]
  exact polyDeriv_comp_clm P u hF (c • ContinuousLinearMap.id ℂ W) x

theorem polyDeriv_comp_smul [FiniteDimensional ℂ W] {P : MvPolynomial σ ℂ} {a : ℕ}
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) :
    polyDeriv P u (fun v => F (c • v)) 0 = c ^ a * polyDeriv P u F 0 := by
  rw [polyDeriv_comp_smul_at hP c u hF, smul_zero]

section Euclid

variable {ι : Type} [Fintype ι]

theorem Hf_eq_inner (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply]

theorem differentiable_translate (q : ℕ) (y : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : Differentiable ℂ F) :
    Differentiable ℂ fun v =>
      cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y) := by
  have h1 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v y := by
    simp only [Hf_eq_inner]
    exact (innerSL ℂ y).differentiable
  have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => F (v - y) :=
    hF.comp (differentiable_id.sub_const y)
  exact (((h1.const_mul _).sub_const _).cexp).mul h2

theorem norm_translate (q : ℕ) (y : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (v : EuclideanSpace ℂ ι) :
    ‖cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y)‖ ^ 2 *
        Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) =
      ‖F (v - y)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - y‖ ^ 2) := by
  have hre : (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2 : ℂ).re =
      q * Real.pi * (inner ℂ y v : ℂ).re - q * Real.pi * ‖y‖ ^ 2 / 2 := by
    rw [Hf_eq_inner, Hf_eq_inner, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hn : ‖v - y‖ ^ 2 = ‖y‖ ^ 2 - 2 * (inner ℂ y v : ℂ).re + ‖v‖ ^ 2 := by
    rw [norm_sub_rev, @norm_sub_sq ℂ]
    rfl
  rw [norm_mul, Complex.norm_exp, hre, hn, mul_pow, mul_comm _ (‖F (v - y)‖ ^ 2), mul_assoc,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  push_cast
  ring

open scoped Classical in
open Classical in
theorem norm_polyDeriv_le (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) F 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set t : ℝ := Real.sqrt q with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq0.le
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  set G : EuclideanSpace ℂ ι → ℂ := fun v => F ((t : ℂ)⁻¹ • v) with hGdef
  have hG : Differentiable ℂ G := hF.comp (g := F) (f := fun v => (t : ℂ)⁻¹ • v) (by fun_prop)
  have hGS : ∀ v, ‖G v‖ ^ 2 * Real.exp (-Real.pi * ‖v‖ ^ 2) ≤ S := by
    intro v
    have h := hS ((t : ℂ)⁻¹ • v)
    have e : -(q * Real.pi) * ‖(t : ℂ)⁻¹ • v‖ ^ 2 = -Real.pi * ‖v‖ ^ 2 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, mul_pow, inv_pow, ht2]
      field_simp
    rwa [e] at h
  have hFG : F = fun v => G ((t : ℂ) • v) := by
    funext v
    simp only [hGdef, smul_smul, inv_mul_cancel₀ htc, one_smul]
  have hb : ‖polyDeriv P (fun i => EuclideanSpace.single i 1) G 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.sqrt S *
        (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2)) := by
    rw [polyDeriv_eq_sum_monomial, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := gCauchy ι G hG S hGS m
    rwa [degree_eq_of_mem_support hP hm] at h
  have hpow : t ^ a = (q : ℝ) ^ ((a : ℝ) / 2) := by
    rw [ht, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have hsplit : ((q : ℝ) * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) =
      t ^ a * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
    rw [hpow, ← Real.mul_rpow hq0.le (by positivity)]
    congr 1
    ring
  rw [hFG, polyDeriv_comp_smul hP _ _ hG, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg ht0.le, hsplit]
  calc t ^ a * ‖polyDeriv P (fun i => EuclideanSpace.single i 1) G 0‖
      ≤ t ^ a * ((∑ m ∈ P.support, ‖P.coeff m‖) * (Real.sqrt S *
        (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Euclid

end Jet

open scoped Classical in
open Classical in
theorem translate_jet_bound {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) (y : EuclideanSpace ℂ ι) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) (U q y F) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  have hfun : U q y F = fun v =>
      cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y) := funext (hU q y F)
  rw [hfun]
  refine Jet.norm_polyDeriv_le q hq _ (Jet.differentiable_translate q y hF) S (fun v => ?_) P a hP
  rw [Jet.norm_translate]
  exact hS _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
namespace GlobalTheory

theorem _root_.GlobalTheory.packingCount : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.PackingCount
  intro n P δ R hδ hR hP hsep
  have h1 := _root_.GlobalTheory.finset_card_le_of_separated P hδ (hδ.le.trans hR) 0
    (by simpa [dist_zero_right] using hP) (fun x hx y hy hxy => hsep x hx y hy hxy)
  rw [finrank_euclideanSpace_fin] at h1
  exact h1.trans (_root_.GlobalTheory.one_add_two_mul_div_pow_le hδ hR n)

theorem _root_.GlobalTheory.sup_le_l2_principal_torus : _root_.ReciprocityTheory.ChartRestriction.G.I2.GSupStatement := _root_.ReciprocityTheory.ChartRestriction.G.I2.gSup _root_.GlobalTheory.packingCount

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocalizedModuleSubtype
namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DualFamily

lemma _root_.GlobalTheory.DualFamily.herm_one_eq {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = ∑ a, x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp [Matrix.one_apply]

lemma _root_.GlobalTheory.DualFamily.herm_one_symm {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x) := by
  rw [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.DualFamily.herm_one_eq]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]

lemma _root_.GlobalTheory.DualFamily.isIntegral_cc {a : E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact ha.map (RingHom.toIntAlgHom (IsCMField.complexConj E).toRingEquiv.toRingHom)

lemma _root_.GlobalTheory.DualFamily.exists_herm_eq {n : ℕ} (f : (Fin n → E) →ₗ[E] E) :
    ∃ w : Fin n → E, ∀ u, f u = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u w := by
  refine ⟨fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (f fun b => if a = b then 1 else 0), fun u => ?_⟩
  rw [f.pi_apply_eq_sum_univ u, _root_.GlobalTheory.DualFamily.herm_one_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  rw [IsCMField.complexConj_apply_apply, smul_eq_mul]

omit [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.eq_zero_of_line {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (w : Fin n → E) (hw : ∀ c : E, c • w ∈ Λ) : w = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have htop : Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) j) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hw _, ?_⟩
    simp [div_mul_cancel₀ _ hj]
  have : Module.Finite (𝓞 E) E := ⟨by rw [← htop]; exact hfg.map _⟩
  have := Algebra.IsIntegral.of_finite (𝓞 E) E
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

lemma _root_.GlobalTheory.DualFamily.span_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.DualFamily.exists_herm_eq f
  have hline : ∀ c : E, c • w ∈ Λ := fun c => hdual _ fun y hy => by
    have hfy : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
    have hsmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (c • w) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w y := by
      simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        mul_assoc]
    rw [hsmul, _root_.GlobalTheory.DualFamily.herm_one_symm w y, ← hw, hfy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    rw [map_zero, mul_zero]
    exact isIntegral_zero
  have hw0 := _root_.GlobalTheory.DualFamily.eq_zero_of_line Λ hfg w hline
  exact hf0 (LinearMap.ext fun u => by simp [hw u, hw0, _root_.GlobalTheory.DualFamily.herm_one_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc])

end DualFamily

omit [IsCMField E] in
private lemma exists_linearForm_extend_of_span_eq_univ {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y : Λ, φ y = g y := by
  obtain ⟨t, htΛ, hts, hli⟩ := exists_linearIndependent E (Λ : Set (Fin n → E))
  let b : Module.Basis t E (Fin n → E) :=
    Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hts, hspan]))
  have hb : ∀ i, b i ∈ Λ := fun i => by rw [Module.Basis.mk_apply]; exact htΛ i.2
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  refine ⟨b.constr E fun i => ((g ⟨b i, hb i⟩ : 𝓞 E) : E), fun y => ?_⟩
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ (b.repr y)
  have hd' : ∀ i, ∃ x : 𝓞 E, algebraMap (𝓞 E) E x = (d : 𝓞 E) • b.repr y i :=
    fun i => hd i (Finset.mem_univ _)
  choose a ha using hd'
  have hdy : (d : 𝓞 E) • y = ∑ i, a i • (⟨b i, hb i⟩ : Λ) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_sum]
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul E (a i), ha i, smul_assoc]
  have hg := congrArg (fun z => ((g z : 𝓞 E) : E)) hdy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul] at hg
  simp only [RingOfIntegers.coe_eq_algebraMap]
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  apply mul_left_cancel₀ hd0
  rw [hg]
  conv_lhs => rw [← b.sum_repr (y : Fin n → E)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, ha i, smul_eq_mul, Algebra.smul_def]
  ring

theorem _root_.GlobalTheory.exists_dual_family {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ ∃ (m : ℕ) (v w : Fin m → Fin n → E),
      (∀ i, v i ∈ Λ) ∧ (∀ i, w i ∈ Λ) ∧ ∀ u : Fin n → E, u = ∑ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u (w i) • v i := by
  have hspan := _root_.GlobalTheory.DualFamily.span_eq_top Λ hfg hdual
  refine ⟨hspan, ?_⟩
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have := Module.finitePresentation_of_finite (𝓞 E) Λ
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hext : ∀ j : Fin m, ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y (hy : y ∈ Λ), φ y = σ ⟨y, hy⟩ j :=
    fun j => (exists_linearForm_extend_of_span_eq_univ Λ hspan ((LinearMap.proj j).comp σ)).imp
      fun φ h y hy => h ⟨y, hy⟩
  choose φ hφ using hext
  choose w hw using fun j => _root_.GlobalTheory.DualFamily.exists_herm_eq (φ j)
  let v : Fin m → Fin n → E := fun j => (π fun k => if j = k then 1 else 0 : Λ)
  refine ⟨m, v, w, fun j => (π _).2, fun j => hdual _ fun y hy => ?_, fun u => ?_⟩
  · rw [_root_.GlobalTheory.DualFamily.herm_one_symm, ← hw, hφ j y hy]
    exact _root_.GlobalTheory.DualFamily.isIntegral_cc (RingOfIntegers.isIntegral_coe _)
  · have hL : (∑ j, (φ j).smulRight (v j)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have hy' : y = ((π (σ ⟨y, hy⟩) : Λ) : Fin n → E) := by
        rw [← LinearMap.comp_apply, hσ]
        rfl
      conv_rhs => rw [hy', π.pi_apply_eq_sum_univ]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hφ j y hy, RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    have hu := congrArg (fun L : (Fin n → E) →ₗ[E] (Fin n → E) => L u) hL
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, hw] at hu
    exact hu.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PushLettersIntCastOfIsHomogeneous
open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.Harm

section Free

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ ι : Type*}

noncomputable def basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (b.repr (AddMonoidAlgebra.coeff P m) i)

theorem coeff_basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S)
    (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (basisComponent b i P) m = b.repr (AddMonoidAlgebra.coeff P m) i := by
  classical
  rw [basisComponent, coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro m' _ h; simp [coeff_monomial, h]
  · intro h; simp [notMem_support_iff.1 h]

theorem exists_eq_sum_basisComponent (b : Module.Basis ι R S) (P : MvPolynomial σ S) :
    ∃ J : Finset ι, P = ∑ i ∈ J, b i • MvPolynomial.map (algebraMap R S) (basisComponent b i P) := by
  classical
  refine ⟨P.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff P m)).support, ?_⟩
  ext m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_basisComponent, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff P m), Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset (s := P.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff P m)).support)]
  · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
  · by_cases hm : m ∈ P.support
    · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (AddMonoidAlgebra.coeff P m)).support) hm
    · simp [notMem_support_iff.1 hm]
  · simp

theorem basisComponent_sum (b : Module.Basis ι R S) (J : Finset ι) (Q : ι → MvPolynomial σ R)
    {i : ι} (hi : i ∈ J) :
    basisComponent b i (∑ j ∈ J, b j • MvPolynomial.map (algebraMap R S) (Q j)) = Q i := by
  classical
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_basisComponent, coeff_sum, coeff_smul, coeff_map, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i] <;> simp +contextual [hi]

variable {T : Type*} {p q : ℕ} {κ : Type*} [Fintype κ] {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}

theorem basisComponent_mem_rowHighest (b : Module.Basis ι R S) (i : ι) {P : Poly S T p q κ}
    (hP : P ∈ rowHighest S c c') : basisComponent b i P ∈ rowHighest R c c' := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
  by_cases hi : i ∈ J
  swap
  · have : basisComponent b i P = 0 := by
      rw [← basisComponent_sum b (insert i J)
        (fun j => if j = i then 0 else basisComponent b j P) (Finset.mem_insert_self i J)
        |>.trans (ite_eq_left rfl)]
      congr 1
      rw [Finset.sum_insert hi, ite_eq_left rfl, map_zero, smul_zero, zero_add]
      refine hJ.trans (Finset.sum_congr rfl fun j hj => ?_)
      rw [ite_eq_right (by rintro rfl; exact hi hj)]
    rw [this]; exact zero_mem _
  refine mem_rowHighest_iff_rowAdd.2 ⟨fun t a b' => ?_, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => ?_⟩
  · have := h₁ t a b'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hJ, map_sum] at this
    simp only [map_smul, ← map_laplacian] at this
    rw [← basisComponent_sum b J (fun j => laplacian t a b' (basisComponent b j P)) hi, this]
    simp [basisComponent]
  · rw [coeff_basisComponent, e]; simp
  · have := h₃ t r r' hr s
    conv_lhs at this => rw [hJ, map_sum]
    simp only [map_smul, ← map_intCast (algebraMap R S), ← map_rowAdd] at this
    rw [← basisComponent_sum b J (fun j => rowAdd t r r' (s : R) (basisComponent b j P)) hi, this]

variable (R S c c') in
theorem span_map_rowHighest [Module.Free R S] :
    Submodule.span S (MvPolynomial.map (algebraMap R S) ''
      (rowHighest R (κ := κ) c c' : Set (Poly R T p q κ))) = rowHighest S c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    exact map_mem_rowHighest _ hP
  · intro P hP
    let b := Module.Free.chooseBasis R S
    obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
    rw [hJ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, basisComponent_mem_rowHighest b i hP, rfl⟩)

end Free

section Scale

variable {R : Type*} [CommRing R] {T : Type*} {p q : ℕ} {κ : Type*}

end Scale

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type*} [Field K]
  {T : Type*} {p q n : ℕ}

theorem herm_one_eq_sum (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

variable (p q) in
noncomputable def symO (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Subalgebra (𝓞 K) (Poly K T p q (Fin n)) :=
  Algebra.adjoin (𝓞 K)
    ({P | ∃ t a, ∃ v ∈ Λ, P = xForm t a fun k => τ t (v k)} ∪
      {P | ∃ t b, ∃ v ∈ Λ, P = yForm t b fun k => τ t (cc (v k))})

noncomputable def Ha (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Poly K T p q (Fin n)) :=
  (rowHighest (R := K) c c').restrictScalars (𝓞 K) ⊓ Subalgebra.toSubmodule (symO p q τ Λ)

variable (τ : T → E →+* K) {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
  {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {P : Poly K T p q (Fin n)}

variable [NumberField K]

variable [Fintype T]

end Lattice

end GlobalTheory.Harm
end

module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnitFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem _root_.GlobalTheory.UnitFrame.trace_eq_sum_re (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have htr : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ => τ z) (fun σ => σ z)
      (fun _ => rfl)).symm
  rw [Complex.ofReal_ratCast, htr]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Ψ)]
  have hsplit : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∉ Ψ), τ z
      = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∈ Ψ), conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      by_contra h
      exact hτ ((hΨ _).2 (by simpa using h))
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (hΨ τ).1 hτ
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hsplit, ← Finset.sum_add_distrib]
  rw [Finset.sum_subtype (Finset.univ.filter (· ∈ Ψ)) (p := (· ∈ Ψ)) (by simp)]
  refine Fintype.sum_congr _ _ (fun τ => ?_)
  rw [Complex.add_conj]
  push_cast; ring

omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UnitFrame.hermC_eq {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v = u ⬝ᵥ (G.map τ) *ᵥ (star v) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UnitFrame.gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map conj) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UnitFrame.hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (c c' : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (x *ᵥ c) (x *ᵥ c') = c ⬝ᵥ (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x) *ᵥ (star c') := by
  have hstar : star (x *ᵥ c') = x.map conj *ᵥ star c' := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [_root_.GlobalTheory.UnitFrame.hermC_eq, _root_.GlobalTheory.UnitFrame.gram_eq,
    ← mulVec_mulVec, ← mulVec_mulVec, hstar, dotProduct_mulVec c xᵀ, vecMul_transpose]

omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UnitFrame.im_sum_periods {r : ℕ} (q : ℕ) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ)
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (u v : Fin r → ℂ) :
    (∑ a : Fin r, (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) u else (x⁻¹ *ᵥ u) a) *
      conj (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) v else (x⁻¹ *ᵥ v) a)).im =
      -(_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v).im := by
  have hsgn : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by
    intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
  have hdet : x.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [_root_.GlobalTheory.UnitFrame.gram_eq, det_mul, det_transpose, h0, zero_mul,
      det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    rcases hsgn a with h | h <;> simp [h]
  have hx1 : x * x⁻¹ = 1 := mul_nonsing_inv x (isUnit_iff_ne_zero.2 hdet)
  have hback : ∀ y : Fin r → ℂ, x *ᵥ (x⁻¹ *ᵥ y) = y := by
    intro y; rw [mulVec_mulVec, hx1, one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a = x *ᵥ Pi.single a 1 := by
    intro a; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, mulVec_single_one]
  have hkey : ∀ a (y : Fin r → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) y
      = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ y) a) := by
    intro a y
    conv_lhs => rw [hcol, ← hback y]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [mulVec_diagonal]
  have hfull : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v
      = ∑ a, (x⁻¹ *ᵥ u) a * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ v) a)) := by
    conv_lhs => rw [← hback u, ← hback v]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [dotProduct, mulVec_diagonal]
  rw [hfull, Complex.im_sum, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < q
  · simp only [ha, if_true, hkey]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]
    ring
  · simp only [ha, if_false]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]

private lemma mem_iff_conjugate_not_mem (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq
    simpa using this
  have hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hrt]; simp
  have h0 := H.sqrt_neg_disc_sq
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  set w := τ (H.rt : E)
  set m := H.rt0
  have reZero : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ^ 2 = H.d := by
    intro z hz
    have e1 := congrArg Complex.re hz
    have e2 := congrArg Complex.im hz
    simp [sq, Complex.mul_re, Complex.mul_im] at e1 e2
    have hre : z.re = 0 := by
      rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h
      · exact h
      · exfalso; rw [h] at e1; nlinarith [sq_nonneg z.re]
    refine ⟨hre, ?_⟩
    rw [hre] at e1; nlinarith
  obtain ⟨hwr, hwi⟩ := reZero w hw
  obtain ⟨hmr, hmi⟩ := reZero m h0
  have hm0 : m.im ≠ 0 := by
    intro h; rw [h] at hmi; linarith
  constructor
  · intro h hc
    rw [h] at hc
    have := congrArg Complex.im hc
    simp at this
    exact hm0 (by linarith)
  · intro hn
    apply Complex.ext
    · rw [hwr, hmr]
    · have : (w.im - m.im) * (w.im + m.im) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exfalso; apply hn
        apply Complex.ext
        · simp [hwr, hmr]
        · simp; linarith

theorem _root_.GlobalTheory.UnitFrame.im_hermForm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) → ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (P : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ τ : Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn D.q (a : ℕ) : ℝ) : ℂ)) → ∀ v w, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im = D.EF v w := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hdata x P hP hgram v w
  have hEF := hdata.2.2.2.2
  have hcm := mem_iff_conjugate_not_mem H Ψ hΨ
  have hherm : ∀ (τ : E →+* ℂ) (a b : Fin r → E),
      τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm a b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ b) := by
    intro τ a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj]
  have hre : ∀ τ : Ψ, (τ.1 (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ v) (φ w))).re
      = -‖τ.1 ξ‖ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ v)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ w))).im := by
    intro τ
    have hc : conj (τ.1 ξ) = -τ.1 ξ := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_neg]
      congr 1
    have hr : (τ.1 ξ).re = 0 := by
      have := congrArg Complex.re hc
      simp at this; linarith
    have hn : ‖τ.1 ξ‖ = (τ.1 ξ).im := by
      have hz : τ.1 ξ = ((τ.1 ξ).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hr]
      rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos]
      · simp
      · simpa using hpos τ.1 τ.2
    rw [map_mul, hherm, Complex.mul_re, hr, hn]
    ring
  have hL : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im
      = ∑ k, 2 * ‖(idx k).1.1 ξ‖ * (P v k * conj (P w k)).im := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, mulVec_diagonal, Complex.im_sum, Pi.star_apply,
      Complex.star_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hL, ← Rat.cast_intCast, hEF, _root_.GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hcm, ← idx.symm.sum_comp,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun τ => ?_
  simp only [Equiv.apply_symm_apply]
  rw [← Finset.mul_sum, ← Complex.im_sum]
  have hPv : ∀ u, ∀ a : Fin r, P u (idx.symm (τ, a)) = if (a : ℕ) < D.q then
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u))
      else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u)) a := by
    intro u a; rw [hP]; simp
  simp only [hPv]
  rw [_root_.GlobalTheory.UnitFrame.im_sum_periods D.q τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (hgram τ), hre]
  ring

end GlobalTheory.UnitFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Imports
namespace GlobalTheory.LatticeBoundedAction

theorem main {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) :
    ∀ v ∈ Submodule.span K (↑Λ : Set V), ∃ (d : R), d ≠ (0 : R) ∧ d • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
    have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have key : (b : R) • (c • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, ← hab, mul_comm, IsLocalization.mk'_spec, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd hb, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact Λ.smul_mem a h

end GlobalTheory.LatticeBoundedAction
end

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section PseudoBasis

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_smul_mem_of_mem_span_fraction {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (v : V) (hv : v ∈ Submodule.span K (Λ : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_8 h_9 h_10 h_11; revert R K h_2 h_3 h_4 h_5 h_6 V h_8 h_9 h_10 h_11 Λ v hv; exact @_root_.GlobalTheory.LatticeBoundedAction.main)
  | exact @_root_.GlobalTheory.LatticeBoundedAction.main
  | exact _root_.GlobalTheory.LatticeBoundedAction.main
  | (apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBoundedAction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBoundedAction.main ..)

theorem exists_splitting_vector {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set V) = ⊤) (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ (c : FractionalIdeal R⁰ K) (e : V), c ≠ 0 ∧ l e = 1 ∧ (∀ v ∈ Λ, l v ∈ c) ∧
      ∀ x ∈ c, x • e ∈ Λ := by
  have hfg' : (Λ.map (l.restrictScalars R)).FG := hfg.map _
  let c : FractionalIdeal R⁰ K := ⟨Λ.map (l.restrictScalars R), FractionalIdeal.isFractional_of_fg hfg'⟩
  have hc : ∀ x, x ∈ c ↔ ∃ v ∈ Λ, l v = x := fun x => Iff.rfl
  have hc0 : c ≠ 0 := by
    intro h
    apply hl
    refine LinearMap.ext_on hsp ?_
    intro v hv
    have : l v ∈ c := (hc _).2 ⟨v, hv, rfl⟩
    rw [h] at this
    simpa using this
  have h1 : (1 : K) ∈ c * c⁻¹ := by
    rw [mul_inv_cancel₀ hc0]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ y ∈ c * c⁻¹, ∃ e : V, l e = y ∧ ∀ x ∈ c, x • e ∈ Λ := by
    intro y hy
    refine FractionalIdeal.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨v, hv, rfl⟩ := (hc _).1 ha
      refine ⟨b • v, by simp [mul_comm], ?_⟩
      intro x hx
      have : x * b ∈ c * c⁻¹ := FractionalIdeal.mul_mem_mul hx hb
      rw [mul_inv_cancel₀ hc0, FractionalIdeal.mem_one_iff] at this
      obtain ⟨t, ht⟩ := this
      rw [smul_smul, ← ht, algebraMap_smul]
      exact Λ.smul_mem _ hv
    · rintro a b ⟨e, he, he'⟩ ⟨f, hf, hf'⟩
      refine ⟨e + f, by simp [he, hf], ?_⟩
      intro x hx
      rw [smul_add]
      exact Λ.add_mem (he' x hx) (hf' x hx)
  obtain ⟨e, he, he'⟩ := key 1 h1
  exact ⟨c, e, hc0, he, fun v hv => (hc _).2 ⟨v, hv, rfl⟩, he'⟩

theorem exists_pseudoCoords (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
      [FiniteDimensional K V], Module.finrank K V = n →
      ∀ (Λ : Submodule R V) (I : Submodule K V), Λ.FG → Submodule.span K (Λ : Set V) = ⊤ →
      ∃ (s : ℕ) (f : Fin n → (V →ₗ[K] K)) (c : Fin n → FractionalIdeal R⁰ K),
        (∀ v, (∀ a, f a v = 0) → v = 0) ∧ (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, f a v ∈ c a) ∧
        ∀ v, v ∈ I ↔ ∀ a : Fin n, s ≤ (a : ℕ) → f a v = 0 := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ hV Λ I _ _
    have : Subsingleton V := Module.finrank_zero_iff.1 hV
    refine ⟨0, Fin.elim0, Fin.elim0, fun v _ => Subsingleton.elim _ _, fun a => a.elim0, ?_, ?_⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => Λ.zero_mem⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => I.zero_mem⟩
  | succ n ih =>
    intro V _ _ _ _ _ hV Λ I hfg hsp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨l, hl, hI⟩ : ∃ l : V →ₗ[K] K, l ≠ 0 ∧ (I = ⊤ ∨ I ≤ LinearMap.ker l) := by
      by_cases h : I = ⊤
      · obtain ⟨l, hl, -⟩ := Submodule.exists_le_ker_of_lt_top (⊥ : Submodule K V) bot_lt_top
        exact ⟨l, hl, Or.inl h⟩
      · obtain ⟨l, hl, h2⟩ := Submodule.exists_le_ker_of_lt_top I (lt_top_iff_ne_top.2 h)
        exact ⟨l, hl, Or.inr h2⟩
    obtain ⟨c0, e, hc0, he, hΛc, hce⟩ := exists_splitting_vector Λ hfg hsp l hl
    set W := LinearMap.ker l with hW
    have hWn : Module.finrank K W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker l
      have h2 : LinearMap.range l = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨x • e, by simp [he]⟩
      rw [h2, finrank_top, Module.finrank_self, hV] at h1
      rw [hW]; omega
    let ι : W →ₗ[R] V := W.subtype.restrictScalars R
    have hι : Function.Injective ι := Subtype.val_injective
    let Λ' : Submodule R W := Λ.comap ι
    have hΛ' : ∀ w : W, w ∈ Λ' ↔ (w : V) ∈ Λ := fun w => Iff.rfl
    have hfg' : Λ'.FG := by
      apply Submodule.fg_of_fg_map_injective ι hι
      exact Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
    have hsp' : Submodule.span K (Λ' : Set W) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span_fraction (K := K) Λ (w : V)
        (by rw [hsp]; trivial)
      have hd1 : algebraMap R K d ≠ 0 := by simpa using hd
      have hm : algebraMap R K d • w ∈ Λ' := by
        rw [hΛ']
        simpa using hdw
      have : w = (algebraMap R K d)⁻¹ • (algebraMap R K d • w) := by
        rw [smul_smul, inv_mul_cancel₀ hd1, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
    obtain ⟨s, f, c, hf, hc, hfΛ, hfI⟩ := ih W hWn Λ' (I.comap W.subtype) hfg' hsp'
    let p : V →ₗ[K] W := LinearMap.codRestrict W (LinearMap.id - l.smulRight e) (by
      intro v
      simp [hW, he])
    have hp : ∀ v, (p v : V) = v - l v • e := fun v => rfl
    let F : Fin (n + 1) → (V →ₗ[K] K) := Fin.snoc (fun a => f a ∘ₗ p) l
    let C : Fin (n + 1) → FractionalIdeal R⁰ K := Fin.snoc c c0
    have hF1 : ∀ a v, F (Fin.castSucc a) v = f a (p v) := by
      intro a v; simp [F]
    have hF2 : ∀ v, F (Fin.last n) v = l v := by
      intro v; simp [F]
    have hC1 : ∀ a, C (Fin.castSucc a) = c a := by
      intro a; simp [C]
    have hC2 : C (Fin.last n) = c0 := by
      simp [C]
    have A1 : ∀ v, (∀ a, F a v = 0) → v = 0 := by
      intro v hv
      have h1 : l v = 0 := by rw [← hF2]; exact hv _
      have h2 : p v = 0 := hf _ fun a => by rw [← hF1]; exact hv _
      have h3 := hp v
      rw [h2, h1] at h3
      simpa using h3.symm
    have A2 : ∀ a, C a ≠ 0 := by
      intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rwa [hC2]
      · rw [hC1]; exact hc a
    have A3 : ∀ v, v ∈ Λ ↔ ∀ a, F a v ∈ C a := by
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2, hC1, hC2]
      rw [← hfΛ, hΛ', hp]
      constructor
      · intro hv
        exact ⟨Λ.sub_mem hv (hce _ (hΛc v hv)), hΛc v hv⟩
      · rintro ⟨h1, h2⟩
        have := Λ.add_mem h1 (hce _ h2)
        simpa using this
    rcases hI with hI | hI
    · refine ⟨n + 1, F, C, A1, A2, A3, ?_⟩
      intro v
      refine ⟨fun _ a ha => absurd a.2 (not_lt.2 ha), fun _ => ?_⟩
      rw [hI]; trivial
    · refine ⟨min s n, F, C, A1, A2, A3, ?_⟩
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2]
      have hh : (∀ a : Fin n, min s n ≤ ((Fin.castSucc a : Fin (n + 1)) : ℕ) → f a (p v) = 0) ↔
          (p v : V) ∈ I := by
        rw [show ((p v : V) ∈ I) ↔ p v ∈ I.comap W.subtype from Iff.rfl, hfI]
        refine forall_congr' fun a => imp_congr_left ?_
        have := a.2
        simp only [Fin.val_castSucc]
        omega
      rw [hh, hp]
      constructor
      · intro hv
        have h0 : l v = 0 := hI hv
        refine ⟨by simpa [h0] using hv, fun _ => h0⟩
      · rintro ⟨h1, h2⟩
        have h0 : l v = 0 := h2 (by simp)
        simpa [h0] using h1

end PseudoBasis

theorem exists_pseudoBasis_adapted :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (I : Submodule E (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ (s : ℕ) (e : Module.Basis (Fin r) E (Fin r → E)) (c : Fin r → FractionalIdeal (𝓞 E)⁰ E), (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, e.repr v a ∈ c a) ∧ ∀ v, v ∈ I ↔ ∀ a : Fin r, s ≤ (a : ℕ) → e.repr v a = 0 := by
  intro E _ _ r Λ I hfg hsp
  obtain ⟨s, f, c, hf, hc, hΛ, hI⟩ :=
    exists_pseudoCoords (R := 𝓞 E) (K := E) r (Fin r → E) (by simp) Λ I hfg hsp
  have hinj : Function.Injective (LinearMap.pi f) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact hf v fun a => congrFun hv a
  let φ : (Fin r → E) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofInjectiveEndo _ hinj
  have hφ : ∀ v a, (Module.Basis.ofEquivFun φ).repr v a = f a v := by
    intro v a
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  refine ⟨s, Module.Basis.ofEquivFun φ, c, hc, ?_, ?_⟩
  · simpa only [hφ] using hΛ
  · simpa only [hφ] using hI

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodChange

private theorem matrix_eq_of_dotProduct_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n] (M K : Matrix n n ℤ)
    (h : ∀ a b : n → ℤ, a ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ (K *ᵥ b)) : M = K := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

private theorem omegaStd_eq_neg_dotProduct_J {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b = -(a ⬝ᵥ (J (Fin g) ℤ *ᵥ b)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
  simp [Matrix.J, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Finset.sum_sub_distrib,
    neg_mulVec, one_mulVec, Finset.sum_neg_distrib, mul_comm]
  ring

private theorem fromBlocks_swap_mul_J_mul_swap {g : ℕ} :
    fromBlocks (0 : Matrix (Fin g) (Fin g) ℤ) 1 1 0 * J (Fin g) ℤ * fromBlocks 0 1 1 0 =
      -J (Fin g) ℤ := by
  simp [Matrix.J, fromBlocks_multiply, fromBlocks_neg]

theorem _root_.GlobalTheory.PeriodChange.swap_mem_symplectic {g : ℕ} (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hN : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd (N *ᵥ a) (N *ᵥ b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) :
    Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∈
      Matrix.symplecticGroup (Fin g) ℤ := by
  set S : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ := fromBlocks 0 1 1 0 with hS
  have hNJN : Nᵀ * J (Fin g) ℤ * N = J (Fin g) ℤ := by
    apply matrix_eq_of_dotProduct_mulVec_eq
    intro a b
    have := hN a b
    rw [omegaStd_eq_neg_dotProduct_J, omegaStd_eq_neg_dotProduct_J, neg_inj] at this
    rw [← this, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
  have hSt : Sᵀ = S := by simp [hS, fromBlocks_transpose]
  have hM : Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ =
      S * Nᵀ * S := by
    conv_rhs => rw [← fromBlocks_toBlocks N]
    simp [hS, fromBlocks_transpose, fromBlocks_multiply]
  rw [hM, SymplecticGroup.mem_iff]
  calc S * Nᵀ * S * J (Fin g) ℤ * (S * Nᵀ * S)ᵀ
      = S * (Nᵀ * ((S * J (Fin g) ℤ * S) * N)) * S := by
        simp only [transpose_mul, transpose_transpose, hSt, Matrix.mul_assoc]
    _ = -(S * (Nᵀ * J (Fin g) ℤ * N) * S) := by
        rw [fromBlocks_swap_mul_J_mul_swap]; simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    _ = J (Fin g) ℤ := by rw [hNJN, fromBlocks_swap_mul_J_mul_swap, neg_neg]

theorem _root_.GlobalTheory.PeriodChange.change_of_normalisation {g : ℕ} (h h' τ' A B L R : Matrix (Fin g) (Fin g) ℂ)
    (hA : h * L = A) (hB : h * R = B) (hL : h' * L = 1) (hR : h' * R = τ') (hs : τ'.IsSymm)
    (hu : IsUnit h.det) :
    τ' = Bᵀ * (Aᵀ)⁻¹ ∧ h' = ((Aᵀ)⁻¹)ᵀ * h ∧ h.det = (Aᵀ).det * h'.det := by
  have hL' : L = h⁻¹ * A := by
    rw [← hA, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  have hAh : h' * h⁻¹ * A = 1 := by rw [Matrix.mul_assoc, ← hL', hL]
  have hA1 : A * (h' * h⁻¹) = 1 := mul_eq_one_comm.mp hAh
  have hAu : IsUnit A.det := isUnit_det_of_right_inverse hA1
  have hAinv : A⁻¹ = h' * h⁻¹ := inv_eq_right_inv hA1
  have hh' : h' = A⁻¹ * h := by
    rw [hAinv, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc τ' = τ'ᵀ := hs.eq.symm
      _ = Bᵀ * (Aᵀ)⁻¹ := by
        rw [← hR, hh', Matrix.mul_assoc, hB, transpose_mul, transpose_nonsing_inv]
  · rw [← transpose_nonsing_inv, transpose_transpose]; exact hh'
  · have : h = A * h' := by
      rw [hh', ← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
    conv_lhs => rw [this]
    rw [det_mul, det_transpose]

private theorem addMonoidHom_eq_matrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℕ}
    (Q : (ι → ℤ) →+ (Fin g → ℂ)) (x : ι → ℤ) :
    Q x = (Matrix.of fun i u => Q (Pi.single u 1) i) *ᵥ fun u => (x u : ℂ) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  funext i
  simp only [Finset.sum_apply, mulVec, dotProduct, of_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hs : Pi.single u (x u) = x u • (Pi.single u 1 : ι → ℤ) := by
    ext v; by_cases hv : v = u <;> simp [hv]
  rw [hs, map_zsmul, Pi.smul_apply, zsmul_eq_mul, mul_comm]

theorem _root_.GlobalTheory.PeriodChange.period_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ)) (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ a, P' a = P (gam a)) → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → (∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → τ' ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → IsUnit h.det → ∃ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, γ = Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∧ τ' = _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ ∧ h' = ((_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹)ᵀ * h ∧ h.det = (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * h'.det := by
  intro E _ _ _ H D g bas gam N P P' h h' τ τ' hEF hgam hNdef hP' hnorm hnorm' hτ hτ' hu
  have hτs : τ.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ; exact hτ.1
  have hτs' : τ'.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ'; exact hτ'.1
  have hNv : ∀ a, bas (N *ᵥ a) = gam (bas a) := by
    intro a
    let f₁ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) := (Matrix.mulVecLin N).toAddMonoidHom
    let f₂ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) :=
      bas.symm.toLinearMap.toAddMonoidHom.comp
        (gam.toAddEquiv.toAddMonoidHom.comp bas.toLinearMap.toAddMonoidHom)
    have hf : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun v x => ?_
      have hs : Pi.single v x = x • (Pi.single v 1 : Fin g ⊕ Fin g → ℤ) := by
        ext u; by_cases hu : u = v <;> simp [hu]
      rw [hs, map_zsmul, map_zsmul]
      congr 1
      funext u
      simp [f₁, f₂, hNdef, mulVec_single_one]
    have := DFunLike.congr_fun hf a
    change N *ᵥ a = bas.symm (gam (bas a)) at this
    rw [this, LinearEquiv.apply_symm_apply]
  have hγ := _root_.GlobalTheory.PeriodChange.swap_mem_symplectic N fun a b => by
    have := hEF (N *ᵥ a) (N *ᵥ b)
    rw [hNv, hNv, hgam, hEF] at this
    exact (neg_inj.mp this).symm
  have hcol : ∀ v, h *ᵥ P' (bas (Pi.single v 1)) =
      fun i => (N (Sum.inl i) v : ℂ) + ∑ j, τ i j * N (Sum.inr j) v := by
    intro v
    have hPb : ∀ x, P (bas x) =
        (Matrix.of fun i u => P (bas (Pi.single u 1)) i) *ᵥ fun u => (x u : ℂ) :=
      fun x => addMonoidHom_eq_matrix_mulVec (P.comp bas.toLinearMap.toAddMonoidHom) x
    rw [hP', ← hNv, hPb, mulVec_mulVec]
    funext i
    have hc : ∀ u, (h * Matrix.of fun i u => P (bas (Pi.single u 1)) i) i u
        = (h *ᵥ P (bas (Pi.single u 1))) i := by
      intro u; simp [Matrix.mul_apply, mulVec, dotProduct]
    rw [mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [hc, (hnorm _).1, (hnorm _).2]
    simp [mulVec_single_one, Pi.single_apply]
  let A₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₁.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₁.map (fun x : ℤ => (x : ℂ))
  let B₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₂.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₂.map (fun x : ℤ => (x : ℂ))
  have hAL : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = A₀ := by
    ext i k
    have := congrFun (hcol (Sum.inl k)) i
    simp only [mulVec, dotProduct] at this
    simp [A₀, Matrix.mul_apply, this, toBlocks₁₁, toBlocks₂₁]
  have hBR : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = B₀ := by
    ext i k
    have := congrFun (hcol (Sum.inr k)) i
    simp only [mulVec, dotProduct] at this
    simp [B₀, Matrix.mul_apply, this, toBlocks₁₂, toBlocks₂₂]
  have hL1 : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = 1 := by
    ext i k
    have := congrFun (hnorm' k).1 i
    simp only [mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Matrix.one_apply, Pi.single_apply]
  have hRτ : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = τ' := by
    ext i k
    have := congrFun (hnorm' k).2 i
    simp only [mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Pi.single_apply]
  obtain ⟨e₁, e₂, e₃⟩ :=
    _root_.GlobalTheory.PeriodChange.change_of_normalisation h h' τ' A₀ B₀ _ _ hAL hBR hL1 hRτ hτs' hu
  have hj : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut (Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ) τ =
      A₀ᵀ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [A₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  refine ⟨_, hγ, rfl, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct
    rw [hj, e₁]
    congr 1
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [B₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  · rw [hj]; exact e₂
  · rw [hj]; exact e₃

end GlobalTheory.PeriodChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CongruenceIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}

omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CongruenceIndex.mul_mulVec (γ δ : GL (Fin r) E) (v : Fin r → E) :
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem _root_.GlobalTheory.CongruenceIndex.isUStab_one : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  exact ⟨fun x y => by simp, fun x => by simp⟩

theorem _root_.GlobalTheory.CongruenceIndex.isUStab_mul {γ δ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ) (hδ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ δ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ (γ * δ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec, _root_.GlobalTheory.CongruenceIndex.mul_mulVec, hγ.1, hδ.1]
  · rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec]
    exact (hδ.2 x).trans (hγ.2 _)

theorem _root_.GlobalTheory.CongruenceIndex.isUStab_inv {γ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ⁻¹ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h := hγ.1 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
    rw [_root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec, _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec] at h
    exact h.symm
  · have h := hγ.2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
    rw [_root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec] at h
    exact h.symm

def congruenceSubgroup (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | FD.IsUStab Gm Λ γ ∧
    (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)}
  one_mem' := ⟨isUStab_one, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, hγ'⟩ ⟨hδ, hδ'⟩
    refine ⟨isUStab_mul hγ hδ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hδ' v hv
    obtain ⟨w', hw', e'⟩ := hγ' _ ((hδ.2 v).1 hv)
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [mul_mulVec, e', e, smul_add, add_assoc]
  inv_mem' := by
    rintro γ ⟨hγ, hγ'⟩
    refine ⟨isUStab_inv hγ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hγ' _ (((isUStab_inv hγ).2 v).1 hv)
    rw [mulVec_inv_mulVec] at e
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact e.symm

private theorem inv_mul_mem_congruenceSubgroup_of_agree_mod {T : Finset (Fin r → E)}
    (hT : Submodule.span (𝓞 E) (T : Set (Fin r → E)) = Λ) {M : ℕ} {s γ : GL (Fin r) E}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ s) (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ)
    (h : ∀ t ∈ T, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t =
      (s : Matrix (Fin r) (Fin r) E) *ᵥ t + M • w) :
    s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by
  have hsi := _root_.GlobalTheory.CongruenceIndex.isUStab_inv hs
  refine ⟨_root_.GlobalTheory.CongruenceIndex.isUStab_mul hsi hγ, fun v hv => ?_⟩
  rw [← hT] at hv
  induction hv using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨w, hw, e⟩ := h t ht
    refine ⟨((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w, (hsi.2 w).1 hw, ?_⟩
    have hst := _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec s⁻¹ t
    rw [inv_inv] at hst
    rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec, e, Matrix.mulVec_add, hst, Matrix.mulVec_smul]
  | zero => exact ⟨0, Λ.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ex⟩ := hx
    obtain ⟨w', hw', ey⟩ := hy
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [Matrix.mulVec_add, ex, ey, smul_add]
    abel
  | smul a x _ hx =>
    obtain ⟨w, hw, ex⟩ := hx
    refine ⟨a • w, Λ.smul_mem a hw, ?_⟩
    rw [Matrix.mulVec_smul, ex, smul_add, smul_comm a M w]

theorem _root_.GlobalTheory.CongruenceIndex.exists_finset_cosets (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ →
      ∃ s ∈ S, s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by
  classical
  obtain ⟨T, hT⟩ := id hΛ
  set I : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  haveI : Subsingleton (Λ ⧸ (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  haveI : Finite (Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  let St := {γ : GL (Fin r) E // _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ}
  let Φ : St → (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := fun γ t =>
    Submodule.Quotient.mk ⟨(γ.1 : Matrix (Fin r) (Fin r) E) *ᵥ t.1,
      (γ.2.2 t.1).1 (hT ▸ Submodule.subset_span t.2)⟩
  haveI : Fintype (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := Fintype.ofFinite _
  let rep : (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) → GL (Fin r) E := fun x =>
    if h : ∃ γ : St, Φ γ = x then h.choose.1 else 1
  refine ⟨Finset.univ.image rep, fun γ hγ =>
    ⟨rep (Φ ⟨γ, hγ⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
  have hex : ∃ δ : St, Φ δ = Φ ⟨γ, hγ⟩ := ⟨_, rfl⟩
  have hrep : rep (Φ ⟨γ, hγ⟩) = hex.choose.1 := dif_pos hex
  rw [hrep]
  refine inv_mul_mem_congruenceSubgroup_of_agree_mod hT hex.choose.2 hγ (fun t ht => ?_)
  have hq := congrFun hex.choose_spec ⟨t, ht⟩
  have hmem := (Submodule.Quotient.eq _).1 hq.symm
  have hdiv : ∀ x : Λ, x ∈ I • (⊤ : Submodule (𝓞 E) Λ) → ∃ b : Λ, (M : 𝓞 E) • b = x := by
    intro x hx
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hdiv _ hmem
  refine ⟨b.1, b.2, ?_⟩
  have hb' := congrArg Subtype.val hb
  simp only [Submodule.coe_smul, Submodule.coe_sub] at hb'
  rw [Nat.cast_smul_eq_nsmul] at hb'
  rw [hb']
  abel

theorem _root_.GlobalTheory.CongruenceIndex.congruence_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → 0 < M → ∃ Γ : Subgroup (GL (Fin r) E), (∀ γ, γ ∈ Γ ↔ _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ := by
  intro E _ _ _ r M Gm Λ hΛ hM
  exact ⟨_root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M, fun γ => Iff.rfl,
    _root_.GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM⟩

end GlobalTheory.CongruenceIndex
end

module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.det_ne_zero_of_im_hermForm_eq_int : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u u).re) → LinearIndependent ℝ lam → Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 := by
  intro g r Hm lam M hpos hli hspan hM hdet
  have hdet' : (M.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have h := RingHom.map_det (Int.castRingHom ℝ) M
    rw [hdet, map_zero] at h
    exact h.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  set w : Fin g → ℂ := ∑ j, v j • lam j with hwdef
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    funext j
    exact Fintype.linearIndependent_iff.mp hli v hw j
  have hlin : ∀ x : Fin g → ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w = ∑ j, v j • _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x (lam j) := by
    intro x
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, hwdef, star_sum, star_smul, star_trivial, Matrix.mulVec_sum,
      Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]
  have hlamw : ∀ i, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) w).im = 0 := by
    intro i
    have hrow := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hrow
    rw [hlin, Complex.im_sum]
    simp only [Complex.smul_im, hM, smul_eq_mul]
    rw [← hrow]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hall : ∀ x, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hlamw i
    | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
    | add y z _ _ hy hz =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct, Complex.add_im] at hy hz ⊢
      rw [hy, hz, add_zero]
    | smul c y _ hy =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im] at hy ⊢
      rw [hy, smul_zero]
  have hI := hall (Complex.I • w)
  have hre := hpos w hw0
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add] at hI hre
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_imHermForm_integral_real_basis : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u u).re) → LinearIndependent ℝ lam → Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 := by
  first | exact @GlobalTheory.det_ne_zero_of_im_hermForm_eq_int | exact GlobalTheory.det_ne_zero_of_im_hermForm_eq_int | (intros; apply GlobalTheory.det_ne_zero_of_im_hermForm_eq_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_conj_symm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hH.apply i j
  rw [← this]
  simp only [star_star, Pi.star_apply]
  ring

noncomputable def hermFormImBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem hermForm_periods_alternating_nondeg :
    ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  intro g r x M Hm hli hsp hH hpos hM
  have hanti : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]
    rw [hermForm_conj_symm_of_isHermitian Hm hH]
    simp
  refine ⟨hanti, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z : Fin g → ℂ := ∑ j, v j • x j with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext j
      exact Fintype.linearIndependent_iff.mp hli v h0 j
    have hxi : ∀ i, hermFormImBilin Hm (x i) z = 0 := by
      intro i
      have : hermFormImBilin Hm (x i) z = ∑ j, v j * M i j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hz, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, ← hM i j]
        rfl
      rw [this]
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hall : ∀ y, hermFormImBilin Hm y z = 0 := by
      have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hxi i
      intro y
      have hy : y ∈ Submodule.span ℝ (Set.range x) := by rw [hsp]; trivial
      simpa using hle hy
    have h1 := hall (Complex.I • z)
    have h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re := by
      show (hermForm Hm (Complex.I • z) z).im = _
      simp [hermForm, smul_dotProduct]
    have := hpos z hz0
    linarith
  · have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Module.finrank_pi_fintype] at h1
    simp [Complex.finrank_real_complex] at h1
    omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  first | exact @GlobalTheory.hermForm_periods_alternating_nondeg | exact GlobalTheory.hermForm_periods_alternating_nondeg | (intros; apply GlobalTheory.hermForm_periods_alternating_nondeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem det_ne_zero_of_real_indep_isotropic : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  intro g Hm E hpos hind him
  have hL : ∀ (a : Fin g → ℝ) (w : Fin g → ℂ), hermForm Hm (∑ i, (a i : ℂ) • E i) w
      = ∑ i, (a i : ℂ) * hermForm Hm (E i) w := by
    intro a w
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hR : ∀ (b : Fin g → ℝ) (z : Fin g → ℂ), hermForm Hm z (∑ j, (b j : ℂ) • E j)
      = ∑ j, (b j : ℂ) * hermForm Hm z (E j) := by
    intro b z
    have hs : star (∑ j, (b j : ℂ) • E j) = ∑ j, (b j : ℂ) • star (E j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext k
      simp
    simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have him0 : ∀ a b : Fin g → ℝ,
      (hermForm Hm (∑ i, (a i : ℂ) • E i) (∑ j, (b j : ℂ) • E j)).im = 0 := by
    intro a b
    rw [hL]
    simp only [hR, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [Complex.mul_im, him i j]
  have hsmulL : ∀ (c : ℂ) (z w : Fin g → ℂ), hermForm Hm (c • z) w = c * hermForm Hm z w := by
    intro c z w
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have hreal : ∀ a : Fin g → ℝ, (∑ i, (a i : ℂ) • E i) = 0 → a = 0 := by
    intro a h0
    have h1 : ∑ i, a i • E i = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      simp
    have := Fintype.linearIndependent_iff.mp hind a h1
    funext i
    exact this i
  have hC : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsplit : (∑ i, (((c i).re : ℝ) : ℂ) • E i) + Complex.I • (∑ i, (((c i).im : ℝ) : ℂ) • E i) = 0 := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      exact (mul_comm Complex.I _ ▸ Complex.re_add_im (c i))
    set X := ∑ i, (((c i).re : ℝ) : ℂ) • E i with hX
    set Y := ∑ i, (((c i).im : ℝ) : ℂ) • E i with hY
    have hXY : X = (-Complex.I) • Y := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hsplit
    have hY0 : Y = 0 := by
      by_contra hne
      have hp := hpos Y hne
      have h2 := him0 (fun i => (c i).re) (fun i => (c i).im)
      change (hermForm Hm X Y).im = 0 at h2
      rw [hXY, hsmulL] at h2
      simp [Complex.mul_im] at h2
      linarith
    have hX0 : X = 0 := by rw [hXY, hY0, smul_zero]
    have hre := hreal (fun i => (c i).re) hX0
    have him' := hreal (fun i => (c i).im) hY0
    intro i
    apply Complex.ext
    · simpa using congrFun hre i
    · simpa using congrFun him' i
  have hcol : LinearIndependent ℂ (Matrix.of fun k i => E i k : Matrix (Fin g) (Fin g) ℂ).col := hC
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hcol
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  first | exact @GlobalTheory.det_ne_zero_of_real_indep_isotropic | exact GlobalTheory.det_ne_zero_of_real_indep_isotropic | (intros; apply GlobalTheory.det_ne_zero_of_real_indep_isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_relations_period_matrix : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  intro g d Hm E F τ hH hpos hF hA hFE
  have hexp : ∀ z w : Fin g → ℂ, hermForm Hm z w = ∑ x, ∑ y, z x * Hm x y * star (w y) := by
    intro z w; unfold hermForm; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Pi.star_apply]; ring
  have lin1 : ∀ (c : Fin d → ℂ) (w : Fin g → ℂ),
      hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
    intro c w
    unfold hermForm
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have symm : ∀ z w : Fin g → ℂ, hermForm Hm w z = star (hermForm Hm z w) := by
    intro z w
    simp only [hexp, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show star (Hm x y) = Hm y x from hH.apply y x]; ring
  have lin2 : ∀ (c : Fin d → ℂ) (z : Fin g → ℂ),
      hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
    intro c z
    rw [symm, lin1, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', ← symm]
  set a : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hA])
  have asymm : aᵀ = a := by
    ext i k; simp only [a, Matrix.transpose_apply, Matrix.of_apply]; rw [symm]; simp
  set Y : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).im with hY
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).re with hX
  have hYA : Yᵀ * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hF j, lin1] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, Y] using h
  have hAY : a * Y = 1 := by
    have h := congrArg Matrix.transpose hYA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, asymm, Matrix.transpose_one] at h
  have hYs : Yᵀ = Y := by
    calc Yᵀ = Yᵀ * (a * Y) := by rw [hAY, Matrix.mul_one]
    _ = (Yᵀ * a) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hYA, Matrix.one_mul]
  have e1 : ∀ i m, ∑ p, Y p i * a p m = if i = m then 1 else 0 := fun i m => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hYA i) m
  have e2 : ∀ p j, ∑ m, a p m * Y m j = if p = j then 1 else 0 := fun p j => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hAY p) j
  have ys : ∀ i j, Y i j = Y j i := fun i j => by
    simpa using (congrFun (congrFun hYs j) i)
  refine ⟨fun v hv => ?_, fun i j => ?_⟩
  · have him : (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im = v ⬝ᵥ (Y *ᵥ v) := by
      simp only [Complex.im_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Y, Complex.mul_im]; ring
    rw [him]
    set w := Y *ᵥ v with hw
    have hAw : a *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
    set Q : Fin g → ℂ := ∑ i, ((w i : ℝ) : ℂ) • E i with hQ
    have hQE : ∀ k, (hermForm Hm Q (E k)).re = v k := by
      intro k
      rw [hQ, lin1, ← hAw]
      simp only [hAr, Complex.re_sum, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.mul_re]
      rw [show a k i = a i k from by simpa using congrFun (congrFun asymm i) k]; ring
    have hQQ : (hermForm Hm Q Q).re = v ⬝ᵥ w := by
      have hl := lin2 (fun i => (w i : ℂ)) Q
      rw [← hQ] at hl
      rw [hl]
      simp only [Complex.re_sum, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hQE k]; simp [Complex.mul_re]; ring
    have hQ0 : Q ≠ 0 := by
      intro h; apply hv; funext k; rw [← hQE k, h]; simp [hermForm]
    rw [← hQQ]; exact hpos Q hQ0
  · have key : (hermForm Hm (F i) (F j)).im = X i j - X j i := by
      rw [hF i, lin1]
      simp only [hF j, lin2, hAr, Complex.im_sum, Finset.mul_sum]
      have h1 : ∀ p m, ((τ p i) * (star (τ m j) * (a p m : ℂ))).im
          = Y p i * a p m * X m j - X p i * (a p m * Y m j) := fun p m => by
        simp [Y, X, Complex.mul_im, Complex.mul_re]; ring
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, e1, e2]
      simp [X]
    apply Complex.ext
    · simp [key, X]
    · simp [Y] at ys; simp [ys j i]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relations_period_matrix_hermitian : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  first | exact @GlobalTheory.riemann_relations_period_matrix | exact GlobalTheory.riemann_relations_period_matrix | (intros; apply GlobalTheory.riemann_relations_period_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransportLimit

theorem val_frame {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} (t : Frame L p) (ht : t.IsGen) {j₀ : L.ι}
    (h₀ : ⊤ ≤ LB.wchart L (K := PUnit) (fun _ => p) (fun _ => j₀)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t r z J = gm (r ≫ p) z _ (L.g (J (r ≫ p)) j₀) * gm r z ⊤ (res h₀ (t.s (fun _ => j₀))) := by
  refine (gen_trans ht r z (hJ.mem _ r) (h₀ (show r z ∈ (⊤ : Y.Opens) from trivial))).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z h₀ (show r z ∈ (⊤ : Y.Opens) from trivial) _).symm)
  simp only [trF, Fintype.prod_unique, zpow_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem gw_change (U : UnifPre I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.toPre.P.A.left} (hp : xe ≫ (fstG I e G).left = p)
    (hq : xe ≫ (U.gt e).pG.left = q) {j j' : D.toPre.P.L.ι} {k k' : U.LG.L.ι} (hj : q z ∈ D.toPre.P.L.U j)
    (hj' : q z ∈ D.toPre.P.L.U j') (hk : p z ∈ U.LG.L.U k) (hk' : p z ∈ U.LG.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.toPre.P.L.g j j') * (gm p z _ (U.LG.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk)
    (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_limit_unit (U : UnifPre I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.toPre.P.A.left)
    (hb : Lies U x b) {jL : U.LG.L.ι} {jM : D.toPre.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ b ⁻¹ᵁ D.toPre.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using GlobalTheory.FormalValue.exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.LG.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.LG.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.toPre.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.toPre.P.L.U jM) (hb e Z r xe h)).mpr
      (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from GlobalTheory.thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (GlobalTheory.FormalValue.toStkA_map_valR _ _ _ _ (ht _) _).trans
      (Eq.trans ?_ (GlobalTheory.FormalValue.toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact GlobalTheory.FormalValue.wv_comp_thickMap e (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := GlobalTheory.FormalValue.exists_unit_limit (I.map φ) _ hc fun e =>
    GlobalTheory.FormalValue.isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := GlobalTheory.NormGen.exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, GlobalTheory.NormGen.gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1,
    map_one, map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← GlobalTheory.NormGen.gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := GlobalTheory.FormalValue.valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [GlobalTheory.NormGen.valR_id, Category.comp_id] at k
  exact k

theorem exists_frRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] [IsLocalRing W] (φ : R →+* W) [IsAdicComplete (I.map φ) W] (x' : Sp W ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ b : Sp W ⟶ D.toPre.P.A.left, Lies U x' b → ∃ (g' : Frame U.LG.L x') (g : Frame D.toPre.P.L b), g'.IsGen ∧ g.IsGen ∧ FrRel U x' b g' g := by
  intro R _ _ I D A G _ _ U W _ _ φ _ x' hx b hb
  obtain ⟨jL, hjL⟩ := exists_chart U.LG.isLB (x' (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.toPre.P.isLB (b (cpt W))
  replace hjL := (top_le_iff_cpt (A := W) x' _).2 hjL
  replace hjM := (top_le_iff_cpt (A := W) b _).2 hjM
  obtain ⟨a, ha⟩ := exists_limit_unit U φ x' hx b hb hjL hjM
  obtain ⟨ν', hν'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) U.LG.L U.LG.isLB (K := PUnit) (fun _ => x') (fun _ => 1)
  obtain ⟨ν, hν⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) D.toPre.P.L D.toPre.P.isLB (K := PUnit) (fun _ => b) (fun _ => 1)
  have tL : ⊤ ≤ LB.wchart U.LG.L (K := PUnit) (fun _ => x') (fun _ => jL) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjL (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  have tM : ⊤ ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => b) (fun _ => jM) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjM (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  refine ⟨GlobalTheory.UU.scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν', GlobalTheory.UU.scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν,
    GlobalTheory.UU.scaleGen_isGen _ hν', GlobalTheory.UU.scaleGen_isGen _ hν, ?_⟩
  intro e Z r y hy z JM JL hJM hJL
  have hyb := hb e Z r y hy
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h =>
    h (show r z ∈ (⊤ : (Sp W).Opens) from trivial)
  have v₁ := GlobalTheory.UU.val_scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν' r hJL
  rw [val_frame ν' hν' tL r z hJL] at v₁
  have v₂ := GlobalTheory.UU.val_scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν r hJM
  rw [val_frame ν hν tM r z hJM] at v₂
  have w₁ : wVal U e z JM JL y = gm (r ≫ b) z _ (D.toPre.P.L.g (JM (r ≫ b)) jM) *
      (gm (r ≫ x') z _ (U.LG.L.g (JL (r ≫ x')) jL))⁻¹ * gw (U.w e) y z jM (fun _ => jL) :=
    (congrArg₂ (fun j k => gw (U.w e) y z (JM j) (fun _ => JL k)) hyb hy).trans
      (gw_change U e y z hy hyb (hJM _) (m hjM) (hJL _) (m hjL))
  rw [eq_inv_of_mul_eq_one_right (ha e Z r y hy z)] at w₁
  rw [v₁, v₂, w₁]
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TransportLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv.Transport

section Helpers

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_fn_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = gs r z ⊤ a := by
  obtain ⟨t, hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) s
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, sval_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

theorem mem_pow_of_gs {W : Type} [CommRing W] (J : Ideal W) (n : ℕ) (a : W)
    (h : ∀ z, gs (adicLevelι J n) z ⊤ (toΓ W a) = 0) : a ∈ J ^ n := by
  have h1 : (adicLevelι J n).appTop.hom (toΓ W a) = 0 := fn_ext (V := ⊤) fun z _ =>
    (gs_pull (𝟙 _) (adicLevelι J n) z ⊤ trivial _).trans (by
      rw [Category.id_comp, h z]; exact (DVR.gs_zero (𝟙 _) z ⊤ trivial).symm)
  have h2 := congrArg (fun q => q.hom (toΓ W a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [h1, map_zero] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (toΓ W a) = a := by
    simp only [toΓ]; exact Iso.inv_hom_id_apply _ _
  rw [h3] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

theorem toΓ_hom {W : Type} [CommRing W] (a : Γ(Sp W, ⊤)) :
    toΓ W ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) = a := by
  simp only [toΓ]; exact Iso.hom_inv_id_apply _ _

end Helpers

theorem exists_adic_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  intro R _ _ I D A G _ _ U W _ φ ξ x' hx b hb g' g hg' hg hfr k σ F hexp
  subst hb
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB

  obtain ⟨a, ha⟩ := exists_fn_of_formal hL
    (φ := Sum.elim (fun _ : Fin 1 => x'.left ≫ 𝟙 G.left) (fun _ : PUnit.{1} => x'.left))
    (ε := Sum.elim (fun _ => (k : ℤ)) (fun _ => -((k : ℤ) * 1)))
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec σ x'.left (LB.invGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ g' k))
      (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg' k)))
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL →
      sval σ (r ≫ x'.left) z JL = gs r z ⊤ a * (val g' r z JL ^ k).val := by
    intro Z r z JL hJL
    have e₁ := (ha Z r z JL hJL).symm.trans (sval_pullMulSec σ x'.left _ _ r z hJL)
    rw [val_inv, show val (GeneratorPullback.powGen U.LG.L _ _ g' k) r z JL = val g' r z JL ^ k from map_pow _ _ _] at e₁
    rw [e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

  have ht : ∀ α, ∃ c : Γ(Sp W, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM →
      sval (F α) (r ≫ ξ.b.left) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ c * (val g r z JM ^ k).val := by
    intro α
    obtain ⟨c, hc⟩ := exists_fn_of_formal hM
      (φ := Sum.elim (fun i => ξ.b.left ≫ D.toPre.famφB α i)
        (Sum.elim (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α) (fun _ : PUnit.{1} => ξ.b.left)))
      (ε := Sum.elim (DegPre.famε k) (Sum.elim DegPre.gtε (fun _ => -((k : ℤ) * 1))))
      (fun U _ h => by
        have e := GlobalTheory.ConstTerm.prod_factors (fun i => h (ξ.b.left ≫ D.toPre.famφB α i)) k
        have e₀ : ∀ i, h (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α i) =
            ![h (ξ.b.left ≫ D.toPre.famφB α 1), h (ξ.b.left ≫ D.toPre.famφB α 2),
              h (ξ.b.left ≫ D.toPre.famφB α 0), h (ξ.b.left ≫ D.toPre.famφB α 3)] i := by
          intro i
          fin_cases i <;> simp [GlobalTheory.ConstTerm.comp_famφB]
        simp only [← e₀] at e
        have e₁ : ξ.b.left ≫ D.toPre.famφB α 0 = ξ.b.left := Category.comp_id _
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← _root_.mul_assoc, e, e₁]
        simp)
      (pullMulSec (F α) ξ.b.left
        (LB.mulGen D.toPre.P.L _ _ _ _ (ξ.s α) (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ g k)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (ξ.isGen α)
          (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg k))))
    refine ⟨c, fun Z r z JM hJM => ?_⟩
    have e₁ := (hc Z r z JM hJM).symm.trans (sval_pullMulSec (F α) ξ.b.left _ _ r z hJM)
    rw [val_mul hJM, val_inv,
      show val (GeneratorPullback.powGen D.toPre.P.L _ _ g k) r z JM = val g r z JM ^ k from map_pow _ _ _] at e₁
    rw [e₁, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  choose c hc using ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a,
    fun α => (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (c α), fun Z r z JL hJL => ?_,
    fun α Z r z JM hJM => ?_, fun e => ?_⟩
  · rw [toΓ_hom]; exact h1 Z r z JL hJL
  · rw [toΓ_hom]; exact hc α Z r z JM hJM
  · set J := I.map φ
    obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ F (hexp e)
    have hy₁ : reduction I x' e ≫ fGl I G e = adicLevelι J (e + 1) ≫ x'.left := reduction_fstG I x' e
    obtain ⟨hy₂, hy₃⟩ := (hasCoords_iff U e ξ _ _).1 (hx e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁)
    have gM : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JM, Good D.toPre.P.L z JM := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart hM (ψ z)
      exact ⟨C, hC⟩
    have gL : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JL, Good U.LG.L z JL := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ G.left => exists_chart hL (ψ z)
      exact ⟨C, hC⟩
    refine ⟨S, fun α hα => mem_pow_of_gs J (e + 1) _ fun z => ?_, mem_pow_of_gs J (e + 1) _ fun z => ?_⟩
    · obtain ⟨JM, hJM⟩ := gM z
      have h0 := (hS _ (reduction I x' e) z JM hJM).1 α hα
      rw [hy₂] at h0
      have h2 := hc α _ (adicLevelι J (e + 1)) z JM hJM
      rw [h0, zero_mul] at h2
      rw [toΓ_hom]
      exact (Units.mul_left_eq_zero _).1 h2.symm
    · obtain ⟨JM, hJM⟩ := gM z
      obtain ⟨JL, hJL⟩ := gL z
      have hE := (hS _ (reduction I x' e) z JM hJM).2 (JL (reduction I x' e ≫ fGl I G e)) (hJL _)
      have hw := hfr e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁ z JM JL hJM hJL
      have hsv : DVR.sv U k σ (reduction I x' e ≫ fGl I G e) z (JL (reduction I x' e ≫ fGl I G e)) =
          sval σ (adicLevelι J (e + 1) ≫ x'.left) z JL := by
        rw [← hy₁]; exact (sval_of σ _ z JL _ fun _ => by rw [Category.comp_id]).symm
      have hwv : DVR.wv U e (reduction I x' e) z (JM (reduction I x' e ≫ pGl U e))
          (JL (reduction I x' e ≫ fGl I G e)) = wVal U e z JM JL (reduction I x' e) := rfl
      have hterm : ∀ α ∈ S, sval (F α) (reduction I x' e ≫ pGl U e) z JM *
          (val (DVR.tG U e α) (reduction I x' e) z JM).val =
          gs (adicLevelι J (e + 1)) z ⊤ (c α) * (val g (adicLevelι J (e + 1)) z JM ^ k).val := fun α _ => by
        rw [hy₃ α z JM hJM, hy₂]; exact hc α _ _ z JM hJM
      rw [hsv, h1 _ _ z JL hJL, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwv, hw, mul_pow,
        Units.val_mul] at hE
      have hfin : gs (adicLevelι J (e + 1)) z ⊤ a = ∑ α ∈ S, gs (adicLevelι J (e + 1)) z ⊤ (c α) := by
        refine (Units.mul_left_inj (wVal U e z JM JL (reduction I x' e) ^ k *
          val g' (adicLevelι J (e + 1)) z JL ^ k)).1 ?_
        rw [Units.val_mul]
        linear_combination hE
      have gsub : ∀ x y : Γ(Sp W, ⊤), gs (adicLevelι J (e + 1)) z ⊤ (x - y) =
          gs (adicLevelι J (e + 1)) z ⊤ x - gs (adicLevelι J (e + 1)) z ⊤ y := fun x y => by
        simp only [gs_eq _ z ⊤ trivial, map_sub]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, toΓ_hom, gsub, DVR.gs_fsum _ z ⊤ trivial, hfin, sub_eq_zero]
      exact Finset.sum_congr rfl fun α _ => by rw [toΓ_hom]

end GlobalTheory.RayEv.Transport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
noncomputable section

open Matrix

namespace GlobalTheory.RedTh

structure IsSiegel {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Prop where

  nonneg : ∀ i, 0 ≤ d i

  step : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q

  diag : ∀ i, u i i = 1

  lower : ∀ i j, j < i → u i j = 0

  upper : ∀ i j, i < j → |u i j| ≤ 1 / 2

def gram {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := uᵀ * diagonal d * u

section Act

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {n : ℕ}

def actMat (b : Module.Basis (Fin n) ℤ X) : O →+* Matrix (Fin n) (Fin n) ℤ :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom).comp (Module.toModuleEnd ℤ X)

theorem actMat_apply (b : Module.Basis (Fin n) ℤ X) (c : O) (i j : Fin n) : actMat b c i j = b.repr (c • b j) i := by
  show LinearMap.toMatrixAlgEquiv b (Module.toModuleEnd ℤ X c) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

end Act

end GlobalTheory.RedTh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pushEx_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have hw : ∀ (b : Fin 0 → ℂ) (z : Fin g → ℂ), (Fu.ex i P z).left ≫ Xo.univ.t.G.hom =
      (fun _ => y) b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := fun _ z => by
    rw [Over.w (Fu.ex i P z), ← hu]; rfl
  have h2 := GlobalTheory.TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ
    (fun (_ : Fin 0 → ℂ) z => (Fu.ex i P z).left) (fun _ => y) h1
    (GlobalTheory.TrueCx.TorHolo.isHolTo_const isOpen_univ y) hw
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_hol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  first | exact @GlobalTheory.familyIsotropicDual_linearIndependent_and_card | exact GlobalTheory.familyIsotropicDual_linearIndependent_and_card | (intros; apply GlobalTheory.familyIsotropicDual_linearIndependent_and_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSnd
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

section Group

variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem tan_le (h : IsGrpPullback G' G x φ) (w : epsR S ⟶ G') (hw : IsTangent w) (V : G.left.Opens)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) : ⊤ ≤ (w.left ≫ φ) ⁻¹ᵁ V := by
  unfold IsTangent at hw
  rw [GlobalTheory.ArcLie.le_iff_fst, ← Category.assoc, hw]
  exact hV

theorem comb_snd [IsCommMonObj G'] (h : IsGrpPullback G' G x φ) {n : ℕ} (v : Fin n → (epsR S ⟶ G'))
    (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) (w : epsR S ⟶ G') (hc : IsLieComb c v w) (V : G.left.Opens)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    (valR (w.left ≫ φ) V f).snd = ∑ k, c k * (valR ((v k).left ≫ φ) V f).snd := by
  obtain ⟨u, hu, hp⟩ := (ReciprocityTheory.ChartRestriction.G.Chart.comb_push h c v w).1 hc
  have e1 : (show Sp S ⟶ G'.left from (1 : Over.mk (𝟙 (Sp S)) ⟶ G').left) = (η[G']).left := by
    have : (1 : Over.mk (𝟙 (Sp S)) ⟶ G') = η[G'] := by
      rfl
    rw [this]
  have key := GlobalTheory.ArcLie.snd_comb_lift h (x' := 𝟙 (Sp S)) (Category.id_comp x) (fun k => (v k).left)
    (fun k => by rw [Category.comp_id]; exact Over.w (v k)) (fun k => (ReciprocityTheory.ChartRestriction.G.Chart.tan_push h (v k)).1 (hv k))
    c w.left (by rw [Category.comp_id]; exact Over.w w) u hu hp (φ ⁻¹ᵁ V) (by rw [e1]; exact hV) ((φ.app V).hom f)
  rw [GlobalTheory.HolHom.valR_comp, key]
  exact Finset.sum_congr rfl fun k _ => by rw [GlobalTheory.HolHom.valR_comp]

end Group

end GlobalTheory.ArcLieCoord
end
end

module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
  (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem fock_hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, mulVec_add, add_dotProduct]

theorem fock_hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, mulVec_add, star_add, dotProduct_add]

theorem fock_hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem fock_hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul]
  rfl

theorem fock_hx_zero_right (z : Fin g → ℂ) : hx X bas idx x z 0 = 0 := by
  simp [hx]

theorem fock_hx_differentiable (w : Fin g → ℂ) : Differentiable ℂ fun z => hx X bas idx x z w := by
  simp only [hx, dotProduct, mulVec]
  fun_prop

theorem fock_hx_conj (hs : IsSympl X bas) (hd : x ∈ X.dom) (z w : Fin g → ℂ) :
    hx X bas idx x w z = conj (hx X bas idx x z w) := by
  have h := imInv_isSymm idx hs hd
  have hr : ∀ i j, conj (imInv X bas idx x i j) = imInv X bas idx x j i := by
    intro i j
    rw [h.apply i j]
    simp [ThFr.imInv]
  simp only [hx]
  generalize hMat X bas idx x *ᵥ z = u
  generalize hMat X bas idx x *ᵥ w = v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply, hr, RCLike.star_def,
    conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem fock_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), (∀ a b, fock X bas idx x k a (fock X bas idx x k b θ) = cexp (-((k : ℂ) * Real.pi * I * ((hx X bas idx x a b).im : ℂ))) • fock X bas idx x k (a + b) θ) ∧ fock X bas idx x k 0 θ = θ ∧ (∀ (N : ℕ) a, fock X bas idx x (N ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock X bas idx x 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ (Differentiable ℂ θ → ∀ a, Differentiable ℂ (fock X bas idx x k a θ)) ∧ ∀ (th : Fin n → (Fin g → ℂ) → ℂ) (κ : ℂ) (φ : TF n g), IsSB φ → (∀ z : Fin n → Fin g → ℂ, ∏ b, th b (z b) = κ * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x 1 (pv X idx x (y b)) (th b) (z b) = κ * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hs hn x hd k θ
  refine ⟨fun a b => ?_, ?_, fun N a => ?_, fun hθ a => ?_, fun th κ φ hφ h y z => ?_⟩
  · funext z
    simp only [fock, Pi.smul_apply, smul_eq_mul]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    rw [add_assoc z a b]
    congr 2
    simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left, smul_add]
    rw [fock_hx_conj X bas idx x hs hd a b]
    have := Complex.sub_conj (hx X bas idx x a b)
    push_cast at this
    linear_combination (-(k : ℂ) * Real.pi / 2) * this
  · funext z
    simp [fock, fock_hx_zero_right]
  · funext z
    simp only [fock, smul_add]
    congr 2
    simp only [fock_hx_add_left, fock_hx_smul_left, fock_hx_smul_right, map_natCast]
    push_cast
    ring
  · have h1 := fock_hx_differentiable X bas idx x a
    unfold fock
    refine Differentiable.mul (Differentiable.cexp (Differentiable.neg (Differentiable.const_mul ?_ _))) ?_
    · exact h1.comp (differentiable_id.add_const _)
    · exact hθ.comp (differentiable_id.add_const _)
  · rw [((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hd z]
    simp only [fock, Finset.prod_mul_distrib]
    rw [h fun b => z b + pv X idx x (y b), ← Complex.exp_sum, mul_left_comm]
    congr 2
    simp only [hx, pv, Finset.mul_sum, Finset.sum_neg_distrib, Nat.cast_one, _root_.one_mul]

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

noncomputable def spOf (γ : GL (Fin r) E) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ :=
  Matrix.of fun p q => crd X bas (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
    ((bas (Pi.single p.swap 1) : X.Λ) : Fin r → E)) q.swap


omit [NumberField E] [IsCMField E] in
theorem gl_mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

variable {X bas}

theorem IsUn.lact_mem {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by

  have hent : ∀ a b, ∑ c, ∑ d, (γ : Matrix (Fin r) (Fin r) E) c a * X.Gm c d *
      cc ((γ : Matrix (Fin r) (Fin r) E) d b) = X.Gm a b := by
    intro a b
    have h := hγ (Pi.single a 1) (Pi.single b 1)
    simpa [herm, Matrix.mulVec, dotProduct, Pi.single_apply, cc] using h

  have key : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    intro τ
    ext a b
    have h := congrArg τ.1 (hent a b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, cc, NumberField.IsCMField.complexEmbedding_complexConj] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact h

  have hgram : ∀ (τ : X.Ψ) (m : Matrix (Fin r) (Fin r) ℂ),
      gram τ.1 X.Gm m = mᵀ * X.Gm.map τ.1 * m.map (starRingEnd ℂ) := by
    intro τ m
    ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmat : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    intro τ
    have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [hm, hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    calc (mat x τ)ᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
          (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) *
            (mat x τ).map (starRingEnd ℂ))
        = (mat x τ)ᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) *
            (mat x τ).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
      _ = (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by rw [key]
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  refine ⟨?_, fun i => ?_⟩
  · have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [hm, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero τ.1).mpr (Matrix.isUnits_det_units γ).ne_zero) hdet
  · simpa only [dmin, hmat τ] using hpos i

theorem spOf_mem (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    spOf X bas γ ∈ Matrix.symplecticGroup (Fin g) ℚ := by

  have hinv : ∀ u v : Fin r → E, EF X (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF X u v := by
    intro u v
    have h := hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
    rw [gl_mulVec_inv_mulVec, gl_mulVec_inv_mulVec] at h
    rw [EF_def, EF_def, h]

  have hrow : ∀ p p' : Fin g ⊕ Fin g,
      ∑ i, (spOf X bas γ p (Sum.inr i) * spOf X bas γ p' (Sum.inl i) -
        spOf X bas γ p (Sum.inl i) * spOf X bas γ p' (Sum.inr i)) =
      ((omegaStd (Pi.single p.swap 1 : Fin g ⊕ Fin g → ℤ) (Pi.single p'.swap 1) : ℤ) : ℚ) := by
    intro p p'
    have h := hinv (bas (Pi.single p.swap 1)) (bas (Pi.single p'.swap 1))
    rw [EF_crd hs, hs] at h
    simp only [spOf, Matrix.of_apply, Sum.swap_inl, Sum.swap_inr]
    linarith
  rw [SymplecticGroup.mem_iff]
  ext p p'
  have hJl : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inl j) = spOf X bas γ p (Sum.inr j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  have hJr : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inr j) = -spOf X bas γ p (Sum.inl j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hJl, hJr, Matrix.transpose_apply, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    ← Finset.sum_sub_distrib]
  rw [hrow]
  rcases p with i | i <;> rcases p' with j | j <;>
    simp [omegaStd, Pi.single_apply, Matrix.J, Matrix.one_apply, eq_comm]

theorem hMat_mul_perMat_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : Fin g → Fin g ⊕ Fin g) :
    hMat X bas idx x * perMat X bas idx s (lact γ x) =
      (qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inl j)) * tauMat X bas idx x +
        qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inr j)))ᵀ := by
  have hsym := tauMat_isSymm (idx := idx) hs hx
  ext i k
  have hcol : (fun l => perMat X bas idx s (lact γ x) l k) =
      per X x (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)) ∘ idx := by
    funext l
    rw [perMat_apply, Function.comp_apply,
      ← per_lact x hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)), gl_mulVec_inv_mulVec]
  have hlhs : (hMat X bas idx x * perMat X bas idx s (lact γ x)) i k =
      (hMat X bas idx x *ᵥ fun l => perMat X bas idx s (lact γ x) l k) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hlhs, hcol, hMat_mulVec_per_crd (idx := idx) hs hx]
  simp only [spOf, qm, qv, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, Pi.add_apply,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Sum.swap_swap, Sum.swap_inl,
    Sum.swap_inr]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym.apply]
  ring

theorem periods_lact_symplectic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∃ σ ∈ Matrix.symplecticGroup (Fin g) ℚ, ∀ x ∈ X.dom, lact γ x ∈ X.dom ∧ tauMat X bas idx x ∈ Siegel (Fin g) ∧ tauMat X bas idx (lact γ x) = spAct σ (tauMat X bas idx x) ∧ hMat X bas idx (lact γ x) = ((spDen σ (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
  intro E _ _ _ r X g bas idx n hs _ γ hγ
  refine ⟨spOf X bas γ, spOf_mem hs hγ, fun x hx => ?_⟩
  have hx' := IsUn.lact_mem hγ hx
  have hD : hMat X bas idx x * perMat X bas idx Sum.inl (lact γ x) =
      (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inl
  have hN : hMat X bas idx x * perMat X bas idx Sum.inr (lact γ x) =
      (qm (spOf X bas γ).toBlocks₁₁ * tauMat X bas idx x + qm (spOf X bas γ).toBlocks₁₂)ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inr
  have hH := isUnit_det_hMat (idx := idx) hs hx
  have hP := isUnit_det_perMat (idx := idx) hs hx'
  have hPeq : perMat X bas idx Sum.inl (lact γ x) =
      (hMat X bas idx x)⁻¹ * (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    rw [← hD, Matrix.nonsing_inv_mul_cancel_left _ _ hH]
  have hh : hMat X bas idx (lact γ x) =
      ((spDen (spOf X bas γ) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
    change (perMat X bas idx Sum.inl (lact γ x))⁻¹ = _
    rw [hPeq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hH, Matrix.transpose_nonsing_inv]
  refine ⟨hx', ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩, ?_, hh⟩
  have ht : tauMat X bas idx (lact γ x) = (spAct (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    change hMat X bas idx (lact γ x) * perMat X bas idx Sum.inr (lact γ x) = _
    rw [hh, Matrix.mul_assoc, hN, spAct, Matrix.transpose_mul]
  have hsym := tauMat_isSymm (idx := idx) hs hx'
  rw [← hsym, ht, Matrix.transpose_transpose]

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
namespace GlobalTheory.Dict

section General
open Filter Topology

theorem const_of_norm_factor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {U : Set V}
    (hU : IsOpen U) (hc : IsPreconnected U) {J : Type*} (R T : J → V → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hR : ∀ i, DifferentiableOn ℂ (R i) U) (hT : ∀ i, DifferentiableOn ℂ (T i) U)
    (h : ∀ x ∈ U, ∃ k : ℂ, ‖k‖ = ρ ∧ ∀ i, R i x = k * T i x) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ U, R i x = C * T i x := by
  by_cases hz : ∀ i, ∀ x ∈ U, T i x = 0
  ·
    refine ⟨(ρ : ℂ), Complex.ofReal_ne_zero.mpr hρ.ne', fun i x hx => ?_⟩
    obtain ⟨k, -, hk⟩ := h x hx
    rw [hk i, hz i x hx, mul_zero, mul_zero]
  simp only [not_forall, exists_prop] at hz
  obtain ⟨j, x0, hx0, hTj⟩ := hz

  have hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ T j y ≠ 0 :=
    (hU.eventually_mem hx0).and (((hT j).continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne hTj)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsub : Metric.ball x0 ε ⊆ U := fun y hy => (hball y hy).1

  have hqd : DifferentiableOn ℂ (fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) := fun y hy =>
    (((hR j).mono hsub) y hy).mul ((((hT j).mono hsub) y hy).inv (hball y hy).2)
  have hqk : ∀ y ∈ Metric.ball x0 ε, ∀ k : ℂ, (∀ i, R i y = k * T i y) → R j y * (T j y)⁻¹ = k := by
    intro y hy k hk
    rw [hk j, mul_inv_cancel_right₀ (hball y hy).2]
  have hqn : ∀ y ∈ Metric.ball x0 ε, ‖R j y * (T j y)⁻¹‖ = ρ := by
    intro y hy
    obtain ⟨k, hkn, hk⟩ := h y (hsub hy)
    rw [hqk y hy k hk, hkn]
  have hx0b : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
  have hmax : IsMaxOn (norm ∘ fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) x0 :=
    isMaxOn_iff.mpr fun y hy => by
      simp only [Function.comp_apply]
      rw [hqn y hy, hqn x0 hx0b]

  have hqc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x0 ε).isPreconnected
    Metric.isOpen_ball hqd hx0b hmax
  set C : ℂ := R j x0 * (T j x0)⁻¹ with hCdef
  have hCn : ‖C‖ = ρ := hqn x0 hx0b
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hCn
    exact hρ.ne' hCn.symm
  have hloc : ∀ y ∈ Metric.ball x0 ε, ∀ i, R i y = C * T i y := by
    intro y hy i
    obtain ⟨k, -, hk⟩ := h y (hsub hy)
    have hqy : R j y * (T j y)⁻¹ = C := hqc hy
    rw [hk i, ← hqk y hy k hk, hqy]

  let S : Set V := {x | ∀ᶠ y in 𝓝 x, ∀ i, R i y = C * T i y}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hx0S : x0 ∈ S := Filter.eventually_of_mem (Metric.ball_mem_nhds x0 hε) hloc
  have hcl : closure S ∩ U ⊆ S := by
    rintro y ⟨hyS, hyU⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU y hyU
    have hδ4 : 0 < δ / 4 := by linarith
    obtain ⟨x1, hx1S, hdist⟩ := Metric.mem_closure_iff.mp hyS (δ / 4) hδ4
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y hδ4) fun z hz i => ?_

    have hφD : ∀ t ∈ Metric.ball (0 : ℂ) (3 / 2), x1 + t • (z - x1) ∈ Metric.ball y δ := by
      intro t ht
      have ht' : ‖t‖ < 3 / 2 := by simpa using ht
      have hx1' : ‖x1 - y‖ < δ / 4 := by rw [← dist_eq_norm, dist_comm]; exact hdist
      have hz' : ‖z - y‖ < δ / 4 := by rw [← dist_eq_norm]; exact hz
      have hw : ‖z - x1‖ ≤ ‖z - y‖ + ‖x1 - y‖ := by
        calc ‖z - x1‖ = ‖(z - y) - (x1 - y)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖x1 - y‖ := norm_sub_le _ _
      have htw : ‖t • (z - x1)‖ ≤ 3 / 2 * ‖z - x1‖ := by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖x1 + t • (z - x1) - y‖ = ‖(x1 - y) + t • (z - x1)‖ := by congr 1; abel
        _ ≤ ‖x1 - y‖ + ‖t • (z - x1)‖ := norm_add_le _ _
        _ < δ := by linarith
    have hφc : Continuous fun t : ℂ => x1 + t • (z - x1) := by fun_prop

    have hgd : DifferentiableOn ℂ (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1)))
        (Metric.ball (0 : ℂ) (3 / 2)) := by
      intro t ht
      have hmem : x1 + t • (z - x1) ∈ U := hδU (hφD t ht)
      have hlin : DifferentiableAt ℂ (fun t : ℂ => x1 + t • (z - x1)) t := by fun_prop
      have h1 : DifferentiableAt ℂ (R i) (x1 + t • (z - x1)) := (hR i).differentiableAt (hU.mem_nhds hmem)
      have h2 : DifferentiableAt ℂ (T i) (x1 + t • (z - x1)) := (hT i).differentiableAt (hU.mem_nhds hmem)
      exact ((h1.comp t hlin).sub ((h2.comp t hlin).const_mul C)).differentiableWithinAt

    have htend : Filter.Tendsto (fun t : ℂ => x1 + t • (z - x1)) (𝓝 0) (𝓝 x1) :=
      hφc.tendsto' 0 x1 (by simp)
    have hg0 : (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1))) =ᶠ[𝓝 0] 0 :=
      (htend.eventually hx1S).mono fun t ht => by
        simp only [Pi.zero_apply]
        rw [ht i, sub_self]

    have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (3 / 2) := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; norm_num
    have hg1 := (hgd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (3 / 2)).isPreconnected (Metric.mem_ball_self (by norm_num)) hg0 h1mem
    have hz1 : x1 + (1 : ℂ) • (z - x1) = z := by rw [one_smul, add_sub_cancel]
    simp only [Pi.zero_apply, hz1] at hg1
    exact sub_eq_zero.mp hg1
  have hUS : U ⊆ S := hc.subset_of_closure_inter_subset hSo ⟨x0, hx0, hx0S⟩ hcl
  exact ⟨C, hC0, fun i x hx => (hUS hx).self_of_nhds i⟩

end General

end GlobalTheory.Dict

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem bchar_ne_zero_of_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : Wt Ψ r)
    {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  unfold bchar
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_

  have htri : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hdet := (hb τ).1
  rw [Matrix.det_of_isUpperTriangular htri] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

private theorem abs_psgn' (p0 n : ℕ) : |psgn p0 n| = 1 := by
  rw [psgn, Finset.abs_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> simp

private theorem dmin_eq_psgn_of_gram_diagonal {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
    {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) (τ : Ψ)
    (hx : gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (i : Fin (r + 1)) : dmin G x τ i = ((psgn p0 i : ℝ) : ℂ) := by
  rw [dmin, lminor, hx, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
    Complex.ofReal_prod, Finset.prod_range]
  simp

theorem exists_unitFr_rmul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ IsUnitFr X (rmul x b) := by
  obtain ⟨x₀, b, hb, hgram, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.ofReal_re]
    have h1 := abs_psgn' X.p0 i
    refine mul_self_pos.mpr fun h0 => ?_
    rw [h0, abs_zero] at h1
    exact zero_ne_one h1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.norm_real, Real.norm_eq_abs, abs_psgn']

theorem const_of_norm_factor_unitFr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (Jx : Type) (R T : Jx → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ → (∀ i, DifferentiableOn ℂ (R i) X.dom ∧ DifferentiableOn ℂ (T i) X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, R i (rmul x b) = bchar la b * R i x ∧ T i (rmul x b) = bchar la b * T i x) → (∀ x ∈ X.dom, IsUnitFr X x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x) → ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ X.dom, R i x = C * T i x := by
  intro E _ _ _ r X la Jx R T ρ hρ hRT hunit
  have hcd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    unfold mat
    fun_prop
  have hopen : IsOpen X.dom := by
    show IsOpen {x | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (hcd τ i))))
  have hconn : IsPreconnected X.dom := (GlobalTheory.frames_isConnected E r X).isPreconnected
  refine const_of_norm_factor hopen hconn R T ρ hρ (fun i => (hRT i).1) (fun i => (hRT i).2.1) ?_

  intro x hx
  obtain ⟨b, hb, hxb, hu⟩ := exists_unitFr_rmul X hx
  obtain ⟨κ, hκ, hRTκ⟩ := hunit _ hxb hu
  refine ⟨κ, hκ, fun i => ?_⟩
  have hne := bchar_ne_zero_of_mem_bor la hb
  have h1 := hRTκ i
  rw [((hRT i).2.2 x hx b hb).1, ((hRT i).2.2 x hx b hb).2] at h1
  apply mul_left_cancel₀ hne
  rw [h1]
  ring

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColPoly

section Deriv

variable {σ κ W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

theorem polyDeriv_comp_linear {F : W' → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (A : W →L[ℂ] W')
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) :
    I2.polyDeriv P u (fun z => F (A z)) x = I2.polyDeriv P (fun l => A (u l)) F (A x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hcomp := A.iteratedFDeriv_comp_right hF x
    (i := Multiset.card (Finsupp.toMultiset m)) (by exact_mod_cast le_top)
  rw [show (fun z => F (A z)) = F ∘ A from rfl, hcomp]
  rfl

private theorem polyDeriv_C_indep (a : ℂ) (u v : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) u F x =
      I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) v F x := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
  subst hm0
  congr 1

theorem polyDeriv_subst [Fintype κ] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [MvPolynomial.algHom_C]
    exact polyDeriv_C_indep a _ _ F x
  | add p q hp hq => rw [map_add (f := _), I2.polyDeriv_add, I2.polyDeriv_add, hp, hq]
  | mul_X p l hp =>
    have e1 : (fun y => I2.polyDeriv (Φ p) u F y) =
        fun y => I2.polyDeriv p (fun l => ∑ k, s l k • u (j l k)) F y := funext hp
    rw [polyDeriv_mul_X hF p _ l x, map_mul, hΦ l, Finset.mul_sum, I2.jof_polyDeriv_sum]
    simp_rw [MvPolynomial.C_mul', mul_smul_comm, I2.polyDeriv_smul, polyDeriv_mul_X hF (Φ p) u _ x, e1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, smul_eq_mul]

end Deriv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

noncomputable def hActL (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (h : Matrix (Fin n) (Fin n) E) :
    (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hAct X idx h
      map_add' := fun x y => by funext k i; simp [hAct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext k i; simp [hAct, Finset.mul_sum, mul_left_comm] }

end GlobalTheory.Dict.ColPoly


open GlobalTheory.Dict.ColPoly in
theorem GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  intro E _ _ _ r X g q0 hr bas idx n _hs _hn h hh k k' P hP
  classical
  let A : X.Ψ → Matrix (Fin n) (Fin n) ℂ := fun t => (h.map (t.1 : E →+* ℂ))ᵀ
  let B : X.Ψ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => h.map (ComplexEmbedding.conjugate (t.1 : E →+* ℂ))
  have hAB : ∀ t, A t * B t = 1 := by
    intro t
    have h1 := congrArg (fun M => M.map (t.1 : E →+* ℂ)) hh
    simp only [Matrix.map_mul, GlobalTheory.SW.Base.ccT_map, Matrix.map_one _ (map_zero _) (map_one _)] at h1
    ext i j
    have h2 := congrFun (congrFun h1 j) i
    simp only [A, B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.conjTranspose_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.one_apply] at h2 ⊢
    convert h2 using 1
    · exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]; rfl
    · by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
  let s : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ :=
    fun l k₁ => rowType X (rowOf X hr (l.1, l.2.1)) (h k₁ l.2.2)
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) :=
    fun l k₁ => (l.1, l.2.1, k₁)
  have hΦ : ∀ l, GlobalTheory.Harm.colSubst A B (MvPolynomial.X l) =
      ∑ k₁, MvPolynomial.C (s l k₁) * MvPolynomial.X (j l k₁) := by
    rintro ⟨t, (a | b), k₀⟩
    · have e : rowType X (t, rowIdx hr (Sum.inl a)) = t.1 := by
        simpa using rowType_rowOf_inl X hr t a
      simp [GlobalTheory.Harm.xForm, GlobalTheory.Harm.rowForm_apply, A, s, j, e]
    · have e : rowType X (t, rowIdx hr (Sum.inr b)) = ComplexEmbedding.conjugate t.1 := by
        simpa using rowType_rowOf_inr X hr t b
      simp [GlobalTheory.Harm.yForm, GlobalTheory.Harm.rowForm_apply, B, s, j, e, ComplexEmbedding.conjugate_coe_eq]
  have hdir : (fun l => hActL X idx h (letterDir X hr idx l)) =
      fun l => ∑ k₁, s l k₁ • letterDir X hr idx (j l k₁) := by
    funext l k₁ i
    show hAct X idx h (letterDir X hr idx l) k₁ i = _
    by_cases hi : i = idx.symm (rowOf X hr (l.1, l.2.1))
    · subst hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, ite_apply, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp only [rowOf_apply] at hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, hi, ite_apply, mul_ite]
  refine ⟨GlobalTheory.Harm.colSubst A B P, GlobalTheory.Harm.colSubst_mem_rowHighest hAB hP, fun F hF => ?_⟩
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  have e0 := polyDeriv_comp_linear hF' (hActL X idx h) P (letterDir X hr idx) 0
  rw [map_zero, hdir] at e0
  rw [show (fun z => F (hAct X idx h z)) = fun z => F (hActL X idx h z) from rfl, e0]
  exact (polyDeriv_subst hF' s j (GlobalTheory.Harm.colSubst A B) hΦ (letterDir X hr idx) P 0).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  first | exact @GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | exact GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | (intros; apply GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Extend

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (a b : GL (Fin r) E) (L : Lt E r) : mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

omit [NumberField E] [IsCMField E] in
theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) (x b : Frame Ψ r) :
    lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) a) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro i
  rw [differentiable_pi]; intro j
  simp only [lact, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

variable {X : Data E r}

theorem gramE {a : GL (Fin r) E} (ha : IsUn X a) :
    (a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc = X.Gm := by
  ext i j
  have h := ha (Pi.single i 1) (Pi.single j 1)
  simp only [FD.herm, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, _root_.one_mul] at h
  have hL : ((a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc) i j =
      ∑ c, ∑ d, (a : Matrix (Fin r) (Fin r) E) c i * X.Gm c d * FD.cc ((a : Matrix (Fin r) (Fin r) E) d j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hL, h]
  simp [apply_ite FD.cc]

omit [NumberField E] [IsCMField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dmin_lact {a : GL (Fin r) E} (ha : IsUn X a) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact a x) τ i = dmin X.Gm x τ i := by
  have hc : ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((a : Matrix (Fin r) (Fin r) E).map FD.cc).map τ.1 := by
    ext i j
    simp only [Matrix.map_apply]
    exact (IsCMField.complexEmbedding_complexConj E τ.1 _).symm
  have key : ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, gramE ha]
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  unfold dmin
  congr 1
  rw [gram_eq, gram_eq, e1, Matrix.transpose_mul, Matrix.map_mul]
  calc (mat x τ).transpose * ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        (((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ))
      = (mat x τ).transpose * (((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) * (mat x τ).map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lact_mem {a : GL (Fin r) E} (ha : IsUn X a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a x ∈ X.dom := by
  intro τ
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (a.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · rw [dmin_lact ha]
    exact (hx τ).2 i

end GlobalTheory.Dict.Extend

theorem GlobalTheory.Dict.exists_form_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  intro E _ _ _ r X Δ 𝓛 mu la Jx _ L Q hun hmu hcoc hL hsep hst hQ
  let F : Lt E r → Frame X.Ψ r → ℂ := fun L' x =>
    if h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L' then
      (mu h.choose.2 (L h.choose.1))⁻¹ * Q h.choose.1 (lact h.choose.2⁻¹ x) else 0
  have key : ∀ k, ∀ a ∈ Δ, ∀ x ∈ X.dom,
      F (mapL a (L k)) x = (mu a (L k))⁻¹ * Q k (lact a⁻¹ x) := by
    intro k a ha x hx
    have h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = mapL a (L k) := ⟨(k, a), ha, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    generalize h.choose = p at h1 h2
    obtain ⟨k', b⟩ := p
    dsimp only at h1 h2 ⊢
    have hs : a⁻¹ * b ∈ Δ := Δ.mul_mem (Δ.inv_mem ha) h1
    have h3 : mapL (a⁻¹ * b) (L k') = L k := by
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
    obtain rfl := hsep k' k _ hs h3
    have h4 : mu b (L k') = mu a (L k') := by
      have := hcoc a ha _ hs _ (hL k')
      rwa [mul_inv_cancel_left, h3, hst _ _ hs h3, _root_.mul_one] at this
    have h5 := (hQ k').inv _ hs h3 _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx)
    rw [Extend.lact_lact, mul_inv_cancel_right] at h5
    rw [h4, h5]
  have zero : ∀ L', (¬ ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L') → ∀ x, F L' x = 0 :=
    fun L' h x => by simp only [F, dif_neg h]
  choose C hC using fun k => (hQ k).bdd
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  refine ⟨F, ⟨fun L' _ => ?_, fun L' _ x hx b hb => ?_, fun g hg L' hL' x hx => ?_,
    max B 0, fun L' _ x hx => ?_⟩, fun k x hx => ?_⟩
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      refine DifferentiableOn.congr ?_ (key k a ha)
      exact ((hQ k).hol.comp (Extend.differentiable_lact a⁻¹).differentiableOn
        fun x hx => Extend.lact_mem (hun _ (Δ.inv_mem ha)) hx).const_mul _
    · exact (differentiableOn_const 0).congr fun x _ => zero L' h x
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨h1, -⟩ := h.choose_spec
      simp only [F, dif_pos h]
      rw [Extend.lact_rmul, (hQ _).bor _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx) b hb]
      ring
    · rw [zero L' h, zero L' h, mul_zero]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      rw [← Extend.mapL_mul, key k _ (Δ.mul_mem hg ha) _ (Extend.lact_mem (hun g hg) hx), key k a ha x hx,
        hcoc g hg a ha _ (hL k), Extend.lact_lact, _root_.mul_inv_rev g a, inv_mul_cancel_right, mul_inv,
        _root_.mul_assoc]
    · rw [zero L' h, mul_zero]
      refine zero _ ?_ _
      rintro ⟨⟨k, a⟩, ha, h2⟩
      refine h ⟨(k, g⁻¹ * a), Δ.mul_mem (Δ.inv_mem hg) ha, ?_⟩
      dsimp only at h2 ⊢
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      have hu := hun _ (Δ.inv_mem ha)
      have h1 := hC k _ (Extend.lact_mem hu hx)
      refine le_trans (le_of_eq ?_) (h1.trans ((hB ⟨k, rfl⟩).trans (le_max_left _ _)))
      simp only [Data.pnorm, Extend.dmin_lact hu]
      rw [key k a ha x hx, norm_mul, norm_inv, (hmu a ha _ (hL k)).2, inv_one, _root_.one_mul]
    · simp only [Data.pnorm]
      rw [zero L' h, norm_zero, zero_mul]
      exact le_max_right _ _
  · have h := key k 1 Δ.one_mem x hx
    rw [hst k 1 Δ.one_mem (Extend.mapL_one _), Extend.mapL_one, inv_one, inv_one, _root_.one_mul,
      Extend.lact_one] at h
    exact h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLatticesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_extend_to_all_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  first | exact @GlobalTheory.Dict.exists_form_extend | exact GlobalTheory.Dict.exists_form_extend | (intros; apply GlobalTheory.Dict.exists_form_extend <;> assumption)
end
end

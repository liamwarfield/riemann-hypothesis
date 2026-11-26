module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLevi
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLevi
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.MaDiag

theorem matrix_eq_of_form {e : ℕ} (A B : Matrix (Fin e) (Fin e) ℂ)
    (h : ∀ w : Fin e → ℂ, w ⬝ᵥ (A *ᵥ star w) = w ⬝ᵥ (B *ᵥ star w)) : A = B := by
  set C := A - B with hC
  have hΦ : ∀ w : Fin e → ℂ, w ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro w
    rw [hC, Matrix.sub_mulVec, dotProduct_sub, h w, sub_self]
  have expand : ∀ (u w : Fin e → ℂ) (c : ℂ), (u + c • w) ⬝ᵥ (C *ᵥ star (u + c • w)) =
      u ⬝ᵥ (C *ᵥ star u) + star c * (u ⬝ᵥ (C *ᵥ star w)) + c * (w ⬝ᵥ (C *ᵥ star u)) +
        c * star c * (w ⬝ᵥ (C *ᵥ star w)) := by
    intro u w c
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hsI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hpair : ∀ u w : Fin e → ℂ, u ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro u w
    have h1 := expand u w 1
    have h2 := expand u w Complex.I
    rw [hΦ (u + (1 : ℂ) • w), hΦ u, hΦ w, star_one] at h1
    rw [hΦ (u + Complex.I • w), hΦ u, hΦ w, hsI] at h2
    linear_combination (-1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2 +
      ((u ⬝ᵥ (C *ᵥ star w) - w ⬝ᵥ (C *ᵥ star u)) / 2) * Complex.I_sq
  ext i j
  have hs : star (Pi.single j (1 : ℂ) : Fin e → ℂ) = Pi.single j 1 := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := hpair (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [C, sub_eq_zero] using this

private theorem pair_inv_mul_eq_of_mul_self_eq_one (c d : ℂ) (a b p q : ℝ) :
    c * ((((a + q : ℝ) : ℂ) + Complex.I * ((b - p : ℝ) : ℂ)) / 4 * star d) =
      ((((c.re * d.re * a + c.re * d.im * b + c.im * d.re * p + c.im * d.im * q) +
        ((Complex.I * c).re * (Complex.I * d).re * a + (Complex.I * c).re * (Complex.I * d).im * b +
          (Complex.I * c).im * (Complex.I * d).re * p +
            (Complex.I * c).im * (Complex.I * d).im * q)) / 4 : ℝ) : ℂ) +
      Complex.I * ((((c.re * (Complex.I * d).re * a + c.re * (Complex.I * d).im * b +
          c.im * (Complex.I * d).re * p + c.im * (Complex.I * d).im * q) -
        ((Complex.I * c).re * d.re * a + (Complex.I * c).re * d.im * b +
          (Complex.I * c).im * d.re * p + (Complex.I * c).im * d.im * q)) / 4 : ℝ) : ℂ) := by
  have h4 : ∀ X : ℂ, X / 4 = ((1 / 4 : ℝ) : ℂ) * X := fun X => by push_cast; ring
  rw [h4]
  apply Complex.ext <;> simp <;> ring

theorem dot_hessC_star {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (w : Fin e → ℂ) :
    w ⬝ᵥ (hessC f z *ᵥ star w) = (levi f z w : ℂ) := by
  set H := fderiv ℝ (fderiv ℝ f) z with hH
  have hsymm : ∀ x y, H x y = H y x := fun x y =>
    hf.isSymmSndFDerivAt minSmoothness_of_isRCLikeNormedField.le x y
  have hsmul : ∀ (c : ℂ) (u : Fin e → ℂ), c • u = c.re • u + c.im • (Complex.I • u) := by
    intro c u
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hHs : ∀ (c d : ℂ) (u v : Fin e → ℂ), H (c • u) (d • v) =
      c.re * d.re * H u v + c.re * d.im * H u (Complex.I • v) +
        c.im * d.re * H (Complex.I • u) v + c.im * d.im * H (Complex.I • u) (Complex.I • v) := by
    intro c d u v
    rw [hsmul c u, hsmul d v]
    simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    ring
  set E := fun i : Fin e => (Pi.single i (1 : ℂ) : Fin e → ℂ) with hE
  have hw : ∀ x : Fin e → ℂ, x = ∑ i, x i • E i := by
    intro x
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply]
  have hHsum : ∀ x y : Fin e → ℂ, H x y = ∑ i, ∑ j, H (x i • E i) (y j • E j) := by
    intro x y
    conv_lhs => rw [hw x, hw y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_comm
  have hpair : ∀ i j, w i * (hessC f z i j * star (w j)) =
      (((H (w i • E i) (w j • E j) + H ((Complex.I * w i) • E i) ((Complex.I * w j) • E j)) / 4 : ℝ) : ℂ) +
        Complex.I * (((H (w i • E i) ((Complex.I * w j) • E j) -
          H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) : ℂ) := by
    intro i j
    have hx : hessC f z i j = (((H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j) : ℝ) : ℂ) +
        Complex.I * ((H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j) : ℝ) : ℂ)) / 4 := rfl
    rw [hx, hHs (w i) (w j), hHs (Complex.I * w i) (Complex.I * w j), hHs (w i) (Complex.I * w j),
      hHs (Complex.I * w i) (w j)]
    exact pair_inv_mul_eq_of_mul_self_eq_one (w i) (w j) _ _ _ _
  have hanti : ∀ F : Fin e → Fin e → ℝ, (∀ i j, F i j = -F j i) → ∑ i, ∑ j, F i j = 0 := by
    intro F hF
    have h1 : ∑ i, ∑ j, F i j = ∑ j, ∑ i, F i j := Finset.sum_comm
    have h2 : ∑ j, ∑ i, F i j = -∑ j, ∑ i, F j i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hF i j)
    linarith
  have hQ0 : ∑ i, ∑ j, ((H (w i • E i) ((Complex.I * w j) • E j) -
      H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) = 0 := by
    apply hanti
    intro i j
    rw [hsymm (w i • E i), hsymm ((Complex.I * w i) • E i)]
    ring
  have hLHS : w ⬝ᵥ (hessC f z *ᵥ star w) = ∑ i, ∑ j, w i * (hessC f z i j * star (w j)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  have hlevi : levi f z w = (H w w + H (Complex.I • w) (Complex.I • w)) / 4 := rfl
  rw [hLHS]
  simp_rw [hpair]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [hQ0, Complex.ofReal_zero, mul_zero, add_zero, hlevi, hHsum w w,
    hHsum (Complex.I • w) (Complex.I • w)]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

theorem dot_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) (w : Fin e → ℂ) :
    w ⬝ᵥ ((Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)) *ᵥ star w) =
      ((∑ q, dd q * ‖(M *ᵥ w) q‖ ^ 2 : ℝ) : ℂ) := by
  have hs : M.map (starRingEnd ℂ) *ᵥ star w = star (M *ᵥ w) := by
    ext q
    simp [Matrix.mulVec, dotProduct, star_sum]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [← Complex.mul_conj']
  simp only [Complex.star_def]
  ring

theorem det_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) :
    (Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)).det =
      (((∏ q, dd q) * ‖M.det‖ ^ 2 : ℝ) : ℂ) := by
  have hc : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hc]
  push_cast
  rw [← Complex.mul_conj']
  ring

theorem maDens_diag_levi (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ)
    (M : Matrix (Fin e) (Fin e) ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hl : ∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) :
    maDens (fun _ => φ) z =
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  have hH : hessC φ z = Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ) := by
    apply matrix_eq_of_form
    intro w
    rw [dot_hessC_star φ z hφ w, dot_congr_diag, hl w]
  simp only [maDens]
  rw [hH, ReciprocityTheory.AnForm.A.mdisc_const, det_congr_diag, Complex.ofReal_re]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.MaDiag
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLeviStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_diagonal_levi : ∀ (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ), ContDiffAt ℝ 2 φ z → (∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) → maDens (fun _ => φ) z = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | exact GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddings
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddings
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem oldPart_mem_mcPts {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨fun k => hu.1 (some k), fun f hf => ?_⟩
  have hg : glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
    funext ⟨o, i⟩
    cases o <;> rfl
  have h1 := hu.2 (inc f) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
  have h2 := eval_inc (basePart₂ u) (fun j => u ⟨none, j⟩) f
  rw [hg] at h2
  rw [← h2]
  exact h1

theorem exists_segre_eq_embL [Nonempty K] {p : ℕ} {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    {u : (Σ o, Tb ι o) → ℂ} (hu : u ∈ mcPts (twist p Q)) {v : Fin 2 → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hv : ∀ j : Fin 2, u ⟨none, j⟩ = c * v j) :
    ∃ z ∈ mcPts Q, segre u = embL v (segre z) := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, mcPts_smul hQ (fun k => if k = k0 then c else 1)
    (fun k => by by_cases h : k = k0 <;> simp [h, hc]) (oldPart_mem_mcPts hu), ?_⟩
  funext J
  show ∏ o, u ⟨o, J o⟩ =
    (∏ k, (if k = k0 then c else 1) * basePart₂ u ⟨k, J (some k)⟩) * v (J none)
  rw [Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k0]
  have h1 : u ⟨none, J none⟩ = c * v (J none) := hv (J none)
  rw [h1]
  simp only [Finset.mem_univ, if_true]
  have h2 : ∀ k, basePart₂ u ⟨k, J (some k)⟩ = u ⟨some k, J (some k)⟩ := fun _ => rfl
  simp only [h2]
  ring

theorem new_coords {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ j : Fin 2, u ⟨none, j⟩ = c * vPlus p j) ∨
      (∀ j : Fin 2, u ⟨none, j⟩ = c * vMinus p j)) := by
  have hq : u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
    rw [← eval_quad]
    exact hu.2 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hy : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    intro h0
    rw [h0] at hq
    have hx : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using hq
    obtain ⟨i, hi⟩ := hu.1 none
    have hall : ∀ j : Fin 2, u ⟨none, j⟩ = 0 := by
      intro j
      fin_cases j
      · exact hx
      · exact h0
    exact hi (hall i)
  refine ⟨u ⟨none, (1 : Fin 2)⟩, hy, ?_⟩
  have hf : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = 0 := by
    have : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) =
        u ⟨none, (0 : Fin 2)⟩ ^ 2 - u ⟨none, (1 : Fin 2)⟩ ^ 2 * cRoot p ^ 2 := by ring
    rw [this, cRoot_sq, ← hq]
    ring
  rcases mul_eq_zero.mp hf with h | h
  · left
    intro j
    fin_cases j
    · simpa [vPlus] using sub_eq_zero.mp h
    · simp [vPlus]
  · right
    intro j
    fin_cases j
    · simpa [vMinus] using eq_neg_of_add_eq_zero_left h
    · simp [vMinus]

theorem embL_image_subset {e : ℕ} {p : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) :
    embL v '' fibre Q (pj v Ψ) y ⊆ fibre (twist p Q) Ψ y := by
  rintro _ ⟨w, ⟨z, hz, rfl, hΨ⟩, rfl⟩
  exact ⟨glue z v, glue_mem_mcPts hz hv hv1, segre_glue z v, hΨ⟩

theorem fibre_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (Q : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ),
    p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q →
    fibre (twist p Q) Ψ y =
      embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪
        embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  intro K _ ι _ p Q e Ψ y _ hK hQ
  refine Set.Subset.antisymm ?_ (Set.union_subset
    (embL_image_subset (vPlus_root p) (by simp [vPlus]))
    (embL_image_subset (vMinus_root p) (by simp [vMinus])))
  rintro w ⟨u, hu, rfl, hΨ⟩
  obtain ⟨c, hc, h | h⟩ := new_coords hu
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inl ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vPlus p) (segre z)) = _
    rw [← hs]
    exact hΨ
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inr ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vMinus p) (segre z)) = _
    rw [← hs]
    exact hΨ

end GlobalTheory.CompanionTheory.Ar.Tw.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddingsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_twist_eq_union_embeddings : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ), p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q → fibre (twist p Q) Ψ y = embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪ embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.SheetD

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinIdx (i : (k : K) → ι k) (j : Fin 2) : (o : Option K) → Tb ι o
  | none => j
  | some k => i k

theorem segre_split (u : (Σ o, Tb ι o) → ℂ) (J : (o : Option K) → Tb ι o) :
    segre u J = segre (basePart₂ u) (fun k => J (some k)) * u ⟨none, J none⟩ := by
  show ∏ o, u ⟨o, J o⟩ = (∏ k, u ⟨some k, J (some k)⟩) * u ⟨none, J none⟩
  rw [Fintype.prod_option, mul_comm]

theorem embL_apply (v : Fin 2 → ℂ) (w : ((k : K) → ι k) → ℂ) (J : (o : Option K) → Tb ι o) :
    embL v w J = w (fun k => J (some k)) * v (J none) := rfl

theorem embL_injective {v : Fin 2 → ℂ} (hv1 : v 1 = 1) :
    Function.Injective (embL v : (((k : K) → ι k) → ℂ) → _) := by
  intro w w' h
  funext i
  have := congrFun h (joinIdx i 1)
  simpa [embL_apply, joinIdx, hv1] using this

theorem glue_oldPart (u : (Σ o, Tb ι o) → ℂ) :
    glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
  funext q
  obtain ⟨o, i⟩ := q
  cases o <;> rfl

theorem oldPart_mem {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨oldPart_ne hu.1, fun f hf => ?_⟩
  have h1 : inc f ∈ twist p Q := Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
  have h2 := hu.2 _ h1
  rw [← glue_oldPart u, eval_inc] at h2
  exact h2

theorem quad_eq_zero {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
  have h1 : (quad p : MRing (Tb ι)) ∈ twist p Q :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have h2 := hu.2 _ h1
  rwa [eval_quad] at h2

theorem second_ne_zero {p : ℕ} (hp : p ≠ 0) {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
  intro h0
  have h1 := quad_eq_zero hu
  rw [h0] at h1
  have h2 : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using h1
  obtain ⟨i, hi⟩ := hu.1 none
  refine hi ?_
  have hi' : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
    have : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    exact this i
  rcases hi' with rfl | rfl
  · exact h2
  · exact h0

theorem glue_isSheet {p e : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet Q (pj v Ψ) y w γ) :
    IsSheet (twist p Q) Ψ y (embL v w) (fun y' => glue (γ y') v) := by
  refine ⟨by rw [segre_glue, h.1], ?_⟩
  filter_upwards [h.2] with y' ⟨hd, hm, hΨ⟩
  refine ⟨?_, glue_mem_mcPts hm hv hv1, ?_⟩
  · refine differentiableAt_pi.mpr fun q => ?_
    obtain ⟨o, i⟩ := q
    cases o with
    | none => exact differentiableAt_const _
    | some k => exact differentiableAt_pi.mp hd ⟨k, i⟩
  · rw [segre_glue]; exact hΨ

open Classical in
theorem sheet_of_twist_sheet {p e : ℕ} (hp : p ≠ 0) {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    (k0 : K) {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 = 1) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ' : (Fin e → ℂ) → (Σ o, Tb ι o) → ℂ}
    (h : IsSheet (twist p Q) Ψ y (embL v w) γ') :
    ∃ γ, IsSheet Q (pj v Ψ) y w γ := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hd0, hm0, hΨ0⟩ := h2.self_of_nhds
  have hρ : v 0 ^ 2 = -(p : ℂ) := by
    rw [hv1] at hv
    linear_combination hv
  have hρ0 : v 0 ≠ 0 := by
    intro h0
    rw [h0] at hρ
    have : (p : ℂ) = 0 := by simpa using hρ
    exact hp (by exact_mod_cast this)
  have hb0 := second_ne_zero hp hm0

  have hne : embL v w ≠ 0 := by
    intro h0
    rw [h1, h0, map_zero] at hΨ0
    have := congrFun hΨ0 0
    simp at this
  have hw : w ≠ 0 := by
    intro h0
    exact hne (by rw [h0, map_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := hi
  have hseg : ∀ j : Fin 2, segre (basePart₂ (γ' y)) i * γ' y ⟨none, j⟩ = w i * v j := by
    intro j
    have := congrFun h1 (joinIdx i j)
    rw [segre_split, embL_apply] at this
    exact this
  have hm : segre (basePart₂ (γ' y)) i ≠ 0 := by
    intro h0
    have := hseg 1
    rw [h0, zero_mul, hv1, mul_one] at this
    exact hi' this.symm
  have hay : γ' y ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y ⟨none, (1 : Fin 2)⟩ := by
    apply mul_left_cancel₀ hm
    have e0 := hseg 0
    have e1 := hseg 1
    rw [hv1, mul_one] at e1
    rw [e0]
    linear_combination (-(v 0)) * e1

  have hcont : ContinuousAt (fun y' => γ' y' ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) y :=
    ((differentiableAt_pi.mp hd0 _).continuousAt).add
      (continuousAt_const.mul (differentiableAt_pi.mp hd0 _).continuousAt)
  have hne2 : γ' y ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    rw [hay]
    have : v 0 * γ' y ⟨none, (1 : Fin 2)⟩ + v 0 * γ' y ⟨none, (1 : Fin 2)⟩ =
        2 * (v 0 * γ' y ⟨none, (1 : Fin 2)⟩) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hρ0 hb0)
  have hline : ∀ᶠ y' in 𝓝 y, γ' y' ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y' ⟨none, (1 : Fin 2)⟩ := by
    filter_upwards [h2, hcont.eventually_ne hne2] with y' ⟨_, hm', _⟩ hn
    have hq := quad_eq_zero hm'
    have hz : (γ' y' ⟨none, (0 : Fin 2)⟩ - v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) *
        (γ' y' ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) = 0 := by
      linear_combination hq - γ' y' ⟨none, (1 : Fin 2)⟩ ^ 2 * hρ
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)

  let c : K → (Fin e → ℂ) → ℂ := fun k y' => if k = k0 then γ' y' ⟨none, (1 : Fin 2)⟩ else 1
  let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' q => c q.1 y' * basePart₂ (γ' y') q
  have hprod : ∀ y', ∏ k, c k y' = γ' y' ⟨none, (1 : Fin 2)⟩ := by
    intro y'
    simp [c, Finset.prod_ite_eq']
  have hkey : ∀ y', γ' y' ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y' ⟨none, (1 : Fin 2)⟩ →
      embL v (segre (γ y')) = segre (γ' y') := by
    intro y' hl
    funext J
    have hj : γ' y' ⟨none, J none⟩ = γ' y' ⟨none, (1 : Fin 2)⟩ * v (J none) := by
      have hJ : ∀ j : Fin 2, γ' y' ⟨none, j⟩ = γ' y' ⟨none, (1 : Fin 2)⟩ * v j := by
        intro j
        have : j = 0 ∨ j = 1 := by
          have : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
          exact this j
        rcases this with rfl | rfl
        · rw [hl]; ring
        · rw [hv1, mul_one]
      exact hJ _
    have hsm : segre (γ y') = (∏ k, c k y') • segre (basePart₂ (γ' y')) :=
      segre_smul (fun k => c k y') (basePart₂ (γ' y'))
    have hs : segre (γ y') (fun k => J (some k)) =
        γ' y' ⟨none, (1 : Fin 2)⟩ * segre (basePart₂ (γ' y')) (fun k => J (some k)) := by
      rw [hsm, hprod]
      rfl
    rw [embL_apply, segre_split, hj, hs]
    ring
  refine ⟨γ, embL_injective hv1 ?_, ?_⟩
  · rw [hkey y hay, h1]
  · filter_upwards [h2, hline] with y' ⟨hd, hm', hΨ'⟩ hl
    refine ⟨?_, ?_, ?_⟩
    · refine differentiableAt_pi.mpr fun q => ?_
      have hc : DifferentiableAt ℂ (c q.1) y' := by
        by_cases hk : q.1 = k0
        · simp only [c, hk, if_true]
          exact differentiableAt_pi.mp hd _
        · simp only [c, hk, if_false]
          exact differentiableAt_const _
      exact hc.mul (differentiableAt_pi.mp hd _)
    · refine mcPts_smul hQ (fun k => c k y') (fun k => ?_) (oldPart_mem hm')
      by_cases hk : k = k0
      · simpa [c, hk] using second_ne_zero hp hm'
      · simp [c, hk]
    · show Ψ (embL v (segre (γ y'))) = _
      rw [hkey y' hl]
      exact hΨ'

theorem density_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  intro K _ ι _ p Q e Ψ L' A' L A s v hp hQ hT hΨ hL' hA' hs hv hLh hAh
  have hv1 : v 1 = 1 := by
    rcases hv with rfl | rfl <;> simp [vPlus, vMinus]
  have hvq : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0 := by
    rcases hv with rfl | rfl
    · exact vPlus_root p
    · exact vMinus_root p
  obtain ⟨k0⟩ := hQ.1
  have hQh : IsMultiHomogIdeal Q := hQ.2.1.2.1
  filter_upwards [sheetIndep (Option K) (Tb ι) (twist p Q) e Ψ L' A' (inc s) hT hΨ hL' hA' hs] with y hind
  intro w
  by_cases hγ : ∃ γ, IsSheet Q (pj v Ψ) y w γ
  · have hg := hγ.choose_spec
    have hg1 := glue_isSheet hvq (by rw [hv1]; exact one_ne_zero) hg
    have hex : ∃ γ', IsSheet (twist p Q) Ψ y (embL v w) γ' := ⟨_, hg1⟩
    unfold sheetDensity
    rw [dite_eq_left hex, dite_eq_left hγ, hind _ _ _ hex.choose_spec hg1]
    have hlog : logNorm A' (inc s) (glue (hγ.choose y) v) = logNorm A s (hγ.choose y) := by
      rw [logNorm, logNorm, eval_inc, hAh _ hg.2.self_of_nhds.2.1]
    have hma : maDensity (fun j y' => pot L' j (glue (hγ.choose y') v)) y =
        maDensity (fun j y' => pot L j (hγ.choose y')) y := by
      refine maDensity_congr_of_eventuallyEq fun j => ?_
      filter_upwards [hg.2] with y' ⟨_, hm, _⟩
      simp only [pot, hLh j _ hm]
    rw [hlog, hma]
  · have hno : ¬ ∃ γ', IsSheet (twist p Q) Ψ y (embL v w) γ' := fun ⟨γ', h⟩ =>
      hγ (sheet_of_twist_sheet hp hQh k0 hvq hv1 h)
    unfold sheetDensity
    rw [dite_eq_right hno, dite_eq_right hγ]

end GlobalTheory.CompanionTheory.Ar.Tw.SheetD
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecompositionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_height_integral_decomposition : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist <;> assumption)
end
end

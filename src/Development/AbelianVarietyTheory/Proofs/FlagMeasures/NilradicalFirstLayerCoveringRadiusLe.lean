module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogon
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogonStatement
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  first | exact @GlobalTheory.NilLift.exists_nilInt_lift | exact GlobalTheory.NilLift.exists_nilInt_lift | (intros; apply GlobalTheory.NilLift.exists_nilInt_lift <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropic
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NilLift

variable {n : ℕ}

theorem hs_eq_trace (M : Matrix (Fin n) (Fin n) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_nonneg' (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs M := by
  simp only [Formalism.REAL.hs]
  positivity

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ (∀ u, P *ᵥ u ∈ W) ∧ ∀ u ∈ W, P *ᵥ u = u := by
  classical
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    W.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := K.starProjection
  have hT : ∀ u, (Matrix.toEuclideanLin.symm T) *ᵥ u = WithLp.ofLp (T (WithLp.toLp 2 u)) := by
    intro u
    have h := congrArg (fun f : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) =>
      WithLp.ofLp (f (WithLp.toLp 2 u))) (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin T)
    exact h
  refine ⟨Matrix.toEuclideanLin.symm T, ?_, ?_, ?_⟩
  · have hH : (Matrix.toEuclideanLin.symm T).IsHermitian := by
      rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearEquiv.apply_symm_apply]
      exact K.starProjection_isSymmetric
    exact hH
  · intro u
    rw [hT]
    have hm : T (WithLp.toLp 2 u) ∈ K := K.starProjection_apply_mem _
    exact hm
  · intro u hu
    rw [hT]
    have hm : WithLp.toLp 2 u ∈ K := hu
    have h2 : T (WithLp.toLp 2 u) = WithLp.toLp 2 u := K.starProjection_eq_self_iff.mpr hm
    rw [h2]

theorem hs_mul_le (D Q : Matrix (Fin n) (Fin n) ℂ) (h1 : Qᴴ = Q) (h2 : Q * Q = Q) :
    hs (D * (1 - Q)) ≤ hs D := by
  have hR : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, h2, sub_self, sub_zero]
  have hDQ : hs (D * Q) = (trace (D * Q * Dᴴ)).re := by
    rw [hs_eq_trace, Matrix.trace_mul_comm, Matrix.conjTranspose_mul, h1, mul_assoc,
      ← mul_assoc Q Q, h2, ← mul_assoc]
  have hDR : hs (D * (1 - Q)) = (trace (D * Dᴴ)).re - (trace (D * Q * Dᴴ)).re := by
    rw [hs_eq_trace, Matrix.trace_mul_comm, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, h1, mul_assoc, ← mul_assoc (1 - Q) (1 - Q), hR, ← mul_assoc,
      mul_sub, mul_one, sub_mul, Matrix.trace_sub, Complex.sub_re]
  have hD : hs D = (trace (D * Dᴴ)).re := by rw [hs_eq_trace, Matrix.trace_mul_comm]
  have h0 := hs_nonneg' (D * Q)
  linarith

theorem core (J P D : Matrix (Fin n) (Fin n) ℂ) (j1 : J * J = 1) (j2 : Jᴴ = J) (p1 : Pᴴ = P)
    (p2 : P * P = P) (p3 : P * J * P = 0) (d1 : D * P = 0)
    (d2 : P * (D * (1 - J * P * J)) = D * (1 - J * P * J)) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ * J + J * A = 0 ∧ P * J * A = 0 ∧
      (∀ u, (P * J) *ᵥ u = 0 → A *ᵥ u = D *ᵥ u) ∧ hs A ≤ 2 * hs D := by
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← mul_assoc, j1, one_mul]
  have hPP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (P * X) = P * X := fun X => by
    rw [← mul_assoc, p2]
  have hPJP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (J * (P * X)) = 0 := fun X => by
    rw [← mul_assoc, ← mul_assoc, p3, zero_mul]
  have hPDh : P * Dᴴ = 0 := by
    have h := congrArg conjTranspose d1
    rwa [conjTranspose_mul, p1, conjTranspose_zero] at h
  obtain ⟨B, hB⟩ : ∃ B, B = D * (1 - J * P * J) := ⟨_, rfl⟩
  rw [← hB] at d2
  have hBJP : B * (J * P) = 0 := by
    rw [hB]
    simp only [mul_assoc, sub_mul, mul_sub, one_mul, mul_one, hJJ, p2, hPP, sub_self, mul_zero]
  have hBJB : B * (J * B) = 0 := by
    calc B * (J * B) = B * (J * (P * B)) := by rw [d2]
      _ = B * (J * P) * B := by simp only [mul_assoc]
      _ = 0 := by rw [hBJP, zero_mul]
  have hBhP : Bᴴ * P = Bᴴ := by
    have h := congrArg conjTranspose d2
    rwa [conjTranspose_mul, p1] at h
  have hPBh : P * Bᴴ = 0 := by
    rw [hB]
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, j2, p1, mul_sub, sub_mul,
      one_mul, mul_one, mul_assoc, hPJP, hPDh, sub_zero, sub_self]
  have hPBhX : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (Bᴴ * X) = 0 := fun X => by
    rw [← mul_assoc, hPBh, zero_mul]
  have hPJB : P * (J * B) = 0 := by
    calc P * (J * B) = P * (J * (P * B)) := by rw [d2]
      _ = 0 := hPJP B
  have hBhJBh : ∀ X : Matrix (Fin n) (Fin n) ℂ, Bᴴ * (J * (Bᴴ * X)) = 0 := by
    intro X
    have h := congrArg conjTranspose hBJB
    rw [conjTranspose_mul, conjTranspose_mul, j2, conjTranspose_zero] at h
    rw [← mul_assoc, ← mul_assoc, h, zero_mul]
  refine ⟨B - J * Bᴴ * J, ?_, ?_, ?_, ?_⟩
  · simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, j2, sub_mul,
      mul_sub, mul_assoc, j1, hJJ, mul_one]
    abel
  · simp only [mul_sub, mul_assoc, hJJ, hPJB, hPBhX, sub_self]
  · intro u hu
    have e1 : J * Bᴴ * J = J * Bᴴ * (P * J) := by
      conv_lhs => rw [← hBhP]
      simp only [mul_assoc]
    have e2 : B = D - D * J * (P * J) := by
      rw [hB, mul_sub, mul_one]
      simp only [mul_assoc]
    have hA : B - J * Bᴴ * J = D - (D * J + J * Bᴴ) * (P * J) := by
      rw [e1, add_mul, ← sub_sub, ← e2]
    rw [hA, sub_mulVec, ← mulVec_mulVec, hu, mulVec_zero, sub_zero]
  · have hK1 : (J * P * J)ᴴ = J * P * J := by
      simp only [conjTranspose_mul, j2, p1, mul_assoc]
    have hK2 : J * P * J * (J * P * J) = J * P * J := by
      simp only [mul_assoc, hJJ, hPP]
    have hsB : hs B ≤ hs D := by
      rw [hB]
      exact hs_mul_le D (J * P * J) hK1 hK2
    have hM : (B - J * Bᴴ * J)ᴴ * (B - J * Bᴴ * J) = Bᴴ * B + J * (B * (Bᴴ * J)) := by
      simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, j2, sub_mul,
        mul_sub, mul_assoc, hJJ, hBJB, hBhJBh, mul_zero, sub_zero, zero_sub, sub_neg_eq_add]
    have t1 : trace (J * (B * (Bᴴ * J))) = trace (Bᴴ * B) := by
      rw [Matrix.trace_mul_comm, mul_assoc, mul_assoc, j1, mul_one, Matrix.trace_mul_comm]
    have hsA : hs (B - J * Bᴴ * J) = 2 * hs B := by
      rw [hs_eq_trace, hs_eq_trace, hM, Matrix.trace_add, t1, Complex.add_re]
      ring
    rw [hsA]
    linarith

theorem hform_eq (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) H x y = star x ⬝ᵥ (H *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]

theorem hform_mulVec (H X Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) H (X *ᵥ x) (Y *ᵥ y) = star x ⬝ᵥ ((Xᴴ * H * Y) *ᵥ y) := by
  rw [hform_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem ext_mulVec' {X Y : Matrix (Fin n) (Fin n) ℂ} (h : ∀ u, X *ᵥ u = Y *ᵥ u) : X = Y := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h1

private theorem jm_sq_lemma (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem jm_herm_lemma_2 (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem exists_lift : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  intro n ε H G D W hG hJ hiso hDW hDperp
  classical
  have j1 : Jm ε * Jm ε = 1 := jm_sq_lemma ε
  have j2 : (Jm ε)ᴴ = Jm ε := jm_herm_lemma_2 ε
  have hGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hiGX : ∀ X : Matrix (Fin n) (Fin n) ℂ, G⁻¹ * (G * X) = X := fun X => by
    rw [← mul_assoc, hiG, one_mul]
  have hGu : ∀ u : Fin n → ℂ, G *ᵥ (G⁻¹ *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hGi, one_mulVec]
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← mul_assoc, j1, one_mul]
  obtain ⟨P, p1, hPW, hPfix⟩ := exists_proj (W.comap (Matrix.toLin' G))
  have hPW' : ∀ u, G *ᵥ (P *ᵥ u) ∈ W := fun u => by
    have h := hPW u
    rwa [Submodule.mem_comap, Matrix.toLin'_apply] at h
  have hPfix' : ∀ v, G *ᵥ v ∈ W → P *ᵥ v = v := fun v hv =>
    hPfix v (by rwa [Submodule.mem_comap, Matrix.toLin'_apply])
  have p2 : P * P = P := ext_mulVec' fun u => by
    rw [← mulVec_mulVec]
    exact hPfix' _ (hPW' u)
  have hPP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (P * X) = P * X := fun X => by
    rw [← mul_assoc, p2]
  have hf : ∀ a b : Fin n → ℂ,
      Formalism.UG.hform (starRingEnd ℂ) H (G *ᵥ a) (G *ᵥ b) = star a ⬝ᵥ (Jm ε *ᵥ b) := fun a b => by
    rw [hform_mulVec, hJ]
  have hPs : ∀ a z : Fin n → ℂ, star (P *ᵥ a) ⬝ᵥ z = star a ⬝ᵥ (P *ᵥ z) := fun a z => by
    rw [star_mulVec, ← dotProduct_mulVec, p1]
  have hperp : ∀ v, G *ᵥ v ∈ perpSet (starRingEnd ℂ) H W ↔ (P * Jm ε) *ᵥ v = 0 := by
    intro v
    simp only [perpSet, Set.mem_setOf_eq]
    constructor
    · intro h
      apply dotProduct_star_self_eq_zero.mp
      rw [← mulVec_mulVec, ← hPs, ← hf]
      exact h _ (hPW' _)
    · intro h w hw
      rw [← hGu w, hf, ← hPfix' (G⁻¹ *ᵥ w) (by rw [hGu]; exact hw), hPs, mulVec_mulVec, h,
        dotProduct_zero]
  have p3 : P * Jm ε * P = 0 := ext_mulVec' fun u => by
    rw [zero_mulVec, ← mulVec_mulVec]
    exact (hperp _).mp (hiso _ (hPW' u))
  have hDv : ∀ v, (G⁻¹ * D * G) *ᵥ v = G⁻¹ *ᵥ (D *ᵥ (G *ᵥ v)) := fun v => by
    simp only [← mulVec_mulVec]
  have d1 : G⁻¹ * D * G * P = 0 := ext_mulVec' fun u => by
    rw [zero_mulVec, ← mulVec_mulVec, hDv, hDW _ (hPW' u), mulVec_zero]
  have d2 : P * (G⁻¹ * D * G * (1 - Jm ε * P * Jm ε)) = G⁻¹ * D * G * (1 - Jm ε * P * Jm ε) :=
    ext_mulVec' fun u => by
      have hz : (P * Jm ε) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ u) = 0 := by
        rw [mulVec_mulVec, mul_sub, mul_one]
        simp only [mul_assoc, hJJ, hPP, sub_self, zero_mulVec]
      have hm : G *ᵥ ((G⁻¹ * D * G) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ u)) ∈ W := by
        rw [hDv, hGu]
        exact hDperp _ ((hperp _).mpr hz)
      rw [← mulVec_mulVec _ P, ← mulVec_mulVec _ (G⁻¹ * D * G)]
      exact hPfix' _ hm
  obtain ⟨A', hA1, hA2, hA3, hA4⟩ := core (Jm ε) P (G⁻¹ * D * G) j1 j2 p1 p2 p3 d1 d2
  have hAv : ∀ v, (G * A' * G⁻¹) *ᵥ (G *ᵥ v) = G *ᵥ (A' *ᵥ v) := fun v => by
    simp only [mulVec_mulVec, mul_assoc, hiG, mul_one]
  have hagree : ∀ u ∈ perpSet (starRingEnd ℂ) H W, (G * A' * G⁻¹) *ᵥ u = D *ᵥ u := by
    intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
    rw [hAv, hA3 v ((hperp v).mp hu), hDv, hGu]
  refine ⟨G * A' * G⁻¹, ?_, hagree, ?_⟩
  · unfold InNil IsSkew
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u u'
      obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
      obtain ⟨v', rfl⟩ : ∃ v', u' = G *ᵥ v' := ⟨G⁻¹ *ᵥ u', (hGu u').symm⟩
      rw [hAv, hAv, hf, hf, star_mulVec, ← dotProduct_mulVec, ← dotProduct_add, mulVec_mulVec,
        mulVec_mulVec, ← add_mulVec, hA1, zero_mulVec, dotProduct_zero]
    · intro u
      obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
      rw [hAv, hperp, mulVec_mulVec, hA2, zero_mulVec]
    · intro u hu
      rw [hagree u hu]
      exact hDperp u hu
    · intro u hu
      rw [hagree u (hiso u hu)]
      exact hDW u hu
  · have hc : G⁻¹ * (G * A' * G⁻¹) * G = A' := by
      simp only [mul_assoc, hiG, mul_one, hiGX]
    rw [hc]
    exact hA4

end GlobalTheory.NilLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropicStatement
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  first | exact @GlobalTheory.NilLift.exists_lift | exact GlobalTheory.NilLift.exists_lift | (intros; apply GlobalTheory.NilLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLe
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.FirstLayer

theorem inNil_sub {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (W : Submodule A (Fin n → A)) (Y Y' : Matrix (Fin n) (Fin n) A)
    (h : InNil s J W Y) (h' : InNil s J W Y') : InNil s J W (Y - Y') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  have l1 : ∀ a b c : Fin n → A, Formalism.UG.hform s J (a - b) c = Formalism.UG.hform s J a c - Formalism.UG.hform s J b c := by
    intro a b c
    simp [Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
  have l2 : ∀ a b c : Fin n → A, Formalism.UG.hform s J c (a - b) = Formalism.UG.hform s J c a - Formalism.UG.hform s J c b := by
    intro a b c
    simp [Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u u'
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, l1, l2]
    have a := h1 u u'
    have b := g1 u u'
    linear_combination a - b
  · intro u w hw
    rw [Matrix.sub_mulVec, l2, h2 u w hw, g2 u w hw, sub_zero]
  · intro u hu
    rw [Matrix.sub_mulVec]
    exact W.sub_mem (h3 u hu) (g3 u hu)
  · intro u hu
    rw [Matrix.sub_mulVec, h4 u hu, g4 u hu, sub_zero]

theorem map_mulVec_emb (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (y : Fin I.n → I.E) :
    M.map (I.φ v) *ᵥ (fun i => I.φ v (y i)) = fun i => I.φ v ((M *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem mem_spanAt (I : AutInst) (v : InfinitePlace I.F) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (y : Fin I.n → I.E) (hy : y ∈ R) : (fun i => I.φ v (y i)) ∈ spanAt I R v :=
  Submodule.subset_span ⟨y, hy, rfl⟩

theorem mulVec_mem_of_span (I : AutInst) (v : InfinitePlace I.F) (A : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (M : Matrix (Fin I.n) (Fin I.n) ℂ) (W : Submodule ℂ (Fin I.n → ℂ))
    (h : ∀ y ∈ A, M *ᵥ (fun i => I.φ v (y i)) ∈ W) : ∀ u ∈ spanAt I A v, M *ᵥ u ∈ W := by
  have : spanAt I A v ≤ W.comap (Matrix.mulVecLin M) := by
    unfold spanAt
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  intro u hu
  exact this hu

theorem frame_inv (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * M * I.P v * uMat (x.1 v) =
      (I.P v * uMat (x.1 v))⁻¹ * M * (I.P v * uMat (x.1 v)) := by
  rw [Matrix.mul_inv_rev]
  have : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
    simp only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
  rw [this]
  simp only [Matrix.mul_assoc]

theorem frame_det (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    IsUnit (I.P v * uMat (x.1 v)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (I.P_unit v).mul (Units.isUnit _)

theorem frame_spec (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
  have h : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  rw [← h, ← I.P_spec v, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem arith (n f k j rd lo hi rho : ℝ) (hf : 0 < f) (hrd : 0 ≤ rd) (hkj : k + j = n) (hlo : 0 < lo)
    (hhi : 0 < hi) (hr : hi ≤ rho * lo) :
    Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) ≤
      (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) := by
  have h1 : (k - j) * j ≤ n ^ 2 / 8 := by
    rw [← hkj]; nlinarith [sq_nonneg (k - 3 * j)]
  have h2 : hi / lo ≤ rho := by rwa [div_le_iff₀ hlo]
  have h3 : 0 < hi / lo := div_pos hhi hlo
  have hs : 0 < Real.sqrt (2 * f) := Real.sqrt_pos.2 (by linarith)
  have e : Real.sqrt 2 * Real.sqrt f = Real.sqrt (2 * f) := (Real.sqrt_mul (by norm_num) f).symm
  have e2 : Real.sqrt (2 * f) * Real.sqrt (2 * f) = 2 * f := Real.mul_self_sqrt (by linarith)
  have e3 : (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) =
      n ^ 2 / 8 * rho * (Real.sqrt (2 * f) * rd / 2) := by
    rw [div_eq_iff hs.ne']
    linear_combination (-(n ^ 2 / 8 * rho * rd / 2)) * e2
  have e4 : Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) =
      (k - j) * j * (hi / lo) * (Real.sqrt (2 * f) * rd / 2) := by
    rw [← e]; field_simp
  rw [e3, e4]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (k - j) * j * (hi / lo) ≤ n ^ 2 / 8 * (hi / lo) := mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ n ^ 2 / 8 * rho := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  intro I x R lo hi rho hsat hiso hhi hlarge hlow hlo hr Y hY
  have hpl : perpIn I x R ≤ lamX I x := by
    unfold perpIn
    rw [Submodule.span_le]
    exact fun y hy => hy.1
  have hfg : (lamX I x).FG := (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x).2.1
  have hsat' : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) R := by
    refine ⟨hiso, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hiso hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hz
      exact hsat.2.2 _ ⟨y, hpl hy, rfl⟩ hz
  obtain ⟨-, -, hperp, hnil, -⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  have hP : ∀ v u, u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ↔
      u ∈ spanAt I (perpIn I x R) v := by
    intro v u
    rw [← hperp v]; rfl
  have hmono : ∀ v, spanAt I R v ≤ spanAt I (perpIn I x R) v := fun v =>
    Submodule.span_mono (Set.image_mono hiso)
  obtain ⟨Φ, hΦ0, hΦ1, D, hD, hDn⟩ := GlobalTheory.T.subquotient_covering_radius_real_places I x (perpIn I x R) R R lo hi (hfg.of_le hpl) hsat'
    (hfg.of_le hsat.1) hlo hhi (fun N h1 h2 => hlow N h1 (h2.trans hpl)) hlarge Y
    (fun v y hy => (hY v).2.2.2 _ (mem_spanAt I v R y hy))
    (fun v y hy => (hY v).2.2.1 _ ((hP v _).2 (mem_spanAt I v _ y hy)))
  obtain ⟨Y₀, hY₀, hY₀Φ⟩ := GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal I x R hiso Φ hΦ0 hΦ1
  have hA : ∀ v, ∃ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) A ∧
      (∀ u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v), A *ᵥ u = D v *ᵥ u) ∧
      hs ((I.P v * uMat (x.1 v))⁻¹ * A * (I.P v * uMat (x.1 v))) ≤
        2 * hs ((I.P v * uMat (x.1 v))⁻¹ * D v * (I.P v * uMat (x.1 v))) := by
    intro v
    refine GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic I.n (I.ε v) _ _ (D v) _ (frame_det I x v) (frame_spec I x v)
      (fun u hu => (hP v u).2 (hmono v hu)) ?_ ?_
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
        refine mulVec_mem_of_span I v R _ ⊥ ?_ u hu
        intro y hy
        rw [map_mulVec_emb, hΦ0 y hy, Submodule.mem_bot]
        funext i; simp
      rw [hD v u (hmono v hu), Matrix.sub_mulVec, (hY v).2.2.2 u hu, (Submodule.mem_bot ℂ).1 h0, sub_zero]
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ spanAt I R v := by
        refine mulVec_mem_of_span I v _ _ _ ?_ u ((hP v u).1 hu)
        intro y hy
        rw [map_mulVec_emb]
        exact mem_spanAt I v R _ (hΦ1 y hy)
      rw [hD v u ((hP v u).1 hu), Matrix.sub_mulVec]
      exact Submodule.sub_mem _ ((hY v).2.2.1 u hu) h0
  choose A hA1 hA2 hA3 using hA
  refine ⟨Y₀, hY₀, Y - diagEmb I Y₀ - A, ?_, ?_⟩
  · intro v
    refine ⟨inNil_sub _ _ _ _ _ (inNil_sub _ _ _ _ _ (hY v) (hnil Y₀ hY₀.1 v)) (hA1 v), ?_⟩
    intro u hu
    have h0 : (Y₀.map (I.φ v) - Φ.map (I.φ v)) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
      refine mulVec_mem_of_span I v _ _ ⊥ ?_ u ((hP v u).1 hu)
      intro y hy
      rw [Matrix.sub_mulVec, map_mulVec_emb, map_mulVec_emb, hY₀Φ y hy, sub_self]
      exact Submodule.zero_mem _
    rw [Submodule.mem_bot, Matrix.sub_mulVec, sub_eq_zero] at h0
    show (Y v - Y₀.map (I.φ v) - A v) *ᵥ u = 0
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hA2 v u hu, hD v u ((hP v u).1 hu), Matrix.sub_mulVec, h0,
      sub_self]
  · rw [sub_sub_cancel]
    have hAD : normAt I x A ≤ Real.sqrt 2 * normAt I x D := by
      unfold normAt
      rw [← Real.sqrt_mul (by norm_num), Finset.mul_sum]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro v _
      rw [frame_inv, frame_inv]
      exact hA3 v
    have hrk : rkK (perpIn I x R) + rkK R = I.n :=
      ((GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.2.2 R R hsat hsat le_rfl).2.1
    have hf : (0 : ℝ) < I.f := by
      have : 0 < I.f := Module.finrank_pos
      exact_mod_cast this
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine hAD.trans ((mul_le_mul_of_nonneg_left hDn (Real.sqrt_nonneg _)).trans ?_)
    exact arith _ _ _ _ _ _ _ _ hf hrd (by exact_mod_cast hrk) hlo hhi hr

end GlobalTheory.Count.FirstLayer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLeStatement
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_first_layer_covering_radius_le : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  first | exact @GlobalTheory.Count.FirstLayer.main | exact GlobalTheory.Count.FirstLayer.main | (intros; apply GlobalTheory.Count.FirstLayer.main <;> assumption)
end

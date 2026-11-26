module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormDimLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormDimLe

theorem coeff_zero_eq_zero_of_mem {F : Type} [Field F] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    (hI : IsProjPrime I) {g : MvPolynomial (Fin n) F} (hg : g ∈ I) : AddMonoidAlgebra.coeff g 0 = 0 := by
  by_contra h
  have h0 := hI.isHomog g hg 0
  rw [homogeneousComponent_zero] at h0
  exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem exists_prime_liesOver {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, AddMonoidAlgebra.coeff g 0 = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  have hle : I ≤ Q.under (MvPolynomial (Fin n) F) := by
    intro g hg
    rw [Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map,
      eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]
  obtain ⟨P, hPQ, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  refine ⟨P, hP, hPQ, ?_⟩
  rw [P.over_def I]
  rfl

theorem ringKrullDim_eq_of_comap {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : P.LiesOver I := ⟨hPI.symm⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))

theorem exists_ne_zero_common_zero {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by
  classical
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  let mk := Ideal.Quotient.mk P
  let ℓ : Fin k → MvPolynomial (Fin n) K := fun i => ∑ j, C (u (i, j)) * X j
  have hℓQ : ∀ i, ℓ i ∈ Q := by
    intro i
    simp [Q, ℓ, RingHom.mem_ker]
  set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk
  have : Mb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  let s : Finset (MvPolynomial (Fin n) K ⧸ P) := Finset.univ.image (fun i => mk (ℓ i))
  have hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb := by
    rw [Ideal.span_le]
    intro y hy
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ (hℓQ i)
  obtain ⟨q, hqmin, hqM⟩ := Ideal.exists_minimalPrimes_le hsM
  have : q.IsPrime := hqmin.1.1
  have hqht : q.height ≤ k := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P) := by
    have h := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := K) Mb
    have hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance
    have h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0 := by
      have h00 := ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF
      convert h00 using 2
    rwa [h0, add_zero] at h
  have hqne : q ≠ Mb := by
    intro hq
    rw [hq] at hqht
    have h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hqht
    rw [hMht] at h1
    exact absurd h1 (not_le.mpr (by exact_mod_cast hdim))
  set Q' := q.comap mk
  have : Q'.IsPrime := Ideal.comap_isPrime mk q
  have hQQ' : ¬ Q ≤ Q' := by
    intro h
    apply hqne
    refine le_antisymm hqM ?_
    calc Mb = Q.map mk := rfl
      _ ≤ Q'.map mk := Ideal.map_mono h
      _ = q := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  have hnull := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hQQ'
    intro g hg
    rw [← hnull, mem_vanishingIdeal_iff]
    intro x hx
    rw [hcon x hx]
    simpa [Q, RingHom.mem_ker] using hg
  refine ⟨x, hx0, fun g hg => ?_, fun i => ?_⟩
  · have hgQ' : g ∈ Q' := by
      show mk g ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact q.zero_mem
    simpa using (mem_zeroLocus_iff.mp hx) g hgQ'
  · have hmem : ℓ i ∈ Q' := by
      show mk (ℓ i) ∈ q
      exact hqmin.1.2 (Ideal.subset_span (by simp [s]))
    simpa [ℓ] using (mem_zeroLocus_iff.mp hx) _ hmem

theorem proof : ChowFormDimLe.Statement := by
  intro F _ n k I f hI hf
  by_contra hdim
  rw [not_le] at hdim
  have := hI.isPrime
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_prime_liesOver (AlgebraicClosure F) I
    (fun g hg => coeff_zero_eq_zero_of_mem hI hg)
  have hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P) := by
    rw [ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]
    exact_mod_cast hdim
  have hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k := by
    intro u
    obtain ⟨x, hx0, hxP, hxu⟩ := exists_ne_zero_common_zero P hPQ hdimP u
    refine ⟨x, hx0, fun g hg => ?_, hxu⟩
    have hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P := by
      rw [← hPI] at hg
      exact hg
    have := hxP _ hgP
    rwa [eval_map, ← aeval_def] at this
  apply hf.1
  apply map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
  apply MvPolynomial.funext
  intro u
  rw [eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]

end ChowFormDimLe

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeHyperplaneNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeHyperplaneNull.proof (hZ : ZeroLocusDimH.Statement) (hC : ChowFormDimLe.Statement) :
    ConeHyperplaneNull.Statement := by
  intro n e h W f u hW hf hu
  have := hW.isPrime
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {linForm u} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) := by
    have h1 := hC ℂ n (e + 1) W f hW hf
    have hr : Ideal.Quotient.mk W (linForm u) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left : W ≤ J))
      (Ideal.Quotient.factor_surjective _) hr
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h3 := h2.trans h1
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = a at h3 ⊢
    induction a using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h3 (by norm_cast)
      | coe m =>
        have : m + 1 ≤ e + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : m ≤ e)

  let g : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hg : ∀ y, g y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective g := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz g).mp hinj

  have hsub : coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0} ⊆
      g ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, hyu⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [linForm, map_sum] using hyu
    intro q hq
    rw [hg]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) <
      (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

end

end GroundTheory.Heights₂.Heights
end

module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.IdealLattice
open NumberField

namespace PI

def IdealLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
      (∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧
        AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} = AddSubgroup.closure {w₁, w₂}) ∧
      area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)}) =
        ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| / 2

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt
open NumberField

namespace PI.IdealLatticeWork

def OKArea : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      |((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im| = Real.sqrt |(NumberField.discr K : ℝ)| / 2

def IdealBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (cc : Ideal (𝓞 K)), cc ≠ ⊥ →
    ∃ c₁ ∈ cc, ∃ c₂ ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = m • c₁ + n • c₂) ∧
      ∃ p q r s : ℤ, c₁ = p • b 0 + q • b 1 ∧ c₂ = r • b 0 + s • b 1 ∧
        (p * s - q * r).natAbs = Ideal.absNorm cc

def OKBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → Nonempty (Module.Basis (Fin 2) ℤ (𝓞 K))

def Assemble : Prop := OKArea → IdealBasis → OKBasis → PI.AreaLat → PI.IdealLattice

end PI.IdealLatticeWork
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdealLattice
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Assemble
open NumberField

namespace PI.IdealLatticeWork

theorem okBasis : OKBasis := by
  intro K _ _ h
  exact ⟨Module.finBasisOfFinrankEq ℤ (𝓞 K) (by rw [NumberField.RingOfIntegers.rank, h])⟩

theorem im_comb (u v : ℂ) (p q r s : ℤ) :
    ((starRingEnd ℂ) ((p : ℂ) * u + (q : ℂ) * v) * ((r : ℂ) * u + (s : ℂ) * v)).im
      = ((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) u * v).im := by
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem im_scale (δ x y : ℂ) :
    ((starRingEnd ℂ) (δ * x) * (δ * y)).im = ‖δ‖ ^ 2 * ((starRingEnd ℂ) x * y).im := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [map_mul, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem phi_comb {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (m n : ℤ) (x y : 𝓞 K) :
    φ ((m • x + n • y : 𝓞 K) : K) = (m : ℂ) * φ (x : K) + (n : ℂ) * φ (y : K) := by
  simp [zsmul_eq_mul]

theorem assemble : Assemble := by
  intro hA hI hB hL K _ _ φ h2 hcx cc δ hcc hδ
  obtain ⟨b⟩ := hB K h2
  obtain ⟨c₁, hc₁, c₂, hc₂, hspan, p, q, r, s, hc1, hc2, hdet⟩ := hI K b cc hcc
  have hgen : AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} =
      AddSubgroup.closure {δ * φ (c₁ : K), δ * φ (c₂ : K)} := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro w ⟨c, hc, rfl⟩
      obtain ⟨m, n, rfl⟩ := hspan c hc
      rw [phi_comb φ m n c₁ c₂]
      have e : δ * ((m : ℂ) * φ (c₁ : K) + (n : ℂ) * φ (c₂ : K)) =
          m • (δ * φ (c₁ : K)) + n • (δ * φ (c₂ : K)) := by
        simp only [zsmul_eq_mul]
        ring
      rw [e]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)
    · rw [AddSubgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact AddSubgroup.subset_closure ⟨c₁, hc₁, rfl⟩
      · exact AddSubgroup.subset_closure ⟨c₂, hc₂, rfl⟩
  have hφc : ∀ c : 𝓞 K, ∀ x y : ℤ, c = x • b 0 + y • b 1 →
      φ (c : K) = (x : ℂ) * φ (b 0 : K) + (y : ℂ) * φ (b 1 : K) := by
    rintro c x y rfl
    exact phi_comb φ x y (b 0) (b 1)
  have him : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im =
      ‖δ‖ ^ 2 * (((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im) := by
    rw [im_scale, hφc c₁ p q hc1, hφc c₂ r s hc2, im_comb]
  have hA' := hA K φ h2 hcx b
  have hd : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| / 2 := by
    have h0 : (NumberField.discr K : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
    exact div_pos (Real.sqrt_pos.mpr (abs_pos.mpr h0)) two_pos
  have hn : Ideal.absNorm cc ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hδ2 : (0 : ℝ) < ‖δ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hδ) 2
  have habs : |((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im| =
      ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) := by
    rw [him, abs_mul, abs_mul, hA', abs_of_pos hδ2, ← hdet, Nat.cast_natAbs, Int.cast_abs]
    ring
  have hpos : (0 : ℝ) < ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) :=
    mul_pos (mul_pos hδ2 (by exact_mod_cast Nat.pos_of_ne_zero hn)) hd
  have hne : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    linarith
  refine ⟨⟨δ * φ (c₁ : K), δ * φ (c₂ : K), hne, hgen⟩, ?_⟩
  rw [hgen]
  change area (PI.lat2 _ _) = _
  rw [(hL _ _ hne).1, habs]
  ring

theorem idealLattice_of (h1 : OKArea) (h2 : IdealBasis) : PI.IdealLattice :=
  assemble h1 h2 okBasis area_lattice_formula

end PI.IdealLatticeWork
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasis
open NumberField

namespace PI.IdealLatticeWork

theorem idealBasis : IdealBasis := by
  intro K _ _ b cc hcc
  classical
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨(bI 0 : 𝓞 K), (bI 0).2, (bI 1 : 𝓞 K), (bI 1).2, ?_, ?_⟩
  · intro c hc
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h := congrArg Subtype.val (bI.sum_repr ⟨c, hc⟩)
    rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower] at h
    exact h.symm
  · refine ⟨b.repr (bI 0) 0, b.repr (bI 0) 1, b.repr (bI 1) 0, b.repr (bI 1) 1, ?_, ?_, ?_⟩
    · have h := b.sum_repr (bI 0 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := b.sum_repr (bI 1 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := Ideal.natAbs_det_basis_change b cc bI
      rw [Module.Basis.det_apply, Matrix.det_fin_two] at h
      simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at h
      rw [← h]
      congr 1
      ring

end PI.IdealLatticeWork
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.OKArea
open NumberField

namespace PI.IdealLatticeWork

theorem sq_det_two (x y : ℂ) :
    (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2
      = (((-4) * (((starRingEnd ℂ) x * y).im) ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> ring

theorem ne_conj {K : Type} [Field K] (φ : K →+* ℂ) (hnr : IsEmpty (K →+* ℝ)) :
    φ ≠ (starRingEnd ℂ).comp φ := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal φ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := congrArg (fun f : K →+* ℂ => f x) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  exact hnr.false hr.embedding

theorem okArea : OKArea := by
  classical
  intro K _ _ φ hK hnr b
  set bQ := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K with hbQ
  have hbQi : ∀ i, bQ i = (b i : K) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K b i
  have hdQ : Algebra.discr ℚ bQ = (NumberField.discr K : ℚ) := by
    rw [hbQ, Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K b,
      NumberField.discr_eq_discr]
    simp

  let φQ : K →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let ψQ : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp φ).toRatAlgHom
  have hne : φQ ≠ ψQ := by
    intro h
    apply ne_conj φ hnr
    ext x
    have := congrArg (fun f : K →ₐ[ℚ] ℂ => f x) h
    simpa [φQ, ψQ] using this
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by
    rw [AlgHom.card ℚ K ℂ, hK]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {φQ, ψQ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have htr : ∀ z : K, algebraMap ℚ ℂ (Algebra.trace ℚ K z) = φ z + (starRingEnd ℂ) (φ z) := by
    intro z
    rw [trace_eq_sum_embeddings ℂ (x := z), huniv, Finset.sum_pair hne]
    simp [φQ, ψQ]
  set x := φ (b 0 : K)
  set y := φ (b 1 : K)

  have key : algebraMap ℚ ℂ (Algebra.discr ℚ bQ) =
      (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2 := by
    rw [Algebra.discr_def, RingHom.map_det, Matrix.det_fin_two]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, htr, hbQi, map_mul]
    ring
  have key2 : ((NumberField.discr K : ℝ) : ℂ) = (x * (starRingEnd ℂ) y - (starRingEnd ℂ) x * y) ^ 2 := by
    rw [← key, hdQ, map_intCast, Complex.ofReal_intCast]
  have hreal : (NumberField.discr K : ℝ) = -4 * ((starRingEnd ℂ) x * y).im ^ 2 := by
    apply Complex.ofReal_injective
    rw [key2, sq_det_two]
  have h4 : |(-4 * ((starRingEnd ℂ) x * y).im ^ 2 : ℝ)| = (2 * |((starRingEnd ℂ) x * y).im|) ^ 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg ((starRingEnd ℂ) x * y).im]), mul_pow, sq_abs]
    ring
  rw [hreal, h4, Real.sqrt_sq (by positivity)]
  ring

end PI.IdealLatticeWork
end

theorem ideal_lattice_basis : PI.IdealLattice :=
  PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis
end

namespace Formalism.MainNotions.Ext

theorem idealLattice_holds : IdealLattice := ideal_lattice_basis

end Formalism.MainNotions.Ext

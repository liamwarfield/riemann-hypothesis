module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormBirational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem pderiv_aeval_eq_sum {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add (f := _), add_mul,
      Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · refine Finset.sum_congr rfl fun b _ => by ring

theorem pderiv_genSubst {K : Type*} [CommRing K] {n k : ℕ} (ζ c : Fin n → K) (i : Fin k) (m : Fin n)
    (j : Fin k × Fin n) :
    pderiv (i, m) (genSubst ζ c j) =
      (if j = (i, m) then 1 else 0) - (if j.1 = i then C (ζ m) * C (c j.2) else 0) := by
  classical
  obtain ⟨j₁, j₂⟩ := j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [genSubst, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
    map_sum, pderiv_X, Pi.single_apply, mul_zero]
  by_cases h : j₁ = i
  · subst h
    simp [Prod.ext_iff, eq_comm, mul_comm]
  · simp [Prod.ext_iff, h]

theorem not_dvd_pderiv_of_degreeOf_pos {F σ : Type*} [Field F] [CharZero F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hi : 0 < degreeOf i g) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hne : pderiv i g ≠ 0 := by
    obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup g.support (support_nonempty.2 hg) (fun m => m i)
    rw [← degreeOf_eq_sup] at hsd
    have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single i 1)) h0
    simp only [coeff_pderiv, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at this
    have hcs : AddMonoidAlgebra.coeff g s ≠ 0 := mem_support_iff.1 hs
    have hsi : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : F) + 1 ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero hcs hsi this
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem ChowFormBirational.proof (h₁ : IncidenceGeneric.Statement)
    (h₂ : ChowFormMultiHomog.Statement) : ChowFormBirational.Statement := by
  intro F _ _ n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (k + 1) P g hP hg
  obtain ⟨s, hs⟩ := support_nonempty.2 hg.1
  obtain ⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by
    by_contra hcon
    push Not at hcon
    have hw := congrFun (hhom (mem_support_iff.1 hs)) 0
    have : (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      obtain ⟨x₁, x₂⟩ := x
      by_cases hx : x₁ = 0
      · subst hx; simp [Nat.le_zero.1 (hcon x₂)]
      · simp [groupWeight, hx]
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩
  have hdeg : 0 < degreeOf (0, l) g := lt_of_lt_of_le hl (monomial_le_degreeOf _ hs)
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_degreeOf_pos hg.1 hdeg
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthQuotientDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

theorem LengthQuotientDet.ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type*} (s : Finset ι)
    (a : ι → O) (ha : ∀ i, a i ≠ 0) : Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha j)), ih]

theorem LengthQuotientDet.proof : LengthQuotientDet.Statement := by
  intro O _ _ _ M _ _ _ _ φ hdet
  classical
  have hinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.mp (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hdet))
  set ι := Module.Free.ChooseBasisIndex O M
  let b := Module.Free.chooseBasis O M
  have hrank : finrank O (LinearMap.range φ) = finrank O M := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hlen : Module.length O (M ⧸ LinearMap.range φ) = ∑ i, Ring.ord O (a i) := by
    rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let v : Basis ι O M := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hv : ∀ i, φ (v i) = a i • b' i := by
    intro i
    have h1 : φ (v i) = ((LinearEquiv.ofInjective φ hinj) (v i) : M) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [v, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det v = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑v) = fun i => a i • b' i := funext hv
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  have hassoc : Associated (LinearMap.det φ) (∏ i, a i) := by
    obtain ⟨u, hu⟩ := b'.isUnit_det v
    exact ⟨u, by rw [hu]; exact hdetprod⟩
  rw [hlen, Ring.ord_eq_of_associated hassoc, LengthQuotientDet.ord_prod _ _ ha]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PProjNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjNullstellensatz.proof (h₁ : FGNullstellensatz.Statement) :
    ProjNullstellensatz.Statement := by
  intro F _ n P hP
  have : P.IsPrime := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  set D := MvPolynomial (Fin n) F ⧸ P
  have hr : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  have hφ : ∃ φ : D →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P (X j)) ≠ 0 := by
    by_contra hne
    apply hr
    refine h₁ F D _ (fun φ => ?_)
    by_contra h
    exact hne ⟨φ, h⟩
  obtain ⟨φ, hφj⟩ := hφ
  have hcomp : φ.comp (Ideal.Quotient.mkₐ F P) = aeval (fun i => φ (Ideal.Quotient.mk P (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_, ?_⟩
  · intro h0
    exact hφj (congrFun h0 j)
  · intro g hg
    rw [← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FGNullstellensatz.full : FGNullstellensatz.Statement :=
  FGNullstellensatz.proof

theorem ProjNullstellensatz.full : ProjNullstellensatz.Statement :=
  ProjNullstellensatz.proof FGNullstellensatz.full

theorem IncidenceGeneric.full : IncidenceGeneric.Statement :=
  IncidenceGeneric.proof FGNullstellensatz.full

theorem IncIdealPrime.full : IncIdealPrime.Statement :=
  IncIdealPrime.proof IncidenceGeneric.full

theorem ChowFormMultiHomog.full : ChowFormMultiHomog.Statement :=
  ChowFormMultiHomog.proof ProjNullstellensatz.full

theorem GenericLinearTrdeg.full : GenericLinearTrdeg.Statement :=
  GenericLinearTrdeg.proof

theorem MinimalPrimeHomog.full : MinimalPrimeHomog.Statement :=
  MinimalPrimeHomog.proof

theorem ConeDimComponent.full : ConeDimComponent.Statement :=
  ConeDimComponent.proof MinimalPrimeHomog.full

theorem LengthQuotientDet.full : LengthQuotientDet.Statement :=
  LengthQuotientDet.proof

theorem OrdPolynomialLocalization.full : OrdPolynomialLocalization.Statement :=
  OrdPolynomialLocalization.proof

theorem ChowFormBirational.full : ChowFormBirational.Statement :=
  ChowFormBirational.proof IncidenceGeneric.full ChowFormMultiHomog.full

theorem IncIdealDim.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    IncIdealDim.Statement :=
  IncIdealDim.proof IncidenceGeneric.full GenericLinearTrdeg.full hA

theorem ConeDimOfChowForm.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ConeDimOfChowForm.Statement :=
  ConeDimOfChowForm.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

theorem ChowFormExists.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ChowFormExists.Statement :=
  ChowFormExists.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

end GroundTheory.Heights₂.Heights

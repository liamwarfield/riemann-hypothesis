module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCase
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNorm.FieldCase

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [Field K] [Algebra F K]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR K e) = inclR K (σ e) := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (x : K ⊗[F] E) :
    sigR K σ (sigR K σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) K) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective

theorem hR_eq_hf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → K ⊗[F] E) :
    hR K σ J x y = GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose y x := by
  simp only [hR, Formalism.UG.hform, GlobalTheory.UTrans.hf, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Alg

theorem exists_unitNorm_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hJ hunit hiso a b ha hb
  have hinj := inclR_injective (F := F) (E := E) K
  haveI : Nontrivial (K ⊗[F] E) := hinj.nontrivial
  haveI : CharZero (K ⊗[F] E) := charZero_of_injective_algebraMap (algebraMap F (K ⊗[F] E)).injective
  have hfield : IsField (K ⊗[F] E) :=
    ⟨exists_pair_ne _, mul_comm, fun {x} hx => (hunit x hx).exists_right_inv⟩
  letI : Field (K ⊗[F] E) := hfield.toField
  have hG : GlobalTheory.UTrans.IsHerm (sigR K σ) (JR K J).transpose :=
    { invol := sigR_sigR K σ (GlobalTheory.HermLineZeros.conj_invol hcm)
      ne_id := by
        obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
        exact ⟨inclR K d, fun h => hd (hinj (by rw [← sigR_inclR]; exact h))⟩
      herm := fun p q => by
        simp only [Matrix.transpose_apply, JR, Matrix.map_apply, sigR_inclR]
        rw [hJ.1 p q]
      det_ne := by
        rw [Matrix.det_transpose, JR, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        intro h
        exact hJ.2 (hinj (by rw [h, map_zero])) }
  have hsymm : ∀ x y, sigR K σ (hR K σ J x y) = hR K σ J y x := by
    intro x y
    rw [hR_eq_hf, hR_eq_hf, GlobalTheory.UTrans.IsoBasis.hf_symm hG]
  obtain ⟨u, hu0, huu⟩ := hiso
  have hz : ∃ z, z ≠ 0 ∧ GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose z z = 0 := ⟨u, hu0, by rw [← hR_eq_hf]; exact huu⟩
  obtain ⟨e, he, hne⟩ := GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid hG hz
    ![GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose a, GlobalTheory.UTrans.IsoBasis.hfL (sigR K σ) (JR K J).transpose b] (by
      intro i
      fin_cases i
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG ha
      · exact GlobalTheory.UTrans.IsoBasis.hfL_ne hG hb)
  have hee : hR K σ J e e = 0 := by rw [hR_eq_hf]; exact he
  have h1 : hR K σ J a e ≠ 0 := by
    rw [hR_eq_hf]; exact hne 0
  have h2 : hR K σ J e b ≠ 0 := by
    intro h
    apply hne 1
    change GlobalTheory.UTrans.hf (sigR K σ) (JR K J).transpose e b = 0
    rw [← hR_eq_hf, ← hsymm, h, map_zero]
  refine ⟨e, ⟨hR K σ J a e, isUnit_iff_ne_zero.2 h1, ?_⟩, ⟨hR K σ J e b, isUnit_iff_ne_zero.2 h2, ?_⟩⟩
  · rw [hsymm, gram2R, hee]; ring
  · rw [hsymm, gram2R, hee]; ring

end GlobalTheory.PlaneNorm.FieldCase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNormGramDetPairFieldCaseStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitNorm_gramDet_pair_fieldCase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ a b : Fin M → K ⊗[F] E, a ≠ 0 → b ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J a w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w b)) := by
  first | exact @GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair | exact GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair | (intros; apply GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNe
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GramVec

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
  {J : Matrix (Fin M) (Fin M) E}

theorem hE_add_smul_right (z u v : Fin M → E) (c : E) :
    hE σ J z (u + c • v) = hE σ J z u + c * hE σ J z v := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_left (z u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) z = hE σ J u z + σ c * hE σ J v z := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_self (u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) (u + c • v) =
      hE σ J u u + c * hE σ J u v + σ c * hE σ J v u + σ c * c * hE σ J v v := by
  rw [hE, GlobalTheory.HermLineZeros.hform_expand]
  rfl

theorem hE_single (i j : Fin M) : hE σ J (Pi.single i 1) (Pi.single j 1) = J i j :=
  GlobalTheory.HermLineZeros.hform_single _ J i j

theorem hermitianGramDetTwoVectors_comm (x z : Fin M → E) : gram2E σ J x z = gram2E σ J z x := by
  unfold gram2E; ring

noncomputable def gramPoly (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (z a b : Fin M → E) : Polynomial E :=
  Polynomial.C (hE σ J z z) * (Polynomial.C (hE σ J a a) + Polynomial.X * Polynomial.C (hE σ J a b + hE σ J b a)
      + Polynomial.X ^ 2 * Polynomial.C (hE σ J b b))
    - (Polynomial.C (hE σ J z a) + Polynomial.X * Polynomial.C (hE σ J z b))
      * (Polynomial.C (hE σ J a z) + Polynomial.X * Polynomial.C (hE σ J b z))

theorem hermitianGramDetTwoVectors_eval_line (z a b : Fin M → E) (t : E) (ht : σ t = t) :
    gram2E σ J z (a + t • b) = (gramPoly σ J z a b).eval t := by
  unfold gram2E gramPoly
  rw [hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, ht]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem exists_gram2E_ne (h : IsCMExt F E σ) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    (z : Fin M → E) (hz : hE σ J z z ≠ 0) : ∃ w, gram2E σ J z w ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set a : Fin M → E := fun i => hE σ J (Pi.single i 1) z
  set b : Fin M → E := fun j => hE σ J z (Pi.single j 1)
  have hdiag : ∀ i, hE σ J z z * J i i - b i * a i = 0 := fun i => by
    have := hc (Pi.single i 1)
    simpa [gram2E, hE_single] using this
  have key : hE σ J z z • J = Matrix.vecMulVec a b := by
    ext i j
    have e1 := hc (Pi.single i 1 + (1 : E) • Pi.single j 1)
    have e2 := hc (Pi.single i 1 + d • Pi.single j 1)
    simp only [gram2E, hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, hE_single,
      map_one] at e1 e2
    have e0i := hdiag i
    have e0j := hdiag j
    have : (d - σ d) * (hE σ J z z * J i j - a i * b j) = 0 := by
      simp only [a, b] at e0i e0j ⊢
      linear_combination e2 - e0i - σ d * d * e0j - σ d * (e1 - e0i - e0j)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hd
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      exact sub_eq_zero.1 h0
  have hdet : (hE σ J z z • J).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz) hJ.2
  have hunit : IsUnit (hE σ J z z • J) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hr := Matrix.rank_of_isUnit _ hunit
  have hle : (Matrix.vecMulVec a b).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq Unit]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  rw [key, Fintype.card_fin] at hr
  omega

end CM

end GlobalTheory.GramVec

open GlobalTheory.GramVec in
theorem GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  intro F E _ _ _ _ _ σ h M J hM hJ x y hx hy
  obtain ⟨w0, h0⟩ := exists_gram2E_ne h hM hJ x hx
  obtain ⟨w1, h1⟩ := exists_gram2E_ne h hM hJ y hy
  set Px := gramPoly σ J x w0 (w1 - w0)
  set Py := gramPoly σ J y w0 (w1 - w0)
  have hPx : Px ≠ 0 := by
    intro h0'
    apply h0
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) x w0 (w1 - w0) 0 (map_zero σ)
    rw [zero_smul, add_zero] at this
    rw [this]; change Polynomial.eval 0 Px = 0; rw [h0', Polynomial.eval_zero]
  have hPy : Py ≠ 0 := by
    intro h1'
    apply h1
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) y w0 (w1 - w0) 1 (map_one σ)
    rw [one_smul, add_sub_cancel] at this
    rw [this]; change Polynomial.eval 1 Py = 0; rw [h1', Polynomial.eval_zero]
  have hfin : {f : F | Px.IsRoot (algebraMap F E f) ∨ Py.IsRoot (algebraMap F E f)}.Finite := by
    have := ((Polynomial.finite_setOf_isRoot hPx).union (Polynomial.finite_setOf_isRoot hPy)).preimage
      (FaithfulSMul.algebraMap_injective F E).injOn
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨f, hf⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, Polynomial.IsRoot.def] at hf
  have hfix : σ (algebraMap F E f) = algebraMap F E f := σ.commutes f
  refine ⟨w0 + algebraMap F E f • (w1 - w0), ?_, ?_⟩
  · rw [hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.1
  · rw [hermitianGramDetTwoVectors_comm, hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  first | exact @GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | exact GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | (intros; apply GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjective
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormDichotomy

theorem unit_or_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  intro F E _ _ _ _ _ σ h K _ _

  obtain ⟨e, he⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set d : E := e - σ e with hd
  have hσd : σ d = -d := by
    rw [hd, map_sub, GlobalTheory.HermLineZeros.conj_invol h]; ring
  have hd0 : d ≠ 0 := by
    intro h0; apply he; rw [hd, sub_eq_zero] at h0; exact h0.symm
  have hfix : σ (d * d) = d * d := by rw [map_mul, hσd]; ring
  obtain ⟨c0, hc0⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h _ hfix
  haveI : CharZero F := inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  set L := K ⊗[F] E
  set ι := algebraMap K L with hι
  set D : L := inclR K d with hD
  set c : K := algebraMap F K c0 with hc
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; apply hd0; rw [map_zero] at hc0; exact mul_self_eq_zero.1 hc0.symm
  have hcne : c ≠ 0 := by rw [hc]; exact (map_ne_zero _).2 hc0ne
  have hDD : D * D = ι c := by
    rw [hD, ← map_mul, ← hc0, hc, hι, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes c0
  have hsD : sigR K σ D = -D := by
    show inclR K (σ d) = _
    rw [hσd, map_neg]
  have hst : ∀ t : K, sigR K σ (ι t) = ι t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl

  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst0
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst0
    have e2 := congrArg σ hst0
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσd, map_zero] at e2
    have ht : algebraMap F E t * d = 0 := by linear_combination (hst0 - e2) / 2
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 ht with h1 | h1
      · exact (map_eq_zero _).1 h1
      · exact absurd h1 hd0
    refine ⟨?_, ht0⟩
    rw [ht0, map_zero, zero_mul, add_zero] at hst0
    exact (map_eq_zero _).1 hst0
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bK := Algebra.TensorProduct.basis K b
  have hdec : ∀ a : L, ∃ u v : K, a = ι u + ι v * D := by
    intro a
    refine ⟨bK.repr a 0, bK.repr a 1, ?_⟩
    conv_lhs => rw [← bK.sum_repr a]
    rw [Fin.sum_univ_two]
    have hb : ⇑b = ![(1 : E), d] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have h0 : bK 0 = 1 := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_zero]; rfl
    have h1 : bK 1 = D := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_one, Matrix.head_cons]; rfl
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  by_cases hsq : ∃ r : K, r * r = c
  · right
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hcne (by rw [← hr, mul_zero])
    have h2 : ι (1 / 2) * 2 = 1 := by
      rw [show (2 : L) = ι 2 from (map_ofNat ι 2).symm, ← map_mul]; norm_num
    have hs : ι r * ι r⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
    have hD2 : D * D = ι r * ι r := by rw [hDD, ← hr, map_mul]
    set ε : L := ι (1 / 2) * (1 + ι r⁻¹ * D) with hε
    have he0 : ε * (1 - ε) = 0 := by
      rw [hε]
      linear_combination (-(1 + ι r⁻¹ * D) * ι (1 / 2)) * h2 + (-ι (1 / 2) ^ 2 * ι r⁻¹ ^ 2) * hD2 + (-ι (1 / 2) ^ 2 * (ι r⁻¹ * ι r + 1)) * hs
    have hσε : sigR K σ ε = 1 - ε := by
      rw [hε, map_mul, map_add (f := _), map_mul, map_one, hst, hst, hsD]
      linear_combination h2
    intro k _
    refine ⟨ι k * ε + (1 - ε), ?_⟩
    rw [map_add (f := _), map_mul, map_sub, map_one, hst, hσε]
    linear_combination (ι k ^ 2 + 1 - 2 * ι k) * he0
  · left
    push_neg at hsq
    intro a ha
    obtain ⟨u, v, rfl⟩ := hdec a
    have hn : u * u - c * (v * v) ≠ 0 := by
      intro h0
      by_cases hv : v = 0
      · apply ha
        have : u * u = 0 := by rw [hv] at h0; simpa using h0
        rw [mul_self_eq_zero.1 this, hv, map_zero, zero_mul, add_zero]
      · apply hsq (u / v)
        field_simp
        linear_combination h0
    have hN : (ι u + ι v * D) * sigR K σ (ι u + ι v * D) = ι (u * u - c * (v * v)) := by
      rw [map_add (f := _), map_mul, hst, hst, hsD, map_sub, map_mul, map_mul, map_mul]
      linear_combination (-(ι v * ι v)) * hDD
    refine IsUnit.of_mul_eq_one (sigR K σ (ι u + ι v * D) * ι (u * u - c * (v * v))⁻¹) ?_
    rw [← mul_assoc, hN, ← map_mul, mul_inv_cancel₀ hn, map_one]

end GlobalTheory.NormDichotomy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjectiveStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorCM_isField_or_norm_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  first | exact @GlobalTheory.NormDichotomy.unit_or_norm | exact GlobalTheory.NormDichotomy.unit_or_norm | (intros; apply GlobalTheory.NormDichotomy.unit_or_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitian
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_local_unitNorm_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hM hJ hiso x y hx hy
  have hinj : Function.Injective (inclR (F := F) K : E →+* K ⊗[F] E) := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hne : ∀ z : Fin M → E, hE σ J z z ≠ 0 → ((fun i => inclR K (z i)) : Fin M → K ⊗[F] E) ≠ 0 := by
    intro z hz h0
    apply hz
    have hz0 : z = 0 := funext fun i => hinj (by simpa using congrFun h0 i)
    subst hz0
    simp [hE, Formalism.UG.hform]
  rcases GlobalTheory.T.tensorCM_isField_or_norm_surjective F E σ hcm K with hfld | hspl
  · exact GlobalTheory.T.exists_unitNorm_gramDet_pair_fieldCase F E σ hcm K M J hJ hfld hiso _ _ (hne x hx) (hne y hy)
  · obtain ⟨w, hxw, hwy⟩ := GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne F E σ hcm M J hM hJ x y hx hy
    have hs : ∀ e : E, sigR K σ (inclR K e) = inclR K (σ e) := fun e => rfl
    have hRE : ∀ a b : Fin M → E, hR K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (hE σ J a b) := by
      intro a b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, hs, JR, Matrix.map_apply, RingHom.coe_coe]
    have hG : ∀ a b : Fin M → E, gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (gram2E σ J a b) := by
      intro a b
      simp only [gram2R, gram2E, hRE, map_sub, map_mul]
    have hsym : ∀ a b : Fin M → E, σ (hE σ J a b) = hE σ J b a := by
      intro a b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, GlobalTheory.HermLineZeros.conj_invol hcm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hJ.1]
      ring
    have hfix : ∀ a b : Fin M → E, σ (gram2E σ J a b) = gram2E σ J a b := by
      intro a b
      simp only [gram2E, map_sub, map_mul, hsym]
      ring
    have key : ∀ a b : Fin M → E, gram2E σ J a b ≠ 0 →
        IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)))) := by
      intro a b hab
      obtain ⟨g, hg⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hcm _ (hfix a b)
      have hg0 : g ≠ 0 := by rintro rfl; exact hab (by rw [← hg, map_zero])
      have hk : algebraMap F K (-g) ≠ 0 := by
        rw [map_neg, neg_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap F K).injective]; exact hg0
      obtain ⟨t, ht⟩ := hspl _ hk
      have hval : -(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i))) =
          algebraMap K (K ⊗[F] E) (algebraMap F K (-g)) := by
        rw [hG, ← hg, map_neg, map_neg]
        congr 1
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes g
      have hu : IsUnit (t * sigR K σ t) := by
        rw [ht]; exact (IsUnit.mk0 _ hk).map _
      exact ⟨t, isUnit_of_mul_isUnit_left hu, by rw [ht, hval]⟩
    exact ⟨fun i => inclR K (w i), key x w hxw, key w y hwy⟩

end GlobalTheory.PlaneNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitianStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  first | exact @GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | exact GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | (intros; apply GlobalTheory.PlaneNorm.exists_local_unitNorm_vector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetPlaneReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetPlaneReduction
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaneNormReduce

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hE_sub_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b y : Fin M → E) (c : E) :
    hE σ J (a - c • b) y = hE σ J a y - σ c * hE σ J b y := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_sub_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y a b : Fin M → E) (c : E) :
    hE σ J y (a - c • b) = hE σ J y a - c * hE σ J y b := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_swap' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (x y : Fin M → E) : hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

end Alg

theorem sigma_sigma' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem reduce : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x z : Fin M → E, hE σ J x x ≠ 0 → IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) → hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0 := by
  intro F E _ _ _ _ _ σ hCM K _ _ M J hJ x z hx hN
  have hσ := sigma_sigma' σ hCM
  set a := hE σ J x x with ha
  set c := hE σ J x z / a with hc
  set q := hE σ J (z - c • x) (z - c • x) with hq
  have hsa : σ a = a := (hE_swap' σ hσ J hJ x x).symm
  have hzx : hE σ J z x = σ (hE σ J x z) := hE_swap' σ hσ J hJ x z
  have hsc : σ c = hE σ J z x / a := by rw [hc, map_div₀, hsa, hzx]

  have hqa : q * a = gram2E σ J x z := by
    rw [hq, hE_sub_smul_left, hE_sub_smul_right, hE_sub_smul_right, hsc, hc, gram2E]
    field_simp
    ring

  obtain ⟨s, hs, hss⟩ := hN
  have hinj : Function.Injective (inclR (F := F) (E := E) K) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hG : gram2E σ J x z ≠ 0 := by
    intro h0
    rw [h0, map_zero, neg_zero] at hss
    have hu : IsUnit (0 : K ⊗[F] E) := by
      rw [← hss]; exact hs.mul (hs.map (sigR K σ))
    have h01 : (0 : K ⊗[F] E) = 1 := isUnit_zero_iff.mp hu
    have : inclR (F := F) K (0 : E) = inclR (F := F) K 1 := by rw [map_zero, map_one, h01]
    exact zero_ne_one (hinj this)
  have hq0 : q ≠ 0 := by
    intro h0; apply hG; rw [← hqa, h0, zero_mul]
  refine ⟨hq0, ?_⟩

  set v : K ⊗[F] E := ↑(hs.unit⁻¹) with hv
  have h1 : v * s = 1 := by rw [hv]; exact hs.val_inv_mul
  have h2 : sigR K σ v * sigR K σ s = 1 := by rw [← map_mul, h1, map_one]
  refine ⟨inclR K a * v, ?_⟩
  have hw : IsUnit (s * sigR K σ s) := hs.mul (hs.map (sigR K σ))
  apply hw.mul_left_eq_zero.mp
  have e1 : inclR K a * v * sigR K σ (inclR K a * v) * (s * sigR K σ s) = inclR K (a * a) := by
    rw [map_mul, sigR_inclR', hsa]
    calc inclR K a * v * (inclR K a * sigR K σ v) * (s * sigR K σ s)
        = inclR K a * inclR K a * (v * s) * (sigR K σ v * sigR K σ s) := by ring
      _ = inclR K (a * a) := by rw [h1, h2, map_mul]; ring
  have e2 : inclR K (a / q) * (s * sigR K σ s) = - inclR K (a * a) := by
    rw [hss, mul_neg, ← map_mul, ← hqa]
    congr 2
    field_simp
  rw [add_mul, e1, e2, add_neg_cancel]

end GlobalTheory.PlaneNormReduce
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetPlaneReductionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitNorm_gramDet_plane_reduction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x z : Fin M → E, hE σ J x x ≠ 0 → IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) → hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0 := by
  first | exact @GlobalTheory.PlaneNormReduce.reduce | exact GlobalTheory.PlaneNormReduce.reduce | (intros; apply GlobalTheory.PlaneNormReduce.reduce <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetRationalApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetRationalApproximation
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm Topology
open scoped TensorProduct

namespace GlobalTheory.PlaneNormApprox

variable {F E : Type} [Field F] [Field E] [Algebra F E]

section Alg

variable (K : Type) [Field K] [Algebra F K]

theorem sigR_inclR' (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR (F := F) K e) = inclR K (σ e) := by
  simp [sigR, inclR]

theorem sigR_algebraMap' (σ : E →ₐ[F] E) (k : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) k) = algebraMap K (K ⊗[F] E) k := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem hR_incl (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR K σ J (fun i => inclR K (x i)) (fun i => inclR K (y i)) = inclR K (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hR, hE, Formalism.UG.hform, JR, map_sum, map_mul, sigR_inclR']

theorem hermitianGramDetTwoVectorsTensor_incl (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    gram2R K σ J (fun i => inclR K (x i)) (fun i => inclR K (y i)) = inclR K (gram2E σ J x y) := by
  simp only [gram2R, gram2E, hR_incl, map_sub, map_mul]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (u : K ⊗[F] E) : sigR K σ (sigR K σ u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem sigR_hR {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin M → K ⊗[F] E) :
    sigR K σ (hR K σ J a b) = hR K σ J b a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR K hσ, JR, Matrix.map_apply, sigR_inclR', hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_gram2R {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin M → K ⊗[F] E) :
    sigR K σ (gram2R K σ J a b) = gram2R K σ J a b := by
  simp only [gram2R, map_sub, map_mul, sigR_hR K hσ hJ]
  ring

theorem exists_lam [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ lam : K ⊗[F] E →ₗ[K] K, ∀ u, u + sigR K σ u = algebraMap K (K ⊗[F] E) (lam u) := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  let φ' : E →ₗ[F] F := φ ∘ₗ (LinearMap.id + σ.toLinearMap)
  have hφ' : ∀ e, algebraMap F E (φ' e) = e + σ e := by
    intro e
    obtain ⟨f, hf⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h (e + σ e)
      (by rw [map_add (f := _), GlobalTheory.HermLineZeros.conj_invol h, add_comm])
    have h1 : φ' e = φ (e + σ e) := rfl
    rw [h1, ← hf]
    have := LinearMap.congr_fun hφ f
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.id_apply] at this
    rw [this]
  refine ⟨(TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap ∘ₗ φ'.baseChange K, fun u => ?_⟩
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    have h2 : sigR K σ (k ⊗ₜ[F] e) = k ⊗ₜ[F] σ e := rfl
    rw [h2, ← TensorProduct.tmul_add, ← hφ', Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    simp [Algebra.TensorProduct.algebraMap_apply]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ← ha, ← hb]; abel

theorem two_ne_zero' (F₀ K₀ : Type) [Field F₀] [CharZero F₀] [Field K₀] [Algebra F₀ K₀] : (2 : K₀) ≠ 0 := by
  have : (2 : K₀) = algebraMap F₀ K₀ 2 := (map_ofNat (algebraMap F₀ K₀) 2).symm
  rw [this]
  exact (map_ne_zero _).2 two_ne_zero

end Alg

section Top

variable [NumberField F] [NumberField E] (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K]

def sigRK (σ : E →ₐ[F] E) : K ⊗[F] E →ₗ[K] K ⊗[F] E where
  toFun := sigR K σ
  map_add' := map_add _
  map_smul' k u := by
    rw [Algebra.smul_def, map_mul, sigR_algebraMap', RingHom.id_apply, Algebra.smul_def]

variable [IsModuleTopology K (K ⊗[F] E)] [IsTopologicalRing (K ⊗[F] E)]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR K σ) :=
  IsModuleTopology.continuous_of_linearMap (sigRK K σ)

theorem continuous_hR {X : Type} [TopologicalSpace X] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {f g : X → Fin M → K ⊗[F] E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => hR K σ J (f t) (g t) := by
  unfold hR Formalism.UG.hform
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR K σ).comp ((continuous_apply i).comp hf)).mul continuous_const).mul
    ((continuous_apply j).comp hg)

theorem continuous_gram2R {X : Type} [TopologicalSpace X] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {f g : X → Fin M → K ⊗[F] E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => gram2R K σ J (f t) (g t) := by
  unfold gram2R
  exact ((continuous_hR K σ J hf hf).mul (continuous_hR K σ J hg hg)).sub
    ((continuous_hR K σ J hf hg).mul (continuous_hR K σ J hg hf))

theorem isUnitNorm_nhds {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {a₀ : K ⊗[F] E} (ha : IsUnitNorm K σ a₀)
    (hfix : sigR K σ a₀ = a₀) : ∀ᶠ b in 𝓝 a₀, sigR K σ b = b → IsUnitNorm K σ b := by
  obtain ⟨lam, hlam⟩ := exists_lam K h
  have h2 := two_ne_zero' F K
  set ι := algebraMap K (K ⊗[F] E) with hι
  have hcancel : ∀ b c : K ⊗[F] E, b + b = c + c → b = c := by
    intro b c hbc
    have e1 : ι 2 * b = ι 2 * c := by rw [map_ofNat, two_mul, two_mul, hbc]
    have hu : IsUnit (ι 2) := (IsUnit.mk0 _ h2).map ι
    exact hu.mul_left_cancel e1
  set k₀ := lam a₀ with hk₀def
  have hk₀ : ι k₀ = a₀ + a₀ := by rw [hk₀def, ← hlam, hfix]
  have hk0 : k₀ ≠ 0 := by
    intro hk
    have : a₀ = 0 := hcancel _ _ (by rw [← hk₀, hk, map_zero, add_zero])
    exact ha.isUnit.ne_zero this
  obtain ⟨U, hU, hUsq⟩ := GlobalTheory.sqOpen_of_two_ne_zero K h2 {μ | μ ≠ 0} (isOpen_ne.mem_nhds one_ne_zero)
  have hc : Continuous fun b => lam b / k₀ := (IsModuleTopology.continuous_of_linearMap lam).div_const k₀
  have hmem : (fun b => lam b / k₀) ⁻¹' U ∈ 𝓝 a₀ :=
    hc.continuousAt.preimage_mem_nhds (by simpa [← hk₀def, div_self hk0] using hU)
  filter_upwards [hmem] with b hb hbfix
  obtain ⟨μ, hμ0, hμ⟩ := hUsq _ hb
  obtain ⟨s, hs, hss⟩ := ha
  refine ⟨ι μ * s, ((IsUnit.mk0 _ hμ0).map ι).mul hs, ?_⟩
  apply hcancel
  rw [map_mul, sigR_algebraMap']
  have e2 : ι (lam b) = b + b := by rw [← hlam, hbfix]
  have e3 : lam b = μ ^ 2 * k₀ := by rw [hμ]; field_simp
  rw [← e2, e3, map_mul, hk₀, ← hss, map_pow]
  ring

theorem isOpen_unitNorm {X : Type} [TopologicalSpace X] {σ : E →ₐ[F] E} (h : IsCMExt F E σ)
    {f : X → K ⊗[F] E} (hf : Continuous f) (hfix : ∀ t, sigR K σ (f t) = f t) :
    IsOpen {t | IsUnitNorm K σ (f t)} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  filter_upwards [hf.continuousAt.eventually (isUnitNorm_nhds K h ht (hfix t))] with s hs using hs (hfix s)

theorem dense_inclR (hd : DenseRange (algebraMap F K)) : Dense (Set.range (inclR (F := F) (E := E) K)) := by
  let S : AddSubgroup (K ⊗[F] E) := (inclR (F := F) (E := E) K).range.toAddSubgroup
  have hS : (S.topologicalClosure : Set (K ⊗[F] E)) = closure (Set.range (inclR (F := F) (E := E) K)) := by
    rw [AddSubgroup.topologicalClosure_coe]
    rfl
  intro u
  rw [← hS]
  induction u using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add a b ha hb => exact add_mem ha hb
  | tmul k e =>
    refine hd.induction_on (p := fun k => k ⊗ₜ[F] e ∈ S.topologicalClosure) k ?_ ?_
    · have hc : Continuous fun k : K => k ⊗ₜ[F] e := by
        have : (fun k : K => k ⊗ₜ[F] e) = fun k => k • ((1 : K) ⊗ₜ[F] e) := by
          funext k; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact (continuous_id : Continuous fun k : K => k).smul (continuous_const : Continuous fun _ : K => (1 : K) ⊗ₜ[F] e)
      exact S.isClosed_topologicalClosure.preimage hc
    · intro c
      apply S.le_topologicalClosure
      refine ⟨c • e, ?_⟩
      simp [inclR, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem dense_ratVec (hd : DenseRange (algebraMap F K)) (M : ℕ) :
    Dense (Set.range fun z : Fin M → E => fun i => inclR (F := F) K (z i)) := by
  have e1 : (Set.range fun z : Fin M → E => fun i => inclR (F := F) K (z i)) =
      Set.univ.pi (fun _ => Set.range (inclR (F := F) (E := E) K)) := by
    ext v
    simp only [Set.mem_range, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, rfl⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext hz⟩
  rw [e1]
  intro v
  rw [closure_pi_set]
  intro i _
  rw [(dense_inclR K hd).closure_eq]
  trivial

end Top

section Expand

variable {A : Type} [CommRing A] {M : ℕ}

theorem hform_add_smul_right (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (a b d : Fin M → A) (c : A) :
    Formalism.UG.hform s J a (b + c • d) = Formalism.UG.hform s J a b + c * Formalism.UG.hform s J a d := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_add_smul_left (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (a b d : Fin M → A) (c : A) :
    Formalism.UG.hform s J (b + c • d) a = Formalism.UG.hform s J b a + s c * Formalism.UG.hform s J d a := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Expand

theorem approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K],
    DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ x y : Fin M → E, hE σ J x x ≠ 0 → ∀ w : Fin M → K ⊗[F] E,
    IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) →
    IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) →
    ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) ∧
      IsUnitNorm K σ (-(inclR K (gram2E σ J z y))) := by
  intro F E _ _ _ _ _ σ h K _ _ _ hd M J hJ x y hxx w h1 h2
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  have hσ := GlobalTheory.HermLineZeros.conj_invol h
  set xb : Fin M → K ⊗[F] E := fun i => inclR K (x i) with hxb
  set yb : Fin M → K ⊗[F] E := fun i => inclR K (y i) with hyb
  set ι := algebraMap K (K ⊗[F] E) with hι

  set U1 := {v : Fin M → K ⊗[F] E | IsUnitNorm K σ (-(gram2R K σ J xb v))} with hU1def
  set U2 := {v : Fin M → K ⊗[F] E | IsUnitNorm K σ (-(gram2R K σ J v yb))} with hU2def
  have hU1 : IsOpen U1 := isOpen_unitNorm K h
    ((continuous_gram2R K σ J continuous_const continuous_id).neg)
    (fun v => by rw [map_neg, sigR_gram2R K hσ hJ.1])
  have hU2 : IsOpen U2 := isOpen_unitNorm K h
    ((continuous_gram2R K σ J continuous_id continuous_const).neg)
    (fun v => by rw [map_neg, sigR_gram2R K hσ hJ.1])

  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hφ1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  let ψ : E →ₗ[F] F := φ ∘ₗ LinearMap.mulLeft F (hE σ J x x)⁻¹
  have hψ : ψ (hE σ J x x) = 1 := by
    change φ ((hE σ J x x)⁻¹ * hE σ J x x) = 1
    rw [inv_mul_cancel₀ hxx, hφ1]
  let lam : K ⊗[F] E →ₗ[K] K := (TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap ∘ₗ ψ.baseChange K
  have hlamι : ∀ e, lam (inclR K e) = algebraMap F K (ψ e) := by
    intro e
    simp [lam, inclR, Algebra.algebraMap_eq_smul_one]
  have hlamA : lam (hR K σ J xb xb) = 1 := by
    rw [hxb, hR_incl, hlamι, hψ, map_one]
  have hlamsmul : ∀ (k : K) (u : K ⊗[F] E), lam (ι k * u) = k * lam u := by
    intro k u
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]

  let wε : K → Fin M → K ⊗[F] E := fun ε => w + ι ε • xb
  have hsig : ∀ ε, sigR K σ (ι ε) = ι ε := sigR_algebraMap' K σ
  have hg1 : ∀ ε, gram2R K σ J xb (wε ε) = gram2R K σ J xb w := by
    intro ε
    simp only [wε, gram2R, hR, hform_add_smul_right, hform_add_smul_left, GlobalTheory.HermLineZeros.hform_expand]
    rw [hsig]
    ring
  have hpoly : ∀ ε, lam (hR K σ J (wε ε) (wε ε)) =
      ε ^ 2 + lam (hR K σ J w xb + hR K σ J xb w) * ε + lam (hR K σ J w w) := by
    intro ε
    have e1 : hR K σ J (wε ε) (wε ε) = hR K σ J w w + ι ε * (hR K σ J w xb + hR K σ J xb w)
        + ι ε * (ι ε * hR K σ J xb xb) := by
      simp only [wε, hR, GlobalTheory.HermLineZeros.hform_expand]
      rw [hsig]
      ring
    rw [e1, map_add (f := _), map_add (f := _), hlamsmul, hlamsmul, hlamsmul, hlamA]
    ring

  set P : Polynomial K := Polynomial.X ^ 2 + Polynomial.C (lam (hR K σ J w xb + hR K σ J xb w)) * Polynomial.X
    + Polynomial.C (lam (hR K σ J w w)) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 2) h0
    simp [hP, Polynomial.coeff_X, Polynomial.coeff_C] at this
  have hZ : {ε : K | P.IsRoot ε}.Countable := (Polynomial.finite_setOf_isRoot hP0).countable
  have hD : Dense {ε : K | P.IsRoot ε}ᶜ := hZ.dense_compl K
  have hcι : Continuous ι :=
    ((continuous_id : Continuous fun k : K => k).smul
      (continuous_const : Continuous fun _ : K => (1 : K ⊗[F] E))).congr
      (fun k => (Algebra.algebraMap_eq_smul_one k).symm)
  have hcw : Continuous wε := continuous_const.add (hcι.smul continuous_const)
  have hV : IsOpen (wε ⁻¹' U2) := hU2.preimage hcw
  have h0 : (0 : K) ∈ wε ⁻¹' U2 := by
    change IsUnitNorm K σ (-(gram2R K σ J (w + ι 0 • xb) yb))
    rw [map_zero, zero_smul, add_zero]
    exact h2
  obtain ⟨ε, hεD, hεV⟩ := hD.exists_mem_open hV ⟨0, h0⟩

  set U3 := {v : Fin M → K ⊗[F] E | lam (hR K σ J v v) ≠ 0} with hU3def
  have hU3 : IsOpen U3 := isOpen_ne.preimage
    ((IsModuleTopology.continuous_of_linearMap lam).comp (continuous_hR K σ J continuous_id continuous_id))
  have hO : IsOpen (U1 ∩ U2 ∩ U3) := (hU1.inter hU2).inter hU3
  have hmem : wε ε ∈ U1 ∩ U2 ∩ U3 := by
    refine ⟨⟨?_, hεV⟩, ?_⟩
    · change IsUnitNorm K σ (-(gram2R K σ J xb (wε ε)))
      rw [hg1]
      exact h1
    · change lam (hR K σ J (wε ε) (wε ε)) ≠ 0
      rw [hpoly]
      intro h0
      apply hεD
      change P.IsRoot ε
      simp only [hP, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [← h0]
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := (dense_ratVec K hd M).exists_mem_open hO ⟨_, hmem⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · intro h0
    apply hz.2
    change lam (hR K σ J (fun i => inclR K (z i)) (fun i => inclR K (z i))) = 0
    rw [hR_incl, h0, map_zero, map_zero]
  · rw [← hermitianGramDetTwoVectorsTensor_incl]
    exact hz.1.1
  · rw [← hermitianGramDetTwoVectorsTensor_incl]
    exact hz.1.2

end GlobalTheory.PlaneNormApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetRationalApproximationStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitNorm_gramDet_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → ∀ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) → IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J z y))) := by
  first | exact @GlobalTheory.PlaneNormApprox.approx | exact GlobalTheory.PlaneNormApprox.approx | (intros; apply GlobalTheory.PlaneNormApprox.approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanes
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_rational_middle_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  intro F E _ _ _ _ _ σ hσ K _ _ _ hd M J hM hJ hu x y hx hy
  obtain ⟨w, h1, h2⟩ := GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian F E σ hσ K M J hM hJ hu x y hx hy
  obtain ⟨z, hz, n1, n2⟩ := GlobalTheory.T.unitNorm_gramDet_rational_approximation F E σ hσ K hd M J hJ x y hx w h1 h2
  exact ⟨z, hz, GlobalTheory.T.unitNorm_gramDet_plane_reduction F E σ hσ K M J hJ x z hx n1, GlobalTheory.T.unitNorm_gramDet_plane_reduction F E σ hσ K M J hJ z y hz n2⟩

end GlobalTheory.PlaneNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  first | exact @GlobalTheory.PlaneNorm.exists_rational_middle_vector | exact GlobalTheory.PlaneNorm.exists_rational_middle_vector | (intros; apply GlobalTheory.PlaneNorm.exists_rational_middle_vector <;> assumption)
end

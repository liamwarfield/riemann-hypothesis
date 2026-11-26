module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def intMuCD_pM (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) → (Fin n → Fin n → ℂ) := fun kz => polarM kz

def intMuCD_P (ε : Fin n → Bool) : Measure (KG ε × (PCoord ε → ℂ)) :=
  (dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))

theorem intMuCD_muPolarMat_eq (ε : Fin n → Bool) :
    muPolarMat ε = Measure.map (intMuCD_pM ε) (intMuCD_P ε) := rfl

theorem lintegral_comap_embedding {α : Type*} [MeasurableSpace α] {e : α → (Fin n → Fin n → ℂ)}
    (he : MeasurableEmbedding e) (μ : Measure (Fin n → Fin n → ℂ)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range e)
    (F : (Fin n → Fin n → ℂ) → ENNReal) :
    ∫⁻ g, F (e g) ∂(Measure.comap e μ) = ∫⁻ x, F x ∂μ := by
  have h1 := he.lintegral_map (μ := Measure.comap e μ) F
  rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem hμ] at h1
  exact h1.symm

theorem intMuCD_measurable_pM (ε : Fin n → Bool) : Measurable (intMuCD_pM ε) := by
  exact Continuous.measurable (f := intMuCD_pM ε) (polarM_continuous ε)

theorem intMuCD_polar_int (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x ∂(muPolarMat ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hpm := intMuCD_measurable_pM ε
  have hJ : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [intMuCD_muPolarMat_eq, lintegral_map hF hpm, intMuCD_P]
  refine (lintegral_prod (F ∘ intMuCD_pM ε) (hF.comp hpm).aemeasurable).trans ?_
  refine lintegral_congr (fun k => ?_)
  refine (lintegral_withDensity_eq_lintegral_mul _ hJ (hF.comp (hpm.comp measurable_prodMk_left))).trans ?_
  refine lintegral_congr (fun z => ?_)
  exact mul_comm _ _

theorem intMuCD_ae_range (ε : Fin n → Bool) (S : Set (Fin n → Fin n → ℂ)) (hS : MeasurableSet S)
    (h : ∀ kz : KG ε × (PCoord ε → ℂ), intMuCD_pM ε kz ∈ S) : ∀ᵐ x ∂(muPolarMat ε), x ∈ S := by
  rw [intMuCD_muPolarMat_eq]
  exact (ae_map_iff (p := fun x => x ∈ S) (intMuCD_measurable_pM ε).aemeasurable hS).2 (ae_of_all _ h)

def intMuCD_eM (ε : Fin n → Bool) : UJ ε → (Fin n → Fin n → ℂ) := fun g => toM g

def intMuCD_eU (ε : Fin n → Bool) : Formalism.REAL.UJ ε → (Fin n → Fin n → ℂ) := fun g => Formalism.MainNotions.S.umat g

private theorem exists_UJ_toM_eq_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ u : UJ ε, toM u = g := by
  change g ∈ Set.range (fun u : UJ ε => toM u)
  rw [range_toM]
  exact hg

theorem lintegral_muPolar (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (toM g) ∂(muPolar ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eM ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eM ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (toM g) ∂(muPolar ε)
        = ∫⁻ g, F (intMuCD_eM ε g) ∂(Measure.comap (intMuCD_eM ε) (muPolarMat ε)) := rfl
    _ = ∫⁻ x, F x ∂(muPolarMat ε) := lintegral_comap_embedding hemb _ hae F
    _ = _ := intMuCD_polar_int ε F hF

theorem lintegral_muCD (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε) =
      ENNReal.ofReal (cPQ ε) * ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eU ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eU ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε)
        = ENNReal.ofReal (cPQ ε) *
            ∫⁻ g, F (intMuCD_eU ε g) ∂(Measure.comap (intMuCD_eU ε) (muPolarMat ε)) := by
          rw [muCD, lintegral_smul_measure]
          rfl
    _ = _ := by rw [lintegral_comap_embedding hemb _ hae F, intMuCD_polar_int ε F hF]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem toMK_inv_eq_conjTranspose {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ = star (toMK k) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (show toMK k ∈ Kset ε from k.2).1)
  rw [h, Matrix.star_eq_conjTranspose]

theorem conj_pmat_eq_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    toMK k⁻¹ * pmat z * toMK k = pmat (adK k⁻¹ z) := by
  rw [pmat_adK, toMK_inv_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem rhoP_real_smul {ε : Fin n → Bool} (t : ℝ) (z : PCoord ε → ℂ) : rhoP ((t : ℂ) • z) = |t| * rhoP z := by
  have hS : ∑ ab, ‖((t : ℂ) • z) ab‖ ^ 2 = t ^ 2 * ∑ ab, ‖z ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold rhoP
  rw [hs_pmat, hs_pmat, hS, show 2 * (t ^ 2 * ∑ ab, ‖z ab‖ ^ 2) = t ^ 2 * (2 * ∑ ab, ‖z ab‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiMExpPmat
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FBridge
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fbr_det_exp_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (NormedSpace.exp (pmat z)).det = 1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : pmat z = U * diagonal (fun i => (pev z i : ℂ)) * Uᴴ := by
    have := (pmat_isHermitian z).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h2
  have hu : IsUnit U := ⟨⟨U, Uᴴ, h2, h1⟩, rfl⟩
  rw [hsp, ← hinv, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal, det_diagonal]
  have he : ∀ i, (NormedSpace.exp (fun i => (pev z i : ℂ))) i = Complex.exp (pev z i : ℂ) := by
    intro i
    rw [Pi.exp_def, Complex.exp_eq_exp_ℂ]
  simp only [he]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum, sum_pev, Complex.ofReal_zero, Complex.exp_zero]

theorem fbr_det_conj {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * A * toMK k).det = A.det := by
  rw [toMK_inv, Matrix.det_mul, Matrix.det_mul, mul_comm ((toMK k)ᴴ.det) A.det, mul_assoc, ← Matrix.det_mul,
    (toMK_facts k).1, Matrix.det_one, mul_one]

theorem fbr_phi {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PhiM μ (toMK k⁻¹ * NormedSpace.exp (pmat z) * toMK k) =
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) := by
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ (pmat_inP z)
  rw [inv_inv] at hP hE
  rw [← hE]
  set Y := toMK k⁻¹ * pmat z * toMK k with hY
  set E := NormedSpace.exp Y with hEdef
  have hpd : E.PosDef := exp_noncompactPart_posDef hP
  have hdet : lead n E = 1 := by
    have h1 : E.det = 1 := by rw [hE, fbr_det_conj, fbr_det_exp_pmat]
    unfold lead
    rw [dite_eq_left le_rfl]
    convert h1 using 2
    ext a b
    rfl
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) E).re := fun i => (lead_posDef hpd _ i.isLt).1
  have h : ∀ i : Fin n, lead ((i : ℕ) + 1) E = ((lead ((i : ℕ) + 1) E).re : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM μ E = ((∏ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_zpow, ← h i]
  rw [hphi]
  congr 1
  have hz : ∀ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) =
      Real.exp (Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ)) := by
    intro i
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos i)]
  rw [prod_congr rfl fun i _ => hz i, ← Real.exp_sum]
  congr 1
  set g : ℕ → ℝ := fun i => -(sCoef lam i * Real.log (lead (i + 1) E).re) with hg
  have hterm : ∀ i : Fin n, Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ) = g i := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have hm : muNext μ i = μ ⟨(i : ℕ) + 1, hi⟩ := by simp [muNext, hi]
      have hs : sCoef lam i = lam i - lam ⟨(i : ℕ) + 1, hi⟩ + 1 := by simp [sCoef, hi]
      rw [hm, hg]
      simp only
      rw [hs]
      push_cast
      rw [hμ i, hμ ⟨(i : ℕ) + 1, hi⟩]
      simp only [rho]
      push_cast
      ring
    · have hs : sCoef lam i = 0 := by simp [sCoef, hi]
      have hn : (i : ℕ) + 1 = n := by omega
      rw [hg]
      simp only
      rw [hs, hn, hdet]
      simp
  rw [sum_congr rfl fun i _ => hterm i, Fin.sum_univ_eq_sum_range g n]
  have hsub : ∑ i ∈ range n, g i = ∑ i ∈ range (n - 1), g i := by
    symm
    refine sum_subset (range_subset_range.mpr (Nat.sub_le n 1)) ?_
    intro i hi hi'
    simp only [mem_range] at hi hi'
    have hs : sCoef lam i = 0 := by simp only [sCoef]; rw [dite_eq_right (by omega)]
    simp [hg, hs]
  rw [hsub, Ph, ← sum_neg_distrib]
  rfl

theorem psM_exp_pmat {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) {Λ : Fin n → ℝ}
    (T : KType ε Λ) (z : PCoord ε → ℂ) : psM T μ (NormedSpace.exp (pmat z)) = fF ε lam T (pmat z) := by
  simp only [psM, fF]
  congr 1
  refine congrArg (fun f : KG ε → T.V →L[ℂ] T.V => ∫ k, f k ∂(muK ε)) (funext fun k => ?_)
  rw [fbr_phi hμ k z]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem psiM_polar {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PsiM T μ (toMK k * NormedSpace.exp (pmat z)) = T.op k * psM T μ (NormedSpace.exp (pmat z)) := by
  have hX := pmat_inP z
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp X' := ⟨k, pmat z, hX, rfl⟩
  unfold PsiM
  rw [dite_eq_left hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := polar_unique hX hP hEq
  rw [← h2, ← h1]

theorem psiM_exp_pmat {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (z : PCoord ε → ℂ) : PsiM T μ (NormedSpace.exp (pmat z)) = psM T μ (NormedSpace.exp (pmat z)) := by
  have h := psiM_polar T μ (1 : KG ε) z
  have e : toMK (1 : KG ε) = 1 := rfl
  have o : T.op (1 : KG ε) = 1 := by simp [KType.op, map_one]
  rwa [e, Matrix.one_mul, o, one_mul] at h

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarAct
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def plog (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.isHermitian_conjTranspose_mul_self h).cfc Real.log

def actR {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => plog (NormedSpace.exp (pmat z) * g) ab.1.1 ab.1.2

theorem pact_cfc_log_exp (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (h : (NormedSpace.exp X).IsHermitian) : h.cfc Real.log = X := by
  have hSA : IsSelfAdjoint X := Matrix.isHermitian_iff_isSelfAdjoint.mp hX
  obtain ⟨W, hWdef⟩ : ∃ W, W = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hW : star W * W = 1 := by
    rw [hWdef]
    exact Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  have hWi : W⁻¹ = star W := Matrix.inv_eq_left_inv hW
  have hWu : IsUnit W := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hW)
  have hexp : NormedSpace.exp X = hX.cfc Real.exp := by
    have hd : NormedSpace.exp (RCLike.ofReal ∘ hX.eigenvalues : Fin n → ℂ) =
        (RCLike.ofReal ∘ Real.exp ∘ hX.eigenvalues : Fin n → ℂ) := by
      funext i
      simp [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ]
    conv_lhs => rw [hX.spectral_theorem]
    rw [Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star]
    rw [← hWdef, ← hWi, Matrix.exp_conj _ _ hWu, Matrix.exp_diagonal, hd]
  rw [← Matrix.IsHermitian.cfc_eq, hexp, ← Matrix.IsHermitian.cfc_eq,
    ← cfc_comp Real.log Real.exp X hSA
      (Real.continuousOn_log.mono (by rintro _ ⟨x, -, rfl⟩; exact (Real.exp_pos x).ne'))
      Real.continuous_exp.continuousOn]
  have hle : Real.log ∘ Real.exp = id := funext Real.log_exp
  rw [hle]
  exact cfc_id ℝ X hSA

theorem pact_cfc_congr {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) (f : ℝ → ℝ) : hA.cfc f = hB.cfc f := by
  subst h
  rfl

theorem plog_unitary_mul_exp (k X : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) (hX : X.IsHermitian) :
    plog (k * NormedSpace.exp X) = X := by
  have hE : (NormedSpace.exp X)ᴴ = NormedSpace.exp X := by
    rw [← Matrix.exp_conjTranspose, hX.eq]
  have h2 : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
    rw [Matrix.exp_add_of_commute X X (Commute.refl X), Matrix.conjTranspose_mul, hE,
      Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  have hB : (NormedSpace.exp (X + X)).IsHermitian := by
    rw [← h2]
    exact Matrix.isHermitian_conjTranspose_mul_self _
  unfold plog
  rw [pact_cfc_congr (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hB h2 Real.log,
    pact_cfc_log_exp (X + X) (hX.add hX) hB, ← two_smul ℂ X, smul_smul]
  norm_num

private theorem toMK_unit_lemma {ε : Fin n → Bool} (k : KG ε) : (toMK k)ᴴ * toMK k = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff'.mp hk.1

theorem plog_polarM {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : plog (polarM (k, z)) = pmat z :=
  plog_unitary_mul_exp (toMK k) (pmat z) (toMK_unit_lemma k) (pmat_isHermitian z)

theorem pact_pmat_coords {ε : Fin n → Bool} (w : PCoord ε → ℂ) :
    (fun ab : PCoord ε => pmat w ab.1.1 ab.1.2) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, h⟩ := ab
  simp only [pmat]
  rw [dite_eq_left h]

private theorem actR_eq_lemma {ε : Fin n → Bool} {g U : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ}
    (hU : Uᴴ * U = 1) (h : NormedSpace.exp (pmat z) * g = U * NormedSpace.exp (pmat w)) :
    actR g z = w := by
  unfold actR
  rw [h, plog_unitary_mul_exp U (pmat w) hU (pmat_isHermitian w)]
  exact pact_pmat_coords w

theorem actR_of_eq_polarM {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ} {k : KG ε}
    (h : NormedSpace.exp (pmat z) * g = polarM (k, w)) : actR g z = w := by
  unfold actR
  rw [h, plog_polarM]
  exact pact_pmat_coords w

theorem pact_inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem actR_spec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    ∃ k : KG ε, NormedSpace.exp (pmat z) * g = polarM (k, actR g z) := by
  obtain ⟨⟨k, w⟩, hkw⟩ := polarM_surj _ (pact_inUJ_mul (exp_pmat_inUJ z) hg)
  refine ⟨k, ?_⟩
  rw [actR_of_eq_polarM hkw.symm]
  exact hkw.symm

theorem actR_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : actR (g * h) z = actR h (actR g z) := by
  obtain ⟨k1, h1⟩ := actR_spec hg z
  obtain ⟨k2, h2⟩ := actR_spec hh (actR g z)
  simp only [polarM] at h1 h2
  apply actR_eq_lemma (U := toMK k1 * toMK k2)
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (toMK k1)ᴴ, toMK_unit_lemma k1,
      Matrix.one_mul, toMK_unit_lemma k2]
  · rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc (toMK k1) (NormedSpace.exp (pmat (actR g z))) h, h2,
      Matrix.mul_assoc (toMK k1) (toMK k2)]

theorem actR_one {ε : Fin n → Bool} (z : PCoord ε → ℂ) : actR (1 : Matrix (Fin n) (Fin n) ℂ) z = z := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [Matrix.mul_one, Matrix.one_mul]

theorem pact_pmat_zero {ε : Fin n → Bool} : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b
  simp [pmat]

private theorem toMK_unit_lemma_2 {ε : Fin n → Bool} (k : KG ε) : toMK k * (toMK k)ᴴ = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff.mp hk.1

theorem actR_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : actR (toMK k) z = adK k⁻¹ z := by
  have hU := toMK_unit_lemma k
  have hU' : toMK k * (toMK k)ᴴ = 1 := toMK_unit_lemma_2 k
  have hinv : toMK k⁻¹ * toMK k = 1 := by
    simp [S7.toMK, S7.toM]
  have hi1 : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  have hi2 : (toMK k)⁻¹ = toMK k⁻¹ := Matrix.inv_eq_left_inv hinv
  have hunit : IsUnit (toMK k) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hU)
  apply actR_eq_lemma hU
  have hi3 : (toMK k)⁻¹ᴴ = toMK k := by rw [hi1, Matrix.conjTranspose_conjTranspose]
  rw [pmat_adK, ← hi2, hi3, Matrix.exp_conj' _ _ hunit, hi1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU',
    Matrix.one_mul]

theorem actR_exp_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ) = y := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [pact_pmat_zero, NormedSpace.exp_zero, Matrix.one_mul]

end ReciprocityTheory.ChartRestriction.DS
end
end

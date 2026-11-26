module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalForm
open Matrix

namespace GlobalTheory.SimNormal

theorem diagonal_comm_of_comm {n : ℕ} {d f : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (h : diagonal d * g = g * diagonal d) (hf : ∀ i j, d i = d j → f i = f j) :
    diagonal f * g = g * diagonal f := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [diagonal_mul, mul_diagonal] at e ⊢
  by_cases hg : g i j = 0
  · simp [hg]
  · have : d i = d j := mul_right_cancel₀ hg (e.trans (mul_comm _ _))
    rw [hf i j this, mul_comm]

theorem simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  intro n J P hJ hJd hP hpos
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.ThK.SqIntMaxCpt.exists_congr_one hP hpos
  set M := Q₀.1ᴴ * J * Q₀.1 with hMdef
  have hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul _ hJ
  set U : Matrix (Fin n) (Fin n) ℂ := hM.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hM.eigenvectorUnitary.2
  set d : Fin n → ℝ := hM.eigenvalues with hd
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => (d i : ℂ) with hD
  have h3 : Uᴴ * M * U = D := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have hdne : ∀ i, d i ≠ 0 := by
    have hUd : Uᴴ.det * U.det = 1 := by rw [← det_mul, h1, det_one]
    have hQd : Q₀.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
    have hDd : D.det ≠ 0 := by
      rw [← h3, hMdef, det_mul, det_mul, det_mul, det_mul]
      have hU1 : Uᴴ.det ≠ 0 := left_ne_zero_of_mul_eq_one hUd
      have hU2 : U.det ≠ 0 := right_ne_zero_of_mul_eq_one hUd
      have hQ2 : Q₀.1ᴴ.det ≠ 0 := by rw [det_conjTranspose]; simpa using hQd
      simp only [ne_eq, mul_eq_zero, not_or]; tauto
    intro i hi
    apply hDd
    rw [hD, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hMU : U * D * Uᴴ = M := by
    rw [← h3]; simp only [← Matrix.mul_assoc, h1', Matrix.one_mul]; rw [Matrix.mul_assoc, h1', Matrix.mul_one]
  set s : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with hs
  have hsq : ∀ i, 0 < Real.sqrt |d i| := fun i => Real.sqrt_pos.2 (abs_pos.2 (hdne i))
  let S : GL (Fin n) ℂ := ⟨diagonal fun i => (s i : ℂ), diagonal fun i => (Real.sqrt |d i| : ℂ), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact inv_mul_cancel₀ (by exact_mod_cast (hsq i).ne'), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast (hsq i).ne')⟩
  let Ug : GL (Fin n) ℂ := ⟨U, Uᴴ, h1', h1⟩
  refine ⟨fun i => decide (0 < d i), Q₀ * Ug * S, ?_, fun g hgP hgJ => ?_⟩
  · have hSh : (S.1)ᴴ = S.1 := by
      show (diagonal fun i => (s i : ℂ))ᴴ = _
      rw [diagonal_conjTranspose]; congr 1; funext i; simp
    have : (Q₀ * Ug * S).1ᴴ * J * (Q₀ * Ug * S).1 = S.1 * (Uᴴ * M * U) * S.1 := by
      simp only [Units.val_mul, conjTranspose_mul, hSh, Matrix.mul_assoc, hMdef]; rfl
    rw [this, h3]
    show diagonal _ * diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i
    have hsi : s i * s i = |d i|⁻¹ := by
      simp only [hs]; rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]
    have : (s i : ℂ) * d i * s i = ((d i * (s i * s i) : ℝ) : ℂ) := by push_cast; ring
    rw [this, hsi]
    rcases lt_or_gt_of_ne (hdne i) with h | h
    · simp [h, not_lt.2 h.le, abs_of_neg h, (hdne i)]
    · simp [h, abs_of_pos h, (hdne i)]
  · have hi : (Q₀⁻¹).1ᴴ * Q₀.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have hPi : (Q₀⁻¹).1ᴴ * (Q₀⁻¹).1 = P := by
      have := congrArg (fun A => (Q₀⁻¹).1ᴴ * A * (Q₀⁻¹).1) hQ₀
      simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this.symm
    have hJi : (Q₀⁻¹).1ᴴ * M * (Q₀⁻¹).1 = J := by
      rw [hMdef]
      simp only [← Matrix.mul_assoc, hi, Matrix.one_mul, Units.mul_inv_cancel_right]
    set g' := Uᴴ * (Q₀⁻¹).1 * g * Q₀.1 * U with hg'
    have hg'1 : g'ᴴ * g' = 1 := by
      calc g'ᴴ * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * P * Q₀.1) * U := by
            rw [h1', Matrix.mul_one, hPi, hgP]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ₀, Matrix.mul_one, h1]
    have hg'D : g'ᴴ * D * g' = D := by
      calc g'ᴴ * D * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * D * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * J * Q₀.1) * U := by
            rw [hMU, hJi, hgJ]; simp only [Matrix.mul_assoc]
        _ = D := by rw [← hMdef, h3]
    have hg'2 : g' * g'ᴴ = 1 := mul_eq_one_comm.1 hg'1
    have hcomm : D * g' = g' * D := by
      calc D * g' = g' * g'ᴴ * D * g' := by rw [hg'2, Matrix.one_mul]
        _ = g' * (g'ᴴ * D * g') := by simp only [Matrix.mul_assoc]
        _ = g' * D := by rw [hg'D]
    have hQinv : ((Q₀ * Ug * S)⁻¹).1 * g * (Q₀ * Ug * S).1 = (S⁻¹).1 * g' * S.1 := by
      simp only [_root_.mul_inv_rev, Units.val_mul, hg', Matrix.mul_assoc]; rfl
    have hSc : (S⁻¹).1 * g' = g' * (S⁻¹).1 :=
      diagonal_comm_of_comm (f := fun i => (Real.sqrt |d i| : ℂ)) hcomm fun i j h => by
        have : d i = d j := by exact_mod_cast h
        simp [this]
    have hfin : (S⁻¹).1 * g' * S.1 = g' := by
      rw [hSc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hQinv, hfin]
    exact hg'1

end GlobalTheory.SimNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalFormStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_posDef_simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  first | exact @GlobalTheory.SimNormal.simultaneous_normal_form | exact GlobalTheory.SimNormal.simultaneous_normal_form | (intros; apply GlobalTheory.SimNormal.simultaneous_normal_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPosDefHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPosDefHermitian
open Matrix

noncomputable section
namespace GlobalTheory.CompactAvg
open MeasureTheory

theorem exists_invariant_posDef_hermitian {n : ℕ} (H : Subgroup (GL (Fin n) ℂ))
    (hH : IsCompact (H : Set (GL (Fin n) ℂ))) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let m : H → Matrix (Fin n) (Fin n) ℂ := fun g => (((g⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hm : Continuous m := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)

  let f : H → (Fin n → Fin n → ℂ) := fun g => ((m g)ᴴ * m g : Matrix (Fin n) (Fin n) ℂ)
  have hf : Continuous f := hm.matrix_conjTranspose.matrix_mul hm
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.of (∫ g, f g ∂μ)

  have hinv : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ * h = P₀ := by
    intro h hh
    let M : Matrix (Fin n) (Fin n) ℂ := h
    let Lₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
      { toFun := fun A => (Mᴴ * Matrix.of A * M : Matrix (Fin n) (Fin n) ℂ)
        map_add' := fun A B => by
          show Mᴴ * Matrix.of (A + B) * M = Mᴴ * Matrix.of A * M + Mᴴ * Matrix.of B * M
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c A => by
          show Mᴴ * Matrix.of (c • A) * M = c • (Mᴴ * Matrix.of A * M)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.mul_smul, Matrix.smul_mul] }
    let L := LinearMap.toContinuousLinearMap Lₗ
    have e1 : L (∫ g, f g ∂μ) = ∫ g, L (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm L hfi).symm
    have e2 : ∀ g : H, L (f g) = f ((⟨h, hh⟩ : H)⁻¹ * g) := by
      intro g
      have hq : m ((⟨h, hh⟩ : H)⁻¹ * g) = m g * M := by
        show (((((⟨h, hh⟩ : H)⁻¹ * g)⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = m g * M
        rw [_root_.mul_inv_rev, inv_inv]
        rfl
      show Mᴴ * ((m g)ᴴ * m g) * M = (m _)ᴴ * m _
      rw [hq, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e3 : ∫ g, f ((⟨h, hh⟩ : H)⁻¹ * g) ∂μ = ∫ g, f g ∂μ := integral_mul_left_eq_self f _
    show L (∫ g, f g ∂μ) = ∫ g, f g ∂μ
    rw [e1]; simp_rw [e2]; exact e3

  have hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P₀ *ᵥ x).re := by
    intro x hx
    let ℓₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun A => star x ⬝ᵥ Matrix.of A *ᵥ x
        map_add' := fun A B => by
          show star x ⬝ᵥ Matrix.of (A + B) *ᵥ x = star x ⬝ᵥ Matrix.of A *ᵥ x + star x ⬝ᵥ Matrix.of B *ᵥ x
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c A => by
          show star x ⬝ᵥ Matrix.of (c • A) *ᵥ x = c • (star x ⬝ᵥ Matrix.of A *ᵥ x)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.smul_mulVec, dotProduct_smul] }
    let ℓ := LinearMap.toContinuousLinearMap ℓₗ
    have e1 : ℓ (∫ g, f g ∂μ) = ∫ g, ℓ (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm ℓ hfi).symm
    have hℓi : Integrable (fun g => ℓ (f g)) μ := ℓ.integrable_comp hfi
    have e2 : (star x ⬝ᵥ P₀ *ᵥ x).re = ∫ g, RCLike.re (ℓ (f g)) ∂μ := by
      rw [integral_re hℓi, ← e1]; rfl
    have e3 : ∀ g : H, RCLike.re (ℓ (f g)) = ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      show (star x ⬝ᵥ ((m g)ᴴ * m g) *ᵥ x).re = _
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.star_def, Complex.mul_re]
    have hnz : ∀ g : H, m g *ᵥ x ≠ 0 := by
      intro g h0
      have : (((g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * m g) *ᵥ x = x := by
        simp [m]
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero] at this
      exact hx this.symm
    have e4 : ∀ g : H, 0 < ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (hnz g)
      have hi' : 0 < ‖(m g *ᵥ x) i‖ ^ 2 := by
        have : 0 < ‖(m g *ᵥ x) i‖ := norm_pos_iff.2 hi
        positivity
      exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i => ‖(m g *ᵥ x) i‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i))
    rw [e2]
    simp_rw [e3]
    have hgi : Integrable (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) μ :=
      (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_pos_iff_support_of_nonneg (fun g => (e4 g).le) hgi]
    have hs : Function.support (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) = Set.univ :=
      Set.eq_univ_of_forall fun g => (e4 g).ne'
    rw [hs]
    exact isOpen_univ.measure_pos μ Set.univ_nonempty
  refine ⟨P₀ + P₀ᴴ, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian, add_comm]
  · intro x hx
    have hc : star x ⬝ᵥ P₀ᴴ *ᵥ x = star (star x ⬝ᵥ P₀ *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_dotProduct]
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hc]
    have := hpos x hx
    simp only [Complex.star_def, Complex.conj_re]
    linarith
  · intro g hg
    have h1 := hinv g hg
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ᴴ * g = P₀ᴴ := by
      conv_rhs => rw [← h1]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2]

end GlobalTheory.CompactAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPosDefHermitianStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact : ∀ {n : ℕ} (H : Subgroup (GL (Fin n) ℂ)), IsCompact (H : Set (GL (Fin n) ℂ)) →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  first | exact @GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | exact GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | (intros; apply GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMajorantFrameCompactSubgroupLe
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix
noncomputable section

namespace GlobalTheory.CptMajorant

theorem exists_frame_le_majCpt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ K hKinf hK
  have key : ∀ w : InfinitePlace F, ∃ c : GL (Fin n) (w.Completion ⊗[F] E),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) c.1 * JR w.Completion J * c.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ ∀ k ∈ K, projArch σ J w k ∈ stabArch σ J w c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    let φ : GAd σ J →* GL (Fin n) ℂ :=
      (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((matHom _ σ J).comp (projArch σ J w))
    have hφv : ∀ x, (φ x).1 = (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun x => rfl
    have hcv : Continuous fun x : GAd σ J => (φ x).1 := by
      simp only [hφv]
      exact (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
        (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
    have hφ : Continuous φ := Units.continuous_iff.2 ⟨hcv, by
      simp only [← map_inv]; exact hcv.comp continuous_inv⟩
    obtain ⟨P, hPh, hPpos, hPinv⟩ := GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact (K.map φ) (by rw [Subgroup.coe_map]; exact hK.image hφ)
    have hG : (J.map τ.1).IsHermitian := by
      ext i j
      exact (h.2.2.2 τ.1 _).symm.trans (congrArg _ (hJ.1 i j))
    have hd : (J.map τ.1).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hJ.2
    obtain ⟨ε, Q, hQ, hQu⟩ := GlobalTheory.T.hermitian_posDef_simultaneous_normal_form hG hd hPh hPpos
    have h1 : (Formalism.UG.bc e.symm.toRingHom Q).1.map (infEmb τ) = Q.1 := Matrix.ext fun i j => e.apply_symm_apply _
    have h1' : ((Formalism.UG.bc e.symm.toRingHom Q)⁻¹).1.map (infEmb τ) = (Q⁻¹).1 :=
      Matrix.ext fun i j => e.apply_symm_apply _
    have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
    refine ⟨Formalism.UG.bc e.symm.toRingHom Q, ⟨ε, Matrix.map_injective e.injective ?_⟩, fun k hk => ?_⟩
    · change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [mem_stabArch]
      change Formalism.UG.cT _ _ * 1 * _ = 1
      refine Matrix.map_injective e.injective ?_
      change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      have hu := hQu (φ k).1 (hPinv _ ⟨k, hk, rfl⟩) (by
        have : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w k)).1 * JR w.Completion J *
          (matHom _ σ J (projArch σ J w k)).1 = JR w.Completion J := (projArch σ J w k).2
        have := congrArg (fun A => A.map (infEmb τ)) this
        simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2, hφv] using this)
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1', hφv,
        Matrix.map_one _ (map_zero _) (map_one _)] using hu
  choose c hc hKc using key
  exact ⟨c, hc, fun k hk => mem_majCpt.2 ⟨hKinf hk, fun w => hKc w k hk⟩⟩

end GlobalTheory.CptMajorant
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMajorantFrameCompactSubgroupLeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_majorantFrame_compact_subgroup_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  first | exact @GlobalTheory.CptMajorant.exists_frame_le_majCpt | exact GlobalTheory.CptMajorant.exists_frame_le_majCpt | (intros; apply GlobalTheory.CptMajorant.exists_frame_le_majCpt <;> assumption)
end

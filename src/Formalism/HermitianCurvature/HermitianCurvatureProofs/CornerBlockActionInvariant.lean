module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearFormRadicalRankOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

theorem liftVec_eB (u : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    liftVec k p ρ u (U.eB k p ρ x) = Sum.elim (Sum.elim (fun _ => 0) u) (fun _ => 0) x := by
  rcases x with (a | b) | c
  · have ha := a.isLt
    simp only [liftVec, Sum.elim_inl]
    rw [dite_eq_right]
    simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
    omega
  · have hb := b.isLt
    simp only [liftVec, Sum.elim_inl, Sum.elim_inr]
    rw [dite_eq_left]
    · congr 1
      ext
      simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
      omega
    · simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
      omega
  · have hc := c.isLt
    simp only [liftVec, Sum.elim_inr]
    rw [dite_eq_right]
    simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
    omega

theorem inWb_liftVec {z : Fin (2 * ρ + k + 1) → ℂ} (hz : inWb k ρ z) : inWb k (p + ρ) (liftVec k p ρ z) := by
  intro i hi
  simp only [liftVec]
  split_ifs with h
  · exact hz _ (by show i.val - p < ρ ∨ ρ + k < i.val - p; omega)
  · rfl

theorem eI_X (a : Fin p) : eI k (p + ρ) (Fin.castAdd ρ a) = U.eB k p ρ (Sum.inl (Sum.inl a)) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

theorem eI_V (a : Fin ρ) : eI k (p + ρ) (Fin.natAdd p a) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ a))) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

theorem eI_V' (a : ℕ) (ha : a < ρ) (h : p + a < p + ρ) :
    eI k (p + ρ) ⟨p + a, h⟩ = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨a, ha⟩))) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

theorem eI_X' (a : ℕ) (ha : a < p) (h : a < p + ρ) :
    eI k (p + ρ) ⟨a, h⟩ = U.eB k p ρ (Sum.inl (Sum.inl ⟨a, ha⟩)) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

private theorem embG_eB_inl_inl_apply_eq_ite (y : B.Mat k ρ) (a : Fin p) (x : U.Ix k p ρ) :
    U.embG k p ρ y (U.eB k p ρ (Sum.inl (Sum.inl a))) (U.eB k p ρ x) = if x = Sum.inl (Sum.inl a) then 1 else 0 := by
  rcases x with (a' | b') | c' <;> simp [U.embG, Ux6.block3_apply, Matrix.one_apply] <;> (try split_ifs) <;> simp_all

private theorem embG_mulVec_liftVec_eB_apply (y : B.Mat k ρ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    (U.embG k p ρ y *ᵥ liftVec k p ρ z) (U.eB k p ρ x) =
      Sum.elim (Sum.elim (fun _ => 0) (y *ᵥ z)) (fun _ => 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (U.eB k p ρ)]
  simp only [U.embG, Ux6.block3_apply, liftVec_eB]
  rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem ell_embG (z : Fin (2 * ρ + k + 1) → ℂ) (y : B.Mat k ρ) :
    ell k (p + ρ) (liftVec k p ρ z) (U.embG k p ρ y) = ell k ρ z y := by
  simp only [Formalism.QuantumDeterminants.ell]
  rw [Fin.sum_univ_add, Finset.sum_eq_zero, zero_add]
  · apply Finset.sum_congr rfl
    intro b _
    have hb := b.isLt
    have hV : eI k (p + ρ) (Fin.natAdd p b) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ b))) := eI_V b
    by_cases h : b.val + 1 < ρ
    · have h' : (Fin.natAdd p b).val + 1 < p + ρ := by simp; omega
      have hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩))) := eI_V' (b.val + 1) h (by simp; omega)
      rw [dite_eq_left h', dite_eq_left h, hV, hV']
      simp [U.embG, Ux6.block3_apply]
    · have h' : ¬ (Fin.natAdd p b).val + 1 < p + ρ := by simp; omega
      rw [dite_eq_right h', dite_eq_right h, hV, embG_mulVec_liftVec_eB_apply]
      rfl
  · intro a _
    have ha := a.isLt
    rw [eI_X a]
    split_ifs with h
    · obtain ⟨x, hx⟩ := (U.eB k p ρ).surjective (eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h⟩)
      rw [← hx, embG_eB_inl_inl_apply_eq_ite, if_neg]
      rintro rfl
      have := congrArg Fin.val hx
      simp [U.eB, eI] at this
    · rw [embG_mulVec_liftVec_eB_apply]
      rfl

private theorem muP_mulVec_liftVec_eB_apply (q : Matrix (Fin p) (Fin p) ℂ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    (U.muP k p ρ q *ᵥ liftVec k p ρ z) (U.eB k p ρ x) = Sum.elim (Sum.elim (fun _ => 0) z) (fun _ => 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (U.eB k p ρ)]
  simp only [U.muP, Ux6.block3_apply, liftVec_eB]
  rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.one_apply]

theorem ell_muP (z : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (q : Matrix (Fin p) (Fin p) ℂ) :
    ell k (p + ρ) (liftVec k p ρ z) (U.muP k p ρ q) = U.supS q := by
  simp only [Formalism.QuantumDeterminants.ell, U.supS]
  rw [Fin.sum_univ_add]
  refine (congrArg₂ HAdd.hAdd ?_ (Finset.sum_eq_zero fun b _ => ?_)).trans (add_zero _)
  · apply Finset.sum_congr rfl
    intro a _
    have ha := a.isLt
    rw [eI_X a]
    by_cases h : a.val + 1 < p
    · have h' : (Fin.castAdd ρ a).val + 1 < p + ρ := by simp; omega
      have hX' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inl ⟨a.val + 1, h⟩)) := eI_X' (a.val + 1) h h'
      rw [dite_eq_left h', dite_eq_left h, hX']
      simp [U.muP, Ux6.block3_apply]
    · rw [dite_eq_right h]
      split_ifs with h'
      · have hρ : 0 < ρ := by simp at h'; omega
        have hV' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ =
            U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨0, hρ⟩))) := by
          ext
          simp [U.eB, eI] <;> omega
        rw [hV']
        simp [U.muP, Ux6.block3_apply]
      · rw [muP_mulVec_liftVec_eB_apply]
        rfl
  · have hb := b.isLt
    rw [eI_V b]
    split_ifs with h'
    · have h : b.val + 1 < ρ := by simp at h'; omega
      have hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩))) := eI_V' (b.val + 1) h (by simp; omega)
      have hne : eI k ρ b ≠ eI k ρ ⟨b.val + 1, h⟩ := by
        intro e
        have := congrArg Fin.val e
        simp [eI] at this
      rw [hV']
      simp [U.muP, Ux6.block3_apply, Matrix.one_apply, hne]
    · rw [muP_mulVec_liftVec_eB_apply]
      exact hz _ (Or.inl (by simp [eI]))

theorem psi_of_ell {r r' : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r)
    (g' : B.Mat k r') (h : ell k r z g = ell k r' z' g') : psi k r z cStd g = psi k r' z' cStd g' := by
  simp only [Formalism.QuantumDeterminants.psi, h]

theorem psi_measure_preserving : PsiMuP := by
  intro k p ρ z' u hz
  simp only [Formalism.QuantumDeterminants.psi, G.psi, U.betaU, ell_muP z' hz]
  show (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [neg_mul, Complex.ofReal_neg]
  ring

theorem upper_isUpUni (u : G.UT p → ℂ) : Formalism.DoubleCosetMeasures.IsUpUni (G.upper u) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
    simp [G.upper, G.strictUpper, Matrix.one_apply, h1, h2]
  · simp [G.upper, G.strictUpper]

theorem rn_nset (x : U.RC k p ρ) : U.Rn k p ρ x ∈ QuantumDeterminants.Nset k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨x, rfl⟩)

theorem psi_right_equivariant : PsiRight := by
  intro k p ρ z' ν' u x hz hν
  have hz0 := inWb_liftVec (p := p) hz
  have hcl := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)
  have h1 := embG_nset (p := p) hν
  have h2 := Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset (k := k) (ρ := ρ) _ (upper_isUpUni u)
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ (hcl.mul_mem _ h1 _ h2) (rn_nset x),
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ h1 h2, psi_of_ell _ z' _ ν' (ell_embG z' ν')]

theorem corner_block_action_invariant (y : B.Mat k ρ) (x : U.RC k p ρ) (v : Fin (2 * ρ + k + 1) → ℂ) (hy : yᴴ * Hpk k ρ * y = Hpk k ρ)
    (hv : y *ᵥ v = v) :
    (-(G.wMat p * (Matrix.of (rcAct y x).1)ᴴ * Hpk k ρ)) *ᵥ v = (-(G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ)) *ᵥ v := by
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have hv' : yᴴ *ᵥ (Hpk k ρ *ᵥ v) = Hpk k ρ *ᵥ v := by
    calc yᴴ *ᵥ (Hpk k ρ *ᵥ v) = yᴴ *ᵥ (Hpk k ρ *ᵥ (y *ᵥ v)) := by rw [hv]
      _ = (yᴴ * Hpk k ρ * y) *ᵥ v := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Hpk k ρ *ᵥ v := by rw [hy]
  have h2 : (G.wMat p * (Matrix.of x.1)ᴴ * yᴴ * Hpk k ρ) *ᵥ v = (G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ v := by
    simp only [← Matrix.mulVec_mulVec, hv']
  rw [h1, Matrix.conjTranspose_mul, Matrix.neg_mulVec, Matrix.neg_mulVec, ← Matrix.mul_assoc, h2]

theorem psi_right_action_comm : PsiRnAct := by
  intro k p ρ z' h' x hz hh
  have hz0 := inWb_liftVec (p := p) hz
  apply psi_of_ell
  rw [Ux3.rn_eq, Ux3.rn_eq, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0]
  by_cases hp : 0 < p
  · rw [dite_eq_left hp, dite_eq_left hp]
    by_cases hρ : 0 < ρ
    · rw [dite_eq_left hρ, dite_eq_left hρ]
      have e := congrFun (corner_block_action_invariant h' x (bvec (eI k ρ ⟨0, hρ⟩)) hh.1 (hh.2.1 ⟨0, hρ⟩).1) ⟨p - 1, by omega⟩
      have e2 : ∀ M : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ,
          M ⟨p - 1, by omega⟩ ⟨0, by omega⟩ = (M *ᵥ bvec (eI k ρ ⟨0, hρ⟩)) ⟨p - 1, by omega⟩ := by
        intro M; simp only [bvec, Matrix.mulVec_single_one]; rfl
      exact (e2 _).trans (e.trans (e2 _).symm)
    · rw [dite_eq_right hρ, dite_eq_right hρ]
      have hlow : U.lowV k p ρ (liftVec k p ρ z') = z' := by
        funext q; simp only [U.lowV, liftVec]; rw [dite_eq_left (by omega)]; congr 1; ext; simp
      rw [hlow]
      exact congrFun (corner_block_action_invariant h' x z' hh.1 hh.2.2) _
  · rw [dite_eq_right hp, dite_eq_right hp]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section sm

variable {r : ℕ} {TT : ℝ}

theorem smInv_mem (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) :
    (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹) ∈ MA.smSub r TT := by
  have hsm : ContDiffOn ℝ MA.sm (MA.ext (f : MA.Qp r TT → ℂ)) (MA.Qset r TT) := f.2
  have hne : ∀ x ∈ MA.Qset r TT, MA.ext (f : MA.Qp r TT → ℂ) x ≠ 0 := by
    intro x hx
    simp only [MA.ext, dif_pos hx]
    exact hf _
  show ContDiffOn ℝ MA.sm (MA.ext (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹)) (MA.Qset r TT)
  exact (hsm.inv hne).congr fun x hx => by simp only [Pi.inv_apply, MA.ext, dif_pos hx]

theorem inverse_apply (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) (q : MA.Qp r TT) :
    ((Ring.inverse f : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ := by
  obtain ⟨g, hg⟩ : ∃ g : MA.SmQ r TT, ∀ q, (g : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ :=
    ⟨⟨_, smInv_mem f hf⟩, fun _ => rfl⟩
  have hfg : f * g = 1 := by
    apply Subtype.ext
    funext q'
    show (f : MA.Qp r TT → ℂ) q' * (g : MA.Qp r TT → ℂ) q' = 1
    rw [hg, mul_inv_cancel₀ (hf q')]
  have hu : IsUnit f := ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, rfl⟩
  have hinv : Ring.inverse f = g := by
    calc Ring.inverse f = Ring.inverse f * (f * g) := by rw [hfg, mul_one]
      _ = g := by rw [← mul_assoc, Ring.inverse_mul_cancel f hu, one_mul]
  rw [hinv, hg]

theorem coordQ_vz (q : MA.Qp r TT) : ((MA.coordQ (r := r) (TT := TT) M.vz : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = q.1.2 := by
  show MA.coordE (M.vz (r := r)) q.1 = q.1.2
  simp [MA.coordE, MA.zE, M.vz]

theorem coordQ_vzb (q : MA.Qp r TT) :
    ((MA.coordQ (r := r) (TT := TT) M.vzb : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = (starRingEnd ℂ) q.1.2 := by
  show MA.coordE (M.vzb (r := r)) q.1 = (starRingEnd ℂ) q.1.2
  simp [MA.coordE, MA.zE, M.vzb]

end sm

def ggS (P : M.Par) : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT

section tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem trR_unit (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hΨ : ∀ q : MA.Qp P.r P.TT, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      (φ : MA.Qp P.r P.TT → ℂ) q • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)) :
    trR P Bs e Ψ = fun ρ => φ * trR P Bs e Φ ρ := by
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  funext ρ
  have hraw : rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      fun q => (φ : MA.Qp P.r P.TT → ℂ) q * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    funext q
    simp only [rawR]
    rw [hΨ q, hsm, inner_smul_right]
    ring
  show MA.toSm P (rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    φ * MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)
  rw [hraw]
  generalize rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ = u
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem φ.2 hu
    rw [dif_pos hmul, dif_pos hu]
    rfl
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∉ MA.smSub P.r P.TT := by
      intro hm
      apply hu
      have h2 := (MA.smSub P.r P.TT).mul_mem (smInv_mem φ hφ) hm
      convert h2 using 1
      funext q
      simp [hφ q]
    rw [dite_eq_right hmul, dite_eq_right hu, mul_zero]

theorem sec_pt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    (q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' ∧
      Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (NF.muZ P.k P.r Bs.μsec q.1.2) = q.1.2 := by
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hq : (q.1.1, q.1.2) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨q.2.1, hζ⟩
  exact ⟨Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq,
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ⟩

theorem tt_pos (P : M.Par) (hP : P.OK) : 0 < P.TT := by
  show 0 < P.T * P.T'
  exact mul_pos hP.T_pos hP.T'_pos

theorem zeta_ne (P : M.Par) (hP : P.OK) (q : MA.Qp P.r P.TT) : q.1.2 ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  intro h
  rw [h, map_zero] at h2
  linarith [tt_pos P hP]

theorem gg_ne (P : M.Par) (q : MA.Qp P.r P.TT) : (q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ)) ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  rw [Complex.mul_conj]
  intro h
  have h3 : ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) = 0 := by
    push_cast
    exact h
  rw [Complex.ofReal_eq_zero] at h3
  linarith

theorem trR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (j : Fin 6)
    (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hv : ∀ q : MA.Qp P.r P.TT, Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.1.2) = (φ : MA.Qp P.r P.TT → ℂ) q)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    trR P Bs e (X.fn j Φ) =
      fun ρ => φ * trR P Bs e Φ ρ := by
  refine trR_unit P Bs e Φ (X.fn j Φ) φ hφ fun q => ?_
  have h := X.fn_apply j Φ _ (sec_pt P Bs hpl q).1
  dsimp only at h
  rw [h, hv q]

end tr

theorem gauge_function_holds : GTFn := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e Φ
  obtain ⟨hpl, -, -, hL, -, -, -⟩ := hH
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hzv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by rw [coordQ_vz]; exact zeta_ne P hP q
  have hzbv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by
    rw [coordQ_vzb]; exact (map_ne_zero _).2 (zeta_ne P hP q)
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 0 _ hzv (fun q => by rw [coordQ_vz]; exact hz q) Φ).trans ?_
    exact (hsc ((MA.DQ P).zP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 1 (Ring.inverse (MA.coordQ M.vz))
      (fun q => by rw [inverse_apply _ hzv]; exact inv_ne_zero (hzv q))
      (fun q => by rw [inverse_apply _ hzv, coordQ_vz]; show (Q.zetaL _ _ _ _ _ _)⁻¹ = _; rw [hz q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ziP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 2 _ hzbv (fun q => by
      rw [coordQ_vzb]; show star (Q.zetaL _ _ _ _ _ _) = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 3 (Ring.inverse (MA.coordQ M.vzb))
      (fun q => by rw [inverse_apply _ hzbv]; exact inv_ne_zero (hzbv q))
      (fun q => by
        rw [inverse_apply _ hzbv, coordQ_vzb]; show (star (Q.zetaL _ _ _ _ _ _))⁻¹ = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbiP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 4 _ hggv (fun q => by rw [hgg]; exact hGG q) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggP P.TT) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

def cW (k r : ℕ) (θ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def PhaseSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ θ : ℝ, ∃ h h' : Q.Mx k r, h ∈ UWset k r z ∧ h' ∈ UWset k r z' ∧
      (∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        h *ᵥ (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = Complex.exp (-((θ : ℂ) * Complex.I)) • (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) ∧
        (∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = 0 → h *ᵥ v = v) ∧
        CP.mu0 k r z z' (rot θ ζ) = h * cW k r θ * CP.mu0 k r z z' ζ * h') ∧
      ∀ v, inWb k r v → herm (Hpk k r) v z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v

def LowerUnipotentRotation : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (θ : ℝ) (Y : ℂ) (f : Q.Mx k r → E), ∀ g ∈ Q.Glev k r (Fin.last r),
      Q.tL k r z z' (Fin.last r) Y 1 0 f (cW k r θ * g) =
        Complex.exp (-((θ : ℂ) * Complex.I)) • Q.tL k r z z' (Fin.last r) Y 1 0 (fun x => f (cW k r θ * x)) g

def RotRadSp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ (θ : ℝ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp)), Φ ∈ Q.RadSp k r z z' π π' →
      (fun c g => Φ c (cW k r θ * g)) ∈ Q.RadSp k r z z' π π'

def ThtRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ (θ : ℝ) (h h' : Q.Mx P.k P.r), h ∈ UWset P.k P.r Bs.z → h' ∈ UWset P.k P.r Bs.z' →
    ∀ ζ ∈ Gauge.GC.Ann P,
      h *ᵥ SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = Complex.exp (-((θ : ℂ) * Complex.I)) • SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z = 0 → herm (Hpk P.k P.r) v (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 →
        h *ᵥ v = v) →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v) →
      ∀ Xf : Wq →L[ℂ] Wp,
        (Bs.π h).comp (((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) Xf).comp (Bs.π' h')) =
          Complex.exp ((θ : ℂ) * Complex.I) • (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) ((Bs.π h).comp (Xf.comp (Bs.π' h')))

def PhaseInvOfCut : Prop :=
  PhaseSec → LowerUnipotentRotation → RotRadSp → ThtRot → KapLine → AlgSS → DatumConst → FibStable → PhaseInv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hs_expand (A C : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec C) =
      ∑ i, inner ℂ (A (stdOrthonormalBasis ℂ Wq i)) (C (stdOrthonormalBasis ℂ Wq i)) := by
  simp only [B.hsVec, PiLp.inner_apply, PiLp.toLp_apply]

theorem hs_comp_right (A C : Wq →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (hQ : ∀ v w, inner ℂ (Q v) w = inner ℂ v (Q w)) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp Q)) = inner ℂ (B.hsVec (A.comp Q)) (B.hsVec C) := by
  rw [hs_expand, hs_expand]
  set b := stdOrthonormalBasis ℂ Wq
  have hQe : ∀ i, Q (b i) = ∑ j, inner ℂ (b j) (Q (b i)) • b j := fun i => (b.sum_repr' _).symm
  simp only [ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; ext i; rw [hQe i, map_sum, inner_sum]
  conv_rhs => arg 2; ext j; rw [hQe j, map_sum, sum_inner]
  simp only [map_smul, inner_smul_right, inner_smul_left]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [inner_conj_symm, hQ]

theorem hs_comp_sum {ι : Type} [Fintype ι] (A C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) (f : ι → ℂ) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp (∑ σ, f σ • Q σ))) =
      ∑ σ, f σ * inner ℂ (B.hsVec A) (B.hsVec (C.comp (Q σ))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hs_expand, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  exact Finset.sum_comm

theorem comp_sum_eq {ι : Type} [Fintype ι] (C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) :
    C.comp (∑ σ, Q σ) = ∑ σ, C.comp (Q σ) := by
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ContinuousLinearMap.sum_apply, map_sum]

end hs

theorem gauge_kappa_of_point_line : GTKapOfCut := by
  intro hPt hLine Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d hH
  have hQQ := hQ.1
  have hQ1 := hQ.2.1
  have hQs := hQ.2.2.1
  have hQk := hQ.2.2.2
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hcs : CSec P.k P.r Bs.z Bs.z' Bs.μsec := hH.2.2.1
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl

  set ζ0 : ℂ := ((Real.sqrt P.TT + 1 : ℝ) : ℂ) with hζ0def
  have hTT : 0 < P.TT := mul_pos hpl.1.T_pos hpl.1.T'_pos
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    have hs := Real.sq_sqrt hTT.le
    nlinarith [Real.sqrt_nonneg P.TT]

  have hFib : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    have hS : NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ = NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ0 :=
      hcs.2 ζ ζ0 (by rw [hTz]; exact hζ) (by rw [hTz]; exact hζ0)
    unfold NF.Fib
    rw [hS]
  choose E hEF hEQ hE1 hEu using fun ρ => hLine Wp Wq P Bs X d hH Qr hQ ζ0 hζ0 ρ

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
      by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
      hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩
  have hcomp : ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0, ∀ ρ,
      Z.comp (Qr ρ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro Z hZ ρ
    let φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator fun _ => Z
    have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
      refine ⟨(contDiffOn_const (c := Z)).congr fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · simp [φ, Set.indicator_of_mem hx]
      · simp only [φ, Set.indicator_of_mem hx]
        rw [hFib x.2 (by rw [← hTz]; exact hx.2)]; exact hZ
      · simp [φ, Set.indicator_of_notMem hx]
    obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB φ hφ
    let c0 : Fin P.r → ℂ := fun _ => 1
    have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
    have hq0 : ((c0, ζ0) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ0⟩
    have hval : Φ c0 (NF.muZ P.k P.r Bs.μsec ζ0) = Z := by
      have h := congrFun hrad (c0, ζ0)
      simp only [NF.radR, Set.indicator_of_mem hq0, φ] at h
      exact h
    let q0 : MA.Qp P.r P.TT := ⟨(c0, ζ0), ⟨hc0, hζ0⟩⟩
    let f : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0
    have hk := hQk f ⟨Φ, hΦ⟩ q0
    have hsum : (∑ σ, f σ • Qr σ) = Qr ρ := by
      simp [f, Finset.sum_ite_eq']
    rw [hsum] at hk
    have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ f).1 ⟨Φ, hΦ⟩).2
    have h2 := hmem.2.1 (c0, ζ0) hq0
    simp only [NF.radR, Set.indicator_of_mem hq0] at h2
    have hk' : (((d.κ f).1 ⟨Φ, hΦ⟩ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ0) = Z.comp (Qr ρ) := by
      rw [← hval]; exact hk
    rw [hk'] at h2
    exact h2
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ => ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun Z hZ => ?_⟩⟩, ?_⟩
  · rw [hFib ζ hζ]; exact hEF ρ
  · split_ifs with h
    · subst h; exact hE1 ρ
    · calc inner ℂ (B.hsVec (E ρ)) (B.hsVec (E ρ'))
          = inner ℂ (B.hsVec (E ρ)) (B.hsVec ((E ρ').comp (Qr ρ'))) := by rw [hEQ ρ']
        _ = inner ℂ (B.hsVec ((E ρ).comp (Qr ρ'))) (B.hsVec (E ρ')) := hs_comp_right _ _ _ (hQs ρ')
        _ = 0 := by
          have h0 : (E ρ).comp (Qr ρ') = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ ρ', if_neg h, ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left]
  · have hZ0 : Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by rw [← hFib ζ hζ]; exact hZ
    have hdec : Z = ∑ ρ, Z.comp (Qr ρ) := by
      rw [← comp_sum_eq, hQ1]; rfl
    conv_lhs => rw [hdec]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hfix : (Z.comp (Qr ρ)).comp (Qr ρ) = Z.comp (Qr ρ) := by
      rw [ContinuousLinearMap.comp_assoc, hQQ ρ ρ, if_pos rfl]
    rw [hEu ρ _ (hcomp Z hZ0 ρ) hfix, hs_comp_right _ _ _ (hQs ρ), hEQ ρ]
  · intro f Φ
    funext ρ
    have hraw : rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
        f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
      funext q
      simp only [rawR, Pi.smul_apply, smul_eq_mul]
      rw [hQk f Φ q, hs_comp_sum]
      have hterm : ∀ σ, f σ * inner ℂ (B.hsVec (E ρ))
          (B.hsVec (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (Qr σ))) =
          if σ = ρ then f ρ * inner ℂ (B.hsVec (E ρ))
            (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) else 0 := by
        intro σ
        rw [hs_comp_right _ _ _ (hQs σ)]
        split_ifs with h
        · subst h; rw [hEQ σ]
        · have h0 : (E ρ).comp (Qr σ) = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ σ, if_neg (Ne.symm h), ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left, mul_zero]
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    show MA.toSm P (rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) = _
    rw [hraw, VLem.toSm_smul]
    have hkap : MA.kap P (MA.DQ P) f = Matrix.diagonal fun σ => algebraMap ℂ (MA.DQ P).Pr (f σ) := rfl
    rw [hkap, VLem.actA_diag]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

abbrev Mb (k : ℕ) := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

def e0 (k r : ℕ) (X : Mb k) : Q.Mx k r := Em k r * X * (Em k r)ᵀ

def dnu (k : ℕ) (a b c : ℂ) : Mb k :=
  a • Matrix.single 0 0 1 + b • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
    c • Matrix.single (Fin.last k) (Fin.last k) 1

def kap (T T' : ℝ) : ℂ := ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)

def nuI (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k := nu k (star (wZ T T' ζ)) (-sZ T T' ζ)

def H1 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k 0 ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) (-(kap T T')⁻¹)

def H2 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k (-(kap T T')⁻¹) ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) 0

def InL (k : ℕ) (C : Mb k) : Prop := ∀ i, C i (Fin.last k) = 0 ∧ C (Fin.last k) i = 0

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVTr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

def Vp (P : M.Par) (Y : ℂ) (i : ℕ) : Wd.M2 (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => Wd.Ts (MA.siteA P (MA.DQ P) l) Y).prod

theorem Vp_zero (P : M.Par) (Y : ℂ) : Vp P Y 0 = 1 := by
  simp [Vp]

theorem Vp_succ (P : M.Par) (Y : ℂ) (i : ℕ) (h : i < P.r) :
    Vp P Y (i + 1) = Wd.Ts (MA.siteA P (MA.DQ P) ⟨i, h⟩) Y * Vp P Y i := by
  simp [Vp, List.take_add_one, h]

theorem sitesCommonSpace_v0_eq_Vp (P : M.Par) (Y : ℂ) : Wd.v0 (MA.sites P (MA.DQ P)) Y = fun b => Vp P Y P.r b 0 := by
  funext b
  simp [Wd.v0, MA.sites, Vp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le, Function.comp_def]

theorem Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) * V 0 0 + -σ.c * V 1 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 1 0 = σ.ci * V 0 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

section ind

theorem actA_p (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).p f = fun ρ => MA.eulerQ (TT := P.TT) (M.vc l) (f ρ) :=
  actA_sc P _ f

theorem actA_c (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).c f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ :=
  actA_sc P _ f

theorem actA_ci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).ci f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc l)) * f ρ :=
  actA_sc P _ f

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Y : ℂ) • (Q.vAB P.r (Y : ℂ) i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 0) Φ =
        (Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc ((Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_vector_transition_holds : GVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y b
  have h := vab_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases b
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

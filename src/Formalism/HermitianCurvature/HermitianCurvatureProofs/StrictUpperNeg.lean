module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatExtMulVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNegBetaL

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section utinv

open Formalism.FourierDecayAlt.P.Dx2.SplitM

def eQ (j : ℕ) : ((G.UT j → ℂ) × (Fin j → ℂ)) ≃ᵐ (G.UT (j + 1) → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : G.UT j ⊕ Fin j => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : G.UT (j + 1) => ℂ) eL)

theorem eQ_eq (j : ℕ) (p : (G.UT j → ℂ) × (Fin j → ℂ)) : eQ j p = combineUpperTriangularCoords p := rfl

theorem eQ_mp (j : ℕ) : MeasurePreserving (eQ j) volume volume := combined_coordinates_measure_preserving

theorem upper_eQ_cc {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a b : Fin j) :
    G.upper (eQ j p) a.castSucc b.castSucc = G.upper p.1 a b := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, Fin.castSucc_inj,
    Fin.castSucc_lt_castSucc_iff]
  congr 1
  split_ifs with h
  · have e : (⟨(a.castSucc, b.castSucc), Fin.castSucc_lt_castSucc_iff.mpr h⟩ : G.UT (j + 1)) = eL (Sum.inl ⟨(a, b), h⟩) := rfl
    rw [e, eQ_eq, combined_coordinates_left]
  · rfl

theorem upper_eQ_cl {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a : Fin j) :
    G.upper (eQ j p) a.castSucc (Fin.last j) = p.2 a := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rw [if_neg (Fin.castSucc_ne_last a), dite_eq_left (Fin.castSucc_lt_last a), zero_add]
  have e : (⟨(a.castSucc, Fin.last j), Fin.castSucc_lt_last a⟩ : G.UT (j + 1)) = eL (Sum.inr a) := rfl
  rw [e, eQ_eq, combineUpperTriangular_inr]

theorem upper_eQ_lc {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (b : Fin j) :
    G.upper (eQ j p) (Fin.last j) b.castSucc = 0 := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rw [if_neg (Ne.symm (Fin.castSucc_ne_last b)), dite_eq_right (not_lt.2 (Fin.castSucc_lt_last b).le), zero_add]

theorem upper_eQ_ll {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) :
    G.upper (eQ j p) (Fin.last j) (Fin.last j) = 1 := by
  simp [G.upper, G.strictUpper]

def utInv (m : ℕ) (u : G.UT m → ℂ) : G.UT m → ℂ := StabilizerDisintegration.utc (G.upper u)⁻¹

theorem upper_inv_mem {m : ℕ} (u : G.UT m → ℂ) : (G.upper u)⁻¹ ∈ C2.UTset m :=
  Formalism.FourierDecayAlt.P.C2x2.ut_inv (StabilizerDisintegration.UC.upper_mem u)

theorem upper_utInv {m : ℕ} (u : G.UT m → ℂ) : G.upper (utInv m u) = (G.upper u)⁻¹ :=
  StabilizerDisintegration.UC.upper_utc (upper_inv_mem u)

theorem utInv_eQ {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) :
    utInv (j + 1) (eQ j p) = eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2)) := by
  have hu1 : IsUnit (G.upper p.1).det := by rw [StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
  have hprod : G.upper (eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) * G.upper (eQ j p) = 1 := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
    · simp [upper_eQ_lc, upper_eQ_ll]
    · simp [upper_eQ_lc, upper_eQ_ll, Matrix.one_apply]
      exact (Fin.castSucc_ne_last _).symm
    · simp only [upper_eQ_cc, upper_eQ_cl, upper_eQ_ll, mul_one, Matrix.one_apply, Fin.castSucc_ne_last, if_false,
        upper_utInv]
      have : ∑ x : Fin j, (G.upper p.1)⁻¹ a x * p.2 x = ((G.upper p.1)⁻¹ *ᵥ p.2) a := rfl
      rw [this]; simp
    · simp only [upper_eQ_cc, upper_eQ_lc, mul_zero, add_zero, upper_utInv, Matrix.one_apply,
        Fin.castSucc_inj]
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hu1, Matrix.one_apply]
  have hinv : (G.upper (eQ j p))⁻¹ = G.upper (eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) :=
    Matrix.inv_eq_left_inv hprod
  unfold utInv
  rw [hinv, StabilizerDisintegration.UC.utc_upper]
  rfl

theorem utInv_mp : ∀ m : ℕ, MeasurePreserving (utInv m) volume volume
  | 0 => by
    have : IsEmpty (G.UT 0) := ⟨fun ⟨⟨a, _⟩, _⟩ => a.elim0⟩
    have : utInv 0 = id := funext fun u => funext fun q => isEmptyElim q
    rw [this]; exact MeasurePreserving.id _
  | j + 1 => by
    have ih := utInv_mp j
    have hA : ∀ u1 : G.UT j → ℂ, ‖(-(G.upper u1)⁻¹).det‖ = 1 := by
      intro u1
      have hu := upper_inv_mem u1
      rw [Matrix.det_neg, StabilizerDisintegration.UC.det_UT hu, mul_one]
      simp
    have hg : MeasurePreserving (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2)))
        volume volume := by
      rw [Measure.volume_eq_prod]
      refine MeasurePreserving.skew_product (f := utInv j) (g := fun u1 v => -((G.upper u1)⁻¹ *ᵥ v)) ih ?_ ?_
      · have hc : Continuous (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => -((G.upper p.1)⁻¹ *ᵥ p.2)) := by
          have h1 : Continuous (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (G.upper p.1)⁻¹) := by
            have : (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (G.upper p.1)⁻¹) =
                fun p => (G.upper p.1).adjugate := by
              funext p
              rw [Matrix.inv_def, StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; simp
            rw [this]
            exact (StabilizerDisintegration.UC.cont_upper.comp continuous_fst).matrix_adjugate
          exact (h1.matrix_mulVec continuous_snd).neg
        exact hc.measurable
      · refine Filter.Eventually.of_forall fun u1 => ?_
        have h := mp_vec (-(G.upper u1)⁻¹) (hA u1)
        have e : (fun v : Fin j → ℂ => -((G.upper u1)⁻¹ *ᵥ v)) = fun v => (-(G.upper u1)⁻¹) *ᵥ v := by
          funext v; rw [Matrix.neg_mulVec]
        rw [e]; exact h.map_eq
    have e : utInv (j + 1) = eQ j ∘ (fun p : (G.UT j → ℂ) × (Fin j → ℂ) =>
        (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) ∘ (eQ j).symm := by
      funext u
      simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] using
        utInv_eQ ((eQ j).symm u)
    rw [e]
    exact (eQ_mp j).comp (hg.comp (MeasurePreserving.symm (eQ j) (eQ_mp j)))

end utinv

section rad

variable {k j ρ : ℕ}

theorem strictUpper_neg {d : ℕ} (v : G.UT d → ℂ) : G.strictUpper (-v) = -G.strictUpper v := by
  ext i j
  simp only [G.strictUpper, Matrix.of_apply, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp

theorem skewOf_neg (q : (G.UT j → ℂ) × (Fin j → ℝ)) : U.skewOf (-q) = -U.skewOf q := by
  simp only [U.skewOf, Prod.fst_neg, Prod.snd_neg, strictUpper_neg, Matrix.conjTranspose_neg]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply]
  split_ifs <;> push_cast <;> ring

theorem rn_mul_neg (x : U.RC k j ρ) : U.Rn k j ρ x * U.Rn k j ρ (-x) = 1 := by
  unfold U.Rn
  rw [Ux3.block3_mul, ← Ux3.block3_one]
  have hc : (Matrix.of (-x).1 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = -Matrix.of x.1 := rfl
  have hs : U.skewOf (-x).2 = -U.skewOf x.2 := skewOf_neg x.2
  rw [hc, hs]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_add_cancel, add_neg_cancel]

  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg, Matrix.mul_assoc]
  module

theorem rn_inv (x : U.RC k j ρ) : (U.Rn k j ρ x)⁻¹ = U.Rn k j ρ (-x) := Matrix.inv_eq_right_inv (rn_mul_neg x)

theorem negRC_mp : MeasurePreserving (fun x : U.RC k j ρ => -x) (U.muRC k j ρ) (U.muRC k j ρ) := by
  have h1 : MeasurePreserving (fun c : Fin (2 * ρ + k + 1) → Fin j → ℂ => -c) volume volume :=
    volume_preserving_pi (fun _ => volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume))
  have h2 : MeasurePreserving (fun c : G.UT j → ℂ => -c) volume volume :=
    volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume)
  have h3 : MeasurePreserving (fun c : Fin j → ℝ => -c) volume volume :=
    volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume)
  unfold U.muRC
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact h1.prod (h2.prod h3)

theorem muP_one : U.muP k j ρ (1 : Matrix (Fin j) (Fin j) ℂ) = 1 := by
  unfold U.muP
  rw [Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Ux3.wMat_mul_self, Ux3.block3_one]

theorem leviElement_inv (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) : (U.muP k j ρ q)⁻¹ = U.muP k j ρ q⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Dx2.Split.leviElement_mul, Matrix.mul_nonsing_inv _ hq, muP_one]

end rad

section split

variable {k : ℕ}

theorem embG_one {j ρ : ℕ} : U.embG k j ρ (1 : B.Mat k ρ) = 1 := by
  unfold U.embG; exact Ux3.block3_one

def psiF (k j : ℕ) (p : U.RC k j 0 × (G.UT j → ℂ)) : Mt k (j + 0) := Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))

def psiR (k j : ℕ) (p : U.RC k j 0 × (G.UT j → ℂ)) : Mt k (j + 0) := Matrix.of.symm (U.muP k j 0 (G.upper p.2) * U.Rn k j 0 p.1)

theorem psiF_cont (j : ℕ) : Continuous (psiF k j) := by
  unfold psiF
  exact ((Dx2.SplitF.rn_cont (k := k) j 0).comp continuous_fst).matrix_mul
    ((Dx2.SplitF.mup_cont (k := k) j 0).comp continuous_snd)

theorem psiR_cont (j : ℕ) : Continuous (psiR k j) := by
  unfold psiR
  exact ((Dx2.SplitF.mup_cont (k := k) j 0).comp continuous_snd).matrix_mul
    ((Dx2.SplitF.rn_cont (k := k) j 0).comp continuous_fst)

theorem psiF_meas (j : ℕ) : Measurable (psiF k j) := by
  exact (psiF_cont j).measurable

theorem psiR_meas (j : ℕ) : Measurable (psiR k j) := by
  exact (psiR_cont j).measurable

theorem muN_fwd (j : ℕ) : D.muN k (j + 0) = ((U.muRC k j 0).prod (volume : Measure (G.UT j → ℂ))).map (psiF k j) := by
  have hs := Dx2.SplitF.split_all (k := k) j 0
  have h0 : D.muN k 0 = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := rfl
  have : SigmaFinite (U.muRC k j 0) := Dx2.SplitF.sf_RC j 0
  rw [hs, h0, Measure.prod_dirac]
  have hm : Measurable (fun u : G.UT j → ℂ => (u, Matrix.of.symm (1 : B.Mat k 0))) :=
    measurable_id.prodMk measurable_const
  conv_lhs => rw [← Measure.map_id (μ := U.muRC k j 0)]
  rw [Measure.map_prod_map _ _ measurable_id hm,
    Measure.map_map (Dx2.SplitF.psi_meas j 0) (measurable_id.prodMap hm)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, Dx2.SplitF.Psi, psiF,
    Equiv.apply_symm_apply, embG_one, Matrix.mul_one]

theorem muN_rev (j : ℕ) : D.muN k (j + 0) = ((U.muRC k j 0).prod (volume : Measure (G.UT j → ℂ))).map (psiR k j) := by
  have : SigmaFinite (U.muRC k j 0) := Dx2.SplitF.sf_RC j 0
  have hinv := Formalism.FourierDecayAlt.P.haar_measure_inversion k (j + 0) (Nset k (j + 0)) (D.muN k (j + 0))
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (j + 0)) (Dx2.MN.haar (k := k) (j + 0))
  rw [← hinv, muN_fwd j, Measure.map_map (Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas) (psiF_meas j)]
  have hmp : MeasurePreserving (fun p : U.RC k j 0 × (G.UT j → ℂ) => (-p.1, utInv j p.2))
      ((U.muRC k j 0).prod volume) ((U.muRC k j 0).prod volume) :=
    negRC_mp.prod (utInv_mp j)
  have e : (B2.invM ∘ psiF k j) = psiR k j ∘ (fun p : U.RC k j 0 × (G.UT j → ℂ) => (-p.1, utInv j p.2)) := by
    funext p
    have hu : IsUnit (G.upper p.2).det := by rw [StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
    show Matrix.of.symm ((Matrix.of (Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))))⁻¹) =
      Matrix.of.symm (U.muP k j 0 (G.upper (utInv j p.2)) * U.Rn k j 0 (-p.1))
    rw [show Matrix.of (Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))) =
      U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2) from rfl, Matrix.mul_inv_rev, rn_inv, leviElement_inv _ hu, upper_utInv]
  rw [e, ← Measure.map_map (psiR_meas j) hmp.measurable, hmp.map_eq]

end split

end Formalism.FourierDecayAlt.P.PBM
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormAnisotropicPart
namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

section lev

variable {k : ℕ}

theorem castV_mulVec' {a b : ℕ} (h : a = b) (M : B.Mat k a) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h (M *ᵥ v) = D.castM h M *ᵥ D.castV h v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]

theorem zL_lift {o ρ r : ℕ} (h : o + ρ = r) (v : Fin (2 * ρ + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (D.castV h (liftVec k o ρ v)) = v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]
  funext i
  have := Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_levPos_gen (k := k) o ρ v i
  simpa [Formalism.FourierDecayAlt.P.Dx2.Tower.zL, levPos] using this

theorem zL_smul {o ρ r : ℕ} (h : o + ρ = r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (c • v) = c • Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v := by
  funext i; simp [Formalism.FourierDecayAlt.P.Dx2.Tower.zL]

theorem hermitian_form_anisotropic_part {m : ℕ} (v w : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) (hw : inWb k m w) :
    herm (Hpk k m) v w = herm (Hb k) (wbPart k m v) (wbPart k m w) := by
  have := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV (k := k) (r := m) (wbPart k m v) (wbPart k m w)
  rwa [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hw] at this

theorem herm_zL {o ρ r : ℕ} (h : o + ρ = r) (v w : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k ρ) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h w) = herm (Hpk k r) v w := by
  rw [hermitian_form_anisotropic_part _ _ (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h v hv) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h w hw),
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, hermitian_form_anisotropic_part v w hv hw]

theorem inWb_last {r : ℕ} (v : Fin (2 * (r - r) + k + 1) → ℂ) : inWb k (r - r) v := by
  intro i hi; exfalso; have := i.isLt; omega

theorem inWb_liftLast {r : ℕ} (h : r + (r - r) = r) (v : Fin (2 * (r - r) + k + 1) → ℂ) :
    inWb k r (D.castV h (liftVec k r (r - r) v)) := by
  intro i hi
  simp only [D.castV]
  apply Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_out_gen
  simp only [Fin.val_cast]
  omega

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nuR (p : KB.Pl P Wp Wq) : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ :=
  Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) (by omega) p.ν'

def m0R (p : KB.Pl P Wp Wq) : B.Mat P.k (P.r - P.r) :=
  fun i j => p.m₀ ⟨i.val + P.r, by have := i.isLt; omega⟩ ⟨j.val + P.r, by have := j.isLt; omega⟩

theorem base_point_block_eq (p : KB.Pl P Wp Wq) :
    D.castM (by omega : P.r + (P.r - P.r) = P.r) (ιLev P.k P.r (P.r - P.r) (m0R p)) = p.m₀ := by
  obtain ⟨-, -, -, ⟨hmU, hmfix⟩, -⟩ := p.hF
  have hme : ∀ a : Fin P.r, p.m₀ *ᵥ ee P.k P.r a = ee P.k P.r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin P.r, p.m₀ *ᵥ es P.k P.r a = es P.k P.r a := fun a => (hmfix a a.isLt).2
  have hcol : ∀ (i j : Fin (2 * P.r + P.k + 1)), (j.val < P.r ∨ P.r + P.k < j.val) →
      p.m₀ i j = if i = j then 1 else 0 := by
    intro i j hj
    rcases hj with hj | hj
    · have e : bvec j = ee P.k P.r ⟨j.val, hj⟩ := by simp [ee, eI]
      have := congrFun (hme ⟨j.val, hj⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
    · have hj2 := j.isLt
      have e : bvec j = es P.k P.r ⟨2 * P.r + P.k - j.val, by omega⟩ := by
        simp only [es, esI]; congr 1; ext; simp; omega
      have := congrFun (hms ⟨2 * P.r + P.k - j.val, by omega⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
  have hrow : ∀ (i j : Fin (2 * P.r + P.k + 1)), (i.val < P.r ∨ P.r + P.k < i.val) →
      (P.r ≤ j.val ∧ j.val ≤ P.r + P.k) → p.m₀ i j = 0 := by
    intro i j hi hj
    have hmj : (p.m₀ *ᵥ bvec j) i = p.m₀ i j := by
      simp [mulVec, dotProduct, bvec, Pi.single_apply]
    rcases hi with hi | hi
    · have h1 := herm_es (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨i.val, hi⟩
      rw [← hms ⟨i.val, hi⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_es] at h1
      have hi' : eI P.k P.r ⟨i.val, hi⟩ = i := by ext; simp [eI]
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
    · have hi2 := i.isLt
      have h1 := herm_ee (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨2 * P.r + P.k - i.val, by omega⟩
      rw [← hme ⟨2 * P.r + P.k - i.val, by omega⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_ee] at h1
      have hi' : esI P.k P.r ⟨2 * P.r + P.k - i.val, by omega⟩ = i := by ext; simp [esI]; omega
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
  ext i j
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold ιLev
  by_cases hi : P.r ≤ i.val ∧ i.val ≤ P.r + P.k <;> by_cases hj : P.r ≤ j.val ∧ j.val ≤ P.r + P.k
  · rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    simp only [m0R]
    congr 1 <;> ext <;> simp <;> omega
  · rw [dite_eq_left (by simp; omega), dite_eq_right (by simp; omega), hcol i j (by omega)]
    rw [if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [dite_eq_right (by simp; omega)]
    rw [hrow i j (by omega) hj, if_neg]
    · intro h; apply hi; have := congrArg Fin.val h; simp at this; omega
  · rw [dite_eq_right (by simp; omega), hcol i j (by omega)]
    congr 1
    apply propext; constructor
    · intro h; ext; have := congrArg Fin.val h; simpa using this
    · intro h; subst h; rfl

theorem levFrame_nuR (p : KB.Pl P Wp Wq) : LevFrame p (nuR p) (m0R p) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := p.hF
  have h : P.r + (P.r - P.r) = P.r := by omega
  have hZ : (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z := by
    show (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z
    rw [← p.T.z_lev P.r le_rfl, zL_lift]
  have hZ' : (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z' := by
    show (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z'
    rw [← p.T.z'_lev P.r le_rfl, zL_lift]
  have hz := p.T.base.z_mem
  have hz' := p.T.base.z'_mem
  have hblk := base_point_block_eq p

  set Lf : (Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) → (Fin (2 * P.r + P.k + 1) → ℂ) :=
    fun v => D.castV h (liftVec P.k P.r (P.r - P.r) v) with hLf
  have hLm : ∀ v, Lf (m0R p *ᵥ v) = p.m₀ *ᵥ Lf v := by
    intro v
    simp only [hLf]
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mulVec_lift, castV_mulVec', hblk]
  have hLh : ∀ v w, herm (Hpk P.k (P.r - P.r)) v w = herm (Hpk P.k P.r) (Lf v) (Lf w) := by
    intro v w
    rw [← herm_zL h (Lf v) (Lf w) (inWb_liftLast h v) (inWb_liftLast h w), zL_lift, zL_lift]
  refine ⟨Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h p.ν' hν, hblk, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact inWb_last _
  · rw [hZ', nuR, herm_zL h _ _ hν hz', hνz]
  · rw [nuR, herm_zL h _ _ hν hν, hνν]
  · apply B2x4.mem_UH_of_herm
    intro x y
    rw [hLh, hLh x y, hLm, hLm, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]
  · intro a _; exact absurd a.isLt (by omega)
  · have e1 : m0R p *ᵥ (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.m₀ *ᵥ p.T.base.z') := by
      have := congrArg (Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h) (hLm (p.T.bs P.r).z')
      rw [zL_lift] at this
      rw [this, hZ']
      simp only [hLf]
      rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h _ hz']
    rw [e1, hmz, zL_smul, ← hZ, hZ', hZ, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz,
      Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz']

end place

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem levFrameExists_statement : PBI.LevFrameExists := by
  intro Wp Wq _ _ _ _ _ _ P p
  exact ⟨PBI.nuR p, PBI.m0R p, PBI.levFrame_nuR p⟩

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem castM_inv' {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h
  simp [D.castM]

private theorem castV_rfl' {a : ℕ} (h : a = a) (v : Fin (2 * a + k + 1) → ℂ) : D.castV h v = v := by
  funext i
  rfl

theorem psi_castM {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h v) c (D.castM h g) = psi k a v c g := by
  subst h
  simp [D.castM, castV_rfl']

theorem castM_N {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM h g ∈ Nset k b := by
  subst h
  simpa [D.castM] using hg

theorem castM_UWv {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} {g : B.Mat k a} (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by
  subst h
  simpa [D.castM, castV_rfl'] using hg

theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by
  subst h
  have e : (D.castM (k := k) (rfl : a = a)) = fun g => g := by
    funext g
    simp [D.castM]
  rw [e]
  exact continuous_id

theorem inWb_castV {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} (hv : inWb k a v) : inWb k b (D.castV h v) := by
  subst h
  rw [castV_rfl']
  exact hv

theorem uw_closedSubgroup (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B2.IsClosedSubgroup (UWset k r z) :=
  ⟨Dx2.Rad.one_UW z, fun _ ha _ hb => WeylGroupFacts.uw_mul ha hb, fun _ ha => WeylGroupFacts.uw_inv ha,
    fun _ ha => HermitianFormFactor.UH_unit (Ux3.hpk_det k r) ha.1, B6.isClosed_UWset k r z⟩

def levA (ρ : ℕ) (x : Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)))

private theorem continuous_ιLev_apply (ρ : ℕ) (p q : Fin (2 * (1 + ρ) + k + 1)) :
    Continuous fun x : Mt k ρ => ιLev k 1 ρ (Matrix.of x) p q := by
  simp only [Formalism.QuantumDeterminants.ιLev]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * ρ + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * ρ + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_pos hp, dif_neg hq]
      exact continuous_const
  · simp only [dif_neg hp]
    exact continuous_const

theorem levA_cont (ρ : ℕ) : Continuous (levA (k := k) ρ) := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [levA, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact continuous_ιLev_apply ρ _ _

private theorem castM_mul_hermitian_curvature {a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h
  simp [D.castM]

theorem lev_mul' (ρ : ℕ) (a b : B.Mat k ρ) :
    D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a * b)) =
      D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ b) := by
  have hL := PI.QnLevBasicsW.level_group_homomorphism
  unfold Formalism.QuantumDeterminants.LevHom at hL
  rw [(hL k 1 ρ).2 a b]
  exact castM_mul_hermitian_curvature _ _ _

theorem castM_back {a b : ℕ} (h : a = b) (g : B.Mat k b) : D.castM h (D.castM h.symm g) = g := by
  subst h
  simp [D.castM]

theorem castV_back {a b : ℕ} (h : a = b) (v : Fin (2 * b + k + 1) → ℂ) : D.castV h (D.castV h.symm v) = v := by
  subst h
  rw [castV_rfl', castV_rfl']

theorem levA_apply (ρ : ℕ) (x : Mt k ρ) :
    (Matrix.of (levA ρ x) : B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) := rfl

theorem lev_onto {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ) (a : B.Mat k (ρ + 1))
    (ha : a ∈ UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) :
    ∃ a0 ∈ UWset k ρ z0, D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) = a := by
  have ha' : D.castM (Nat.add_comm 1 ρ).symm a ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := by
    have := castM_UWv (Nat.add_comm 1 ρ).symm ha
    have e : D.castV (Nat.add_comm 1 ρ).symm (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) = liftVec k 1 ρ z0 := by
      have := castV_back (k := k) (Nat.add_comm 1 ρ).symm (liftVec k 1 ρ z0)
      simpa using this
    rwa [e] at this
  obtain ⟨y, hy, hy'⟩ := JCTx5.uw_onto (k := k) (i := 1) (r' := ρ) z0 _ ha'
  exact ⟨y, hy, by rw [hy']; exact castM_back _ a⟩

theorem muW_lev {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ)
    (μ0 : Measure (Mt k ρ)) (μ1 : Measure (Mt k (ρ + 1)))
    (h0 : B.IsHaarOn (UWset k ρ z0) μ0)
    (h1 : B.IsHaarOn (UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) μ1)
    (n0 : μ0 Set.univ = 1) (n1 : μ1 Set.univ = 1) :
    μ1 = μ0.map (levA ρ) := by
  set U1 := UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) with hU1
  have hm : Measurable (levA (k := k) ρ) := (levA_cont ρ).measurable
  have hmem : ∀ y ∈ UWset k ρ z0, (Matrix.of (levA ρ y) : B.Mat k (ρ + 1)) ∈ U1 := fun y hy =>
    castM_UWv _ (Dx2.Tower.lev_UW 1 ρ z0 (Matrix.of y) hy)
  set ν := μ0.map (levA (k := k) ρ) with hν
  have hνu : ν Set.univ = 1 := by rw [hν, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, n0]
  have hconc : ν U1ᶜ = 0 := by
    have hcl : IsClosed {x : Mt k (ρ + 1) | Matrix.of x ∈ U1} := B7.isClosed_UW _
    show ν {x : Mt k (ρ + 1) | Matrix.of x ∈ U1}ᶜ = 0
    rw [hν, Measure.map_apply hm hcl.measurableSet.compl]
    apply measure_mono_null _ h0.conc
    intro y hy hyU
    exact hy (hmem y hyU)
  have hleft : ∀ a ∈ U1, ν.map (lmulM a) = ν := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := lev_onto z0 a ha
    have hl : Measurable (lmulM (k := k) (r := ρ + 1) (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0))) :=
      B2x5.measurable_lmulM _
    have hl0 : Measurable (lmulM (k := k) (r := ρ) a0) := B2x5.measurable_lmulM _
    have e : lmulM (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0)) ∘ levA (k := k) ρ = levA ρ ∘ lmulM a0 := by
      funext x
      show (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) :
          B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a0 * Matrix.of x))
      rw [lev_mul']
    rw [hν, Measure.map_map hl hm, e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  have hfin : ∀ K : Set (Mt k (ρ + 1)), IsCompact K → ν K < ⊤ := by
    intro K _
    calc ν K ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hνu
      _ < ⊤ := ENNReal.one_lt_top
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (ρ + 1) U1 μ1 ν (uw_closedSubgroup (ρ + 1) _) h1 hconc hleft hfin
  have hc1 : (c : ENNReal) = 1 := by
    have := congrArg (fun μ : Measure (Mt k (ρ + 1)) => μ Set.univ) hc
    simp only [Measure.smul_apply, n1, hνu, smul_eq_mul, mul_one, ENNReal.smul_def] at this
    exact this.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hc, hc1', one_smul]

def Qm (ρ : ℕ) (p : Mt k (1 + ρ) × Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (Matrix.of p.1 * ιLev k 1 ρ (Matrix.of p.2)))

theorem Qm_cont (ρ : ℕ) : Continuous (Qm (k := k) ρ) := by
  have hI : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => ιLev k 1 ρ (Matrix.of p.2) :=
    continuous_pi fun a => continuous_pi fun b => (continuous_ιLev_apply ρ a b).comp continuous_snd
  have h1 : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => (Matrix.of p.1 : B.Mat k (1 + ρ)) := continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Qm, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply _).comp ((continuous_apply _).comp (h1.matrix_mul hI))

theorem sf_heis (ρ : ℕ) : SigmaFinite (B2.μHeis k ρ) :=
  Dx2.MN.sigma_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)

theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := Dx2.MN.sigma_of_haar (Dx2.MN.haar ρ)

theorem muN_succ' (ρ : ℕ) : D.muN k (ρ + 1) = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by
  have := sf_heis (k := k) ρ
  have := sf_muN (k := k) ρ
  have hl : Measurable (B2.levM k ρ) := (B2x2.levM_cont k ρ).measurable
  have hmu : Measurable (B2.mulM : Mt k (1 + ρ) × Mt k (1 + ρ) → Mt k (1 + ρ)) := B2x2.mulM_cont.measurable
  have hc : Measurable (Dx2.MN.castMt (k := k) (Nat.add_comm 1 ρ)) := (Dx2.MN.castMt_cont _).measurable
  have e1 : (B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ)) =
      ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Prod.map id (B2.levM k ρ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hl, Measure.map_id]
  rw [Dx2.MN.muN_succ, e1, Measure.map_map hmu (measurable_id.prodMap hl), Measure.map_map hc (hmu.comp (measurable_id.prodMap hl))]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasMOfCont
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def MeasM (A : X → Matrix (Fin n) (Fin n) ℂ) : Prop := Measurable fun x => (Matrix.of.symm (A x) : Fin n → Fin n → ℂ)

theorem measM_iff {A : X → Matrix (Fin n) (Fin n) ℂ} : MeasM A ↔ ∀ i j, Measurable fun x => A x i j := by
  simp only [MeasM, measurable_pi_iff]
  exact Iff.rfl

theorem measM_const (C : Matrix (Fin n) (Fin n) ℂ) : MeasM (fun _ : X => C) := measurable_const

theorem measM_of_cont {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {f : Y → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous fun y => (Matrix.of.symm (f y) : Fin n → Fin n → ℂ))
    {g : X → Y} (hg : Measurable g) : MeasM (fun x => f (g x)) := hf.measurable.comp hg

theorem measM_mul {A B : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) (hB : MeasM B) : MeasM (fun x => A x * B x) := by
  rw [measM_iff] at hA hB ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hA i l).mul (hB l j)

theorem measM_star {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)ᴴ) := by
  rw [measM_iff] at hA ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (hA j i)

theorem cont_det : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of M).det :=
  Continuous.matrix_det continuous_id

theorem cont_adj : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of.symm (Matrix.of M).adjugate : Fin n → Fin n → ℂ) :=
  Continuous.matrix_adjugate continuous_id

theorem measM_inv {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)⁻¹) := by
  have hd : Measurable fun x => (A x).det := cont_det.measurable.comp hA
  have hadj : MeasM (fun x => (A x).adjugate) := cont_adj.measurable.comp hA
  rw [measM_iff] at hadj ⊢
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.inv.mul (hadj i j)

variable {k r : ℕ}

theorem measM_nEich (z : Fin (2 * r + k + 1) → ℂ) {ξ : X → Fin r → ℂ} (hξ : Measurable ξ) :
    MeasM (fun x => C2.nEich k r z (ξ x)) := by
  have hxi : Continuous fun ξ : Fin r → ℂ => C2.xiV k r ξ := by
    refine continuous_pi fun i => ?_
    by_cases h : i.val < r
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_const
  have hc : Continuous fun ξ : Fin r → ℂ => (C2.nEich k r z ξ : Matrix _ _ ℂ) := by
    unfold C2.nEich
    have h1 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ z)) :=
      hxi.matrix_vecMulVec continuous_const
    have h2 : Continuous fun ξ : Fin r → ℂ => vecMulVec z (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    have h3 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      hxi.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    fun_prop
  exact measM_of_cont (f := fun ξ => C2.nEich k r z ξ) hc hξ

theorem measM_submatrix_castSucc {A : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : MeasM A) :
    MeasM (fun x => (A x).submatrix Fin.castSucc Fin.castSucc) := by
  rw [measM_iff] at hA ⊢
  intro i j
  exact hA _ _

theorem measM_mX {A : X → Matrix (Fin r) (Fin r) ℂ} (hA : MeasM A) : MeasM (fun x => C2.mX k r (A x)) := by
  have hinv : MeasM fun x => ((A x)ᴴ)⁻¹ := measM_inv (measM_star hA)
  rw [measM_iff] at hA hinv ⊢
  intro i j
  simp only [C2.mX]
  split_ifs
  all_goals first | exact measurable_const | exact hA _ _ | exact hinv _ _

theorem measM_tau (z : Fin (2 * r + k + 1) → ℂ) {v : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : MeasM v) :
    MeasM (fun x => C2.tauM k r z (v x)) := by
  show MeasM fun x => C2.nEich k r z (fun a => v x a.castSucc (Fin.last r)) *
    C2.mX k r ((v x).submatrix Fin.castSucc Fin.castSucc)
  refine measM_mul (measM_nEich z ?_) (measM_mX (measM_submatrix_castSucc hv))
  exact Measurable.of_eval fun a => (measM_iff.1 hv) _ _

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

def GQBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e →
    ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (X.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)

def GQKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    ∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)

def GQSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    (∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1),
      Gauge.GC.Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) ∧
      Gauge.GC.Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l))

def GQQSSFOfCut : Prop := GQBridge → GQKap → GQSS → GQQSSF

theorem gQQSSF_of_cut : GQQSSFOfCut := by
  intro hB hK hS Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg
  have hQ : ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b) := by
    intro Y a b
    rw [← hA.2.2.2.2 (Y : ℂ)]
    exact hB Wp Wq P Bs hk X d hA e he hg Y a b
  have hκ := hK Wp Wq P Bs hk X d hA e he hQ
  intro l hl Φ
  exact ⟨(hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).1 Φ, (hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).2 Φ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

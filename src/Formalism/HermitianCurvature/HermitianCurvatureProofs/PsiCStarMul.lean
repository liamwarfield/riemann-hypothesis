module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlkUUMapMuPRn
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section alg

variable {k r : ℕ}

theorem eI_eB' (a : Fin r) : eI k r a = eB k r 0 (Sum.inl (Sum.inl a)) := by
  ext; rw [Ux3.block_index_first_val]; rfl

theorem blkU_uMap (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    blkU (C2.uMap k r z g) = Matrix.of fun a b => g (eI k r a) (eI k r b) := by
  ext a b
  simp only [blkU, Matrix.submatrix_apply, C2.uMap, Matrix.of_apply]
  rw [dite_eq_left (by simp), fvec_low z b.castSucc (by simp), herm_bvec_esI', mulVec_bvec_apply]
  rfl

theorem muP_Rn_blk (W : Matrix (Fin r) (Fin r) ℂ) (y : U.RC k r 0) (a b : Fin r) :
    (U.muP k r 0 W * U.Rn k r 0 y) (eI k r a) (eI k r b) = W a b := by
  rw [eI_eB', eI_eB', U.muP, Ux3.rn_eq, Ux3.block3_mul, Ux3.block3_apply]
  simp

theorem blkU_uMap_muP_Rn (z : Fin (2 * r + k + 1) → ℂ) (W : Matrix (Fin r) (Fin r) ℂ) (y : U.RC k r 0) :
    blkU (C2.uMap k r z (U.muP k r 0 W * U.Rn k r 0 y)) = W := by
  rw [blkU_uMap]; ext a b; exact muP_Rn_blk W y a b

theorem xiTau_one {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau S (1, 1) p = psi k r S.z cStd (Matrix.of p.1.2) * star (psi k r S.z' cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau psi B.lam
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul]
  push_cast; ring

theorem leviElement_superdiagonal_entry (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (W : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    (if h : a.val + 1 < r then (U.muP k r 0 W) (eI k r a) (eI k r ⟨a.val + 1, h⟩)
      else (U.muP k r 0 W *ᵥ z) (eI k r a)) = (if h : a.val + 1 < r then W a ⟨a.val + 1, h⟩ else 0) := by
  split_ifs with h
  · rw [eI_eB', eI_eB', U.muP, Ux3.block3_apply]; simp
  · rw [eI_eB', mulVec_eB, U.muP]
    simp only [Ux3.block3_apply]
    simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromRows_apply_inl, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hz _ (Or.inl (by rw [Ux3.block_index_first_val]; exact c.isLt)), mul_zero]

theorem psi_muP (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) (W : Matrix (Fin r) (Fin r) ℂ) :
    psi k r z c (U.muP k r 0 W) = C2.psiC c (C2.simpleUp W) := by
  have hell : ell k r z (U.muP k r 0 W) = C2.simpleUp W := by
    unfold ell C2.simpleUp
    exact Finset.sum_congr rfl fun a _ => leviElement_superdiagonal_entry z hz W a
  unfold psi C2.psiC
  rw [hell]

theorem simpleUp_mul {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) (hB : B ∈ C2.UTset m) :
    C2.simpleUp (A * B) = C2.simpleUp A + C2.simpleUp B := by
  unfold C2.simpleUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · set b : Fin m := ⟨a.val + 1, h⟩
    have hab : a ≠ b := by intro e; have := congrArg Fin.val e; simp [b] at this
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
    · rw [hA.2 a, hB.2 b, one_mul, mul_one, add_comm]
    · intro c ⟨hca, hcb⟩
      by_cases hc : c < a
      · rw [hA.1 a c hc, zero_mul]
      · have hc' : b < c := by
          have h1 : a < c := lt_of_le_of_ne (not_lt.1 hc) (Ne.symm hca)
          rw [Fin.lt_def] at h1 ⊢
          have : c.val ≠ a.val + 1 := fun e => hcb (Fin.ext e)
          simp [b]; omega
        rw [hB.1 c b hc', mul_zero]
  · simp

theorem gaXi_zero (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0) :
    U.gaXi k 0 σ d ξ (fun a => a.elim0) γ =
      (U.Rn k r 0 ξ.1.1)⁻¹ * U.mMap k r 0 (U.headH σ d ξ.2.2.1 ξ.2.2.2) γ * U.Rn k r 0 ξ.1.2 := by
  unfold U.gaXi U.ZjH
  rw [Dx2.SL.zj_zero]
  rfl

theorem psiStar_zero (σ : Equiv.Perm (Fin r)) (z z' : Fin (2 * (r + 0 + 0) + k + 1) → ℂ) (ξ : U.Xi k r 0 0 σ) :
    U.psiStar k 0 σ z z' ξ = psi k r z cStd (U.Rn k r 0 ξ.1.1) * star (psi k r z' cStd (U.Rn k r 0 ξ.1.2)) *
      G.psi U.betaU (U.subS (U.wP σ * U.lowW σ ξ.2.2.1 * (U.wP σ)⁻¹) + U.supS (G.upper ξ.2.2.2)) := by
  unfold U.psiStar U.psiH
  simp only [Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero, add_zero]
  rfl

theorem gv_unit {ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ B.GV k ρ) : IsUnit y.det := by
  have := B2x5.normSq_det_GV hy
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, Complex.normSq_zero] at this; exact zero_ne_one this

theorem sgs_formula (z0 z0' : Fin (2 * 0 + k + 1) → ℂ) (h h' : Mt k r)
    (hh : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0)) (hh' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0'))
    (V V' : G.UT r → ℂ) (y y' : U.RC k r 0) (Z : Matrix (Fin r) (Fin r) ℂ) (γ0 : B.Mat k 0) :
    B.sgs ((h, psiR k r (y, V)), (h', psiR k r (y', V'))) (U.mMap k r 0 Z γ0) =
      (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h))⁻¹ y))⁻¹ *
        U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) *
        U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h'))⁻¹ y') := by
  set y1 := midB r 0 (Matrix.of h) with hy1def
  set y1' := midB r 0 (Matrix.of h') with hy1def'
  have hy1 : y1 ∈ UWset k 0 z0 := uw_mid r 0 z0 _ hh
  have hy1' : y1' ∈ UWset k 0 z0' := uw_mid r 0 z0' _ hh'
  have hH : (Matrix.of h : B.Mat k (r + 0)) = U.embG k r 0 y1 := by
    rw [← Dx2.Tower.lev_eq_embG, uw_block r 0 z0 _ hh]
  have hH' : (Matrix.of h' : B.Mat k (r + 0)) = U.embG k r 0 y1' := by
    rw [← Dx2.Tower.lev_eq_embG, uw_block r 0 z0' _ hh']
  have u1 := gv_unit hy1.1
  have uE : IsUnit (U.embG k r 0 y1).det := by
    rw [← Dx2.Tower.lev_eq_embG]; exact gv_unit (Dx2.Tower.lev_GV r 0 y1 hy1.1)
  have uE' : IsUnit (U.embG k r 0 y1').det := by
    rw [← Dx2.Tower.lev_eq_embG]; exact gv_unit (Dx2.Tower.lev_GV r 0 y1' hy1'.1)
  have uV : IsUnit (G.upper V).det := Dx2.SL.isUnit_up V
  have uRn : IsUnit (U.Rn k r 0 y).det := by
    refine Matrix.isUnit_det_of_right_inverse (B := U.Rn k r 0 (-y)) ?_
    exact PBM.rn_mul_neg y

  have hM1 : (U.muP k r 0 (G.upper V))⁻¹ * U.mMap k r 0 Z γ0 * U.muP k r 0 (G.upper V') =
      U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') γ0 := by
    rw [leviElement_inv _ uV, BigCellDiagonalMap.leviElement_mul_mMap _ _ _ ((G.upper V).isUnit_nonsing_inv_det uV), Ux4.mMap_mul_muP,
      Matrix.conjTranspose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_conjTranspose]; exact uV.star)]
  unfold B.sgs
  simp only [psiR, Matrix.of.apply_symm_apply]
  rw [hH, hH']
  set E := U.embG k r 0 y1
  set E' := U.embG k r 0 y1'
  have e1 : (U.Rn k r 0 (rnAct y1⁻¹ y))⁻¹ = E⁻¹ * (U.Rn k r 0 y)⁻¹ * E := by
    rw [← embG_conj_Rn y1 hy1.1 y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ uE,
      Matrix.mul_assoc]
  have e2 : U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') (y1⁻¹ * γ0 * y1') =
      E⁻¹ * U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') γ0 * E' := (embG_conj_mMap y1 y1' u1 _ γ0).symm
  have e3 : U.Rn k r 0 (rnAct y1'⁻¹ y') = E'⁻¹ * U.Rn k r 0 y' * E' := (embG_conj_Rn y1' hy1'.1 y').symm
  rw [e1, e2, e3, ← hM1, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ uE, Matrix.mul_nonsing_inv_cancel_left _ _ uE']

theorem conjS_UT {w0 : Equiv.Perm (Fin r)} {d0 : Fin r → ℂ} (hd0 : ∀ a, d0 a ≠ 0) (x0 : C2.Lstidx w0 → ℂ) :
    (C2.monoP w0 d0)⁻¹ * StabilizerDisintegration.lowS w0 x0 * C2.monoP w0 d0 ∈ C2.UTset r :=
  (Dx2.Rad.low_mem w0 d0 hd0 x0).2

theorem orbit_split {w0 : Equiv.Perm (Fin r)} {d0 : Fin r → ℂ} (hd0 : ∀ a, d0 a ≠ 0) (x0 : C2.Lstidx w0 → ℂ)
    (y2 : C2.LPidx w0 → ℂ) (V' : G.UT r → ℂ) :
    (G.upper (StabilizerDisintegration.UC.fSp w0 (x0, y2)))ᴴ * C2.monoP w0 d0 * G.upper V' =
      StabilizerDisintegration.lowP w0 y2 * C2.monoP w0 d0 *
        G.upper (StabilizerDisintegration.utc ((C2.monoP w0 d0)⁻¹ * StabilizerDisintegration.lowS w0 x0 * C2.monoP w0 d0 * G.upper V')) := by
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w0 d0 hd0
  rw [StabilizerDisintegration.UC.upper_fSp, StabilizerDisintegration.UC.upper_utc (Formalism.FourierDecayAlt.P.C2x2.ut_mul (conjS_UT hd0 x0) (StabilizerDisintegration.UC.upper_mem V')),
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem mMap_mul_mMap {ρ : ℕ} (Z Y : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det) (hY : IsUnit Y.det)
    (γ : B.Mat k ρ) (hγ : IsUnit γ.det) :
    U.mMap k r ρ Zᴴ γ⁻¹ * U.mMap k r ρ Y γ = U.muP k r ρ (Z⁻¹ * Y) := by
  have hZH : IsUnit Zᴴ.det := by rw [Matrix.det_conjTranspose]; exact hZ.star
  have hYH : IsUnit Yᴴ.det := by rw [Matrix.det_conjTranspose]; exact hY.star
  unfold U.mMap U.muP
  rw [Ux3.block3_mul]
  congr 1
  · simp only [Matrix.mul_zero, zero_add, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (G.wMat r), Ux3.wMat_mul_self, Matrix.one_mul]
  all_goals try simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  · exact Matrix.nonsing_inv_mul _ hγ
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hZH]
    simp only [Matrix.mul_assoc]

theorem conj_muP (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det) (γ0 : B.Mat k 0) (hγ0 : IsUnit γ0.det)
    (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : IsUnit Q.det) :
    (U.mMap k r 0 Z γ0)⁻¹ * U.muP k r 0 Q * U.mMap k r 0 Z γ0 = U.muP k r 0 (Z⁻¹ * (Qᴴ)⁻¹ * Z) := by
  have hQH : IsUnit (Qᴴ)⁻¹.det := by
    rw [Matrix.det_nonsing_inv, Matrix.det_conjTranspose]; exact (hQ.star).ringInverse
  rw [mMap_inv Z γ0 hZ hγ0, Matrix.mul_assoc, BigCellDiagonalMap.leviElement_mul_mMap _ _ _ hQ,
    mMap_mul_mMap Z _ hZ (by rw [Matrix.det_mul]; exact hQH.mul hZ) γ0 hγ0, Matrix.mul_assoc]

theorem relevance_U {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det)
    (γ0 : B.Mat k 0) (hγ0 : IsUnit γ0.det) (hrel : C6.IsRelevant S (U.mMap k r 0 Z γ0))
    (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q ∈ C2.UTset r) (hQ' : Z⁻¹ * (Qᴴ)⁻¹ * Z ∈ C2.UTset r) :
    C2.psiC cStd (C2.simpleUp Q) = C2.psiC cStd (C2.simpleUp (Z⁻¹ * (Qᴴ)⁻¹ * Z)) := by
  have uQ : IsUnit Q.det := by rw [StabilizerDisintegration.UC.det_UT hQ]; exact isUnit_one
  have hN : ∀ A : Matrix (Fin r) (Fin r) ℂ, A ∈ C2.UTset r → U.muP k r 0 A ∈ Formalism.QuantumDeterminants.Nset k (r + 0) :=
    fun A hA => BigCellDiagonalMap.leviElement_nset A ⟨fun i j hij => hA.1 i j hij, hA.2⟩
  have hρ : U.muP k r 0 Q ∈ C6.Rset (U.mMap k r 0 Z γ0) := by
    refine ⟨hN Q hQ, ?_⟩
    rw [conj_muP Z hZ γ0 hγ0 Q uQ]; exact hN _ hQ'
  have h := hrel.2 _ hρ
  rw [conj_muP Z hZ γ0 hγ0 Q uQ, psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem] at h
  exact h

end alg

end Formalism.FourierDecayAlt.P.PBM
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdPermThree
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UTransEMp
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section muSS

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def QN (k r : ℕ) : Measure (U.RC k r 0 × (G.UT r → ℂ)) := (U.muRC k r 0).prod volume

instance (k r : ℕ) : SigmaFinite (U.muRC k r 0) := Dx2.SplitF.sf_RC r 0

instance (k r : ℕ) : SFinite (QN k r) := by unfold QN; infer_instance

def TN (k r : ℕ) (p : (Mt k r × (U.RC k r 0 × (G.UT r → ℂ))) × (Mt k r × (U.RC k r 0 × (G.UT r → ℂ)))) :
    B.SS k r :=
  ((p.1.1, psiR k r p.1.2), (p.2.1, psiR k r p.2.2))

theorem TN_meas : Measurable (TN k r) := by
  unfold TN
  exact ((measurable_fst.comp measurable_fst).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_fst))).prodMk
    ((measurable_fst.comp measurable_snd).prodMk ((psiR_meas r).comp (measurable_snd.comp measurable_snd)))

theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) :
    S.μSS = ((S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r))).map (TN k r) := by
  have hW : SigmaFinite S.μW := Dx2.MN.sigma_of_haar S.haarW
  have hW' : SigmaFinite S.μW' := Dx2.MN.sigma_of_haar S.haarW'
  have hN' : S.μN = (QN k r).map (psiR k r) := by rw [hN]; exact muN_rev (k := k) r
  unfold B.RealPlaceData.μSS
  rw [hN', ← Measure.map_id (μ := S.μW), Measure.map_prod_map _ _ measurable_id (psiR_meas r),
    ← Measure.map_id (μ := S.μW'), Measure.map_prod_map _ _ measurable_id (psiR_meas r),
    Measure.map_prod_map _ _ (measurable_id.prodMap (psiR_meas r)) (measurable_id.prodMap (psiR_meas r)),
    Measure.map_id, Measure.map_id]
  rfl

end muSS

section utrans

variable {r : ℕ} {X : Type} [MeasurableSpace X]

theorem ut_of_mem {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : G.upper (StabilizerDisintegration.utc A) = A := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (ne_of_lt h), dite_eq_left h, zero_add]
  · subst h
    rw [if_pos rfl, dite_eq_right (lt_irrefl _), add_zero, hA.2 i]
  · rw [if_neg (ne_of_gt h), dite_eq_right (not_lt.2 h.le), add_zero, hA.1 i j h]

theorem ut_inv_mem {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : A⁻¹ ∈ C2.UTset r := by
  have hT : Matrix.BlockTriangular A id := fun i j hij => hA.1 i j hij
  have hu : IsUnit A.det := by
    rw [Matrix.det_of_upperTriangular hT]
    simp [hA.2]
  haveI := Matrix.invertibleOfIsUnitDet A hu
  have hTi : Matrix.BlockTriangular A⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨fun i j hij => hTi hij, fun i => ?_⟩
  have h1 : (A * A⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [hA.2, one_mul] at h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hTi h, mul_zero]
  · simp

theorem ut_det {A : Matrix (Fin r) (Fin r) ℂ} (hA : A ∈ C2.UTset r) : IsUnit A.det := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hA.1 i j hij)]
  simp [hA.2]

def uTransE (A : X → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r) (hAc : ∀ i j, Measurable fun x => A x i j)
    (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j) :
    (X × (G.UT r → ℂ)) ≃ᵐ (X × (G.UT r → ℂ)) where
  toFun p := (p.1, StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2))
  invFun p := (p.1, StabilizerDisintegration.utc (A p.1 * G.upper p.2))
  left_inv p := by
    ext
    · rfl
    · simp only
      rw [ut_of_mem (C2x2.ut_mul (ut_inv_mem (hA p.1)) (StabilizerDisintegration.UC.upper_mem _)), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (ut_det (hA p.1)), Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  right_inv p := by
    ext
    · rfl
    · simp only
      rw [ut_of_mem (C2x2.ut_mul (hA p.1) (StabilizerDisintegration.UC.upper_mem _)), ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (ut_det (hA p.1)), Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  measurable_toFun := by
    refine measurable_fst.prodMk ?_
    refine Measurable.of_eval fun q => ?_
    simp only [StabilizerDisintegration.utc, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun c _ => Measurable.mul ?_ ?_
    · exact (hAi _ _).comp measurable_fst
    · exact ((StabilizerDisintegration.UC.cont_upper.matrix_elem _ _).measurable).comp measurable_snd
  measurable_invFun := by
    refine measurable_fst.prodMk ?_
    refine Measurable.of_eval fun q => ?_
    simp only [StabilizerDisintegration.utc, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun c _ => Measurable.mul ?_ ?_
    · exact (hAc _ _).comp measurable_fst
    · exact ((StabilizerDisintegration.UC.cont_upper.matrix_elem _ _).measurable).comp measurable_snd

theorem uTransE_mp (A : X → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r) (hAc : ∀ i j, Measurable fun x => A x i j)
    (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j)
    (μ : Measure X) [SFinite μ] :
    MeasurePreserving (uTransE A hA hAc hAi) (μ.prod volume) (μ.prod volume) := by
  have h := MeasurePreserving.skew_product (f := id) (g := fun x u => StabilizerDisintegration.utc ((A x)⁻¹ * G.upper u))
    (MeasurePreserving.id μ) (measurable_snd.comp (uTransE A hA hAc hAi).measurable)
    (Filter.Eventually.of_forall fun x => (StabilizerDisintegration.utLeft r _ (ut_inv_mem (hA x))).map_eq)
  exact h

end utrans

end Formalism.FourierDecayAlt.P.PBM
end
end

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section perms

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa] [SFinite μb] [SFinite μc]
  [SFinite μd]

theorem measurePreserving_prod_perm_one : MeasurePreserving (fun p : α × (β × (γ × δ)) => ((p.1, p.2.2.2), (p.2.2.1, p.2.1)))
    (μa.prod (μb.prod (μc.prod μd))) ((μa.prod μd).prod (μc.prod μb)) := by
  have h1 := (MeasurePreserving.id μa).prod (Measure.measurePreserving_swap (μ := μb) (ν := μc.prod μd))
  have h2 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μc) (ν := μd)).prod (MeasurePreserving.id μb))
  have h3 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μd μc μb)
  have h4 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μd (μc.prod μb))
  exact h4.comp (h3.comp (h2.comp h1))

theorem measurePreserving_prod_perm_two : MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.2.2, p.1.2)))
    ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μd.prod μb)) := by
  have g1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have g2 := (MeasurePreserving.id μa).prod (Measure.measurePreserving_swap (μ := μb) (ν := μc.prod μd))
  have g3 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μd μb)
  have g4 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μd.prod μb))
  exact g4.comp (g3.comp (g2.comp g1))

theorem measurePreserving_prod_perm_three : MeasurePreserving (fun p : α × ((β × γ) × δ) => ((p.2.1.1, p.1), (p.2.1.2, p.2.2)))
    (μa.prod ((μb.prod μc).prod μd)) ((μb.prod μa).prod (μc.prod μd)) := by
  have k1 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd)
  have k2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb (μc.prod μd))
  have k3 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id (μc.prod μd))
  exact k3.comp (k2.comp k1)

end perms

section phi

variable {k r : ℕ} (σ : Equiv.Perm (Fin r)) (y1 y1' : B.Mat k 0)
  (A : (C2.Lstidx σ.symm → ℂ) → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ x, A x ∈ C2.UTset r)
  (hAc : ∀ i j, Measurable fun x => A x i j) (hAi : ∀ i j, Measurable fun x => (A x)⁻¹ i j)

def phiC (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) :=
  ((rnAct y1 p.2.1.1, StabilizerDisintegration.UC.fSp σ.symm (p.1, fun q => p.2.2.2.1 (StabilizerDisintegration.UC.iota σ q))),
   (rnAct y1' p.2.1.2, StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2.2.2.2)))

instance : SFinite (U.muRC k r 0) := inferInstance

instance : SFinite (U.muXiH r 0 σ) := by unfold U.muXiH; infer_instance

include hA hAc hAi in
theorem phiC_mp (hy1 : y1 ∈ B.GV k 0) (hy1' : y1' ∈ B.GV k 0) :
    MeasurePreserving (phiC σ y1 y1' A) ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (U.muXi k r 0 0 σ))
      ((QN k r).prod (QN k r)) := by
  have := Dx2.SL.probT r

  have hin : MeasurePreserving (fun t : U.XiH r 0 σ => (fun q => t.2.1 (StabilizerDisintegration.UC.iota σ q), t.2.2))
      (U.muXiH r 0 σ) ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))) := by
    have h1 := Dx2.SL.dropE_mp ((Fin 0 → Fin r → ℂ) × (Fin r → Fin 0 → ℂ)) ((U.LW σ → ℂ) × (G.UT r → ℂ))
      volume ((volume : Measure (U.LW σ → ℂ)).prod volume)
    have h2 : MeasurePreserving (Prod.map (fun (y : U.LW σ → ℂ) (q : C2.LPidx σ.symm) => y (StabilizerDisintegration.UC.iota σ q)) id)
        ((volume : Measure (U.LW σ → ℂ)).prod (volume : Measure (G.UT r → ℂ)))
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod volume) :=
      (Dx2.SL.reindex_mp (StabilizerDisintegration.UC.iota σ)).prod (MeasurePreserving.id _)
    have := h2.comp h1
    unfold U.muXiH
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod (α := U.LW σ → ℂ)]
    convert this using 1
    funext t
    rfl
  have hA' : MeasurePreserving
      (fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        (p.1, (p.2.1, (fun q => p.2.2.2.1 (StabilizerDisintegration.UC.iota σ q), p.2.2.2.2))))
      ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (U.muXi k r 0 0 σ))
      ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (((U.muRC k r 0).prod (U.muRC k r 0)).prod
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))))) :=
    (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hin)
  have hC := measurePreserving_prod_perm_one (volume : Measure (C2.Lstidx σ.symm → ℂ)) ((U.muRC k r 0).prod (U.muRC k r 0))
    (volume : Measure (C2.LPidx σ.symm → ℂ)) (volume : Measure (G.UT r → ℂ))
  have hD : MeasurePreserving (Prod.map (uTransE A hA hAc hAi) id)
      (((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))).prod
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod ((U.muRC k r 0).prod (U.muRC k r 0))))
      (((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (volume : Measure (G.UT r → ℂ))).prod
        ((volume : Measure (C2.LPidx σ.symm → ℂ)).prod ((U.muRC k r 0).prod (U.muRC k r 0)))) :=
    (uTransE_mp A hA hAc hAi _).prod (MeasurePreserving.id _)
  have hE := measurePreserving_prod_perm_two (volume : Measure (C2.Lstidx σ.symm → ℂ)) (volume : Measure (G.UT r → ℂ))
    (volume : Measure (C2.LPidx σ.symm → ℂ)) ((U.muRC k r 0).prod (U.muRC k r 0))
  have hF : MeasurePreserving
      (Prod.map (StabilizerDisintegration.UC.fSp σ.symm) (Prod.map (Prod.map (rnAct (j := r) y1) (rnAct (j := r) y1')) id))
      (((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (volume : Measure (C2.LPidx σ.symm → ℂ))).prod
        (((U.muRC k r 0).prod (U.muRC k r 0)).prod (volume : Measure (G.UT r → ℂ))))
      ((volume : Measure (G.UT r → ℂ)).prod (((U.muRC k r 0).prod (U.muRC k r 0)).prod
        (volume : Measure (G.UT r → ℂ)))) := by
    refine MeasurePreserving.prod ?_ (((rnAct_mp y1 hy1).prod (rnAct_mp y1' hy1')).prod (MeasurePreserving.id _))
    have := StabilizerDisintegration.UC.fSp_mp σ.symm
    rw [Measure.volume_eq_prod] at this
    exact this
  have hG := measurePreserving_prod_perm_three (volume : Measure (G.UT r → ℂ)) (U.muRC k r 0) (U.muRC k r 0) (volume : Measure (G.UT r → ℂ))
  have := hG.comp (hF.comp (hE.comp (hD.comp (hC.comp hA'))))
  unfold QN
  convert this using 1
  funext p
  rfl

def psiC (q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) :
    (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ :=
  (((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1,
    ((rnAct y1⁻¹ q.1.1, rnAct y1'⁻¹ q.2.1),
      (default, (fun l => ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).2 ((StabilizerDisintegration.UC.iota σ).symm l),
        StabilizerDisintegration.utc (A ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1 * G.upper q.2.2)))))

theorem rnAct_inv_rnAct {a : B.Mat k 0} (ha : IsUnit a.det) (x : U.RC k r 0) : rnAct a⁻¹ (rnAct a x) = x := by
  simp only [rnAct, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
    Equiv.symm_apply_apply]

theorem rnAct_rnAct_inv {a : B.Mat k 0} (ha : IsUnit a.det) (x : U.RC k r 0) : rnAct a (rnAct a⁻¹ x) = x := by
  simp only [rnAct, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
    Equiv.symm_apply_apply]

theorem rnAct_meas (a : B.Mat k 0) : Measurable (rnAct (j := r) a) := by
  have h : (rnAct (j := r) a) = fun x => (Matrix.of.symm (a * Matrix.of x.1), x.2) := by
    funext x
    rfl
  rw [h]
  refine Measurable.prodMk ?_ measurable_snd
  refine Measurable.of_eval (fun i => Measurable.of_eval (fun l => ?_))
  change Measurable fun x : U.RC k r 0 => ∑ m, a i m * x.1 m l
  exact Finset.measurable_sum _ (fun m _ => measurable_const.mul
    ((measurable_pi_apply l).comp ((measurable_pi_apply m).comp measurable_fst)))

include hA in
theorem psiC_phiC (hy1 : IsUnit y1.det) (hy1' : IsUnit y1'.det) :
    Function.LeftInverse (psiC σ y1 y1' A) (phiC σ y1 y1' A) := by
  intro p
  obtain ⟨x0, ⟨⟨a, b⟩, ⟨e, ⟨v, u⟩⟩⟩⟩ := p
  have hM : (A x0)⁻¹ * G.upper u ∈ C2.UTset r :=
    StabilizerDisintegration.HC.UT_mul (ut_inv_mem (hA x0)) (StabilizerDisintegration.HC.upper_mem u)
  have hE : (StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.fSp σ.symm (x0, fun q => v (StabilizerDisintegration.UC.iota σ q))) =
      (x0, fun q => v (StabilizerDisintegration.UC.iota σ q)) := (StabilizerDisintegration.UC.eSp σ.symm).symm_apply_apply _
  have hU : A x0 * G.upper (StabilizerDisintegration.utc ((A x0)⁻¹ * G.upper u)) = G.upper u := by
    rw [ut_of_mem hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_det (hA x0)), Matrix.one_mul]
  simp only [psiC, phiC, hE, rnAct_inv_rnAct hy1, rnAct_inv_rnAct hy1', Equiv.apply_symm_apply, hU,
    StabilizerDisintegration.HC.utc_upper, Prod.mk.injEq, and_true, true_and]
  exact Subsingleton.elim _ _

include hA in
theorem phiC_psiC (hy1 : IsUnit y1.det) (hy1' : IsUnit y1'.det) :
    Function.RightInverse (psiC σ y1 y1' A) (phiC σ y1 y1' A) := by
  intro q
  obtain ⟨⟨x1, w1⟩, ⟨x2, w2⟩⟩ := q
  have hE : StabilizerDisintegration.UC.fSp σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm w1) = w1 := (StabilizerDisintegration.UC.eSp σ.symm).apply_symm_apply w1
  have hM : A ((StabilizerDisintegration.UC.eSp σ.symm).symm w1).1 * G.upper w2 ∈ C2.UTset r :=
    StabilizerDisintegration.HC.UT_mul (hA _) (StabilizerDisintegration.HC.upper_mem w2)
  have hU : (A ((StabilizerDisintegration.UC.eSp σ.symm).symm w1).1)⁻¹ *
      G.upper (StabilizerDisintegration.utc (A ((StabilizerDisintegration.UC.eSp σ.symm).symm w1).1 * G.upper w2)) = G.upper w2 := by
    rw [ut_of_mem hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (ut_det (hA _)), Matrix.one_mul]
  simp only [psiC, phiC, rnAct_rnAct_inv hy1, rnAct_rnAct_inv hy1', Equiv.symm_apply_apply, Prod.mk.eta, hE, hU,
    StabilizerDisintegration.HC.utc_upper]

include hA hAc hAi in
theorem phiC_emb (hy1 : IsUnit y1.det) (hy1' : IsUnit y1'.det) : MeasurableEmbedding (phiC σ y1 y1' A) := by
  have hup : ∀ m j : Fin r, Measurable fun v : G.UT r → ℂ => G.upper v m j := by
    intro m j
    by_cases h : m < j
    · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_pos h]
      exact measurable_const.add (measurable_pi_apply _)
    · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
      exact measurable_const
  have hmφ : Measurable (phiC σ y1 y1' A) := by
    have h1 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ => rnAct y1 p.2.1.1 :=
      (rnAct_meas y1).comp measurable_snd.fst.fst
    have h2 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        StabilizerDisintegration.UC.fSp σ.symm (p.1, fun q => p.2.2.2.1 (StabilizerDisintegration.UC.iota σ q)) :=
      (StabilizerDisintegration.UC.eSp σ.symm).measurable.comp (measurable_fst.prodMk (Measurable.of_eval fun q =>
        (measurable_pi_apply _).comp measurable_snd.snd.snd.fst))
    have h3 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ => rnAct y1' p.2.1.2 :=
      (rnAct_meas y1').comp measurable_snd.fst.snd
    have h4 : Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        StabilizerDisintegration.utc ((A p.1)⁻¹ * G.upper p.2.2.2.2) := by
      refine Measurable.of_eval fun q => ?_
      change Measurable fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ =>
        ∑ m, (A p.1)⁻¹ q.1.1 m * G.upper p.2.2.2.2 m q.1.2
      exact Finset.measurable_sum _ fun m _ => ((hAi _ _).comp measurable_fst).mul
        ((hup m _).comp measurable_snd.snd.snd.snd)
    exact (h1.prodMk h2).prodMk (h3.prodMk h4)
  have hmψ : Measurable (psiC σ y1 y1' A) := by
    have hes : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        (StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2 :=
      (StabilizerDisintegration.UC.eSp σ.symm).symm.measurable.comp measurable_fst.snd
    have g1 := hes.fst
    have g2 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        rnAct y1⁻¹ q.1.1 := (rnAct_meas y1⁻¹).comp measurable_fst.fst
    have g3 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        rnAct y1'⁻¹ q.2.1 := (rnAct_meas y1'⁻¹).comp measurable_snd.fst
    have g5 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        fun l => ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).2 ((StabilizerDisintegration.UC.iota σ).symm l) :=
      Measurable.of_eval fun l => (measurable_pi_apply _).comp hes.snd
    have g6 : Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        StabilizerDisintegration.utc (A ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1 * G.upper q.2.2) := by
      refine Measurable.of_eval fun q' => ?_
      change Measurable fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        ∑ m, A ((StabilizerDisintegration.UC.eSp σ.symm).symm q.1.2).1 q'.1.1 m * G.upper q.2.2 m q'.1.2
      exact Finset.measurable_sum _ fun m _ => ((hAc _ _).comp g1).mul
        ((hup _ _).comp measurable_snd.snd)
    exact g1.prodMk ((g2.prodMk g3).prodMk (measurable_const.prodMk (g5.prodMk g6)))
  let e : ((C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) ≃ᵐ
      ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) :=
    { toFun := phiC σ y1 y1' A
      invFun := psiC σ y1 y1' A
      left_inv := psiC_phiC σ y1 y1' A hA hy1 hy1'
      right_inv := phiC_psiC σ y1 y1' A hA hy1 hy1'
      measurable_toFun := hmφ
      measurable_invFun := hmψ }
  exact e.measurableEmbedding

end phi

end Formalism.FourierDecayAlt.P.PBM
end
end

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section pw

variable {k r : ℕ}

theorem hMat_monoP (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : U.hMat σ d = C2.monoP σ.symm d := by
  ext i a
  simp only [U.hMat, U.wP, C2.monoP, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases h : σ i = a
  · have h' : i = σ.symm a := by rw [← h, Equiv.symm_apply_apply]
    simp [h, h']
  · have h' : ¬ i = σ.symm a := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    simp [h, h']

theorem headH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (v : U.LW σ → ℂ) (u : G.UT r → ℂ) :
    U.headH σ d v u = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) * C2.monoP σ.symm d * G.upper u := by
  have h := StabilizerDisintegration.UC.permutationMatrix_mul_lowerUnipotent (σ := σ) (fun q => v (StabilizerDisintegration.UC.iota σ q))
  simp only [Equiv.apply_symm_apply] at h
  rw [U.headH, h, Matrix.mul_assoc (StabilizerDisintegration.lowP σ.symm _) (U.wP σ), ← U.hMat, hMat_monoP]

theorem psiC_add (c x y : ℂ) : C2.psiC c (x + y) = C2.psiC c x * C2.psiC c y := by
  unfold C2.psiC
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Complex.add_re, Complex.ofReal_add]

theorem psiC_star_mul (c x : ℂ) : C2.psiC c x * star (C2.psiC c x) = 1 := by
  have key : ∀ t : ℝ, Complex.exp (Complex.I * t) * star (Complex.exp (Complex.I * t)) = 1 := by
    intro t
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [show Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 by ring, Complex.exp_zero]
  exact key _

end pw

section pwmain

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def Amat (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (x0 : C2.Lstidx σ.symm → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d

private theorem mul_mem_utset_of_mem {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_ge l i with hl | hl
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hji hl), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl' | hl'
      · rw [hA.1 i l hl', zero_mul]
      · rw [hB.1 l i hl', mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem integrand_pw (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z')
    (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) :
    theta0 S.z σ.symm (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
        (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F
        (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
          (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) =
    chiL σ.symm p.1 • ((S.π (Matrix.of h)).comp
      ((U.psiStar k 0 σ S.z S.z' p.2 • F (U.gaXi k 0 σ d p.2 (fun a => a.elim0)
        ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')))).comp (S.π' (Matrix.of h')⁻¹))) := by
  obtain ⟨x0, ⟨⟨y, y'⟩, ⟨⟨a, b⟩, ⟨v, u⟩⟩⟩⟩ := p
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := hz ▸ hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := hz' ▸ hh'
  have hY := uw_mid r 0 z0 _ hhL
  have hY' := uw_mid r 0 z0' _ hhL'
  have hYu : IsUnit (midB r 0 (Matrix.of h)).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY.1
  have hY'u : IsUnit (midB r 0 (Matrix.of h')).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY'.1
  have hAm : Amat σ d x0 ∈ C2.UTset r := conjS_UT hd x0
  have hAmi : (Amat σ d x0)⁻¹ ∈ C2.UTset r := ut_inv_mem hAm
  have hup : G.upper u ∈ C2.UTset r := StabilizerDisintegration.UC.upper_mem u
  have hprod : (Amat σ d x0)⁻¹ * G.upper u ∈ C2.UTset r := mul_mem_utset_of_mem hAmi hup
  have hV' : G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = (Amat σ d x0)⁻¹ * G.upper u := ut_of_mem hprod
  have hAmu : IsUnit (Amat σ d x0).det := ut_det hAm
  have hZu : IsUnit (U.hMat σ d).det := by
    rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact (Formalism.FourierDecayAlt.P.Dx2.SL.isUnit_wP σ).mul
      (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hd a))
  have hγ0u : IsUnit γ0.det := gv_unit hγ0
  have hmat : (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))))ᴴ * U.hMat σ d * G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = U.headH σ d v u := by
    rw [hMat_monoP, orbit_split hd, headH_eq, hV']
    show _ * _ * G.upper (StabilizerDisintegration.utc (Amat σ d x0 * ((Amat σ d x0)⁻¹ * G.upper u))) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAmu, Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  have hsgs : B.sgs ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) (U.mMap k r 0 (U.hMat σ d) γ0) =
      U.gaXi k 0 σ d ((y, y'), ((a, b), (v, u))) (fun a => a.elim0) ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) := by
    rw [sgs_formula z0 z0' h h' hhL hhL', rnAct_inv_rnAct hYu, rnAct_inv_rnAct hY'u, hmat, gaXi_zero]
  have hθ : theta0 S.z σ.symm ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = chiL σ.symm x0 := by
    simp only [theta0, psiR, Equiv.apply_symm_apply, blkU_uMap_muP_Rn, x0c, StabilizerDisintegration.UC.utc_upper]
    show chiL σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.eSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))).1 = chiL σ.symm x0
    rw [MeasurableEquiv.symm_apply_apply]
  have hUU : ∀ w : G.UT r → ℂ, Formalism.DoubleCosetMeasures.IsUpUni (G.upper w) := fun w =>
    ⟨fun i j hij => (StabilizerDisintegration.UC.upper_mem w).1 i j hij, (StabilizerDisintegration.UC.upper_mem w).2⟩
  have hr1 : psi k r S.z cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h)) y)) = psi k r S.z cStd (U.Rn k r 0 y) := by
    have e := psi_rnAct z0 cStd _ hY (rnAct (midB r 0 (Matrix.of h)) y)
    rw [rnAct_inv_rnAct hYu] at e
    rw [hz]
    exact e.symm
  have hr2 : psi k r S.z' cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h')) y')) = psi k r S.z' cStd (U.Rn k r 0 y') := by
    have e := psi_rnAct z0' cStd _ hY' (rnAct (midB r 0 (Matrix.of h')) y')
    rw [rnAct_inv_rnAct hY'u] at e
    rw [hz']
    exact e.symm
  have hs1 : C2.simpleUp (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))) = C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ +
      C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ := by
    rw [StabilizerDisintegration.UC.upper_fSp]
    exact simpleUp_mul (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1)
      (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowerUnipotent_mem σ.symm _).1)
  have hs2 : C2.simpleUp (G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) = C2.simpleUp (Amat σ d x0)⁻¹ + C2.simpleUp (G.upper u) := by
    rw [hV']
    exact simpleUp_mul hAmi hup
  have hMu : IsUnit (C2.monoP σ.symm d).det := hMat_monoP σ d ▸ hZu
  have hinv : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d = (Amat σ d x0)⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose, hMat_monoP]
    show _ = ((C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    simp only [Matrix.mul_assoc]
  have hrelU : C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ) =
      C2.psiC cStd (C2.simpleUp (Amat σ d x0)⁻¹) := by
    have hQ : (StabilizerDisintegration.lowS σ.symm x0)ᴴ ∈ C2.UTset r := StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1
    have hQ' : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d ∈ C2.UTset r := by
      rw [hinv]
      exact hAmi
    rw [relevance_U S (U.hMat σ d) hZu γ0 hγ0u hrel _ hQ hQ', hinv]
  have hw : U.wP σ * U.lowW σ v * (U.wP σ)⁻¹ = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) := by
    have e := StabilizerDisintegration.UC.conj_lowW σ (fun q => v (StabilizerDisintegration.UC.iota σ q))
    simp only [Equiv.apply_symm_apply] at e
    exact e
  have hright : G.psi U.betaU (U.subS (U.wP σ * U.lowW σ v * (U.wP σ)⁻¹) + U.supS (G.upper u)) =
      C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) := by
    rw [StabilizerDisintegration.UC.psi_conj, map_add (f := _), psiC_add, hw, ← StabilizerDisintegration.UC.subS_eq, ← StabilizerDisintegration.UC.psi_conj,
      StabilizerDisintegration.UC.psi_star, StabilizerDisintegration.UC.supS_eq]
  have hstar := psiC_star_mul cStd (C2.simpleUp (Amat σ d x0)⁻¹)
  have hxi : B.xiTau S (1, 1) ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = U.psiStar k 0 σ S.z S.z' ((y, y'), ((a, b), (v, u))) := by
    rw [xiTau_one, psiStar_zero]
    simp only [psiR, Equiv.apply_symm_apply]
    rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z S.z_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z' S.z'_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem, hr1, hr2, hs1, hs2, psiC_add, psiC_add, hrelU, hright,
      star_mul', star_mul']
    linear_combination (C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) *
      psi k r S.z cStd (U.Rn k r 0 y) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) *
      star (psi k r S.z' cStd (U.Rn k r 0 y'))) * hstar
  have hphi : phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) (x0, ((y, y'), ((a, b), (v, u)))) =
      ((rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))), (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) := rfl
  rw [hphi]
  dsimp only
  rw [show TN k r ((h, (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) from rfl,
    D.orbIntegrand, B.rho]
  dsimp only
  rw [hθ, hxi, hsgs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end pwmain

end Formalism.FourierDecayAlt.P.PBM

module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LeadingMinorSecondProj
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ph_inverse (φ : E →+* F) {x : E} (hx : IsUnit x) : φ (Ring.inverse x) = (φ x)⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  rw [Ring.inverse_unit, map_units_inv]

private theorem ph1_ph2_ZZm_apply (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (ZZm g Zh T T' a b) = (g.q : F)⁻¹ * ph1 g (Zh a b) ∧
      ph2 g (ZZm g Zh T T' a b) = -(g.q : F)⁻¹ * ph2 g (Zh b a) := by
  have hZ : ZZm g Zh T T' a b = g.e.symm ((g.e (Zh a b)).1 / (g.q : F), -((g.e (Zh b a)).2 / (g.q : F))) := by
    unfold ZZm cor
    simp only [HermSp.ZZplusOf, hs, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> simp
  have h1 : ∀ x : E, ph1 g x = (g.e x).1 := fun x => rfl
  have h2 : ∀ x : E, ph2 g x = (g.e x).2 := fun x => rfl
  rw [hZ, h1, h2, h1, h2, AlgEquiv.apply_symm_apply]
  constructor
  · simp only
    ring
  · simp only
    ring

theorem leadingMinor_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph1 g ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc).det =
      ((g.q : F)⁻¹) ^ r * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [RingHom.map_det, RingHom.map_det]
  have hmat : (ph1 g).mapMatrix ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc) =
      (g.q : F)⁻¹ • (ph1 g).mapMatrix (Zh.submatrix Fin.castSucc Fin.castSucc) := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      (ph1_ph2_ZZm_apply hs Zh T T' _ _).1]
  rw [hmat, Matrix.det_smul, Fintype.card_fin]

private theorem ph2_mapMatrix_ZZm_submatrix_eq_smul_transpose (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ph2 g).mapMatrix ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc) =
      (-(g.q : F)⁻¹) • Matrix.transpose ((ph2 g).mapMatrix (Zh.submatrix Fin.castSucc Fin.castSucc)) :=
  Matrix.ext fun a b => (ph1_ph2_ZZm_apply hs Zh T T' _ _).2

theorem leadingMinor_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph2 g ((ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc).det =
      (-(g.q : F)⁻¹) ^ r * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [RingHom.map_det, RingHom.map_det, ph2_mapMatrix_ZZm_submatrix_eq_smul_transpose hs Zh T T', Matrix.det_smul, Fintype.card_fin,
    Matrix.det_transpose]

theorem det_firstProj_zzMinus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph1 g (ZZm g Zh T T').det = ((g.q : F)⁻¹) ^ (r + 1) * ph1 g Zh.det := by
  rw [RingHom.map_det, RingHom.map_det]
  have hmat : (ph1 g).mapMatrix (ZZm g Zh T T') = (g.q : F)⁻¹ • (ph1 g).mapMatrix Zh := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      (ph1_ph2_ZZm_apply hs Zh T T' _ _).1]
  rw [hmat, Matrix.det_smul, Fintype.card_fin]

private theorem ph2_mapMatrix_ZZm_eq_smul_transpose (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ph2 g).mapMatrix (ZZm g Zh T T') = (-(g.q : F)⁻¹) • Matrix.transpose ((ph2 g).mapMatrix Zh) :=
  Matrix.ext fun a b => (ph1_ph2_ZZm_apply hs Zh T T' a b).2

theorem det_secondProj_zzMinus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    ph2 g (ZZm g Zh T T').det = (-(g.q : F)⁻¹) ^ (r + 1) * ph2 g Zh.det := by
  rw [RingHom.map_det, RingHom.map_det, ph2_mapMatrix_ZZm_eq_smul_transpose hs Zh T T', Matrix.det_smul, Fintype.card_fin,
    Matrix.det_transpose]

private theorem map_kapR_eq_inv_det_mul_det_submatrix (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (φ : E →+* F) (hu : IsUnit Zm.det) :
    φ (kapR Zm) = (φ Zm.det)⁻¹ * φ (Zm.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold kapR
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, ph_inverse φ hu,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hpow : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hpow, one_mul, Fin.succAbove_last]

private theorem isUnit_det_ZZm_of_isUnit_det (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) : IsUnit (ZZm g Zh T T').det := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have h1 : ph1 g Zh.det ≠ 0 := (hu.map (ph1 g)).ne_zero
  have h2 : ph2 g Zh.det ≠ 0 := (hu.map (ph2 g)).ne_zero
  rw [← MulEquiv.isUnit_map g.e.toMulEquiv, Prod.isUnit_iff]
  constructor
  · show IsUnit (ph1 g (ZZm g Zh T T').det)
    rw [det_firstProj_zzMinus hs Zh T T']
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq)) h1)
  · show IsUnit (ph2 g (ZZm g Zh T T').det)
    rw [det_secondProj_zzMinus hs Zh T T']
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq))) h2)

theorem cornerRatio_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) :
    ph1 g (kapR (ZZm g Zh T T')) = (g.q : F) * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det /
      ph1 g Zh.det := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have h1 : ph1 g Zh.det ≠ 0 := (hu.map (ph1 g)).ne_zero
  rw [map_kapR_eq_inv_det_mul_det_submatrix _ _ (isUnit_det_ZZm_of_isUnit_det hs Zh T T' hu), det_firstProj_zzMinus hs Zh T T', leadingMinor_firstProj hs Zh T T', mul_inv, inv_pow,
    inv_inv, inv_pow, pow_succ]
  field_simp

theorem cornerRatio_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) :
    ph2 g (kapR (ZZm g Zh T T')) = -((g.q : F) * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det /
      ph2 g Zh.det) := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have h2 : ph2 g Zh.det ≠ 0 := (hu.map (ph2 g)).ne_zero
  have hc : (-(g.q : F)⁻¹) ≠ 0 := neg_ne_zero.2 (inv_ne_zero hq)
  have hcq : (-(g.q : F)⁻¹)⁻¹ = -(g.q : F) := by rw [inv_neg, inv_inv]
  rw [map_kapR_eq_inv_det_mul_det_submatrix _ _ (isUnit_det_ZZm_of_isUnit_det hs Zh T T' hu), det_secondProj_zzMinus hs Zh T T', leadingMinor_secondProj hs Zh T T', pow_succ, mul_inv,
    mul_inv, hcq]
  have hcr : (-(g.q : F)⁻¹) ^ r ≠ 0 := pow_ne_zero _ hc
  generalize (-(g.q : F)⁻¹) ^ r = C at hcr ⊢
  field_simp

theorem laG_llMap (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : M.Mat (r + 1)) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det)
    (TT : M.R) (m : Fin (r + 1) → M.R) :
    laG (ZZm g Zh T T') (llMap hs Z TT m) =
      (m (Fin.last r) : E) * (1 - tau0 g T T' * kapR (ZZm g Zh T T')) -
        (TT : E) * algebraMap F E (trO hs (m (Fin.last r))) * kapR (ZZm g Zh T T') := by
  have hl : ∀ v w : Fin (r + 1) → M.R, laG (ZZm g Zh T T') (v - w) =
      laG (ZZm g Zh T T') v - laG (ZZm g Zh T T') w := by
    intro v w
    unfold laG
    rw [show (fun i => ((v - w) i : E)) = (fun i => (v i : E)) - (fun i => (w i : E)) by
      funext i; simp, Matrix.mulVec_sub]
    rfl
  have hsm : ∀ (c : M.R) (v : Fin (r + 1) → M.R), laG (ZZm g Zh T T') (c • v) =
      (c : E) * laG (ZZm g Zh T T') v := by
    intro c v
    unfold laG
    rw [show (fun i => ((c • v) i : E)) = (c : E) • (fun i => (v i : E)) by
      funext i; simp, Matrix.mulVec_smul]
    rfl
  show laG _ (Z.Z.mulVec m - (TT * dgR hs (trO hs (m (Fin.last r)))) • eV r) = _
  rw [hl, hsm, laG_mulVec Zh T T' Z hZ (unit_zzm hs Zh T T' hu), laG_e]
  rw [Subring.coe_mul, dgR_coe]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.FirstQuotientEqZeroIff
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem mem_headCols_iff (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (l : Fin (r + 1) → M.R) :
    l ∈ headCols Z ↔ ∃ w : Fin (r + 1) → M.R, w (Fin.last r) = 0 ∧ Z.mulVec w = l := by
  constructor
  · intro hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨Pi.single a.castSucc 1, by simp [(Fin.castSucc_lt_last a).ne], ?_⟩
      rw [← col_eq_mulVec]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', by simp [hw, hw'], Matrix.mulVec_add _ _ _⟩
    | smul s x _ hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨s • w, by simp [hw], Matrix.mulVec_smul _ _ _⟩
  · rintro ⟨w, hw, rfl⟩
    exact mulVec_mem_headCols _ _ hw

theorem llMap_of_last (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (w : Fin (r + 1) → M.R)
    (hw : w (Fin.last r) = 0) : llMap hs Z TT w = Z.Z.mulVec w := by
  show Z.Z.mulVec w - (TT * dgR hs (trO hs (w (Fin.last r)))) • eV r = _
  rw [hw, map_zero, map_zero, mul_zero, zero_smul, sub_zero]

theorem headCols_le_LL (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) {l : Fin (r + 1) → M.R}
    (hl : l ∈ headCols Z.Z) : l ∈ LL hs Z TT := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z.Z l).1 hl
  exact ⟨w, llMap_of_last hs Z TT w hw⟩

theorem firstQuotient_eq_zero_iff (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (l : Fin (r + 1) → M.R) :
    mk1 hs Z TT l = 0 ↔ ∃ m, llMap hs Z TT m = l := by
  rw [mk1, QuotientAddGroup.eq_zero_iff]
  rfl

theorem ker_fact (hs : M.split = some g) (T T' : F) (TT : M.R) (hTT : g.e (TT : E) = (T, T'))
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det)
    (hG : IsUnit (Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)))
    (l : Fin (r + 1) → M.R) (h1 : mk1 hs Z TT l = 0) (h2 : laG (ZZm g Zh T T') l = 0) :
    l ∈ headCols Z.Z := by
  obtain ⟨m, rfl⟩ := (firstQuotient_eq_zero_iff hs Z TT l).1 h1
  rw [laG_llMap hs Zh T T' Z hZ hu] at h2
  have hq := q_ne g
  have hd1 := ((isUnit_iff_ph (g := g) _).1 hu).1
  have hd2 := ((isUnit_iff_ph (g := g) _).1 hu).2
  have hG1 := ((isUnit_iff_ph (g := g) _).1 hG).1
  have ecj : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    rw [firstProj_apply, secondProj_apply, g.e_cj]; rfl
  have eal1 : ∀ c : F, ph1 g (algebraMap F E c) = c := fun c => by rw [firstProj_apply, AlgEquiv.commutes]; rfl
  have eal2 : ∀ c : F, ph2 g (algebraMap F E c) = c := fun c => by rw [secondProj_apply, AlgEquiv.commutes]; rfl
  have et1 : ph1 g (tau0 g T T') = -T / (g.q : F) := by simp [firstProj_apply]
  have et2 : ph2 g (tau0 g T T') = T' / (g.q : F) := by simp [secondProj_apply]
  have eT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have eT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  set a := ph1 g ((m (Fin.last r) : M.R) : E) with ha
  set b := ph2 g ((m (Fin.last r) : M.R) : E) with hb
  have etr : ((trO hs (m (Fin.last r)) : 𝒪[F]) : F) = (a - b) / (g.q : F) := by rw [trO_coe]; rfl
  have H1 := congrArg (ph1 g) h2
  have H2 := congrArg (ph2 g) h2
  simp only [map_sub, map_mul, map_one, map_zero, eal1, eal2, et1, et2, eT1, eT2, etr,
    cornerRatio_firstProj hs Zh T T' hu, cornerRatio_secondProj hs Zh T T' hu] at H1 H2
  rw [← ha] at H1
  rw [← hb] at H2
  have E1 : a * ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * b = 0 := by
    field_simp [hd1, hq] at H1
    linear_combination H1
  have E2 : b * ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * a = 0 := by
    field_simp [hd2, hq] at H2
    linear_combination H2
  have hG1' : ph1 g Zh.det * ph2 g Zh.det - T * T' * (ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det *
      ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0 := by
    simpa [map_sub, map_mul, ecj, eal1] using hG1
  have ha0 : a = 0 := by
    have : a * (ph1 g Zh.det * ph2 g Zh.det - T * T' * (ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det *
        ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det)) = 0 := by
      linear_combination ph2 g Zh.det * E1 - T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * E2
    exact (mul_eq_zero.1 this).resolve_right hG1'
  have hb0 : b = 0 := by
    rw [ha0, mul_zero, add_zero] at E2
    exact (mul_eq_zero.1 E2).resolve_right hd2
  have hm : m (Fin.last r) = 0 := by
    apply Subtype.ext
    apply g.e.injective
    rw [ZeroMemClass.coe_zero, map_zero]
    exact Prod.ext ha0 hb0
  rw [llMap_of_last hs Z TT m hm]
  exact mulVec_mem_headCols _ _ hm

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzplusDetUnit
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SplitIsoCountOfComponents
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def StepZsig0 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g → ∀ (r : ℕ) (T T' : F), T ∈ 𝒪[F] →
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
      Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' → IsUnit Zh.det →
      (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
      (∃ TT : M.R, g.e (TT : E) = (T, T')) ∧ IsUnit (Z.map M.R.subtype).det ∧
      ∃ Zσ : M.Mat (r + 1), Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T'

def SplitIsometryCountIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), T ∈ 𝒪[F] → (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    (Zh₁.submatrix Fin.castSucc Fin.castSucc).det = 0 → (Zh₂.submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

theorem splitIsoCount_of_components (hZ : StepZsig0) (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : SplitIsometryCountIntegral := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT huv hc Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ s₁ s₂
  obtain ⟨⟨TT, hTT⟩, hZ₁, Zσ₁, hσ₁⟩ := hZ F E M g hs r T T' hT huv hc Zh₁ Z₁ e₁ u₁ s₁
  obtain ⟨_, hZ₂, Zσ₂, hσ₂⟩ := hZ F E M g hs r T T' hT huv hc Zh₂ Z₂ e₂ u₂ s₂
  let W₁ : M.Mat (r + 1) := ⟨Z₁, hZ₁⟩
  let W₂ : M.Mat (r + 1) := ⟨Z₂, hZ₂⟩
  have gh : ∀ {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {W Wσ : M.Mat (r + 1)},
      W.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' →
      Wσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' →
      IsUnit Zh.det → (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
      GHyp M g T T' TT Zh W Wσ := by
    intro Zh W Wσ hW hWσ hu hz
    refine ⟨huv, hc, hTT, hW, hWσ, hu, ?_⟩
    rw [hz, map_zero, zero_mul, mul_zero, sub_zero]
    exact hu.mul (hu.map M.L.cj)
  have G₁ : GHyp M g T T' TT Zh₁ W₁ Zσ₁ := gh e₁ hσ₁ u₁ s₁
  have G₂ : GHyp M g T T' TT Zh₂ W₂ Zσ₂ := gh e₂ hσ₂ u₂ s₂
  have K : KapEq Zh₁ Zh₂ := by
    unfold KapEq
    rw [s₁, s₂, mul_zero, mul_zero]
  have Gσ₁ := gHyp_cj G₁
  have Gσ₂ := gHyp_cj G₂
  have Kσ := kapEq_cj (M := M) K
  rw [h0 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K]
  refine Nat.card_eq_of_bijective
    (fun p => (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.2.1 p.2.2.2.1).choose)
    ⟨?_, ?_⟩
  · intro p p' hpp
    have i1 := (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.2.1 p.2.2.2.1).choose_spec
    have i2 := (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p'.1.1 p'.2.1 p'.2.2.2.1).choose_spec
    simp only at hpp
    rw [hpp] at i1
    have q1 : p.1.1 = p'.1.1 := ind_det hs _ _ _ i1 i2
    have hb := p'.2.2.2.2.2
    rw [← q1] at hb
    have q2 : p.1.2 = p'.1.2 :=
      h5 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.1.2 p'.1.2 p.2.2.2.2.2 hb
    exact Subtype.ext (Prod.ext q1 q2)
  · intro γ
    obtain ⟨θ₁, o₁, m₁, i₁⟩ := h2 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K γ
    obtain ⟨γ', hγ'⟩ := h4 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K γ
    obtain ⟨θ₂, o₂, m₂, i₂⟩ := h2 F E M g hs r T T' TT (Zh₁.map M.L.cj) (Zh₂.map M.L.cj)
      Zσ₁ Zσ₂ W₁ W₂ Gσ₁ Gσ₂ Kσ γ'
    refine ⟨⟨(θ₁, θ₂), o₁, o₂, m₁, m₂, hγ' θ₁ θ₂ i₁ i₂⟩, ?_⟩
    exact h3 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K θ₁ _ γ
      (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K θ₁ o₁ m₁).choose_spec i₁

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem zzplus_det_unit (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) (h0 : (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0) :
    IsUnit (HermSp.ZZplusOf M Zh T T').det := by
  have hne : ∀ i : Fin r, (Fin.castSucc i = Fin.last r) = False := fun i => eq_false (Fin.castSucc_ne_last i)
  have h1 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map (ph1 g) =
      ((g.q : F)⁻¹) • (Zh.submatrix Fin.castSucc Fin.castSucc).map (ph1 g) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, firstProj_apply, zz_comp hs,
      hne, false_and, if_false, sub_zero]
    rw [div_eq_inv_mul]
  have h2 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map (ph2 g) =
      (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map (ph2 g)).transpose := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      secondProj_apply, zz_comp hs, hne, false_and, if_false, sub_zero]
    rw [div_eq_inv_mul, neg_mul]
  have hS1 : ph1 g ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [det_ph, h1, Matrix.det_smul, ← det_ph, h0, map_zero, mul_zero]
  have hS2 : ph2 g ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [det_ph, h2, Matrix.det_smul, Matrix.det_transpose, ← det_ph, h0, map_zero, mul_zero]
  have hS : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    apply g.e.injective
    rw [map_zero]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_zero, ← firstProj_apply]
      exact hS1
    · rw [Prod.snd_zero, ← secondProj_apply]
      exact hS2
  have hm : (ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc =
      (HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp only [ZZm, Matrix.submatrix_apply, Matrix.add_apply, Matrix.of_apply, cor, hne, false_and, if_false,
      add_zero]
  have key : HermSp.ZZplusOf M Zh T T' = ZZm g Zh T T' +
      Matrix.of fun a b => cor r a b (-(g.e.symm (-T / (g.q : F), T' / (g.q : F)))) := by
    ext a b
    simp only [ZZm, Matrix.add_apply, Matrix.of_apply, cor]
    split_ifs <;> ring
  rw [key, det_add_cor, hm, hS, mul_zero, add_zero]
  exact unit_zzm hs Zh T T' hu

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

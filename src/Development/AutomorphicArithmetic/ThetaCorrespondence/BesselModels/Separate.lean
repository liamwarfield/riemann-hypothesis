module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualCoefSpaceIsTensorOverRealPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopSeparation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainCompositesExistLiftCombinations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteTopSpaceColumnValues
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SepGap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HyperbolicFrameCongruentSplitHermGram
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsometryConjMapsUnipotentRadical
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IrreducibleUnitaryRepIsoHarishChandraType

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.RankLeOneOfDep
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SylvesterInertiaSignFormCongrSplitHermitian
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.Inertia

theorem card_plus_of_congr_Hpk : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool)
    {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r),
    (Finset.univ.filter fun i => ε i = true).card = m + r := by
  intro m r ε Q Qi h1 h2 hg
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  have hc : Formalism.MainNotions.S.IsCayley m r ε Q := ⟨hu, hg⟩
  exact (ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA.cayley_signature' hc).1

end UpperTheory.Lit.Bur.Inertia

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool) {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r), (Finset.univ.filter fun i => ε i = true).card = m + r := by
  first | exact @UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | exact UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | (intros; apply UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SmoothVecStableUnderUnitaryGroup
noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SmoothTranslate

theorem conj_mem_lieG {n : ℕ} {J g X : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g) (hg : g ∈ Formalism.QuantumDeterminants.UH J)
    (hX : X ∈ lieG J) : g⁻¹ * X * g ∈ lieG J := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hAB : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hd
  have hBA : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hBA' : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  have h : gᴴ * J * g = J := hg
  have hX' : Xᴴ * J + J * X = 0 := hX
  show (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g)
      = (g⁻¹ * X * g)ᴴ * (gᴴ * J * g) + (gᴴ * J * g) * (g⁻¹ * X * g) := by rw [h]
    _ = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * gᴴ) * J + J * (g * g⁻¹) * X) * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem mul_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

theorem smoothVec_translate : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H}
    (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  intro n H _ _ J hJ σ hσ g hg v hv k Xs hXs
  have hu : IsUnit g := isUnit_of_mem_UH hJ hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieG J := fun i => conj_mem_lieG hu hg (hXs i)
  have hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := fun X t => by
    rw [← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := ((σ g).restrictScalars ℝ).contDiff.comp (hv k _ hY)
  convert h1 using 2 with t
  show σ _ (σ g v) = σ g (σ _ v)
  have hP := expProd_mem_UH hJ hXs t
  have hQ := expProd_mem_UH hJ hY t
  have e1 := hσ.1.2 _ hP _ hg
  have e2 := hσ.1.2 _ hg _ hQ
  have e3 : g * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← mul_prod_conj hu, List.map_ofFn]
    simp only [hc, Function.comp_def]
  have e4 := e1.symm.trans ((congrArg σ e3).symm.trans e2)
  exact congrArg (fun T : H →L[ℂ] H => T v) e4

end UpperTheory.Lit.Bur.SmoothTranslate

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H} (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  first | exact @UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate | exact UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate | (intros; apply UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsFrameExistsIsotropicDualColumns
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.DualCols


open scoped ComplexOrder in
theorem exists_right_inv {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hJ : IsUnit J) (he : LinearIndependent ℂ eᵀ) : ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 := by
  have hr : eᵀ.rank = r := by simpa using LinearIndependent.rank_matrix (M := eᵀ) he
  have hr2 : (eᴴ * J).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det J).1 hJ),
      Matrix.rank_conjTranspose, ← Matrix.rank_transpose, hr]
  have hs : Function.Surjective (eᴴ * J).mulVec := by
    have h : LinearMap.range (eᴴ * J).mulVecLin = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank] using hr2)
    exact LinearMap.range_eq_top.1 h
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs

theorem adj {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) {α β : Type} [Fintype α] [Fintype β]
    (X : Matrix (Fin n) α ℂ) (Y : Matrix (Fin n) β ℂ) : (Xᴴ * J * Y)ᴴ = Yᴴ * J * X := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]

theorem core {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e f' : Matrix (Fin n) (Fin r) ℂ} {Z : Matrix (Fin n) Unit ℂ} {c : ℂ}
    (hJ : Jᴴ = J) (hd : IsUnit J₀.det) (hc : c ≠ 0) (hFF : Fᴴ * J * F = J₀) (hFe : Fᴴ * J * e = 0)
    (hFZ : Fᴴ * J * Z = 0) (hee : eᴴ * J * e = 0) (heZ : eᴴ * J * Z = 0) (hZZ : Zᴴ * J * Z = c • 1)
    (hf' : eᴴ * J * f' = 1) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ Zᴴ * J * f = 0 := by
  have heF : eᴴ * J * F = 0 := by rw [← adj hJ F e, hFe, conjTranspose_zero]
  have hZF : Zᴴ * J * F = 0 := by rw [← adj hJ F Z, hFZ, conjTranspose_zero]
  have hZe : Zᴴ * J * e = 0 := by rw [← adj hJ e Z, heZ, conjTranspose_zero]
  obtain ⟨P, hP⟩ : ∃ P, J₀ * P = Fᴴ * J * f' :=
    ⟨J₀⁻¹ * (Fᴴ * J * f'), by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Zᴴ * J * Z * Q = Zᴴ * J * f' :=
    ⟨c⁻¹ • (Zᴴ * J * f'), by rw [hZZ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨f₂, h₂⟩ : ∃ f₂, f₂ = f' - F * P - Z * Q := ⟨_, rfl⟩
  have hF₂ : Fᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hFF, hFZ, hP,
      Matrix.zero_mul, sub_self, sub_zero]
  have hZ₂ : Zᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hZF, hQ,
      Matrix.zero_mul, sub_zero, sub_self]
  have he₂ : eᴴ * J * f₂ = 1 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, heF, heZ, hf',
      Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have he₂' : f₂ᴴ * J * e = 1 := by rw [← adj hJ e f₂, he₂, conjTranspose_one]
  obtain ⟨H, hH, hHH⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ, Hᴴ = H ∧ H + H = f₂ᴴ * J * f₂ := by
    refine ⟨(1 / 2 : ℝ) • (f₂ᴴ * J * f₂), ?_, ?_⟩
    · rw [conjTranspose_smul, adj hJ f₂ f₂]; simp
    · rw [← add_smul]; norm_num
  have hfH : (f₂ - e * H)ᴴ = f₂ᴴ - H * eᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, hH]
  refine ⟨f₂ - e * H, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hee, he₂, Matrix.zero_mul, sub_zero]
  · have h1 : (f₂ᴴ - H * eᴴ) * J * f₂ = f₂ᴴ * J * f₂ - H := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc H, Matrix.mul_assoc H, he₂,
        Matrix.mul_one]
    have h2 : (f₂ᴴ - H * eᴴ) * J * e = 1 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, he₂', Matrix.mul_assoc H, Matrix.mul_assoc H, hee,
        Matrix.mul_zero, sub_zero]
    rw [hfH, Matrix.mul_sub, ← Matrix.mul_assoc _ e, h1, h2, Matrix.one_mul, ← hHH]
    abel
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hFe, hF₂, Matrix.zero_mul, sub_zero]
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hZe, hZ₂, Matrix.zero_mul, sub_zero]

theorem exists_dual_cols {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  obtain ⟨f', hf'⟩ := exists_right_inv hf.unit hf.e_indep
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) Unit ℂ, Z = Matrix.of fun i _ => z i := ⟨_, rfl⟩
  have hcol : ∀ {a : Type} (M : Matrix a (Fin n) ℂ) (i : a) (u : Unit), (M * Z) i u = (M *ᵥ z) i := by
    intro a M i u
    subst hZ
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hFZ : Fᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpF]
    rfl
  have heZ : eᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpE]
    rfl
  have hZZ : Zᴴ * J * Z = (Formalism.QuantumDeterminants.herm J z z) • (1 : Matrix Unit Unit ℂ) := by
    ext u v
    subst hZ
    simp [Formalism.QuantumDeterminants.herm, Matrix.mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨f, h1, h2, h3, h4⟩ := core hf.herm ((Matrix.isUnit_iff_isUnit_det J₀).1 hf.unit₀) hf.z_ne hf.gram
    hf.e_perp hFZ hf.e_iso heZ hZZ hf'
  refine ⟨f, h1, h2, h3, ?_⟩
  have h5 : fᴴ * J * Z = 0 := by rw [← adj hf.herm Z f, h4, conjTranspose_zero]
  funext i
  rw [← hcol _ i (), h5]
  rfl

end UpperTheory.Lit.Bur.DualCols

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns : ∀ {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z), ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  first | exact @UpperTheory.Lit.Bur.DualCols.exists_dual_cols | exact UpperTheory.Lit.Bur.DualCols.exists_dual_cols | (intros; apply UpperTheory.Lit.Bur.DualCols.exists_dual_cols <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.BlockEmbedConjIsUnitaryEmbedding
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.BlockEmb

open PI.UpqRep PI.HwUniqW

theorem blockW_mul_colW {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) :
    PI.UpqRep.blockW m r s * colW m r = colW m r * s := by
  ext i a
  have h1 : (PI.UpqRep.blockW m r s * colW m r) i a = PI.UpqRep.blockW m r s i (bl m r a) := by
    simp [Matrix.mul_apply, colW]
  rw [h1]
  by_cases hi : InB m r i
  · have hp : i.val - r < m := by unfold InB at hi; omega
    have hb := block_mk hi hp
    rw [← hb, blockW_bl, Matrix.mul_apply]
    simp [colW, blockIndex_injective.eq_iff]
  · rw [blockW_out s hi, if_neg (ne_of_inB (inB_bl a) hi).symm, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    simp [colW, (ne_of_inB (inB_bl b) hi).symm]

theorem blockW_mulVec_of_vanish {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) {y : Fin (2 * r + m + 1) → ℂ}
    (hy : ∀ a, y (bl m r a) = 0) : PI.UpqRep.blockW m r s *ᵥ y = y := by
  have hz : ∀ j, InB m r j → y j = 0 := fun j hj => by
    have hp : j.val - r < m := by unfold InB at hj; omega
    rw [← block_mk hj hp]; exact hy _
  funext i
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : InB m r i
  · rw [hz i hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : InB m r j
    · rw [hz j hj, mul_zero]
    · rw [blockW_in_out s hi hj, zero_mul]
  · simp [blockW_out s hi]

theorem isEmb_conj_blockW {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ}
    {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r)
    (hF : Q * colW m r = F * A) (hA : A * Ai = 1) :
    IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  have hFe : F = Q * colW m r * Ai := by rw [hF, Matrix.mul_assoc, hA, Matrix.mul_one]
  refine ⟨?_, fun x hx => ?_⟩
  · calc Q * PI.UpqRep.blockW m r s * Qi * F
        = Q * PI.UpqRep.blockW m r s * (Qi * Q) * colW m r * Ai := by
          rw [hFe]; simp only [Matrix.mul_assoc]
      _ = Q * (PI.UpqRep.blockW m r s * colW m r) * Ai := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Q * colW m r) * s * Ai := by
          rw [blockW_mul_colW]; simp only [Matrix.mul_assoc]
      _ = F * (A * s * Ai) := by
          rw [hF]; simp only [Matrix.mul_assoc]
  · have hy : ∀ a, (Qi *ᵥ x) (bl m r a) = 0 := fun a => by
      have e : (colW m r)ᴴ * PI.UpqRep.Hpk m r * Qi = Aᴴ * (Fᴴ * J) := by
        have hH : PI.UpqRep.Hpk m r = Qᴴ * J * Q := hg.symm
        rw [hH]
        calc (colW m r)ᴴ * (Qᴴ * J * Q) * Qi = (Q * colW m r)ᴴ * J * (Q * Qi) := by
              rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = Aᴴ * (Fᴴ * J) := by
              rw [h1, hF, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [← colW_mulVec (Qi *ᵥ x) a, mulVec_mulVec, e, ← mulVec_mulVec, hx, mulVec_zero]; rfl
    rw [← mulVec_mulVec, ← mulVec_mulVec, blockW_mulVec_of_vanish s hy, mulVec_mulVec, h1, one_mulVec]

end UpperTheory.Lit.Bur.BlockEmb

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding : ∀ {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r) (hF : Q * colW m r = F * A) (hA : A * Ai = 1), IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  first | exact @UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | exact UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | (intros; apply UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SmoothVecConjugateUnitaryGroupIff
noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
open scoped ContDiff

namespace UpperTheory.Lit.Bur.SmoothConj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_list_prod {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    Q * l.prod * Qi = (l.map fun g => Q * g * Qi).prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc Q * (a * l.prod) * Qi = Q * a * 1 * l.prod * Qi := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * a * Qi * (Q * l.prod * Qi) := by
          rw [← h2]; simp only [Matrix.mul_assoc]

theorem exp_conj_of_inverse {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Qi)) = Q * NormedSpace.exp (t • X) * Qi := by
  have hi : Qi = Q⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  subst hi
  rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mem_lieG_of_gram {J G Q Qi X : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hX : X ∈ lieG G) : Q * X * Qi ∈ lieG J := by
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Q * X * Qi)ᴴ * J + J * (Q * X * Qi) = 0
  calc (Q * X * Qi)ᴴ * J + J * (Q * X * Qi)
      = Qiᴴ * Xᴴ * Qᴴ * J * 1 + 1 * J * Q * X * Qi := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = Qiᴴ * Xᴴ * Qᴴ * J * (Q * Qi) + (Qiᴴ * Qᴴ) * J * Q * X * Qi := by rw [h1, hc]
    _ = Qiᴴ * (Xᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * X) * Qi := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hg, hX']; simp

theorem conj_inv_mem_lieG_of_gram {J G Q Qi Y : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hY : Y ∈ lieG J) : Qi * Y * Q ∈ lieG G := by
  have hY' : Yᴴ * J + J * Y = 0 := hY
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Qi * Y * Q)ᴴ * G + G * (Qi * Y * Q) = 0
  subst hg
  calc (Qi * Y * Q)ᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * (Qi * Y * Q)
      = Qᴴ * Yᴴ * (Qiᴴ * Qᴴ) * J * Q + Qᴴ * J * (Q * Qi) * Y * Q := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * (Yᴴ * J + J * Y) * Q := by
        rw [h1, hc]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = 0 := by rw [hY']; simp

theorem smoothVec_conj_of_subset {L L' : Set (Matrix (Fin n) (Fin n) ℂ)}
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {Q Qi : Matrix (Fin n) (Fin n) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hL : ∀ X ∈ L', Q * X * Qi ∈ L) {v : H}
    (hv : SmoothVec L σ v) : SmoothVec L' (fun g => σ (Q * g * Qi)) v := by
  intro k Xs hX
  have h := hv k (fun i => Q * Xs i * Qi) fun i => hL _ (hX i)
  have he : ∀ t : Fin k → ℝ, Q * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * Qi =
      (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Qi))).prod := by
    intro t
    rw [conj_list_prod h1 h2, List.map_ofFn]
    congr 1
    congr 1
    funext i
    exact (exp_conj_of_inverse h1 h2 (Xs i) (t i)).symm
  simpa only [he] using h

theorem smoothVec_conj_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * J * Q = G) (v : H) :
    SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  constructor
  · intro h
    have h' := smoothVec_conj_of_subset (L := lieG G) (L' := lieG J)
      (fun g => σ (Q * g * Qi)) h2 h1 (fun Y hY => conj_inv_mem_lieG_of_gram h1 hg hY) h
    have he : (fun g => σ (Q * (Qi * g * Q) * Qi)) = σ := by
      funext g
      have : Q * (Qi * g * Q) * Qi = g := by
        calc Q * (Qi * g * Q) * Qi = (Q * Qi) * g * (Q * Qi) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [h1]; simp
      rw [this]
    rwa [he] at h'
  · exact smoothVec_conj_of_subset σ h1 h2 fun X hX => conj_mem_lieG_of_gram h1 hg hX

end UpperTheory.Lit.Bur.SmoothConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (v : H), SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  first | exact @UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | exact UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | (intros; apply UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.CasselmanWallachContFiniteSumSobolevForms
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.CWCombo

theorem isCWCont_of_sobCont {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v)
    {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp)
    (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp}
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  classical
  have hnn : ∀ (L : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))) (v : H),
      0 ≤ (L.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := fun L v =>
    List.sum_nonneg (by
      intro x hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _)
  have key : ∀ s : Finset ι, ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, ∀ X ∈ w, PI.UpqRep.InLieHpk k r X) ∧
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ‖∑ i ∈ s, l i v • b i‖ ≤
        C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, [], by simp, by simp⟩
    | insert i s hi ih =>
      obtain ⟨C, Ws, hW, hb⟩ := ih
      obtain ⟨S, D, hS, hD⟩ := hl i
      refine ⟨|D| * ‖b i‖ + |C|, S ++ Ws, ?_, ?_⟩
      · intro w hw X hX
        rcases List.mem_append.1 hw with h | h
        · exact hS w h X hX
        · exact hW w h X hX
      · intro v hv
        have e : ‖l i v‖ ≤ D * (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
          have := hD v (hs v hv)
          simpa only [dsigW_eq] using this
        have h1 := hnn S v
        have h2 := hnn Ws v
        have h3 := hb v hv
        rw [Finset.sum_insert hi, List.map_append, List.sum_append]
        set P := (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        set Q := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        have hbn : 0 ≤ ‖b i‖ := norm_nonneg _
        have e1 : ‖l i v • b i‖ ≤ |D| * ‖b i‖ * P := by
          rw [norm_smul]
          calc ‖l i v‖ * ‖b i‖ ≤ (|D| * P) * ‖b i‖ :=
                mul_le_mul_of_nonneg_right (e.trans (mul_le_mul_of_nonneg_right (le_abs_self D) h1)) hbn
            _ = |D| * ‖b i‖ * P := by ring
        have e2 : ‖∑ j ∈ s, l j v • b j‖ ≤ |C| * Q :=
          h3.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h2)
        have a1 : 0 ≤ |D| * ‖b i‖ * Q := mul_nonneg (mul_nonneg (abs_nonneg _) hbn) h2
        have a2 : 0 ≤ |C| * P := mul_nonneg (abs_nonneg _) h1
        calc ‖l i v • b i + ∑ j ∈ s, l j v • b j‖ ≤ ‖l i v • b i‖ + ‖∑ j ∈ s, l j v • b j‖ := norm_add_le _ _
          _ ≤ |D| * ‖b i‖ * P + |C| * Q := add_le_add e1 e2
          _ ≤ (|D| * ‖b i‖ + |C|) * (P + Q) := by nlinarith
  obtain ⟨C, Ws, hW, hb⟩ := key Finset.univ
  exact ⟨C, Ws, hW, fun v hv => by rw [hB v hv]; exact hb v hv⟩

end UpperTheory.Lit.Bur.CWCombo

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms : ∀ {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v) {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp) (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp} (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i), PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  first | exact @UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | exact UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | (intros; apply UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HermitianFormPosCongruentIdentity
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.HermCongr


open scoped ComplexOrder in
theorem posDef_of_herm_re_pos {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) : J₀.PosDef := by
  have hA : J₀.IsHermitian := hH
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA ?_
  intro x hx
  have hre : 0 < (star x ⬝ᵥ J₀ *ᵥ x).re := hp x hx
  have him : (star x ⬝ᵥ J₀ *ᵥ x).im = 0 := hA.im_star_dotProduct_mulVec_self x
  exact Complex.pos_iff.2 ⟨hre, him.symm⟩

theorem exists_congr_one {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) :
    ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  have hP := posDef_of_herm_re_pos hH hp
  have hA : J₀.IsHermitian := hH
  have hd : ∀ i, 0 < hA.eigenvalues i := hP.eigenvalues_pos
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hJ : J₀ = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  let s : Fin m → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)
  let t : Fin m → ℂ := fun i => (((Real.sqrt (hA.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one]
  have htdt : diagonal t * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h0 : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    have h1 : Real.sqrt (hA.eigenvalues i) * Real.sqrt (hA.eigenvalues i) = hA.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have h2 : (Real.sqrt (hA.eigenvalues i))⁻¹ * hA.eigenvalues i * (Real.sqrt (hA.eigenvalues i))⁻¹ = 1 := by
      have h3 : ∀ r : ℝ, r ≠ 0 → r⁻¹ * (r * r) * r⁻¹ = 1 := by
        intro r hr
        field_simp
      have h4 := h3 _ h0
      rwa [h1] at h4
    simp only [t]
    exact_mod_cast h2
  have htH : (diagonal t)ᴴ = diagonal t := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [t]
  refine ⟨U * diagonal t, diagonal s * star U, ?_, ?_, ?_⟩
  · calc U * diagonal t * (diagonal s * star U) = U * (diagonal t * diagonal s) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hts, Matrix.mul_one, hUU']
  · calc diagonal s * star U * (U * diagonal t) = diagonal s * (star U * U) * diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hst]
  · rw [conjTranspose_mul, htH, ← star_eq_conjTranspose]
    calc diagonal t * star U * J₀ * (U * diagonal t)
        = diagonal t * star U * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U)
            * (U * diagonal t) := by rw [← hJ]
      _ = diagonal t * (star U * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
            * (star U * U) * diagonal t := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, Matrix.mul_one, htdt]

end UpperTheory.Lit.Bur.HermCongr

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity : ∀ {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀) (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re), ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  first | exact @UpperTheory.Lit.Bur.HermCongr.exists_congr_one | exact UpperTheory.Lit.Bur.HermCongr.exists_congr_one | (intros; apply UpperTheory.Lit.Bur.HermCongr.exists_congr_one <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SobolevContOfConjGramForm
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SobConj

theorem sobCont_conj {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) {l : H →ₗ[ℂ] ℂ} (hl : Sobolev₂ (lieG J) σ l) :
    Sobolev₂ (lieG G) (fun g => σ (Q * g * Qi)) l := by
  have back : ∀ a : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * a * Q) * Qi = a := fun a => by
    calc Q * (Qi * a * Q) * Qi = (Q * Qi) * a * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  have lie : ∀ X ∈ lieG J, Qi * X * Q ∈ lieG G := fun X hX =>
    GlobalTheory.SmoothCyclic.conj_lie h2 hg hX
  have e : ∀ X w, dRep (fun g => σ (Q * g * Qi)) (Qi * X * Q) w = dRep σ X w := fun X w => by
    simp only [dRep, GlobalTheory.SmoothCyclic.exp_conj_of_mul h2, back]
  have hsm : ∀ w, SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) w → SmoothVec (lieG J) σ w :=
    fun w hw k Xs hX => by
      simpa only [GlobalTheory.SmoothCyclic.expProd_conj h2, back] using
        hw k (fun i => Qi * Xs i * Q) fun i => lie _ (hX i)
  obtain ⟨S, C, hS, hb⟩ := hl
  refine ⟨S.map fun L => L.map fun X => Qi * X * Q, C, fun L hL X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact lie Y (hS L' hL' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using hb w (hsm w hw)

end UpperTheory.Lit.Bur.SobConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.sobolevCont_of_conj_gram_form : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) {l : H →ₗ[ℂ] ℂ} (hl : Sobolev₂ (lieG J) σ l), Sobolev₂ (lieG G) (fun g => σ (Q * g * Qi)) l := by
  first | exact @UpperTheory.Lit.Bur.SobConj.sobCont_conj | exact UpperTheory.Lit.Bur.SobConj.sobCont_conj | (intros; apply UpperTheory.Lit.Bur.SobConj.sobCont_conj <;> assumption)
end

noncomputable section

namespace UpperTheory.Lit.Bur.BurPos

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem rank_le_one_of_dep {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (h : ∀ x ∈ S, ∀ y ∈ S, ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • x + b • y = 0) : Module.rank ℂ S ≤ 1 := by
  by_cases h0 : S = ⊥
  · subst h0; simp
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  refine rank_le_one_iff.2 ⟨⟨x, hx⟩, fun y => ?_⟩
  obtain ⟨a, b, hab, e⟩ := h x hx y y.2
  have hb : b ≠ 0 := by
    rintro rfl
    rcases hab with ha | hb
    · simp only [zero_smul, add_zero] at e
      exact (smul_ne_zero ha hx0) e
    · exact hb rfl
  refine ⟨-(b⁻¹ * a), Subtype.ext ?_⟩
  have e' : (y : V) = -(b⁻¹ * a) • x := by
    have : b • (y : V) = -(a • x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e
    calc (y : V) = b⁻¹ • (b • (y : V)) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = -(b⁻¹ * a) • x := by rw [this, smul_neg, smul_smul, neg_smul]
  simpa using e'.symm

theorem isDSHpk_tr {m r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (H →L[ℂ] H)}
    {J Q Qi fr : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {ε : Fin (2 * r + m + 1) → Bool}
    {lam : Fin (2 * r + m + 1) → ℝ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r)
    (hfr : IsUnit fr) (hJ : frᴴ * Formalism.REAL.Jm ε * fr = J) (hds : Formalism.MainNotions.S.IsDS ε lam (fun g => σ (fr⁻¹ * g * fr))) :
    PI.UpqRep.IsDSHpk m r ε lam (fun g => σ (Q * g * Qi)) := by
  have hd := (Matrix.isUnit_iff_isUnit_det fr).1 hfr
  have g1 : (fr * Q) * (Qi * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h1, Matrix.one_mul, mul_nonsing_inv _ hd]
  have g2 : (Qi * fr⁻¹) * (fr * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc fr⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul, h2]
  have gg : (fr * Q)ᴴ * Formalism.REAL.Jm ε * (fr * Q) = Formalism.QuantumDeterminants.Hpk m r := by
    rw [← hg, ← hJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hc := UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian ε g1 g2 gg
  obtain ⟨P, hP⟩ := (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff m r ε).2 hc
  refine ⟨P, hP, ?_⟩
  have := Formalism.L2.SG.Pf.Choice.dsHpk_tr rfl ε ε (fun _ => rfl) lam lam (fun _ => rfl) _ hds (fr * Q) (Qi * fr⁻¹) g1 gg P hP
  have e : (fun g => σ (fr⁻¹ * (fr * Q * (P⁻¹ * g * P) * (Qi * fr⁻¹)) * fr)) = fun g => σ (Q * (P⁻¹ * g * P) * Qi) := by
    funext g
    congr 1
    have e1 : fr⁻¹ * (fr * Q * (P⁻¹ * g * P) * (Qi * fr⁻¹)) * fr = (fr⁻¹ * fr) * Q * (P⁻¹ * g * P) * Qi * (fr⁻¹ * fr) := by
      simp only [Matrix.mul_assoc]
    rw [e1, nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_one]
  rw [e] at this
  exact this

theorem frame_normal {m r : ℕ} {J : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {e : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ}
    {z : Fin (2 * r + m + 1) → ℂ} (hf : IsFrame J J₀ F e z) (hz : (Formalism.QuantumDeterminants.herm J z z).re < 0)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) :
    ∃ (Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ) (A Ai : Matrix (Fin m) (Fin m) ℂ) (t : ℝ),
      Q * Qi = 1 ∧ Qi * Q = 1 ∧ A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 ∧ Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r ∧
      Q * colE m r = e ∧ Q * colW m r = F * A ∧ 0 < t ∧
      Q *ᵥ ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = z := by
  have h0 : J₀ᴴ = J₀ := by
    rw [← hf.gram]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, hf.herm, Matrix.mul_assoc]
  obtain ⟨A, Ai, a1, a2, a3⟩ := UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity h0 hp
  obtain ⟨f, f1, f2, f3, f4⟩ := UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns hf
  have hreal : Formalism.QuantumDeterminants.herm J z z = (((Formalism.QuantumDeterminants.herm J z z).re : ℝ) : ℂ) := by
    have hc : star (Formalism.QuantumDeterminants.herm J z z) = Formalism.QuantumDeterminants.herm J z z := by
      unfold Formalism.QuantumDeterminants.herm
      conv_rhs => rw [star_dotProduct, star_mulVec, hf.herm, ← dotProduct_mulVec]
    exact (Complex.conj_eq_iff_re.1 hc).symm
  set T : ℝ := -(Formalism.QuantumDeterminants.herm J z z).re with hT
  have hTp : 0 < T := by simpa [hT] using hz
  set t : ℝ := Real.sqrt T with ht
  have htp : 0 < t := Real.sqrt_pos.2 hTp
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
  have hsq : t * t = T := Real.mul_self_sqrt hTp.le
  obtain ⟨Q, Qi, q1, q2, qg, qe, qw, qy⟩ := UpperTheory.Lit.Bur.hyperbolic_frame_congruent_splitHermGram (Fa := F * A) (e := e) (f := f) (y := (t⁻¹ : ℂ) • z) hf.herm
    (by rw [conjTranspose_mul]; calc _ = Aᴴ * (Fᴴ * J * F) * A := by simp only [Matrix.mul_assoc]
                                     _ = 1 := by rw [hf.gram, a3])
    hf.e_iso f2 f1
    (by rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, hf.e_perp]; simp)
    (by rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, f3]; simp)
    (by rw [mulVec_smul, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hf.z_perpF]; simp)
    (by rw [mulVec_smul, hf.z_perpE]; simp)
    (by rw [mulVec_smul, f4]; simp)
    (by
      have e1 : Formalism.QuantumDeterminants.herm J ((t⁻¹ : ℂ) • z) ((t⁻¹ : ℂ) • z) = (t⁻¹ : ℂ) * (t⁻¹ : ℂ) * Formalism.QuantumDeterminants.herm J z z := by
        unfold Formalism.QuantumDeterminants.herm
        rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
        simp [mul_assoc]
      rw [e1, hreal]
      have e2 : (((Formalism.QuantumDeterminants.herm J z z).re : ℝ) : ℂ) = -((t : ℂ) * t) := by
        have : (Formalism.QuantumDeterminants.herm J z z).re = -(t * t) := by rw [hsq, hT]; ring
        rw [this]; push_cast; ring
      rw [e2]
      field_simp)
  refine ⟨Q, Qi, A, Ai, t, q1, q2, a1, a2, a3, qg, qe, qw, htp, ?_⟩
  rw [mulVec_smul, qy, smul_smul, mul_inv_cancel₀ htc, one_smul]

theorem tz_last (m r : ℕ) (t : ℝ) :
    Formalism.QuantumDeterminants.Tz m r ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = t ^ 2 := by
  have hb : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = -1 := by
    unfold Formalism.QuantumDeterminants.herm Formalism.QuantumDeterminants.bvec
    simp [dotProduct, Pi.single_apply, mulVec, Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.wI]
    rw [Finset.sum_eq_single (⟨r + m, by omega⟩ : Fin (2 * r + m + 1))]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  unfold Formalism.QuantumDeterminants.Tz
  have e1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = (t : ℂ) * t * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) := by
    unfold Formalism.QuantumDeterminants.herm
    rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
    simp [mul_assoc]
  rw [e1, hb]
  simp [pow_two, ← Complex.ofReal_mul]

theorem inWb_last (m r : ℕ) (t : ℝ) :
    Formalism.QuantumDeterminants.inWb m r ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) := by
  intro i hi
  have : i ≠ Formalism.QuantumDeterminants.wI m r (Fin.last m) := by
    intro h; subst h; simp [Formalism.QuantumDeterminants.wI] at hi
  simp [Formalism.QuantumDeterminants.bvec, this]

theorem isFrameW_one (m r : ℕ) {t : ℝ} (ht : 0 < t) :
    PI.UpqRep.IsFrameW m r ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) 1 := by
  refine ⟨?_, fun a => ⟨one_mulVec _, one_mulVec _⟩, ?_⟩
  · show (1 : Matrix _ _ ℂ)ᴴ * _ * 1 = _
    simp
  · have := tz_last m r t
    rw [one_mulVec]
    show ((Real.sqrt (Formalism.QuantumDeterminants.Tz m r _) : ℝ) : ℂ) • _ = _
    rw [this, Real.sqrt_sq ht.le]
    rfl

theorem chi_eq {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ}
    {e : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ} {z z' : Fin (2 * r + m + 1) → ℂ} {c : Fin r → ℂ}
    {χ : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → ℂ} (q1 : Q * Qi = 1) (q2 : Qi * Q = 1)
    (qg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r) (qe : Q * colE m r = e) (qz : Q *ᵥ z' = z) (hz' : Formalism.QuantumDeterminants.inWb m r z')
    (hf' : IsFrame (Formalism.QuantumDeterminants.Hpk m r) 1 ((1 : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ) * colW m r) (colE m r) z') (hχ : IsCharWith J e z c χ)
    {u : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (hu : u ∈ unipRad (Formalism.QuantumDeterminants.Hpk m r) (colE m r)) :
    χ (Q * u * Qi) = PI.BesselMapUniq.psiGen m r z' c u := by
  obtain ⟨a, ha⟩ := hf'.exists_coords hu
  rw [isCharWith hz' c u hu a ha, hχ _ (UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical q1 q2 qg qe hu) a fun j => ?_]
  have hfl : flagVec e z j.succ = Q *ᵥ flagVec (colE m r) z' j.succ := by
    refine Fin.lastCases ?_ (fun i => ?_) j.succ
    · simp [flagVec, qz]
    · simp only [flagVec, Fin.snoc_castSucc]
      rw [← qe]
      funext k
      simp [Matrix.mul_apply, mulVec, dotProduct]
  have hq : Q * u * Qi - 1 = Q * (u - 1) * Qi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, q1]
  rw [hfl, hq, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, q2, Matrix.mul_one, ← mulVec_mulVec, ha j, ← qe,
    mulVec_mulVec]

theorem burGapPos_of_bmu : CompanionTheory.Bmu.BesselMapUniqGap → UpperTheory.Lit.Bur.BurGapPos := by
  intro hB n m r J J₀ F e z hf hm hz hp χ hχ H _ _ _ σ hU hI h hh hgap W _ _ _ π₀ hπ
  obtain rfl : n = 2 * r + m + 1 := by have := hf.codim; omega
  by_cases hW : Nontrivial W
  swap
  · have : Subsingleton W := not_nontrivial_iff_subsingleton.1 hW
    refine rank_le_one_of_dep _ fun x _ y _ => ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    ext w
    simp [Subsingleton.elim w 0]
  obtain ⟨ε, lam, fr, hfrU, hfrJ, hHC, hG, hDS⟩ := hgap
  obtain ⟨c, hc, hχc⟩ := hχ
  obtain ⟨Q, Qi, A, Ai, t, q1, q2, a1, a2, a3, qg, qe, qw, ht, qz⟩ := frame_normal hf hz hp
  set z' : Fin (2 * r + m + 1) → ℂ := (t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m)) with hz'
  have hzW : Formalism.QuantumDeterminants.inWb m r z' := inWb_last m r t
  have hTz : 0 < Formalism.QuantumDeterminants.Tz m r z' := by rw [hz', tz_last]; positivity
  have hfw : PI.UpqRep.IsFrameW m r z' 1 := isFrameW_one m r ht
  have hf' := isFrame hfw hzW hTz
  set σ' : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (H →L[ℂ] H) := fun g => σ (Q * g * Qi) with hσ'
  have hDSH : PI.UpqRep.IsDSHpk m r ε lam σ' := isDSHpk_tr q1 q2 qg hfrU hfrJ hDS
  obtain ⟨-, hU', -⟩ := rep_of_isDSHpk hDSH
  have hsm : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := m) (r := r) σ' ↔ v ∈ smSub J σ := fun v =>
    (smoothOnH_iff_mem PI.HwUniqW.Hpk_conjTranspose PI.HwUniqW.Hpk_mul_self hU' v).trans (UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff σ q1 q2 qg v)
  have hπ' := UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred a1 a2 a3 hπ
  obtain ⟨Wp, _, _, _, ρ, T1, hρ, hT1, hirr⟩ := UpperTheory.Lit.Bur.contIrred_compactUnitaryGroup_rep_isUnitarizable hπ'
  have hD : Nontrivial (Module.Dual ℂ W) := (Module.nontrivial_dual_iff ℂ).2 hW
  have : Nontrivial Wp := T1.symm.toEquiv.nontrivial
  obtain ⟨u, Wq, _, _, ρ', T2, hty, hT2⟩ := UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType hρ hirr
  set T : Module.Dual ℂ W ≃ₗ[ℂ] Wq := T1.trans T2 with hTdef
  have hone : ∀ s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ), s ∈ PI.UpqRep.UJset (PI.UpqRep.allPos m) := fun s hs =>
    PI.HwUniqW.mem_UJset_allPos.2 (mem_UH_one.1 hs)
  have hT : ∀ s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ), ∀ l : Module.Dual ℂ W,
      T ((π₀ (A * sᴴ * Ai)).dualMap l) = ρ' s (T l) := fun s hs l => by
    simp only [hTdef, LinearEquiv.trans_apply]
    rw [hT1 s hs l, hT2 s (hone s hs)]
  set π : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (Wq →L[ℂ] Wq) := fun g => ρ' (PI.HwUniqW.sub m r g) with hπdef
  have hty' : PI.UpqRep.IsHCTypeW m r z' u π := by
    refine ⟨1, hfw, ?_⟩
    have e1 : (fun h => π (1 * PI.UpqRep.blockW m r h * (1 : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ)⁻¹)) = ρ' := by
      funext h
      simp [hπdef, PI.HwUniqW.sub_blockW]
    rw [e1]
    exact hty
  have key : ∀ β ∈ besselForms J J₀ F e χ σ π₀ (smSub J σ), ∃ B : H → Wq,
      PI.BesselMapUniq.IsBesselMapSm (k := m) (r := r) z' (PI.BesselMapUniq.psiGen m r z' c) σ' π B ∧
      ∀ x : smSub J σ, B x = T (β.flip x) := by
    intro β hβ
    have hBm : ∃ B : H → Wq, ∀ x : smSub J σ, B x = T (β.flip x) := by
      classical
      exact ⟨fun v => if hv : v ∈ smSub J σ then T (β.flip ⟨v, hv⟩) else 0, fun x => dif_pos x.2⟩
    obtain ⟨B, hBx⟩ := hBm
    refine ⟨B, ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h' hh' u' hu' v hv => ?_, ?_⟩, hBx⟩
    · have hv' := (hsm v).1 hv
      have hw' := (hsm w).1 hw
      have e0 := hBx (⟨v, hv'⟩ + ⟨w, hw'⟩)
      rw [map_add (f := _), map_add (f := _), ← hBx, ← hBx] at e0
      exact e0
    · have hv' := (hsm v).1 hv
      have e0 := hBx (a • ⟨v, hv'⟩)
      rw [map_smul, map_smul, ← hBx] at e0
      exact e0
    · have hv' := (hsm v).1 hv
      have hfix : PI.HwUniqW.FixEW m r h' := by
        refine ⟨hh'.2.1, ?_⟩
        have e0 := hh'.2.2
        rw [hz', mulVec_smul] at e0
        exact smul_right_injective _ (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0) e0
      obtain ⟨hs, hbl⟩ := PI.HwUniqW.fix_block hh'.1 hfix
      set s := PI.HwUniqW.sub m r h' with hsdef
      have hs1 : sᴴ * s = 1 := PI.HwUniqW.mem_UJset_allPos.1 hs
      have hs2 : s * sᴴ = 1 := mul_eq_one_comm.1 hs1
      have hsU : s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) := mem_UH_one.2 hs1
      have hJ₀ : Aiᴴ * Ai = J₀ := by
        have e0 : Aiᴴ * (Aᴴ * J₀ * A) * Ai = (A * Ai)ᴴ * J₀ * (A * Ai) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
        rw [a3, a1] at e0
        simpa using e0
      have hmem : ∀ y : Matrix (Fin m) (Fin m) ℂ, yᴴ * y = 1 → A * y * Ai ∈ Formalism.QuantumDeterminants.UH J₀ := fun y hy => by
        show (A * y * Ai)ᴴ * J₀ * (A * y * Ai) = J₀
        have e0 : (A * y * Ai)ᴴ * J₀ * (A * y * Ai) = Aiᴴ * (yᴴ * (Aᴴ * J₀ * A) * y) * Ai := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
        rw [e0, a3, Matrix.mul_one, hy, Matrix.mul_one, hJ₀]
      have hh0 := hmem s hs1
      have hh1 := hmem sᴴ (by rw [conjTranspose_conjTranspose]; exact hs2)
      have h01 : (A * s * Ai) * (A * sᴴ * Ai) = 1 := by
        have e0 : (A * s * Ai) * (A * sᴴ * Ai) = A * s * (Ai * A) * sᴴ * Ai := by simp only [Matrix.mul_assoc]
        rw [e0, a2, Matrix.mul_one, Matrix.mul_assoc A, hs2, Matrix.mul_one, a1]
      have hinv : ∀ w, π₀ (A * s * Ai) (π₀ (A * sᴴ * Ai) w) = w := fun w => by
        have e0 := hπ.1.2 _ hh0 _ hh1
        rw [h01, hπ.1.1] at e0
        exact (LinearMap.congr_fun e0 w).symm
      have hgu := UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical q1 q2 qg qe (UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup hu')
      have hQi : Qiᴴ * Formalism.QuantumDeterminants.Hpk m r * Qi = J := by
        rw [← qg]
        calc Qiᴴ * (Qᴴ * J * Q) * Qi = (Q * Qi)ᴴ * J * (Q * Qi) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = J := by rw [q1]; simp
      have hgh : Q * h' * Qi ∈ Formalism.QuantumDeterminants.UH J := by
        show (Q * h' * Qi)ᴴ * J * (Q * h' * Qi) = J
        have hh2 : h'ᴴ * Formalism.QuantumDeterminants.Hpk m r * h' = Formalism.QuantumDeterminants.Hpk m r := hh'.1
        calc (Q * h' * Qi)ᴴ * J * (Q * h' * Qi) = Qiᴴ * (h'ᴴ * (Qᴴ * J * Q) * h') * Qi := by
              simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = J := by rw [qg, hh2, hQi]
      have hE : IsEmb J F (Q * h' * Qi) (A * s * Ai) := by
        have := UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding (s := s) q1 q2 qg qw a1
        rwa [← hbl] at this
      have e1 : σ' (h' * u') v = σ (Q * h' * Qi) (σ (Q * u' * Qi) v) := by
        have e0 : Q * (h' * u') * Qi = (Q * h' * Qi) * (Q * u' * Qi) := by
          have : (Q * h' * Qi) * (Q * u' * Qi) = Q * h' * (Qi * Q) * u' * Qi := by simp only [Matrix.mul_assoc]
          rw [this, q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
        show σ (Q * (h' * u') * Qi) v = _
        rw [e0, hU.1.2 _ hgh _ hgu.1]
        rfl
      let x : smSub J σ := ⟨v, hv'⟩
      let y1 : smSub J σ := ⟨σ (Q * u' * Qi) v, UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup hf.unit hU hgu.1 hv'⟩
      let y2 : smSub J σ := ⟨σ (Q * h' * Qi) y1, UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup hf.unit hU hgh y1.2⟩
      have hflip : β.flip y2 = χ (Q * u' * Qi) • (π₀ (A * sᴴ * Ai)).dualMap (β.flip x) := by
        ext w
        have i1 := hβ.inv _ hh0 _ hgh hE (π₀ (A * sᴴ * Ai) w) y1 y2 rfl
        have i2 := hβ.equiv _ hgu (π₀ (A * sᴴ * Ai) w) x y1 rfl
        rw [hinv] at i1
        simp only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.dualMap_apply, smul_eq_mul]
        rw [i1, i2]
      have hχe := chi_eq q1 q2 qg qe qz hzW hf' hχc (UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup hu')
      rw [e1]
      show B (y2 : H) = _
      rw [hBx y2, hflip, map_smul, hT s hsU, hχe, ← hBx x]
    · let b := Module.finBasis ℂ W
      choose l hl1 hl2 using fun i => hβ.cont (b i)
      refine UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms (fun v hv => (UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff σ q1 q2 qg v).2 ((hsm v).1 hv)) l (fun i => T (b.coord i))
        (fun i => UpperTheory.Lit.Bur.sobolevCont_of_conj_gram_form σ q1 q2 qg (hl1 i)) (fun v hv => ?_)
      have hv' := (hsm v).1 hv
      have e0 := hBx ⟨v, hv'⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_dual_apply_smul_coord (β.flip ⟨v, hv'⟩), map_sum] at e0
      refine e0.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_smul, LinearMap.flip_apply, ← hl2 i ⟨v, hv'⟩]
  refine rank_le_one_of_dep _ fun β₁ h₁ β₂ h₂ => ?_
  obtain ⟨B₁, m₁, e₁⟩ := key β₁ h₁
  obtain ⟨B₂, m₂, e₂⟩ := key β₂ h₂
  obtain ⟨a, b, hab, hz0⟩ := hB m r ε lam h H σ' z' c u Wq π hm hG hh hHC hDSH hzW hTz hc hty' B₁ B₂ m₁ m₂
  refine ⟨a, b, hab, ?_⟩
  ext w x
  have h0 := hz0 x ((hsm x).2 x.2)
  rw [e₁ x, e₂ x] at h0
  have h1 : T (a • β₁.flip x + b • β₂.flip x) = 0 := by rw [map_add (f := _), map_smul, map_smul]; exact h0
  have := LinearMap.congr_fun (T.map_eq_zero_iff.1 h1) w
  simpa using this

end UpperTheory.Lit.Bur.BurPos
end
end

namespace UpperTheory.Lit

open GlobalTheory.SepRows

theorem burGapPos : Bur.BurGapPos := Bur.BurPos.burGapPos_of_bmu CompanionTheory.Bmu.besselMapUniqGap

end UpperTheory.Lit

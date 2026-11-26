module

public import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ConeVal
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.SmallFSing
set_option linter.unusedSectionVars false

noncomputable section

open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil PositivityTheory.ThK.SplitLoc

namespace PositivityTheory.ThKG.Std

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL GlobalTheory.CompanionTheory.QL.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d a a' : ℕ} {ν α β : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}

def InR (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) : Prop :=
  ∀ i j, valuation k (Y i j) ≤ valuation k (rad ϖ c e j)

open Classical in
theorem prod_ind (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) :
    ∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) (Y p.1 p.2) = if InR ϖ c e Y then 1 else 0 := by
  simp only [ind, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff, InR, Prod.forall]
  congr

theorem InR.mul {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (h : InR ϖ c e Y) {g : Matrix (Fin n) (Fin n) k}
    (hg : ∀ i j, g i j ∈ 𝒪[k]) : InR ϖ c e (g * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact (valuation k).map_sum_le fun l _ => by rw [map_mul]; exact (mul_le_of_le_one_left' (hg i l)).trans (h l j)

open Classical in
theorem std_mul {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) (g : GL (Fin n) k) (z : ℂ) :
    std ν ϖ c e (g.1 * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z =
      (KO k (Fin n) : Set _).indicator (fun _ => if InR ϖ c e Y then 1 else 0) g := by
  have hb : (g.1 * Y).submatrix id e = g.1 := by
    rw [show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, hY, Matrix.mul_one]
  rw [std, hb, prod_ind]
  by_cases hg : g ∈ KO k (Fin n)
  · have hv := valuation_gdet_of_mem_KO hg
    rw [Set.indicator_of_mem hg, show g.1.det = (gdet g : k) from rfl, dl_unit _ hv, apow_of_valuation_eq_one hv]
    rw [mem_KO_iff] at hg
    have : InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y := ⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩
    simp [this]
  · rw [Set.indicator_of_notMem hg]
    by_cases h1 : InR ϖ c e (g.1 * Y)
    · have h2 : ∀ i j, valuation k (g.1 i j) ≤ 1 := fun i j => by
        have := h1 i (e j)
        rwa [rad_e, map_one, show (g.1 * Y) i (e j) = g.1 i j from congrFun (congrFun hb i) j] at this
      rw [dl_of_ne, mul_zero, zero_mul, zero_mul]
      intro hd
      refine hg ((mem_KO_iff _).2 ⟨h2, fun i j => ?_⟩)
      show valuation k _ ≤ 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd,
        inv_one, one_mul, adjugate_apply]
      refine val_det fun p q => ?_
      rw [updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]; split_ifs <;> simp
      · exact h2 p q
    · simp [h1]

theorem std_sing {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) (g : Matrix (Fin n) (Fin n) k) :
    std ν ϖ c e (g * Y) = 0 := by
  rw [std, show (g * Y).submatrix id e = g * Y.submatrix id e from rfl, det_mul, hY, mul_zero, dl_of_ne (by simp), mul_zero]

variable [MeasurableSpace k] [BorelSpace k]

theorem int_KO (A : ℂ) : ∫ g, (KO k (Fin n) : Set _).indicator (fun _ => A) g ∂haarVol (KO k (Fin n)) = A := by
  rw [integral_indicator isOpen_KO.measurableSet]
  simp [Measure.real, haarVol_self isOpen_KO le_rfl]

theorem bigF_sing (μ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) :
    bigF μ ϖ ν (std ν ϖ c e) Y = 0 := by simp [bigF, shellSum, shell, std_sing hY]

theorem smallF_sing (μ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) :
    smallF μ ν (std ν ϖ c e) Y = 0 := by simp [smallF, std_sing hY]

open Classical in
theorem smallF_std {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) :
    smallF (haarVol (KO k (Fin n))) ν (std ν ϖ c e) Y = if InR ϖ c e Y then 1 else 0 := by
  simp only [smallF, std_mul hY, int_KO]

open Classical in
theorem bigF_std (hϖ : IsUnif ϖ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) :
    bigF (haarVol (KO k (Fin n))) ϖ ν (std ν ϖ c e) Y = if InR ϖ c e Y then 1 else 0 := by
  rw [bigF, shellSum, finsum_eq_single _ ⟨0, antitone_const⟩]
  · simp only [shell, std_mul hY, shellSet_zero]
    rw [setIntegral_indicator isOpen_KO.measurableSet, Set.inter_self, ← integral_indicator isOpen_KO.measurableSet, int_KO]
  · intro m hm
    simp only [shell, std_mul hY]
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => Set.indicator_of_notMem (fun hK => hm (Subtype.ext (funext fun i => ?_))) _
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
    have h1 := (mem_KO_iff _).1 ((Subgroup.mul_mem_cancel_left _ hx).1 ((Subgroup.mul_mem_cancel_right _ hy).1 hK))
    have h2 : valuation k ((ϖ : k) ^ m.1 i) ≤ 1 := by simpa [diagGL_val] using (show valuation k _ ≤ 1 from h1.1 i i)
    have h3 : valuation k ((ϖ : k) ^ (-m.1 i)) ≤ 1 := by
      have := (show valuation k _ ≤ 1 from h1.2 i i)
      rw [show (diagGL fun i => ϖ ^ m.1 i)⁻¹ = diagGL fun i => ϖ ^ (-m.1 i) from inv_eq_of_mul_eq_one_right (Units.ext (by
        simp [diagGL_val, funext_iff, zpow_ne_zero]))] at this
      simpa [diagGL_val] using this
    rw [map_zpow₀, hϖ, zpow_le_one_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one] at h2 h3
    show m.1 i = 0
    omega

def eA (a a' : ℕ) (i : Fin a) : Fin (a + a') := finSumFinEquiv (Sum.inl i)

def eB (a a' : ℕ) (i : Fin a') : Fin (a + a') := finSumFinEquiv (Sum.inr i)

def low (y : Matrix (Fin a') (Fin a) k) : GL (Fin (a + a')) k :=
  ⟨(fromBlocks 1 0 y 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    (fromBlocks 1 0 (-y) 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp, by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp⟩

theorem gdet_low (y : Matrix (Fin a') (Fin a) k) : gdet (low y) = 1 := Units.ext (by
  show det (Matrix.submatrix _ _ _) = 1
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simp)

theorem rad_AB (j : Fin a') : rad ϖ c (eA a a') (finSumFinEquiv (Sum.inr j)) = (ϖ : k) ^ c :=
  if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h

theorem rad_BA (j : Fin a) : rad ϖ c (eB a a') (finSumFinEquiv (Sum.inl j)) = (ϖ : k) ^ c :=
  if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h

theorem low_X (y : Matrix (Fin a') (Fin a) k) : ∀ i (j : Fin a ⊕ Fin a'), (X0 k finSumFinEquiv * (invT (low y)).1 : Matrix (Fin a) (Fin (a + a')) k) i (finSumFinEquiv j) =
    fromBlocks (1 : Matrix (Fin a) (Fin a) k) 0 (-y) (1 : Matrix (Fin a') (Fin a') k) j (Sum.inl i) := fun i j => by
    refine (frameMatrixFirstColumnBlock_mul_apply finSumFinEquiv (invT (low y)).1 i _).trans ?_
    simp [invT_val, low]

theorem low_Y (y : Matrix (Fin a') (Fin a) k) : ∀ i (j : Fin a ⊕ Fin a'), (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k) i (finSumFinEquiv j) =
    fromBlocks (1 : Matrix (Fin a) (Fin a) k) 0 y 1 (Sum.inr i) j := fun i j => by
    refine (frameMatrixSecondColumnBlock_mul_apply finSumFinEquiv (low y).1 i _).trans ?_
    simp [low]

open Classical in
theorem pRam_low (hϖ : IsUnif ϖ) (y : Matrix (Fin a') (Fin a) k) : pRam a a' ϖ ν β (std ν ϖ c (eA a a')) (low y) =
    if ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c) then 1 else 0 := by
  have e := low_X (k := k) y
  rw [pRam, bigZetaIntegral_eq, gdet_low, bigF_std hϖ (by
    ext i j; rw [submatrix_apply, eA, id]; erw [e]; simp [Matrix.one_apply, eq_comm])]
  simp only [map_one, Units.val_one, apow_one, one_mul]
  refine if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl
  · have := h j (finSumFinEquiv (Sum.inr i))
    erw [e, rad_AB] at this
    simpa using this
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · erw [e, show finSumFinEquiv (Sum.inl j) = eA a a' j from rfl, rad_e]
      simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · erw [e, rad_AB]; simpa using h j i

open Classical in
theorem pRam'_low (y : Matrix (Fin a') (Fin a) k) : pRam' a a' ν α (std ν ϖ c (eB a a')) (low y) =
    if ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c) then 1 else 0 := by
  have e := low_Y (k := k) y
  have hY : (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a') = 1 := by
    ext i j; rw [submatrix_apply, eB, id, e]; simp
  rw [pRam', smallP, gdet_low]
  erw [smallF_std hY]
  simp only [map_one, Units.val_one, apow_one, one_mul]
  refine if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl
  · have := h i (finSumFinEquiv (Sum.inl j))
    erw [e, rad_BA] at this
    simpa using this
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · erw [e, rad_BA]; simpa using h i j
    · erw [e, show finSumFinEquiv (Sum.inr j) = eB a a' j from rfl, rad_e]
      simp only [fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp

theorem pRam_ne (hϖ : IsUnif ϖ) : pRam a a' ϖ ν β (std ν ϖ c (eA a a')) ≠ 0 := fun h => by
  have := congrFun h (low 0)
  rw [pRam_low hϖ] at this
  simp at this

theorem std_pair (H : HidaSetting a a' ϖ α β ν) (hr : ¬ IsUnram ν) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) :
    pRam a a' ϖ ν β (std ν ϖ c (eA a a')) = pRam' a a' ν α (std ν ϖ c (eB a a')) := by
  funext h
  let s : Fin a ⊕ Fin a' ≃ Fin (a + a') := finSumFinEquiv
  set N := h.1.submatrix s s with hN
  set N' := (h⁻¹).1.submatrix s s with hN'
  have hNN : N * N' = 1 := by rw [hN, hN', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
  by_cases hD : N.toBlocks₂₂.det = 0
  · have h1 : N'.toBlocks₁₁.det = 0 := by
      by_contra h1
      rw [← fromBlocks_toBlocks N, ← fromBlocks_toBlocks N', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hNN
      obtain ⟨-, -, e1, e2⟩ := hNN
      have e3 : N.toBlocks₂₁ = -(N.toBlocks₂₂ * N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹) := by
        rw [← Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left e1, Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit h1)]
      have e4 : N.toBlocks₂₂ * (N'.toBlocks₂₂ - N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹ * N'.toBlocks₁₂) = 1 := by
        rw [← e2, e3]; simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]; abel
      have := congrArg det e4
      rw [det_mul, hD, zero_mul, det_one] at this
      exact zero_ne_one this
    have a1 : ((X0 k finSumFinEquiv * (invT h).1 : Matrix (Fin a) (Fin (a + a')) k).submatrix id (eA a a')).det = 0 := by
      rw [← det_transpose, ← h1]; congr 1; ext i j
      exact frameMatrixFirstColumnBlock_mul_apply s (invT h).1 j _
    have a2 : ((Y0 k finSumFinEquiv * h.1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a')).det = 0 := by
      rw [← hD]; congr 1; ext i j
      exact frameMatrixSecondColumnBlock_mul_apply s h.1 i _
    rw [pRam, bigZetaIntegral_eq, pRam', smallP]
    erw [bigF_sing _ a1, smallF_sing _ a2]
    simp
  · set y := N.toBlocks₂₂⁻¹ * N.toBlocks₂₁ with hy
    set b := h * (low y)⁻¹ with hb
    have eb : b.1.submatrix s s = N * fromBlocks 1 0 (-y) 1 := by
      rw [hb, Units.val_mul, ← submatrix_mul_equiv _ _ _ s]
      congr 1
      ext i j; simp [low, s]
    have e21 : (b.1.submatrix s s).toBlocks₂₁ = 0 := by
      rw [eb, ← fromBlocks_toBlocks N, fromBlocks_multiply]
      simp [hy, Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hD)]
    have hu : IsBlockUpper b := fun i j => congrFun (congrFun e21 i) j
    have hdet : (blkA b).det * (blkD b).det ≠ 0 := by
      have : b.1.det = (blkA b).det * (blkD b).det := by
        rw [← det_submatrix_equiv_self s, ← fromBlocks_toBlocks (b.1.submatrix s s), e21, det_fromBlocks_zero₂₁]; rfl
      rw [← this]; exact b.det_ne_zero
    have hh : h = b * low y := by simp [hb]
    rw [hh, (pRam_mem H hr (std_mem H.unif hc hν _)).2 b _ hu (Units.mk0 _ (left_ne_zero_of_mul hdet))
      (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, (pRam'_mem H (std_mem H.unif hc hν _)).2 b _ hu
      (Units.mk0 _ (left_ne_zero_of_mul hdet)) (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, pRam_low H.unif, pRam'_low]

omit [MeasurableSpace k] [BorelSpace k] in
theorem std_left {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (Y : Matrix (Fin n) (Fin d) k) :
    (ν (gdet g) : ℂ) * std ν ϖ c e (g.1 * Y) = std ν ϖ c e Y := by
  have hv := valuation_gdet_of_mem_KO hg
  rw [mem_KO_iff] at hg
  have : InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y := ⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩
  rw [std, std, prod_ind, prod_ind, show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, det_mul,
    show g.1.det = (gdet g : k) from rfl, dl_mul_unit hv, dl_unit _ hv]
  rw [propext this, mul_left_comm, ← mul_assoc (ν _ : ℂ), Units.mul_inv, one_mul]

omit [MeasurableSpace k] [BorelSpace k] in
theorem omA_std {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : omA ν β g 1 (std ν ϖ c e) = std ν ϖ c e := by
  funext Y
  rw [← std_left (inv_mem hg) Y]
  simp [omA, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]

omit [MeasurableSpace k] [BorelSpace k] in
theorem omB_std {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : omB ν α g 1 (std ν ϖ c e) = std ν ϖ c e := by
  funext Y
  rw [← std_left (inv_mem (invT_mem_KO hg)) Y, invT_inv_val, gdet, map_inv, ← gdet, gdet_invT, inv_inv]
  simp [omB, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]

end PositivityTheory.ThKG.Std
end
end

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

open PositivityTheory.ThK.SplitLoc

local instance measFv (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

local instance scFv (v : Pl F) : SecondCountableTopology (Fv F v) := (GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)).1

theorem exists_vol (v : Pl F) : ∃ m : Measure (Fv F v), IsVol m :=
  ⟨Measure.addHaarMeasure ⟨⟨_, IsNonarchimedeanLocalField.isCompact_closedBall _ (valuation (Fv F v) 1)⟩, by
    rw [(isClopen_ball one_ne_zero).2.interior_eq]; exact ⟨0, by simp⟩⟩, inferInstance, Measure.addHaarMeasure_self⟩

def skF {n n₁ : ℕ} (h : n = n₁ + 2) (i₀ i₁ : ℕ) (j : Fin n₁) : Fin n := ⟨skip i₀ i₁ j, by
  have := j.2; unfold skip; split_ifs <;> omega⟩

theorem skF_inj {n n₁ : ℕ} (h : n = n₁ + 2) (i₀ i₁ : ℕ) : Function.Injective (skF h i₀ i₁) := fun a b e => Fin.ext (by
  have := congrArg Fin.val e
  simp only [skF, skip] at this
  split_ifs at this <;> omega)

theorem skF_cover {n n₁ : ℕ} (h : n = n₁ + 2) {j₀ j₁ : Fin n} (l : j₀.1 < j₁.1) (i : Fin n) :
    i = j₀ ∨ i = j₁ ∨ ∃ j, i = skF h j₀ j₁ j := by
  have := i.2
  have := j₁.2
  by_cases a : i.1 = j₀.1
  · exact Or.inl (Fin.ext a)
  by_cases b : i.1 = j₁.1
  · exact Or.inr (Or.inl (Fin.ext b))
  refine Or.inr (Or.inr ?_)
  by_cases c : i.1 < j₀.1
  · exact ⟨⟨i.1, by omega⟩, Fin.ext (by simp [skF, skip, c])⟩
  by_cases d : i.1 < j₁.1
  · exact ⟨⟨i.1 - 1, by omega⟩, Fin.ext (by simp only [skF, skip]; split_ifs <;> omega)⟩
  · exact ⟨⟨i.1 - 2, by omega⟩, Fin.ext (by simp only [skF, skip]; split_ifs <;> omega)⟩

theorem skF_ne {n n₁ : ℕ} (h : n = n₁ + 2) {j₀ j₁ : Fin n} (l : j₀.1 < j₁.1) (j : Fin n₁) :
    skF h j₀ j₁ j ≠ j₀ ∧ skF h j₀ j₁ j ≠ j₁ := by
  constructor <;> intro e <;> have := congrArg Fin.val e <;> simp only [skF, skip] at this <;> split_ifs at this <;> omega

theorem skF_mid (b : ℕ) : skF (rfl : b + 2 = b + 2) (0 : Fin (b + 2)).1 (Fin.last (b + 1)).1 = mid := funext fun j => Fin.ext (by
  have := j.2
  show skip 0 (b + 1) j = j + 1
  unfold skip; split_ifs <;> omega)

variable {B : Base F E}

theorem plane' (hσ : IsCMExt F E σ) {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : Fin n}
    (h : H.IsAdapted σ B X X₁ j₀ j₁) {ε : E} (hJ : ∀ i j, σ (X.J j i) = ε * X.J i j) (hε : ε * ε = 1) (w : B.P) (l : j₀.1 < j₁.1) :
    PE σ (B.τ w) X.J X₁.J (X.bas w) (X₁.bas w) H.ι (skF h.rank j₀ j₁) ∧ PX σ (B.τ w) X.J (X.bas w) H.x H.y j₀ j₁ (B.τ w ε) :=
  plane hσ h hJ hε w rfl rfl (fun _ => rfl) (skF_inj _ _ _) (skF_cover _ l) (fun e => by rw [e] at l; omega)
    (fun j => (skF_ne _ l j).1) fun j => (skF_ne _ l j).2

theorem cond_ex {ν : (Fv F v)ˣ →* ℂˣ} (h : ∃ e, CondLE (unifAt v) e ν) (hr : ¬ GlobalTheory.SplitWeil.IsUnram ν) :
    ∃ κ, condExp ν = κ + 1 ∧ CondLE (unifAt v) (κ + 1) ν ∧ ¬ CondLE (unifAt v) κ ν := by
  have m : CondLE (unifAt v) (condExp ν) ν := Nat.sInf_mem (show {e | CondLE (unifAt v) e ν}.Nonempty from h)
  have h0 : condExp ν ≠ 0 := fun e => hr fun x hx => by
    rw [e] at m
    exact m x ⟨hx, by simpa using (valuation (Fv F v)).map_sub_le hx.le (map_one _).le⟩
  obtain ⟨κ, hκ⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact ⟨κ, hκ, by rw [hκ] at m; exact m, fun e => Nat.notMem_of_lt_sInf (s := {c | CondLE (unifAt v) c ν}) (by
    show κ < condExp ν
    omega) e⟩

theorem eps_eq {m : Measure (Fv F v)} (hm : IsVol m) {ψ : AddChar (AF F) ℂ} (hψ : IsPsi (psiV ψ v)) {ν : (Fv F v)ˣ →* ℂˣ} {κ : ℕ}
    (h : condExp ν = κ + 1) (hν : CondLE (unifAt v) (κ + 1) ν) (z : ℕ) :
    gI m (psiV ψ v) ν (((unifAt v : Fv F v) ^ (κ + 1))⁻¹) * (ν (unifAt v) : ℂ) ^ (κ + 1) *
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1)) ^ z = eps ψ ν (1 - z) := by
  have q := (GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F v).1
  have q0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have g : gI m (psiV ψ v) ν (((unifAt v : Fv F v) ^ condExp ν)⁻¹) =
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ condExp ν)⁻¹ * gauss ψ ν := by
    letI : Fintype (Res (Fv F v) (condExp ν))ˣ := Fintype.ofFinite _
    rw [gI_gauss (ϖ := unifAt v) hm hψ exists_isUnif.choose_spec (by omega) (h ▸ hν), gauss]
    congr
    exact Subsingleton.elim _ _
  rw [eps, ← h, g, q, show -(condExp ν : ℤ) * (1 - z) = (condExp ν * z : ℕ) - (condExp ν : ℕ) by push_cast; ring, zpow_sub₀ q0,
    zpow_natCast, zpow_natCast, pow_mul]
  ring

theorem data {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om' R Rf} (T : IsMatched B G X om om' R Rf) (w : B.P) (hw : w.1 ∈ X.T)
    {sec} (h : IsSec σ (B.τ w) sec) {κ : ℕ} (hν : CondLE (unifAt w.1) (κ + 1) (chrW X.ν (B.τ w))) :
    ∃ ι ι' φ φ', Lin G.M B.ψ w (cW (B.τ w) (G.V.bas w) (G.W.bas w)) (cB σ (B.τ w) G.V G.W (G.V.bas w) (G.W.bas w)) ι ∧
      Lin G.M' B.ψ w (cB σ (B.τ w) G.V' G.W (G.V'.bas w) (G.W.bas w)) (fun u => -cW (B.τ w) (G.V'.bas w) (G.W.bas w) u) ι' ∧
      φ ∈ SB _ ∧ φ' ∈ SB _ ∧ ι φ = std (chrW X.ν (B.τ w)) (unifAt w.1) (κ + 1) (eA a a') ∧
      ι' φ' = std (chrW X.ν (B.τ w)) (unifAt w.1) (κ + 1) (eB a a') ∧ Rf.p w φ = Rf.p' w φ' ∧ Rf.p w φ ≠ 0 ∧
      (∀ K, IsStab B K → ∀ k ∈ kAt K (evFin F w), Acts (evFin F w) (om (k, 1)) φ φ) ∧
      ∀ K, IsStab B K → ∀ k ∈ kAt K (evFin F w), Acts (evFin F w) (om' (k, 1)) φ' φ' := by
  have inB_mem {v : Pl F} {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n : ℕ} {Y : Spc F E n} {b : GL (Fin n) (Fv F v)} (h : IsSec σ t sec) {B : Base F E} (hb : IsSplitBasis t Y.L b) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K) {k}
      (hk : k ∈ K) : StdDict.inB t b k ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) := by
    have to' : ∀ z ∈ latHat Y, (fun i => piW t (z i)) ∈ splitLat t Y.L := fun z hz => by
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, -, ha, x, hx, rfl⟩ := hz
        exact ⟨fun i => evFin F v a ⊗ₜ[F] x i, AddSubgroup.subset_closure ⟨_, ha v, x, hx, rfl⟩, funext fun i => by
          rw [Pi.smul_apply, (h.smul _ _).1, incV, (h.inc _).1]; rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a b _ _ ha hb => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem ha hb
      | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact neg_mem ha
    have fr : ∀ y ∈ latLoc F Y.L v, ∃ z ∈ latHat Y, (fun i => piW t (z i)) = splitVec t y := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hy
        refine ⟨sgl v a • incV F x, AddSubgroup.subset_closure ⟨sgl v a, map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_,
          x, hx, rfl⟩, funext fun i => by rw [Pi.smul_apply, (h.smul _ _).1, incV, (h.inc _).1, ev_sgl]; rfl⟩
        rcases eq_or_ne u v with rfl | hu
        · rwa [ev_sgl]
        · rw [show evFin F u (sgl v a) = 0 from evalV_singleFin_ne hu a]; exact zero_mem _
      | zero => exact ⟨0, zero_mem _, funext fun _ => (map_zero _).trans (map_zero _).symm⟩
      | add a b _ _ ha hb =>
        obtain ⟨p, p1, p2⟩ := ha
        obtain ⟨q, q1, q2⟩ := hb
        exact ⟨p + q, add_mem p1 q1, funext fun i => by
          rw [Pi.add_apply, map_add (f := _), congrFun p2 i, congrFun q2 i]; exact (map_add _ _ _).symm⟩
      | neg a _ ha =>
        obtain ⟨p, p1, p2⟩ := ha
        exact ⟨-p, neg_mem p1, funext fun i => by rw [Pi.neg_apply, map_neg, congrFun p2 i]; exact (map_neg _ _).symm⟩
    have key : ∀ k ∈ K, ∀ i j, (StdDict.inB t b k).1 i j ∈ 𝒪[Fv F v] := fun k hk i j => by
      obtain ⟨y, hy, e⟩ := (hb (Pi.single j 1)).1 fun i => by rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]
      obtain ⟨z, hz, e'⟩ := fr y hy
      have := hb.mem_iff.1 (to' _ (((hK k).1 hk).2 z hz).1) i
      rw [show (fun i => piW t ((mat k *ᵥ z) i)) = (mat k).map (piW t) *ᵥ fun i => piW t (z i) from
        funext fun i => RingHom.map_mulVec _ _ _ i, e', e, mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
      exact (int_iff _).1 this
    refine (mem_KO_iff _).2 ⟨key k hk, ?_⟩
    rw [show (StdDict.inB t b k)⁻¹ = StdDict.inB t b k⁻¹ by simp [StdDict.inB, mul_assoc]]
    exact key _ (inv_mem hk)
  
  have t := T.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  obtain ⟨hα, hβ, e, hcond, hram, -⟩ := PositivityTheory.ThK.SplitAsm.split_character_facts F E B X a a' w (B.τ w) t.chars
  have hS : HidaSetting a a' (unifAt w.1) (chrW X.α (B.τ w)) (chrW X.β (B.τ w)) (chrW X.ν (B.τ w)) :=
    ⟨exists_isUnif.choose_spec, hα, hβ, e, t.geo.lt, t.geo.even, hcond⟩
  obtain ⟨ι, ι', l, l', v1, v2, z⟩ := T.fin.zeta w hw
  have L := local_splitting_linear_skew hB.std h (StdDict.grams h t.geo.hV t.geo.hW) l v1
  have L' := lin_Bar hB.std h (StdDict.grams h t.geo.hV' t.geo.hW) l' v2
  obtain ⟨φ, s, a1⟩ := L.bij.2.2 (std_mem hS.unif (by omega) hν (eA a a'))
  obtain ⟨φ', s', a2⟩ := L'.bij.2.2 (std_mem hS.unif (by omega) hν (eB a a'))
  refine ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, (z φ s φ' s').2 ?_, fun h0 => ?_, fun K hK k hk => ?_, fun K hK k hk => ?_⟩
  · rw [a1, a2]; exact std_pair hS (hram hw) (by omega) hν
  · have := (z φ s 0 (zero_mem _)).1 (by rw [h0, map_zero])
    rw [a1, map_zero] at this
    refine pRam_ne (a' := a') (β := chrW X.β (B.τ w)) hS.unif (this.trans ?_)
    funext g; simp [smallP, smallF]
  · obtain ⟨j, l1, u1, g1, -⟩ := StdDict.model_alt hB t.geo.hV t.geo.hW (t.geo.hM.vac w) t.weil (t.geo.hV.bas w) (t.geo.hW.bas w)
      (ν := chrW X.ν (B.τ w)) (β := chrW X.β (B.τ w)) (MonoidHom.ext fun x => by
        rw [StdDict.chrW_div, StdDict.chrW_conj hB.cm _ t.chars.resα, StdDict.chrW_conj hB.cm _ t.chars.resβ, Chars.ν, StdDict.chrW_div, inv_div_inv])
      (StdDict.chrW_conj hB.cm _ t.chars.resβ)
    have J := local_splitting_linear_skew hB.std h (StdDict.grams h t.geo.hV t.geo.hW) l1 u1
    obtain ⟨φ₁, b1, b2, b3⟩ := g1 k (uat_closure hk.2) φ s
    rw [lin_uniq hm hB hu t.geo.hM L J s, a1, omA_std (inB_mem h (t.geo.hV.bas w) hK hk.1), ← a1, lin_uniq hm hB hu t.geo.hM L J b1] at b3
    rwa [L.bij.2.1 b1 s b3] at b2
  · obtain ⟨j, l1, u1, g1, -⟩ := StdDict.model_Bar hB t.geo.hV' t.geo.hW (t.geo.hM'.vac w) t.weil' (t.geo.hV'.bas w) (t.geo.hW.bas w)
      (δ := 1) (fun x => by rw [one_mul]; exact hu x) (one_smul _ _).symm
    have J := lin_Bar hB.std h (StdDict.grams h t.geo.hV' t.geo.hW) l1 u1
    obtain ⟨φ₁, b1, b2, b3⟩ := g1 k (uat_closure hk.2) φ' s'
    rw [lin_uniq hm hB hu t.geo.hM' L' J s', a2] at b3
    erw [omB_std (inB_mem h (t.geo.hV'.bas w) hK hk.1)] at b3
    erw [← a2] at b3
    rw [lin_uniq hm hB hu t.geo.hM' L' J b1] at b3
    rwa [L'.bij.2.1 b1 s' b3] at b2

theorem nu_data {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} (t : IsTriple B G X om om') (w : B.P) (hw : w.1 ∈ X.T) :
    (∀ x, chrW X.ν ((B.τ w).comp σ) x = (chrW X.ν (B.τ w) x)⁻¹) ∧ ∃ κ, condExp (chrW X.ν (B.τ w)) = κ + 1 ∧
      CondLE (unifAt w.1) (κ + 1) (chrW X.ν (B.τ w)) ∧ ¬ CondLE (unifAt w.1) κ (chrW X.ν (B.τ w)) := by
  obtain ⟨-, -, e, ⟨c, h1, h2⟩, hram, -⟩ := PositivityTheory.ThK.SplitAsm.split_character_facts F E B X a a' w (B.τ w) t.chars
  refine ⟨fun x => ?_, cond_ex ⟨c, e ▸ h1.div h2⟩ (hram hw)⟩
  rw [Chars.ν, StdDict.chrW_div, StdDict.chrW_div, StdDict.chrW_conj t.base.cm _ t.chars.resα, StdDict.chrW_conj t.base.cm _ t.chars.resβ, inv_div_inv, inv_div]

theorem eA_val {a a' : ℕ} (i : Fin a) : (eA a a' i).1 = i := rfl

theorem eB_val {a a' : ℕ} (i : Fin a') : (eB a a' i).1 = a + i := rfl

theorem unit_J {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (h : IsSec σ t sec) {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    IsUnit (X.J.map t) ∧ IsUnit (W.J.map t) := by
  have := StdDict.grams h hX hW
  rw [← incM_map h, ← incM_map h]
  exact ⟨this.uA, this.uB⟩

theorem stdB : StdB := by
  refine ⟨1, fun F E _ _ _ _ _ σ B a b G G₁ H H' cf e ei ev e' ei' ev' he hl he' hl' K μ hK hμ X om om' R Rf om₁ om₁' R₁ Rf₁ T T₁ w hw => ?_⟩
  have t := T.triple
  have t₁ := T₁.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  have hϖ : IsUnif (unifAt w.1) := exists_isUnif.choose_spec
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm w (B.τ w)
  obtain ⟨hc, κ, k1, k2, k3⟩ := nu_data t w hw
  obtain ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, mt, -, -, fx⟩ := data T w hw h k2
  obtain ⟨ι₁, ι₁', φ₁, φ₁', L₁, L₁', s₁, s₁', b1, b2, mt₁, ne₁, -, -⟩ := data T₁ w hw h k2
  have lt : (eB a (b + 2) 0).1 < (eB a (b + 2) (Fin.last _)).1 := by simp [eB_val]
  obtain ⟨pe', px'⟩ := plane' hB.cm (j₀ := eB a (b + 2) 0) (j₁ := eB a (b + 2) (Fin.last _)) cf.hH' (ε := -1)
    (fun i j => by rw [t.geo.hW.skew, neg_one_mul]) (by simp) w lt
  obtain ⟨pe, px⟩ := plane' hB.cm (j₀ := 0) (j₁ := Fin.last _) cf.hH (ε := 1) (fun i j => by rw [t.geo.hV'.herm, one_mul]) (by simp) w
    (by simp)
  rw [map_neg, map_one] at px'
  rw [map_one] at px
  have cv := skF_cover (rfl : b + 2 = b + 2) (j₀ := 0) (j₁ := Fin.last _) (by simp)
  rw [skF_mid] at pe cv
  have cv' := skF_cover cf.hH'.rank lt
  have nz := skF_ne cf.hH'.rank lt
  set jc := skF cf.hH'.rank (eB a (b + 2) 0) (eB a (b + 2) (Fin.last _)) with hjc
  have e1 : ev w φ = ((((GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ^ (κ + 1))⁻¹) ^ a) • φ₁ := by
    refine L₁.bij.2.1 ((hl.vac w).2 ▸ Submodule.mem_map_of_mem s) ((SB _).smul_mem _ s₁) (funext fun y => ?_)
    rw [ev0W hm hB hu h t.geo.hM t₁.geo.hM he hl L L₁ (unit_J h t.geo.hV t.geo.hW).1 (by rw [cf.eV]; exact pe_one _ _) pe' px' cv' s,
      a1, map_smul, b1]
    exact int_ev hm hϖ (skF_inj _ _ _) (fun i => Fin.ext (by simp [hjc, skF, skip, eA_val, eB_val])) _
      (fun ⟨i, hi⟩ => by have := congrArg Fin.val hi; have := i.2; simp [eA_val, eB_val] at *; omega) (fun j => (nz j).1.symm) y
  let P : Finset (Fin (b + 2) × Fin (a + (b + 2))) :=
    Finset.univ.filter fun p => p.1 = Fin.last _ ∨ p.2 = eB a (b + 2) (Fin.last _) ∧ p.1 ≠ 0
  have hP : ∀ p, p ∈ P ↔ p.1 = Fin.last _ ∨ p.2 = eB a (b + 2) (Fin.last _) ∧ p.1 ≠ 0 := fun p => by simp [P]
  have ml : ∀ i : Fin b, mid i ≠ Fin.last (b + 1) := fun i h => by have := congrArg Fin.val h; simp [mid] at this; omega
  have ei2 : Function.Injective (eB a (b + 2)) := fun _ _ h => by simpa using finSumFinEquiv.injective h
  have e2 := cone_val hm hB hu L' L₁' (hl'.vac w).2 (fun φ s y => evB hm hB hu h t.geo.hM' t₁.geo.hM' he' hl' L' L₁'
      (unit_J h t₁.geo.hV' t₁.geo.hW).1 (unit_J h t.geo.hV' t.geo.hW).2 pe px cv pe' px' cv' P hP s y) hϖ X.ν hc k2 k3 s' s₁' a2 b2 hμ
    (fx K hK) (shiftB_c h px px') (skF_inj _ _ _) ei2
    (fun i => Fin.ext (by have := i.2; show skip (a + 0) (a + (b + 1)) (a + i) = a + (i + 1)
                          unfold skip; split_ifs <;> omega))
    (fun j => (nz j).1.symm) (fun j => (nz j).2.symm) (fun i j => by simp [hP, ml, (nz j).2]) (by simp [hP]) (by simp [hP])
    (Or.inl ⟨fun j _ => by simp [hP], fun i => by simp [hP, ml, ei2.eq_iff]⟩) (fun j => (Fin.last _, eA a (b + 2) j))
    (fun _ _ h => by simpa [eA] using h) (fun p => by
      rw [hP]
      refine ⟨?_, fun ⟨x, y⟩ => ?_⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Or.inl rfl, fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi⟩
      · obtain ⟨j | j, hj⟩ := finSumFinEquiv.surjective p.2
        · exact ⟨j, Prod.ext (x.resolve_right fun x => y ⟨_, x.1.symm⟩).symm hj⟩
        · exact absurd ⟨j, hj⟩ y) ((a - (b + 2)) / 2 + 1)
  have q0 : (GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ≠ 0 := by
    rw [(GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F w).1]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
  refine ⟨φ, s, φ', s', mt, ?_, ?_⟩
  · rw [e1, map_smul]; exact smul_ne_zero (by positivity) ne₁
  · rw [e2, e1, eps_eq hm (isPsi hB.std hu) k1 k2, map_smul, map_smul, mt₁, smul_smul]
    simp

theorem stdA_gen {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'} {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')}
    (eV : G₁.V' = G.V') (hH : H.IsAdapted σ B G.V G₁.V 0 (b + 1)) (hH' : H'.IsAdapted σ B G.W G₁.W 0 (b + 1))
    {e ei ev e' ei' ev'} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e) (hl : IsEvLoc G.M G₁.M e ei ev)
    (he' : IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e') (hl' : IsEvLoc G.M' G₁.M' e' ei' ev') {K : Subgroup (UA σ G.V.J)} {μ : LocMeas K}
    (hK : IsStab B K) (hμ : μ.Is) {X om om' R Rf om₁ om₁' R₁ Rf₁} (T : IsMatched B G X om om' R Rf)
    (T₁ : IsMatched B G₁ X om₁ om₁' R₁ Rf₁) (w : B.P) (hw : w.1 ∈ X.T) :
    ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p w φ = Rf.p' w φ' ∧ Rf₁.p' w (ev' w φ') ≠ 0 ∧
      Rf₁.p w (coneF B G.M om μ w (ev w) (shiftA H H') X.ν ((b + 2 - a') / 2) φ) =
        eps B.ψ (chrW X.ν (B.τ w)) (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) • Rf₁.p' w (ev' w φ') := by
  have t := T.triple
  have t₁ := T₁.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  have hϖ : IsUnif (unifAt w.1) := exists_isUnif.choose_spec
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm w (B.τ w)
  obtain ⟨hc, κ, k1, k2, k3⟩ := nu_data t w hw
  obtain ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, mt, -, fx, -⟩ := data T w hw h k2
  obtain ⟨ι₁, ι₁', φ₁, φ₁', L₁, L₁', s₁, s₁', b1, b2, mt₁, ne₁, -, -⟩ := data T₁ w hw h k2
  have lt : (eA (b + 2) a' 0).1 < (eA (b + 2) a' (Fin.last _)).1 := by simp [eA_val]
  obtain ⟨pe', px'⟩ := plane' hB.cm (j₀ := eA (b + 2) a' 0) (j₁ := eA (b + 2) a' (Fin.last _)) hH' (ε := -1)
    (fun i j => by rw [t.geo.hW.skew, neg_one_mul]) (by simp) w lt
  obtain ⟨pe, px⟩ := plane' hB.cm (j₀ := 0) (j₁ := Fin.last _) hH (ε := 1) (fun i j => by rw [t.geo.hV.herm, one_mul]) (by simp) w
    (by simp)
  rw [map_neg, map_one] at px'
  rw [map_one] at px
  have cv := skF_cover (rfl : b + 2 = b + 2) (j₀ := 0) (j₁ := Fin.last _) (by simp)
  rw [skF_mid] at pe cv
  have cv' := skF_cover hH'.rank lt
  have nz := skF_ne hH'.rank lt
  set jc := skF hH'.rank (eA (b + 2) a' 0) (eA (b + 2) a' (Fin.last _)) with hjc
  have e1 : ev' w φ' = ((((GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ^ (κ + 1))⁻¹) ^ a') • φ₁' := by
    refine L₁'.bij.2.1 ((hl'.vac w).2 ▸ Submodule.mem_map_of_mem s') ((SB _).smul_mem _ s₁') (funext fun y => ?_)
    rw [ev0B hm hB hu h t.geo.hM' t₁.geo.hM' he' hl' L' L₁' (unit_J h t.geo.hV' t.geo.hW).1 (by rw [eV]; exact pe_one _ _) pe' px' cv' s',
      a2, map_smul, b2]
    exact int_ev hm hϖ (skF_inj _ _ _) (fun i => Fin.ext (by
        show skip 0 (b + 1) (b + i) = b + 2 + i
        unfold skip; split_ifs <;> omega)) _
      (fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi) (fun j => (nz j).2.symm) y
  let P : Finset (Fin (b + 2) × Fin (b + 2 + a')) :=
    Finset.univ.filter fun p => p.2 = eA (b + 2) a' 0 ∨ p.1 = 0 ∧ p.2 ≠ eA (b + 2) a' (Fin.last _)
  have hP : ∀ p, p ∈ P ↔ p.2 = eA (b + 2) a' 0 ∨ p.1 = 0 ∧ p.2 ≠ eA (b + 2) a' (Fin.last _) := fun p => by simp [P]
  have m0 : ∀ i : Fin b, mid i ≠ 0 := fun i h => by simpa [mid] using congrArg Fin.val h
  have ei2 : Function.Injective (eA (b + 2) a') := fun _ _ h => by simpa using finSumFinEquiv.injective h
  have e2 := cone_val hm hB hu L L₁ (hl.vac w).2 (fun φ s y => evA hm hB hu h t.geo.hM t₁.geo.hM he hl L L₁
      (unit_J h t.geo.hV t.geo.hW).1 (unit_J h t₁.geo.hV t₁.geo.hW).2 pe px cv pe' px' cv' P hP s y) hϖ X.ν hc k2 k3 s s₁ a1 b1 hμ
    (fx K hK) (shiftA_c h px px') (skF_inj _ _ _) ei2
    (fun i => Fin.ext (by have := i.2; show skip 0 (b + 1) i = i + 1
                          unfold skip; split_ifs <;> omega))
    (fun j => (nz j).1.symm) (fun j => (nz j).2.symm) (fun i j => by simp [hP, m0, (nz j).1]) (by simp [hP]) (by simp [hP, ei2.eq_iff])
    (Or.inr ⟨fun i hi => by simp [hP, hi, ei2.eq_iff], fun j => by simp [hP, m0, ei2.eq_iff]⟩) (fun j => (0, eB (b + 2) a' j))
    (fun _ _ h => by simpa [eB] using h) (fun p => by
      rw [hP]
      refine ⟨?_, fun ⟨x, y⟩ => ?_⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Or.inr ⟨rfl, fun hi => by simpa using finSumFinEquiv.injective hi⟩,
          fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi⟩
      · obtain ⟨j | j, hj⟩ := finSumFinEquiv.surjective p.2
        · exact absurd ⟨j, hj⟩ y
        · exact ⟨j, Prod.ext (x.resolve_left fun x => y ⟨_, x.symm⟩).1.symm hj⟩) ((b + 2 - a') / 2)
  have q0 : (GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ≠ 0 := by
    rw [(GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F w).1]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
  refine ⟨φ, s, φ', s', mt, ?_, ?_⟩
  · rw [e1, map_smul, ← mt₁]; exact smul_ne_zero (by positivity) ne₁
  · rw [e2, e1, eps_eq hm (isPsi hB.std hu) k1 k2, map_smul, map_smul, mt₁, smul_smul]

theorem stdA : StdA :=
  ⟨1, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf _ _ _ _ _ _ he hl he' hl' _ _ hK hμ _ _ _ _ _ _ _ _ _ T T₁ w hw => by
    simpa only [map_one, Units.val_one, one_mul] using stdA_gen cf.eV cf.hH cf.hH' he hl he' hl' hK hμ T T₁ w hw⟩

end PositivityTheory.ThKG.Std

module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.BranchModel
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SpBlkSurj
section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitD
section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitB
section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitA
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

def sp_sub (ε : Fin n → Bool) (c : Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (cnt ε c)) (Fin (cnt ε c)) ℂ :=
  M.submatrix (blk ε c) (blk ε c)

theorem sp_blk_inj (ε : Fin n → Bool) (c : Bool) : Function.Injective (blk ε c) := by
  intro a b h
  exact ((univ.filter fun i : Fin n => ε i = c).orderEmbOfFin rfl).injective h

theorem sp_blk_surj (ε : Fin n → Bool) (a : Fin n) : ∃ r, blk ε (ε a) r = a := by
  have ha : a ∈ ((univ.filter fun i : Fin n => ε i = ε a : Finset (Fin n)) : Set (Fin n)) := by
    simp
  rw [← Finset.range_orderEmbOfFin (univ.filter fun i : Fin n => ε i = ε a) rfl] at ha
  obtain ⟨r, hr⟩ := ha
  exact ⟨r, hr⟩

private theorem eps_blk (ε : Fin n → Bool) (c : Bool) (r : Fin (cnt ε c)) : ε (blk ε c r) = c := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = c) rfl r
  exact (Finset.mem_filter.mp h).2

private theorem apply_eq_zero_of_commute_Jm_of_eps_ne {ε : Fin n → Bool} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) (a b : Fin n) (h : ε a ≠ ε b) : M a b = 0 := by
  have e := congrFun (congrFun hM a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have key : M a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
    rw [mul_sub, e]; ring
  have hne : ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) ≠ 0 := by
    revert h
    cases ha : ε a <;> cases hb : ε b <;> norm_num
  exact (mul_eq_zero.mp key).resolve_right hne

private theorem image_blk_univ_eq_filter_eps (ε : Fin n → Bool) (c : Bool) :
    (univ.image (blk ε c)) = univ.filter fun i : Fin n => ε i = c := by
  ext b
  constructor
  · intro hb
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, eps_blk ε c t⟩
  · intro hb
    have hb' : ε b = c := (Finset.mem_filter.mp hb).2
    subst hb'
    obtain ⟨t, ht⟩ := sp_blk_surj ε b
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩

private theorem sp_sub_mul_of_eq_zero_off_eps_blocks {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ a b, ε a ≠ ε b → M a b = 0) (N : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (M * N) = sp_sub ε c M * sp_sub ε c N := by
  ext r s
  simp only [sp_sub, Matrix.submatrix_apply, Matrix.mul_apply]
  have hs := Finset.sum_image (s := (univ : Finset (Fin (cnt ε c)))) (g := blk ε c)
    (f := fun b => M (blk ε c r) b * N b (blk ε c s)) (fun x _ y _ h => sp_blk_inj ε c h)
  rw [image_blk_univ_eq_filter_eps] at hs
  rw [← hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  have hb' : ε b ≠ c := fun e => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩)
  rw [hM _ _ (by rw [eps_blk ε c r]; exact fun e => hb' e.symm), zero_mul]

theorem sp_sub_mul {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) (N : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (M * N) = sp_sub ε c M * sp_sub ε c N := by
  exact sp_sub_mul_of_eq_zero_off_eps_blocks c (fun a b h => apply_eq_zero_of_commute_Jm_of_eps_ne hM a b h) N

theorem sp_sub_one (ε : Fin n → Bool) (c : Bool) : sp_sub ε c 1 = 1 := by
  unfold sp_sub
  exact Matrix.submatrix_one _ (sp_blk_inj ε c)

theorem sp_sub_diag (ε : Fin n → Bool) (c : Bool) (t : Fin n → ℂ) :
    sp_sub ε c (diagonal t) = diagonal (t ∘ blk ε c) := by
  unfold sp_sub
  exact Matrix.submatrix_diagonal _ _ (sp_blk_inj ε c)

theorem sp_sub_smul (ε : Fin n → Bool) (c : Bool) (x : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (x • M) = x • sp_sub ε c M := by
  ext i j
  simp [sp_sub]

theorem sp_sub_pow {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) (k : ℕ) : sp_sub ε c (M ^ k) = sp_sub ε c M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, sp_sub_one]
  | succ k ih => rw [pow_succ', pow_succ', sp_sub_mul c hM, ih]

theorem sp_Jm_true (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by
  simp [Jm]

theorem sp_sub_Kset {ε : Fin n → Bool} (c : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    sp_sub ε c g ∈ Kset (fun _ : Fin (cnt ε c) => true) := by
  simp only [Kset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  have hzs : ∀ a b, ε a ≠ ε b → (star g) a b = 0 := by
    intro a b h
    rw [Matrix.star_apply, apply_eq_zero_of_commute_Jm_of_eps_ne hc b a (Ne.symm h), star_zero]
  refine ⟨?_, by rw [sp_Jm_true, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hst : star (sp_sub ε c g) = sp_sub ε c (star g) := by
    ext i j
    simp [sp_sub, Matrix.star_apply]
  rw [hst, ← sp_sub_mul_of_eq_zero_off_eps_blocks c hzs, Matrix.mem_unitaryGroup_iff'.mp hu, sp_sub_one]

theorem sp_sub_exp {ε : Fin n → Bool} (c : Bool) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M * Jm ε = Jm ε * M) :
    sp_sub ε c (NormedSpace.exp M) = NormedSpace.exp (sp_sub ε c M) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin (cnt ε c)) (Fin (cnt ε c)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (cnt ε c)) (Fin (cnt ε c)) ℂ) := Matrix.linftyOpNormedAlgebra
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M
  have hs' := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (sp_sub ε c M)
  have hmap : HasSum (fun k => sp_sub ε c (((k.factorial : ℂ)⁻¹) • M ^ k))
      (sp_sub ε c (NormedSpace.exp M)) := by
    refine Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => ?_
    exact Pi.hasSum.mp (Pi.hasSum.mp hs (blk ε c i)) (blk ε c j)
  simp only [sp_sub_smul, sp_sub_pow c hM] at hmap
  exact hmap.unique hs'

def sp_proj (ε : Fin n → Bool) (c : Bool) : KG ε →* KG (fun _ : Fin (cnt ε c) => true) where
  toFun k := torepK _ (sp_sub_Kset c k.2)
  map_one' := onep_KG_ext (by rw [toMK_torepK]; exact sp_sub_one ε c)
  map_mul' k k' := onep_KG_ext (by
    rw [toMK_torepK]
    exact sp_sub_mul c k.2.2 _)

theorem sp_toMK_proj (ε : Fin n → Bool) (c : Bool) (k : KG ε) :
    toMK (sp_proj ε c k) = sp_sub ε c (toMK k) := by
  exact toMK_torepK _ _

theorem sp_proj_cont (ε : Fin n → Bool) (c : Bool) : Continuous (sp_proj ε c) := by
  have hA : Continuous fun k : KG ε =>
      sp_sub ε c (((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _
  show Continuous fun k : KG ε => torepK _ (sp_sub_Kset c k.2)
  unfold torepK
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  rw [Units.continuous_iff]
  exact ⟨hA, hA.matrix_conjTranspose⟩

theorem sp_sub_inK {ε : Fin n → Bool} (c : Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    inK (fun _ : Fin (cnt ε c) => true) (sp_sub ε c X) := by
  unfold inK at hX ⊢
  obtain ⟨hG, hc⟩ := hX
  refine ⟨?_, by rw [sp_Jm_true, Matrix.mul_one, Matrix.one_mul]⟩
  unfold inG at hG ⊢
  rw [sp_Jm_true, Matrix.mul_one, Matrix.one_mul]
  ext i j
  have e := congrFun (congrFun hG (blk ε c i)) (blk ε c j)
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.zero_apply,
    Matrix.conjTranspose_apply, eps_blk] at e
  simp only [sp_sub, Matrix.add_apply, Matrix.zero_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]
  have hd : (if c = true then (1 : ℂ) else -1) ≠ 0 := by cases c <;> norm_num
  have e2 : (if c = true then (1 : ℂ) else -1) *
      (star (X (blk ε c j) (blk ε c i)) + X (blk ε c i) (blk ε c j)) = 0 := by
    linear_combination e
  exact (mul_eq_zero.mp e2).resolve_left hd

theorem sp_proj_curve {ε : Fin n → Bool} (c : Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    {γ : ℝ → KG ε} (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    toMK (sp_proj ε c (γ t)) = NormedSpace.exp ((t : ℂ) • sp_sub ε c X) := by
  rw [sp_toMK_proj, hγ, sp_sub_exp c (by rw [Matrix.smul_mul, hX.2, Matrix.mul_smul]),
    sp_sub_smul]

theorem sp_sub_single_same (ε : Fin n → Bool) (c : Bool) (r s : Fin (cnt ε c)) (x : ℂ) :
    sp_sub ε c (single (blk ε c r) (blk ε c s) x) = single r s x := by
  ext i j
  simp [sp_sub, Matrix.single_apply, (sp_blk_inj ε c).eq_iff]

theorem sp_sub_single_other (ε : Fin n → Bool) {c c' : Bool} (h : c ≠ c') (r s : Fin (cnt ε c)) (x : ℂ) :
    sp_sub ε c' (single (blk ε c r) (blk ε c s) x) = 0 := by
  ext i j
  have hne : blk ε c r ≠ blk ε c' i := fun e => h (by rw [← eps_blk ε c r, e, eps_blk ε c' i])
  simp [sp_sub, Matrix.single_apply, hne]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

section Tens

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem sp_mapL_one : mapL (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := mapL_id_id

theorem sp_star_mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) : star (mapL A B) = mapL (star A) (star B) := by
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ F
  have := FiniteDimensional.complete ℂ (E ⊗[ℂ] F)
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_mapL]

theorem sp_mapL_unitary (A : unitary (E →L[ℂ] E)) (B : unitary (F →L[ℂ] F)) :
    mapL (A : E →L[ℂ] E) (B : F →L[ℂ] F) ∈ unitary (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) := by
  rw [Unitary.mem_iff, sp_star_mapL, ← mapL_mul, ← mapL_mul, Unitary.star_mul_self_of_mem A.2,
    Unitary.star_mul_self_of_mem B.2, Unitary.mul_star_self_of_mem A.2, Unitary.mul_star_self_of_mem B.2]
  exact ⟨sp_mapL_one, sp_mapL_one⟩

def sp_tensU {G : Type*} [Monoid G] (ρ1 : G →* unitary (E →L[ℂ] E)) (ρ2 : G →* unitary (F →L[ℂ] F)) :
    G →* unitary (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) where
  toFun g := ⟨mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F), sp_mapL_unitary _ _⟩
  map_one' := Subtype.ext (by
    show mapL _ _ = 1
    rw [map_one, map_one]
    exact sp_mapL_one)
  map_mul' g h := Subtype.ext (by
    show mapL _ _ = mapL _ _ * mapL _ _
    rw [map_mul, map_mul]
    exact mapL_mul _ _ _ _)

def tensorLeftOperator : (E →L[ℂ] E) →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mapL A (1 : F →L[ℂ] F)
      map_add' := fun _ _ => mapL_add_left _ _ _
      map_smul' := fun _ _ => mapL_smul_left _ _ _ }

def tensorRightOperator : (F →L[ℂ] F) →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => mapL (1 : E →L[ℂ] E) B
      map_add' := fun _ _ => mapL_add_right _ _ _
      map_smul' := fun _ _ => mapL_smul_right _ _ _ }

theorem tensorLeftOperator_apply (A : E →L[ℂ] E) : (tensorLeftOperator : _ →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F)) A =
    mapL A (1 : F →L[ℂ] F) := rfl

theorem tensorRightOperator_apply (B : F →L[ℂ] F) : (tensorRightOperator : _ →L[ℂ] (E ⊗[ℂ] F →L[ℂ] E ⊗[ℂ] F)) B =
    mapL (1 : E →L[ℂ] E) B := rfl

theorem sp_mapL_split (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    mapL A B = mapL A (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) B := by
  rw [← mapL_mul, mul_one, one_mul]

theorem sp_tensU_cont {G : Type*} [Monoid G] [TopologicalSpace G] (ρ1 : G →* unitary (E →L[ℂ] E))
    (ρ2 : G →* unitary (F →L[ℂ] F)) (h1 : Continuous ρ1) (h2 : Continuous ρ2) :
    Continuous (sp_tensU ρ1 ρ2) := by
  have c1 : Continuous fun g => (ρ1 g : E →L[ℂ] E) := continuous_subtype_val.comp h1
  have c2 : Continuous fun g => (ρ2 g : F →L[ℂ] F) := continuous_subtype_val.comp h2
  have h : Continuous fun g => mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F) := by
    have e : (fun g => mapL (ρ1 g : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F)) =
        fun g => mapL (ρ1 g : E →L[ℂ] E) (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) (ρ2 g : F →L[ℂ] F) :=
      funext fun g => sp_mapL_split _ _
    rw [e]
    exact ((tensorLeftOperator (F := F)).continuous.comp c1).mul ((tensorRightOperator (E := E)).continuous.comp c2)
  exact Continuous.subtype_mk h _

theorem sp_mapL_hasDeriv {a : ℝ → E →L[ℂ] E} {b : ℝ → F →L[ℂ] F} {a' : E →L[ℂ] E} {b' : F →L[ℂ] F}
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    HasDerivAt (fun t => mapL (a t) (b t)) (mapL a' (1 : F →L[ℂ] F) + mapL (1 : E →L[ℂ] E) b') 0 := by
  have h1 := ((tensorLeftOperator (F := F)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
  have h2 := ((tensorRightOperator (E := E)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hb
  have h := h1.mul h2
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', tensorLeftOperator_apply, tensorRightOperator_apply,
    ha0, hb0, sp_mapL_one, mul_one, one_mul] at h
  have e : (fun t => mapL (a t) (b t)) = fun t => mapL (a t) (1 : F →L[ℂ] F) * mapL (1 : E →L[ℂ] E) (b t) :=
    funext fun t => sp_mapL_split _ _
  rw [e]
  exact h

end Tens

variable {n : ℕ} {ε : Fin n → Bool} {Λ1 : Fin (cnt ε true) → ℝ} {Λ2 : Fin (cnt ε false) → ℝ}

theorem sp_sub_add (ε : Fin n → Bool) (c : Bool) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    sp_sub ε c (X + Y) = sp_sub ε c X + sp_sub ε c Y := by
  ext; simp [sp_sub]

def sp_dτ (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T1.V ⊗[ℂ] T2.V →L[ℂ] T1.V ⊗[ℂ] T2.V) where
  toFun X := mapL (T1.dτ (sp_sub ε true X)) 1 + mapL 1 (T2.dτ (sp_sub ε false X))
  map_add' X Y := by
    simp only [sp_sub_add, map_add (f := _), mapL_add_left, mapL_add_right]
    abel
  map_smul' c X := by
    simp only [sp_sub_smul, map_smul, mapL_smul_left, mapL_smul_right, smul_add, RingHom.id_apply]

theorem sp_dτ_apply (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (X : Matrix (Fin n) (Fin n) ℂ) :
    sp_dτ T1 T2 X = mapL (T1.dτ (sp_sub ε true X)) 1 + mapL 1 (T2.dτ (sp_sub ε false X)) := rfl

theorem sp_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → KG ε}
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 :=
  onep_KG_ext (by rw [hγ 0]; simp; rfl)

def sp_rep (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) : KRep ε where
  V := T1.V ⊗[ℂ] T2.V
  instCS := FiniteDimensional.complete ℂ _
  τ := sp_tensU (T1.τ.comp (sp_proj ε true)) (T2.τ.comp (sp_proj ε false))
  cont := sp_tensU_cont _ _ (T1.cont.comp (sp_proj_cont ε true)) (T2.cont.comp (sp_proj_cont ε false))
  dτ := sp_dτ T1 T2
  hasDeriv := by
    intro X hX γ hγ
    have h1 := T1.hasDeriv _ (sp_sub_inK true hX) (fun t => sp_proj ε true (γ t))
      (sp_proj_curve true hX hγ)
    have h2 := T2.hasDeriv _ (sp_sub_inK false hX) (fun t => sp_proj ε false (γ t))
      (sp_proj_curve false hX hγ)
    have e0 := sp_curve_zero hγ
    refine sp_mapL_hasDeriv h1 h2 ?_ ?_
    · simp only [e0, map_one]; rfl
    · simp only [e0, map_one]; rfl

theorem sp_rep_op (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (k : KG ε) :
    (sp_rep T1 T2).op k = mapL (T1.op (sp_proj ε true k)) (T2.op (sp_proj ε false k)) := rfl

theorem sp_units_true (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (r s : Fin (cnt ε true))
    (x : T1.V ⊗[ℂ] T2.V) :
    (sp_rep T1 T2).units (blk ε true r) (blk ε true s) x = TensorProduct.map (kunits T1 r s) LinearMap.id x := by
  show (sp_dτ T1 T2 (single (blk ε true r) (blk ε true s) 1)) x = _
  simp [sp_dτ_apply, sp_sub_single_same, sp_sub_single_other, kunits, mapL_apply]
  rfl

theorem sp_units_false (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1)
    (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2) (r s : Fin (cnt ε false))
    (x : T1.V ⊗[ℂ] T2.V) :
    (sp_rep T1 T2).units (blk ε false r) (blk ε false s) x = TensorProduct.map LinearMap.id (kunits T2 r s) x := by
  show (sp_dτ T1 T2 (single (blk ε false r) (blk ε false s) 1)) x = _
  simp [sp_dτ_apply, sp_sub_single_same, sp_sub_single_other, kunits, mapL_apply]
  rfl

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitC
noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

theorem sp_coef_map {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] M) (ψ : N →ₗ[ℂ] ℂ) (x : M ⊗[ℂ] N) :
    TensorProduct.rid ℂ M (ψ.lTensor M (TensorProduct.map f LinearMap.id x)) =
      f (TensorProduct.rid ℂ M (ψ.lTensor M x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sp_expand {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [Module.Finite ℂ N] (x : M ⊗[ℂ] N) :
    x = ∑ i, TensorProduct.rid ℂ M (((Module.finBasis ℂ N).coord i).lTensor M x) ⊗ₜ
      (Module.finBasis ℂ N) i := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight (Module.finBasis ℂ N)).symm_apply_apply x]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp_rw [TensorProduct.equivFinsuppOfBasisRight_apply]

theorem sp_tmul_cancel {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [AddCommGroup N]
    [Module ℂ N] {w : E} (hw : ‖w‖ = 1) {y z : N} (h : w ⊗ₜ[ℂ] y = w ⊗ₜ[ℂ] z) : y = z := by
  have e := congrArg (fun u => TensorProduct.lid ℂ N
    (((innerSL ℂ w : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ).rTensor N u)) h
  simpa [hw] using e

variable {p q : ℕ} {Λ1 : Fin p → ℝ} {Λ2 : Fin q → ℝ}

theorem sp_left (T1 : KType (fun _ : Fin p => true) Λ1) {N : Type*} [AddCommGroup N] [Module ℂ N]
    [Module.Finite ℂ N] (x : T1.V ⊗[ℂ] N) (ν : Fin p → ℝ)
    (hw : ∀ r, TensorProduct.map (kunits T1 r r) LinearMap.id x = ((ν r : ℝ) : ℂ) • x)
    (hr : ∀ r s, r < s → TensorProduct.map (kunits T1 r s) LinearMap.id x = 0) :
    ∃ y : N, x = T1.w ⊗ₜ y := by
  have hcoef : ∀ i, ∃ c : ℂ,
      TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x) = c • T1.w := by
    intro i
    by_cases hm : TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x) = 0
    · exact ⟨0, by rw [hm, zero_smul]⟩
    · have h : IsKHWVec (fun _ : Fin p => true) (kunits T1) ν
          (TensorProduct.rid ℂ _ (((Module.finBasis ℂ N).coord i).lTensor _ x)) := by
        refine ⟨fun r => ?_, fun r s hrs _ => ?_⟩
        · rw [← sp_coef_map, hw r, map_smul, map_smul]
        · rw [← sp_coef_map, hr r s hrs, map_zero, map_zero]
      obtain ⟨-, c, hc⟩ := KType.hw_unique T1 hm h
      exact ⟨c, hc⟩
  choose c hc using hcoef
  refine ⟨∑ i, c i • (Module.finBasis ℂ N) i, ?_⟩
  conv_lhs => rw [sp_expand x]
  simp_rw [hc, TensorProduct.smul_tmul, TensorProduct.tmul_sum]

theorem sp_ker (T1 : KType (fun _ : Fin p => true) Λ1) (T2 : KType (fun _ : Fin q => true) Λ2)
    (x : T1.V ⊗[ℂ] T2.V) (hx0 : x ≠ 0) (ν1 : Fin p → ℝ) (ν2 : Fin q → ℝ)
    (hw1 : ∀ r, TensorProduct.map (kunits T1 r r) LinearMap.id x = ((ν1 r : ℝ) : ℂ) • x)
    (hr1 : ∀ r s, r < s → TensorProduct.map (kunits T1 r s) LinearMap.id x = 0)
    (hw2 : ∀ r, TensorProduct.map LinearMap.id (kunits T2 r r) x = ((ν2 r : ℝ) : ℂ) • x)
    (hr2 : ∀ r s, r < s → TensorProduct.map LinearMap.id (kunits T2 r s) x = 0) :
    ∃ c : ℂ, x = c • (T1.w ⊗ₜ T2.w) := by
  obtain ⟨y, rfl⟩ := sp_left T1 x ν1 hw1 hr1
  have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (TensorProduct.tmul_zero _ _)
  have h : IsKHWVec (fun _ : Fin q => true) (kunits T2) ν2 y := by
    refine ⟨fun r => ?_, fun r s hrs _ => ?_⟩
    · have e := hw2 r
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul] at e
      exact sp_tmul_cancel T1.w_norm e
    · have e := hr2 r s hrs
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_zero T2.V T1.w] at e
      exact sp_tmul_cancel T1.w_norm e
  obtain ⟨-, c, hc⟩ := KType.hw_unique T2 hy0 h
  exact ⟨c, by rw [hc, TensorProduct.tmul_smul]⟩

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

theorem sp_trace_piece {Λ' μ : Fin n → ℝ} (T : KType ε Λ') (T' : KType ε μ) (hμ : μ = Λ') (R : KRep ε)
    (S : Submodule ℂ R.V) (hS : S = ⊤) (φ : T'.V ≃ₗᵢ[ℂ] S)
    (hφ : ∀ (k : KG ε) (v : T'.V), (φ (T'.op k v) : R.V) = R.op k (φ v)) (k : KG ε) :
    LinearMap.trace ℂ T.V (T.op k : T.V →ₗ[ℂ] T.V) = LinearMap.trace ℂ R.V (R.op k : R.V →ₗ[ℂ] R.V) := by
  subst hμ hS
  obtain ⟨ψ, hψ, -, -⟩ := kType_unique T T'
  let Θ : T.V ≃ₗ[ℂ] R.V := ψ.toLinearEquiv ≪≫ₗ φ.toLinearEquiv ≪≫ₗ LinearEquiv.ofTop ⊤ rfl
  have hΘ : ∀ v, Θ (T.op k v) = R.op k (Θ v) := by
    intro v
    show ((φ (ψ (T.op k v)) : R.V)) = R.op k (φ (ψ v))
    rw [hψ, hφ]
  have e : (R.op k : R.V →ₗ[ℂ] R.V) = Θ.conj (T.op k : T.V →ₗ[ℂ] T.V) := by
    ext v
    rw [LinearEquiv.conj_apply_apply]
    show R.op k v = Θ (T.op k (Θ.symm v))
    rw [hΘ, LinearEquiv.apply_symm_apply]
  rw [e, LinearMap.trace_conj']

theorem sp_trace_of_rep {Λ' : Fin n → ℝ} (T : KType ε Λ') (R : KRep ε) (x : R.V) (hx : x ≠ 0)
    (hxw : Formalism.REAL.KHighest ε R.units Λ' x)
    (huniq : ∀ (μ : Fin n → ℝ) (y : R.V), y ≠ 0 → Formalism.REAL.KHighest ε R.units μ y → ∃ c : ℂ, y = c • x)
    (k : KG ε) :
    LinearMap.trace ℂ T.V (T.op k : T.V →ₗ[ℂ] T.V) = LinearMap.trace ℂ R.V (R.op k : R.V →ₗ[ℂ] R.V) := by
  obtain ⟨m, xs, μ, h1, h2, h3, -, -, h6⟩ := compRed n ε R
  choose c hc using fun i => huniq (μ i) (xs i) (h1 i).1 (h1 i).2
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h; apply (h1 i).1; rw [hc i, h, zero_smul]
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : x ∈ (⨆ i : Fin 0, Formalism.REAL.kSpan ε R.units (xs i)) := by rw [h3]; trivial
    rw [iSup_of_empty, Submodule.mem_bot] at this
    exact hx this
  have hm1 : m ≤ 1 := by
    by_contra hm
    have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h := h2 _ _ hne (xs ⟨0, by omega⟩) (Formalism.REAL.mem_compact_span_self (ε := ε) (F := R.units) _)
      (xs ⟨1, by omega⟩) (Formalism.REAL.mem_compact_span_self (ε := ε) (F := R.units) _)
    rw [hc, hc, inner_smul_left, inner_smul_right] at h
    refine (mul_ne_zero ((map_ne_zero _).mpr (hc0 _)) (mul_ne_zero (hc0 _) (inner_self_ne_zero.mpr hx))) h
  obtain rfl : m = 1 := by omega
  have htop : Formalism.REAL.kSpan ε R.units (xs 0) = ⊤ := by rw [← h3, iSup_unique]; rfl
  have hμ : μ 0 = Λ' := by
    funext a
    have e1 := (h1 0).2.1 a
    have e2 := hxw.1 a
    have hne : xs 0 ≠ 0 := (h1 0).1
    rw [hc 0, map_smul, e2, smul_comm] at e1
    have e3 : ((μ 0 a : ℝ) : ℂ) • xs 0 = ((Λ' a : ℝ) : ℂ) • xs 0 := by rw [hc 0]; exact e1.symm
    exact_mod_cast smul_left_injective ℂ hne e3
  obtain ⟨T', φ, -, hφ, -, -⟩ := h6 0
  exact sp_trace_piece T T' hμ R _ htop φ hφ k

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

open Matrix TensorProduct ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

theorem sp_blk_surj' (ε : Fin n → Bool) (c : Bool) (a : Fin n) (h : ε a = c) : ∃ r, blk ε c r = a := by
  subst h
  exact sp_blk_surj ε a

theorem sp_tens_ne (Λ' : Fin n → ℝ) (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) :
    (T1.w ⊗ₜ[ℂ] T2.w) ≠ 0 := by
  intro h
  have e := norm_tmul T1.w T2.w (𝕜 := ℂ)
  rw [h, norm_zero, T1.w_norm, T2.w_norm] at e
  norm_num at e

theorem sp_tens_hw (Λ' : Fin n → ℝ) (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) :
    Formalism.REAL.KHighest ε (sp_rep T1 T2).units Λ' (T1.w ⊗ₜ[ℂ] T2.w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · cases hc : ε a
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε false a hc
      rw [sp_units_false, TensorProduct.map_tmul, LinearMap.id_apply]
      show T1.w ⊗ₜ (T2.dτ (single r r 1) T2.w) = _
      rw [T2.w_wt r, TensorProduct.tmul_smul]; rfl
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε true a hc
      rw [sp_units_true, TensorProduct.map_tmul, LinearMap.id_apply]
      show (T1.dτ (single r r 1) T1.w) ⊗ₜ T2.w = _
      rw [T1.w_wt r, ← TensorProduct.smul_tmul']; rfl
  · cases hc : ε a
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε false a hc
      obtain ⟨s, rfl⟩ := sp_blk_surj' ε false b (he ▸ hc)
      have hrs : r < s := (blk_strictMono ε false).lt_iff_lt.mp hab
      rw [sp_units_false, TensorProduct.map_tmul, LinearMap.id_apply]
      show T1.w ⊗ₜ (T2.dτ (single r s 1) T2.w) = 0
      rw [T2.w_hw r s hrs rfl, TensorProduct.tmul_zero]
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε true a hc
      obtain ⟨s, rfl⟩ := sp_blk_surj' ε true b (he ▸ hc)
      have hrs : r < s := (blk_strictMono ε true).lt_iff_lt.mp hab
      rw [sp_units_true, TensorProduct.map_tmul, LinearMap.id_apply]
      show (T1.dτ (single r s 1) T1.w) ⊗ₜ T2.w = 0
      rw [T1.w_hw r s hrs rfl, TensorProduct.zero_tmul]

theorem sp_tens_uniq {Λ1 : Fin (cnt ε true) → ℝ} {Λ2 : Fin (cnt ε false) → ℝ}
    (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1) (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2)
    (μ : Fin n → ℝ) (y : (sp_rep T1 T2).V) (hy : y ≠ 0)
    (h : Formalism.REAL.KHighest ε (sp_rep T1 T2).units μ y) : ∃ c : ℂ, y = c • (T1.w ⊗ₜ[ℂ] T2.w) := by
  obtain ⟨hwt, hr⟩ := h
  refine sp_ker T1 T2 y hy (fun r => μ (blk ε true r)) (fun r => μ (blk ε false r)) ?_ ?_ ?_ ?_
  · intro r; have e := hwt (blk ε true r); exact (sp_units_true T1 T2 r r y).symm.trans e
  · intro r s hrs
    have e := hr _ _ (blk_strictMono ε true hrs) (by rw [blk_mem ε true r, blk_mem ε true s])
    exact (sp_units_true T1 T2 r s y).symm.trans e
  · intro r; have e := hwt (blk ε false r); exact (sp_units_false T1 T2 r r y).symm.trans e
  · intro r s hrs
    have e := hr _ _ (blk_strictMono ε false hrs) (by rw [blk_mem ε false r, blk_mem ε false s])
    exact (sp_units_false T1 T2 r s y).symm.trans e

theorem sp_kChar (Λ' : Fin n → ℝ) (T : KType ε Λ')
    (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) (k : KG ε) :
    kChar T k = kChar T1 (sp_proj ε true k) * kChar T2 (sp_proj ε false k) := by
  unfold kChar
  rw [sp_trace_of_rep T (sp_rep T1 T2) _ (sp_tens_ne Λ' T1 T2) (sp_tens_hw Λ' T1 T2)
    (fun μ y hy h => sp_tens_uniq T1 T2 μ y hy h) k, sp_rep_op]
  rw [show ((mapL (T1.op (sp_proj ε true k)) (T2.op (sp_proj ε false k)) : _ →L[ℂ] _) : _ →ₗ[ℂ] _) =
      TensorProduct.map (T1.op (sp_proj ε true k) : T1.V →ₗ[ℂ] T1.V)
        (T2.op (sp_proj ε false k) : T2.V →ₗ[ℂ] T2.V) from toLinearMap_mapL _ _]
  exact LinearMap.trace_tensorProduct' _ _

theorem kCharGT_of (hU : UCharStatement) : KCharGTStatement := by
  intro n ε Λ hdom T k t hk
  have hd : ∀ c, ∀ a b : Fin (cnt ε c), a < b → (fun _ => true) a = (fun _ => true) b →
      (((Λ ∘ blk ε c) b : ℤ) : ℝ) ≤ (((Λ ∘ blk ε c) a : ℤ) : ℝ) :=
    fun c a b hab _ => by exact_mod_cast antitone_blk hdom c hab.le
  obtain ⟨T1⟩ := kType_exists_of_dom (fun _ : Fin (cnt ε true) => true)
    (fun r => (((Λ ∘ blk ε true) r : ℤ) : ℝ)) (fun a => ⟨_, rfl⟩) (hd true)
  obtain ⟨T2⟩ := kType_exists_of_dom (fun _ : Fin (cnt ε false) => true)
    (fun r => (((Λ ∘ blk ε false) r : ℤ) : ℝ)) (fun a => ⟨_, rfl⟩) (hd false)
  rw [sp_kChar (fun a => (Λ a : ℝ)) T T1 T2 k,
    hU _ _ (antitone_blk hdom true) T1 (sp_proj ε true k) (t ∘ blk ε true)
      (by rw [sp_toMK_proj, hk, sp_sub_diag]),
    hU _ _ (antitone_blk hdom false) T2 (sp_proj ε false k) (t ∘ blk ε false)
      (by rw [sp_toMK_proj, hk, sp_sub_diag])]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.UCharOf
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem uChar_of (hS : SqCharStatement) : UCharStatement := by
  intro N Λ _ T k t hk
  obtain ⟨σ, hσk, hU, hK⟩ := ReciprocityTheory.ChartRestriction.DS.HW.KType.exists_rep T
  obtain ⟨lam, hlam, e, he⟩ :=
    ReciprocityTheory.ChartRestriction.DS.HW.model_equiv N (fun a => (Λ a : ℝ)) T.V σ ⊤ hU hK
  have hw : lam.w = Λ := by
    funext a
    exact_mod_cast (hlam a).symm
  let g : GL (Fin N) ℂ := ReciprocityTheory.ChartRestriction.DS.HW.torepUnit _ k.2
  have hg : (g : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t := hk
  obtain ⟨f, hf, htr⟩ := hS N lam g t hg
  let e' : T.V ≃ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam := Submodule.topEquiv.symm.trans e
  have hconj : f = e'.conj ((T.op k : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have hz := he g k.2 (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at hz
    rw [hf y, ← hz, ← hσk k]
    rfl
  have hk' : kChar T k = LinearMap.trace ℂ _ f := by
    rw [hconj, LinearMap.trace_conj']
    rfl
  rw [hk', htr, hw]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockP
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

theorem bp_filter_eq_map {n : ℕ} (ε : Fin n → Bool) (b : Bool) :
    (univ.filter fun i : Fin n => ε i = b) =
      univ.map ((univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl).toEmbedding := by
  exact (Finset.map_orderEmbOfFin_univ _ rfl).symm

theorem bp_prod_blk {M : Type*} [CommMonoid M] {n : ℕ} (ε : Fin n → Bool) (b : Bool)
    (g : Fin n → M) :
    ∏ i ∈ univ.filter (fun i : Fin n => ε i = b), g i = ∏ r, g (blk ε b r) := by
  rw [bp_filter_eq_map, Finset.prod_map]
  rfl

theorem bp_split {M : Type*} [CommMonoid M] {n : ℕ} (ε : Fin n → Bool) (F : Fin n → M) :
    ∏ i, F i = (∏ r, F (blk ε true r)) * ∏ r, F (blk ε false r) := by
  rw [← bp_prod_blk ε true F, ← bp_prod_blk ε false F,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => ε i = true)]
  congr 2

theorem bp_blk_surj {n : ℕ} (ε : Fin n → Bool) (b : Bool) (i : Fin n) (h : ε i = b) :
    ∃ r, blk ε b r = i := by
  have hi : i ∈ univ.filter fun i : Fin n => ε i = b := by simp [h]
  rw [bp_filter_eq_map] at hi
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp hi
  exact ⟨r, hr⟩

theorem bp_blk_disj {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε true)) (s : Fin (cnt ε false)) :
    blk ε true r ≠ blk ε false s := by
  intro h
  have h1 : ε (blk ε true r) = true := by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = true) rfl r
    simpa [blk] using this
  have h2 : ε (blk ε false s) = false := by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = false) rfl s
    simpa [blk] using this
  rw [h, h2] at h1
  exact Bool.false_ne_true h1

theorem bp_wden {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (t : Fin n → K) :
    wdenK ε t = wden (cnt ε true) (t ∘ blk ε true) * wden (cnt ε false) (t ∘ blk ε false) := by
  have hmem : ∀ (b : Bool) (s : Fin (cnt ε b)), ε (blk ε b s) = b := fun b s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  have hsame : ∀ (b : Bool) (r r' : Fin (cnt ε b)),
      (if blk ε b r < blk ε b r' ∧ ε (blk ε b r) = ε (blk ε b r') then t (blk ε b r) - t (blk ε b r') else 1) =
        (if r < r' then (t ∘ blk ε b) r - (t ∘ blk ε b) r' else 1) := by
    intro b r r'
    rw [hmem b r, hmem b r']
    simp only [and_true, Function.comp_apply, (blk_strictMono ε b).lt_iff_lt]
  have hother : ∀ (b b' : Bool), b ≠ b' → ∀ (r : Fin (cnt ε b)) (s : Fin (cnt ε b')),
      (if blk ε b r < blk ε b' s ∧ ε (blk ε b r) = ε (blk ε b' s) then t (blk ε b r) - t (blk ε b' s) else 1) = 1 := by
    intro b b' hbb r s
    rw [if_neg]
    rintro ⟨_, h⟩
    rw [hmem b r, hmem b' s] at h
    exact hbb h
  unfold wdenK wden
  rw [bp_split ε]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [bp_split ε]
    rw [Finset.prod_eq_one (fun s _ => hother true false (by decide) r s), mul_one]
    exact Finset.prod_congr rfl fun r' _ => hsame true r r'
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [bp_split ε]
    rw [Finset.prod_eq_one (fun s _ => hother false true (by decide) r s), one_mul]
    exact Finset.prod_congr rfl fun r' _ => hsame false r r'

theorem bp_rho {n : ℕ} (ε : Fin n → Bool) (b : Bool) : rhoK ε ∘ blk ε b = delta (cnt ε b) := by
  have hmem : ∀ s : Fin (cnt ε b), ε (blk ε b s) = b := fun s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  funext r
  simp only [Function.comp_apply, rhoK, delta, hmem r]
  have hset : (univ.filter fun j : Fin n => blk ε b r < j ∧ ε j = b) =
      (Finset.Ioi r).map ⟨blk ε b, (blk_strictMono ε b).injective⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Ioi,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hlt, hj⟩
      obtain ⟨s, hs⟩ := bp_blk_surj ε b j hj
      rw [← hs] at hlt
      exact ⟨s, (blk_strictMono ε b).lt_iff_lt.mp hlt, hs⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(blk_strictMono ε b) hs, hmem s⟩
  rw [hset, Finset.card_map, Fin.card_Ioi]
  have := r.isLt
  omega

theorem bp_alt_eq_sum {K : Type*} [Field K] (n : ℕ) (a : Fin n → ℤ) (t : Fin n → K) :
    alt n a t = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, t (σ i) ^ a i := by
  unfold alt
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [Matrix.of_apply]

def bp_e {n : ℕ} (ε : Fin n → Bool) : Fin (cnt ε true) ⊕ Fin (cnt ε false) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (blk ε true) (blk ε false)) (by
    constructor
    · rintro (r | r) (s | s) h
      · exact congrArg Sum.inl ((blk_strictMono ε true).injective h)
      · exact absurd h (bp_blk_disj ε r s)
      · exact absurd h.symm (bp_blk_disj ε s r)
      · exact congrArg Sum.inr ((blk_strictMono ε false).injective h)
    · intro i
      cases hb : ε i
      · obtain ⟨r, hr⟩ := bp_blk_surj ε false i hb
        exact ⟨Sum.inr r, hr⟩
      · obtain ⟨r, hr⟩ := bp_blk_surj ε true i hb
        exact ⟨Sum.inl r, hr⟩)

theorem bp_e_inl {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε true)) :
    bp_e ε (Sum.inl r) = blk ε true r := rfl

theorem bp_e_inr {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε false)) :
    bp_e ε (Sum.inr r) = blk ε false r := rfl

theorem bp_phi_inl {n : ℕ} (ε : Fin n → Bool) (α : Equiv.Perm (Fin (cnt ε true)))
    (β : Equiv.Perm (Fin (cnt ε false))) (r : Fin (cnt ε true)) :
    (bp_e ε).permCongr (Equiv.Perm.sumCongr α β) (blk ε true r) = blk ε true (α r) := by
  rw [Equiv.permCongr_apply, ← bp_e_inl ε r, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inl, bp_e_inl]

theorem bp_phi_inr {n : ℕ} (ε : Fin n → Bool) (α : Equiv.Perm (Fin (cnt ε true)))
    (β : Equiv.Perm (Fin (cnt ε false))) (r : Fin (cnt ε false)) :
    (bp_e ε).permCongr (Equiv.Perm.sumCongr α β) (blk ε false r) = blk ε false (β r) := by
  rw [Equiv.permCongr_apply, ← bp_e_inr ε r, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inr, bp_e_inr]

theorem bp_num {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K) :
    numK ε a t = alt (cnt ε true) (a ∘ blk ε true) (t ∘ blk ε true) *
      alt (cnt ε false) (a ∘ blk ε false) (t ∘ blk ε false) := by
  classical
  have hmem : ∀ (b : Bool) (s : Fin (cnt ε b)), ε (blk ε b s) = b := fun b s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  rw [bp_alt_eq_sum, bp_alt_eq_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  unfold numK
  symm
  refine Finset.sum_bij (fun p _ => (bp_e ε).permCongr (Equiv.Perm.sumCongr p.1 p.2)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    obtain ⟨x, rfl⟩ := (bp_e ε).surjective i
    rcases x with r | r
    · rw [bp_e_inl, bp_phi_inl, hmem, hmem]
    · rw [bp_e_inr, bp_phi_inr, hmem, hmem]
  · intro p _ q _ h
    exact Equiv.Perm.sumCongrHom_injective ((Equiv.permCongr (bp_e ε)).injective h)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hmaps : Set.MapsTo ((bp_e ε).symm.permCongr σ) (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨r, rfl⟩
      obtain ⟨r', hr'⟩ := bp_blk_surj ε true (σ (blk ε true r)) (by rw [hσ, hmem])
      refine ⟨r', ?_⟩
      rw [Equiv.permCongr_apply, Equiv.symm_symm, bp_e_inl, ← hr', ← bp_e_inl, Equiv.symm_apply_apply]
    obtain ⟨q, hq⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    refine ⟨q, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    have hq' : Equiv.Perm.sumCongr q.1 q.2 = (bp_e ε).symm.permCongr σ := hq
    rw [hq']
    ext i
    simp [Equiv.permCongr_apply]
  · intro p _
    rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      bp_split ε (fun i => t (((bp_e ε).permCongr (Equiv.Perm.sumCongr p.1 p.2)) i) ^ a i)]
    simp only [bp_phi_inl, bp_phi_inr, Function.comp_apply, Units.val_mul, Int.cast_mul]
    ring

theorem blockComb : BlockCombStatement := by
  intro K _ n ε a t
  exact ⟨bp_wden ε t, bp_num ε a t, bp_rho ε⟩

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem weyl : WeylStatement :=
  weyl_of (kCharGT_of (uChar_of sqChar)) blockComb

end ReciprocityTheory.ChartRestriction.TR.Weyl

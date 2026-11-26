module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.RelOpCurve
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRedOf
noncomputable section

open Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma inUJ_of_mem_K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  simp only [Kset, inUJ, Set.mem_setOf_eq] at *
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]

def cr2K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_K ε hg⟩, hg⟩

lemma KRep.actM_units {ε : Fin n → Bool} (R : KRep ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : R.V) :
    actM R.units X v = R.dτ X v := by
  simp only [KRep.units, actM]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  have h : ∀ a b, Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) := by
    intro a b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_smul]
  simp [LinearMap.sum_apply, ContinuousLinearMap.sum_apply]

def compactRepOfUnitaryDifferential (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (τ : KG ε →* unitary (H →L[ℂ] H)) (hτ : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
      (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
        HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0) : KRep ε :=
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  { V := H, τ := τ, cont := hτ, dτ := dτ, hasDeriv := hd }

theorem uRepCompRed_of (hU : URepHomStatement) (hD : DerivExistsStatement)
    (hR : KRepRelStatement) (hC : CompRedStatement) : URepCompRedStatement := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨τ, hτc, hτ⟩ := hU n ε H σ hσ
  obtain ⟨dτ, hd⟩ := hD n ε H τ hτc
  obtain ⟨hRel, hUnit⟩ := hR n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  obtain ⟨m, x, μ, h1, h2, h3, h4, h5, h6⟩ := hC n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  refine ⟨(compactRepOfUnitaryDifferential ε H τ hτc dτ hd).units, hRel, hUnit, ?_, m, x, μ, h1, h2, h3, ?_⟩
  · intro X hX v
    have hK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t =>
      (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (Formalism.REAL.inK_smul_real ε hX t)
    have hγ : ∀ t : ℝ, toMK (cr2K ε (hK t)) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hder := hd X hX (fun t => cr2K ε (hK t)) hγ
    erw [KRep.actM_units (compactRepOfUnitaryDifferential ε H τ hτc dτ hd) X v]
    have hfun : (fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • X))) v) =
        fun t : ℝ => (((τ (cr2K ε (hK t)) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) v := by
      funext t; rw [hτ, hγ]
    rw [hfun]
    have h2 := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
    exact h2
  · refine ⟨?_, ?_⟩
    · intro i g hg v hv
      have := h5 i (cr2K ε hg) v hv
      simp only [KRep.op, compactRepOfUnitaryDifferential] at this
      have e : σ g = ((τ (cr2K ε hg) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
        rw [hτ]; rfl
      rw [e]; exact this
    · intro i
      obtain ⟨T, φ, -, hop, hdτ, hw⟩ := h6 i
      refine ⟨T, φ, ?_, ?_, hw⟩
      · intro k v
        have e : σ (toMK k) = ((τ k : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := (hτ k).symm
        rw [e]; exact hop k v
      · intro a b hab v
        have hc : Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
          show Matrix.single a b (1 : ℂ) * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.single a b 1
          ext i j
          rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
          by_cases h : a = i ∧ b = j
          · obtain ⟨rfl, rfl⟩ := h; simp [hab]
          · simp [h]
        exact hdτ _ hc v

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Stable
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem KRep.op_curve {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by
  set A := R.dτ X with hA
  have hmulK : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have honeK : toMK (1 : KG ε) = 1 := rfl
  have hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    rw [hmulK, hγ, hγ, hγ, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hop : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b
    simp [KRep.op]
  have hγ0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ, honeK]
    simp
  have hd0 : HasDerivAt (fun t => R.op (γ t)) A 0 := R.hasDeriv X hX γ hγ
  have hd : ∀ s : ℝ, HasDerivAt (fun t => R.op (γ t)) (R.op (γ s) * A) s := by
    intro s
    have h1 : HasDerivAt (fun t => R.op (γ (t - s))) A s :=
      HasDerivAt.comp_sub_const (f := fun t => R.op (γ t)) s s (by rwa [sub_self])
    refine (h1.const_mul (R.op (γ s))).congr_of_eventuallyEq ?_
    filter_upwards with u
    rw [← hop, ← hγadd, add_sub_cancel]
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A))
      (NormedSpace.exp (s • -A) * -A) s := fun s => hasDerivAt_exp_smul_const (-A) s
  have hcomm : ∀ s : ℝ, Commute A (NormedSpace.exp (s • -A)) := fun s =>
    (((Commute.refl A).neg_right).smul_right s).exp_right
  have hh : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hE s)
    have key : R.op (γ s) * A * NormedSpace.exp (s • -A) +
        R.op (γ s) * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, (hcomm s).eq, mul_neg, mul_neg, add_neg_cancel]
    rw [key] at this
    exact this
  have hconst : ∀ u : ℝ, R.op (γ u) * NormedSpace.exp (u • -A) = 1 := by
    intro u
    have := is_const_of_deriv_eq_zero (f := fun u => R.op (γ u) * NormedSpace.exp (u • -A))
      (fun s => (hh s).differentiableAt) (fun s => (hh s).deriv) u 0
    rw [this]
    simp [hγ0, KRep.op]
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hk : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
        0 s := by
      intro s
      have := (hE s).mul (hasDerivAt_exp_smul_const A s)
      have hcF : Commute (NormedSpace.exp (s • A)) A := ((Commute.refl A).smul_left s).exp_left
      have key : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
          NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
        rw [mul_assoc, neg_mul, mul_neg, hcF.eq, neg_add_cancel]
      rw [key] at this
      exact this
    have := is_const_of_deriv_eq_zero
      (f := fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
      (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    rw [this]
    simp
  calc R.op (γ t) = R.op (γ t) * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by
        rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]
    _ = NormedSpace.exp ((t : ℂ) • A) := by rw [Complex.coe_smul]

theorem KRep.op_eq_exp {ε : Fin n → Bool} (R : KRep ε) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ R.op k = NormedSpace.exp (R.dτ Y) := by
  obtain ⟨Y, hY, hk⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := by
    apply onep_KG_ext
    rw [hγ 1, hk, Complex.ofReal_one, one_smul]
  refine ⟨Y, hY, ?_⟩
  rw [← h1, R.op_curve hY γ hγ 1, Complex.ofReal_one, one_smul]

theorem KRep.dτ_stable_of_stable {ε : Fin n → Bool} (R : KRep ε)
    (W : Submodule ℂ R.V) (hW : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, R.dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := R.hasDeriv X hX γ hγ
    let L : (R.V →L[ℂ] R.V) →L[ℝ] R.V := (ContinuousLinearMap.apply ℂ R.V v).restrictScalars ℝ
    have hdv : HasDerivAt (fun t => R.op (γ t) v) (R.dτ X v) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd
    have hclosed : IsClosed (W : Set R.V) := W.closed_of_finiteDimensional
    refine hclosed.mem_of_tendsto hdv.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  have hX1 : inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    · rw [sub_mul, mul_sub, single_mul_Jm_comm hab, single_mul_Jm_comm hab.symm]
  have hX2 : inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm,
        Matrix.single_neg]
    · rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, single_mul_Jm_comm hab,
        single_mul_Jm_comm hab.symm]
  have hI : -Complex.I / 2 * Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  have hdec : Matrix.single a b (1 : ℂ) =
      (1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) +
        (-Complex.I / 2) • (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    rw [smul_smul, hI]
    module
  rw [hdec, map_add (f := _), map_smul, map_smul, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply]
  exact W.add_mem (W.smul_mem _ (hK _ hX1 v hv)) (W.smul_mem _ (hK _ hX2 v hv))

theorem KRep.stable_of_dτ_stable {ε : Fin n → Bool} (R : KRep ε) (W : Submodule ℂ R.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W) :
    ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := by
  intro k v hv
  obtain ⟨Y, hY, hk⟩ := R.op_eq_exp k
  rw [hk]
  refine exp_mem_of_stable W (R.dτ Y) ?_ v hv
  intro w hw
  rw [Matrix.matrix_eq_sum_single Y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, FunLike.coe_sum, Finset.sum_apply]
  refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab w hw)
  · rw [inK_entry_eq_zero hY hab, Matrix.single_zero, map_zero]
    exact W.zero_mem

theorem kRepStable : KRepStableStatement := by
  intro n ε R W
  constructor
  · intro h a b hab x hx
    exact R.dτ_stable_of_stable W h a b hab x hx
  · intro h
    exact R.stable_of_dτ_stable W (fun a b hab x hx => h a b hab x hx)

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.EntryEqZeroOfComm
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

namespace PieceCon

variable {n : ℕ}

theorem entry_eq_zero_of_comm {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y * Jm ε = Jm ε * Y) {a b : Fin n} (hab : ε a ≠ ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha, hb] at h; simp only [Bool.false_eq_true, if_false, if_true] at h
    linear_combination h / 2
  · rw [ha, hb] at h; simp only [Bool.false_eq_true, if_false, if_true] at h
    linear_combination -h / 2
  · exact absurd (ha.trans hb.symm) hab

theorem single_block {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) :
    ∀ i j, ε i ≠ ε j → Matrix.single a b (1 : ℂ) i j = 0 := by
  intro i j hij
  rw [Matrix.single_apply]
  split_ifs with h
  · exact absurd (h.1 ▸ h.2 ▸ hab) hij
  · rfl

def blockPart (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := Matrix.of fun a b => if ε a = ε b then X a b else 0
  map_add' X Y := by
    ext a b; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext a b; simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem blockPart_eq {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ a b, ε a ≠ ε b → X a b = 0) : blockPart ε X = X := by
  ext a b
  simp only [blockPart, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (hX a b h).symm

section Cut

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def cut (W : Submodule ℂ V) : (V →L[ℂ] V) →L[ℂ] (W →L[ℂ] W) :=
  (ContinuousLinearMap.compL ℂ W V W W.orthogonalProjectionOnto).comp
    ((ContinuousLinearMap.compL ℂ W V V).flip W.subtypeL)

theorem cut_apply (W : Submodule ℂ V) (A : V →L[ℂ] V) (v : W) :
    cut W A v = W.orthogonalProjectionOnto (A v) := rfl

theorem cut_apply_mem (W : Submodule ℂ V) (A : V →L[ℂ] V) (v : W) (h : A v ∈ W) :
    ((cut W A v : W) : V) = A v := by
  rw [cut_apply]
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := W) ⟨A v, h⟩)

theorem cut_mul (W : Submodule ℂ V) (A B : V →L[ℂ] V) (hB : ∀ v ∈ W, B v ∈ W) :
    cut W (A * B) = cut W A * cut W B := by
  ext1 v
  show cut W (A * B) v = cut W A (cut W B v)
  rw [cut_apply, cut_apply, cut_apply_mem W B v (hB v v.2)]
  rfl

theorem cut_one (W : Submodule ℂ V) : cut W 1 = 1 := by
  ext1 v
  apply Subtype.ext
  rw [cut_apply_mem W 1 v v.2]
  rfl

end Cut

section Piece

variable {ε : Fin n → Bool} (R : KRep ε)

theorem op_mul (k k' : KG ε) : R.op (k * k') = R.op k * R.op k' := by
  simp [KRep.op, map_mul]

theorem op_one : R.op 1 = 1 := by
  simp [KRep.op, map_one]

theorem op_inv (k : KG ε) : R.op k⁻¹ = star (R.op k) := by
  simp [KRep.op, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]

theorem dτ_mem {W : Submodule ℂ R.V} (hW : Formalism.REAL.KStable ε R.units W)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : ∀ a b, ε a ≠ ε b → X a b = 0) :
    ∀ v ∈ W, R.dτ X v ∈ W := by
  intro v hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.matrix_eq_sum_single X, map_sum, _root_.sum_apply]
  refine W.sum_mem fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, _root_.sum_apply]
  refine W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · have e : Matrix.single a b (X a b) = X a b • Matrix.single a b 1 := by
      ext i j; simp [Matrix.single_apply]
    rw [e, map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab v hv)
  · have e : Matrix.single a b (X a b) = 0 := by
      rw [hX a b hab]; ext i j; simp [Matrix.single_apply]
    rw [e, map_zero, _root_.zero_apply]
    exact W.zero_mem

variable {W : Submodule ℂ R.V} (hτ : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W)
include hτ

theorem star_cut (k : KG ε) : star (cut W (R.op k)) = cut W (R.op k⁻¹) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [Submodule.coe_inner, Submodule.coe_inner, cut_apply_mem W _ u (hτ _ u u.2),
    cut_apply_mem W _ v (hτ _ v v.2), op_inv, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem cut_mem_unitary (k : KG ε) : cut W (R.op k) ∈ unitary (W →L[ℂ] W) := by
  rw [Unitary.mem_iff, star_cut R hτ, ← cut_mul W _ _ (hτ k), ← cut_mul W _ _ (hτ k⁻¹),
    ← op_mul, ← op_mul, inv_mul_cancel, mul_inv_cancel, op_one, cut_one]
  exact ⟨rfl, rfl⟩

def tauW : KG ε →* unitary (W →L[ℂ] W) where
  toFun k := ⟨cut W (R.op k), cut_mem_unitary R hτ k⟩
  map_one' := Subtype.ext (by simp only [op_one, cut_one]; rfl)
  map_mul' k k' := Subtype.ext (by
    simp only [op_mul]
    exact cut_mul W _ _ (hτ k'))

theorem tauW_coe (k : KG ε) : ((tauW R hτ k : unitary (W →L[ℂ] W)) : W →L[ℂ] W) = cut W (R.op k) :=
  rfl

theorem tauW_cont : Continuous (tauW R hτ) := by
  have h : Continuous fun k : KG ε => cut W (R.op k) :=
    (cut W).continuous.comp (continuous_subtype_val.comp R.cont)
  exact h.subtype_mk _

end Piece

end PieceCon


open PieceCon in
def pieceKType {n : ℕ} {ε : Fin n → Bool} (R : KRep ε)
    (hS : KRepStableStatement) (hR : KRepRelStatement) (μ : Fin n → ℝ) (x : R.V) (hx : x ≠ 0)
    (hhi : Formalism.REAL.KHighest ε R.units μ x) : KType ε μ :=
  let W := Formalism.REAL.kSpan ε R.units x
  have hK : Formalism.REAL.KStable ε R.units W := Formalism.REAL.isCompactInvariant_compactSpan x
  have hτ : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := (hS n ε R W).mpr hK
  have hxW : x ∈ W := Formalism.REAL.mem_compactSpan x
  { V := W
    τ := tauW R hτ
    cont := tauW_cont R hτ
    irred := by
      intro W' hW'
      set S : Submodule ℂ R.V := W'.map W.subtype with hSdef
      have hSτ : ∀ k : KG ε, ∀ v ∈ S, R.op k v ∈ S := by
        intro k v hv
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
        refine Submodule.mem_map.mpr ⟨(tauW R hτ k : W →L[ℂ] W) u, hW' k u hu, ?_⟩
        rw [tauW_coe]
        exact cut_apply_mem W _ u (hτ k u u.2)
      have hSK : Formalism.REAL.KStable ε R.units S := (hS n ε R S).mp hSτ
      have hle : S ≤ W := Submodule.map_subtype_le W W'
      have hinj := Submodule.map_injective_of_injective W.injective_subtype
      rcases Formalism.REAL.kIrr R.V n ε R.units μ x inferInstance (hR n ε R).1 (hR n ε R).2 hhi S hle hSK
        with h | h
      · left
        apply hinj
        rw [Submodule.map_bot]
        exact h
      · right
        apply hinj
        rw [Submodule.map_subtype_top]
        exact h
    dτ := (cut W).toLinearMap ∘ₗ R.dτ ∘ₗ blockPart ε
    hasDeriv := by
      intro X hX γ hγ
      have hb : blockPart ε X = X := blockPart_eq fun a b h => entry_eq_zero_of_comm hX.2 h
      have hd := ((cut W).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (R.hasDeriv X hX γ hγ)
      show HasDerivAt (fun t => cut W (R.op (γ t))) (cut W (R.dτ (blockPart ε X))) 0
      rw [hb]
      simpa [Function.comp_def] using hd
    w := ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, W.smul_mem _ hxW⟩
    w_norm := by
      rw [Submodule.coe_norm]
      show ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    w_wt := by
      intro a
      apply Subtype.ext
      have hb : blockPart ε (Matrix.single a a 1) = Matrix.single a a 1 :=
        blockPart_eq (single_block rfl)
      show ((cut W (R.dτ (blockPart ε (Matrix.single a a 1))) _ : W) : R.V) = _
      rw [hb, cut_apply_mem W _ _ (dτ_mem R hK (single_block rfl) _ (W.smul_mem _ hxW))]
      simp only [map_smul, Submodule.coe_smul]
      have h1 : R.dτ (Matrix.single a a 1) x = ((μ a : ℝ) : ℂ) • x := hhi.1 a
      rw [h1, smul_comm]
    w_hw := by
      intro a b hab hε
      apply Subtype.ext
      have hb : blockPart ε (Matrix.single a b 1) = Matrix.single a b 1 :=
        blockPart_eq (single_block hε)
      show ((cut W (R.dτ (blockPart ε (Matrix.single a b 1))) _ : W) : R.V) = _
      rw [hb, cut_apply_mem W _ _ (dτ_mem R hK (single_block hε) _ (W.smul_mem _ hxW))]
      simp only [map_smul, Submodule.coe_zero]
      have h1 : R.dτ (Matrix.single a b 1) x = 0 := hhi.2 a b hab hε
      rw [h1, smul_zero] }


open PieceCon in
theorem kRepPiece_of (hR : KRepRelStatement) (hS : KRepStableStatement) : KRepPieceStatement := by
  intro n ε R μ x hx hhi
  set W := Formalism.REAL.kSpan ε R.units x with hWdef
  have hK : Formalism.REAL.KStable ε R.units W := Formalism.REAL.isCompactInvariant_compactSpan x
  have hτ : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := (hS n ε R W).mpr hK
  refine ⟨pieceKType R hS hR μ x hx hhi, LinearIsometryEquiv.refl ℂ W, ?_, ?_, ?_⟩
  · intro k v
    change ↥W at v
    exact cut_apply_mem W _ v (hτ k v v.2)
  · intro X hX v
    change ↥W at v
    have hb : ∀ a b, ε a ≠ ε b → X a b = 0 := fun a b h => entry_eq_zero_of_comm hX h
    show ((cut W (R.dτ (blockPart ε X)) v : W) : R.V) = R.dτ X v
    rw [blockPart_eq hb]
    exact cut_apply_mem W _ v (dτ_mem R hK hb v v.2)
  · rfl

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Decomp
noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem finrank_eq_sum_of_orth {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {m : ℕ} (A : Fin m → Submodule ℂ V)
    (horth : ∀ i i', i ≠ i' → ∀ y ∈ A i, ∀ z ∈ A i', ⟪y, z⟫_ℂ = 0) (htop : (⨆ i, A i) = ⊤) :
    Module.finrank ℂ V = ∑ i, Module.finrank ℂ (A i) := by
  classical
  have hOF : OrthogonalFamily ℂ (fun i => A i) fun i => (A i).subtypeₗᵢ :=
    fun i j hij v w => horth i j hij _ v.2 _ w.2
  have hind : iSupIndep A := by
    first
      | exact hOF.independent
      | exact hOF.iSupIndep
  have hint : DirectSum.IsInternal A := by
    first
      | exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).mpr ⟨hind, htop⟩
      | exact (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top A).mpr ⟨hind, htop⟩
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun i => Module.finBasis ℂ (A i)),
    Fintype.card_sigma]
  simp

theorem compRed_of (hR : KRepRelStatement) (hS : KRepStableStatement) (hP : KRepPieceStatement) :
    CompRedStatement := by
  intro n ε R
  obtain ⟨hrel, hunit⟩ := hR n ε R
  obtain ⟨m, x, μ, hx, horth, htop⟩ :=
    Formalism.REAL.kDecomp R.V n ε R.units ⊤ inferInstance hrel hunit (fun a b _ v _ => Submodule.mem_top)
  refine ⟨m, x, μ, fun i => ⟨(hx i).2.1, (hx i).2.2⟩, horth, htop, ?_, ?_, ?_⟩
  · exact finrank_eq_sum_of_orth _ horth htop
  · intro i k v hv
    exact (hS n ε R _).mpr (Formalism.REAL.isCompactInvariant_compactSpan (x i)) k v hv
  · intro i
    obtain ⟨T, φ, h1, h2, h3⟩ := hP n ε R (μ i) (x i) (hx i).2.1 (hx i).2.2
    exact ⟨T, φ, φ.toLinearEquiv.finrank_eq, h1, h2, h3⟩

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivK
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Blocks
noncomputable section

open Matrix Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def blkP (ε : Fin n → Bool) (s : Bool) : ℕ := Fintype.card {a // ε a = s}

def blkE (ε : Fin n → Bool) (s : Bool) : Fin (blkP ε s) ≃ {a // ε a = s} :=
  (Fintype.equivFin _).symm

def blkSig (ε : Fin n → Bool) : (Σ s : Bool, Fin (blkP ε s)) ≃ Fin n :=
  (Equiv.sigmaCongrRight (blkE ε)).trans (Equiv.sigmaFiberEquiv ε)

lemma ε_blkSig (ε : Fin n → Bool) (s : Bool) (i : Fin (blkP ε s)) : ε (blkSig ε ⟨s, i⟩) = s :=
  (blkE ε s i).2

def blkRes (ε : Fin n → Bool) (s : Bool) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ where
  toFun X := Matrix.of fun i j => X (blkSig ε ⟨s, i⟩) (blkSig ε ⟨s, j⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma blkRes_apply (ε : Fin n → Bool) (s : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin (blkP ε s)) : blkRes ε s X i j = X (blkSig ε ⟨s, i⟩) (blkSig ε ⟨s, j⟩) := rfl

def blkDiag (ε : Fin n → Bool) :
    (∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (blkSig ε)).toRingEquiv.toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun s => Fin (blkP ε s)) ℂ)

lemma blkDiag_apply (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ)
    (x y : Σ s : Bool, Fin (blkP ε s)) :
    blkDiag ε v (blkSig ε x) (blkSig ε y) = blockDiagonal' v x y := by
  simp [blkDiag, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

lemma continuous_blkDiag (ε : Fin n → Bool) : Continuous (blkDiag ε) := by
  let L : (∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := blkDiag ε
      map_add' := map_add _
      map_smul' := fun c v => by
        ext i j
        obtain ⟨x, rfl⟩ := (blkSig ε).surjective i
        obtain ⟨y, rfl⟩ := (blkSig ε).surjective j
        rcases x with ⟨s, a⟩
        rcases y with ⟨t, b⟩
        simp only [RingHom.id_apply, Matrix.smul_apply, blkDiag_apply]
        by_cases hst : s = t
        · subst hst
          simp [Matrix.blockDiagonal'_apply_eq]
        · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hst] }
  exact L.continuous_of_finiteDimensional

lemma commJ_iff (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M * Jm ε = Jm ε * M ↔ ∀ a b, ε a ≠ ε b → M a b = 0 := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h1 ⊢ <;>
      first | exact h1 | linear_combination h1 / 2 | linear_combination -h1 / 2
  · intro h
    ext a b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]

lemma blkDiag_commJ (ε : Fin n → Bool)
    (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    blkDiag ε v * Jm ε = Jm ε * blkDiag ε v := by
  refine (commJ_iff ε _).mpr fun a b hab => ?_
  obtain ⟨⟨s, i⟩, rfl⟩ := (blkSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (blkSig ε).surjective b
  rw [ε_blkSig ε s i, ε_blkSig ε t j] at hab
  rw [blkDiag_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hab]

lemma eq_blkDiag {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) :
    X = blkDiag ε (fun s => blkRes ε s X) := by
  ext a b
  obtain ⟨⟨s, i⟩, rfl⟩ := (blkSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (blkSig ε).surjective b
  rw [blkDiag_apply]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.blockDiagonal'_apply_eq, blkRes_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hst]
    refine (commJ_iff ε X).mp hX _ _ ?_
    rw [ε_blkSig ε s i, ε_blkSig ε t j]
    exact hst

lemma blkDiag_conjTranspose (ε : Fin n → Bool)
    (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    (blkDiag ε v)ᴴ = blkDiag ε (fun s => (v s)ᴴ) := by
  simp [blkDiag, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex,
    Matrix.blockDiagonal'_conjTranspose]

lemma blkDiag_Kset (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ)
    (hv : ∀ s, v s * (v s)ᴴ = 1) : blkDiag ε v ∈ Kset ε := by
  refine ⟨?_, blkDiag_commJ ε v⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, blkDiag_conjTranspose, ← map_mul]
  have : (v * fun s => (v s)ᴴ) = 1 := by
    funext s
    exact hv s
  rw [this, map_one]

def embM (ε : Fin n → Bool) (s : Bool) (A : Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  blkDiag ε (Pi.mulSingle (M := fun s => Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) s A)

lemma Jm_allPos (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by
  simp [Jm]

lemma embM_Kset (ε : Fin n → Bool) (s : Bool) {A : Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ}
    (hA : A ∈ Kset (fun _ : Fin (blkP ε s) => true)) : embM ε s A ∈ Kset ε := by
  refine blkDiag_Kset ε _ fun t => ?_
  by_cases hts : t = s
  · subst hts
    rw [Pi.mulSingle_eq_same]
    have := hA.1
    rwa [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
  · rw [Pi.mulSingle_eq_of_ne hts]
    simp

def blkK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩, by
      show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]⟩, hg⟩

def blkEmbed (ε : Fin n → Bool) (s : Bool) : KG (fun _ : Fin (blkP ε s) => true) →* KG ε where
  toFun h := blkK ε (embM_Kset ε s h.2)
  map_one' := by
    apply onep_KG_ext
    show embM ε s 1 = 1
    rw [embM, Pi.mulSingle_one, map_one]
  map_mul' h h' := by
    apply onep_KG_ext
    show embM ε s (toMK h * toMK h') = embM ε s (toMK h) * embM ε s (toMK h')
    rw [embM, embM, embM, ← map_mul, Pi.mulSingle_mul]

lemma toMK_blkEmbed (ε : Fin n → Bool) (s : Bool) (h : KG (fun _ : Fin (blkP ε s) => true)) :
    toMK (blkEmbed ε s h) = embM ε s (toMK h) := rfl

lemma continuous_blkEmbed (ε : Fin n → Bool) (s : Bool) : Continuous (blkEmbed ε s) := by
  have hmk : Continuous (fun h : KG (fun _ : Fin (blkP ε s) => true) => toMK h) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hemb : Continuous fun h : KG (fun _ : Fin (blkP ε s) => true) => embM ε s (toMK h) :=
    (continuous_blkDiag ε).comp ((continuous_mulSingle s).comp hmk)
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact Units.continuous_iff.mpr ⟨hemb, hemb.matrix_conjTranspose⟩

lemma inK_blkRes {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (s : Bool) :
    inK (fun _ : Fin (blkP ε s) => true) (blkRes ε s X) := by
  refine ⟨?_, by rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul]⟩
  show (blkRes ε s X)ᴴ * Jm (fun _ : Fin (blkP ε s) => true) +
    Jm (fun _ : Fin (blkP ε s) => true) * blkRes ε s X = 0
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul]
  ext i j
  have h := congrFun (congrFun hX.1 (blkSig ε ⟨s, i⟩)) (blkSig ε ⟨s, j⟩)
  rw [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, ε_blkSig ε s i,
    ε_blkSig ε s j] at h
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, blkRes_apply, Matrix.zero_apply] at h ⊢
  cases s <;> simp at h ⊢ <;> first | linear_combination h | linear_combination -h

lemma exp_blkDiag (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    NormedSpace.exp (blkDiag ε v) = blkDiag ε (fun s => NormedSpace.exp (v s)) := by
  letI : ∀ s : Bool, NormedRing (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedRing
  letI : ∀ s : Bool, NormedAlgebra ℚ (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  letI : ∀ s : Bool, NormedAlgebra ℂ (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  haveI : ∀ s : Bool, CompleteSpace (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => FiniteDimensional.complete ℂ _
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := NormedSpace.map_exp (blkDiag ε) (continuous_blkDiag ε) v
  exact h.symm.trans (congrArg _ (Pi.exp_def v))

theorem exp_blk {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) :
    NormedSpace.exp X = embM ε true (NormedSpace.exp (blkRes ε true X)) *
      embM ε false (NormedSpace.exp (blkRes ε false X)) := by
  conv_lhs => rw [eq_blkDiag hX, exp_blkDiag]
  rw [embM, embM, ← map_mul]
  congr 1
  funext t
  cases t <;> simp [Pi.mulSingle_apply]

theorem blk_curve {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (γp : ℝ → KG (fun _ : Fin (blkP ε true) => true))
    (hp : ∀ t : ℝ, toMK (γp t) = NormedSpace.exp ((t : ℂ) • blkRes ε true X))
    (γm : ℝ → KG (fun _ : Fin (blkP ε false) => true))
    (hm : ∀ t : ℝ, toMK (γm t) = NormedSpace.exp ((t : ℂ) • blkRes ε false X)) (t : ℝ) :
    γ t = blkEmbed ε true (γp t) * blkEmbed ε false (γm t) := by
  apply onep_KG_ext
  have hX' : ((t : ℂ) • X) * Jm ε = Jm ε * ((t : ℂ) • X) := by
    rw [Matrix.smul_mul, hX.2, Matrix.mul_smul]
  show toMK (γ t) = toMK (blkEmbed ε true (γp t)) * toMK (blkEmbed ε false (γm t))
  rw [toMK_blkEmbed, toMK_blkEmbed, hγ, hp, hm, exp_blk hX', map_smul, map_smul]

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma onepCurve_zero (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    onepCurve ε hX 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp [onepCurve]

lemma hasDerivAt_mul_of_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : ℝ → A} {a b : A}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    HasDerivAt (fun t => f t * g t) (a + b) 0 := by
  have h := hf.mul hg
  rw [hf0, hg0, one_mul, mul_one] at h
  exact h

theorem derivExists_of_split (h : DerivExistsAllPosStatement) (ε : Fin n → Bool)
    (p : Bool → ℕ) (emb : ∀ s, KG (fun _ : Fin (p s) => true) →* KG ε)
    (hemb : ∀ s, Continuous (emb s))
    (blk : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (p s)) (Fin (p s)) ℂ)
    (hblk : ∀ s X, inK ε X → inK (fun _ : Fin (p s) => true) (blk s X))
    (hsplit : ∀ X (hX : inK ε X) (t : ℝ),
      toMK (emb true (onepCurve _ (hblk true X hX) t)) *
          toMK (emb false (onepCurve _ (hblk false X hX) t)) =
        NormedSpace.exp ((t : ℂ) • X))
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    ∃ dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0 := by
  choose dτs hdτs using fun s => h (p s) V (τ.comp (emb s)) (hτ.comp (hemb s))
  refine ⟨(dτs true).comp (blk true) + (dτs false).comp (blk false), fun X hX γ hγ => ?_⟩
  have hγeq : ∀ t, γ t = emb true (onepCurve _ (hblk true X hX) t) *
      emb false (onepCurve _ (hblk false X hX) t) := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact (hγ t).trans (hsplit X hX t).symm
  have hd1 := hdτs true (blk true X) (hblk true X hX) (onepCurve _ (hblk true X hX))
    (toMK_onepCurve _ (hblk true X hX))
  have hd2 := hdτs false (blk false X) (hblk false X hX) (onepCurve _ (hblk false X hX))
    (toMK_onepCurve _ (hblk false X hX))
  have hprod := hasDerivAt_mul_of_one hd1 hd2 (by simp [onepCurve_zero]) (by simp [onepCurve_zero])
  have hfun : (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) =
      fun t => (((τ.comp (emb true)) (onepCurve _ (hblk true X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) *
        (((τ.comp (emb false)) (onepCurve _ (hblk false X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
    funext t
    rw [hγeq t, map_mul]
    rfl
  rw [hfun]
  simpa using hprod

theorem derivExists_of (h : DerivExistsAllPosStatement) : DerivExistsStatement := by
  intro n ε V _ _ _ τ hτ
  refine derivExists_of_split h ε (blkP ε) (blkEmbed ε) (continuous_blkEmbed ε) (blkRes ε)
    (fun s X hX => inK_blkRes hX s) (fun X hX t => ?_) V τ hτ
  have hc := blk_curve hX (onepCurve ε hX) (toMK_onepCurve ε hX)
    (onepCurve _ (inK_blkRes hX true)) (toMK_onepCurve _ (inK_blkRes hX true))
    (onepCurve _ (inK_blkRes hX false)) (toMK_onepCurve _ (inK_blkRes hX false)) t
  have h1 := congrArg toMK hc
  rw [toMK_onepCurve] at h1
  exact h1.symm

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepHom
noncomputable section

open Matrix Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma urepHom_toMK_mul {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma urepHom_toMK_one {ε : Fin n → Bool} : toMK (1 : KG ε) = 1 := rfl

lemma urepHom_mem_unitary {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset ε) σ)
    (k : KG ε) : σ (toMK k) ∈ unitary (H →L[ℂ] H) := by
  have hmem : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  set a := σ (toMK k)
  set c := σ (toMK k⁻¹)

  have h1 : star a * a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self a).1 (hσ.2.1 _ (hmem k))

  have h2 : a * c = 1 := by
    have e : toMK k * toMK k⁻¹ = 1 := by
      rw [← urepHom_toMK_mul, mul_inv_cancel, urepHom_toMK_one]
    have := hσ.1.2 _ (hmem k) _ (hmem k⁻¹)
    rw [e, hσ.1.1] at this
    exact this.symm
  have h3 : a * star a = 1 := by
    calc a * star a = a * star a * (a * c) := by rw [h2, mul_one]
      _ = a * (star a * a) * c := by noncomm_ring
      _ = 1 := by rw [h1, mul_one, h2]
  exact Unitary.mem_iff.2 ⟨h1, h3⟩

theorem uRepHom : URepHomStatement := by
  intro n ε H _ _ _ σ hσ
  have hmem : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  refine ⟨{ toFun := fun k => ⟨σ (toMK k), urepHom_mem_unitary hσ k⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_, fun k => rfl⟩
  · apply Subtype.ext
    show σ (toMK (1 : KG ε)) = 1
    rw [urepHom_toMK_one, hσ.1.1]
  · intro k k'
    apply Subtype.ext
    show σ (toMK (k * k')) = σ (toMK k) * σ (toMK k')
    rw [urepHom_toMK_mul]
    exact hσ.1.2 _ (hmem k) _ (hmem k')
  · have hc : Continuous (fun k : KG ε => toMK k) := by
      fun_prop
    have hop : Continuous (fun k : KG ε => σ (toMK k)) := by
      refine continuous_clm_apply.2 fun v => ?_
      exact (hσ.2.2 v).comp_continuous hc hmem
    exact Continuous.subtype_mk hop _

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

namespace ReciprocityTheory.ChartRestriction.DS.HW

theorem kRepPiece : KRepPieceStatement := kRepPiece_of kRepRel kRepStable

theorem compRed : CompRedStatement := compRed_of kRepRel kRepStable kRepPiece

theorem derivExists : DerivExistsStatement := derivExists_of derivExists_allPos

theorem uRepCompRed : URepCompRedStatement := uRepCompRed_of uRepHom derivExists kRepRel compRed

end ReciprocityTheory.ChartRestriction.DS.HW

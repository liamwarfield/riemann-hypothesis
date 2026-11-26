module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBound
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBound
open Formalism.UG GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

private theorem mem_range_bc_of_entries_mem_intL {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    (g : GL (Fin n) L) (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) :
    g ∈ (Formalism.UG.bc (Formalism.UG.intL L).subtype).range := by
  let M : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h2 i j⟩
  have hM : (Formalism.UG.intL L).subtype.mapMatrix M = g := by ext i j; rfl
  have hM' : (Formalism.UG.intL L).subtype.mapMatrix M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have inj : Function.Injective
      ((Formalism.UG.intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) → Matrix (Fin n) (Fin n) L) :=
    fun A B h => Matrix.ext fun i j => Subtype.ext (by simpa [RingHom.mapMatrix_apply] using congrFun (congrFun h i) j)
  refine ⟨⟨M, M', inj ?_, inj ?_⟩, Units.ext hM⟩
  · rw [map_mul, map_one, hM, hM']
    exact g.mul_inv
  · rw [map_mul, map_one, hM, hM']
    exact g.inv_mul

private theorem entry_lemma_2 {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
    (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : Formalism.UG.GU σ 1) (i j : Fin 1) :
    ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) i j ∈ Formalism.UG.intL L := by
  have hg : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * Formalism.UG.antiJ L 1 *
      ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = Formalism.UG.antiJ L 1 := g.2
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  set x := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0 with hx
  have e : σ x * x = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.antiJ, hx] using this
  have e2 : Valued.v x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hv x]
    rw [← map_mul, e, map_one]
  refine (Valuation.mem_integer_iff _ _).mpr ?_
  exact (pow_le_one_iff two_ne_zero).mp e2.le

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hσ hn g
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  interval_cases n
  · exact mem_range_bc_of_entries_mem_intL _ (fun i => i.elim0) (fun i => i.elim0)
  · exact mem_range_bc_of_entries_mem_intL _ (entry_lemma_2 hσ.2.1 g) (entry_lemma_2 hσ.2.1 g⁻¹)

end GlobalTheory.CompanionTheory.InertZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBoundStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.smallRank | exact GlobalTheory.CompanionTheory.InertZeta.smallRank | (intros; apply GlobalTheory.CompanionTheory.InertZeta.smallRank <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.TraceIndexFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.TraceIndexFormula
open GlobalTheory.InertZeta Formalism.UG

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem traceZero_eq_map {σ : L →+* L} {c : L} (hc : c ≠ 0) (hσ : σ c = c) :
    traceZero σ c =
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft c⁻¹) := by
  ext x
  rw [mem_traceZero, AddSubgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c * x, AddSubgroup.mem_inf.2 ⟨h1, ?_⟩, by simp [hc]⟩
    rw [AddMonoidHom.mem_ker]
    show σ (c * x) + c * x = 0
    rw [map_mul, hσ, ← mul_add, h2, mul_zero]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hy
    rw [AddMonoidHom.mem_ker] at h2
    have h2' : σ y + y = 0 := h2
    have hi : σ c⁻¹ = c⁻¹ := by rw [map_inv₀, hσ]
    refine ⟨?_, ?_⟩
    · show c * (c⁻¹ * y) ∈ intL L
      rw [mul_inv_cancel_left₀ hc]
      exact h1
    · show σ (c⁻¹ * y) + c⁻¹ * y = 0
      rw [map_mul, hi, ← mul_add, h2', mul_zero]

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hbase := GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex GlobalTheory.SatakeWeyl.intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, hv, -, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  have hϖ1 : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv', ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have hS : ∀ f : ℕ, traceZero σ (ϖ ^ f) = T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) := fun f =>
    traceZero_eq_map (pow_ne_zero f h0) (by rw [map_pow, hϖ])
  have hmono : ∀ f : ℕ, traceZero σ (ϖ ^ f) ≤ traceZero σ (ϖ ^ (f + 1)) := by
    intro f x hx
    obtain ⟨h1, h2⟩ := mem_traceZero.1 hx
    refine mem_traceZero.2 ⟨?_, h2⟩
    rw [pow_succ', mul_assoc]
    exact mul_mem hϖ1 h1
  have hstep : ∀ f : ℕ, (traceZero σ (ϖ ^ f)).relIndex (traceZero σ (ϖ ^ (f + 1))) = q := by
    intro f
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) :=
      mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ h0))
    have e : T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨ϖ * y, ⟨y, hy, rfl⟩, ?_⟩
        field_simp
        ring
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        field_simp
        ring
    rw [hS f, hS (f + 1), e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hbase
  induction f with
  | zero =>
    rw [pow_zero, pow_zero, AddSubgroup.relIndex_self]
  | succ f ih =>
    have hle : traceZero σ 1 ≤ traceZero σ (ϖ ^ f) := by
      clear ih
      induction f with
      | zero => rw [pow_zero]
      | succ f ih => exact ih.trans (hmono f)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle (hmono f), ih, hstep, pow_succ]

end GlobalTheory.CompanionTheory.InertZeta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.TraceIndexFormulaStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_index_formula : TraceIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.traceIndex | exact GlobalTheory.CompanionTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.CompanionTheory.InertZeta.traceIndex <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
open GlobalTheory.InertZeta Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem det_updateRow_one (i : Fin n) (ρ : Fin n → L) :
    ((1 : Matrix (Fin n) (Fin n) L).updateRow i ρ).det = ρ i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one, ← Matrix.cramer_apply,
    Matrix.cramer_one]
  rfl

theorem rowLat_updateRow {M : Matrix (Fin n) (Fin n) L} {ρ : Fin n → L} {i : Fin n}
    (h0 : ρ i ≠ 0) (h1 : Valued.v (ρ i)⁻¹ ≤ 1) (h2 : ∀ j, Valued.v (ρ j) ≤ Valued.v (ρ i)) :
    rowLat M ⊔ Submodule.span (Formalism.UG.intL L) {ρ ᵥ* M} = rowLat (M.updateRow i (ρ ᵥ* M)) := by
  set w := ρ ᵥ* M with hw
  apply le_antisymm
  · refine sup_le (rowLat_le.2 fun j => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    · by_cases hj : j = i
      · subst hj
        refine mem_rowLat.2 ⟨fun l => if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹), fun l => ?_, ?_⟩
        · by_cases hl : l = j
          · simp only [if_pos hl]
            exact h1
          · simp only [hl, if_false]
            refine neg_mem ?_
            rw [mem_intL_iff, map_mul, map_inv₀]
            exact mul_inv_le_one_of_le₀ (h2 l) zero_le'
        · rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have e1 : ∑ l ∈ Finset.univ.erase j, (if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹)) • (M.updateRow j w) l
              = ∑ l ∈ Finset.univ.erase j, (-(ρ l * (ρ j)⁻¹)) • M l :=
            Finset.sum_congr rfl fun l hl => by
              have := Finset.ne_of_mem_erase hl
              simp [this, Matrix.updateRow_ne]
          have e2 : w = ρ j • M j + ∑ l ∈ Finset.univ.erase j, ρ l • M l := by
            rw [hw, Matrix.vecMul_eq_sum]
            exact (Finset.add_sum_erase _ (fun l => ρ l • M l) (Finset.mem_univ j)).symm
          rw [e1]
          simp only [if_true, Matrix.updateRow_self]
          rw [e2, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum, add_assoc,
            ← Finset.sum_add_distrib]
          simp only [smul_smul, neg_smul]
          have : ∀ l, (ρ j)⁻¹ * ρ l = ρ l * (ρ j)⁻¹ := fun l => mul_comm _ _
          simp [this]
      · have := row_mem_rowLat (M.updateRow i w) j
        rwa [Matrix.updateRow_ne hj] at this
    · have := row_mem_rowLat (M.updateRow i w) i
      rwa [Matrix.updateRow_self] at this
  · refine rowLat_le.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Matrix.updateRow_self]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Matrix.updateRow_ne hj]
      exact Submodule.mem_sup_left (row_mem_rowLat M j)

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  by_cases e0 : e = 0
  · subst e0
    refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact mem_intL_iff.2 (by simpa using hρ i)
  · obtain ⟨i, hi⟩ := he.resolve_left e0
    have h0 : ρ i ≠ 0 := fun h => by
      rw [h, map_zero] at hi
      exact WithZero.exp_ne_zero hi.symm
    have hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (e : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h1 : Valued.v (ρ i)⁻¹ ≤ 1 := by
      rw [map_inv₀, hi]
      exact inv_le_one_of_one_le₀ hone
    refine ⟨M.updateRow i (ρ ᵥ* M), ?_, rowLat_updateRow h0 h1 fun j => hi ▸ hρ j⟩
    have e1 : M.updateRow i (ρ ᵥ* M) = (1 : Matrix (Fin n) (Fin n) L).updateRow i ρ * M := by
      ext a b
      by_cases ha : a = i
      · subst ha
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
      · simp [Matrix.updateRow_ne ha, Matrix.mul_apply, Matrix.one_apply]
    rw [e1, Matrix.det_mul, det_updateRow_one, map_mul, hi, hM, ← WithZero.exp_add, add_comm]

end GlobalTheory.CompanionTheory.InertZeta

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExistsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetInjective
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem rad_mul_levi_apply {β : Fin n → ℕ} {u p : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β) {i j : Fin n}
    (hij : β j ≤ β i) : mat (u * p) i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hu i i le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rcases le_or_gt (β l) (β i) with h1 | h1
    · rw [hu i l h1, Matrix.one_apply_ne hl.symm, zero_mul]
    · rw [hp l j (by omega), mul_zero]
  · simp

theorem rad_levi_rad_apply {β : Fin n → ℕ} {u p u' : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β)
    (hu' : u' ∈ radU σ β) {i j : Fin n} (hij : β j ≤ β i) : mat (u * p * u') i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hu' j j le_rfl, Matrix.one_apply_eq, mul_one]
    exact rad_mul_levi_apply hu hp hij
  · intro l _ hl
    rcases le_or_gt (β j) (β l) with h1 | h1
    · rw [hu' l j h1, Matrix.one_apply_ne hl, mul_zero]
    · rw [rad_mul_levi_apply hu hp (by omega), hp i l (by omega), zero_mul]
  · simp

variable {N : ℕ}

theorem levi_mul_zero {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) : mat (x * y) 0 0 = mat x 0 0 * mat y 0 0 := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
    add_zero]
  intro j _
  rw [hx 0 (mid j) (by simp), zero_mul]

theorem levi_mul_last {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) :
    mat (x * y) (Fin.last (N + 1)) (Fin.last (N + 1)) =
      mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * mat y (Fin.last (N + 1)) (Fin.last (N + 1)) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
    zero_add]
  intro j _
  rw [hx (Fin.last (N + 1)) (mid j) (by simp), zero_mul]

theorem levi_mul_mid {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (i j : Fin N) :
    mat (x * y) (mid i) (mid j) = ∑ k, mat x (mid i) (mid k) * mat y (mid k) (mid j) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, hx (mid i) 0 (by simp), hx (mid i) (Fin.last (N + 1)) (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hk
  obtain ⟨-, hσ, hσϖ, hϖ, -, -, -⟩ := hU
  obtain ⟨hl, h0, h1, h2⟩ := hm
  obtain ⟨hl', h0', h1', h2'⟩ := hm'
  have hli : m⁻¹ ∈ leviU σ (blk N) := inv_mem hl
  have hp : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hli hl'
  have e : (m * u)⁻¹ * (m' * u') = u⁻¹ * (m⁻¹ * m') * u' := by group
  rw [e] at hk
  have hint : ∀ i j, blk N j ≤ blk N i → mat (m⁻¹ * m') i j ∈ intL L := fun i j hij => by
    rw [← rad_levi_rad_apply (inv_mem hu) hp hu' hij]
    exact (mem_KU_iff hσ _).1 hk i j
  have e0 : mat (m⁻¹ * m') 0 0 = ϖ ^ (a' - a) := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_zero hli, mat_inv_apply, Fin.rev_zero, h1, h0', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have e1 : mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_last hli, mat_inv_apply, Fin.rev_last, h0, h1', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have hv0 : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
  have hv1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    exact WithZero.coe_lt_one.2 (by decide)
  have i0 : Valued.v ϖ ^ (a' - a) ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') 0 0) ≤ 1 := hint 0 0 le_rfl
    rwa [e0, map_zpow₀] at this
  have i1 : Valued.v ϖ ^ (a - a') ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 :=
      hint _ _ (le_refl (blk N (Fin.last (N + 1))))
    rwa [e1, map_zpow₀] at this
  rw [zpow_le_one_iff_right_of_lt_one₀ hv0 hv1] at i0 i1
  refine ⟨by omega, (mem_KU_iff hσ _).2 fun i j => ?_⟩
  have := hint (mid i) (mid j) (by simp)
  have e2 : ∀ i j, mat m⁻¹ (mid i) (mid j) = mat g₀⁻¹ i j := fun i j => by
    rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, h2]
  rw [levi_mul_mid hli] at this
  simp only [e2, h2'] at this
  rw [mat_mul, Matrix.mul_apply]
  exact this

end GlobalTheory.CompanionTheory.InertZeta

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetInjectiveStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_injective : CosetInj := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetInj | exact GlobalTheory.CompanionTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetInj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.GeneratingFunctionIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.GeneratingFunctionIdentity
open GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertGenFun

theorem hasSum_counts (q N c : ℕ) (X : ℂ) (h : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j)
      (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)) := by
  set y : ℂ := (q : ℂ) ^ (N + 1) * X with hy
  set F : ℕ → ℂ := fun j => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j with hF
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have hev : HasSum (fun m : ℕ => F (2 * m)) (c * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m)) = fun m => (c : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2), hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hodd : HasSum (fun m : ℕ => F (2 * m + 1)) (c * q * X * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m + 1)) = fun m => (c * q * X : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [show (2 * m + 1) / 2 = m by omega, hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hne : (1 : ℂ) - y ^ 2 ≠ 0 := by
    intro h0
    have : ‖y ^ 2‖ = 1 := by
      rw [show y ^ 2 = 1 by linear_combination -h0]
      simp
    linarith
  have hval : (c : ℂ) * (1 + q * X) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * X * (1 - y ^ 2)⁻¹ := by
    field_simp
  rw [hval]
  exact HasSum.even_add_odd hev hodd

theorem hasSum_of_counts {ι : Type} (g : ι → ℕ) (A : ℕ → ℕ) (hA : ∀ j, A j ≠ 0)
    (hc : ∀ j, Nat.card {i // g i ≤ j} = A j) (X s : ℂ)
    (hT : HasSum (fun j : ℕ => (A j : ℂ) * X ^ j) s) :
    HasSum (fun i => X ^ g i) ((1 - X) * s) := by
  have hfinle : ∀ j, Finite {i // g i ≤ j} := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc j]; exact hA j)
  have hfin : ∀ j, Finite {i // g i = j} := fun j =>
    Finite.of_injective (fun c : {i // g i = j} => (⟨c.1, c.2.le⟩ : {i // g i ≤ j}))
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have hcard : ∀ j, Nat.card {i // g i = j} + (if j = 0 then 0 else A (j - 1)) = A j := by
    intro j
    rcases j with _ | k
    · simp only [if_true, add_zero, ← hc 0]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by omega))
    · have : ∀ i, g i ≤ k + 1 ↔ g i ≤ k ∨ g i = k + 1 := fun i => by omega
      have e := (Equiv.subtypeEquivRight this).trans
        (subtypeOrEquiv (fun i => g i ≤ k) (fun i => g i = k + 1)
          (Pi.disjoint_iff.2 fun i => Prop.disjoint_iff.2 (by omega)))
      rw [← hc (k + 1), Nat.card_congr e, Nat.card_sum, if_neg (Nat.succ_ne_zero k),
        Nat.add_sub_cancel, ← hc k, add_comm]
  have hfib : ∀ (j : ℕ) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (F : ℕ → M),
      HasSum (fun c : {i // g i = j} => F (g c)) (Nat.card {i // g i = j} • F j) := by
    intro j M _ _ F
    have := hfin j
    have : Fintype {i // g i = j} := Fintype.ofFinite _
    convert hasSum_fintype (fun c : {i // g i = j} => F (g c)) using 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hle : ∀ j, Nat.card {i // g i = j} ≤ A j := fun j => by
    have := hcard j
    omega
  have hnorm : Summable (fun j : ℕ => (A j : ℝ) * ‖X‖ ^ j) := by
    have := hT.summable.norm
    simpa [norm_mul, norm_pow] using this
  have hsum : Summable (fun i => X ^ g i) := by
    apply Summable.of_norm
    rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
    show Summable fun p : (Σ j : ℕ, {i // g i = j}) => ‖X ^ g (p.2 : ι)‖
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (hfib j (fun n => ‖X ^ n‖)).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) hnorm
    have h1 := (hfib j (fun n => ‖X ^ n‖)).tsum_eq
    rw [h1, nsmul_eq_mul, norm_pow]
    gcongr
    exact_mod_cast hle j
  obtain ⟨t, ht⟩ := hsum
  have hsig := ((Equiv.sigmaFiberEquiv g).hasSum_iff.2 ht).sigma
    (fun j => hfib j (fun n => X ^ n))
  have hshift : HasSum (fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) (s * X) := by
    have h0 : HasSum (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1))
        (s * X) := by
      have hfun : (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1)) =
          fun n => (A n : ℂ) * X ^ n * X := by
        funext n
        rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
        ring
      rw [hfun]
      exact hT.mul_right X
    have h1 := (hasSum_nat_add_iff
      (f := fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) 1).1 h0
    simp only [Finset.sum_range_one, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero] at h1
    exact h1
  have hdiff := hT.sub hshift
  have heq : (fun j : ℕ => (A j : ℂ) * X ^ j - ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) =
      fun j => Nat.card {i // g i = j} • X ^ j := by
    funext j
    rw [nsmul_eq_mul, ← hcard j]
    push_cast
    ring
  rw [heq] at hdiff
  have := hsig.unique hdiff
  rw [this] at ht
  rwa [show (1 - X) * s = s - s * X by ring]

theorem genFun : GenFun := by
  intro ι f l c q N X hc hq hf hcount hX
  have hA : ∀ j, c * q ^ (2 * N * (j / 2) + j) ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hcg : ∀ j, Nat.card {i // f i - l ≤ j} = c * q ^ (2 * N * (j / 2) + j) := by
    intro j
    rw [← hcount j]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by have := hf i; omega))
  have h := hasSum_of_counts (fun i => f i - l) (fun j => c * q ^ (2 * N * (j / 2) + j)) hA hcg X _
    (hasSum_counts q N c X hX)
  have key : (fun i => X ^ f i) = fun i => X ^ l * X ^ (f i - l) := by
    funext i
    rw [← pow_add]
    congr 1
    have := hf i
    omega
  rw [key, show (c : ℂ) * X ^ l * jFac q N X =
    X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
  exact h.mul_left _

end GlobalTheory.CompanionTheory.InertGenFun
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.GeneratingFunctionIdentityStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generating_function_identity : GenFun := by
  first | exact @GlobalTheory.CompanionTheory.InertGenFun.genFun | exact GlobalTheory.CompanionTheory.InertGenFun.genFun | (intros; apply GlobalTheory.CompanionTheory.InertGenFun.genFun <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwap
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwap
noncomputable section

open Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (hK : IsCommensurated K) (g : G) : Finset (G ⧸ K) :=
  (P.finite_cosets_in_doset hK g).toFinset

theorem mem_cosetsIn {hK : IsCommensurated K} {g : G} {x : G ⧸ K} :
    x ∈ cosetsIn hK g ↔ x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [cosetsIn, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, a.2, b, b.2, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩

theorem hAct_dosetInd (hK : IsCommensurated K) (g : G) (f : G → ℂ) :
    hAct K (dosetInd ℂ K g) f 1 = ∑ x ∈ cosetsIn hK g, f x.out := by
  unfold hAct
  rw [finsum_eq_sum_of_support_subset (s := cosetsIn hK g)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hm : x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := mem_cosetsIn.mp hx
    simp [dosetInd, Set.indicator_apply, hm]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Finset.mem_coe, mem_cosetsIn]
    by_contra hm
    apply hx
    simp [dosetInd, Set.indicator_apply, hm]

theorem eq_of_mem_cosetsIn {hK : IsCommensurated K} {f : G → ℂ} (hf : IsBiInv K f) {g : G} {x : G ⧸ K}
    (hx : x ∈ cosetsIn hK g) : f x.out = f g := by
  obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.mp (mem_cosetsIn.mp hx)
  rw [h]
  exact hf ⟨a, ha⟩ ⟨b, hb⟩ g

def dosetOf (x : G ⧸ K) : Set G := DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

theorem dosetOf_eq_iff {hK : IsCommensurated K} {x y : G ⧸ K} : dosetOf y = dosetOf x ↔ y ∈ cosetsIn hK x.out := by
  rw [mem_cosetsIn]
  unfold dosetOf
  constructor
  · intro h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K y.out
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h

theorem tsum_fiber {M : Type} [AddCommMonoid M] [TopologicalSpace M] (hK : IsCommensurated K) (x : G ⧸ K)
    (h : G ⧸ K → M) : ∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, h c = ∑ y ∈ cosetsIn hK x.out, h y := by
  rw [← Finset.tsum_subtype (cosetsIn hK x.out) h]
  exact (Equiv.subtypeEquivRight
    (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).tsum_eq (fun c => h c.1)

theorem finite_fiber (hK : IsCommensurated K) (q : Set G) : Finite {y : G ⧸ K // dosetOf y = q} := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight
      (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).symm
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    infer_instance

theorem fiber_compare (hK : IsCommensurated K) {F w φ : G → ℂ} (hF : IsBiInv K F) (hw : IsBiInv K w)
    (h : ∀ g, hAct K (dosetInd ℂ K g) w 1 = hAct K (dosetInd ℂ K g) φ 1) (q : Set G) :
    ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out = ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out ∧
    ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * w c.1.out‖ ≤
      ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * φ c.1.out‖ := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    have t1 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * φ c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := tsum_fiber hK x (fun y => F y.out * φ y.out)
    have t2 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * w c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out := tsum_fiber hK x (fun y => F y.out * w y.out)
    have t3 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * w c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * w y.out‖)
    have t4 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * φ c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * φ y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * φ y.out‖)
    rw [t1, t2, t3, t4]
    have hF' : ∀ y ∈ cosetsIn hK x.out, F y.out = F x.out := fun y hy => eq_of_mem_cosetsIn hF hy
    have hW' : ∀ y ∈ cosetsIn hK x.out, w y.out = w x.out := fun y hy => eq_of_mem_cosetsIn hw hy
    have hsum : ∑ y ∈ cosetsIn hK x.out, φ y.out = ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [← hAct_dosetInd hK, ← hAct_dosetInd hK, h]
    have e1 : ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, φ y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e2 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e4 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := by
      rw [e1, e2, hsum]
    have hc : ∀ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * w x.out := fun y hy => by
      rw [hF' y hy, hW' y hy]
    have e3 : ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ = ‖∑ y ∈ cosetsIn hK x.out, F y.out * w y.out‖ := by
      rw [Finset.sum_congr rfl hc, Finset.sum_congr rfl (fun y hy => congrArg (‖·‖) (hc y hy))]
      simp only [Finset.sum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
    refine ⟨e4.symm, ?_⟩
    rw [e3, e4]
    exact norm_sum_le _ _
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    simp only [tsum_empty, le_refl, and_self]

theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw h ha
  let e : (Σ q : Set G, {y : G ⧸ K // dosetOf y = q}) ≃ G ⧸ K := Equiv.sigmaFiberEquiv dosetOf
  have haN : Summable fun x : G ⧸ K => ‖F x.out * φ x.out‖ := summable_norm_iff.mpr ha.summable
  have haN' : Summable fun p => ‖F (e p).out * φ (e p).out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * φ x.out‖)).mpr haN
  have hbN' : Summable fun p => ‖F (e p).out * w (e p).out‖ := by
    rw [summable_sigma_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun q => ?_, ?_⟩
    · haveI := finite_fiber hK q
      exact Summable.of_finite
    · have hA := ((summable_sigma_of_nonneg (fun p => norm_nonneg _)).mp haN').2
      refine Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => norm_nonneg _) (fun q => ?_) hA
      exact (fiber_compare hK hF hw h q).2
  have hbN : Summable fun x : G ⧸ K => ‖F x.out * w x.out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * w x.out‖)).mp hbN'
  have hbS : Summable fun x : G ⧸ K => F x.out * w x.out := hbN.of_norm
  have hbS' : Summable fun p => F (e p).out * w (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * w x.out)).mpr hbS
  have haS' : Summable fun p => F (e p).out * φ (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * φ x.out)).mpr ha.summable
  have key : ∑' x : G ⧸ K, F x.out * w x.out = ∑' x : G ⧸ K, F x.out * φ x.out := by
    calc ∑' x : G ⧸ K, F x.out * w x.out = ∑' p, F (e p).out * w (e p).out :=
          (e.tsum_eq (fun x => F x.out * w x.out)).symm
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out := hbS'.tsum_sigma
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out :=
          tsum_congr fun q => ((fiber_compare hK hF hw h q).1).symm
      _ = ∑' p, F (e p).out * φ (e p).out := haS'.tsum_sigma.symm
      _ = ∑' x : G ⧸ K, F x.out * φ x.out := e.tsum_eq (fun x => F x.out * φ x.out)
  have hb := hbS.hasSum
  rwa [key, ha.tsum_eq] at hb

end GlobalTheory.CompanionTheory.InertZeta
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwapStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_swap : DosetSwap := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.dosetSwap | exact GlobalTheory.CompanionTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.CompanionTheory.InertZeta.dosetSwap <;> assumption)
end
end

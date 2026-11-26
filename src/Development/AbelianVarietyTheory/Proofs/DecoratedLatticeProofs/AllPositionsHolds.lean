module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPosition
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeBlockDiagonalTargetEntryConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeBlockDiagonalTargetEntryConditions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PosEntries

section Shape
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_inr {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i : Fin c) (s : n ⊕ Fin c)
    (hs : M (Sum.inr i) s ≠ 0) : s = Sum.inr i := by
  rcases s with x | j
  · exfalso
    by_cases h : i.val + 1 < p
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · by_cases hij : j = i
    · rw [hij]
    exfalso
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))

theorem shape_inl {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hp : 1 ≤ p)
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (j : Fin c)
    (hs : M (Sum.inl x) (Sum.inr j) ≠ 0) : j.val + 1 = p := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))

end Shape

section Trans
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem mulD_inr (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (l : Fin (c + 1)) :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inr l) =
      x r (Sum.inr l) * (ϖ : k) ^ (l.val + 1) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem mulD_inl (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (y : n') :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inl y) =
      x r (Sum.inl y) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_ite_eq']

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem opE_translate_free (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (hz : ∀ r s, ¬ Free p (r, s) → z r s = 0) (hΨ : ∀ x, Ψ (x + z) = Ψ x) (x₀ : Matrix n n' k) :
    opE ψ ν p Ψ x₀ = (ψ (-ch z) : ℂ) * opE ψ ν p Ψ x₀ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ez : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs => z rs.1.1 rs.1.2
  have hpt : ∀ e, affPt p x₀ (e + ez) = affPt p x₀ e + z := by
    intro e; ext r s
    simp only [affPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
    split_ifs with h
    · simp only [ez]; ring
    · simp [hz r s h]
  unfold opE
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ ez]
  congr 1; ext e
  rw [hpt, hΨ, ch_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem exists_affPt_ne_zero (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : opE ψ ν p Ψ x₀ ≠ 0) :
    ∃ e, Ψ (affPt p x₀ e) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  simp [opE, hn]

end Trans

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem entries_core (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : HasConductor ψ 1)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c p : ℕ) (hp1 : 1 ≤ p) (A : GL (n ⊕ Fin c) k)
    (hA1 : A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hA2 : A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (hB1 : (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hB2 : (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hInt : ∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val))
    (hMax : ∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) →
      Ψ (x + z) = Ψ x)
    (hE : opE ψ ν p Ψ ≠ 0) :
    (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧
      (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧
    ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hE
  obtain ⟨e, he⟩ := exists_affPt_ne_zero ψ ν p hx₀
  have hI := hInt _ he
  have hx_diag : ∀ i : Fin c, affPt p x₀ e (Sum.inr i) (Sum.inr i.castSucc) = 1 := by
    intro i; simp [affPt, basePt, Free]
  have hx_X : ∀ (y : n) (q : Fin c), q.val + 1 = p → affPt p x₀ e (Sum.inl y) (Sum.inr q.castSucc) = 0 := by
    intro y q hq; subst hq; simp [affPt, basePt, Free]
  have hAB : ∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (A⁻¹).val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun (Units.mul_inv A) (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have h := hI (Sum.inr i) (Sum.inr i.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i), hx_diag] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  · have hb0 : (A⁻¹).val (Sum.inr i) (Sum.inr i) ≠ 0 := right_ne_zero_of_mul_eq_one (hAB i)
    have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
    have key : ∀ y : k, valuation k y ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) →
        ψ y = 1 := by
      intro y hy
      let ζ := y * ((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹
      let E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
        Matrix.of fun u s => if u = Sum.inr i ∧ s = Sum.inr i.succ then ζ else 0
      let z := (A⁻¹).val * E
      have hAz : A.val * z = E := by simp only [z, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hzent : ∀ r s, z r s = if s = Sum.inr i.succ then (A⁻¹).val r (Sum.inr i) * ζ else 0 := by
        intro r s
        simp only [z, E, Matrix.mul_apply, Matrix.of_apply]
        split_ifs with hs
        · rw [Finset.sum_eq_single (Sum.inr i)] <;> simp_all
        · simp [hs]
      have hval : valuation k (ζ * (ϖ : k) ^ (i.val + 2)) < 1 := by
        have h1 : (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ *
            (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) = ϖ := by
          field_simp; ring
        calc valuation k (ζ * (ϖ : k) ^ (i.val + 2))
            = valuation k y * valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by
              rw [← map_mul, mul_assoc]
          _ ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) *
              valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by gcongr
          _ = valuation k (ϖ : k) := by rw [← map_mul, h1]
          _ < 1 := hϖ
      have hmax : MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) := by
        intro r s
        rw [hAz]
        rcases s with y' | l
        · rw [mulD_inl]; simp [E]
        · rw [mulD_inr]
          simp only [E, Matrix.of_apply]
          split_ifs with h
          · obtain ⟨rfl, hl⟩ := h
            obtain rfl : l = i.succ := Sum.inr_injective hl
            rw [show (i.succ : Fin (c + 1)).val + 1 = i.val + 2 by simp [Fin.val_succ]]
            exact hval
          · simp
      have hfree : ∀ r s, ¬ Free p (r, s) → z r s = 0 := by
        intro r s hns
        rw [hzent]
        split_ifs with hs
        · subst hs
          by_cases h0 : (A⁻¹).val r (Sum.inr i) = 0
          · simp [h0]
          · exfalso; apply hns
            rcases r with y' | j
            · have := shape_inl hp1 hB1 hB2 y' i h0
              simp [Free, Fin.val_succ]; omega
            · obtain ⟨⟩ := shape_inr hB1 hB2 j (Sum.inr i) h0
              simp [Free, Fin.val_succ]
        · rfl
      have htr := opE_translate_free ψ ν p hfree (fun x' => hMax x' z hmax) x₀
      have hch : ch z = y := by
        simp only [ch, hzent]
        rw [Finset.sum_eq_single i]
        · simp only [if_true, ζ]; field_simp
        · intro j _ hj; simp [Fin.succ_inj, hj]
        · simp
      have h1 : (ψ (-ch z) : ℂ) = 1 := by
        have : ((ψ (-ch z) : ℂ) - 1) * opE ψ ν p Ψ x₀ = 0 := by rw [sub_mul, ← htr]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hx₀
      have h2 : ψ (-ch z) = 1 := Circle.ext (by simpa using h1)
      rw [AddChar.map_neg_eq_inv, inv_eq_one, hch] at h2
      exact h2
    have hle := (hψ _).mp key
    simp only [Units.val_one, map_one] at hle
    exact hle
  · intro q hq y
    have h := hI (Sum.inl y) (Sum.inr q.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr q)] at h
    · rw [hx_diag] at h; simpa using h
    · intro s _ hs
      rcases s with z | j
      · simp [hx_X z q hq]
      · by_cases h0 : A.val (Sum.inl y) (Sum.inr j) = 0
        · simp [h0]
        · have := shape_inl hp1 hA1 hA2 y j h0
          exact absurd (by congr 1; exact Fin.ext (by omega)) hs
    · simp

end Main

theorem entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], HasConductor ψ 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → ∀ (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val)) → (∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) → Ψ (x + z) = Ψ x) → opE ψ ν p Ψ ≠ 0 → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧ ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ ν _ hψ ϖ hϖ n n' _ _ _ _ c p hp1 _ A hA1 hA2 hB1 hB2 Ψ hInt hMax hE
  exact entries_core ψ ν hψ ϖ hϖ n n' c p hp1 A hA1 hA2 hB1 hB2 Ψ hInt hMax hE

end GlobalTheory.PosEntries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeBlockDiagonalTargetEntryConditionsStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_blockDiagonal_target_entry_conditions : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], HasConductor ψ 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → ∀ (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val)) → (∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) → Ψ (x + z) = Ψ x) → opE ψ ν p Ψ ≠ 0 → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧ ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.PosEntries.entries | exact GlobalTheory.PosEntries.entries | (intros; apply GlobalTheory.PosEntries.entries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleBlockTriangularMemIntegralMulLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleBlockTriangularMemIntegralMulLevi
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PClassAlg

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_aX (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (l : Fin c) (y : n) :
    B (Sum.inr l) (Sum.inl y) = 0 := by
  by_cases h : l.val + 1 < p
  · apply h2
    show OrderDual.toDual (lev p (Sum.inl y : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr l : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega

theorem shape_aa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i j : Fin c) (hij : i ≠ j) :
    B (Sum.inr i) (Sum.inr j) = 0 := by
  have : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne this with h | h
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr j : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c))
    simp only [lev, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inr]; omega

theorem shape_Xa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (i : Fin c) (hi : i.val + 1 ≠ p) :
    B (Sum.inl x) (Sum.inr i) = 0 := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inl x : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega

theorem eq_fromBlocks (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    B = fromBlocks (toBlocks₁₁ B) (toBlocks₁₂ B) 0 (toBlocks₂₂ B) := by
  conv_lhs => rw [← fromBlocks_toBlocks B]
  congr 1
  ext l y; exact shape_aX hp B h1 h2 l y

theorem diag_block (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    toBlocks₂₂ B = diagonal fun i => B (Sum.inr i) (Sum.inr i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [toBlocks₂₂]
  · simp [toBlocks₂₂, diagonal_apply_ne _ h, shape_aa B h1 h2 i j h]

end GlobalTheory.PClassAlg

namespace GlobalTheory.PClassAlg

theorem blockDiag_mem_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  intro k _ _ _ _ ϖ n _ _ c p hp hpc A hA1 hA2 hB1 hB2 hD hE
  have eA := eq_fromBlocks hp _ hA1 hA2
  have eB := eq_fromBlocks hp _ hB1 hB2
  have dA := diag_block _ hA1 hA2
  have dB := diag_block _ hB1 hB2
  have sXa := shape_Xa _ hA1 hA2
  set P := toBlocks₁₁ A.val
  set Q := toBlocks₁₂ A.val
  set S := toBlocks₂₂ A.val
  set P' := toBlocks₁₁ (A⁻¹).val
  set Q' := toBlocks₁₂ (A⁻¹).val
  set S' := toBlocks₂₂ (A⁻¹).val
  have hAB : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have hBA : (A⁻¹).val * A.val = 1 := Units.inv_mul A
  rw [eA, eB, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hAB hBA
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hAB hBA
  obtain ⟨hPP', hPQ, -, -⟩ := hAB
  obtain ⟨hP'P, -, -, -⟩ := hBA
  let γ : GL n k := ⟨P', P, hP'P, hPP'⟩
  have hpow : ∀ i : Fin c, (((ϖ ^ (i.val + 1) : kˣ)) : k) = (ϖ : k) ^ (i.val + 1) := fun i => by simp
  have hne : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ ϖ.ne_zero
  refine ⟨γ, (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨?_, ?_⟩⟩
  · have hM : (A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))).val =
        fromBlocks (P * P') (Q * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) 0
          (S * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
      rw [Units.val_mul, Units.val_mul, eA]
      show fromBlocks P Q 0 S * fromBlocks P' 0 0 1 * fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val = _
      simp [fromBlocks_multiply, hpow]
    rw [hM, hPP']
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, mul_diagonal]
      by_cases h : i.val + 1 = p
      · exact hE i h x
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, mul_diagonal, dA]
      by_cases h : l = i
      · subst h; simpa using (hD l).1
      · simp [diagonal_apply_ne _ h]

  · have hM : ((A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)))⁻¹).val =
        fromBlocks (P * P') (P * Q') 0
          ((diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) * S') := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, Units.val_mul, Units.val_mul, eB]
      show fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val *
        (fromBlocks P 0 0 1 * fromBlocks P' Q' 0 S') = _
      have : ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val =
          diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹ := by
        ext i j; simp [GlobalTheory.SplitFlip.diagGL, diagonal_apply]
      rw [this]
      simp [fromBlocks_multiply]
    have hPQ' : P * Q' = -(Q * S') := eq_neg_of_add_eq_zero_left hPQ
    rw [hM, hPP', hPQ', dB]
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, Matrix.neg_apply, mul_diagonal]
      by_cases h : i.val + 1 = p
      · have e : Q x i * (A⁻¹).val (Sum.inr i) (Sum.inr i) =
            (A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1)) *
              ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) := by
          have := hne i
          simp only [Q, toBlocks₁₂, of_apply]
          field_simp
        rw [e]
        exact neg_mem (mul_mem (hE i h x) (hD i).2)
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, diagonal_mul_diagonal, diagonal_apply]
      split_ifs with h
      · subst h; rw [mul_comm]; exact (hD l).2
      · exact zero_mem _

end GlobalTheory.PClassAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleBlockTriangularMemIntegralMulLeviStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  first | exact @GlobalTheory.PClassAlg.blockDiag_mem_KO | exact GlobalTheory.PClassAlg.blockDiag_mem_KO | (intros; apply GlobalTheory.PClassAlg.blockDiag_mem_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPhiSupportPeriodicStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_phi_support_periodic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s) (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), ((S.T t).Phi j c H x ≠ 0 → IntM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * x * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧ (MaxM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * z * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) → (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPosition
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem classAt_all : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ j c H p hp1 hpc h hE
  haveI := hν.1
  obtain ⟨D, hDdef⟩ : ∃ D : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
      D = embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : GL (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      D' = embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  have hD : (S.T t).bas (j + 1) c (by omega) = D := by rw [hDdef]; rfl
  have hlt : valuation k (S.ϖ : k) < 1 := (S.unif (S.ϖ : k)).2 le_rfl
  let lv' : XIx (Fin κ) t (j + 1) ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))
  have hlv : ∀ r s, lev p s < lev p r → lv' s < lv' r := by
    rintro (r | r) (s | s) h0 <;> simp only [lev, lv', Sum.elim_inl, Sum.elim_inr] at h0 ⊢ <;> omega
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k _ lv' (h * D)
  have hb' : b.val.BlockTriangular (lev p) := fun r s hrs => hb (hlv r s hrs)
  obtain ⟨u, hu, m, hm1, hm2, hum⟩ := BlockLevi.exists_unip_mul_levi k _ c p b hb'
  have hh : h = u * (m * w * D⁻¹) := by
    have : h = h * D * D⁻¹ := by group
    rw [this, hbw, hum]; group
  obtain ⟨v, hv⟩ : ∃ v, v = m * w * D⁻¹ := ⟨_, rfl⟩
  rw [← hv] at hh
  have key : om (S.μ (j + 1)) 1 (u * v) ((S.T t).Phi j c H) =
      om (S.μ (j + 1)) 1 u (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) := by
    simpa using Model.om_mul (S.μ (j + 1)) 1 1 u v ((S.T t).Phi j c H)
  have hE' : opE S.ψ ν p (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0; apply hE
    rw [hh, key, opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν (S.μ (j + 1)) _ u hu, h0, smul_zero]
  have eg : D⁻¹ * v⁻¹ = w⁻¹ * m⁻¹ := by rw [hv]; group
  have ev : ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      (D⁻¹).val * ((v⁻¹).val * x) * D'.val = (w⁻¹).val * ((m⁻¹).val * x * D'.val) := by
    intro x
    rw [← Matrix.mul_assoc (D⁻¹).val, ← Units.val_mul, eg, Units.val_mul]; simp only [Matrix.mul_assoc]
  have hinst := GlobalTheory.T.symmetricLevelChain_phi_support_periodic k s κ S t j c H
  rw [← hDdef, ← hD'def] at hinst
  have hsup : ∀ x, om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x ≠ 0 → IntM ((m⁻¹).val * x * D'.val) := by
    intro x hx
    have hΦ : (S.T t).Phi j c H ((v⁻¹).val * x) ≠ 0 := by
      have := right_ne_zero_of_mul hx
      simpa using this
    have h1 := (hinst ((v⁻¹).val * x) 0).1 hΦ
    rw [ev] at h1
    have e2 : (m⁻¹).val * x * D'.val = w.val * ((w⁻¹).val * ((m⁻¹).val * x * D'.val)) := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e2]; exact (intM_of_mem_KO hw).mul h1
  have hper : ∀ x z, MaxM ((m⁻¹).val * z * D'.val) →
      om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) (x + z) = om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x := by
    intro x z hz
    have h1 : MaxM ((D⁻¹).val * ((v⁻¹).val * z) * D'.val) := by
      rw [ev]; exact (mem_KO.1 hw).2.mul_maxM hz
    simp only [om, Units.val_one, Matrix.mul_one, Matrix.mul_add]
    rw [(hinst ((v⁻¹).val * x) ((v⁻¹).val * z)).2 h1]
  have sm1 : m.val.BlockTriangular lv' := by
    intro r s hrs
    by_cases e : lev p r = lev p s
    · rw [hm2 r s e]; exact hb hrs
    · exact hm1 r s e
  have sm2 : m.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    intro r s hrs
    exact hm1 r s (Nat.ne_of_lt (OrderDual.toDual_lt_toDual.mp hrs))
  have si1 : (m⁻¹).val.BlockTriangular lv' := BlockLevi.blockTriangular_inv lv' m sm1
  have si2 : (m⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    letI : Invertible m.val := m.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular sm2
  have sm1' : (m⁻¹⁻¹).val.BlockTriangular lv' := by rw [inv_inv]; exact sm1
  have sm2' : (m⁻¹⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by rw [inv_inv]; exact sm2
  rw [hD'def] at hsup hper
  obtain ⟨E1, E2⟩ := GlobalTheory.T.rootExchange_blockDiagonal_target_entry_conditions k S.ψ ν S.cond S.ϖ hlt _ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' _ hsup hper hE'
  obtain ⟨γ, hK⟩ := GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi k S.ϖ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' E1 E2
  rw [← hDdef] at hK
  refine ⟨u * embX c γ, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨γ, rfl⟩),
    (u * embX c γ)⁻¹ * h, ?_, by group⟩
  rw [hD, mem_stabLat]
  have : D⁻¹ * ((u * embX c γ)⁻¹ * h) * D = (m⁻¹ * embX c γ * D)⁻¹ * w := by
    rw [hh, hv]; group
  rw [this]
  exact mul_mem (inv_mem hK) hw

end GlobalTheory.SymChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPositionStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_classAt_every_position : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν := by
  first | exact @GlobalTheory.SymChain.classAt_all | exact GlobalTheory.SymChain.classAt_all | (intros; apply GlobalTheory.SymChain.classAt_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPattern
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRootExchangeParabolicMulPrincipalCongruenc
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRootExchangeParabolicMulPrincipalCongruenc
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ResidueLift

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def blockIx (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p) (fun i => 2 * (i.val + 1) + 1)

theorem of_blockIx_lt {a b : n ⊕ Fin c} (h : blockIx p b < blockIx p a) :
    lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) ∧ a ≠ b := by
  rcases a with a | a <;> rcases b with b | b <;> simp only [blockIx, Sum.elim_inl, Sum.elim_inr] at h
  · omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, fun e => ?_⟩
    · simp only [lev, Sum.elim_inr]; omega
    · cases e; omega

theorem mem_R_of_pattern (r : GL (n ⊕ Fin c) k)
    (hr : ∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
      r.val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b) :
    r ∈ R k n c p := by
  have hbt : r.val.BlockTriangular (blockIx p) := fun a b h => by
    obtain ⟨h1, h2, h3⟩ := of_blockIx_lt h
    rw [hr a b h1 h2, one_apply_ne h3]
  have hbt' : (r⁻¹).val.BlockTriangular (blockIx p) := by
    rw [Matrix.coe_units_inv]; exact blockTriangular_inv_of_blockTriangular hbt
  have hz : ∀ (x : n) (j : Fin c), j.val + 1 ≤ p → r.val (.inl x) (.inr j) = 0 := fun x j hj => by
    rw [hr _ _ (by simpa [lev] using hj) (by simp)]; simp
  have hz' : ∀ (x : n) (j : Fin c), p ≤ j.val + 1 → (r⁻¹).val (.inr j) (.inl x) = 0 := fun x j hj =>
    hbt' (by simp only [blockIx, Sum.elim_inl, Sum.elim_inr]; omega)
  have e1 : r.val.toBlocks₁₁ * (r⁻¹).val.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ (congrArg Units.val (mul_inv_cancel r))
    rw [Units.val_mul, mul_toBlocks₁₁, Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁] at this
    rw [← this, left_eq_add]
    ext x x'
    simp only [Matrix.mul_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_total (j.val + 1) p with hj | hj
    · rw [hz x j hj, zero_mul]
    · rw [hz' x' j hj, mul_zero]
  let γ : GL n k := ⟨r.val.toBlocks₁₁, (r⁻¹).val.toBlocks₁₁, e1, mul_eq_one_comm.1 e1⟩
  have e2 : (γ⁻¹).val * r.val.toBlocks₁₁ = 1 := Units.inv_mul γ
  have hm : InN p ((embX c γ)⁻¹ * r) := by
    intro a b hab
    rw [← map_inv, Units.val_mul, show (embX c γ⁻¹).val = fromBlocks (γ⁻¹).val 0 0 1 from rfl]
    rcases a with x | i
    · rcases b with x' | j
      · have := congrFun (congrFun e2 x) x'
        simpa [Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, Matrix.one_apply] using this
      · have hj : j.val + 1 ≤ p := by simpa [lev] using hab
        simp [Matrix.mul_apply, Fintype.sum_sum_type, hz _ _ hj]
    · rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, zero_add]
      change ((1 : Matrix (Fin c) (Fin c) k) *ᵥ (fun j => r.val (.inr j) b)) i = _
      rw [Matrix.one_mulVec]
      exact hr (.inr i) b hab (by simp)
  have : r = embX c γ * ((embX c γ)⁻¹ * r) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hm))

end GlobalTheory.SymChain.ResidueLift

namespace GlobalTheory.SymChain.ResidueLift

theorem exists_R_mul_KOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (h : GL (n ⊕ Fin c) k), (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KO k (n ⊕ Fin c) → (∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) → valuation k (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b - (1 : Matrix _ _ k) a b) < 1) → ∃ r ∈ R k n c p, ∃ u : GL (n ⊕ Fin c) k, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * u * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KOne k (n ⊕ Fin c) ∧ h = r * u := by
  intro k _ _ _ _ ϖ n _ _ c p h hg hpat
  classical
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of fun a b =>
    if lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) then (1 : Matrix _ _ k) a b
    else ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b
  have hM : MaxM (M - ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val) := fun a b => by
    simp only [M, Matrix.sub_apply, Matrix.of_apply]
    split_ifs with hc
    · rw [← neg_sub, Valuation.map_neg]; exact hpat a b hc.1 hc.2
    · simp
  obtain ⟨u', hu', eu'⟩ := exists_mul_KOne hg hM
  refine ⟨(typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas *
      (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas) * u') *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_,
    (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_, ?_⟩
  · refine mem_R_of_pattern _ fun a b h1 h2 => ?_
    rw [Units.val_mul, Units.val_mul, eu', Model.typeFrame_val, Model.typeFrame_inv, mul_diagonal, diagonal_mul]
    simp only [M, Matrix.of_apply, if_pos (And.intro h1 h2)]
    by_cases hab : a = b
    · subst hab; simp [mul_inv_cancel₀ (Model.wt_ne_zero ϖ a)]
    · simp [one_apply_ne hab]
  · have e : (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ *
        (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹) * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas = u'⁻¹ := by group
    rw [e]; exact inv_mem hu'
  · group

end GlobalTheory.SymChain.ResidueLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRootExchangeParabolicMulPrincipalCongruencStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootExchangeParabolic_mul_principalCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (h : GL (n ⊕ Fin c) k), (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KO k (n ⊕ Fin c) → (∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) → valuation k (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b - (1 : Matrix _ _ k) a b) < 1) → ∃ r ∈ R k n c p, ∃ u : GL (n ⊕ Fin c) k, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * u * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KOne k (n ⊕ Fin c) ∧ h = r * u := by
  first | exact @GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne | exact GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne | (intros; apply GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPattern
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport

noncomputable section
namespace GlobalTheory.SymSupportP

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem exists_factor {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (p : ℕ) (T : n → Prop)
    (h1 : ∀ l s, T s → p ≤ l.val + 1 → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ u ∈ KOne k (n ⊕ Fin c), ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∀ a b, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
        (g * u * lowU D).val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b := by
  classical
  let P : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s =>
    Sum.elim (fun s => T s ∧ ∃ l : Fin c, r = .inr l ∧ p ≤ l.val + 1)
      (fun i => lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r) s
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
    Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s
  obtain ⟨u, hu, e⟩ := exists_mul_KOne hg (M := M) (fun r s => by
    by_cases hP : P r s
    · rw [Matrix.sub_apply, Valuation.map_sub_swap,
        show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]
      rcases s with s | i
      · obtain ⟨hT, l, rfl, hl⟩ := hP
        simpa using h1 l s hT hl
      · exact h2 r i hP
    · rw [Matrix.sub_apply, show M r s = g.val r s from if_neg hP]; simp)
  have hM : IntM M := e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))
  have m2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) :=
    fun r i hl => if_pos hl
  have m1 : ∀ (l : Fin c) s, T s → p ≤ l.val + 1 → M (.inr l) (.inl s) = 0 := fun l s hT hl => by
    have : M (.inr l) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr l) (.inl s) :=
      if_pos ⟨hT, l, rfl, hl⟩
    simpa using this
  have hd : M.toBlocks₂₂.det = 1 := by
    rw [det_of_upperTriangular, Finset.prod_eq_one]
    · intro i _
      simpa [toBlocks₂₂] using m2 (.inr i) i le_rfl
    · intro i j hij
      have := m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)
      simpa [toBlocks₂₂, (show j < i from hij).ne'] using this
  obtain ⟨V, hV, hUV⟩ := exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd
  let D : Matrix (Fin c) n k := Matrix.of fun l s => if T s then 0 else -(V * M.toBlocks₂₁) l s
  have hVM : IntM (V * M.toBlocks₂₁) := hV.mul fun i j => hM _ _
  refine ⟨u, hu, D, fun i j => ?_, fun l s hT => if_pos hT, ?_⟩
  · by_cases hT : T j
    · simp [D, hT, zero_mem]
    · simpa [D, hT] using neg_mem (hVM i j)
  · intro a b hl hab
    rw [Units.val_mul, e]
    change (M * (fromBlocks 1 0 D 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) a b = _
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply]
    rcases b with x | i
    · rcases a with y | l
      · simp at hab
      · have hl' : p ≤ l.val + 1 := by simpa [lev] using hl
        simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₁, Matrix.add_apply]
        by_cases hT : T x
        · have : (M.toBlocks₂₂ * D) l x = 0 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_eq_zero fun m _ => by simp [D, hT]
          rw [this, add_zero]
          simpa [toBlocks₂₁] using m1 l x hT hl'
        · have : (M.toBlocks₂₂ * D) l x = (M.toBlocks₂₂ * (-(V * M.toBlocks₂₁))) l x := by
            simp only [Matrix.mul_apply]
            exact Finset.sum_congr rfl fun m _ => by simp [D, hT]
          rw [this, Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
          simp
    · rcases a with y | l
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₁₂]
        simpa [toBlocks₁₂] using m2 (.inl y) i hl
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₂]
        simpa [toBlocks₂₂] using m2 (.inr l) i hl

end Local

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem supportAt (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t) :
    S.SupportAt t := by
  intro j c H p hp1 hpc h hh x₀ e hΦ
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  let B := (typeFrame S.ϖ o).bas
  let B' := (typeFrame S.ϖ o').bas
  have hG : B⁻¹ * h * B ∈ KO k _ := mem_stabLat.1 hh
  let Z := (B⁻¹).val * affPt p x₀ e * B'.val
  let J := (S.P.iter t S.μ S.tame (j + 1)).reindex o
  have hΦ' : (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o').submatrix ((ixSucc _ t j).trans o) id) ≠ 0 := by
    have e1 : ((B⁻¹ * h * B)⁻¹).val * Z = (B⁻¹).val * ((h⁻¹).val * affPt p x₀ e) * B'.val := by
      simp only [Z, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B.val, Units.mul_inv, Matrix.one_mul]
    have e2 : ((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o' = (((B⁻¹ * h * B)⁻¹).val * Z).submatrix id o' := rfl
    rw [e2, e1]
    exact hΦ
  obtain ⟨κ₀, hκ, hc⟩ := exists_match _ _ _ hG _ hΦ'
  have hκ' : κ₀ ∈ J.J := hκ
  have hZ : ∀ r s, Z r s = Sum.elim (fun _ => 1) (fun i : Fin c => ((S.ϖ : k) ^ (i.val + 1))⁻¹) r *
      affPt p x₀ e r s * Sum.elim (fun _ => 1) (fun i : Fin (c + 1) => (S.ϖ : k) ^ (i.val + 1)) s := by
    intro r s
    simp only [Z, B, B', typeFrame_val, typeFrame_inv_val, mul_diagonal, diagonal_mul]
  obtain ⟨u, hu, D, hD, hD0, hpat⟩ := exists_factor (mul_mem hG (J.le_KO hκ')) p
    (fun s => ∃ i, s = .inl (.inl i)) (by
      rintro l _ ⟨i, rfl⟩ hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val (.inr l) (.inl (.inl (.inl i))) -
        Z (.inr l) (.inl (.inl (.inl i)))) < 1 := hc (.inr l) (.inl (.inl i))
      have hf : ¬ (l.val + 1 < p) := by omega
      rwa [hZ, show affPt p x₀ e (.inr l) (.inl (.inl (.inl i))) = 0 by simp [affPt, basePt, Free, hf],
        mul_zero, zero_mul, sub_zero] at h1) (by
      intro r i hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val r (o (.inl (.inr ⟨i.val, by omega⟩))) -
        Z r (o' (.inl (.inr ⟨i.castSucc.val, by simp; omega⟩)))) < 1 := hc r (.inl (.inr ⟨i.val, by omega⟩))
      rw [standardOrderExtendedBasis_apply_low_block, standardOrderExtendedBasis_apply_low_block, hZ] at h1
      convert h1 using 3
      rcases r with r | r
      · have : ¬ (p < i.val + 1) := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have : ¬ r < i := by simpa [lev] using hl
        by_cases hri : r = i
        · subst hri; simp [affPt, basePt, Free]
        · simp [affPt, basePt, Free, this, hri, Fin.val_inj])
  have hlowK : lowU D ∈ KO k _ := mem_KO.2 ⟨intM_fromBlocks.2 ⟨intM_one, intM_zero, hD, intM_one⟩,
      intM_fromBlocks.2 ⟨intM_one, intM_zero, hD.neg, intM_one⟩⟩
  have hlow : lowU D ∈ J.J := by
    refine (hP (j + 1) ((reGL o).symm (lowU D))).2 ⟨?_, fun a b hab => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_KO.1 hlowK
      exact mem_KO.2 ⟨fun a b => h1 _ _, fun a b => by rw [← map_inv]; exact h2 _ _⟩
    · have : (lowU D).val (o a) (o b) = (1 : Matrix _ _ k) (o a) (o b) := by
        obtain ⟨a, rfl⟩ := o.symm.surjective a
        obtain ⟨b, rfl⟩ := o.symm.surjective b
        rw [o.apply_symm_apply, o.apply_symm_apply]
        rcases a with a | a <;> rcases b with b | b
        · simp [lowU, Matrix.one_apply]
        · simp [lowU]
        · have a1 : o.symm (.inr a) = .inl (.inr ⟨a.val, by omega⟩) :=
            o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block _ t _ _ _ a).symm
          rcases b with (b | b) | b
          · simpa [lowU] using hD0 a _ ⟨b, rfl⟩
          · have a3 : o.symm (.inl (.inl (.inr b))) = .inl (.inr ⟨c + b.val, by omega⟩) :=
              o.symm_apply_eq.2 (stdOrd_f _ t _ _ _ b).symm
            rw [a1, a3] at hab
            exact absurd (show a.val < c + b.val by omega) hab
          · have a6 : o.symm (.inl (.inr b)) = .inr b := o.symm_apply_eq.2 rfl
            rw [a1, a6] at hab
            exact absurd trivial hab
        · simp [lowU, Matrix.one_apply]
      rw [reGL_symm_val, submatrix_apply, this]
      simp [Matrix.one_apply]
  let kap := κ₀ * u * lowU D
  have hkap : kap ∈ J.J := mul_mem (mul_mem hκ' (J.KOne_le hu)) hlow
  have hbas : (typeFrame S.ϖ (Equiv.refl (XIx (Fin κ) t (j + 1) ⊕ Fin c))).bas = B :=
    Units.ext (by rw [typeFrame_val, typeFrame_val])
  have hconj : B⁻¹ * (h * (B * kap * B⁻¹)) * B = B⁻¹ * h * B * κ₀ * u * lowU D := by
    simp only [kap]; group
  obtain ⟨r, hr, u', hu', eq⟩ := GlobalTheory.T.exists_rootExchangeParabolic_mul_principalCongruence k S.ϖ _ c p (h * (B * kap * B⁻¹))
    (by rw [hbas, hconj]
        exact mul_mem (mul_mem (mul_mem hG (J.le_KO hκ')) (KOne_le_KO hu)) hlowK)
    (by
      intro a b hl hab
      rw [hbas, hconj, hpat a b hl hab]
      simp)
  refine ⟨r, hr, u' * (B * kap⁻¹ * B⁻¹), ?_, ?_⟩
  · change (reGL o).symm (B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
    have : B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B = (B⁻¹ * u' * B) * kap⁻¹ := by group
    rw [this]
    rw [hbas] at hu'
    exact mul_mem (J.KOne_le hu') (inv_mem hkap)
  · calc h = (h * (B * kap * B⁻¹)) * (B * kap⁻¹ * B⁻¹) := by group
      _ = _ := by rw [eq]; group

end Main

theorem supportAt_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    S.Pattern t → S.SupportAt t :=
  fun _ _ _ _ _ s κ S t _ _ hP => supportAt s κ S t hP

end GlobalTheory.SymSupportP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPatternStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportAt t := by
  first | exact @GlobalTheory.SymSupportP.supportAt_of_pattern | exact GlobalTheory.SymSupportP.supportAt_of_pattern | (intros; apply GlobalTheory.SymSupportP.supportAt_of_pattern <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupport
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem oneIndexAt_of_classAt_supportAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c H p hp1 hpc h hE
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c H p hp1 hpc h hE
  obtain ⟨γ, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  have hmul : ∀ (a b : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k) (Ψ : type_of% ((S.T t).Phi j c H)),
      om (S.μ (j + 1)) 1 (a * b) Ψ = om (S.μ (j + 1)) 1 a (om (S.μ (j + 1)) 1 b Ψ) :=
    fun a b Ψ => by rw [← om_mul, one_mul]
  have hne : opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0
    apply hE
    rw [mul_assoc, hmul, (opE_om_embX k _ _ c p hp1 hpc S.ψ ν _ _).1, hmul,
      opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν _ _ g hg, h0]
    funext y
    simp [om]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  classical
  obtain ⟨e, he⟩ : ∃ e, om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H) (affPt p x₀ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx₀
    simp [opE, hc]
  have hΦ : (S.T t).Phi j c H ((u⁻¹).val * affPt p x₀ e) ≠ 0 := by
    intro h0
    apply he
    simp only [om, Units.val_one, Matrix.mul_one, h0, mul_zero]
  obtain ⟨r', hr', u', hu', rfl⟩ := hS j c H p hp1 hpc u hu x₀ e hΦ
  exact ⟨embX c γ * g * r', mul_mem hr hr', u', hu', by group⟩

end GlobalTheory.SymChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupportStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  first | exact @GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | exact GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | (intros; apply GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt <;> assumption)
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem allPositions_holds : AllPositions := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hsupp : S.SupportAt t := GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern k s κ S t hpat
  have hclass : S.ClassAt t ν := GlobalTheory.T.symmetricLevelChain_classAt_every_position k ν hν s κ S t
  exact ⟨GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange k ν hν s κ S t hpat⟩

end GlobalTheory.SymChain

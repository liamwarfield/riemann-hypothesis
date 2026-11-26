module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodCurvesPairingMemMaxIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSaturatedGoodVectorsSmallCorankStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSaturatedGoodVectorsSmallCorank
noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GoodCorank

variable {C : Type} [Field C] {V : VF C}

theorem div_int {x y : C} (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  by_cases hy : y = 0
  · subst hy; simpa using VF.Ge.zero (V := V) 0
  · have e : V.v x = V.v y + V.v (x / y) := by
      rw [← V.v.map_mul, mul_div_cancel₀ _ hy]
    have hy' : V.v y ≠ ⊤ := by
      intro h0
      have h1 : V.v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, V.v.map_one]
      rw [V.v.map_mul, h0, top_add] at h1
      exact WithTop.top_ne_zero h1
    unfold VF.Ge
    rw [e] at h
    have h2 : V.v y + 0 ≤ V.v y + V.v (x / y) := by simpa using h
    simpa using (WithTop.add_le_add_iff_left hy').mp h2

theorem ge_ite (p : Prop) [Decidable p] : V.Ge 0 (if p then (1 : C) else 0) := by
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem exists_cut {N : ℕ} (φ : Fin (N + 1) → C) :
    ∃ A : Fin N → Fin (N + 1) → C, IsSat V A ∧ ∀ ν, ∑ k, A ν k * φ k = 0 := by
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun k => V.v (φ k)) Finset.univ_nonempty
  refine ⟨fun ν k => (if k = k0.succAbove ν then 1 else 0) -
      (φ (k0.succAbove ν) / φ k0) * (if k = k0 then 1 else 0), ⟨fun ν k => ?_,
      fun k c => if k = k0.succAbove c then 1 else 0, fun k c => ge_ite _, fun c c' => ?_⟩, fun ν => ?_⟩
  · exact (ge_ite _).sub ((div_int (hk0 _ (Finset.mem_univ _))).mul_int (ge_ite _))
  · simp [Fin.succAbove_ne, eq_comm]
  · simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : φ k0 = 0
    · have h1 := hk0 (k0.succAbove ν) (Finset.mem_univ _)
      rw [h0, V.v.map_zero, top_le_iff] at h1
      have h2 : φ (k0.succAbove ν) = 0 := by
        by_contra hy
        have h3 : V.v (φ (k0.succAbove ν) * (φ (k0.succAbove ν))⁻¹) = 0 := by
          rw [mul_inv_cancel₀ hy, V.v.map_one]
        rw [V.v.map_mul, h1, top_add] at h3
        exact WithTop.top_ne_zero h3
      simp [h0, h2]
    · rw [div_mul_cancel₀ _ h0, sub_self]

theorem isSat_comp {M N : ℕ} {σ : Type} [Fintype σ] {A : Fin M → Fin N → C} {w : Fin N → σ → C}
    (hA : IsSat V A) (hw : IsSat V w) : IsSat V (fun ν c => ∑ k, A ν k * w k c) := by
  obtain ⟨hA0, A', hA', hAA⟩ := hA
  obtain ⟨hw0, w', hw', hww⟩ := hw
  refine ⟨fun ν c => VF.Ge.sum fun k _ => (hA0 _ _).mul_int (hw0 _ _),
    fun x c => ∑ k, w' x k * A' k c, fun x c => VF.Ge.sum fun k _ => (hw' _ _).mul_int (hA' _ _),
    fun c c' => ?_⟩
  have e1 : Matrix.of A * Matrix.of A' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hAA i j
  have e2 : Matrix.of w * Matrix.of w' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hww i j
  have e3 : (Matrix.of A * Matrix.of w) * (Matrix.of w' * Matrix.of A') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of w), e2, Matrix.one_mul, e1]
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun e3 c) c'

theorem exists_sat_ker {I κ : Type} [Fintype I] [DecidableEq I] (P : Finset I) (φ : κ → I → C) (S : Finset κ) :
    ∃ (N : ℕ) (w : Fin N → I → C), IsSat V w ∧ (∀ ν c, c ∉ P → w ν c = 0) ∧
      (∀ ν, ∀ b ∈ S, ∑ c, w ν c * φ b c = 0) ∧ P.card ≤ N + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨P.card, fun ν c => if c = (P.equivFin.symm ν : I) then 1 else 0, ⟨fun ν c => ge_ite _,
      fun c ν => if c = (P.equivFin.symm ν : I) then 1 else 0, fun c ν => ge_ite _, fun ν ν' => ?_⟩,
      fun ν c hc => ?_, by simp, by simp⟩
    · simp [Subtype.val_inj, eq_comm]
    · refine if_neg ?_
      rintro rfl
      exact hc (P.equivFin.symm ν).2
  | insert b S hb ih =>
    obtain ⟨N, w, hs, hP, hφ, hN⟩ := ih
    rw [Finset.card_insert_of_notMem hb]
    cases N with
    | zero => exact ⟨0, w, hs, hP, fun ν => ν.elim0, by omega⟩
    | succ N =>
      obtain ⟨A, hA, hA0⟩ := exists_cut (V := V) (fun k => ∑ c, w k c * φ b c)
      have key : ∀ ν b', ∑ c, (∑ k, A ν k * w k c) * φ b' c = ∑ k, A ν k * ∑ c, w k c * φ b' c := by
        intro ν b'
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      refine ⟨N, fun ν c => ∑ k, A ν k * w k c, isSat_comp hA hs, fun ν c hc => ?_, fun ν b' hb' => ?_, by omega⟩
      · simp [hP _ c hc]
      · rw [key]
        rcases Finset.mem_insert.mp hb' with rfl | hb'
        · exact hA0 ν
        · simp [hφ _ b' hb']

variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]

theorem good_of_int (G : Cart V d I J) {a : ZMod d} {u : I → C} {y : ℕ → I ⊕ J → C} (hy : G.IsCurve a u y)
    (h1 : ∀ b, V.Ge 0 (y 1 (Sum.inl b))) : ∃ x, G.Good a u x := by
  obtain ⟨z, hz, hz0, hzp⟩ := G.t4 (a + 1) (fun b => y 1 (Sum.inl b)) h1
    (fun b hb => hy.2.2 1 _ (by simpa using hb))
  refine ⟨y - Vpow 1 z, ⟨G.Ty.sub_mem hy.1 (G.V_mem _ hz), ?_, fun i n hn => ?_⟩, fun c => ?_⟩
  · funext n
    simp [Vpow, hy.2.1]
  · cases i with
    | zero => simp [Vpow, hy.2.2 0 n hn]
    | succ i =>
      have : z i n = 0 := hzp i n (by
        intro hc; apply hn; rw [hc]; push_cast; ring)
      simp [Vpow, hy.2.2 _ n hn, this]
  · simp [Vpow, hz0]

theorem good_of_ker (G : Cart V d I J) {a : ZMod d} (r : I → I → C)
    (hr : ∀ b c, r b c ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b)) {u : I → C} (hu : ∀ c, V.Ge 0 (u c))
    (hp : ∀ c, G.ty (Sum.inl c) ≠ a → u c = 0)
    (hk : ∀ b, G.ty (Sum.inl b) = a + 1 → ∑ c, u c * r b c = 0) : ∃ x, G.Good a u x := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hy : G.IsCurve a u (∑ c, teich V.l (u c) (G.std c)) := by
    refine ⟨G.Ty.sum_mem fun c _ => G.teich_mem _ (hu c) _ (G.std_spec c).1, ?_, fun i n hn => ?_⟩
    · funext n
      have : ∀ b, G.std b 0 n = Sum.elim (Pi.single b 1) 0 n := fun b => by rw [(G.std_spec b).2.1]
      simp only [Finset.sum_apply, teich, this, pow_zero, pow_one]
      cases n with
      | inl c => simp [Pi.single_apply]
      | inr j => simp
    · simp only [Finset.sum_apply, teich]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : G.ty (Sum.inl c) = a
      · rw [(G.std_spec c).2.2 i n (by rwa [hc]), mul_zero]
      · rw [hp c hc, zero_pow (lpos i), zero_mul]
  refine good_of_int G hy fun b => ?_
  by_cases hb : G.ty (Sum.inl b) = a + 1
  · have hrint : ∀ c, V.Ge 0 (r b c) := fun c => by
      refine GlobalTheory.AdaptedChain.int_of_pow V.l_prime.ne_zero ?_
      rw [hr]
      simpa using (G.bound0 1 _ (G.std_spec c).1 (Sum.inl b)).l_mul
    have hf := (GlobalTheory.AdaptedChain.frob_sum Finset.univ (fun c => u c * r b c)
      (fun c => (hu c).mul_int (hrint c)) 1).neg
    rw [hk b hb, zero_pow (lpos 1), zero_sub, neg_neg] at hf
    have e : ∑ c, (u c * r b c) ^ V.l ^ 1 =
        (V.l : C) * (∑ c, teich V.l (u c) (G.std c)) 1 (Sum.inl b) := by
      simp only [Finset.sum_apply, teich, pow_one, mul_pow, hr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e] at hf
    simpa using hf.of_l_mul
  · rw [hy.2.2 1 _ (by simpa using hb)]
    exact VF.Ge.zero 0

theorem exists_good_sat (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] (G : Cart V d I J) (a : ZMod d) :
    ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧
      (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧
      (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤
        N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  have hex : ∀ b c : I, ∃ r : C, r ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b) := fun b c =>
    IsAlgClosed.exists_pow_nat_eq _ V.l_prime.pos
  choose r hr using hex
  obtain ⟨N, w, hs, hP, hφ, hN⟩ := exists_sat_ker (V := V)
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a) r
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1)
  have hp : ∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0 := fun ν c hc => hP ν c (by simpa using hc)
  have hx : ∀ ν, ∃ x, G.Good a (w ν) x := fun ν =>
    good_of_ker G r hr (hs.1 ν) (hp ν) fun b hb => hφ ν b (by simpa using hb)
  choose x hx using hx
  exact ⟨N, w, x, hx, hp, hs, hN⟩

end GlobalTheory.GoodCorank

end
end

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_saturated_good_vectors_small_corank : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] (G : Cart V d I J) (a : ZMod d), ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧ (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧ (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤ N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  first | exact @GlobalTheory.GoodCorank.exists_good_sat | exact GlobalTheory.GoodCorank.exists_good_sat | (intros; apply GlobalTheory.GoodCorank.exists_good_sat <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowKernel

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_sum {ι : Type} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  V.v.map_lt_sum (by simp) h

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_int_mul hb ha

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := le_of_lt h

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_div {a b : C} (hb : b ≠ 0) (h : V.v b ≤ V.v a) : V.Ge 0 (a / b) := by
  show (0 : WithTop ℝ) ≤ V.v (a / b)
  have e : V.v a = V.v (a / b) + V.v b := by rw [← V.v.map_mul, div_mul_cancel₀ a hb]
  have hb' : V.v b ≠ ⊤ := by simpa using hb
  rw [e] at h
  exact (WithTop.add_le_add_iff_right hb').mp (by simpa using h)

theorem card_add_le {σ : Type} [Fintype σ] (p : σ → Prop) [DecidablePred p] {N M : ℕ}
    (A : Fin N → σ → C) (B : Fin M → σ → C) (hA : IndepMod V A) (hAp : ∀ ν s, ¬ p s → A ν s = 0)
    (hB : IsSat V B) (hBp : ∀ μ s, ¬ p s → B μ s = 0) (hAB : ∀ ν μ, V.MM (∑ s, A ν s * B μ s)) :
    N + M ≤ (Finset.univ.filter p).card := by
  classical
  obtain ⟨-, W, hW, hBW⟩ := hB
  let F : Fin N ⊕ Fin M → {s // p s} → C := Sum.elim (fun ν s => A ν s.1) (fun μ s => W s.1 μ)
  have hF : LinearIndependent C F := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ s, p s → ∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ = 0 := by
      intro s hs
      have := congrFun hg ⟨s, hs⟩
      simpa [F, Fintype.sum_sum_type, Finset.sum_apply] using this
    have h2 : ∀ μ', g (Sum.inr μ') = -∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
      intro μ'
      have h3 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = 0 :=
        Finset.sum_eq_zero fun s _ => by
          by_cases hs : p s
          · rw [h1 s hs, zero_mul]
          · rw [hBp μ' s hs, mul_zero]
      have h4 : ∑ s, (∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = g (Sum.inr μ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ μ, ∑ s, g (Sum.inr μ) * W s μ * B μ' s = g (Sum.inr μ) * if μ' = μ then 1 else 0 := by
          intro μ
          rw [← hBW μ' μ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp [this]
      have h5 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s) * B μ' s = ∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ => by ring
      simp only [add_mul, Finset.sum_add_distrib] at h3
      rw [h4, h5] at h3
      linear_combination h3
    have h6 : ∀ ν, g (Sum.inl ν) = 0 := by
      by_contra hc
      push_neg at hc
      obtain ⟨ν1, hν1⟩ := hc
      obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (g (Sum.inl ν)))
        ⟨ν1, Finset.mem_univ _⟩
      have h0 : g (Sum.inl ν0) ≠ 0 := by
        intro h0
        have := hmin ν1 (Finset.mem_univ _)
        rw [h0, V.v.map_zero, top_le_iff] at this
        exact hν1 (by simpa using this)
      have hint : ∀ ν, V.Ge 0 (g (Sum.inl ν) / g (Sum.inl ν0)) := fun ν =>
        ge_div h0 (hmin ν (Finset.mem_univ _))
      have key := hA (fun ν => g (Sum.inl ν) / g (Sum.inl ν0)) hint (fun s => by
        by_cases hs : p s
        · have e : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
              ∑ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) * W s μ := by
            have e1 : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
                (g (Sum.inl ν0))⁻¹ * ∑ ν, g (Sum.inl ν) * A ν s := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e2 : ∀ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) =
                -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) := by
              intro μ
              rw [h2 μ, mul_neg, neg_neg, Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e3 : ∑ μ, -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) * W s μ =
                -((g (Sum.inl ν0))⁻¹ * ∑ μ, g (Sum.inr μ) * W s μ) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun ν _ => by ring
            simp only [e2]
            rw [e1, e3]
            linear_combination (g (Sum.inl ν0))⁻¹ * h1 s hs
          rw [e]
          exact mm_sum fun μ _ => mm_mul_int (mm_sum fun ν _ => mm_int_mul (hint ν) (hAB ν μ)) (hW s μ)
        · simp only [hAp _ s hs, mul_zero, Finset.sum_const_zero]
          exact mm_zero) ν0
      simp only [div_self h0] at key
      exact not_mm_one key
    intro i
    cases i with
    | inl ν => exact h6 ν
    | inr μ => rw [h2 μ]; simp [h6]
  have := hF.fintype_card_le_finrank
  simpa [Fintype.card_subtype] using this

theorem mm_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.MM a) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_int_mul ((mm_ge h).pow m) h

theorem independenceBoundCondition_of_rankMaximalCondition : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  intro C _ V d _ I _ κ _ X hL hR H h2 hA g a ha N w x hgood hV hind
  classical
  haveI := hL.closed
  have hstep := CharacteristicFromRanks.alt_step X.big hR.big_compl hA
  have hb1 : X.big (1 - g) (a + 1) := (hR.big_compl g (a + 1)).2 fun h => (hstep g a).1 h ha
  have hb2 : ¬ X.big (1 - g) (a + 1 + 1) := fun h => (hstep (1 - g) (a + 1)).1 h hb1
  obtain ⟨M, w', x', hgood', hsupp, hsat, hcard⟩ :=
    GlobalTheory.T.exists_saturated_good_vectors_small_corank C V d (I (1 - g)) (JJ I (1 - g)) (RawChart.cart (H (1 - g))) (a + 1)
  have c1 := hR.rk_big (1 - g) (a + 1) hb1
  have c2 := hR.rk_small (1 - g) (a + 1 + 1) hb2
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  have hind' : IndepMod V (fun ν => (RawChart.cart (H g)).c0' (x ν)) := by
    intro c hc hmm
    choose co hco using fun ν => IsAlgClosed.exists_pow_nat_eq (c ν) (Nat.pos_of_ne_zero hl)
    have hcoi : ∀ ν, V.Ge 0 (co ν) := fun ν => ge_of_pow hl (by rw [hco]; exact hc ν)
    have hG := Cart.Good.comb Finset.univ (fun ν _ => hcoi ν) (fun ν _ => hgood ν)
    have h3 := h2 hA g a ha _ _ hG (fun q => by
      rw [Cart.c0'_comb]
      simp only [hco]
      exact hmm q)
    have h4 := hind co hcoi (fun k => by simpa [Finset.sum_apply] using h3 k)
    intro ν
    rw [← hco ν]
    exact mm_pow hl (h4 ν)
  have key := card_add_le (V := V) (fun c : I (1 - g) => X.ty (1 - g) c = a + 1)
    (fun ν => (RawChart.cart (H g)).c0' (x ν)) w' hind'
    (fun ν s hs => by
      have := (hgood ν).1.2.2 1 (Sum.inr s) (by simpa [RawChart.cart, RawChart.tyC] using hs)
      simp [Cart.c0', this])
    hsat (fun μ s hs => hsupp μ s hs)
    (fun ν μ => GlobalTheory.T.goodCurves_pairing_mem_maxIdeal C V d I κ X hL H g a (a + 1) (w ν) (x ν) (w' μ) (x' μ) (hgood ν) (hgood' μ) (hV ν))
  have hcard' : X.n + X.j ≤ M + X.j' := by
    rw [← c1, ← c2]
    convert hcard <;> rfl
  have key' : N + M ≤ X.n + X.j := by
    rw [← c1]
    convert key
  omega

end GlobalTheory.RowKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecondStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  first | exact @GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition | exact GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition | (intros; apply GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition <;> assumption)
end

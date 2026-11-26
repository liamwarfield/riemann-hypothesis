module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EllipticEstimateWordLeOnePlusLaplacianPow
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EllipticEstimateWordLeOnePlusLaplacianPow
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.Elliptic

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type} [Fintype ι]


open Classical in
def words (D : ι → Module.End ℂ V) (m : ℕ) : Finset (Module.End ℂ V) :=
  Nat.rec {1} (fun _ W => W ∪ Finset.univ.biUnion fun i => W.image (D i * ·)) m

def filt (D : ι → Module.End ℂ V) (m : ℕ) : Submodule ℂ (Module.End ℂ V) := Submodule.span ℂ (words D m : Set _)

def wordNorm (D : ι → Module.End ℂ V) (m : ℕ) (v : V) : ℝ := ∑ T ∈ words D m, ‖T v‖

def lap (D : ι → Module.End ℂ V) : Module.End ℂ V := 1 - ∑ i, D i * D i

variable {D : ι → Module.End ℂ V}

theorem mem_words_succ {m : ℕ} {T : Module.End ℂ V} :
    T ∈ words D (m + 1) ↔ T ∈ words D m ∨ ∃ i, ∃ T' ∈ words D m, D i * T' = T := by
  simp [words]

theorem filt_le (m : ℕ) : filt D m ≤ filt D (m + 1) :=
  Submodule.span_mono fun _ h => mem_words_succ.2 (Or.inl h)

theorem mul_mem_filt {m : ℕ} {S T : Module.End ℂ V} (hS : S ∈ Submodule.span ℂ (Set.range D)) (hT : T ∈ filt D m) :
    S * T ∈ filt D (m + 1) := by
  induction hS using Submodule.span_induction with
  | mem S hS =>
    obtain ⟨i, rfl⟩ := hS
    induction hT using Submodule.span_induction with
    | mem T hT => exact Submodule.subset_span (mem_words_succ.2 (Or.inr ⟨i, T, hT, rfl⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem comm_mem_filt (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) (i : ι) (m : ℕ) :
    ∀ T ∈ filt D m, D i * T - T * D i ∈ filt D m := by
  have ext : ∀ m, (∀ T ∈ words D m, D i * T - T * D i ∈ filt D m) → ∀ T ∈ filt D m, D i * T - T * D i ∈ filt D m := by
    intro m h T hT
    induction hT using Submodule.span_induction with
    | mem T hT => exact h T hT
    | zero => simp
    | add x y _ _ hx hy =>
      have : D i * (x + y) - (x + y) * D i = (D i * x - x * D i) + (D i * y - y * D i) := by noncomm_ring
      rw [this]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]; exact Submodule.smul_mem _ c hx
  induction m with
  | zero => exact ext 0 fun T hT => by simp [words] at hT; simp [hT]
  | succ m ih =>
    refine ext _ fun T hT => ?_
    rcases mem_words_succ.1 hT with h | ⟨j, T', h, rfl⟩
    · exact filt_le m (ih T (Submodule.subset_span h))
    · have : D i * (D j * T') - D j * T' * D i = (D i * D j - D j * D i) * T' + D j * (D i * T' - T' * D i) := by
        noncomm_ring
      rw [this]
      exact add_mem (mul_mem_filt (hbr i j) (Submodule.subset_span h))
        (mul_mem_filt (Submodule.subset_span ⟨j, rfl⟩) (ih T' (Submodule.subset_span h)))

theorem lap_comm_mem_filt (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) {m : ℕ}
    {T : Module.End ℂ V} (hT : T ∈ filt D m) : lap D * T - T * lap D ∈ filt D (m + 1) := by
  have : lap D * T - T * lap D = -∑ i, (D i * D i * T - T * (D i * D i)) := by
    simp only [lap, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, one_mul, mul_one]
    abel
  rw [this]
  refine neg_mem (Submodule.sum_mem _ fun i _ => ?_)
  have h1 := comm_mem_filt hbr i m T hT
  have h2 := mul_mem_filt (Submodule.subset_span ⟨i, rfl⟩) h1
  have h3 := filt_le m (comm_mem_filt hbr i m _ h1)
  have : D i * D i * T - T * (D i * D i) = D i * (D i * T - T * D i) + (D i * (D i * T - T * D i) -
    (D i * (D i * T - T * D i) - (D i * T - T * D i) * D i)) := by noncomm_ring
  rw [this]
  exact add_mem h2 (sub_mem h2 h3)

theorem wordNorm_nonneg (m : ℕ) (v : V) : 0 ≤ wordNorm D m v := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_wordNorm {m : ℕ} {T : Module.End ℂ V} (hT : T ∈ words D m) (v : V) : ‖T v‖ ≤ wordNorm D m v :=
  Finset.single_le_sum (f := fun T : Module.End ℂ V => ‖T v‖) (fun _ _ => norm_nonneg _) hT

theorem exists_le_wordNorm {m : ℕ} {T : Module.End ℂ V} (hT : T ∈ filt D m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖T v‖ ≤ C * wordNorm D m v := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨1, zero_le_one, fun v => by simpa using le_wordNorm hT v⟩
  | zero => exact ⟨0, le_rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a + b, add_nonneg ha hb, fun v => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hx v) (hy v))
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨‖c‖ * a, by positivity, fun v => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hx v) (norm_nonneg _)

theorem energy_le (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ) (u : V) :
    ‖u‖ ^ 2 + ∑ i, ‖D i u‖ ^ 2 ≤ ‖u‖ * ‖lap D u‖ := by
  have h : ⟪u, lap D u⟫_ℂ = ((‖u‖ ^ 2 + ∑ i, ‖D i u‖ ^ 2 : ℝ) : ℂ) := by
    simp only [lap, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, Module.End.mul_apply,
      inner_sub_right, inner_sum, hsk _ u, inner_self_eq_norm_sq_to_K, Finset.sum_neg_distrib, sub_neg_eq_add]
    push_cast; rfl
  have h2 := norm_inner_le_norm (𝕜 := ℂ) u (lap D u)
  rw [h, Complex.norm_real] at h2
  exact (le_abs_self _).trans h2

theorem norm_le_lap (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ) (u : V) : ‖u‖ ≤ ‖lap D u‖ := by
  have h := energy_le hsk u
  have h0 : 0 ≤ ∑ i, ‖D i u‖ ^ 2 := by positivity
  rcases (norm_nonneg u).eq_or_lt with h1 | h1
  · rw [← h1]; exact norm_nonneg _
  · nlinarith

theorem sq_le_lap (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ) (i : ι) (u : V) :
    ‖D i u‖ ^ 2 ≤ ‖u‖ * ‖lap D u‖ := by
  have h := energy_le hsk u
  have h0 : ‖D i u‖ ^ 2 ≤ ∑ i, ‖D i u‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖D i u‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  nlinarith [sq_nonneg ‖u‖]

theorem wordNorm_le (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ)
    (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, wordNorm D m v ≤ C * ‖(lap D ^ m) v‖ := by
  induction m with
  | zero => exact ⟨1, zero_le_one, fun v => by simp [wordNorm, words]⟩
  | succ m ih =>
    obtain ⟨C, hC, ih⟩ := ih
    have h1 : ∀ v, wordNorm D m v ≤ C * ‖(lap D ^ (m + 1)) v‖ := fun v =>
      (ih v).trans (mul_le_mul_of_nonneg_left (by rw [pow_succ']; exact norm_le_lap hsk _) hC)
    have h2 : ∀ v, wordNorm D m (lap D v) ≤ C * ‖(lap D ^ (m + 1)) v‖ := fun v => by
      rw [pow_succ]; exact ih _
    have key : ∀ δ : ℝ, 0 < δ → ∀ T ∈ words D (m + 1), ∃ K : ℝ, 0 ≤ K ∧
        ∀ v, ‖T v‖ ≤ δ * wordNorm D (m + 1) v + K * ‖(lap D ^ (m + 1)) v‖ := by
      intro δ hδ T hT
      rcases mem_words_succ.1 hT with h | ⟨j, T', h, rfl⟩
      · refine ⟨C, hC, fun v => ((le_wordNorm h v).trans (h1 v)).trans (le_add_of_nonneg_left ?_)⟩
        exact mul_nonneg hδ.le (wordNorm_nonneg _ _)
      · obtain ⟨C', hC', h3⟩ := exists_le_wordNorm (lap_comm_mem_filt hbr (Submodule.subset_span h))
        refine ⟨C + C * C' / δ, by positivity, fun v => ?_⟩
        have e1 := sq_le_lap hsk j (T' v)
        have e2 := (le_wordNorm h v).trans (h1 v)
        have e3 := (le_wordNorm h (lap D v)).trans (h2 v)
        have e4 : ‖lap D (T' v)‖ ≤ C * ‖(lap D ^ (m + 1)) v‖ + C' * wordNorm D (m + 1) v := by
          have : lap D (T' v) = T' (lap D v) + (lap D * T' - T' * lap D) v := by simp
          rw [this]
          exact (norm_add_le _ _).trans (add_le_add e3 (h3 v))
        have hN := wordNorm_nonneg (D := D) (m + 1) v
        have ha := norm_nonneg ((lap D ^ (m + 1)) v)
        generalize wordNorm D (m + 1) v = N at *
        generalize ‖(lap D ^ (m + 1)) v‖ = a at *
        have e5 : ‖D j (T' v)‖ ^ 2 ≤ (C * a) * (C * a + C' * N) :=
          e1.trans (mul_le_mul e2 e4 (norm_nonneg _) (by positivity))
        have hq : 0 ≤ C * C' / δ := by positivity
        have hq' : C * C' / δ * δ = C * C' := div_mul_cancel₀ _ hδ.ne'
        generalize C * C' / δ = q at *
        refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (e5.trans ?_)
        have : (δ * N + (C + q) * a) ^ 2 = (C * a) * (C * a + C' * N) +
          ((δ * N) ^ 2 + 2 * δ * N * C * a + δ * N * q * a + 2 * C * q * a ^ 2 + (q * a) ^ 2) := by
          linear_combination (N * a) * hq'
        rw [this]
        exact le_add_of_nonneg_right (by positivity)
    set c : ℝ := ((words D (m + 1)).card : ℝ) with hc
    have hc0 : 0 ≤ c := by positivity
    choose! K hK0 hK using key (1 / (2 * (c + 1))) (by positivity)
    refine ⟨2 * ∑ T ∈ words D (m + 1), K T, mul_nonneg zero_le_two (Finset.sum_nonneg hK0), fun v => ?_⟩
    have h4 : wordNorm D (m + 1) v ≤ c * (1 / (2 * (c + 1)) * wordNorm D (m + 1) v) +
        (∑ T ∈ words D (m + 1), K T) * ‖(lap D ^ (m + 1)) v‖ := by
      refine (Finset.sum_le_sum fun T hT => hK T hT v).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
    have h5 : c * (1 / (2 * (c + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right h5 (wordNorm_nonneg (D := D) (m + 1) v)
    nlinarith

theorem exists_le_of_mem_filt (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ)
    (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) {m : ℕ} {T : Module.End ℂ V}
    (hT : T ∈ filt D m) : ∃ C : ℝ, ∀ v, ‖T v‖ ≤ C * ‖(lap D ^ m) v‖ := by
  obtain ⟨a, ha, h1⟩ := exists_le_wordNorm hT
  obtain ⟨b, -, h2⟩ := wordNorm_le hsk hbr m
  exact ⟨a * b, fun v => (h1 v).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h2 v) ha)⟩

end Abstract

variable {n : ℕ}

theorem mem_pairs {ε : Fin n → Bool} {s : Bool} {p : Fin n × Fin n} :
    p ∈ pairs ε s ↔ p.1 < p.2 ∧ (ε p.1 == ε p.2) = s := by
  obtain ⟨a, b⟩ := p
  simp [pairs, List.mem_product]

theorem mem_lie_iff {ε : Fin n → Bool} {X : Mx n} : X ∈ lieSet ε ↔
    ∀ a b, star (X b a) * (if ε b then 1 else -1) + (if ε a then 1 else -1) * X a b = 0 := by
  show Xᴴ * Jm ε + Jm ε * X = 0 ↔ _
  rw [← Matrix.ext_iff]
  simp [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem basis_mem (ε : Fin n → Bool) : ∀ Z ∈ kList ε ++ pList ε, Z ∈ lieSet ε := by
  intro Z hZ
  rw [mem_lie_iff]
  intro a b
  simp only [kList, pList, List.mem_append, List.mem_map, List.mem_flatMap, mem_pairs, List.mem_cons,
    List.not_mem_nil, or_false] at hZ
  rcases hZ with (⟨c, -, rfl⟩ | ⟨⟨c, d⟩, ⟨h1, h2⟩, rfl | rfl⟩) | ⟨⟨c, d⟩, ⟨h1, h2⟩, rfl | rfl⟩
  · by_cases h : c = a ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h
      cases hc : ε c <;> simp
    · have h' : ¬ (c = b ∧ c = a) := fun k => h k.symm
      simp [Matrix.single_apply, h, h']
  all_goals
    have h3 : c ≠ d := h1.ne
    simp only [beq_iff_eq, beq_eq_false_iff_ne] at h2
    by_cases e1 : c = a ∧ d = b
    · obtain ⟨rfl, rfl⟩ := e1
      cases hc : ε c <;> cases hd : ε d <;> simp_all [Matrix.single_apply, h3, h3.symm]
    · by_cases e2 : d = a ∧ c = b
      · obtain ⟨rfl, rfl⟩ := e2
        cases hc : ε c <;> cases hd : ε d <;> simp_all [Matrix.single_apply, h3, h3.symm]
      · have e3 : ¬ (d = b ∧ c = a) := fun h => e1 h.symm
        have e4 : ¬ (c = b ∧ d = a) := fun h => e2 h.symm
        simp [Matrix.single_apply, e1, e2, e3, e4]

theorem mem_span_basis (ε : Fin n → Bool) {X : Mx n} (hX : X ∈ lieSet ε) :
    X ∈ Submodule.span ℝ {Z | Z ∈ kList ε ++ pList ε} := by
  rw [mem_lie_iff] at hX
  set S := Submodule.span ℝ {Z | Z ∈ kList ε ++ pList ε} with hS
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
  have lt : ∀ a b, a < b → Matrix.single a b (X a b) + Matrix.single b a (X b a) ∈ S := by
    intro a b hab
    have h := hX b a
    have hne := hab.ne
    by_cases e : ε a = ε b
    · have m1 : invSqrtTwo • (unitE a b - unitE b a) ∈ S := Submodule.subset_span (by
        simp only [kList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, by simp [e]⟩, by simp⟩))
      have m2 : (invSqrtTwo * Complex.I) • (unitE a b + unitE b a) ∈ S := Submodule.subset_span (by
        simp only [kList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, by simp [e]⟩, by simp⟩))
      have h' : X b a = -star (X a b) := by
        rw [e] at h
        cases hb : ε b <;> simp only [hb] at h <;> simp at h ⊢
        exacts [by linear_combination -h, by linear_combination h]
      convert add_mem (S.smul_mem (√2 * (X a b).re) m1) (S.smul_mem (√2 * (X a b).im) m2) using 1
      rw [h', ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
      push_cast
      rw [mul_right_comm, mul_inv_cancel₀ hs, ← mul_assoc, mul_right_comm _ _ invSqrtTwo, mul_inv_cancel₀ hs]
      simp only [smul_sub, smul_add, Matrix.smul_single, one_mul, smul_eq_mul, mul_one]
      rw [sub_eq_add_neg, Matrix.single_neg, add_add_add_comm, ← Matrix.single_add, ← Matrix.single_add]
      congr 2 <;> apply Complex.ext <;> simp
    · have e' : (ε a == ε b) = false := by simpa using e
      have m1 : invSqrtTwo • (unitE a b + unitE b a) ∈ S := Submodule.subset_span (by
        simp only [pList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, e'⟩, by simp⟩)
      have m2 : (invSqrtTwo * Complex.I) • (unitE a b - unitE b a) ∈ S := Submodule.subset_span (by
        simp only [pList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, e'⟩, by simp⟩)
      have h' : X b a = star (X a b) := by
        cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb] at h e <;> simp at h e ⊢
        exacts [by linear_combination h, by linear_combination -h]
      convert add_mem (S.smul_mem (√2 * (X a b).re) m1) (S.smul_mem (√2 * (X a b).im) m2) using 1
      rw [h', ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
      push_cast
      rw [mul_right_comm, mul_inv_cancel₀ hs, ← mul_assoc, mul_right_comm _ _ invSqrtTwo, mul_inv_cancel₀ hs]
      simp only [smul_sub, smul_add, Matrix.smul_single, one_mul, smul_eq_mul, mul_one]
      rw [sub_eq_add_neg, Matrix.single_neg, add_add_add_comm, ← Matrix.single_add, ← Matrix.single_add]
      congr 2 <;> apply Complex.ext <;> simp
  have dg : ∀ a, Matrix.single a a (X a a) ∈ S := by
    intro a
    have m1 : Complex.I • unitE a a ∈ S := Submodule.subset_span (by
      simp only [kList, Set.mem_setOf_eq, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨a, by simp, rfl⟩))
    have h : (X a a).re = 0 := by
      have := congrArg Complex.re (hX a a)
      cases hb : ε a <;> simp [hb] at this <;> linarith
    convert S.smul_mem (X a a).im m1 using 1
    rw [← Complex.coe_smul, smul_smul, Matrix.smul_single]
    congr 1
    apply Complex.ext <;> simp [h]
  have all : ∀ a b, Matrix.single a b (X a b) + Matrix.single b a (X b a) ∈ S := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact lt a b h
    · exact add_mem (dg a) (dg a)
    · rw [add_comm]; exact lt b a h
  have e : X = (1 / 2 : ℝ) • ∑ a, ∑ b, (Matrix.single a b (X a b) + Matrix.single b a (X b a)) := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => Matrix.single b a (X b a)), ← Matrix.matrix_eq_sum_single, ← two_smul ℝ,
      smul_smul]
    simp
  rw [e]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.sum_mem fun b _ => all a b)

theorem word_le_lapOne : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖ := by
  intro n ε H _ _ _ σ h l hl
  set L := kList ε ++ pList ε with hL
  have hB : ∀ i, L.get i ∈ lieSet ε := fun i => basis_mem ε _ (List.get_mem _ _)
  let D : Fin L.length → Module.End ℂ (smooth (Jm ε) σ) := fun i => dOp (isUnit_Jm ε) h.1 (hB i)
  have hsp : ∀ X (hX : X ∈ lieSet ε), dOp (isUnit_Jm ε) h.1 hX ∈ Submodule.span ℂ (Set.range D) := by
    intro X hX
    have h1 := mem_span_basis ε hX
    rw [← hL, ← Set.range_list_get] at h1
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨fun i => c i, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    exact (h.dRep_sum hB w.2 c).symm
  have hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ := fun i x y =>
    inner_dRep (isUnit_Jm ε) h.1 x.2 y.2 (hB i)
  have hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D) := by
    intro i j
    have hX := hB i
    have hY := hB j
    have hm : L.get i * L.get j - L.get j * L.get i ∈ lieSet ε := by
      generalize L.get i = X at *
      generalize L.get j = Y at *
      have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
      have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
      show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
      rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
        mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
      noncomm_ring
    convert hsp _ hm using 1
    exact LinearMap.ext fun w => Subtype.ext (dRep_bracket n ε H σ h w w.2 _ hX _ hY)
  have hw : ∃ T ∈ filt D l.length, ∀ w : smooth (Jm ε) σ, (T w : H) = Dw σ l w := by
    induction l with
    | nil => exact ⟨1, Submodule.subset_span (by simp [words]), fun _ => rfl⟩
    | cons X l ih =>
      obtain ⟨T, hT, e⟩ := ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      exact ⟨_, mul_mem_filt (hsp X (hl X List.mem_cons_self)) hT, fun w => by
        rw [Dw, List.foldr_cons, ← Dw, ← e]; rfl⟩
  have hA : ∀ w : smooth (Jm ε) σ, (lap D w : H) = lapOne ε σ w := by
    intro w
    have e : ∀ M : List (Mx n), ∑ i, dRep σ (M.get i) (dRep σ (M.get i) w) =
        (M.map fun Z => dRep σ Z (dRep σ Z w)).sum := fun M =>
      Fin.sum_univ_fun_getElem M fun Z => dRep σ Z (dRep σ Z w)
    simp only [lap, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, Submodule.coe_sub,
      Submodule.coe_sum, lapOne, onePlusCas, kB, pB, e, sub_sub]
    rw [← List.sum_append, ← List.map_append, ← hL, ← e]
    rfl
  have hAs : ∀ (s : ℕ) (w : smooth (Jm ε) σ), ((lap D ^ s) w : H) = (lapOne ε σ)^[s] w := by
    intro s
    induction s with
    | zero => intro w; rfl
    | succ s ih => intro w; rw [pow_succ', Module.End.mul_apply, hA, ih, Function.iterate_succ_apply']
  obtain ⟨T, hT, e⟩ := hw
  obtain ⟨C, hC⟩ := exists_le_of_mem_filt hsk hbr hT
  refine ⟨l.length, C, fun v hv => ?_⟩
  have := hC ⟨v, hv⟩
  rwa [Submodule.coe_norm, Submodule.coe_norm, e, hAs] at this

end GlobalTheory.TypeSum.Elliptic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EllipticEstimateWordLeOnePlusLaplacianPowStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_estimate_word_le_onePlusLaplacian_pow : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖ := by
  first | exact @GlobalTheory.TypeSum.Elliptic.word_le_lapOne | exact GlobalTheory.TypeSum.Elliptic.word_le_lapOne | (intros; apply GlobalTheory.TypeSum.Elliptic.word_le_lapOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WordsOnWeightedCasimirEigenvectorsBoundedFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WordsOnWeightedCasimirEigenvectorsBoundedFrame
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {q : ℕ}
    (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have h := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, hL, Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

theorem frame_sm_sum {q : ℕ} (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    Sm ε σ (∑ i, c i • x i) :=
  (smooth (Jm ε) σ).sum_mem fun i _ => (smooth (Jm ε) σ).smul_mem (c i) (hx i)

theorem frame_dRep2_sum (hσ : IsURepOn (UJset ε) σ) {X : Mx n} (hX : X ∈ lieSet ε) {q : ℕ}
    (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    dRep σ X (dRep σ X (∑ i, c i • x i)) = ∑ i, c i • dRep σ X (dRep σ X (x i)) := by
  have := frame_Dw_sum hσ (l := [X, X]) (by simp [hX]) c hx
  simpa [Dw] using this

theorem frame_lapOne_sum (hσ : IsURepOn (UJset ε) σ) (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε)
    {q : ℕ} (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    lapOne ε σ (∑ i, c i • x i) = ∑ i, c i • lapOne ε σ (x i) := by
  simp only [lapOne, onePlusCas, frame_dRep2_sum hσ (hk _) c hx, frame_dRep2_sum hσ (hp _) c hx,
    smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (γ := Fin q), Finset.sum_comm (γ := Fin q)]

theorem frame_lapOne_eig {χ : ℂ}
    (hcas : ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v))
    {e : H} (he : Sm ε σ e) {μ : ℝ} (h : onePlusCas σ (kB ε) e = (μ : ℂ) • e) :
    lapOne ε σ e = (((2 * μ : ℝ) : ℂ) - (1 + χ)) • e := by
  have hs : ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) e) = e - (μ : ℂ) • e := by
    rw [← h, onePlusCas]; abel
  rw [lapOne, hcas e he, hs, h]
  push_cast
  module

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_iterate (hσ : IsURepOn (UJset ε) σ) (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε)
    {q : ℕ} {e : Fin q → H} (he : ∀ j, Sm ε σ (e j)) (c : Fin q → ℂ) (hc : ∀ j, lapOne ε σ (e j) = c j • e j)
    (r : ℕ) (b : Fin q → ℂ) :
    (lapOne ε σ)^[r] (∑ j, b j • e j) = ∑ j, (b j * c j ^ r) • e j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, frame_lapOne_sum hσ hk hp _ he]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc, smul_smul, pow_succ, mul_assoc]

theorem frame_norm_sq {q : ℕ} {e : Fin q → H} (ho : Orthonormal ℂ e) (d : Fin q → ℂ) :
    ‖∑ j, d j • e j‖ ^ 2 = ∑ j, ‖d j‖ ^ 2 := by
  have h := ho.inner_sum d d Finset.univ
  rw [@norm_sq_eq_re_inner ℂ, h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Complex.conj_mul', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.re_to_complex]
  norm_cast

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_coef_bound (χ : ℂ) {μ : ℝ} (hμ : 1 ≤ μ) {s₀ s : ℕ} (hs : s₀ ≤ s) (z : ℂ) :
    ‖((((μ ^ s)⁻¹ : ℝ) : ℂ) * z) * (((2 * μ : ℝ) : ℂ) - (1 + χ)) ^ s₀‖ ≤ (2 + ‖1 + χ‖) ^ s₀ * ‖z‖ := by
  have hc : ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ≤ (2 + ‖1 + χ‖) * μ := by
    calc ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ≤ ‖((2 * μ : ℝ) : ℂ)‖ + ‖1 + χ‖ := norm_sub_le _ _
      _ = 2 * μ + ‖1 + χ‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ _ := by nlinarith [norm_nonneg (1 + χ)]
  have hμs : 0 < μ ^ s := pow_pos (by linarith) _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hμs.le)]
  have h1 : ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ^ s₀ ≤ ((2 + ‖1 + χ‖) * μ) ^ s₀ := pow_le_pow_left₀ (norm_nonneg _) hc s₀
  have h2 : μ ^ s₀ ≤ μ ^ s := pow_le_pow_right₀ hμ hs
  have hK : 0 ≤ (2 + ‖1 + χ‖) ^ s₀ := by positivity
  rw [mul_pow] at h1
  calc (μ ^ s)⁻¹ * ‖z‖ * ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ^ s₀
      ≤ (μ ^ s)⁻¹ * ‖z‖ * ((2 + ‖1 + χ‖) ^ s₀ * μ ^ s₀) := by gcongr
    _ ≤ (μ ^ s)⁻¹ * ‖z‖ * ((2 + ‖1 + χ‖) ^ s₀ * μ ^ s) := by gcongr
    _ = (2 + ‖1 + χ‖) ^ s₀ * ‖z‖ := by field_simp

theorem frame_word (hσ : IsURepOn (UJset ε) σ) (hKS : ∀ v, IsKFin ε σ v → Sm ε σ v)
    (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε) {χ : ℂ}
    (hcas : ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v))
    {m : List (Mx n)} (hm : ∀ X ∈ m, X ∈ lieSet ε) {s₀ : ℕ} {C₀ : ℝ}
    (hest : ∀ v, Sm ε σ v → ‖Dw σ m v‖ ≤ C₀ * ‖(lapOne ε σ)^[s₀] v‖) {s : ℕ} (hs : s₀ ≤ s)
    {q : ℕ} {e : Fin q → H} {μ : Fin q → ℝ} (ho : Orthonormal ℂ e) (hkf : ∀ i, IsKFin ε σ (e i))
    (hμ : ∀ i, 1 ≤ μ i) (heig : ∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) (z : Fin q → ℂ) :
    ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤
      (max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀)) * ∑ j, ‖z j‖ ^ 2 := by
  have he : ∀ j, Sm ε σ (e j) := fun j => hKS _ (hkf j)
  have hc : ∀ j, lapOne ε σ (e j) = (fun j => ((2 * μ j : ℝ) : ℂ) - (1 + χ)) j • e j := fun j =>
    frame_lapOne_eig hcas (he j) (heig j)
  rw [← frame_Dw_sum hσ hm _ he]
  have h1 := hest _ (frame_sm_sum (fun j => (((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) he)
  rw [frame_iterate hσ hk hp he _ hc s₀] at h1
  have h2 := h1.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, frame_norm_sq ho] at h3
  refine h3.trans ?_
  rw [mul_assoc (max C₀ 0 ^ 2), Finset.mul_sum Finset.univ (fun j => ‖z j‖ ^ 2) ((2 + ‖1 + χ‖) ^ (2 * s₀))]
  gcongr with j
  have := frame_coef_bound χ (hμ j) hs (z j)
  calc _ ≤ ((2 + ‖1 + χ‖) ^ s₀ * ‖z j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := by ring

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

theorem frame_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  intro n ε H _ _ _ σ hstd hk hp χ hcas hell T hT
  have hσ := hstd.1
  have hKS := hstd.2.2.1
  have key : ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∃ (s₀ : ℕ) (C₀ : ℝ),
      s₀ ≤ s ∧ (∀ v, Sm ε σ v → ‖Dw σ m v‖ ≤ C₀ * ‖(lapOne ε σ)^[s₀] v‖) ∧
        max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀) ≤ C := by
    intro T
    induction T with
    | nil => intro _; exact ⟨0, 0, by simp⟩
    | cons m T ih =>
      intro hT
      obtain ⟨s₁, C₁, h₁⟩ := ih (fun l hl => hT l (List.mem_cons_of_mem _ hl))
      obtain ⟨s₀, C₀, h₀⟩ := hell m (hT m List.mem_cons_self)
      refine ⟨max s₀ s₁, max (max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀)) C₁, fun l hl => ?_⟩
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨s₀, C₀, le_max_left _ _, h₀, le_max_left _ _⟩
      · obtain ⟨s', C', hs', he', hC'⟩ := h₁ l hl
        exact ⟨s', C', hs'.trans (le_max_right _ _), he', hC'.trans (le_max_right _ _)⟩
  obtain ⟨s, C, hsC⟩ := key T hT
  refine ⟨s, C, fun m hm q e μ ho hkf hμ heig z => ?_⟩
  obtain ⟨s₀, C₀, hs, hest, hC⟩ := hsC m hm
  exact (frame_word hσ hKS hk hp hcas (hT m hm) hest hs ho hkf hμ heig z).trans
    (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun j _ => by positivity))

end GlobalTheory.TypeSum.CasBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WordsOnWeightedCasimirEigenvectorsBoundedFrameStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.frame_bounded | exact GlobalTheory.TypeSum.CasBasis.frame_bounded | (intros; apply GlobalTheory.TypeSum.CasBasis.frame_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesProps
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesProps
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasisFacts

variable {n : ℕ}

lemma inG_iff_entry (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j = true then (1:ℂ) else -1) +
      (if ε i = true then (1:ℂ) else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [mul_diagonal, diagonal_mul, conjTranspose_apply] using this
  · intro h
    ext i j
    simpa [mul_diagonal, diagonal_mul, conjTranspose_apply] using h i j

lemma i_smul_diag_casimir_unit_mem_indefinite_lie (ε : Fin n → Bool) (a : Fin n) : inG ε (Complex.I • unitE a a) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> grind

lemma same_sign_casimir_skew_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a = ε b) :
    inG ε (invSqrtTwo • (unitE a b - unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma same_sign_casimir_i_sym_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a = ε b) :
    inG ε ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma opp_sign_casimir_sym_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a ≠ ε b) :
    inG ε (invSqrtTwo • (unitE a b + unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma opp_sign_casimir_i_skew_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a ≠ ε b) :
    inG ε ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma i_smul_diag_casimir_unit_skewHermitian (a : Fin n) : (Complex.I • unitE a a)ᴴ = -(Complex.I • unitE a a) := by
  simp [unitE, Matrix.conjTranspose_single]
  ext i j
  simp [Matrix.single_apply]
  split_ifs <;> simp

lemma casimir_unit_skew_diff_skewHermitian (a b : Fin n) :
    (invSqrtTwo • (unitE a b - unitE b a))ᴴ = -(invSqrtTwo • (unitE a b - unitE b a)) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  module

lemma casimir_unit_i_sym_sum_skewHermitian (a b : Fin n) :
    ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))ᴴ =
      -((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  ext i j
  simp [Matrix.single_apply]
  split_ifs <;> simp

lemma casimir_unit_sym_sum_hermitian (a b : Fin n) :
    (invSqrtTwo • (unitE a b + unitE b a))ᴴ = invSqrtTwo • (unitE a b + unitE b a) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single, add_comm]

lemma casimir_unit_i_skew_diff_hermitian (a b : Fin n) :
    ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a))ᴴ =
      (invSqrtTwo * Complex.I) • (unitE a b - unitE b a) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  module

lemma i_smul_diag_casimir_unit_hs_le_one (a : Fin n) : hs (Complex.I • unitE a a) ≤ 1 := by
  unfold hs
  have : ∀ i j, ‖(Complex.I • unitE a a) i j‖ ^ 2 = if a = i then (if a = j then 1 else 0) else 0 := by
    intro i j
    simp only [unitE, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  simp only [this]
  simp

lemma pair_hs (a b : Fin n) (hab : a ≠ b) (c : ℂ) (hc : ‖c‖ ^ 2 = 1 / 2) (t : ℂ) (ht : ‖t‖ = 1) :
    hs (c • (unitE a b + t • unitE b a)) ≤ 1 := by
  unfold hs
  have : ∀ i j, ‖(c • (unitE a b + t • unitE b a)) i j‖ ^ 2 =
      (if a = i then (if b = j then 1 / 2 else 0) else 0) +
        (if b = i then (if a = j then 1 / 2 else 0) else 0) := by
    intro i j
    simp only [unitE, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all [norm_mul, mul_pow]
  simp only [this]
  simp [Finset.sum_add_distrib]
  norm_num

lemma norm_sq_invSqrtTwo : ‖invSqrtTwo‖ ^ 2 = 1 / 2 := by
  simp [invSqrtTwo, norm_inv, inv_pow]

lemma casimir_unit_skew_diff_hs_le_one (a b : Fin n) (hab : a ≠ b) : hs (invSqrtTwo • (unitE a b - unitE b a)) ≤ 1 := by
  have e : unitE a b - unitE b a = unitE a b + (-1 : ℂ) • unitE b a := by
    simp [sub_eq_add_neg]
  rw [e]
  exact pair_hs a b hab _ norm_sq_invSqrtTwo _ (by simp)

lemma casimir_unit_i_sym_sum_hs_le_one (a b : Fin n) (hab : a ≠ b) :
    hs ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) ≤ 1 := by
  have e : unitE a b + unitE b a = unitE a b + (1 : ℂ) • unitE b a := by simp
  rw [e]
  exact pair_hs a b hab _ (by rw [norm_mul, mul_pow, norm_sq_invSqrtTwo]; simp) _ (by simp)

lemma mem_pairs {ε : Fin n → Bool} {same : Bool} {a b : Fin n} (h : (a, b) ∈ pairs ε same) :
    a ≠ b ∧ ((ε a = ε b) ↔ same = true) := by
  simp only [pairs, List.mem_filter, List.pair_mem_product, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨ne_of_lt h.1, ?_⟩
  have h2 := h.2
  cases same <;> cases hx : ε a <;> cases hy : ε b <;> simp_all

end GlobalTheory.TypeSum.CasBasisFacts


open GlobalTheory.TypeSum.CasBasisFacts in
theorem GlobalTheory.TypeSum.CasBasis.bases_mem_lie : ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧
      ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  intro n ε
  constructor
  · intro i
    have hm : kB ε i ∈ kList ε := List.get_mem _ _
    generalize kB ε i = X at hm ⊢
    simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨a, -, rfl⟩ | ⟨⟨a, b⟩, hp, rfl | rfl⟩
    · exact ⟨i_smul_diag_casimir_unit_mem_indefinite_lie ε a, i_smul_diag_casimir_unit_skewHermitian a, i_smul_diag_casimir_unit_hs_le_one a⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨same_sign_casimir_skew_sum_mem_indefinite_lie ε a b hab (he.2 rfl), casimir_unit_skew_diff_skewHermitian a b, casimir_unit_skew_diff_hs_le_one a b hab⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨same_sign_casimir_i_sym_sum_mem_indefinite_lie ε a b hab (he.2 rfl), casimir_unit_i_sym_sum_skewHermitian a b, casimir_unit_i_sym_sum_hs_le_one a b hab⟩
  · intro i
    have hm : pB ε i ∈ pList ε := List.get_mem _ _
    generalize pB ε i = X at hm ⊢
    simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨⟨a, b⟩, hp, rfl | rfl⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨opp_sign_casimir_sym_sum_mem_indefinite_lie ε a b hab (fun h => by simpa using he.1 h), casimir_unit_sym_sum_hermitian a b⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨opp_sign_casimir_i_skew_sum_mem_indefinite_lie ε a b hab (fun h => by simpa using he.1 h), casimir_unit_i_skew_diff_hermitian a b⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesPropsStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧ ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lie | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lie | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lie <;> assumption)
end
end

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.TraceBound

theorem trace_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε ∧ (X i)ᴴ = -X i ∧ hs (X i) ≤ 1) ∧ ∀ S : List (List (Mx n)), Words (lieSet ε) S → ∃ (r : ℕ) (A : ℝ), ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ S (e i) ^ 2 / μ i ^ r ≤ A := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨hk, hp⟩ := GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props n ε
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors n ε H σ hσ
  refine ⟨_, kB ε, hk, fun S hS => ?_⟩
  obtain ⟨S0, C0, hS0, hC0, HS⟩ := SobHS.sobolev_hilbertSchmidt n ε H σ hσ
  have hT : Words (lieSet ε) (S.flatMap fun l => S0.map (· ++ l)) := by
    intro m hm X hX
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.1 hm
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hm
    exact (List.mem_append.1 hX).elim (hS0 l' hl' X) (hS l hl X)
  obtain ⟨s, C, hC⟩ := GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame n ε H σ hσ (fun i => (hk i).1) (fun b => (hp b).1) χ hχ (GlobalTheory.T.elliptic_estimate_word_le_onePlusLaplacian_pow n ε H σ hσ) _ hT
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨2 * s, S.length * (S.length * (C0 * C')), fun q e μ he hK hμ heig => ?_⟩
  have hsm : ∀ j, Sm ε σ (e j) := fun j => hσ.2.2.1 _ (hK j)
  have hμ0 : ∀ j, 0 < μ j := fun j => lt_of_lt_of_le one_pos (hμ j)

  have key : ∀ l ∈ S, ∑ j, ‖Dw σ l (e j)‖ ^ 2 / μ j ^ (2 * s) ≤ C0 * C' := by
    intro l hl
    have hlw : ∀ X ∈ l, X ∈ lieSet ε := hS l hl
    set c : Fin q → ℝ := fun j => (μ j ^ s)⁻¹ with hc
    have hc0 : ∀ j, 0 ≤ c j := fun j => inv_nonneg.2 (pow_nonneg (hμ0 j).le _)
    set x : Fin q → H := fun j => ((c j : ℝ) : ℂ) • Dw σ l (e j) with hx
    have hxs : ∀ j, Sm ε σ (x j) := fun j =>
      sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ((hsm j).word hσ.1 hlw)))
    have hframe : ∀ l' ∈ S0, ∀ z : Fin q → ℂ, ‖∑ j, z j • Dw σ l' (x j)‖ ^ 2 ≤ C' * ∑ j, ‖z j‖ ^ 2 := by
      intro l' hl' z
      have e1 : ∀ j, z j • Dw σ l' (x j) = (((c j : ℝ) : ℂ) * z j) • Dw σ (l' ++ l) (e j) := fun j => by
        rw [hx, Dw_smul hσ.1 (hS0 l' hl') _ ((hsm j).word hσ.1 hlw), Dw_append, smul_smul, mul_comm]
      simp only [e1]
      have hm : l' ++ l ∈ S.flatMap fun l => S0.map (· ++ l) :=
        List.mem_flatMap.2 ⟨l, hl, List.mem_map.2 ⟨l', hl', rfl⟩⟩
      refine (hC _ hm q e μ he hK hμ heig z).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ => by positivity)
    have hH := HS (Fin q) x x C' hC'0 hxs hframe
    have eQ : ∑ j, ⟪x j, x j⟫_ℂ = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => inner_self_eq_norm_sq_to_K (x j)
    rw [eQ, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hH
    have hQ0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hQ : ∑ j, ‖x j‖ ^ 2 ≤ C0 * C' := by
      by_contra hne
      push_neg at hne
      have hK0 : 0 ≤ C0 * C' := mul_nonneg hC0 hC'0
      nlinarith
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hQ
    rw [hx]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 j), mul_pow, hc, inv_pow, ← pow_mul,
      mul_comm s 2, div_eq_mul_inv, mul_comm]

  have hcs : ∀ j, sobNorm σ S (e j) ^ 2 ≤ S.length * ∑ i : Fin S.length, ‖Dw σ S[i] (e j)‖ ^ 2 := by
    intro j
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin S.length)))
      (f := fun i => ‖Dw σ S[i] (e j)‖)
    rw [Finset.card_univ, Fintype.card_fin] at this
    unfold sobNorm
    rw [← Fin.sum_univ_fun_getElem]
    exact this
  calc ∑ j, sobNorm σ S (e j) ^ 2 / μ j ^ (2 * s)
      ≤ ∑ j, (S.length * ∑ i : Fin S.length, ‖Dw σ S[i] (e j)‖ ^ 2) / μ j ^ (2 * s) :=
        Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hcs j) (pow_nonneg (hμ0 j).le _)
    _ = S.length * ∑ i : Fin S.length, ∑ j, ‖Dw σ S[i] (e j)‖ ^ 2 / μ j ^ (2 * s) := by
        simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc]
        exact Finset.sum_comm
    _ ≤ S.length * ∑ _i : Fin S.length, C0 * C' := by
        gcongr with i
        exact key _ (List.getElem_mem _)
    _ = S.length * (S.length * (C0 * C')) := by simp

end GlobalTheory.TypeSum.TraceBound

module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Analytic
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.NcBound
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.WeightBound
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.LayerSpan
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def layerWtVecs (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (k : ℕ) : Set M :=
  {w | ∃ ν ω : Fin n → ℝ, ∃ j ≤ k, IsNCSum ε j ω ∧
    (∃ v ∈ V, v ≠ 0 ∧ ∀ a, E a a v = (ν a : ℂ) • v) ∧ ∀ a, E a a w = ((ν + ω) a : ℂ) • w}

theorem isNCSum_add_root {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω) {a b : Fin n}
    (hab : ε a ≠ ε b) : IsNCSum ε (j + 1) (ω + root a b) := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  refine ⟨Fin.snoc (α := fun _ => Fin n × Fin n) γ (a, b), fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hab
    · simpa using hγ i
  · rw [Fin.sum_univ_castSucc]
    simp

theorem diag_apply_of_weight (hE : IsGlRep E) {ω : Fin n → ℝ} {w : M}
    (hw : ∀ c, E c c w = (ω c : ℂ) • w) (a b c : Fin n) :
    E c c (E a b w) = ((ω + root a b) c : ℂ) • E a b w := by
  have h := congrArg (fun T : Module.End ℂ M => T w) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h2 : E c c (E a b w) = E a b (E c c w) +
      ((if c = a then E c b else 0) w - (if b = c then E a c else 0) w) := by
    rw [← h]
    abel
  have e1 : (if c = a then E c b else 0) w = ((if c = a then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : c = a
    · subst h'
      simp
    · simp [h']
  have e2 : (if b = c then E a c else 0) w = ((if c = b then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : b = c
    · subst h'
      simp
    · simp [h', Ne.symm h']
  rw [h2, hw c, map_smul, e1, e2]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  module

theorem le_span_weightVecs (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    V ≤ Submodule.span ℂ {v | v ∈ V ∧ ∃ ν : Fin n → ℝ, ∀ a, E a a v = (ν a : ℂ) • v} := by
  haveI := hVf
  have hst : ∀ a, ∀ v ∈ V, E a a v ∈ V := fun a v hv => hVK a a rfl v hv
  let T : Fin n → Module.End ℂ V := fun a => (E a a).restrict (hst a)
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a
    refine LinearMap.IsSymmetric.restrict_invariant (T := E a a) (fun x y => ?_) (hst a)
    rw [hU a a x y]
    simp [adjSign]
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a c _
    have h := hE a a c c
    have hEc : E a a * E c c = E c c * E a a := by
      rw [← sub_eq_zero, h]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Ne.symm hac]
    show T a * T c = T c * T a
    refine LinearMap.ext fun v => Subtype.ext ?_
    show E a a (E c c v) = E c c (E a a v)
    exact congrArg (fun F : Module.End ℂ M => F (v : M)) hEc
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  intro x hx
  have hy : (⟨x, hx⟩ : V) ∈ ⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  show ((⟨x, hx⟩ : V) : M) ∈ _
  refine Submodule.iSup_induction _ (motive := fun y : V => (y : M) ∈ Submodule.span ℂ _) hy ?_ ?_ ?_
  · intro χ y hy
    rw [Submodule.mem_iInf] at hy
    by_cases hy0 : y = 0
    · subst hy0
      exact Submodule.zero_mem _
    · have hreal : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := by
        intro a
        have hev : Module.End.HasEigenvalue (T a) (χ a) := by
          first
            | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy a, hy0⟩
            | exact (Submodule.ne_bot_iff _).2 ⟨y, hy a, hy0⟩
        exact Complex.conj_eq_iff_re.1 ((hsym a).conj_eigenvalue_eq_self hev)
      refine Submodule.subset_span ⟨y.2, fun a => (χ a).re, fun a => ?_⟩
      have h := Module.End.mem_eigenspace_iff.1 (hy a)
      have h' := congrArg Subtype.val h
      simp only [T, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h'
      rw [h', hreal a]
  · exact Submodule.zero_mem _
  · intro y z hy hz
    simpa using Submodule.add_mem _ hy hz

theorem layerWtVecs_mono {k l : ℕ} (h : k ≤ l) : layerWtVecs ε E V k ⊆ layerWtVecs ε E V l := by
  rintro w ⟨ν, ω, j, hj, hω, hv, hw⟩
  exact ⟨ν, ω, j, hj.trans h, hω, hv, hw⟩

theorem layer_le_span (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) (k : ℕ) :
    layer ε E V k ≤ Submodule.span ℂ (layerWtVecs ε E V k) := by
  induction k with
  | zero =>
    refine (le_span_weightVecs hE hU hVf hVK).trans (Submodule.span_le.2 fun w hw => ?_)
    obtain ⟨hwV, ν, hν⟩ := hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨ν, 0, 0, le_refl 0, ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩,
        ⟨w, hwV, hw0, hν⟩, fun a => by simpa using hν a⟩
  | succ k ih =>
    show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _
    refine sup_le (ih.trans (Submodule.span_mono (layerWtVecs_mono (Nat.le_succ k))))
      (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    refine (Submodule.map_mono ih).trans ?_
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, ⟨ν, ω, j, hj, hω, hv, hw⟩, rfl⟩
    refine ⟨ν, ω + root a b, j + 1, by omega, isNCSum_add_root hω hab, hv, fun c => ?_⟩
    rw [diag_apply_of_weight hE hw a b c, add_assoc]

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem sqrt_nsq_eq_norm' (x : Fin n → ℝ) :
    √(nsq x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  first
    | (rw [EuclideanSpace.norm_eq]
       congr 1
       simp [nsq, dot, Real.norm_eq_abs, sq])
    | (rw [EuclideanSpace.norm_eq]
       congr 1
       simp only [nsq, dot, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, sq])

theorem nsq_nonneg' (x : Fin n → ℝ) : 0 ≤ nsq x := by
  unfold nsq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_weight_bound (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R := by
  classical
  haveI := hVf
  have hT : ∀ a, {r : ℝ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) (r : ℂ)}.Finite := by
    intro a
    have hf : {μ : ℂ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) μ}.Finite := by
      first
        | exact Module.End.finite_hasEigenvalue _
        | exact (Module.End.finite_spectrum _).subset fun μ h => h.mem_spectrum
    exact hf.preimage Complex.ofReal_injective.injOn
  have hW := Set.Finite.pi hT
  obtain ⟨B, hB⟩ := (hW.image fun ν => √(nsq (ν + rhoC ε))).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun v hv hv0 ν hν => ?_⟩
  have hmem : ν ∈ Set.pi Set.univ fun a =>
      {r : ℝ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) (r : ℂ)} := by
    intro a _
    have hx : ((E a a).restrict (hVK a a rfl)) ⟨v, hv⟩ = (ν a : ℂ) • (⟨v, hv⟩ : V) := by
      apply Subtype.ext
      simp [hν a]
    have hx0 : (⟨v, hv⟩ : V) ≠ 0 := by simpa using hv0
    first
      | exact Module.End.hasEigenvalue_of_hasEigenvector
          (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩)
      | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩
  exact (hB ⟨ν, hmem, rfl⟩).trans (le_max_left _ _)

theorem sqrt_nsq_add_le (x y : Fin n → ℝ) : √(nsq (x + y)) ≤ √(nsq x) + √(nsq y) := by
  rw [sqrt_nsq_eq_norm', sqrt_nsq_eq_norm', sqrt_nsq_eq_norm']
  first
    | (rw [WithLp.toLp_add]; exact norm_add_le _ _)
    | (have h := norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)
       rwa [← WithLp.toLp_add] at h)

theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [nsq, dot]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (add_le_add le_rfl ih)

theorem sqrt_nsq_add_ncSum_le {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω)
    (x : Fin n → ℝ) :
    √(nsq (x + ω)) ≤ √(nsq x) + √2 * j := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  have hroot : ∀ a b : Fin n, a ≠ b → nsq (root a b) = 2 := by
    intro a b hne
    unfold nsq dot
    rw [Fintype.sum_eq_add a b hne]
    · norm_num [root, Pi.single_apply, hne, hne.symm]
    · intro c hc
      simp [root, Pi.single_apply, hc.1, hc.2]
  have hr : ∀ i, √(nsq (root (γ i).1 (γ i).2)) ≤ √2 := fun i => by
    have hne : (γ i).1 ≠ (γ i).2 := fun h => hγ i (congrArg ε h)
    exact le_of_eq (by rw [hroot _ _ hne])
  calc √(nsq (x + ∑ i, root (γ i).1 (γ i).2))
      ≤ √(nsq x) + √(nsq (∑ i, root (γ i).1 (γ i).2)) := sqrt_nsq_add_le _ _
    _ ≤ √(nsq x) + ∑ i, √(nsq (root (γ i).1 (γ i).2)) :=
        add_le_add le_rfl (sqrt_nsq_sum_le _ _)
    _ ≤ √(nsq x) + ∑ _i : Fin j, √2 := add_le_add le_rfl (Finset.sum_le_sum fun i _ => hr i)
    _ = √(nsq x) + √2 * j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem weight_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) {R : ℝ}
    (hR : ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R)
    (k : ℕ) {w : M} (hw : w ∈ layer ε E V k) (hw0 : w ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, E a a w = (μ a : ℂ) • w) :
    √(nsq (μ + rhoC ε)) ≤ R + √2 * k := by
  classical
  have hspan := layer_le_span hE hU hVf hVK k hw
  by_contra hcon
  have hP : ∀ s ∈ layerWtVecs ε E V k, (∀ a, ∃ l : ℂ, E a a s = l • s) ∧
      (s = 0 ∨ ∃ a, ∃ l : ℝ, l ≠ μ a ∧ E a a s = (l : ℂ) • s) := by
    intro s hs
    obtain ⟨ν, ω, j, hj, hω, ⟨v, hv, hv0, hνv⟩, hs'⟩ := hs
    refine ⟨fun a => ⟨_, hs' a⟩, ?_⟩
    by_cases hl : ν + ω = μ
    · exfalso
      subst hl
      apply hcon
      rw [add_right_comm]
      calc √(nsq (ν + rhoC ε + ω)) ≤ √(nsq (ν + rhoC ε)) + √2 * j := sqrt_nsq_add_ncSum_le hω _
        _ ≤ R + √2 * k := add_le_add (hR v hv hv0 ν hνv)
            (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hj) (Real.sqrt_nonneg 2))
    · right
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hl
      exact ⟨a, (ν + ω) a, ha, hs' a⟩
  have key : ∀ G : Finset M, (∀ s ∈ G, (∀ a, ∃ l : ℂ, E a a s = l • s) ∧
      (s = 0 ∨ ∃ a, ∃ l : ℝ, l ≠ μ a ∧ E a a s = (l : ℂ) • s)) →
      ∃ T : Module.End ℂ M, ∃ c : ℂ, c ≠ 0 ∧ T w = c • w ∧ ∀ s ∈ G, T s = 0 := by
    intro G
    refine Finset.induction_on G ?_ ?_
    · intro _
      exact ⟨1, 1, one_ne_zero, by simp, by simp⟩
    · intro s G hsG ih hG
      obtain ⟨T, c, hc, hTw, hTG⟩ := ih fun x hx => hG x (Finset.mem_insert_of_mem hx)
      rcases (hG s (Finset.mem_insert_self s G)).2 with h0 | ⟨a, l, hl, hs⟩
      · refine ⟨T, c, hc, hTw, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · rw [h0, map_zero]
        · exact hTG x hx
      · refine ⟨T * (E a a - (l : ℂ) • 1), c * ((μ a : ℂ) - l),
          mul_ne_zero hc (sub_ne_zero.2 (by exact_mod_cast hl.symm)), ?_, ?_⟩
        · have h1 : (T * (E a a - (l : ℂ) • 1)) w = T (((μ a : ℂ) - l) • w) := by
            simp [hμ a, sub_smul]
          rw [h1, map_smul, hTw, smul_smul, mul_comm]
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp [hs]
          · obtain ⟨l', hx'⟩ := (hG x (Finset.mem_insert_of_mem hx)).1 a
            have h2 : (T * (E a a - (l : ℂ) • 1)) x = T ((l' - l) • x) := by
              simp [hx', sub_smul]
            rw [h2, map_smul, hTG x hx, smul_zero]
  obtain ⟨F, hFS, hwF⟩ := Submodule.mem_span_finite_of_mem_span hspan
  obtain ⟨T, c, hc, hTw, hTF⟩ := key F fun s hs => hP s (hFS hs)
  have hle : Submodule.span ℂ (F : Set M) ≤ LinearMap.ker T :=
    Submodule.span_le.2 fun s hs => LinearMap.mem_ker.2 (hTF s hs)
  have h0 : T w = 0 := LinearMap.mem_ker.1 (hle hwF)
  rw [hTw] at h0
  exact hw0 ((smul_eq_zero.1 h0).resolve_left hc)

theorem exists_re_inner_casimirK_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      RCLike.re (inner ℂ (casimirK ε E x) x) ≤ ((R + √2 * k) ^ 2 - nsq (rhoC ε)) * ‖x‖ ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := exists_weight_bound hU hVf hVK
  refine ⟨R, hR0, fun k x hx => ?_⟩
  refine re_inner_casimirK_le hE (isKUnitary_of_isInfUnitary hU) (finiteDimensional_layer hVf k)
    (layer_kStable hE hVK k) _ (fun w hw hw0 μ hμ => ?_) x hx
  unfold casValK
  have h := weight_layer_le hE hU hVf hVK hR k hw hw0 hμ.1
  have h0 : 0 ≤ nsq (μ + rhoC ε) := nsq_nonneg' _
  have h1 : nsq (μ + rhoC ε) ≤ (R + √2 * k) ^ 2 := by
    rw [← Real.sq_sqrt h0]
    first
      | exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      | exact pow_le_pow_left (Real.sqrt_nonneg _) h 2
      | gcongr
  linarith

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem casimir_apply_eq_casimirK_add (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = casimirK ε E x +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x) := by
  simp only [casimir, casimirK, LinearMap.sum_apply, Module.End.mul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun b _ => ?_) fun _ _ => rfl
  exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩

theorem sum_nc_swap (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f a b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · simp [h]
  · simp [h, Ne.symm h]

theorem re_inner_casimir_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hU : IsInfUnitary ε E) (x : M) :
    RCLike.re (inner ℂ (casimir E x) x) = RCLike.re (inner ℂ (casimirK ε E x) x) -
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [casimir_apply_eq_casimirK_add ε E x, inner_add_left, map_add (f := _), sum_inner, map_sum]
  have key : ∀ a, RCLike.re (inner ℂ (∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x)) x) =
      -∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E b a x‖ ^ 2 := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_inner, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hab : ε a ≠ ε b := (Finset.mem_filter.1 hb).2
    rw [hU a b (E b a x) x, adjSign, if_neg hab, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  simp only [key, Finset.sum_neg_distrib]
  rw [sum_nc_swap ε (fun a b => ‖E a b x‖ ^ 2)]
  ring

theorem re_inner_smul_self (c : ℝ) (x : M) :
    RCLike.re (inner ℂ ((c : ℂ) • x) x) = c * ‖x‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

private theorem casimir_eq_smul_on_layer {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) {V : Submodule ℂ M} {c : ℝ} (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∀ k : ℕ, ∀ x ∈ layer ε E V k, casimir E x = (c : ℂ) • x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    exact hc x hx
  | succ k ih =>
    intro x hx
    have hle : layer ε E V (k + 1) ≤ LinearMap.ker (casimir E - (c : ℂ) • 1) := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun y hy => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, ih y hy]
        simp
      · rw [Submodule.map_le_iff_le_comap]
        intro y hy
        rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply]
        have e := congrArg (fun f => f y) (casimir_comm hE a b)
        simp only [Module.End.mul_apply] at e
        rw [e, ih y hy, map_smul]
        simp
    have h1 := hle hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    simpa using h1

theorem exists_sum_nc_norm_sq_le (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤
        ((R + √2 * k) ^ 2 - nsq (rhoC ε) - c) * ‖x‖ ^ 2 := by
  obtain ⟨R, hR, hK⟩ := exists_re_inner_casimirK_layer_le hE hU hVf hVK
  refine ⟨R, hR, fun k x hx => ?_⟩
  have h1 := re_inner_casimir_eq ε hU x
  rw [casimir_eq_smul_on_layer hE hc k x hx, re_inner_smul_self] at h1
  have h2 := hK k x hx
  nlinarith

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Growth
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem actM_mem_layer_succ (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k) :
    actM E X x ∈ layer ε E V (k + 1) := by
  unfold actM
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)

theorem sqrt_sub_le_add {y d : ℝ} (hy : 0 ≤ y) : √(y ^ 2 - d) ≤ y + √(max 0 (-d)) := by
  have hs := Real.sqrt_nonneg (max 0 (-d))
  have hs2 : √(max 0 (-d)) ^ 2 = max 0 (-d) := Real.sq_sqrt (le_max_left _ _)
  have hm : -d ≤ max 0 (-d) := le_max_right _ _
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith

theorem norm_actM_le {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k) :
    ‖actM E X x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
  set f : Fin n × Fin n → ℝ := fun p => ‖X p.1 p.2‖ with hf
  set g : Fin n × Fin n → ℝ := fun p => if ε p.1 ≠ ε p.2 then ‖E p.1 p.2 x‖ else 0 with hg
  have h1 : ‖actM E X x‖ ≤ ∑ p : Fin n × Fin n, f p * g p := by
    unfold actM
    rw [LinearMap.sum_apply, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [LinearMap.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [LinearMap.smul_apply, norm_smul]
    by_cases hab : ε a = ε b
    · simp [hf, hg, hab, inP_apply_eq_zero hX hab]
    · simp [hf, hg, hab]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n × Fin n)) f g
  have hfs : ∑ p : Fin n × Fin n, f p ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hgs : ∑ p : Fin n × Fin n, g p ^ 2 =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : ε a = ε b <;> simp [hg, hab]
  rw [hfs, hgs] at h2
  set y : ℝ := R + √2 * k with hy
  have hy0 : 0 ≤ y := by positivity
  have h3 : √(∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2) ≤
      (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
    calc _ ≤ √((y ^ 2 - d) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hR k x hx)
      _ ≤ √(max 0 (y ^ 2 - d)) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (le_max_left _ _),
            Real.sqrt_sq (norm_nonneg x)]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      _ ≤ (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          have := sqrt_sub_le_add (d := d) hy0
          rcases le_total 0 (y ^ 2 - d) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, Real.sqrt_zero]; positivity
  calc ‖actM E X x‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * ((R + √(max 0 (-d)) + √2 * k) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem actM_pow_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) : ((actM E X) ^ m) x ∈ layer ε E V (k + m) := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact actM_mem_layer_succ hE hV hX ih

theorem norm_actM_pow_le (hE : IsGlRep E) (hV : IsKStableSub ε E V) {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) :
    ‖((actM E X) ^ m) x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
      (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := norm_actM_le hR0 hR hX (k + m) (actM_pow_mem_layer hE hV hX hx m)
    have hc : 0 ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) := by
      positivity
    calc _ ≤ _ := h
      _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) *
          (√(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
            (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = _ := by
          rw [Finset.prod_range_succ, pow_succ]
          push_cast
          ring

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Series
noncomputable section

open Finset Filter

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem summable_prod_mul_pow_div_factorial {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hrB : r * B < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ) := by
  set q : ℝ := (1 + r * B) / 2 with hq_def
  have hq1 : q < 1 := by rw [hq_def]; linarith
  have hd : 0 < q - r * B := by rw [hq_def]; linarith
  have hq0 : 0 ≤ q := by rw [hq_def]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (((A + B * k) * r) / (q - r * B))
  have hterm : ∀ i : ℕ, 0 ≤ A + B * ((k : ℝ) + i) := fun i =>
    add_nonneg hA (mul_nonneg hB (by positivity))
  have hf : ∀ m : ℕ, 0 ≤ (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ) :=
    fun m => div_nonneg (mul_nonneg (prod_nonneg fun i _ => hterm i) (pow_nonneg hr _)) (by positivity)
  refine summable_of_ratio_norm_eventually_le hq1 ?_
  filter_upwards [eventually_ge_atTop N] with m hm
  rw [Real.norm_of_nonneg (hf _), Real.norm_of_nonneg (hf _)]
  have hx : (A + B * ((k : ℝ) + m)) * r ≤ q * ((m : ℝ) + 1) := by
    have h0 := (div_le_iff₀ hd).1 hN
    have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : (A + B * k) * r ≤ (q - r * B) * m := by nlinarith
    nlinarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  rw [prod_range_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have key : (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * (A + B * ((k : ℝ) + m)) * (r ^ m * r) /
      (((m : ℝ) + 1) * (m.factorial : ℝ)) =
      ((∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ)) *
        ((A + B * ((k : ℝ) + m)) * r / ((m : ℝ) + 1)) := by
    field_simp
  rw [key, mul_comm q]
  apply mul_le_mul_of_nonneg_left _ (hf m)
  rw [div_le_iff₀ hm1]
  exact hx

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem exists_orbit_bound (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) :
    ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) ∧ (∀ m, 0 ≤ a m) ∧
      ∀ r : ℝ, 0 ≤ r → r * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1 →
        Summable fun m : ℕ => a m * r ^ m / (m.factorial : ℝ) := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨R, hR0, hR⟩ := exists_sum_nc_norm_sq_le ε hE hU hVf hVK hc
  set d : ℝ := nsq (rhoC ε) + c
  have hR' : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2 := by
    intro k x hx
    have := hR k x hx
    simpa only [d, sub_sub] using this
  rw [genSub_eq_iSup_layer hE hVK, Submodule.mem_iSup_of_directed _ (show Monotone (layer ε E V) from fun _ _ h => layer_mono h).directed_le] at hv
  obtain ⟨k, hk⟩ := hv
  set S : ℝ := √(∑ a, ∑ b, ‖X a b‖ ^ 2)
  set A : ℝ := R + √(max 0 (-d))
  have hA : 0 ≤ A := add_nonneg hR0 (Real.sqrt_nonneg _)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨fun m => S ^ m * (∏ l ∈ range m, (A + √2 * ((k : ℝ) + l))) * ‖v‖, ?_, ?_, ?_⟩
  · intro m
    have := norm_actM_pow_le hE hVK hR0 hR' hX k hk m
    simpa only [Submodule.coe_norm] using this
  · intro m
    refine mul_nonneg (mul_nonneg (pow_nonneg hS _) ?_) (norm_nonneg _)
    exact prod_nonneg fun l _ => add_nonneg hA (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
  · intro r hr hrS
    have h1 := summable_prod_mul_pow_div_factorial hA (Real.sqrt_nonneg 2) (mul_nonneg hr hS)
      (by nlinarith) k
    have h2 := h1.mul_left ‖v‖
    refine h2.congr fun m => ?_
    rw [mul_pow]
    ring

theorem orbit_hasSum_taylor (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) (t₀ t : ℝ)
    (ht : |t - t₀| * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1) :
    HasSum (fun m : ℕ => (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
        σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by
  obtain ⟨a, ha, -, hs⟩ := exists_orbit_bound hσ hD hVf hVK hc hX hv
  exact hasSum_orbit_of_bound hσ hD hX.1 v a ha t₀ t (hs _ (abs_nonneg _) ht)

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem closure_E_mem_genSub {V : Submodule ℂ D} (a b : Fin n) {v : D} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem closure_actM_pow_mem_genSub {V : Submodule ℂ D} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    {v : D} (hv : v ∈ genSub E V) : ((actM E X) ^ m) v ∈ genSub E V := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, actM, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (closure_E_mem_genSub a b ih)

theorem closure_mapsTo_of_genSub {V : Submodule ℂ D} (T : H →L[ℂ] H)
    (hT : ∀ v : D, v ∈ genSub E V → T (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure)
    {x : H} (hx : x ∈ ((genSub E V).map D.subtype).topologicalClosure) :
    T x ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hsub : (((genSub E V).map D.subtype : Submodule ℂ H) : Set H) ⊆
      T ⁻¹' ((((genSub E V).map D.subtype).topologicalClosure : Submodule ℂ H) : Set H) := by
    rintro y ⟨v, hv, rfl⟩
    exact hT v hv
  have hcl : IsClosed (T ⁻¹' ((((genSub E V).map D.subtype).topologicalClosure :
      Submodule ℂ H) : Set H)) :=
    ((genSub E V).map D.subtype).isClosed_topologicalClosure.preimage T.continuous
  have hx' : x ∈ closure (((genSub E V).map D.subtype : Submodule ℂ H) : Set H) := by
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  exact closure_minimal hsub hcl hx'

theorem closure_inUJ_of_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k.conjTranspose * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  show k.conjTranspose * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exp_apply_mem_topologicalClosure (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp X) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hSc : IsClosed ((((genSub E V).map D.subtype).topologicalClosure : Submodule ℂ H) : Set H) :=
    ((genSub E V).map D.subtype).isClosed_topologicalClosure
  have hsub : ∀ w : D, w ∈ genSub E V →
      (w : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := fun w hw =>
    ((genSub E V).map D.subtype).le_topologicalClosure ⟨w, hw, rfl⟩
  have hc0 : (0 : ℝ) ≤ √2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2))
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt hc0 hN
  have hstep : ∀ j : ℕ, ∀ w : D, w ∈ genSub E V →
      σ (NormedSpace.exp ((((j : ℝ) / N : ℝ) : ℂ) • X)) (w : H) ∈
        ((genSub E V).map D.subtype).topologicalClosure := by
    intro j
    induction j with
    | zero =>
      intro w hw
      simp only [Nat.cast_zero, zero_div, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
      rw [hσ.1.1, ContinuousLinearMap.one_apply]
      exact hsub w hw
    | succ j ih =>
      intro w hw
      have hdiff : (((j + 1 : ℕ) : ℝ) / N) - ((j : ℝ) / N) = 1 / N := by
        rw [Nat.cast_succ, add_div, add_sub_cancel_left]
      have ht : |(((j + 1 : ℕ) : ℝ) / N) - ((j : ℝ) / N)| * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1 := by
        rw [hdiff, abs_of_pos (div_pos one_pos hN0), one_div, inv_mul_lt_iff₀ hN0, mul_one]
        exact hN
      have hs := orbit_hasSum_taylor hσ hD hVf hVK hc hX hw ((j : ℝ) / N) (((j + 1 : ℕ) : ℝ) / N) ht
      refine hSc.mem_of_tendsto hs.tendsto_sum_nat (Filter.Eventually.of_forall fun M => ?_)
      refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
      exact ih _ (closure_actM_pow_mem_genSub X m hw)
  have h := hstep N v hv
  rwa [div_self hN0.ne', Complex.ofReal_one, one_smul] at h

theorem closure_genSub_stable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∀ g ∈ UJset ε, ∀ x ∈ ((genSub E V).map D.subtype).topologicalClosure,
      σ g x ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  intro g hg x hx
  obtain ⟨k, hk, Y, hY, hgk⟩ := polar_UJ hg
  have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
  have h1 : k.conjTranspose * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk.1
  have h2 : k * k.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk.1
  have hEq : k.conjTranspose * g = NormedSpace.exp Y := by
    rw [hgk, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hkg : k.conjTranspose * g ∈ UJset ε := by
    have hg' : g.conjTranspose * Jm ε * g = Jm ε := hg
    show (k.conjTranspose * g).conjTranspose * Jm ε * (k.conjTranspose * g) = Jm ε
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc g.conjTranspose * k * Jm ε * (k.conjTranspose * g)
        = g.conjTranspose * (k * Jm ε) * k.conjTranspose * g := by simp only [Matrix.mul_assoc]
      _ = g.conjTranspose * (Jm ε * k) * k.conjTranspose * g := by rw [hk.2]
      _ = g.conjTranspose * Jm ε * (k * k.conjTranspose) * g := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [h2, Matrix.mul_one, hg']
  have hσg : σ g = (σ k).comp (σ (k.conjTranspose * g)) := by
    have h3 := hσ.1.2 k hkU _ hkg
    rwa [← Matrix.mul_assoc, h2, Matrix.one_mul] at h3
  have hs1 : σ (NormedSpace.exp Y) x ∈ ((genSub E V).map D.subtype).topologicalClosure :=
    closure_mapsTo_of_genSub _ (fun v hv => exp_apply_mem_topologicalClosure hσ hD hVf hVK hc hY hv) hx
  obtain ⟨Z, hZ, hZe⟩ := exists_exp_eq_of_mem_Kset hk
  have hs2 : ∀ y ∈ ((genSub E V).map D.subtype).topologicalClosure,
      σ k y ∈ ((genSub E V).map D.subtype).topologicalClosure := fun y hy =>
    closure_mapsTo_of_genSub _ (fun v hv => by
      rw [← hZe]
      exact exp_inK_apply_mem_closure hσ hD hVf hVK hZ hv) hy
  rw [hσg, ContinuousLinearMap.comp_apply, hEq]
  exact hs2 _ hs1

end Rep

end ReciprocityTheory.ChartRestriction.DS

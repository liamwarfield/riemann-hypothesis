module

public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

noncomputable section

universe u

def polyAt (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n) : ℂ :=
  MvPolynomial.eval (fun i => w i) Δ

def VanishOrder {M : Type u} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (x : M)
    (N : ℕ) : Prop :=
  f =O[𝓝 x] fun y => ‖z y - z x‖ ^ N


open Classical in
def fiberVals {M : Type u} (n : ℕ) (z : M → V n) (u : M → ℂ) (w : V n) : Multiset ℂ := by
  classical
  exact if h : (z ⁻¹' {w}).Finite then h.toFinset.val.map u else 0

def fiberSymm {M : Type u} (n : ℕ) (z : M → V n) (u : M → ℂ) (k : ℕ) (w : V n) : ℂ :=
  (fiberVals n z u w).esymm k

def lineVanishStatement : Prop :=
  ∀ (g : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (K N : ℕ), B.Finite → K < N →
    DifferentiableOn ℂ g Bᶜ → (∀ t ∉ B, ‖g t‖ ≤ A * (1 + ‖t‖) ^ K) →
    (g =O[𝓝 0] fun t => t ^ N) → ∀ t ∉ B, g t = 0

def esymmZeroStatement : Prop :=
  ∀ s : Multiset ℂ, (∀ k : ℕ, 1 ≤ k → s.esymm k = 0) → ∀ a ∈ s, a = 0

def sheetsStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)) (u : M → ℂ),
    IsCoveringMapOn z U → ∀ w ∈ U, (z ⁻¹' {w}).Finite →
    ∃ (W : Set (V n)) (d : ℕ) (s : Fin d → V n → M), IsOpen W ∧ w ∈ W ∧
      (∀ i, ContinuousOn (s i) W) ∧ (∀ i, ∀ v ∈ W, z (s i v) = v) ∧
      ∀ v ∈ W, fiberVals n z u v = (Finset.univ : Finset (Fin d)).val.map (fun i => u (s i v))

def symmDiffStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)) (u : M → ℂ),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ w ∈ U, (z ⁻¹' {w}).Finite) →
    Holo n z u → ∀ (k : ℕ), ∀ w ∈ U, DifferentiableAt ℂ (fiberSymm n z u k) w

def symmVanishStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)) (u : M → ℂ)
    (w₀ : V n) (N : ℕ),
    IsCoveringMapOn z U → w₀ ∈ U → (z ⁻¹' {w₀}).Finite →
    (∀ x, z x = w₀ → VanishOrder n z u x N) →
    ∀ k : ℕ, fiberSymm n z u k =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (k * N)

def symmGrowthStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) (z : M → V n) (u : M → ℂ) (R : V n → ℝ) (δ : ℕ),
    (∀ x, ‖u x‖ ≤ R (z x)) → (∀ w, (z ⁻¹' {w}).encard ≤ δ) →
    ∀ (k : ℕ) (w : V n), ‖fiberSymm n z u k w‖ ≤ 2 ^ δ * (max (R w) 0) ^ k

def lineFiniteStatement : Prop :=
  ∀ (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n), polyAt n Δ 0 ≠ 0 →
    {t : ℂ | polyAt n Δ (t • w) = 0}.Finite

def holoSectionStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ),
    IsLocalHomeomorph z → Holo n z f → ∀ (s : V n → M) (w : V n),
      ContinuousAt s w → (∀ᶠ v in 𝓝 w, z (s v) = v) → DifferentiableAt ℂ (f ∘ s) w

def normVanishStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (Δ : MvPolynomial (Fin n) ℂ)
    (δ m : ℕ) (C : ℝ) (u : M → ℂ),
    polyAt n Δ 0 ≠ 0 →
    IsCoveringMapOn z {w | polyAt n Δ w ≠ 0} →
    (∀ x, polyAt n Δ (z x) ≠ 0) →
    (∀ w, (z ⁻¹' {w}).encard ≤ δ) →
    Holo n z u →
    (∀ x, ‖u x‖ ≤ C * (1 + ‖z x‖ ^ 2) ^ ((m : ℝ) / 2)) →
    (∀ x, z x = 0 → VanishOrder n z u x (m + 1)) →
    ∀ x, u x = 0

end

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfHoloSection
section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.Sheets
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem sheets : sheetsStatement.{u} := by
  intro n M _ z U u hcov w hw hfin
  obtain ⟨_, W, hwW, hW, _, H, hH⟩ := hcov w hw
  have : Finite (z ⁻¹' {w}) := hfin.to_subtype
  let e : Fin (Nat.card (z ⁻¹' {w})) ≃ (z ⁻¹' {w}) := (Finite.equivFin _).symm
  classical
  let s : Fin (Nat.card (z ⁻¹' {w})) → V n → M :=
    fun i v => if hv : v ∈ W then (H.symm (⟨v, hv⟩, e i)).1 else (e i).1
  have hs : ∀ i v (hv : v ∈ W), s i v = (H.symm (⟨v, hv⟩, e i)).1 := fun i v hv => dif_pos hv
  have hzs : ∀ i, ∀ v ∈ W, z (s i v) = v := by
    intro i v hv
    rw [hs i v hv]
    have := hH (H.symm (⟨v, hv⟩, e i))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hinj : ∀ v (hv : v ∈ W) i j, s i v = s j v → i = j := by
    intro v hv i j hij
    rw [hs i v hv, hs j v hv] at hij
    have h2 := congrArg (fun y => (H y).2)
      (Subtype.ext hij : H.symm (⟨v, hv⟩, e i) = H.symm (⟨v, hv⟩, e j))
    simp only [Homeomorph.apply_symm_apply] at h2
    exact e.injective h2
  have hsurj : ∀ v (hv : v ∈ W) (y : M), z y = v → ∃ i, s i v = y := by
    intro v hv y hy
    have hyW : y ∈ z ⁻¹' W := by
      show z y ∈ W
      rw [hy]; exact hv
    refine ⟨e.symm (H ⟨y, hyW⟩).2, ?_⟩
    rw [hs _ v hv]
    simp only [Equiv.apply_symm_apply]
    have h1 : (H ⟨y, hyW⟩).1 = ⟨v, hv⟩ := Subtype.ext (by rw [hH]; exact hy)
    have h3 : H.symm (⟨v, hv⟩, (H ⟨y, hyW⟩).2) = ⟨y, hyW⟩ := by
      rw [← h1]; simp
    rw [h3]
  refine ⟨W, Nat.card (z ⁻¹' {w}), s, hW, hwW, ?_, hzs, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have : W.domRestrict (s i) = fun v : W => (H.symm (v, e i)).1 := by
      funext v
      exact hs i v.1 v.2
    rw [this]
    exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
  · intro v hv
    have hfv : (z ⁻¹' {v}).Finite := by
      refine (Set.finite_range fun i => s i v).subset ?_
      intro y hy
      obtain ⟨i, hi⟩ := hsurj v hv y hy
      exact ⟨i, hi⟩
    unfold fiberVals
    rw [dif_pos hfv]
    have hF : hfv.toFinset = Finset.univ.map ⟨fun i => s i v, fun i j h => hinj v hv i j h⟩ := by
      ext y
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
      constructor
      · intro hy; exact hsurj v hv y hy
      · rintro ⟨i, rfl⟩; exact hzs i v hv
    rw [hF, Finset.map_val, Multiset.map_map]
    rfl

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmVanish
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmVanish : symmVanishStatement.{u} := by
  intro n M _ z U u w₀ N hcov hw₀ hfin hvan k
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w₀ hw₀ hfin
  have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hwW
  have hi : ∀ i, (fun v => u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ N := by
    intro i
    have hx : z (s i w₀) = w₀ := hzs i w₀ hwW
    have h1 := IsBigO.comp_tendsto (hvan (s i w₀) hx) ((hcont i).continuousAt hWn)
    refine h1.congr' (Eventually.of_forall fun v => rfl) ?_
    filter_upwards [hWn] with v hv
    simp only [Function.comp_apply, hzs i v hv, hx]
  have hprod : ∀ t : Finset (Fin d),
      (fun v => ∏ i ∈ t, u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (t.card * N) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 w₀))
    | insert a t ha ih =>
      have hc : (insert a t).card = t.card + 1 := by
        exact Finset.card_insert_of_notMem ha
      simp only [Finset.prod_insert ha]
      rw [hc]
      exact ((hi a).mul ih).congr' (Eventually.of_forall fun v => rfl)
        (Eventually.of_forall fun v => by
          show ‖v - w₀‖ ^ N * ‖v - w₀‖ ^ (t.card * N) = ‖v - w₀‖ ^ ((t.card + 1) * N)
          rw [← pow_add]; congr 1; ring)
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w₀] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine IsBigO.congr' ?_ heq (Eventually.of_forall fun _ => rfl)
  refine IsBigO.fun_sum fun t ht => ?_
  have := hprod t
  rwa [(Finset.mem_powersetCard.mp ht).2] at this

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmDiff
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmDiff_of_holoSection (hsec : holoSectionStatement.{u}) : symmDiffStatement.{u} := by
  intro n M _ z U u hcov hU hfinU hholo k w hw
  have hloc : IsLocalHomeomorph z := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    have := hcov.isLocalHomeomorphOn
    rwa [Set.preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hU x)] at this
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w hw (hfinU w hw)
  have hWn : W ∈ 𝓝 w := hW.mem_nhds hwW
  have hdiff : ∀ i, DifferentiableAt ℂ (fun v => u (s i v)) w := fun i =>
    hsec n M z u hloc hholo (s i) w ((hcont i).continuousAt hWn)
      (Filter.eventually_of_mem hWn (hzs i))
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  have hprod : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, u (s i v)) w := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hdiff a).mul ih
  exact DifferentiableAt.fun_sum fun t _ => hprod t

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfParts
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem growth_on_line (n m : ℕ) (C : ℝ) (t : ℂ) (w : V n) :
    max (C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)) 0 ≤
      max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by
  have hr : 0 ≤ ‖t • w‖ := norm_nonneg _
  have hP : (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) = (Real.sqrt (1 + ‖t • w‖ ^ 2)) ^ m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  have hs : Real.sqrt (1 + ‖t • w‖ ^ 2) ≤ (1 + ‖w‖) * (1 + ‖t‖) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [norm_smul]
    have ht := norm_nonneg t
    have hw := norm_nonneg w
    nlinarith [mul_nonneg ht hw, mul_nonneg (mul_nonneg ht hw) ht, mul_nonneg (mul_nonneg ht hw) hw]
  have hQ : (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) ≤ ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by
    rw [hP]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs m
  have hQ0 : 0 ≤ (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) := by positivity
  refine max_le ?_ (by positivity)
  calc C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)
      ≤ max C 0 * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0
    _ ≤ max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m :=
        mul_le_mul_of_nonneg_left hQ (le_max_right _ _)

theorem normVanish_of_parts (h1 : lineVanishStatement) (h2 : esymmZeroStatement)
    (h4 : symmDiffStatement.{u}) (h5 : symmVanishStatement.{u})
    (h6 : symmGrowthStatement.{u}) (h7 : lineFiniteStatement) :
    normVanishStatement.{u} := by
  intro n M _ z Δ δ m C u hΔ0 hcov hrange hdeg hholo hgrowth hvan x
  have hfin : ∀ w, (z ⁻¹' {w}).Finite := fun w => Set.finite_of_encard_le_coe (hdeg w)
  have key : ∀ k : ℕ, 1 ≤ k → fiberSymm n z u k (z x) = 0 := by
    intro k hk
    have hB : {t : ℂ | polyAt n Δ (t • z x) = 0}.Finite := h7 n Δ (z x) hΔ0
    have h1B : (1 : ℂ) ∉ {t : ℂ | polyAt n Δ (t • z x) = 0} := by
      simpa using hrange x
    have hlt : k * m < k * (m + 1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self m) hk
    have := h1 (fun t => fiberSymm n z u k (t • z x)) {t : ℂ | polyAt n Δ (t • z x) = 0}
      (2 ^ δ * (max C 0) ^ k * (1 + ‖z x‖) ^ (k * m)) (k * m) (k * (m + 1)) hB hlt ?_ ?_ ?_ 1 h1B
    · simpa using this
    ·
      intro t ht
      have hU : t • z x ∈ {w | polyAt n Δ w ≠ 0} := ht
      exact ((h4 n M z {w | polyAt n Δ w ≠ 0} u hcov (fun y => hrange y) (fun w _ => hfin w)
        hholo k (t • z x) hU).comp t (differentiableAt_id.smul_const (z x))).differentiableWithinAt
    ·
      intro t _
      have hg := h6 n M z u (fun v => C * (1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)) δ hgrowth hdeg k (t • z x)
      refine hg.trans ?_
      have hl := growth_on_line n m C t (z x)
      have hl' : (max (C * (1 + ‖t • z x‖ ^ 2) ^ ((m : ℝ) / 2)) 0) ^ k ≤
          (max C 0 * ((1 + ‖z x‖) * (1 + ‖t‖)) ^ m) ^ k :=
        pow_le_pow_left₀ (le_max_right _ _) hl k
      calc 2 ^ δ * (max (C * (1 + ‖t • z x‖ ^ 2) ^ ((m : ℝ) / 2)) 0) ^ k
          ≤ 2 ^ δ * (max C 0 * ((1 + ‖z x‖) * (1 + ‖t‖)) ^ m) ^ k :=
            mul_le_mul_of_nonneg_left hl' (by positivity)
        _ = 2 ^ δ * (max C 0) ^ k * (1 + ‖z x‖) ^ (k * m) * (1 + ‖t‖) ^ (k * m) := by
            rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m k]; ring
    ·
      have hv := h5 n M z {w | polyAt n Δ w ≠ 0} u 0 (m + 1) hcov hΔ0 (hfin 0) hvan k
      have ht : Tendsto (fun t : ℂ => t • z x) (𝓝 0) (𝓝 0) := by
        exact ((continuous_id.smul continuous_const).tendsto' (0 : ℂ) (0 : V n) (by simp) :
          Tendsto (fun t : ℂ => t • z x) (𝓝 0) (𝓝 0))
      refine (hv.comp_tendsto ht).trans ?_
      refine IsBigO.of_bound (‖z x‖ ^ (k * (m + 1))) (Eventually.of_forall fun t => ?_)
      simp [norm_smul, mul_pow, norm_pow, mul_comm]
  have hmem : u x ∈ fiberVals n z u (z x) := by
    unfold fiberVals
    rw [dite_eq_left (hfin (z x))]
    exact Multiset.mem_map.mpr ⟨x, by simp, rfl⟩
  exact h2 _ key (u x) hmem

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.LineFinite
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem eval_line (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n) (t : ℂ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ).eval t =
      polyAt n Δ (t • w) := by
  unfold polyAt
  induction Δ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.aeval_X,
      MvPolynomial.eval_X]
    congr 1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp
    ring

theorem lineFinite : lineFiniteStatement := by
  intro n Δ w h0
  have hne : MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ ≠ 0 := by
    intro hz
    apply h0
    have := eval_line n Δ w 0
    rw [hz] at this
    simpa using this.symm
  refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
  intro t ht
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_line]
  exact ht

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.EsymmZero
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem esymmZero : esymmZeroStatement := by
  intro s hs a ha
  have h := Multiset.prod_X_add_C_eq_sum_esymm s
  have hR : ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j)
      = Polynomial.X ^ s.card := by
    rw [Finset.sum_eq_single 0]
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro j _ hj
      rw [hs j (Nat.one_le_iff_ne_zero.mpr hj)]
      simp
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  rw [hR] at h
  have h2 := congrArg (Polynomial.eval (-a)) h
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_pow, Polynomial.eval_X] at h2
  have h3 : (Multiset.map (Polynomial.eval (-a))
      (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s)).prod = 0 := by
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨a, ha, by simp⟩
  rw [h3] at h2
  exact neg_eq_zero.mp (pow_eq_zero_iff'.mp h2.symm).1

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.Section
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem holoSection : holoSectionStatement.{u} := by
  intro n M _ z f hz hf s w hs hzs
  obtain ⟨e, hxe, rfl⟩ := hz (s w)
  have hchart : IsChart n e e := fun _ _ => rfl
  have hw : e (s w) = w := hzs.self_of_nhds
  have htarget : e.target ∈ 𝓝 w := by
    rw [← hw]
    exact e.open_target.mem_nhds (e.map_source hxe)
  have hsrc : ∀ᶠ v in 𝓝 w, s v ∈ e.source := hs (e.open_source.mem_nhds hxe)
  have heq : f ∘ e.symm =ᶠ[𝓝 w] f ∘ s := by
    filter_upwards [hsrc, hzs] with v h1 h2
    simp only [Function.comp_apply]
    rw [show e.symm v = s v by rw [← e.left_inv h1, h2]]
  exact ((hf e hchart).differentiableAt htarget).congr_of_eventuallyEq heq.symm

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmGrowth
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmGrowth : symmGrowthStatement.{u} := by
  intro n M z u R δ hR hdeg k w
  have hfin : (z ⁻¹' {w}).Finite := Set.finite_of_encard_le_coe (hdeg w)
  have hcard : hfin.toFinset.card ≤ δ := by
    have := hdeg w
    rw [← hfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  unfold fiberSymm fiberVals
  rw [dite_eq_left hfin, Finset.esymm_map_val]
  have hB : 0 ≤ max (R w) 0 := le_max_right _ _
  have hu : ∀ y ∈ hfin.toFinset, ‖u y‖ ≤ max (R w) 0 := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    have hy' : z y = w := hy
    calc ‖u y‖ ≤ R (z y) := hR y
      _ = R w := by rw [hy']
      _ ≤ max (R w) 0 := le_max_left _ _
  calc ‖∑ t ∈ hfin.toFinset.powersetCard k, t.prod u‖
      ≤ ∑ t ∈ hfin.toFinset.powersetCard k, ‖t.prod u‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ hfin.toFinset.powersetCard k, (max (R w) 0) ^ k := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_powersetCard] at ht
        rw [norm_prod]
        calc ∏ y ∈ t, ‖u y‖ ≤ ∏ _y ∈ t, max (R w) 0 :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun y hy => hu y (ht.1 hy))
          _ = (max (R w) 0) ^ k := by rw [Finset.prod_const, ht.2]
    _ = ((hfin.toFinset.powersetCard k).card : ℝ) * (max (R w) 0) ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ δ * (max (R w) 0) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB k)
        rw [Finset.card_powersetCard]
        have h1 := Nat.choose_le_two_pow hfin.toFinset.card k
        have h2 : 2 ^ hfin.toFinset.card ≤ 2 ^ δ := Nat.pow_le_pow_right (by norm_num) hcard
        exact_mod_cast h1.trans h2

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.SymmetricSections.RemovableFinset
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem removable_finset (S : Finset ℂ) : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (↑S)ᶜ →
    (∀ c ∈ S, ∃ M : ℝ, ∀ᶠ t in 𝓝[≠] c, ‖f t‖ ≤ M) →
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ t ∉ S, F t = f t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro f hd _
    refine ⟨f, ?_, fun _ _ => rfl⟩
    exact differentiableOn_univ.mp (by simpa using hd)
  | insert c S hc ih =>
    intro f hd hb
    obtain ⟨M, hM⟩ := hb c (Finset.mem_insert_self c S)
    have hSc : ∀ᶠ t in 𝓝 c, t ∉ (S : Set ℂ) :=
      (S.finite_toSet.isClosed.isOpen_compl).mem_nhds (by simpa using hc)
    rw [eventually_nhdsWithin_iff] at hM
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hM.and hSc)
    set g := Function.update f c (limUnder (𝓝[≠] c) f) with hg
    have hsub : Metric.ball c ε \ {c} ⊆ (↑(insert c S) : Set ℂ)ᶜ := by
      intro t ht
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
      exact ⟨ht.2, (hball ht.1).2⟩
    have hgc : DifferentiableOn ℂ g (Metric.ball c ε) := by
      apply Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hε)
        (hd.mono hsub)
      refine ⟨M, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact (hball ht.1).1 ht.2
    have hgS : DifferentiableOn ℂ g (↑S)ᶜ := by
      intro t ht
      by_cases htc : t = c
      · subst htc
        exact (hgc.differentiableAt (Metric.ball_mem_nhds _ hε)).differentiableWithinAt
      · have hmem : t ∈ (↑(insert c S) : Set ℂ)ᶜ := by
          simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
          exact ⟨htc, ht⟩
        have hft : DifferentiableAt ℂ f t :=
          hd.differentiableAt ((Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds hmem)
        have heq : g =ᶠ[𝓝 t] f := by
          filter_upwards [isOpen_compl_singleton.mem_nhds htc] with y hy
          exact Function.update_of_ne hy _ _
        exact (hft.congr_of_eventuallyEq heq).differentiableWithinAt
    have hgb : ∀ c' ∈ S, ∃ M : ℝ, ∀ᶠ t in 𝓝[≠] c', ‖g t‖ ≤ M := by
      intro c' hc'
      obtain ⟨M', hM'⟩ := hb c' (Finset.mem_insert_of_mem hc')
      refine ⟨M', ?_⟩
      have hne : c' ≠ c := fun h => hc (h ▸ hc')
      have hnc : ∀ᶠ t in 𝓝[≠] c', t ≠ c :=
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne)
      filter_upwards [hM', hnc] with t h1 h2
      rwa [hg, Function.update_of_ne h2]
    obtain ⟨F, hF, hFg⟩ := ih g hgS hgb
    refine ⟨F, hF, fun t ht => ?_⟩
    have htc : t ≠ c := fun h => ht (h ▸ Finset.mem_insert_self c S)
    have htS : t ∉ S := fun h => ht (Finset.mem_insert_of_mem h)
    rw [hFg t htS, hg, Function.update_of_ne htc]

theorem lineVanish : lineVanishStatement := by
  intro g B A K N hB hKN hd hgr h0 t ht
  classical
  obtain ⟨c0, hc0⟩ := h0.bound
  have hg0 : g 0 = 0 := by
    have h1 := hc0.self_of_nhds
    rw [zero_pow (by omega : N ≠ 0), norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  by_cases ht0 : t = 0
  · rw [ht0]; exact hg0
  set S : Finset ℂ := insert 0 hB.toFinset with hS
  have hBc : IsOpen Bᶜ := hB.isClosed.isOpen_compl
  have hmemS : ∀ x, x ∉ S ↔ x ≠ 0 ∧ x ∉ B := by intro x; simp [hS]
  set h : ℂ → ℂ := fun x => g x / x ^ N with hh
  have hdh : DifferentiableOn ℂ h (↑S)ᶜ := by
    intro x hx
    have hx' := (hmemS x).mp hx
    have hgx : DifferentiableAt ℂ g x := hd.differentiableAt (hBc.mem_nhds hx'.2)
    exact (hgx.div (differentiableAt_pow N) (pow_ne_zero N hx'.1)).differentiableWithinAt
  have hbd : ∀ c ∈ S, ∃ M : ℝ, ∀ᶠ x in 𝓝[≠] c, ‖h x‖ ≤ M := by
    intro c hc
    by_cases hc0' : c = 0
    · subst hc0'
      refine ⟨c0, ?_⟩
      filter_upwards [nhdsWithin_le_nhds hc0, self_mem_nhdsWithin] with x hx hx0
      have hxn : 0 < ‖x‖ ^ N := pow_pos (norm_pos_iff.mpr hx0) N
      rw [hh]
      simp only [norm_div, norm_pow] at hx ⊢
      rw [div_le_iff₀ hxn]
      exact hx
    · have hcont : ContinuousAt (fun x : ℂ => |A| * (1 + ‖x‖) ^ K / ‖x‖ ^ N) c := by
        apply ContinuousAt.div₀ (by fun_prop) (by fun_prop)
        exact pow_ne_zero N (norm_ne_zero_iff.mpr hc0')
      refine ⟨|A| * (1 + ‖c‖) ^ K / ‖c‖ ^ N + 1, ?_⟩
      have h1 : ∀ᶠ x in 𝓝 c, |A| * (1 + ‖x‖) ^ K / ‖x‖ ^ N < |A| * (1 + ‖c‖) ^ K / ‖c‖ ^ N + 1 :=
        hcont.eventually (gt_mem_nhds (lt_add_one _))
      have h2 : ∀ᶠ x in 𝓝 c, x ≠ 0 := isOpen_compl_singleton.mem_nhds hc0'
      have h3 : ∀ᶠ x in 𝓝[≠] c, x ∉ B := by
        have h4 : ∀ᶠ x in 𝓝 c, x ∉ B \ {c} :=
          (hB.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
        filter_upwards [nhdsWithin_le_nhds h4, self_mem_nhdsWithin] with x hx hxc
        intro hxB
        exact hx ⟨hxB, hxc⟩
      filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, h3] with x hx1 hx2 hx3
      have hxn : 0 < ‖x‖ ^ N := pow_pos (norm_pos_iff.mpr hx2) N
      rw [hh]
      simp only [norm_div, norm_pow]
      refine le_trans ?_ hx1.le
      rw [div_le_div_iff_of_pos_right hxn]
      exact (hgr x hx3).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
  obtain ⟨F, hF, hFh⟩ := removable_finset S h hdh hbd
  set R : ℝ := 1 + ∑ b ∈ S, ‖b‖ with hR
  have hR1 : 1 ≤ R := by
    have := Finset.sum_nonneg (fun b (_ : b ∈ S) => norm_nonneg b)
    linarith
  have hfar : ∀ x : ℂ, R ≤ ‖x‖ → x ∉ S := by
    intro x hx hxS
    have := Finset.single_le_sum (fun b (_ : b ∈ S) => norm_nonneg b) hxS
    linarith
  have hlim : Tendsto F (cocompact ℂ) (𝓝 0) := by
    have hev : ∀ᶠ x in cocompact ℂ, R ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)
    have hlim0 : Tendsto (fun x : ℂ => |A| * 2 ^ K / ‖x‖) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
    refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [hev] with x hx
    have hxS := hfar x hx
    have hx1 : 1 ≤ ‖x‖ := hR1.trans hx
    have hx' := (hmemS x).mp hxS
    have hxpos : 0 < ‖x‖ := by linarith
    rw [hFh x hxS, hh]
    simp only [norm_div, norm_pow]
    rw [div_le_div_iff₀ (pow_pos hxpos N) hxpos]
    have hg1 : ‖g x‖ ≤ |A| * (2 * ‖x‖) ^ K := by
      refine (hgr x hx'.2).trans ?_
      calc A * (1 + ‖x‖) ^ K ≤ |A| * (1 + ‖x‖) ^ K :=
            mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 * ‖x‖) ^ K :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) K)
              (abs_nonneg A)
    have hpow : ‖x‖ ^ K * ‖x‖ ≤ ‖x‖ ^ N := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hx1 hKN
    calc ‖g x‖ * ‖x‖ ≤ |A| * (2 * ‖x‖) ^ K * ‖x‖ := mul_le_mul_of_nonneg_right hg1 hxpos.le
      _ = |A| * 2 ^ K * (‖x‖ ^ K * ‖x‖) := by rw [mul_pow]; ring
      _ ≤ |A| * 2 ^ K * ‖x‖ ^ N := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hF0 : ∀ x, F x = 0 := fun x => hF.apply_eq_of_tendsto_cocompact x hlim
  have htS : t ∉ S := (hmemS t).mpr ⟨ht0, ht⟩
  have h2 : g t / t ^ N = 0 := by
    show h t = 0
    rw [← hFh t htS, hF0 t]
  exact (div_eq_zero_iff.mp h2).resolve_right (pow_ne_zero N ht0)

end ReciprocityTheory.L2DbarEstimates.Norm
end

namespace ReciprocityTheory.L2DbarEstimates.Norm

universe u

theorem normVanish_of_holoSection (hsec : holoSectionStatement.{u}) : normVanishStatement.{u} :=
  normVanish_of_parts lineVanish esymmZero (symmDiff_of_holoSection hsec) symmVanish symmGrowth
    lineFinite

theorem normVanish : normVanishStatement.{u} := normVanish_of_holoSection holoSection

end ReciprocityTheory.L2DbarEstimates.Norm
end

section -- merged from ReciprocityTheory.L2DbarEstimates.NormFibrations.NormOrd
universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormOrdStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ) (x : M) (m : ℕ),
    IsLocalHomeomorph z → Holo n z f → VanishesBeyond n z f x m →
    Norm.VanishOrder n z f x (m + 1)

theorem normOrd : NormOrdStatement.{u} := by
  intro n M _ z f x m hz hf hv
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  obtain ⟨C, hC⟩ := Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x)
    e.open_target hzx (hf e he) m (hv e he hx)
  have h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1) :=
    hz.continuous.continuousAt.tendsto.eventually hC
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  rw [Norm.VanishOrder, Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [h1, h2] with y hy hys
  have hy' : e.symm (z y) = y := by rw [he hys]; exact e.left_inv hys
  simp only [Function.comp_apply, hy'] at hy
  rw [norm_pow, norm_norm]
  exact hy

end ReciprocityTheory.L2DbarEstimates
end

section -- merged from ReciprocityTheory.L2DbarEstimates.NormFibrations.NormFib
universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormFibStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ y : V n, (z ⁻¹' {y}).Finite) → ConnectedSpace M →
    ∃ δ : ℕ, ∀ y : V n, (z ⁻¹' {y}).encard ≤ δ

theorem normFib : NormFibStatement.{u} := by
  intro n M _ z U hcov himg hfin hconn

  have hloc : ∀ x : M, ∀ᶠ x' in 𝓝 x, (z ⁻¹' {z x'}).encard = (z ⁻¹' {z x}).encard := by
    intro x
    obtain ⟨hd, W, hxW, hW, hzW, H, hH⟩ := hcov (z x) (himg x)
    have hev : ∀ w ∈ W, IsEvenlyCovered z w (z ⁻¹' {z x}) :=
      fun w hw => ⟨hd, W, hw, hW, hzW, H, hH⟩
    filter_upwards [hzW.mem_nhds (show x ∈ z ⁻¹' W from hxW)] with x' hx'
    exact Set.encard_congr (hev (z x') hx').fiberHomeomorph.toEquiv.symm
  obtain ⟨x0⟩ := (inferInstance : Nonempty M)
  have hS : IsClopen {x : M | (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard} := by
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
      rw [hx']
      exact hx
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx', hx]
  have hall := hS.eq_univ ⟨x0, rfl⟩
  refine ⟨(z ⁻¹' {z x0}).ncard, fun y => ?_⟩
  rw [(hfin (z x0)).cast_ncard_eq]
  by_cases hy : ∃ x, z x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx : (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard := Set.eq_univ_iff_forall.1 hall x
    exact hx.le
  · have h0 : z ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hy ⟨x, h⟩
    rw [h0, Set.encard_empty]
    exact zero_le

end ReciprocityTheory.L2DbarEstimates
end

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

theorem norm (n : ℕ) (M : Type u) [TopologicalSpace M] : NORMStatement n M := by
  intro z Δ u C m hΔ hcov himg hfin hconn hu hgr hvan
  have hpre : z ⁻¹' {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall himg
  have hz : IsLocalHomeomorph z := by
    have h := hcov.isLocalHomeomorphOn
    rw [hpre] at h
    exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 h
  obtain ⟨δ, hδ⟩ := normFib.{u} n M z _ hcov himg hfin hconn
  have hΔ0 : Norm.polyAt n Δ 0 ≠ 0 := by
    have h0 : Norm.polyAt n Δ 0 = MvPolynomial.constantCoeff Δ := by
      rw [← MvPolynomial.eval_zero]
      rfl
    rw [h0]
    exact hΔ
  funext x
  exact Norm.normVanish.{u} n M z Δ δ m C u hΔ0 hcov himg hδ hu hgr
    (fun x hx => normOrd.{u} n M z u x m hz hu (hvan x hx)) x

end ReciprocityTheory.L2DbarEstimates

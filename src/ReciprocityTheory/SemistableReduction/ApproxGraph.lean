module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.ApproxGraphC
section -- merged from ReciprocityTheory.SemistableReduction.ApproxGraphB
section -- merged from ReciprocityTheory.SemistableReduction.ApproxGraphA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

def posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then u k else 0

def negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then 0 else u k

def euc {r : ℕ} (u : Fin r → ℂ) : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 u

lemma euc_add {r : ℕ} (u v : Fin r → ℂ) : euc (u + v) = euc u + euc v := rfl

lemma euc_smul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) : euc (c • u) = c • euc u := rfl

lemma normSq_eq_euc {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq, euc]

lemma posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = ‖euc (posPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold posSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, posPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = ‖euc (negPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold negSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, negPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma normSq_split (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : normSq u = posSq p u + negSq p u := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma posPart_add_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p u + negPart p u = u := by
  funext k
  simp only [posPart, negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    posPart p (u + v) = posPart p u + posPart p v := by
  funext k
  simp only [posPart, Pi.add_apply]
  split_ifs <;> simp

lemma negPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    negPart p (u + v) = negPart p u + negPart p v := by
  funext k
  simp only [negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    posPart p (c • u) = c • posPart p u := by
  funext k
  simp only [posPart, Pi.smul_apply]
  split_ifs <;> simp

lemma negPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    negPart p (c • u) = c • negPart p u := by
  funext k
  simp only [negPart, Pi.smul_apply]
  split_ifs <;> simp

lemma inner_euc {r : ℕ} (x y : Fin r → ℂ) : inner ℂ (euc x) (euc y) = ∑ k, conj (x k) * y k := by
  simp [euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma jForm_eq (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) :
    jForm p x y = inner ℂ (euc (posPart p x)) (euc (posPart p y)) -
      inner ℂ (euc (negPart p x)) (euc (negPart p y)) := by
  rw [inner_euc, inner_euc, ← Finset.sum_sub_distrib]
  unfold jForm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn, posPart, negPart]
  split_ifs <;> simp

lemma jForm_self (p : ℕ) {r : ℕ} (y : Fin r → ℂ) :
    jForm p y y = ((posSq p y - negSq p y : ℝ) : ℂ) := by
  unfold jForm posSq negSq
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  unfold sgn
  split_ifs <;> simp

lemma norm_posPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (posPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := posSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (posPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma norm_negPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (negPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := negSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (negPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma euc_zero {r : ℕ} : euc (0 : Fin r → ℂ) = 0 := by
  rfl

lemma euc_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    euc (∑ j ∈ s, f j) = ∑ j ∈ s, euc (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact euc_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]

lemma euc_eq_zero {r : ℕ} {w : Fin r → ℂ} (h : euc w = 0) : w = 0 := by
  have h' := congrArg WithLp.ofLp h
  simpa [euc] using h'

lemma sum_norm_le_sqrt {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)
  rw [EuclideanSpace.norm_eq]
  simpa [euc] using h

lemma norm_err_le {r p : ℕ} {μ R : ℝ} (X : Fin r → Fin r → ℂ)
    (hX : ∀ j : Fin r, (j : ℕ) < p → normSq (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (hμ : 0 ≤ μ) (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := by
  have he : ∀ j : Fin r, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ ≤ ‖w j‖ * μ := by
    intro j
    by_cases hj : (j : ℕ) < p
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := hX j hj
      rw [normSq_eq_euc] at h1
      have ha := norm_nonneg (euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))
      by_contra h
      push_neg at h
      nlinarith
    · rw [hw j (not_lt.mp hj)]
      simp
  calc ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖
      = ‖∑ j, w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        rw [euc_sum]
        simp only [euc_smul]
    _ ≤ ∑ j, ‖w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        simp only [norm_smul]
    _ ≤ ∑ j, ‖w j‖ * μ := Finset.sum_le_sum fun j _ => he j
    _ = μ * ∑ j, ‖w j‖ := by
        rw [Finset.mul_sum]
        simp only [mul_comm]
    _ ≤ μ * (√(r : ℝ) * ‖euc w‖) := mul_le_mul_of_nonneg_left (sum_norm_le_sqrt w) hμ
    _ = √(r : ℝ) * μ * ‖euc w‖ := by ring

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

lemma posPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (posPart p u) = posPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma posPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (negPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma negPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (posPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma negPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (negPart p u) = negPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma posPart_zero (p : ℕ) {r : ℕ} : posPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [posPart]

lemma negPart_zero (p : ℕ) {r : ℕ} : negPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [negPart]

lemma posPart_supp (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ∀ j : Fin r, p ≤ (j : ℕ) → posPart p u j = 0 := fun j hj => by
  simp [posPart, not_lt.mpr hj]

lemma approxR_nonneg (r : ℕ) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) : 0 ≤ approxR r μ ρ := by
  unfold approxR
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hμ.le) hρ.le

lemma graph_bound {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (negPart p (∑ j, w j • X j))‖ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ ∧
      3 * (√(r : ℝ) * μ * ‖euc w‖) ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
  set R := approxR r μ ρ with hRdef
  have hR0 : 0 ≤ R := approxR_nonneg r hμ hρ
  set E : Fin r → ℂ := ∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) with hE
  have hEn : ‖euc E‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := norm_err_le X hX hμ.le w hw

  have hsum : ∑ j, w j • X j = (R : ℂ) • w + E := by
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hpw : posPart p w = w := by
    ext k
    simp only [posPart]
    split_ifs with h
    · rfl
    · exact (hw k (not_lt.mp h)).symm
  have hnw : negPart p w = 0 := by
    ext k
    simp only [negPart, Pi.zero_apply]
    split_ifs with h
    · rfl
    · exact hw k (not_lt.mp h)
  have hpos : posPart p (∑ j, w j • X j) = (R : ℂ) • w + posPart p E := by
    rw [hsum, posPart_add, posPart_smul, hpw]
  have hneg : negPart p (∑ j, w j • X j) = negPart p E := by
    rw [hsum, negPart_add, negPart_smul, hnw, smul_zero, zero_add]
  set s := √(r : ℝ) * μ * ‖euc w‖ with hs
  have hs0 : 0 ≤ s := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hμ.le) (norm_nonneg _)
  have hnegle : ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := by
    rw [hneg]; exact (norm_negPart_le p E).trans hEn
  have hRw : ‖euc ((R : ℂ) • w)‖ = 4 * s / ρ := by
    rw [euc_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR0, hRdef, approxR, hs]
    ring
  have hposge : 4 * s / ρ - s ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
    rw [hpos, euc_add]
    have h1 := norm_sub_le (euc ((R : ℂ) • w) + euc (posPart p E)) (euc (posPart p E))
    rw [add_sub_cancel_right] at h1
    have h2 := (norm_posPart_le p E).trans hEn
    linarith
  have hq : 4 * s ≤ 4 * s / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  have hqρ : 4 * s / ρ * ρ = 4 * s := div_mul_cancel₀ _ hρ.ne'
  refine ⟨?_, by linarith⟩
  calc ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := hnegle
    _ ≤ ρ / 3 * (4 * s / ρ - s) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hs0]
    _ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ :=
      mul_le_mul_of_nonneg_left hposge (by positivity)

lemma approxGraph_one {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)) := by
  obtain ⟨h1, h2⟩ := graph_bound X hμ hρ hρ1 hX w hw
  refine ⟨?_, fun hw0 => ?_⟩
  · rw [negSq_eq, posSq_eq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · rw [posSq_eq]
    have hwpos : 0 < ‖euc w‖ := by
      rw [norm_pos_iff]; intro h; exact hw0 (euc_eq_zero h)
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; exact absurd (Subsingleton.elim w 0) hw0
      · exact h
    have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
    have h3 : 0 < 3 * (√(r : ℝ) * μ * ‖euc w‖) :=
      mul_pos (by norm_num) (mul_pos (mul_pos hsq hμ) hwpos)
    exact pow_pos (lt_of_lt_of_le h3 h2) 2

def graphMap (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun w := posPart p (∑ j, posPart p w j • X j) + negPart p w
  map_add' u v := by
    simp only [posPart_add, negPart_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c u := by
    have h : ∀ j, posPart p (c • u) j • X j = c • (posPart p u j • X j) := fun j => by
      rw [posPart_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    simp only [← Finset.smul_sum, posPart_smul, negPart_smul, RingHom.id_apply, smul_add]

lemma graphMap_apply (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    graphMap p X w = posPart p (∑ j, posPart p w j • X j) + negPart p w := rfl

lemma exists_graph_pos {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (b : Fin r → ℂ) : ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧
      posPart p (∑ j, w j • X j) = posPart p b := by

  have hinj : Function.Injective (graphMap p X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [graphMap_apply] at hu
    have hn : negPart p u = 0 := by
      have := congrArg (negPart p) hu
      rwa [negPart_add, negPart_posPart, zero_add, negPart_negPart, negPart_zero] at this
    have hp : posPart p (∑ j, posPart p u j • X j) = 0 := by
      have := congrArg (posPart p) hu
      rwa [posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_zero] at this
    have h2 := (graph_bound X hμ hρ hρ1 hX (posPart p u) (posPart_supp p u)).2
    rw [hp, euc_zero, norm_zero] at h2
    have hu0 : posPart p u = 0 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; exact Subsingleton.elim _ _
      · have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
        have hle : ‖euc (posPart p u)‖ ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (mul_pos hsq hμ) hc)
          linarith
        exact euc_eq_zero (norm_le_zero_iff.mp hle)
    rw [← posPart_add_negPart p u, hu0, hn, add_zero]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) (posPart p b)
  refine ⟨posPart p u, posPart_supp p u, ?_⟩
  have := congrArg (posPart p) hu
  rwa [graphMap_apply, posPart_add, posPart_posPart, posPart_negPart, add_zero,
    posPart_posPart] at this

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

lemma jForm_zero_left (p : ℕ) {r : ℕ} (y : Fin r → ℂ) : jForm p 0 y = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.jForm]

lemma jForm_add_left (p : ℕ) {r : ℕ} (x x' y : Fin r → ℂ) :
    jForm p (x + x') y = jForm p x y + jForm p x' y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]

lemma jForm_smul_left (p : ℕ) {r : ℕ} (c : ℂ) (x y : Fin r → ℂ) :
    jForm p (c • x) y = conj c * jForm p x y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma jForm_sum_left (p : ℕ) {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ)
    (y : Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jForm_add_left, ih]

lemma jForm_span_zero (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (y : Fin r → ℂ)
    (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (w : Fin r → ℂ)
    (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) : jForm p (∑ j, w j • X j) y = 0 := by
  rw [jForm_sum_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jForm_smul_left]
  by_cases hj : (j : ℕ) < p
  · rw [hy j hj, mul_zero]
  · rw [hw j (not_lt.mp hj), map_zero, zero_mul]

lemma pos_small_of_orth {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) :
    ‖euc (posPart p y)‖ ≤ ρ / 3 * ‖euc (negPart p y)‖ := by
  obtain ⟨w, hw, hwb⟩ := exists_graph_pos X hμ hρ hρ1 hX y
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  rw [hwb] at hb
  rw [jForm_eq, hwb, sub_eq_zero] at h0
  have h1 := congrArg (fun z : ℂ => (RCLike.re z : ℝ)) h0
  rw [inner_self_eq_norm_sq] at h1
  have h2 : ‖euc (posPart p y)‖ ^ 2 ≤
      ‖euc (negPart p (∑ j, w j • X j))‖ * ‖euc (negPart p y)‖ :=
    h1 ▸ (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hA := norm_nonneg (euc (posPart p y))
  have hB := norm_nonneg (euc (negPart p y))
  have h3 : ‖euc (posPart p y)‖ ^ 2 ≤
      ρ / 3 * ‖euc (posPart p y)‖ * ‖euc (negPart p y)‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hb hB)
  rcases hA.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (div_nonneg hρ.le (by norm_num)) hB
  · nlinarith

lemma approxGraph_two {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (hy0 : y ≠ 0) :
    (jForm p y y).re < 0 := by
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_self, Complex.ofReal_re, posSq_eq, negSq_eq]
  have hA := norm_nonneg (euc (posPart p y))
  have hB := norm_nonneg (euc (negPart p y))
  have hB0 : 0 < ‖euc (negPart p y)‖ := by
    refine lt_of_le_of_ne hB fun h => hy0 ?_
    have hA0 : ‖euc (posPart p y)‖ = 0 :=
      le_antisymm (by rw [← h, mul_zero] at hs; exact hs) hA
    rw [← posPart_add_negPart p y, euc_eq_zero (norm_eq_zero.mp hA0),
      euc_eq_zero (norm_eq_zero.mp h.symm), add_zero]
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  nlinarith [mul_le_mul hs' hs' hA (by linarith : (0 : ℝ) ≤ ‖euc (negPart p y)‖ / 3)]

private theorem exists_coeffs_of_mem_span_lemma {r p : ℕ} (X : Fin r → Fin r → ℂ) {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧ u = ∑ j, w j • X j := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨(Pi.single j 1 : Fin r → ℂ), fun k hk => ?_, ?_⟩
    · have hkj : k ≠ j := fun h => by subst h; exact (not_lt.mpr hk) hj
      simp [hkj]
    · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨c • a, fun j hj => by simp [ha j hj], ?_⟩
    simp [Finset.smul_sum, smul_smul]

lemma approxGraph_three {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (v y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0)
    (hvy : v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ‖jForm p y y‖ ≤ 2 * normSq v := by
  obtain ⟨w, hw, hu⟩ := exists_coeffs_of_mem_span_lemma X hvy
  have hv : v = y + ∑ j, w j • X j := by rw [← hu]; abel
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_eq, sub_eq_zero] at h0
  have hre : RCLike.re (inner ℂ (euc (posPart p y))
        (euc (posPart p (∑ j, w j • X j)))) =
      RCLike.re (inner ℂ (euc (negPart p y)) (euc (negPart p (∑ j, w j • X j)))) := by
    rw [inner_re_symm, h0, inner_re_symm]
  have hI := (RCLike.abs_re_le_norm (inner ℂ (euc (negPart p y))
    (euc (negPart p (∑ j, w j • X j))))).trans (norm_inner_le_norm _ _)
  rw [jForm_self, Complex.norm_real, Real.norm_eq_abs, normSq_split p v, posSq_eq,
    posSq_eq, negSq_eq, negSq_eq, hv, posPart_add, negPart_add, euc_add,
    euc_add, norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hre]
  have hPy := norm_nonneg (euc (posPart p y))
  have hNy := norm_nonneg (euc (negPart p y))
  have hPu := norm_nonneg (euc (posPart p (∑ j, w j • X j)))
  have hNu := norm_nonneg (euc (negPart p (∑ j, w j • X j)))
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  have hb' : ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (posPart p (∑ j, w j • X j))‖ / 3 :=
    hb.trans (by nlinarith)
  have hI' := (abs_le.mp hI).1
  have ha : ‖euc (posPart p y)‖ ^ 2 ≤ ‖euc (negPart p y)‖ ^ 2 := by nlinarith
  have hc : ‖euc (negPart p y)‖ * ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (negPart p y)‖ * (‖euc (posPart p (∑ j, w j • X j))‖ / 3) :=
    mul_le_mul_of_nonneg_left hb' hNy
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg (‖euc (posPart p (∑ j, w j • X j))‖ -
      2 / 3 * ‖euc (negPart p y)‖), sq_nonneg ‖euc (posPart p y)‖,
      sq_nonneg ‖euc (negPart p (∑ j, w j • X j))‖, sq_nonneg ‖euc (negPart p y)‖]

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

namespace ReciprocityTheory.MultiplicativeHeights

open ApproximationGraph in
theorem approxGraph_holds : ApproxGraphStatement := by
  intro r p μ ρ X _ hμ hρ hρ1 hX
  exact ⟨fun w hw => approxGraph_one X hμ hρ hρ1 hX w hw,
    fun y hy hy0 => approxGraph_two X hμ hρ hρ1 hX y hy hy0,
    fun v y hy hvy => approxGraph_three X hμ hρ hρ1 hX v y hy hvy⟩

end ReciprocityTheory.MultiplicativeHeights

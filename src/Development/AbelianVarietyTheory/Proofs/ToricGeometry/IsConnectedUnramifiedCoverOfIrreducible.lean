module

public import ReciprocityTheory.ThetaQuasiPeriods.Change

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.NodupRootsOfDerivativeNeZero
open Filter Topology Polynomial

namespace GlobalTheory.SimpleRoots

variable {d : ℕ}

theorem eval_map_eq_sum (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by
  rw [eval_map, eval₂_eq_sum_range]

theorem analyticAt_mvPolynomial_eval (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x :=
  AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)

theorem analyticAt_eval_map (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by
  simp only [eval_map_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)

theorem exists_analytic_root (p : Polynomial (MvPolynomial (Fin d) ℂ)) {x₀ : Fin d → ℂ} {y₀ : ℂ}
    (h0 : (p.map (MvPolynomial.eval x₀)).eval y₀ = 0)
    (h1 : (p.map (MvPolynomial.eval x₀)).derivative.eval y₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0) ∧
      ∀ᶠ w in 𝓝 (x₀, y₀), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 ↔ ψ w.1 = w.2 := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun w => (p.map (MvPolynomial.eval w.1)).eval w.2 with hf
  have ha : AnalyticAt ℂ f (x₀, y₀) := analyticAt_eval_map p _
  have hc : ContDiffAt ℂ ⊤ f (x₀, y₀) := ha.contDiffAt
  have hd : HasFDerivAt (fun y : ℂ => f (x₀, y))
      (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ) y₀ :=
    ha.differentiableAt.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)
  have hd' := ((p.map (MvPolynomial.eval x₀)).hasDerivAt y₀).hasFDerivAt
  have he := hd.unique hd'
  have hi : (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [he]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨hc.implicitFunction (by simp) hi, ?_, hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with x hx
    exact hx.trans h0
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with w hw
    rw [← hw]
    exact Iff.of_eq (congrArg _ h0.symm)

theorem nodup_roots_of_derivative_ne_zero {P : ℂ[X]} (hP : P ≠ 0)
    (h : ∀ y, P.eval y = 0 → P.derivative.eval y ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hy
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)
  exact h y h1 h2

theorem exists_analytic_roots {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0) :
    ∃ ψ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ y ∈ (p.map (MvPolynomial.eval x₀)).roots, AnalyticAt ℂ (ψ y) x₀ ∧ ψ y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).roots
        = (p.map (MvPolynomial.eval x₀)).roots.map fun y => ψ y x := by
  classical
  have hne : ∀ x, p.map (MvPolynomial.eval x) ≠ 0 := fun x => (hp.map _).ne_zero
  have hex : ∀ y, ∃ ψ : (Fin d → ℂ) → ℂ, y ∈ (p.map (MvPolynomial.eval x₀)).roots →
      AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y ∧
        ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0 := by
    intro y
    by_cases hy : y ∈ (p.map (MvPolynomial.eval x₀)).roots
    · have hy' := (mem_roots (hne x₀)).mp hy
      obtain ⟨ψ, h1, h2, h3, -⟩ := exists_analytic_root p hy' (h y hy')
      exact ⟨ψ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun hy' => absurd hy' hy⟩
  choose ψ hψ using hex
  refine ⟨ψ, fun y hy => ⟨(hψ y hy).1, (hψ y hy).2.1⟩, ?_⟩
  set S := (p.map (MvPolynomial.eval x₀)).roots with hS
  have hnd : S.Nodup := nodup_roots_of_derivative_ne_zero (hne x₀) h
  have hcard : ∀ x, (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := fun x => by
    rw [← hp.natDegree_map (MvPolynomial.eval x)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have e1 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 :=
    (Finset.eventually_all _).mpr fun y hy => (hψ y (Multiset.mem_toFinset.mp hy)).2.2
  have e2 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, ∀ y' ∈ S.toFinset, y ≠ y' → ψ y x ≠ ψ y' x := by
    refine (Finset.eventually_all _).mpr fun y hy => (Finset.eventually_all _).mpr fun y' hy' => ?_
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun _ hn => absurd hyy hn
    · obtain ⟨a1, a2, -⟩ := hψ y (Multiset.mem_toFinset.mp hy)
      obtain ⟨b1, b2, -⟩ := hψ y' (Multiset.mem_toFinset.mp hy')
      have := (a1.continuousAt.ne_iff_eventually_ne b1.continuousAt).mp (by rwa [a2, b2])
      exact this.mono fun x hx _ => hx
  filter_upwards [e1, e2] with x h1 h2
  symm
  refine Multiset.eq_of_le_of_card_le ?_ ?_
  · refine (Multiset.le_iff_subset (hnd.map_on fun y hy y' hy' hyy => ?_)).mpr fun t ht => ?_
    · by_contra hn
      exact h2 y (Multiset.mem_toFinset.mpr hy) y' (Multiset.mem_toFinset.mpr hy') hn hyy
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ht
      exact (mem_roots (hne x)).mpr (h1 y (Multiset.mem_toFinset.mpr hy))
  · rw [Multiset.card_map, hcard, hS, hcard]

theorem differentiableAt_coeff_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by
  induction T using Multiset.induction_on generalizing k with
  | empty => simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ (ha.mul (ih' k))
    cases k with
    | zero => simp
    | succ k => simpa only [coeff_X_mul] using ih' k

theorem norm_coeff_prod_le (T : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ y ∈ T, ‖y‖ ≤ R) (k : ℕ) :
    ‖(T.map fun y => X - C y).prod.coeff k‖ ≤ (1 + R) ^ T.card := by
  induction T using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero]
    split_ifs <;> simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul,
      Multiset.card_cons]
    have h1 : ‖(X * (T.map fun y => X - C y).prod).coeff k‖ ≤ (1 + R) ^ T.card := by
      cases k with
      | zero => simp; positivity
      | succ k => simpa only [coeff_X_mul] using ih' k
    have h2 : ‖a * (T.map fun y => X - C y).prod.coeff k‖ ≤ R * (1 + R) ^ T.card := by
      rw [norm_mul]
      exact mul_le_mul ha (ih' k) (norm_nonneg _) hR
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring

theorem exists_norm_eval_le (a : MvPolynomial (Fin d) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x a‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction a using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add a b ha hb =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    obtain ⟨C₂, m₂, h₂, hb⟩ := hb
    refine ⟨C₁ + C₂, m₁ + m₂, by positivity, fun x => ?_⟩
    have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rw [map_add (f := _), add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((ha x).trans ?_) ((hb x).trans ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₁
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₂
  | mul_X a i ha =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    refine ⟨C₁, m₁ + 1, h₁, fun x => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (ha x) ?_ (norm_nonneg _) (by positivity)
    linarith [norm_le_pi_norm x i]

theorem norm_root_le {P : ℂ[X]} (hP : P.Monic) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ M) {y : ℂ} (hy : P.eval y = 0) : ‖y‖ ≤ M + 1 := by
  have h1 := IsRoot.norm_lt_cauchyBound hP.ne_zero hy
  lift M to NNReal using hM0
  have h2 : P.cauchyBound ≤ M + 1 := by
    unfold cauchyBound
    rw [hP.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi => by exact_mod_cast hM i (Finset.mem_range.mp hi)
  exact_mod_cast (h1.trans_le h2).le

theorem exists_norm_root_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)
  set s := Finset.range p.natDegree
  have hs : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h2 := norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i))
    (by positivity) (fun i hi => ?_) hy
  · rw [add_mul, one_mul]
    linarith [one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]
  · rw [hp.natDegree_map] at hi
    have hi' : i ∈ s := Finset.mem_range.mpr hi
    rw [coeff_map]
    refine (h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi')
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi'))
      (by positivity) hs)

end GlobalTheory.SimpleRoots
end

open Filter Topology

namespace GlobalTheory.SimpleRoots

open Polynomial

variable {d : ℕ}


open Classical in
noncomputable def partialProd (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : ℂ[X] := by
  classical
  exact (((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u).map
    fun y => X - C y).prod

theorem card_roots_map {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) (x : Fin d → ℂ) :
    (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := by
  rw [IsAlgClosed.card_roots_eq_natDegree, hp.natDegree_map]

theorem natDegree_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : (partialProd p u x).natDegree ≤ p.natDegree := by
  classical
  unfold partialProd
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← card_roots_map hp x]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem partialProd_mul_compl {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) :
    partialProd p u x * partialProd p uᶜ x = p.map (MvPolynomial.eval x) := by
  classical
  unfold partialProd
  rw [← Multiset.prod_add, ← Multiset.map_add (f := _)]
  convert Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map (MvPolynomial.eval x))
    (by rw [card_roots_map hp x, hp.natDegree_map]) using 3
  convert Multiset.filter_add_not (fun y => (x, y) ∈ u) (p.map (MvPolynomial.eval x)).roots using 2
  congr 1

theorem exists_norm_coeff_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) :
    ∃ (C : ℝ) (m : ℕ), ∀ k x, ‖(partialProd p u x).coeff k‖ ≤ C * (1 + ‖x‖) ^ m := by
  classical
  obtain ⟨C₀, m₀, hC₀, hroot⟩ := exists_norm_root_le hp
  refine ⟨(1 + C₀) ^ p.natDegree, m₀ * p.natDegree, fun k x => ?_⟩
  set R := C₀ * (1 + ‖x‖) ^ m₀ with hR
  have ht : 1 ≤ (1 + ‖x‖) ^ m₀ := one_le_pow₀ (by linarith [norm_nonneg x])
  have hR0 : 0 ≤ R := mul_nonneg hC₀ (by linarith)
  have hbound := norm_coeff_prod_le
    ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) hR0
    (fun y hy => hroot x y ((Polynomial.mem_roots (hp.map _).ne_zero).mp
      (Multiset.mem_of_mem_filter hy))) k
  have hcard : Multiset.card ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) ≤
      p.natDegree := by
    rw [← card_roots_map hp x]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have h1R : 1 + R ≤ (1 + C₀) * (1 + ‖x‖) ^ m₀ := by
    rw [hR]; nlinarith
  calc ‖(partialProd p u x).coeff k‖ ≤ (1 + R) ^ Multiset.card
          ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) := hbound
    _ ≤ (1 + R) ^ p.natDegree := pow_le_pow_right₀ (by linarith) hcard
    _ ≤ ((1 + C₀) * (1 + ‖x‖) ^ m₀) ^ p.natDegree := pow_le_pow_left₀ (by linarith) h1R _
    _ = (1 + C₀) ^ p.natDegree * (1 + ‖x‖) ^ (m₀ * p.natDegree) := by rw [mul_pow, ← pow_mul]

theorem differentiableAt_coeff_partialProd {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {u : Set ((Fin d → ℂ) × ℂ)} {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0)
    (hu : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
      (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u)) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (partialProd p u x).coeff k) x₀ := by
  classical
  obtain ⟨ψ, hψ, hroots⟩ := exists_analytic_roots hp h
  set R₀ := (p.map (MvPolynomial.eval x₀)).roots with hR₀
  have hψc : ∀ y ∈ R₀, ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 →
      ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) := by
    intro y hy
    have hy0 : (p.map (MvPolynomial.eval x₀)).eval y = 0 :=
      (Polynomial.mem_roots (hp.map _).ne_zero).mp hy
    have ht : Tendsto (fun x => (x, ψ y x)) (𝓝 x₀) (𝓝 (x₀, y)) := by
      have := (continuousAt_id.prodMk (hψ y hy).1.continuousAt).tendsto
      simpa [(hψ y hy).2] using this
    exact ht.eventually (hu y hy0)
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ R₀.toFinset,
      (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 → ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) :=
    (Filter.eventually_all_finset _).mpr fun y hy => hψc y (Multiset.mem_toFinset.mp hy)
  have heq : (fun x => (partialProd p u x).coeff k) =ᶠ[𝓝 x₀]
      fun x => ((R₀.filter fun y => (x₀, y) ∈ u).map fun y => X - C (ψ y x)).prod.coeff k := by
    filter_upwards [hroots, hall] with x hx hxa
    have hfilter : (R₀.filter fun y => (x, ψ y x) ∈ u) =
        (R₀.filter fun y => (x₀, y) ∈ u) := by
      refine Multiset.filter_congr fun y hy => ?_
      refine hxa y (Multiset.mem_toFinset.mpr hy) ?_
      have hmem : ψ y x ∈ (p.map (MvPolynomial.eval x)).roots := by
        rw [hx]; exact Multiset.mem_map_of_mem _ hy
      exact (Polynomial.mem_roots (hp.map _).ne_zero).mp hmem
    simp only [partialProd, hx, Multiset.filter_map, Multiset.map_map, Function.comp_def, hfilter]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact differentiableAt_coeff_prod _ ψ
    (fun y hy => (hψ y (Multiset.mem_of_mem_filter hy)).1.differentiableAt) k

theorem eq_of_map_eval_eq_of_dense {a b : Polynomial (MvPolynomial (Fin d) ℂ)}
    {U : Set (Fin d → ℂ)} (hU : Dense U)
    (h : ∀ x ∈ U, a.map (MvPolynomial.eval x) = b.map (MvPolynomial.eval x)) : a = b := by
  ext i
  have hfun : (fun x => MvPolynomial.eval x (a.coeff i)) = fun x => MvPolynomial.eval x (b.coeff i) := by
    refine Continuous.ext_on hU (MvPolynomial.continuous_eval _) (MvPolynomial.continuous_eval _) ?_
    intro x hx
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) (h x hx)
    simpa [Polynomial.coeff_map] using this
  exact congrArg (fun c => AddMonoidAlgebra.coeff c _) (MvPolynomial.funext fun x => congrFun hfun x)

end GlobalTheory.SimpleRoots

namespace GlobalTheory

open SimpleRoots

theorem isConnected_unramified_cover_of_irreducible :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) →
    (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) →
    (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ),
      p.Monic → Irreducible p → q ≠ 0 →
      (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 →
        (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) →
      IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) := by
  intro H1 H2 d p q hp hirr hq hsimp
  obtain ⟨hΩc, hΩd⟩ := H1 d q hq
  have hΩo : IsOpen {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
  have hdeg : p.natDegree ≠ 0 := by
    intro h0
    exact hirr.not_isUnit (by rw [hp.natDegree_eq_zero.mp h0]; exact isUnit_one)
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hΩc.nonempty
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by rw [card_roots_map hp x]; omega : 0 < Multiset.card (p.map (MvPolynomial.eval x)).roots)
    exact ⟨(x, y), hx, (Polynomial.mem_roots (hp.map _).ne_zero).mp hy⟩
  intro u v hu hv hZ hZu hZv
  by_contra hne
  have hdisj : ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
      (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ u → z ∉ v :=
    fun z hzq hz0 hzu hzv => hne ⟨z, ⟨hzq, hz0⟩, hzu, hzv⟩
  have hloc : ∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      ∀ᶠ w in 𝓝 (x₀, y), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u) := by
    intro x₀ hx₀ y hy
    by_cases hyu : (x₀, y) ∈ u
    · filter_upwards [hu.mem_nhds hyu] with w hw _ using iff_of_true hw hyu
    · have hyv : (x₀, y) ∈ v := (@hZ (x₀, y) ⟨hx₀, hy⟩).resolve_left hyu
      filter_upwards [hv.mem_nhds hyv,
        continuous_fst.continuousAt.preimage_mem_nhds (hΩo.mem_nhds hx₀)] with w hwv hwq hw0
      exact iff_of_false (fun hwu => hdisj w hwq hw0 hwu hwv) hyu
  have hpoly : ∀ s : Set ((Fin d → ℂ) × ℂ), (∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y,
      (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
        (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ s ↔ (x₀, y) ∈ s)) →
      ∃ A : Polynomial (MvPolynomial (Fin d) ℂ), ∀ x, MvPolynomial.eval x q ≠ 0 →
        A.map (MvPolynomial.eval x) = partialProd p s x := by
    intro s hs
    obtain ⟨C₁, m, hC₁⟩ := exists_norm_coeff_partialProd_le hp s
    have hk : ∀ k, ∃ a : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        (partialProd p s x).coeff k = MvPolynomial.eval x a := fun k =>
      H2 d m q (fun x => (partialProd p s x).coeff k) C₁ hq
        (fun x hx => (differentiableAt_coeff_partialProd hp (fun y hy => hsimp x y hx hy)
          (hs x hx) k).differentiableWithinAt)
        (fun x _ => hC₁ k x)
    choose a ha using hk
    refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (a k), fun x hx => ?_⟩
    ext k
    rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hk'
    · exact (ha k x hx).symm
    · have := natDegree_partialProd_le hp s x
      rw [map_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  obtain ⟨A, hA⟩ := hpoly u hloc
  obtain ⟨B, hB⟩ := hpoly uᶜ fun x₀ hx₀ y hy =>
    (hloc x₀ hx₀ y hy).mono fun w hw h0 => not_congr (hw h0)
  have hAB : A * B = p := eq_of_map_eval_eq_of_dense hΩd fun x hx => by
    rw [Polynomial.map_mul, hA x hx, hB x hx, partialProd_mul_compl hp]
  have hnot : ∀ (s : Set ((Fin d → ℂ) × ℂ)) (A' : Polynomial (MvPolynomial (Fin d) ℂ)),
      (∀ x, MvPolynomial.eval x q ≠ 0 → A'.map (MvPolynomial.eval x) = partialProd p s x) →
      ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ s → ¬ IsUnit A' := by
    intro s A' hA' z hzq hz0 hzs hunit
    classical
    have hu' : IsUnit (A'.map (MvPolynomial.eval z.1)) :=
      hunit.map (Polynomial.mapRingHom (MvPolynomial.eval z.1))
    rw [hA' z.1 hzq] at hu'
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit hu'
    unfold partialProd at h2
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_eq_zero] at h2
    exact Multiset.filter_eq_nil.mp h2 z.2 ((Polynomial.mem_roots (hp.map _).ne_zero).mpr hz0) hzs
  obtain ⟨z, ⟨hzq, hz0⟩, hzu⟩ := hZu
  obtain ⟨z', ⟨hzq', hz0'⟩, hzv'⟩ := hZv
  rcases hirr.isUnit_or_isUnit hAB.symm with h | h
  · exact hnot u A hA z hzq hz0 hzu h
  · exact hnot uᶜ B hB z' hzq' hz0' (fun hzu' => hdisj z' hzq' hz0' hzu' hzv') h

end GlobalTheory

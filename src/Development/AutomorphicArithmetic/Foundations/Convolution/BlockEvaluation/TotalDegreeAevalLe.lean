module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TotalDegreeAevalLe
open Classical

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem totalDegree_aeval_le {σ : Type*} (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ 1) (p : Polynomial ℂ) :
    (Polynomial.aeval q p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  calc
    i * q.totalDegree ≤ i * 1 := Nat.mul_le_mul_left _ hq
    _ ≤ p.natDegree := by simpa using hi'

private theorem exists_fin_map (n : ℕ) (s : Multiset ℂ) (hs : s.card = n) :
    ∃ f : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map f = s := by
  subst hs
  induction s using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get <;> simp

theorem UpperTheory.ConvolutionTheory.Ci.bdLem :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ κ' : Finset (Pl K)) (D D' d d' : ℕ) (R R' : PR K n),
      (Bd κ D d R → Bd κ' D' d' R' → Bd (κ ∪ κ') (D + D') (d + d') (R * R')) ∧ (∀ η m, Bd κ 0 m (chebP η m : PR K n)) ∧
      (κ ⊆ κ' → D ≤ D' → d ≤ d' → Bd κ D d R → Bd κ' D' d' R) ∧
      ∀ Λ : (K →+* ℂ) → Multiset ℂ, (∀ τ, (Λ τ).card = n) → ∃ L : Ix K n → ℂ, msOf L = Λ := by
  intro K _ _ n κ κ' D D' d d' R R'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, (totalDegree_mul _ _).trans (Nat.add_le_add h2 h2'), ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (vars_mul R R' hx) with h | h
      · exact Finset.mem_union_left _ (h1 x h)
      · exact Finset.mem_union_right _ (h1' x h)
    · intro β
      rw [coeff_mul]
      exact totalDegree_finsetSum_le fun _ _ =>
        (totalDegree_mul _ _).trans (Nat.add_le_add (h3 _) (h3' _))
  · intro η m
    have hq : (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_X]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [chebP, vars_C] at hx
    · simp [chebP]
    · intro β
      unfold chebP
      rw [coeff_C]
      split_ifs
      · refine (totalDegree_aeval_le _ hq _).trans ?_
        simp [Polynomial.Chebyshev.natDegree_T]
      · simp
  · rintro hκ hD hd ⟨h1, h2, h3⟩
    exact ⟨fun x hx => hκ (h1 x hx), h2.trans hD, fun β => (h3 β).trans hd⟩
  · intro Λ hΛ
    choose f hf using fun τ => exists_fin_map n (Λ τ) (hΛ τ)
    refine ⟨fun y => f y.1 y.2, ?_⟩
    funext τ
    exact hf τ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.ExpForm
open UpperTheory.ConvolutionTheory.Ci

namespace UpperTheory.ConvolutionTheory.Ci.ExponentialForm

open Polynomial

private theorem semiconj_aeval {A : Type} [Ring A] [Algebra ℂ A] {a x y : A} (h : SemiconjBy a x y) (p : ℂ[X]) :
    SemiconjBy a (aeval x p) (aeval y p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add_right hq
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def]
    have := (h.pow_right n).eq
    unfold SemiconjBy
    rw [mul_smul_comm, smul_mul_assoc, this]

private theorem nil_mul {A : Type} [Ring A] (l : ℕ) (hl : 0 < l) (M : ZMod l → A) (B : A)
    (hc : ∀ i k, Commute (M i) (M k)) (hB : ∀ i, B * M i = M (i + 1) * B) (h0 : IsNilpotent (M 0)) :
    IsNilpotent (M 0 * B) := by
  have h1 : ∀ (m : ℕ) (i : ZMod l), B ^ m * M i = M (i + m) * B ^ m := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hB, mul_assoc, Nat.cast_succ, add_assoc]
  have h2 : ∀ m : ℕ, ∃ P : A, Commute (M 0) P ∧ (M 0 * B) ^ (m + 1) = M 0 * (P * B ^ (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨1, Commute.one_right _, by simp⟩
    | succ m ih =>
      obtain ⟨P, hP, h⟩ := ih
      refine ⟨P * M (0 + ((m + 1 : ℕ) : ZMod l)), hP.mul_right (hc _ _), ?_⟩
      rw [pow_succ, h, pow_succ B (m + 1)]
      simp only [mul_assoc]
      rw [← mul_assoc (B ^ (m + 1)) (M 0), h1, mul_assoc]
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  obtain ⟨P, hP, h⟩ := h2 m
  have h3 : Commute (M 0) (B ^ (m + 1)) := by
    have := h1 (m + 1) 0
    rw [ZMod.natCast_self, add_zero] at this
    exact this.symm
  have h4 : IsNilpotent ((M 0 * B) ^ (m + 1)) := by
    rw [h]
    exact (hP.mul_right h3).isNilpotent_mul_right h0
  exact h4.of_pow

private theorem nil_nodal {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (U : Module.End ℂ W) :
    IsNilpotent (aeval U (Lagrange.nodal U.charpoly.roots.toFinset id)) := by
  classical
  set r := Lagrange.nodal U.charpoly.roots.toFinset id with hr
  have h1 : U.charpoly = (U.charpoly.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits U.charpoly).eq_prod_roots_of_monic U.charpoly_monic
  have h2 : (U.charpoly.roots.map fun a => X - C a).prod ∣ (U.charpoly.roots.map fun _ => r).prod :=
    Multiset.prod_dvd_prod_of_dvd _ _ fun a ha =>
      Lagrange.X_sub_C_dvd_nodal id (Multiset.mem_toFinset.2 ha)
  rw [← h1, Multiset.map_const', Multiset.prod_replicate] at h2
  obtain ⟨q, hq⟩ := h2
  refine ⟨U.charpoly.roots.card, ?_⟩
  rw [← map_pow, hq, map_mul, LinearMap.aeval_self_charpoly, zero_mul]

private theorem pow_eq (s : Finset ℂ) (j : ℕ) :
    ∃ q : ℂ[X], X ^ j = Lagrange.nodal s id * q + ∑ z ∈ s, C (z ^ j) * Lagrange.basis s id z := by
  classical
  have h : Lagrange.nodal s id ∣ X ^ j - ∑ z ∈ s, C (z ^ j) * Lagrange.basis s id z := by
    unfold Lagrange.nodal
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
    · intro a ha
      rw [dvd_iff_isRoot, IsRoot.def, eval_sub]
      have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (fun z : ℂ => z ^ j) (Set.injOn_id _) ha
      rw [Lagrange.interpolate_apply] at this
      rw [this]
      simp
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

private theorem trace_eq {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (l : ℕ) (hl : 0 < l)
    (U : ZMod l → Module.End ℂ W) (B : Module.End ℂ W) (hc : ∀ i k, Commute (U i) (U k))
    (hB : ∀ i, B * U i = U (i + 1) * B) :
    ∃ (s : Finset ℂ) (p : ℂ → ℂ[X]), ∀ j : ℕ, LinearMap.trace ℂ W (U 0 ^ j * B) =
      ∑ z ∈ s, LinearMap.trace ℂ W (aeval (U 0) (p z) * B) * z ^ j := by
  classical
  refine ⟨(U 0).charpoly.roots.toFinset, Lagrange.basis (U 0).charpoly.roots.toFinset id, fun j => ?_⟩
  obtain ⟨q, hq⟩ := pow_eq (U 0).charpoly.roots.toFinset j
  have hn := nil_nodal (U 0)
  set r := Lagrange.nodal (U 0).charpoly.roots.toFinset id with hr
  have h1 : IsNilpotent (aeval (U 0) (r * q) * B) := by
    refine nil_mul l hl (fun i => aeval (U i) (r * q)) B (fun i k => ?_) (fun i => semiconj_aeval (hB i) _) ?_
    · exact Commute.symm (semiconj_aeval (Commute.symm (semiconj_aeval (hc i k) _)) _)
    · have : Commute (aeval (U 0) r) (aeval (U 0) q) := (Commute.all r q).map _
      simp only [map_mul]
      exact this.isNilpotent_mul_right hn
  have h2 : LinearMap.trace ℂ W (aeval (U 0) (r * q) * B) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  have h3 : U 0 ^ j = aeval (U 0) (X ^ j : ℂ[X]) := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h3, hq, map_add (f := _), add_mul, map_add (f := _), h2, zero_add, map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul (aeval (U 0)), aeval_C, ← Algebra.smul_def, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]

end UpperTheory.ConvolutionTheory.Ci.ExponentialForm

theorem UpperTheory.ConvolutionTheory.Ci.expForm :
    ExpForm := by
  classical
  intro W _ _ _ l hl U B hc hB
  obtain ⟨s, p, h⟩ := ExponentialForm.trace_eq l hl U B hc hB
  refine ⟨s.erase 0, fun z => LinearMap.trace ℂ W (Polynomial.aeval (U 0) (p z) * B), Finset.notMem_erase _ _,
    fun j hj => ?_⟩
  rw [h j]
  refine (Finset.sum_erase _ ?_).symm
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (Nat.le_zero.1 hj)
    rw [Subsingleton.elim (Polynomial.aeval (U 0) (p 0) * B) 0, map_zero, zero_mul]
  · rw [zero_pow hj0.ne', mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SideEst
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem msOf_ex {K : Type} [Field K] [NumberField K] {n : ℕ} (Λ : (K →+* ℂ) → Multiset ℂ) (h : ∀ τ, (Λ τ).card = n) :
    ∃ L : Ix K n → ℂ, msOf L = Λ := by
  have : ∀ τ, ∃ f : Fin n → ℂ, Finset.univ.val.map f = Λ τ := by
    intro τ
    have h1 := h τ
    induction hm : Λ τ using Quotient.inductionOn with
    | _ a =>
      rw [hm] at h1
      have h2 : a.length = n := by simpa using h1
      subst h2
      exact ⟨a.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  choose f hf using this
  exact ⟨fun x => f x.1 x.2, funext hf⟩

private theorem val_congr {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Pl K)) (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t t' : Pl K → Multiset ℂ) (h : ∀ w ∉ S, t w = t' w) (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) :
    val x Λ t P = val x Λ t' P :=
  eval₂Hom_congr' rfl (fun i hi _ => by unfold hval; rw [h _ (hP i hi)]) rfl

private theorem arith (C w zN zi q r kM e B E1 E2 kk f g1 g2 : ℝ) (hw : 0 ≤ w) (hzN : 0 ≤ zN) (hzi : 0 ≤ zi) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hkM : 0 ≤ kM) (he : 0 ≤ e) (hB : 0 ≤ B) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hkk : 0 ≤ kk) (hf : 0 < f)
    (hg1 : 1 ≤ g1) (hg2 : 1 ≤ g2) (h1 : w * zN ≤ E1 * g1) (h2 : w * zi ≤ E2) (h3 : q ≤ B * e) (h4 : r ≤ B * e / f)
    (h5 : kM ≤ kk * g2) :
    C * w * (zN * (q + kM * r) + kM * zi * q) ≤ |C| * e * g1 * g2 * B * (E1 * (1 + kk / f) + kk * E2) := by
  have g1' : 0 ≤ g1 := zero_le_one.trans hg1
  have g2' : 0 ≤ g2 := zero_le_one.trans hg2
  have h2' : w * zi ≤ g1 * E2 := h2.trans (le_mul_of_one_le_left hE2 hg1)
  have h3' : q ≤ g2 * (B * e) := h3.trans (le_mul_of_one_le_left (by positivity) hg2)
  have hC := le_abs_self C
  calc _ = C * (w * zN * (q + kM * r) + kM * (w * zi) * q) := by ring
    _ ≤ |C| * (w * zN * (q + kM * r) + kM * (w * zi) * q) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ |C| * (E1 * g1 * (g2 * (B * e) + kk * g2 * (B * e / f)) + kk * g2 * (g1 * E2) * (B * e)) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Ci.sideEst :
    OneSide → EvVal → TruncSpec → ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n l : ℕ), 0 < n →
      ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)),
      𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → ∀ C₀ : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) ∧
        ∀ Φ G, admitted 𝔰.S Φ → IsGen Φ G →
          (∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖ ≤ C ^ (d + 1) / d.factorial) →
          ∀ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ 𝔰.S) → ∃ u : ℝ × Submodule ℂ (LL μ) → ℕ → ℂ,
            (∀ y ∈ s, ∀ (L : Ix K n → ℂ) t, At μ 𝔰.S y.2 (msOf L) t →
              Tendsto (u y) atTop (𝓝 (y.1 * val y.1 (msOf L) t P * evK L (hval t) Φ))) ∧
            ∀ (p : ℕ) (N : ℝ) (s₀ : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (j d : ℕ), ∀ m ≤ s₀, ∀ m' ≤ s₀, ∀ f : TG K n,
              𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (C₀ * ((j + m' : ℕ) : ℝ))) f →
              ‖twInt θ f - ∑ y ∈ s, u y d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
                  trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)‖ ≤
                M ^ (d + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) := by
  intro hOS hEV hTS K _ _ _ n l hn μ _ θ 𝔰 ev hev hin C₀
  classical
  obtain ⟨N, hN⟩ := hOS K n l hn μ θ 𝔰 ev hev hin
  obtain ⟨C, hC0, hC1⟩ : ∃ C : ℝ, C₀ ≤ C ∧ 1 ≤ C := ⟨max C₀ 1, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨lu, hlu0, hlu⟩ : ∃ lu : ℝ, 0 ≤ lu ∧ ‖𝔰.Uq 0‖ ≤ Real.exp lu :=
    ⟨‖𝔰.Uq 0‖, norm_nonneg _, by linarith [Real.add_one_le_exp ‖𝔰.Uq 0‖]⟩
  refine ⟨N * C + lu, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := hN η hη hη1 χ hχ hχ1 hχ2
  refine ⟨s, hs1, hs2, fun Φ G hΦ hG hb P hP => ?_⟩
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨⟨κ, D, hκ, hBd⟩, hu, hM⟩ := (hTS K n 𝔰.S Φ hΦ).2 G hG
  obtain ⟨Mt, hMt⟩ := hM _ ev hev.const
  have hE := fun y (hy : y ∈ s) => hEV K n hn μ 𝔰.toAmp y.2 y.1 (hη.trans ((hs1 y).1 hy).1) ((hs1 y).1 hy).2.1
  have hex : ∀ y : ℝ × Submodule ℂ (LL μ), ∃ (L : Ix K n → ℂ) (t : Pl K → Multiset ℂ), y ∈ s → At μ 𝔰.S y.2 (msOf L) t := by
    intro y
    by_cases hy : y ∈ s
    · obtain ⟨Λ, t, h⟩ := (hE y hy).1 ((hs1 y).1 hy).2.2.2
      obtain ⟨L, rfl⟩ := msOf_ex Λ fun τ => (h.1 τ).1
      exact ⟨L, t, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose L t hLt using hex
  choose u hu1 hu2 using hu
  have hT : ∀ d, ∀ y ∈ (trunc d G).vars, y.1 ∉ 𝔰.S := fun d y hy => hκ _ ((hBd d).1 y hy)
  refine ⟨fun y d => y.1 * val y.1 (msOf (L y)) (t y) P * u (L y) (t y) d, fun y hy L' t' h' => ?_, fun p N₁ s₀ => ?_⟩
  · obtain ⟨e1, e2⟩ := (hE y hy).2.1 _ _ _ _ (hLt y hy) h'
    have hy0 : (y.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hη.trans ((hs1 y).1 hy).1).ne'
    have e3 : u (L y) (t y) = u L' t' := by
      funext d
      refine mul_left_cancel₀ (pow_ne_zero d hy0) ?_
      rw [← hu2, ← hu2, e1]
      exact val_congr 𝔰.S _ _ _ _ e2 _ (hT d)
    beta_reduce
    rw [e3, e1, val_congr 𝔰.S _ _ _ _ e2 P hP]
    exact (hu1 L' t').const_mul _
  obtain ⟨N', hN'⟩ := exists_nat_ge (max N₁ 0 + lu)
  obtain ⟨C₁, hC₁⟩ := hs3 N'
  have hk : 1 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have hc₁ : 0 ≤ N * C + lu := by positivity
  obtain ⟨B, hB1, hB2, hB3⟩ : ∃ B : ℝ, 1 ≤ B ∧ |Mt| ≤ B ∧ |Cb| ≤ B :=
    ⟨max 1 (max |Mt| |Cb|), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  obtain ⟨K0, hK0, hK1⟩ : ∃ K0 : ℝ, |C₁| * ‖ev P‖ * Real.exp ((N * C + lu) * s₀) * (4 / η) ^ s₀ ≤ K0 ∧ 1 ≤ K0 :=
    ⟨max _ 1, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K0 * B, by positivity, fun j d m hm m' hm' f hf => ?_⟩
  have hJ0 : (0 : ℝ) ≤ ((j + m' : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJ1 : (j : ℝ) ≤ ((j + m' : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right j m'
  have hJ2 : ((j + m' : ℕ) : ℝ) ≤ j + s₀ := by exact_mod_cast Nat.add_le_add_left hm' j
  have hQv : ∀ y ∈ (trunc d G * P).vars, y.1 ∉ 𝔰.S := fun y hy => by
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · exact hT d y h
    · exact hP y h
  have key := hC₁ (trunc d G * P) (fun y => val y.1 (msOf (L y)) (t y) (trunc d G * P))
    (fun y hy v hv => (hE y hy).2.2 ev hev _ _ (hLt y hy) _ hQv v hv) (j / p + m) (j + m')
    (Real.exp (C * ((j + m' : ℕ) : ℝ))) f (Real.one_le_exp (by positivity))
    ⟨hf.1, fun x hx => hf.2 x (lt_of_le_of_lt (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC0 hJ0)) hx)⟩
  have es : ∑ y ∈ s, y.1 * val y.1 (msOf (L y)) (t y) P * u (L y) (t y) d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) =
      ∑ y ∈ s, (cheb η (j / p + m) y.1 : ℂ) * (y.1 * val y.1 (msOf (L y)) (t y) (trunc d G * P) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, hu2]
    ring
  beta_reduce
  rw [es]
  refine key.trans ?_
  have hw : ‖𝔰.Uq 0‖ ^ (j + m') ≤ Real.exp (lu * ((j + m' : ℕ) : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hlu _
  have hdf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have a1 : ‖𝔰.Uq 0‖ ^ (j + m') * Real.exp (C * ((j + m' : ℕ) : ℝ)) ^ N ≤
      Real.exp ((N * C + lu) * j) * Real.exp ((N * C + lu) * s₀) := by
    refine (mul_le_mul_of_nonneg_right hw (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hJ2 hc₁
    linarith
  have a2 : ‖𝔰.Uq 0‖ ^ (j + m') * (Real.exp (C * ((j + m' : ℕ) : ℝ)) ^ N')⁻¹ ≤ Real.exp (-N₁ * j) := by
    refine (mul_le_mul_of_nonneg_right hw (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have b1 : (N' : ℝ) * ((j + m' : ℕ) : ℝ) ≤ N' * (C * ((j + m' : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hJ0 hC1) (Nat.cast_nonneg _)
    have b2 := mul_le_mul_of_nonneg_right hN' hJ0
    have b3 := mul_le_mul_of_nonneg_left hJ1 (le_max_right N₁ 0)
    have b4 := mul_le_mul_of_nonneg_right (le_max_left N₁ 0) (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    linarith
  have pw : ∀ x : ℝ, |x| ≤ B → x ^ (d + 1) ≤ B ^ (d + 1) := fun x hx =>
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx _)
  have a3 : ‖ev (trunc d G * P)‖ ≤ B ^ (d + 1) * ‖ev P‖ := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((hMt d).trans (pw _ hB2)) (norm_nonneg _))
  have a4 : ‖ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖ ≤ B ^ (d + 1) * ‖ev P‖ / d.factorial := by
    have e : ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ) =
        ev P ∘L (ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)) := by
      rw [mul_comm, map_mul]
      rfl
    rw [e, mul_comm (B ^ (d + 1)), mul_div_assoc]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ((hCb d).trans ?_) (norm_nonneg _))
    exact div_le_div_of_nonneg_right (pw _ hB3) hdf.le
  have a5 : (4 / η) ^ (j / p + m) ≤ (4 / η) ^ (j / p) * (4 / η) ^ s₀ := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk hm) (by positivity)
  refine (arith C₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (norm_nonneg _) (norm_nonneg _)
    (by positivity) (norm_nonneg _) (by positivity) (by positivity) (by positivity) (by positivity) hdf
    (Real.one_le_exp (by positivity)) (one_le_pow₀ hk) a1 a2 a3 a4 a5).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (hK0.trans (le_self_pow₀ hK1 (by omega))) (by positivity)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.EvalPowE
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

theorem UpperTheory.ConvolutionTheory.Ci.valBc :
    ValBc := by
  classical
  intro F E _ _ _ _ _ n x Λ t P hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [val, bcPR]
      · rintro (_ | y)
        · simp [val, bcPR]
        · simp [val, bcPR, bcInf]
    · intro y hy _
      have h := eval_powE (resDeg F y.1) y.2 _ (hP y hy)
      simp only [val, bcPR, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h]
      have hc : ((eval fun o : Option (Ix F n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)).comp C)
          = RingHom.id ℂ := by
        ext c
        simp
      rw [hc]
      rfl
  · intro y hy
    have h : bcPR F P = bind₁ (fun x : Pl E × Fin n =>
        (map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)) : PR F n))
        (map (rename (Option.map fun x : Ix E n => (x.1.comp (algebraMap F E), x.2))).toRingHom P) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [h] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    refine ⟨y', vars_map _ _ hy', ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    rfl
  · intro η m
    simp only [chebP, bcPR, eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Polynomial.aeval_algHom_apply]
    simp
end

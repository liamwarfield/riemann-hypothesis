module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerIndependenceOfOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ReesGradedPieceSurjection
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleMono

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LkHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.lk_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    Q.F (Fin.last r) ∈ satSq x → ∃ 𝔮 : Ideal (mR Q), (𝔮 : Set (mR Q)) = leadKer Q wt φ ∧ (GMod.self (mGr Q)).IsHomSub 𝔮 ∧
      coefIdeal _ (RingHom.ker φ) ≤ 𝔮 ∧ (∀ b : 𝒜 0, x b = 0 → algebraMap (𝒜 0) (mR Q) b ∈ 𝔮) ∧
      (∀ c : O, c ≠ 0 → ∀ p, algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) c) * p ∈ 𝔮 → p ∈ 𝔮) ∧
      ∀ (f g : A) (hf : f ∈ 𝒜 (-1)) (hg : g ∈ 𝒜 (-1)), f - g ∈ satSq x →
        sec (mN 𝒜 (Q.F (Fin.last r))) 0 (f ^ 2) (sq_mem_neg 𝒜 hf) - sec (mN 𝒜 (Q.F (Fin.last r))) 0 (g ^ 2) (sq_mem_neg 𝒜 hg) ∈ 𝔮 := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hF
  have hsat := satfil_holds O A 𝒜 x hW τ wt φ hφ
  have hlat := latfil_holds O A 𝒜 x hW τ wt φ hφ _ (Q.hF (Fin.last r)) hF
  have hmul : ∀ (a b : ℕ) (g h : MvPowerSeries τ (FractionRing O)), g ∈ fil (FractionRing O) wt a →
      h ∈ fil (FractionRing O) wt b → g * h ∈ fil (FractionRing O) wt (a + b) :=
    fun a b g h hg hh => (fil_holds _ τ wt a b g h hg hh).1
  have h0 : ∀ g : MvPowerSeries τ (FractionRing O), g ∈ fil (FractionRing O) wt 0 :=
    fun g ν hν => absurd hν (Nat.not_lt_zero _)
  let 𝔮 : Ideal (mR Q) :=
    { carrier := leadKer Q wt φ
      add_mem' := fun {p q} hp hq μ => by
        show φ (AddMonoidAlgebra.coeff (p.1 + q.1) μ) ∈ _
        rw [MvPolynomial.coeff_add, map_add (f := _)]
        exact add_mem (hp μ) (hq μ)
      zero_mem' := fun μ => by
        show φ 0 ∈ _
        rw [map_zero φ]; exact zero_mem _
      smul_mem' := fun c p hp μ => by
        show φ (AddMonoidAlgebra.coeff (c.1 * p.1) μ) ∈ _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [MvPolynomial.coeff_mul, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        rw [map_mul]
        have h1 := hmul _ _ _ _ (hlat d.1 _ (c.2 d.1)).2 (hp d.2)
        have h2 : d.1 + d.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hd
        have h3 : 2 * μ 0 + 4 * μ 2 + 1 = 2 * d.1 0 + 4 * d.1 2 + (2 * d.2 0 + 4 * d.2 2 + 1) := by
          rw [← h2, Finsupp.add_apply, Finsupp.add_apply]; ring
        rw [h3]; exact h1 }
  have hmono : ∀ (μ : Fin 3 →₀ ℕ) (p : mR Q) (f : A), p.1 = MvPolynomial.monomial μ f →
      φ f ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2 + 1) → p ∈ 𝔮 := by
    intro μ p f hp h ν
    rw [hp, MvPolynomial.coeff_monomial]
    split_ifs with h1
    · rw [← h1]; exact h
    · rw [map_zero φ]; exact zero_mem _
  refine ⟨𝔮, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun p hp => hp.1)
    rw [eq_sum_mono _ p]
    exact Submodule.sum_mem _ fun μ _ =>
      Submodule.subset_span ⟨hmono μ _ _ rfl (hp μ), toDeg μ, mono_mem _ μ _ _⟩
  · intro p hp μ
    have : φ (AddMonoidAlgebra.coeff p.1 μ) = 0 := hp μ
    rw [this]; exact zero_mem _
  · intro b hb
    exact hmono 0 _ b.1 rfl (hsat.2 b.1 b.2 hb)
  · intro c hc p hp μ
    have h1 : φ (AddMonoidAlgebra.coeff (MvPolynomial.C (algebraMap O A c) * p.1) μ) ∈ _ := hp μ
    rw [MvPolynomial.coeff_C_mul, map_mul, AlgHom.commutes, ← Algebra.smul_def,
      ← algebraMap_smul (FractionRing O)] at h1
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      simpa using hc
    exact (Submodule.smul_mem_iff _ hc').1 h1
  · intro f g hf hg hfg
    refine hmono (Finsupp.single 0 1) _ (f ^ 2 - g ^ 2) ?_ ?_
    · rw [map_sub]; rfl
    · have h1 := hsat.1 _ (sub_mem hf hg) hfg
      have h2 := (fil_holds _ τ wt 0 0 _ _ (h0 (φ (f + g))) (h0 0)).2 _ (hφ.graded _ _ (add_mem hf hg))
      have h3 := hmul _ _ _ _ h1 h2
      rw [← map_mul] at h3
      have h4 : f ^ 2 - g ^ 2 = (f - g) * (f + g) := by ring
      rw [h4]
      simpa using h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FrobeniusInclusionXEqMulQ
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

noncomputable section

namespace UpperTheory.V.Alg.M.NumericalFunctions

private def sh : Multiplicative (ℤ × ℤ) →* Module.End ℤ (ℤ × ℤ → ℤ) where
  toFun v := LinearMap.funLeft ℤ ℤ (fun p => p - v.toAdd)
  map_one' := by ext f p; simp [LinearMap.funLeft]
  map_mul' v w := by
    refine LinearMap.ext fun f => funext fun p => ?_
    simp [LinearMap.funLeft, sub_sub]

private def φ : AddMonoidAlgebra ℤ (ℤ × ℤ) →ₐ[ℤ] Module.End ℤ (ℤ × ℤ → ℤ) :=
  AddMonoidAlgebra.lift ℤ _ _ sh

private def x (v : ℤ × ℤ) : AddMonoidAlgebra ℤ (ℤ × ℤ) := AddMonoidAlgebra.single v 1

private theorem x_add (v w : ℤ × ℤ) : x (v + w) = x v * x w := by
  simp [x, AddMonoidAlgebra.single_mul_single]

private theorem frobenius_inclusion_X_eq_mul_Q (v : ℤ × ℤ) (f : ℤ × ℤ → ℤ) (p : ℤ × ℤ) : φ (x v) f p = f (p - v) := by
  simp [φ, x, sh, LinearMap.funLeft]

private theorem φ_mul (a b : AddMonoidAlgebra ℤ (ℤ × ℤ)) (f : ℤ × ℤ → ℤ) : φ (a * b) f = φ a (φ b f) := by
  rw [map_mul]; rfl

private theorem φ_sub (v : ℤ × ℤ) (f : ℤ × ℤ → ℤ) (p : ℤ × ℤ) : φ (1 - x v) f p = f p - f (p - v) := by
  rw [map_sub, map_one, LinearMap.sub_apply, Pi.sub_apply, frobenius_inclusion_X_eq_mul_Q]; rfl

private theorem φ_add (v : ℤ × ℤ) (f : ℤ × ℤ → ℤ) (p : ℤ × ℤ) : φ (1 + x v) f p = f p + f (p - v) := by
  rw [map_add (f := _), map_one, LinearMap.add_apply, Pi.add_apply, frobenius_inclusion_X_eq_mul_Q]; rfl

private theorem one_sub_x_ne {v : ℤ × ℤ} (hv : v ≠ 0) : 1 - x v ≠ 0 := by
  intro h
  have := φ_sub v (fun q => if q = 0 then 1 else 0) 0
  simp [h, hv] at this

private theorem dif_eq {k : ℕ} (l : Deg k →+ ℤ × ℤ) (f : ℤ × ℤ → ℤ) (L : List (Deg k)) (d : Deg k) :
    dif L (fun d => f (l d)) d = φ (L.map fun v => 1 - x (l v)).prod f (l d) := by
  induction L generalizing d with
  | nil => simp [dif]
  | cons v L ih => rw [dif, List.map_cons, List.prod_cons, φ_mul, φ_sub, ih, ih, map_sub]

private theorem ev_sub {f : ℤ × ℤ → ℤ} {c : ℤ} (h : ∀ᶠ p in atTop, f p = c) (v : ℤ × ℤ) :
    ∀ᶠ p in atTop, f (p - v) = c := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 h
  exact eventually_atTop.2 ⟨a + v, fun p hp => ha _ (le_sub_iff_add_le.2 hp)⟩

private theorem eventually_const_of_shift {f : ℤ × ℤ → ℤ} {c : ℤ} (h : ∀ᶠ p in atTop, f p = c) (v : ℤ × ℤ) :
    ∀ᶠ p in atTop, φ (x v) f p = c := by
  simpa only [frobenius_inclusion_X_eq_mul_Q] using ev_sub h v

private theorem ev_pow {f : ℤ × ℤ → ℤ} {c : ℤ} (h : ∀ᶠ p in atTop, f p = c) (v : ℤ × ℤ) (n : ℕ) :
    ∀ᶠ p in atTop, φ ((1 + x v) ^ n) f p = 2 ^ n * c := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    filter_upwards [ih, ev_sub ih v] with p h1 h2
    rw [pow_succ', φ_mul, φ_add, h1, h2]; ring

private def mons {τ : Type} (w : τ → ℤ × ℤ) (S : Finset τ) (p : ℤ × ℤ) : Set (τ →₀ ℕ) :=
  {ν | (∀ j ∉ S, ν j = 0) ∧ Finsupp.weight w ν = p}

private def N {τ : Type} (w : τ → ℤ × ℤ) (S : Finset τ) (p : ℤ × ℤ) : ℤ := (mons w S p).ncard

private theorem N_insert {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) (hfin : ∀ S p, (mons w S p).Finite)
    (S : Finset τ) (i : τ) (hi : i ∉ S) : φ (1 - x (w i)) (N w (insert i S)) = N w S := by
  funext p
  have h : mons w (insert i S) p =
      mons w S p ∪ (fun ν => ν + Finsupp.single i 1) '' mons w (insert i S) (p - w i) := by
    ext ν
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h0 : ν i = 0
      · left
        refine ⟨fun j hj => ?_, h2⟩
        by_cases hji : j = i
        · rw [hji, h0]
        · exact h1 j (by simp [hj, hji])
      · right
        have e1 : ν - Finsupp.single i 1 + Finsupp.single i 1 = ν :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))
        refine ⟨ν - Finsupp.single i 1, ⟨fun j hj => by simp [h1 j hj], ?_⟩, e1⟩
        rw [← h2]
        conv_rhs => rw [← e1, map_add (f := _), Finsupp.weight_single, one_smul, add_sub_cancel_right]
    · rintro (⟨h1, h2⟩ | ⟨μ, ⟨h1, h2⟩, rfl⟩)
      · exact ⟨fun j hj => h1 j (fun h => hj (by simp [h])), h2⟩
      · refine ⟨fun j hj => ?_, by simp [map_add (f := _), Finsupp.weight_single, h2]⟩
        have : i ≠ j := by rintro rfl; simp at hj
        simp [h1 j hj, this]
  rw [φ_sub, N, N, N, h, Set.ncard_union_eq _ (hfin _ _) ((hfin _ _).image _),
    Set.ncard_image_of_injective _ (add_left_injective _)]
  · push_cast; ring
  · rw [Set.disjoint_left]
    rintro ν ⟨h1, -⟩ ⟨μ, -, rfl⟩
    simpa using h1 i hi

private theorem N_prod {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) (hfin : ∀ S p, (mons w S p).Finite)
    (T U : Finset τ) (h : Disjoint U T) : φ (∏ i ∈ U, (1 - x (w i))) (N w (U ∪ T)) = N w T := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    rw [Finset.disjoint_insert_left] at h
    rw [Finset.prod_insert hi, mul_comm, φ_mul, Finset.insert_union, N_insert w hfin _ _ (by simp [hi, h.1]), ih h.2]

private theorem weight_pair {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) {i j : τ} (hij : i ≠ j) (ν : τ →₀ ℕ)
    (h : ∀ k ∉ ({i, j} : Finset τ), ν k = 0) : Finsupp.weight w ν = ν i • w i + ν j • w j := by
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset (s := {i, j}), Finset.sum_pair hij]
  · intro k hk
    by_contra hk'
    exact Finsupp.mem_support_iff.1 hk (h k hk')
  · simp

private theorem N_one {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) {i j : τ} (hi : w i = (1, 0)) (hj : w j = (0, 1)) :
    ∀ᶠ p in atTop, N w {i, j} p = 1 := by
  have hij : i ≠ j := by rintro rfl; simp [hi] at hj
  filter_upwards [eventually_ge_atTop (0 : ℤ × ℤ)] with p hp
  obtain ⟨a, b⟩ := p
  obtain ⟨ha, hb⟩ : 0 ≤ a ∧ 0 ≤ b := hp
  lift a to ℕ using ha
  lift b to ℕ using hb
  have : mons w {i, j} (a, b) = {Finsupp.single i a + Finsupp.single j b} := by
    ext ν
    constructor
    · rintro ⟨h1, h2⟩
      rw [weight_pair w hij ν h1, hi, hj] at h2
      simp at h2
      ext k
      by_cases hki : k = i
      · simp [hki, hij, h2.1]
      by_cases hkj : k = j
      · simp [hkj, hij, h2.2]
      simp [h1 k (by simp [hki, hkj]), hki, hkj]
    · rintro rfl
      refine ⟨fun k hk => ?_, by simp [map_add (f := _), Finsupp.weight_single, hi, hj]⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [hk.1, hk.2]
  simp [N, this]

private theorem N_zero {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) {i j : τ} (hi : w i = (0, 1)) (hj : w j = (0, 2)) :
    ∀ᶠ p in atTop, N w {i, j} p = 0 := by
  have hij : i ≠ j := by rintro rfl; simp [hi] at hj
  filter_upwards [eventually_ge_atTop ((1, 1) : ℤ × ℤ)] with p hp
  have : mons w {i, j} p = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ν ⟨h1, h2⟩
    rw [weight_pair w hij ν h1, hi, hj] at h2
    have := hp.1
    rw [← h2] at this
    simp at this
  simp [N, this]

private theorem key {τ : Type} [Fintype τ] [DecidableEq τ] (w : τ → ℤ × ℤ) (hfin : ∀ S p, (mons w S p).Finite)
    (r s r' s' : ℕ) {i₀ i₁ i₂ : τ} (h₀ : w i₀ = (1, 0)) (h₁ : w i₁ = (0, 1)) (h₂ : w i₂ = (0, 2))
    (hP : ∏ i, (1 - x (w i)) =
      (1 - x (1, 0)) ^ (r + 1) * (1 - x (2, 0)) ^ s * (1 - x (0, 1)) ^ (r' + 1) * (1 - x (0, 2)) ^ (s' + 1)) :
    ∀ᶠ p in atTop, φ ((1 - x (2, 0)) ^ r * ((1 - x (2, 0)) ^ s * (1 - x (0, 2)) ^ r' * (1 - x (0, 2)) ^ s' *
      (1 - x (4, 2)))) (N w Finset.univ) p = 2 ^ (r + r') := by
  have h01 : i₀ ≠ i₁ := by rintro rfl; simp [h₀] at h₁
  have h12 : i₁ ≠ i₂ := by rintro rfl; simp [h₁] at h₂
  set C := (1 - x (1, 0)) ^ r * (1 - x (2, 0)) ^ s * (1 - x (0, 1)) ^ r' * (1 - x (0, 2)) ^ s' with hC
  have hT : ∀ T : Finset τ, φ (∏ i ∈ Tᶜ, (1 - x (w i))) (N w Finset.univ) = N w T := fun T => by
    rw [← N_prod w hfin T Tᶜ disjoint_compl_left, Finset.union_comm, Finset.union_compl]
  have nX : 1 - x (1, 0) ≠ 0 := one_sub_x_ne (by simp)
  have nY : 1 - x (0, 1) ≠ 0 := one_sub_x_ne (by simp)
  have nY2 : 1 - x (0, 2) ≠ 0 := one_sub_x_ne (by simp)
  have e1 : ∏ i ∈ ({i₀, i₁} : Finset τ)ᶜ, (1 - x (w i)) = C * (1 - x (0, 2)) := by
    apply mul_right_cancel₀ (mul_ne_zero nX nY)
    have := Finset.prod_compl_mul_prod ({i₀, i₁} : Finset τ) (fun i => 1 - x (w i))
    rw [Finset.prod_pair h01, h₀, h₁] at this
    rw [this, hP, hC]; ring
  have e2 : ∏ i ∈ ({i₁, i₂} : Finset τ)ᶜ, (1 - x (w i)) = C * (1 - x (1, 0)) := by
    apply mul_right_cancel₀ (mul_ne_zero nY nY2)
    have := Finset.prod_compl_mul_prod ({i₁, i₂} : Finset τ) (fun i => 1 - x (w i))
    rw [Finset.prod_pair h12, h₁, h₂] at this
    rw [this, hP, hC]; ring
  have hX2 : 1 - x (2, 0) = (1 + x (1, 0)) * (1 - x (1, 0)) := by
    rw [show ((2, 0) : ℤ × ℤ) = (1, 0) + (1, 0) from rfl, x_add]; ring
  have hY2 : 1 - x (0, 2) = (1 + x (0, 1)) * (1 - x (0, 1)) := by
    rw [show ((0, 2) : ℤ × ℤ) = (0, 1) + (0, 1) from rfl, x_add]; ring
  have h42 : 1 - x (4, 2) = (1 - x (0, 2)) + x (0, 2) * (1 + x (2, 0)) * ((1 + x (1, 0)) * (1 - x (1, 0))) := by
    rw [← hX2, show ((4, 2) : ℤ × ℤ) = (2, 0) + (2, 0) + (0, 2) from rfl, x_add, x_add]; ring
  have hop : (1 - x (2, 0)) ^ r * ((1 - x (2, 0)) ^ s * (1 - x (0, 2)) ^ r' * (1 - x (0, 2)) ^ s' * (1 - x (4, 2))) =
      (1 + x (1, 0)) ^ r * ((1 + x (0, 1)) ^ r' * (C * (1 - x (0, 2)) +
        x (0, 2) * ((1 + x (2, 0)) ^ 1 * ((1 + x (1, 0)) ^ 1 * (C * (1 - x (1, 0))))))) := by
    have a1 : (1 - x (2, 0)) ^ r = (1 + x (1, 0)) ^ r * (1 - x (1, 0)) ^ r := by rw [hX2, mul_pow]
    have a2 : (1 - x (0, 2)) ^ r' = (1 + x (0, 1)) ^ r' * (1 - x (0, 1)) ^ r' := by rw [hY2, mul_pow]
    rw [a1, a2, h42, hC]; ring
  rw [hop, φ_mul, φ_mul, pow_add, ← mul_one (2 ^ r')]
  refine ev_pow (ev_pow ?_ _ _) _ _
  rw [map_add (f := _), LinearMap.add_apply, ← e1, ← e2, φ_mul, φ_mul, φ_mul, hT, hT]
  filter_upwards [N_one w h₀ h₁, eventually_const_of_shift (ev_pow (ev_pow (N_zero w h₁ h₂) (1, 0) 1) (2, 0) 1) (0, 2)] with p a1 a2
  rw [Pi.add_apply, a1, a2]; simp

private def lam : Deg 3 →+ ℤ × ℤ where
  toFun d := (2 * d 0 + 4 * d 2, 2 * d 1 + 2 * d 2)
  map_zero' := by simp
  map_add' a b := by ext <;> simp <;> ring

end UpperTheory.V.Alg.M.NumericalFunctions

open UpperTheory.V.Alg.M.NumericalFunctions in
theorem UpperTheory.V.Alg.M.num_holds :
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (r s r' s' : ℕ), 1 ≤ r → (∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j) →
      ∀ᶠ d in atTop, dif (List.replicate (r - 1) (e 0) ++ (List.replicate s (e 0) ++ List.replicate r' (e 1) ++
          List.replicate s' (e 1) ++ [e 2])) (fun d : Deg 3 => cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2)) d = 2 ^ (r - 1 + r') := by
  intro τ _ wt r s r' s' hr hc
  classical
  obtain ⟨r, rfl⟩ : ∃ r₀, r = r₀ + 1 := ⟨r - 1, by omega⟩
  have hc' : ∀ j, (Finset.univ.filter fun i => wt i = j).card = mDims (r + 1) s r' s' 0 j := fun j => by
    rw [← hc j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hex : ∀ j, mDims (r + 1) s r' s' 0 j ≠ 0 → ∃ i, wt i = j := fun j hj => by
    rw [← hc'] at hj
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.1 hj
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  have hwt : ∀ i, wt i ∈ ({-1, -2, 1, 2} : Finset ℤ) := fun i => by
    by_contra h
    have : (Finset.univ.filter fun i' => wt i' = wt i).card ≠ 0 := Finset.card_ne_zero.2 ⟨i, by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    rw [hc'] at this
    simp [mDims, h] at this
  let w : τ → ℤ × ℤ := fun i => ((negW wt i : ℤ), (posW wt i : ℤ))
  have hw : ∀ ν : τ →₀ ℕ, Finsupp.weight w ν =
      (((Finsupp.weight (negW wt) ν : ℕ) : ℤ), ((Finsupp.weight (posW wt) ν : ℕ) : ℤ)) := fun ν => by
    induction ν using Finsupp.induction_linear with
    | zero => simp [Prod.ext_iff]
    | add a b ha hb => simp [map_add (f := _), ha, hb]
    | single i n => simp [Finsupp.weight_single, w]
  have hfin : ∀ S p, (mons w S p).Finite := fun S p => by
    refine (Finsupp.finite_of_nat_weight_le (fun i => negW wt i + posW wt i) (fun i => ?_)
      (p.1.toNat + p.2.toNat)).subset ?_
    · have := hwt i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      simp only [negW, posW]; omega
    · rintro ν ⟨-, rfl⟩
      have : Finsupp.weight (fun i => negW wt i + posW wt i) ν =
          Finsupp.weight (negW wt) ν + Finsupp.weight (posW wt) ν := by
        simp [Finsupp.weight_apply, Finsupp.sum, mul_add, Finset.sum_add_distrib]
      simp [hw, this]
  have hcnt : (fun d : Deg 3 => cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2)) =
      fun d => N w Finset.univ (lam d) := by
    funext d
    rw [cnt, N, ← Nat.card_coe_set_eq]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun ν => ?_)
    simp [mons, hw, lam]
  obtain ⟨i₀, h₀⟩ := hex (-1) (by simp [mDims])
  obtain ⟨i₁, h₁⟩ := hex 1 (by simp [mDims])
  obtain ⟨i₂, h₂⟩ := hex 2 (by simp [mDims])
  have hP : ∏ i, (1 - x (w i)) =
      (1 - x (1, 0)) ^ (r + 1) * (1 - x (2, 0)) ^ s * (1 - x (0, 1)) ^ (r' + 1) * (1 - x (0, 2)) ^ (s' + 1) := by
    rw [← Finset.prod_fiberwise_of_maps_to (fun i _ => hwt i)]
    have : ∀ j : ℤ, ∏ i ∈ Finset.univ.filter (fun i => wt i = j), (1 - x (w i)) =
        (1 - x (((-j).toNat : ℤ), (j.toNat : ℤ))) ^ mDims (r + 1) s r' s' 0 j := fun j => by
      rw [← hc', ← Finset.prod_const]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [← (Finset.mem_filter.1 hi).2]; rfl
    simp only [this]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
      mul_assoc, mul_assoc]
    rfl
  have hk := key w hfin r s r' s' (i₀ := i₀) (i₁ := i₁) (i₂ := i₂) (by simp [w, negW, posW, h₀])
    (by simp [w, negW, posW, h₁]) (by simp [w, negW, posW, h₂]) hP
  have l0 : lam (e 0) = (2, 0) := by simp [lam, e]
  have l1 : lam (e 1) = (0, 2) := by simp [lam, e]
  have l2 : lam (e 2) = (4, 2) := by simp [lam, e]
  obtain ⟨a, ha⟩ := eventually_atTop.1 hk
  filter_upwards [eventually_ge_atTop (fun _ => |a.1| + |a.2| : Deg 3)] with d hd
  rw [hcnt, dif_eq]
  simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, l0, l1, l2, Nat.add_sub_cancel]
  refine ha _ ?_
  have d0 : |a.1| + |a.2| ≤ d 0 := hd 0
  have d1 : |a.1| + |a.2| ≤ d 1 := hd 1
  have d2 : |a.1| + |a.2| ≤ d 2 := hd 2
  have := le_abs_self a.1
  have := le_abs_self a.2
  have := abs_nonneg a.1
  have := abs_nonneg a.2
  exact ⟨show a.1 ≤ 2 * d 0 + 4 * d 2 by linarith, show a.2 ≤ 2 * d 1 + 2 * d 2 by linarith⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LaDifPerm
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem la_dif_perm {k : ℕ} {l l' : List (Deg k)} (h : l.Perm l') (f : Deg k → ℤ) :
    ∀ m, dif l f m = dif l' f m := by
  induction h with
  | nil => intro m; rfl
  | cons a _ ih => intro m; simp only [dif, ih]
  | swap a b l =>
    intro m
    simp only [dif]
    rw [sub_right_comm m a b]
    ring
  | trans _ _ ih1 ih2 => intro m; rw [ih1, ih2]

private theorem la_hdiff {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (ts : List (Deg k × R)) (G : GMod B R k) :
    ∀ m, Sm.hdiff ts G m = dif (ts.map Prod.fst) (hilb G) m := by
  induction ts with
  | nil => intro m; rw [Sm.hdiff_nil]; rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro m
    rw [Sm.hdiff_cons, ih, ih]
    rfl

private theorem la_adm {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (d : Deg k) (a y : X.R)
    (ts : List (Deg k × X.R)) (h : admitted X.𝒜 ((d, a * y) :: ts) J) : admitted X.𝒜 ((d, y) :: ts) J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨e, he⟩
  rcases List.mem_cons.1 he with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, List.mem_cons_self⟩)
  · exact Ideal.subset_span ⟨e, List.mem_cons_of_mem _ h⟩

private theorem la_mem {k : ℕ} (X : HidaSetting k) (β : X.B) (c : ℕ) {d : Deg k} {y : X.R} (hy : y ∈ X.𝒜 d) :
    algebraMap X.B X.R β ^ c * y ∈ X.𝒜 d := by
  rw [← map_pow, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hy

private theorem la_peel {k : ℕ} (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) (β : X.B)
    (hβ : ∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0)
    (hA : admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann) (d : Deg k) (hd : 0 ≤ d) (y : X.R)
    (hy : y ∈ X.𝒜 d) (ts : List (Deg k × X.R)) (hV : Valid X.𝒜 ts) (c : ℕ) :
    admitted X.𝒜 ((d, algebraMap X.B X.R β ^ c * y) :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, algebraMap X.B X.R β ^ c * y) :: ts) F m =
      (c : ℤ) * dif (ts.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m + chi ((d, y) :: ts) F m := by
  have hb : algebraMap X.B X.R β ∈ X.𝒜 0 := by
    rw [X.std.zero]; exact ⟨β, rfl⟩
  have hs := ruleSmall k X ts _ hV ((ruleGr k X F hF).2.2 0 _ hb).1 hA
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro h
    rw [pow_succ', mul_assoc] at h ⊢
    have hV' : Valid X.𝒜 ((0, algebraMap X.B X.R β) :: (d, algebraMap X.B X.R β ^ c * y) :: ts) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨le_rfl, hb⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, la_mem X β c hy⟩
      · exact hV p hp
    filter_upwards [euler_rule_product_zero k X ts F d _ _ hV' hF h, ih (la_adm X _ d _ _ ts h), hs] with m h1 h2 h3
    have h4 : chi ts (F.quot (algebraMap X.B X.R β)) m = _ := h3.trans (la_hdiff ts _ m)
    rw [h1, h2, ruleNzd k X ts F 0 _ hβ m, h4]
    push_cast
    ring

theorem UpperTheory.V.Alg.M.la_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ β : X.B, (∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0) →
      admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann → ∀ (d : Deg k), 0 ≤ d → ∀ (n : ℕ) (y : Fin n → X.R) (c : Fin n → ℕ),
      (∀ i, y i ∈ X.𝒜 d) → ∀ us : List (Deg k × X.R), Valid X.𝒜 us →
      admitted X.𝒜 ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F.Ann →
      ∀ᶠ m in atTop, ((∑ i, c i : ℕ) : ℤ) * dif (List.replicate (n - 1) d ++ us.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m ≤
        chi ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F m := by
  intro k X F hF β hβ hA d hd n
  induction n with
  | zero =>
    intro y c _ us hV h
    simpa using rulePos k X us F hV hF (by simpa using h)
  | succ n ih =>
    intro y c hy us hV h
    rw [List.ofFn_succ, List.cons_append] at h ⊢
    set L := (List.ofFn fun i : Fin n => (d, algebraMap X.B X.R β ^ c i.succ * y i.succ)) with hL
    have hVL : Valid X.𝒜 (L ++ us) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact ⟨hd, la_mem X β _ (hy _)⟩
      · exact hV p hp
    have hc : ∀ l, Valid X.𝒜 l → Valid X.𝒜 ((d, y 0) :: l) := by
      intro l hl p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, hy 0⟩
      · exact hl p hp
    have hP : ((d, y 0) :: (L ++ us)).Perm (L ++ (d, y 0) :: us) := List.perm_middle.symm
    have h' := la_adm X _ d _ _ _ h
    have h'' : admitted X.𝒜 (L ++ (d, y 0) :: us) F.Ann := by
      unfold admitted at h' ⊢
      rwa [← E2.secs_perm hP]
    have hfst : (L ++ us).map Prod.fst = List.replicate n d ++ us.map Prod.fst := by
      rw [List.map_append, hL, List.map_ofFn]
      congr 1
      exact List.ofFn_const n d
    filter_upwards [la_peel X F hF β hβ hA d hd (y 0) (hy 0) _ hVL (c 0) h,
      euler_rule_two_of_graded_finite_iso ruleGr ruleFin ruleIso (euler_additivity_of_rules ruleGr ruleFin ruleIso) k X _ _ F (hc _ hVL) hP hF h',
      ih (fun i => y i.succ) (fun i => c i.succ) (fun i => hy _) _ (hc _ hV) h''] with m h1 h2 h3
    rw [h1, h2, hfst, Fin.sum_univ_succ, Nat.add_sub_cancel, Nat.cast_add, add_mul]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) h3)
    cases n with
    | zero => simp
    | succ n =>
      congr 1
      refine la_dif_perm ?_ _ m
      rw [Nat.add_sub_cancel, List.replicate_succ, List.map_cons, List.cons_append]
      exact List.perm_middle.symm
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (𝒜 : Deg k → Submodule B R)

private theorem self_isGr [GradedAlgebra 𝒜] : (GMod.self 𝒜).IsGr 𝒜 := by
  refine ⟨?_, DirectSum.Decomposition.isInternal 𝒜, Module.Finite.self R⟩
  exact fun ha hx => SetLike.mul_mem_graded (A := 𝒜) ha hx

private theorem mem_quo_ann_of_smul_mem {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F : GMod B R k)
    (N : Submodule R F.M) (x : R) (h : ∀ y : F.M, x • y ∈ N) : x ∈ (F.quo N).Ann := by
  rw [GMod.Ann, Module.mem_annihilator]
  intro m
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact (Submodule.Quotient.mk_smul _ x y).symm.trans ((Submodule.Quotient.mk_eq_zero _).mpr (h y))

private theorem le_ann_quo (J : Ideal R) : J ≤ ((GMod.self 𝒜).quo J).Ann := by
  intro x hx
  exact mem_quo_ann_of_smul_mem (GMod.self 𝒜) J x fun (y : R) => J.mul_mem_right y hx

private theorem mem_ann_quot (F : GMod B R k) (s : R) : s ∈ (F.quot s).Ann := by
  rw [GMod.Ann, Module.mem_annihilator]
  intro m
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact (Submodule.Quotient.mk_smul _ s y).symm.trans
    ((Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩)

private theorem secs_le_sup_secs_of_forall₂_sub_mem {k : ℕ} {R : Type} [CommRing R] {J' : Ideal R} :
    ∀ {ts ts' : List (Deg k × R)}, List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ J') ts ts' →
      secs ts ≤ J' ⊔ secs ts'
  | _, _, .nil => by simp [secs]
  | p :: l, q :: l', .cons hpq hl => by
    have ih := secs_le_sup_secs_of_forall₂_sub_mem hl
    have hsub : secs l' ≤ secs (q :: l') :=
      Ideal.span_mono fun s ⟨d, hd⟩ => ⟨d, List.mem_cons_of_mem _ hd⟩
    have hq : q.2 ∈ secs (q :: l') := Ideal.subset_span ⟨q.1, List.mem_cons_self ..⟩
    rw [secs, Ideal.span_le]
    rintro s ⟨d, hd⟩
    rcases List.mem_cons.mp hd with h | h
    · subst h
      have hs : s = (s - q.2) + q.2 := by ring
      rw [hs]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hpq.2) (Ideal.mem_sup_right hq)
    · exact sup_le_sup_left hsub _ (ih (Ideal.subset_span ⟨d, h⟩))

private theorem admissible_mono_ideal [IsLocalRing B] {ts ts' : List (Deg k × R)} {J J' : Ideal R} (h : admitted 𝒜 ts J) (hJ : J ≤ J')
    (ht : List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ J') ts ts') : admitted 𝒜 ts' J' := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hN.trans (sup_le (hJ.trans le_sup_left) (secs_le_sup_secs_of_forall₂_sub_mem ht))⟩

end

private theorem exists_surjective_graded_quot_to_quo {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F0 : GMod B R k)
    (J Q : Submodule R F0.M) (hle : J ≤ Q) (a : R) (haQ : ∀ x : F0.M, a • x ∈ Q) (hQ : F0.IsHomSub Q) :
    ∃ g : ((F0.quo J).quot a).M →ₗ[R] (F0.quo Q).M, Function.Surjective g ∧
      (∀ m, (F0.quo Q).gr m = Submodule.map (g.restrictScalars B) (((F0.quo J).quot a).gr m)) ∧
      ((F0.quo J).quot a).IsHomSub (LinearMap.ker g) := by
  let g1 : (F0.quo J).M →ₗ[R] (F0.quo Q).M := Submodule.factor hle
  let N : Submodule R (F0.quo J).M := (LinearMap.lsmul R (F0.quo J).M a).range
  have hN : N ≤ LinearMap.ker g1 := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J y
    have h0 : (Submodule.Quotient.mk (a • x) : F0.M ⧸ Q) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr (haQ x)
    exact h0
  let g : ((F0.quo J).quot a).M →ₗ[R] (F0.quo Q).M := N.liftQ g1 hN
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Q z
    exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x), rfl⟩
  · intro m
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x), ⟨Submodule.Quotient.mk x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨v, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  · unfold GMod.IsHomSub
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have hz' : (Submodule.Quotient.mk x : F0.M ⧸ Q) = 0 := hz
      have hxQ : x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hz'
      let π : F0.M →ₗ[R] ((F0.quo J).quot a).M := N.mkQ ∘ₗ J.mkQ
      have hS : Q ≤ Submodule.comap π
          (Submodule.span R {x | x ∈ LinearMap.ker g ∧ ∃ m, x ∈ ((F0.quo J).quot a).gr m}) := by
        refine (le_of_eq hQ).trans ?_
        rw [Submodule.span_le]
        rintro s ⟨hsQ, m, hsm⟩
        show π s ∈ Submodule.span R _
        apply Submodule.subset_span
        have hs0 : (Submodule.Quotient.mk s : F0.M ⧸ Q) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hsQ
        exact ⟨hs0, m, ⟨Submodule.Quotient.mk s, ⟨s, hsm, rfl⟩, rfl⟩⟩
      exact hS hxQ
    · exact Submodule.span_le.mpr fun x hx => hx.1

private theorem mono_quo {k : ℕ} (X : HidaSetting k) (J 𝔮 : Ideal X.R) (hJ : (GMod.self X.𝒜).IsHomSub J)
    (h𝔮 : (GMod.self X.𝒜).IsHomSub 𝔮) (hle : J ≤ 𝔮) (a : X.R) (ha0 : a ∈ X.𝒜 0) (ha : a ∈ 𝔮)
    (ts : List (Deg k × X.R)) (hts : Valid X.𝒜 ts) (hadm : admitted X.𝒜 ts (J ⊔ Ideal.span {a})) :
    ∀ᶠ m in atTop, chi ts ((GMod.self X.𝒜).quo 𝔮) m ≤ chi ts (((GMod.self X.𝒜).quo J).quot a) m := by
  obtain ⟨g, hgs, hgr, hker⟩ :=
    exists_surjective_graded_quot_to_quo (GMod.self X.𝒜) J 𝔮 hle a (fun (x : X.R) => 𝔮.mul_mem_right x ha) h𝔮
  have hS := self_isGr X.𝒜
  have hFJ := quo_isGr X.𝒜 hS hJ
  have hF := ((ruleGr k X ((GMod.self X.𝒜).quo J) hFJ).2.2 0 a ha0).1
  have hF'' := quo_isGr X.𝒜 hS h𝔮
  have hF' := ((ruleGr k X _ hF).1 (LinearMap.ker g) hker).1
  have ses : SES ((((GMod.self X.𝒜).quo J).quot a).sub (LinearMap.ker g))
      (((GMod.self X.𝒜).quo J).quot a) ((GMod.self X.𝒜).quo 𝔮) :=
    ⟨(LinearMap.ker g).subtype, g, Submodule.injective_subtype _, hgs, LinearMap.exact_subtype_ker_map g,
      fun m => rfl, hgr⟩
  have hann : J ⊔ Ideal.span {a} ≤ (((GMod.self X.𝒜).quo J).quot a).Ann :=
    sup_le ((le_ann_quo X.𝒜 J).trans (Cong.ann_le_quot _ a))
      ((Ideal.span_singleton_le_iff_mem _).mpr (mem_ann_quot _ a))
  have hadm' := admissible_mono_ideal X.𝒜 hadm hann (List.forall₂_same.mpr fun p _ => ⟨rfl, by simp⟩)
  exact ruleMono k X ts _ _ _ hts hF' hF hF'' ses hadm'

private theorem coef_hom {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)
    (J : Ideal A) : (GMod.self (reesGr N)).IsHomSub (coefIdeal N J) := by
  classical
  refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun w hw => hw.1)
  rw [eq_sum_mono N p]
  refine Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨fun n => ?_, _, mono_mem N m _ _⟩
  show AddMonoidAlgebra.coeff (MvPolynomial.monomial m _) n ∈ J
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hp m
  · exact zero_mem _

private theorem e_nn {k : ℕ} (i : Fin k) : 0 ≤ e i := by
  intro j
  simp only [e, Pi.zero_apply]
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Pi.single_apply, h]

private theorem dif_congr {k : ℕ} (h h' : Deg k → ℤ) (hh : ∀ᶠ d in atTop, h d = h' d) (L : List (Deg k)) :
    ∀ᶠ d in atTop, dif L h d = dif L h' d := by
  induction L with
  | nil =>
    filter_upwards [hh] with d hd
    rw [dif.eq_1, dif.eq_1, hd]
  | cons a ds ih =>
    have ht : Tendsto (fun d : Deg k => d - a) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + a, fun d hd => le_sub_iff_add_le.mpr hd⟩
    filter_upwards [ih, ht.eventually ih] with d h1 h2
    rw [dif.eq_2, dif.eq_2, h1, h2]

private theorem sec_congr' {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (i : Fin k) {f f' : A} (h : f ∈ N i) (h' : f' ∈ N i) (hff : f = f') :
    sec N i f h = sec N i f' h' := by
  subst hff
  rfl

private theorem sec_smul_eq_algebraMap_mul_sec {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (i : Fin k) (b : B) (f : A) (hf : f ∈ N i) (hbf : b • f ∈ N i) :
    sec N i (b • f) hbf = algebraMap B (rees N) b * sec N i f hf := by
  apply Subtype.ext
  show MvPolynomial.monomial _ (b • f) = algebraMap B (MvPolynomial (Fin k) A) b * MvPolynomial.monomial _ f
  rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_mul_monomial, Algebra.smul_def]

private theorem quo_smul_eq_zero_imp_eq_zero_of_regular {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (F : GMod B R k)
    (N : Submodule R F.M) (t : R) (h : ∀ y : F.M, t • y ∈ N → y ∈ N) :
    ∀ z : (F.quo N).M, t • z = 0 → z = 0 := by
  intro z hz
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hz' : (Submodule.Quotient.mk (t • y) : F.M ⧸ N) = 0 := hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr (h y ((Submodule.Quotient.mk_eq_zero _).mp hz'))

private theorem list_forall₂_ofFn {α β : Type} {R : α → β → Prop} :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, R (f i) (g i)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, f, g, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (list_forall₂_ofFn _ _ fun i => h i.succ)

theorem UpperTheory.V.Alg.M.low_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ r → (∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j) → ∀ ϖ : O, Irreducible ϖ →
    ∀ (y : Fin r → A) (c : Fin r → ℕ), (∀ i, y i ∈ 𝒜 (-1) ∧ Q.F i.castSucc - ϖ ^ c i • y i ∈ satSq x) → Q.F (Fin.last r) ∈ satSq x →
    ∀ a : 𝒜 0, x a = 0 →
      admitted (mGr Q) (ts Q) (coefIdeal _ (RingHom.ker φ) ⊔ Ideal.span {algebraMap (𝒜 0) (mR Q) a}) →
      ∀ᶠ d in atTop, ((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') ≤
        chi (ts Q) ((mQ Q (coefIdeal _ (RingHom.ker φ))).quot (algebraMap (𝒜 0) (mR Q) a)) d := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hr hdim ϖ hϖ y c hy hlast a ha hadm
  classical
  have hfg : ∀ i, (mN 𝒜 (Q.F (Fin.last r)) i).FG := by
    intro i
    fin_cases i
    · exact fg_holds O A 𝒜 x hW (-2)
    · exact fg_holds O A 𝒜 x hW 2
    · exact (Submodule.fg_span_singleton _).sup
        (((fg_holds O A 𝒜 x hW (-2)).mul (fg_holds O A 𝒜 x hW (-2))).mul (fg_holds O A 𝒜 x hW 2))
  let X : HidaSetting 3 := HidaSetting.mk (𝒜 0) (mR Q) (mGr Q) (std_holds (𝒜 0) A 3 _ hfg)
  obtain ⟨𝔮, h𝔮lead, h𝔮hom, hJ𝔮, h𝔮x, h𝔮reg, h𝔮sq⟩ := lk_holds O A 𝒜 x hW r s r' s' m Q τ wt φ hφ hlast
  have hF : GMod.IsGr (mGr Q) ((GMod.self (mGr Q)).quo 𝔮) := quo_isGr (mGr Q) (self_isGr (mGr Q)) h𝔮hom
  have ha0 : algebraMap (𝒜 0) (mR Q) a ∈ mGr Q 0 := SetLike.algebraMap_mem_graded _ _
  have haq : algebraMap (𝒜 0) (mR Q) a ∈ 𝔮 := h𝔮x a ha
  have hvalR : Valid (mGr Q) (tsR Q) := by
    intro p hp
    simp only [tsR, List.mem_append, List.mem_ofFn, List.mem_singleton] at hp
    rcases hp with ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl
    · exact ⟨e_nn _, sec_mem _ _ _ (Q.hG i)⟩
    · exact ⟨e_nn _, sec_mem _ _ _ (sq_mem_pos 𝒜 (Q.hE i))⟩
    · exact ⟨e_nn _, sec_mem _ _ _ (Q.hE' i)⟩
    · exact ⟨e_nn _, sec_mem _ _ _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))⟩
  have hvalF : Valid (mGr Q) (tsF Q) := by
    intro p hp
    simp only [tsF, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact ⟨e_nn _, sec_mem _ _ _ (sq_mem_neg 𝒜 (Q.hF _))⟩
  have hval : Valid (mGr Q) (ts Q) := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hvalF p h
    · exact hvalR p h
  have hup := mono_quo X (coefIdeal _ (RingHom.ker φ)) 𝔮 (coef_hom _ _) h𝔮hom hJ𝔮 _ ha0 haq (ts Q) hval hadm
  have hy2 : ∀ i, y i ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 0 := fun i => sq_mem_neg 𝒜 (hy i).1
  have hreg := quo_smul_eq_zero_imp_eq_zero_of_regular (GMod.self (mGr Q)) 𝔮 (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))
    (fun (p : mR Q) hp => h𝔮reg ϖ hϖ.ne_zero p hp)
  have hadm0 : admitted (mGr Q) []
      (((GMod.self (mGr Q)).quo 𝔮).quot (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))).Ann := by
    refine ⟨1, ?_⟩
    rw [pow_one]
    refine le_trans Ideal.mul_le_left (le_trans ?_ le_sup_left)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap]
    have hxb : res0 𝒜 x b ∈ maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have hm : b * algebraMap O (𝒜 0) v ∈ maximalIdeal (𝒜 0) := Ideal.mul_mem_right _ _ hb
      have h1 : IsUnit (1 - b * algebraMap O (𝒜 0) v) := by
        by_contra hn
        have hn' : 1 - b * algebraMap O (𝒜 0) v ∈ maximalIdeal (𝒜 0) := (IsLocalRing.mem_maximalIdeal _).mpr hn
        have h1m := Ideal.add_mem _ hn' hm
        rw [sub_add_cancel] at h1m
        exact (maximalIdeal.isMaximal (𝒜 0)).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
      have h2 := h1.map (res0 𝒜 x)
      rw [map_sub, map_one, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply, hv, sub_self] at h2
      exact not_isUnit_zero h2
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp
      (((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ) ▸ hxb)
    have hc : x ↑(b - algebraMap O (𝒜 0) (res0 𝒜 x b)) = 0 := by
      change res0 𝒜 x (b - algebraMap O (𝒜 0) (res0 𝒜 x b)) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have hcq := h𝔮x _ hc
    have hb' : algebraMap (𝒜 0) (mR Q) b = algebraMap (𝒜 0) (mR Q) (b - algebraMap O (𝒜 0) (res0 𝒜 x b)) +
        algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ) * algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) u) := by
      rw [← hu, map_sub, map_mul, map_mul]
      ring
    rw [hb']
    refine Ideal.add_mem _ ((Cong.ann_le_quot _ _) (le_ann_quo (mGr Q) 𝔮 hcq)) ?_
    exact Ideal.mul_mem_right _ _ (mem_ann_quot _ _)
  have hkey : ∀ i : Fin r, ∀ h : (ϖ ^ c i • y i) ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 0,
      sec (mN 𝒜 (Q.F (Fin.last r))) 0 ((ϖ ^ c i • y i) ^ 2) h =
        algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) *
          sec (mN 𝒜 (Q.F (Fin.last r))) 0 (y i ^ 2) (hy2 i) := by
    intro i h
    have hs : (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) • y i ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 0 :=
      Submodule.smul_mem _ _ (hy2 i)
    have heq : ((ϖ ^ c i • y i) ^ 2 : A) = (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) • y i ^ 2 := by
      rw [smul_pow, ← map_pow, algebraMap_smul, ← pow_mul, mul_comm (c i) 2]
    rw [sec_congr' _ 0 h hs heq, sec_smul_eq_algebraMap_mul_sec _ 0 _ _ (hy2 i) hs, map_pow]
  have hrel : List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ ((GMod.self (mGr Q)).quo 𝔮).Ann) (ts Q)
      (List.ofFn (fun i => (e 0, algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ) ^ (2 * c i) *
        sec (mN 𝒜 (Q.F (Fin.last r))) 0 (y i ^ 2) (hy2 i))) ++ tsR Q) := by
    refine List.rel_append ?_ (List.forall₂_same.mpr fun p _ => ⟨rfl, by simp⟩)
    refine list_forall₂_ofFn _ _ fun i => ⟨rfl, ?_⟩
    have hg : ϖ ^ c i • y i ∈ 𝒜 (-1) := Submodule.smul_mem _ _ (hy i).1
    have h := h𝔮sq (Q.F i.castSucc) (ϖ ^ c i • y i) (Q.hF _) hg (hy i).2
    have h' := hkey i (sq_mem_neg 𝒜 hg)
    refine le_ann_quo (mGr Q) 𝔮 ?_
    convert h using 2
    exact h'.symm
  have hJa : coefIdeal _ (RingHom.ker φ) ⊔ Ideal.span {algebraMap (𝒜 0) (mR Q) a} ≤
      ((GMod.self (mGr Q)).quo 𝔮).Ann :=
    sup_le (hJ𝔮.trans (le_ann_quo (mGr Q) 𝔮))
      ((Ideal.span_singleton_le_iff_mem _).mpr (le_ann_quo (mGr Q) 𝔮 haq))
  have hadmF := admissible_mono_ideal (mGr Q) hadm hJa hrel
  have hla := la_holds 3 X ((GMod.self (mGr Q)).quo 𝔮) hF (algebraMap O (𝒜 0) ϖ) hreg hadm0 (e 0) (e_nn 0) r
    (fun i => sec (mN 𝒜 (Q.F (Fin.last r))) 0 (y i ^ 2) (hy2 i)) (fun i => 2 * c i)
    (fun i => sec_mem _ _ _ _) (tsR Q) hvalR hadmF
  have hhilb : ∀ᶠ d in atTop, hilb (((GMod.self (mGr Q)).quo 𝔮).quot
      (algebraMap (𝒜 0) (mR Q) (algebraMap O (𝒜 0) ϖ))) d = cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2) := by
    filter_upwards [eventually_ge_atTop 0] with d hd
    exact hf_holds O A 𝒜 x hW r s r' s' m Q τ wt φ hφ hlast 𝔮 h𝔮lead ϖ hϖ d hd
  have hdif := dif_congr _ _ hhilb (List.replicate (r - 1) (e 0) ++ List.map Prod.fst (tsR Q))
  have hnum := num_holds τ wt r s r' s' hr hdim
  have hmap : List.map Prod.fst (tsR Q) =
      List.replicate s (e 0) ++ List.replicate r' (e 1) ++ List.replicate s' (e 1) ++ [e 2] := by
    simp [tsR, List.map_ofFn, Function.comp_def, List.ofFn_const]
    rw [← List.append_assoc, List.replicate_append_replicate]
  have hchi := Cong.chi_cong ((GMod.self (mGr Q)).quo 𝔮) hrel
  have harith : ((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') = ((∑ i, 2 * c i : ℕ) : ℤ) * 2 ^ (r - 1 + r') := by
    have hr' : r + r' = (r - 1 + r') + 1 := by omega
    rw [hr', pow_succ, ← Finset.mul_sum]
    push_cast
    ring
  filter_upwards [hup, hla, hdif, hnum] with d h1 h2 h3 h4
  rw [h3, hmap, h4, ← hchi] at h2
  calc ((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') = ((∑ i, 2 * c i : ℕ) : ℤ) * 2 ^ (r - 1 + r') := harith
    _ ≤ chi (ts Q) ((GMod.self (mGr Q)).quo 𝔮) d := h2
    _ ≤ _ := h1

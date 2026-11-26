module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobOfShapiroSystem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA.TameLim

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  have hi : IsIntegral ℤ_[l] x := by
    have h := (isIntegral_algHom_iff (c.O.val.restrictScalars ℤ_[l]) Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : c.O))
    simpa using h
  have hq : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem inv_pow_mem (c : Coef l) (e k : ℕ) (h : k = 0 ∨ ¬ l ∣ k) : (((k : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases h with rfl | h
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using c.O.one_mem
    · simpa [zero_pow he.ne'] using c.O.zero_mem
  · have hk : IsUnit ((k : ℤ_[l])) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_def]
      push_cast
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h
    obtain ⟨u, hu⟩ := hk.pow e
    have e1 : (((k : ℕ) : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [e1]
    exact c.O.algebraMap_mem _

theorem val_unit (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (x : ZMod (l ^ r)).val = 0 ∨ ¬ l ∣ (x : ZMod (l ^ r)).val := by
  have hp : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · left
    haveI : NeZero (l ^ 0) := ⟨by simp⟩
    have := ZMod.val_lt (x : ZMod (l ^ 0))
    exact Nat.lt_one_iff.mp (lt_of_lt_of_eq this (pow_zero l))
  · right
    intro hd
    have hc := ZMod.val_coe_unit_coprime x
    have h2 : l ∣ Nat.gcd (x : ZMod (l ^ r)).val (l ^ r) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem mul_sub_mul_le (a a' u u' : Qbar l) (C : ℝ) (ha' : ‖a'‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (h1 : ‖a' - a‖ ≤ C) (h2 : ‖u' - u‖ ≤ C) : ‖a' * u' - a * u‖ ≤ C := by
  have e : a' * u' - a * u = a' * (u' - u) + (a' - a) * u := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ha').trans h2
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans h1

end GlobalTheory.KA.TameLim

namespace GlobalTheory.KA.TameLim

theorem core (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ)
    (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l)
    (hWO : ∀ s i j, mat W s i j ∈ c.O) (hWρ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hρO : ∀ s i j, ρ s i j ∈ c.O) (hηO : ∀ r x, η r x ∈ c.O)
    (hηc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hηa : ∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hSh : ∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r))
    (hcont : ∀ r x i, Continuous fun s => Yw r s x i)
    (hYO : ∀ r s x i, Yw r s x i ∈ c.O)
    (hnc : ∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s)
    (hb : ∀ r i, b r i ∈ c.O)
    (hrel : ∀ r s i, ‖(∑ a, spec (η r) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧
      (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧
      (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧
      ∀ r s x i, ‖Y s x i - spec (η r) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hq := GlobalTheory.norm_natCast_prime_qbar l
  have hC : ∀ r : ℕ, (0 : ℝ) ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun r => norm_nonneg _
  have ht0 : Filter.Tendsto (fun r : ℕ => ‖((l : ℕ) : Qbar l) ^ r‖) Filter.atTop (nhds 0) := by
    simp only [norm_pow]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq
  have hzero : ∀ z : Qbar l, (∀ r, ‖z‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → z = 0 := fun z hz =>
    norm_le_zero_iff.mp (ge_of_tendsto' ht0 hz)
  have n1 : ∀ {x : Qbar l}, x ∈ c.O → ‖x‖ ≤ 1 := fun hx => norm_le_one_of_mem c hx
  have hMle : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => n1 (hWO s i j)
  have hρle : ∀ s i j, ‖ρ s i j‖ ≤ 1 := fun s i j => n1 (hρO s i j)

  set Yr : ℕ → G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l :=
    fun r s a => spec (η r) (fun s x => Yw r s (a, x)) s with hYr
  have hYr_apply : ∀ r s a i, Yr r s a i = ∑ x, η r x * Yw r s (a, x) i := by
    intro r s a i; simp only [hYr, spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hYrO : ∀ r s a i, Yr r s a i ∈ c.O := by
    intro r s a i; rw [hYr_apply]
    exact Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (hηO r x) (hYO r s (a, x) i)

  have hslice : ∀ a r s, (fun x => Yw r s (a, x)) = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (fun s x' => Yw (r + 1) s (a, x')) s := by
    intro a r s; funext x
    rw [hnc r s]
    simp only [push]
    refine Finset.sum_nbij' (fun p => p.2) (fun x' => (a, x')) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq] at hp ⊢; exact hp.2
    · intro x' hx'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hx' ⊢; first | exact hx' | exact ⟨rfl, hx'⟩
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hp
      exact Prod.ext hp.1.symm rfl
    · intro x' _; rfl
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hp
      rw [← hp.1]
  have hstep : ∀ r s a i, ‖Yr (r + 1) s a i - Yr r s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s a i
    exact spec_cauchy l (fun r s x => Yw r s (a, x)) η (fun r s x i => n1 (hYO r s (a, x) i))
      (fun r x => n1 (hηO r x)) (fun r s => hslice a r s) hηc r s i
  have hlim : ∀ s a i, ∃ v ∈ c.O, ∀ r, ‖v - Yr r s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    fun s a i => GlobalTheory.coef_limit l c (fun r => Yr r s a i) (fun r => hYrO r s a i) (fun r => hstep r s a i)
  choose Y hYO' hYap using hlim

  have happ : ∀ r s t a i, ‖Yr r (s * t) a i - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) i‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s t a i
    have key : Yr r (s * t) a - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) =
        ρ s *ᵥ ∑ x, (η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)) • Yw r t (a * ψ s, x) := by
      have h1 : Yr r (s * t) a = Yr r s a +
          ρ s *ᵥ ∑ x, η r x • Yw r t (a * ψ s, x * (cycMod ℚ Ω l r s)⁻¹) := by
        simp only [hYr, spec, hSh r s t, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul,
          Prod.mk_mul_mk, MonoidHom.prod_apply, MonoidHom.inv_apply]
      have hre : ∑ x, η r x • Yw r t (a * ψ s, x * (cycMod ℚ Ω l r s)⁻¹) =
          ∑ x, η r (x * cycMod ℚ Ω l r s) • Yw r t (a * ψ s, x) :=
        Fintype.sum_equiv (Equiv.mulRight (cycMod ℚ Ω l r s)⁻¹) _ _ (fun x => by simp)
      rw [h1, hre, hWρ s]
      simp only [hYr, spec]
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul, add_sub_add_left_eq_sub, ← Matrix.mulVec_sub]
      congr 1
      simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, mul_comm (θ s : Qbar l)]
    rw [← Pi.sub_apply, key]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
    intro j _
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hρle s i j)) ?_
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
    intro x _
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (n1 (hYO r t _ j))) (hηa r s x)

  have hcoc : ShCoc (mat W) ψ Y := by
    intro s t a
    funext i
    rw [← sub_eq_zero]
    apply hzero
    intro r
    have e : Y (s * t) a i - (Y s a + mat W s *ᵥ Y t (a * ψ s)) i =
        (Y (s * t) a i - Yr r (s * t) a i) + (Yr r (s * t) a i - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) i)
          + (Yr r s a i - Y s a i) + (mat W s *ᵥ (Yr r t (a * ψ s) - Y t (a * ψ s))) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]; ring
    rw [e]
    have hM : ‖(mat W s *ᵥ (Yr r t (a * ψ s) - Y t (a * ψ s))) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
      intro j _
      rw [norm_mul, norm_sub_rev]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hMle s i j)) (hYap t (a * ψ s) j r)
    have h3 : ‖Yr r s a i - Y s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      rw [norm_sub_rev]; exact hYap s a i r
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hYap _ _ _ r) (happ r s t a i))) h3)) hM)

  have hcontY : ∀ x i, Continuous fun s => Y s x i := by
    intro x i
    have hu : TendstoUniformly (fun r s => Yr r s x i) (fun s => Y s x i) Filter.atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [ht0.eventually (gt_mem_nhds hε)] with r hr s
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hYap s x i r) hr
    refine hu.continuous (Filter.Frequently.of_forall fun r => ?_)
    simp only [hYr_apply]
    exact continuous_finsetSum _ fun x' _ => continuous_const.mul (hcont r (x, x') i)

  obtain ⟨b', hb'K, φ, hφ, hφt⟩ := (isCompact_univ_pi (fun _ : Fin 2 => GlobalTheory.Coef.isCompact_O l c)).tendsto_subseq
    (x := b) (fun r => Set.mem_univ_pi.mpr (hb r))
  have hb'O : ∀ i, b' i ∈ c.O := fun i => Set.mem_univ_pi.mp hb'K i
  have hsum : ∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b') := by
    intro s; funext i
    have hφ0 : Filter.Tendsto (fun k => ‖((l : ℕ) : Qbar l) ^ φ k‖) Filter.atTop (nhds 0) :=
      ht0.comp hφ.tendsto_atTop
    have h1 : Filter.Tendsto (fun k => (∑ x, Yr (φ k) s x) i) Filter.atTop (nhds ((∑ x, Y s x) i)) := by
      simp only [Finset.sum_apply]
      refine tendsto_finsetSum _ fun x _ => ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hφ0
      rw [norm_sub_rev]; exact hYap s x i (φ k)
    have hg : Continuous fun v : Fin 2 → Qbar l => (P • y s + (mat W s *ᵥ v - v)) i := by
      fun_prop
    have h2 : Filter.Tendsto (fun k => (P • y s + (mat W s *ᵥ b (φ k) - b (φ k))) i) Filter.atTop
        (nhds ((P • y s + (mat W s *ᵥ b' - b')) i)) :=
      (hg.tendsto b').comp hφt
    have h3 : Filter.Tendsto (fun k => (∑ x, Yr (φ k) s x) i - (P • y s + (mat W s *ᵥ b (φ k) - b (φ k))) i)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hrel (φ k) s i) hφ0
    exact sub_eq_zero.mp (tendsto_nhds_unique (h1.sub h2) h3)
  exact ⟨Y, b', hcoc, hcontY, hYO', hb'O, hsum, fun r s x i => hYap s x i r⟩

end GlobalTheory.KA.TameLim

namespace GlobalTheory.KA

theorem tame_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (e n : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) → (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) → P ∈ c.O → (∀ r i, b r i ∈ c.O) → (∀ s i, y s i ∈ c.O) → (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧ (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧ (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧ ∀ r s x i, ‖Y s x i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Ω _ _ W c e n χ θ ρ ψ Yw y P b hWO hWρ hρO hχO hχc hηa hSh hcont hYO hnc _ hb _ hrel
  refine TameLim.core l Ω W c n (fun r x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) θ ρ ψ Yw y P b
    hWO hWρ hρO (fun r x => Subalgebra.mul_mem _ (TameLim.inv_pow_mem c e _ (TameLim.val_unit r x)) (hχO r x))
    (fun r x => ?_) hηa hSh hcont hYO hnc hb hrel
  exact TameLim.mul_sub_mul_le _ _ _ _ _
    (TameLim.norm_le_one_of_mem c (TameLim.inv_pow_mem c e _ (TameLim.val_unit (r + 1) x)))
    (TameLim.norm_le_one_of_mem c (hχO r _)) (GlobalTheory.PowCong.powCong l e r x).1 (hχc r x)

end GlobalTheory.KA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystemStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameClass_limit_of_normCompatible_shapiroSystem : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (e n : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) → (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) → P ∈ c.O → (∀ r i, b r i ∈ c.O) → (∀ s i, y s i ∈ c.O) → (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧ (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧ (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧ ∀ r s x i, ‖Y s x i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  first | exact @GlobalTheory.KA.tame_limit | exact GlobalTheory.KA.tame_limit | (intros; apply GlobalTheory.KA.tame_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsPlaceOverRat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem exists_isPlaceOver_rat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl),
      ∃ B : ValuationSubring Ω, IsPlaceOver B q := by
  intro Ω _ _ _ q
  exact ReciprocityTheory.Gal.exists_isPlaceOver Ω q

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RatUnramToIntUnram
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory


open Polynomial in
theorem coefO_dvd_pow_l {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O)
    (h0 : x ≠ 0) : ∃ k : ℕ, ∃ u ∈ c.O, x * u = ((l : ℕ) : Qbar l) ^ k := by
  haveI := c.fin
  haveI := c.dvr
  set x' : c.O := ⟨x, hx⟩
  have hx0 : x' ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hint : IsIntegral ℤ_[l] x' := Algebra.IsIntegral.isIntegral x'
  obtain ⟨p, hpm, hp⟩ := hint
  rw [← aeval_def] at hp
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  rw [X_dvd_iff] at hq
  have hqx : aeval x' q = 0 := by
    rw [hpq, map_mul, map_pow, aeval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hx0)
  obtain ⟨r, hr⟩ := (X_dvd_sub_C : X ∣ q - C (q.coeff 0))
  have hrel : algebraMap ℤ_[l] c.O (q.coeff 0) = x' * (-(aeval x' r)) := by
    have := congrArg (aeval x') hr
    rw [map_sub, aeval_C, map_mul, aeval_X, hqx] at this
    linear_combination -this
  set a := q.coeff 0 with ha
  set w : ℤ_[l]ˣ := PadicInt.unitCoeff hq
  have hspec : a = (w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation := PadicInt.unitCoeff_spec hq
  have haw : a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (l : ℤ_[l]) ^ a.valuation := by
    calc a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
        = ((w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation) * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by rw [← hspec]
      _ = (l : ℤ_[l]) ^ a.valuation := by
        rw [mul_comm, ← mul_assoc]; simp
  refine ⟨a.valuation, (((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : c.O) : Qbar l),
    Subtype.property _, ?_⟩
  have h2 : x' * ((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]))
      = algebraMap ℤ_[l] c.O ((l : ℤ_[l]) ^ a.valuation) := by
    rw [← mul_assoc, ← hrel, ← map_mul, haw]
  have h3 := congrArg Subtype.val h2
  simpa using h3

end GlobalTheory

namespace GlobalTheory

theorem rat_unram_to_int_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∃ m : ℕ, ∀ (Y : G ℚ Ω → Fin 2 → Qbar l) (v : Fin 2 → Qbar l), (∀ s i, Y s i ∈ c.O) → (∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ v - v) → ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, (((l : ℕ) : Qbar l) ^ m) • Y s = mat W s *ᵥ t - t := by
  intro l _ Ω _ _ W c B _hW hWO
  let A : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l) := fun s => mat W s - 1
  have hAO : ∀ s i j, A s i j ∈ c.O := by
    intro s i j
    simp only [A, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact sub_mem (hWO s i j) (one_mem _)
    · simpa using hWO s i j
  have hmv : ∀ s (w : Fin 2 → Qbar l) i,
      (mat W s *ᵥ w - w) i = A s i 0 * w 0 + A s i 1 * w 1 := by
    intro s w i
    rw [show mat W s *ᵥ w - w = A s *ᵥ w by simp [A, Matrix.sub_mulVec]]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  by_cases h2 : ∃ s ∈ Ine (F := ℚ) B, ∃ s' ∈ Ine (F := ℚ) B, ∃ i i' : Fin 2,
      A s i 0 * A s' i' 1 - A s i 1 * A s' i' 0 ≠ 0
  · obtain ⟨s, hs, s', hs', i, i', hd⟩ := h2
    obtain ⟨k, u, hu, hdu⟩ := coefO_dvd_pow_l c
      (sub_mem (mul_mem (hAO s i 0) (hAO s' i' 1)) (mul_mem (hAO s i 1) (hAO s' i' 0))) hd
    refine ⟨k, fun Y v hY hYv => ⟨((l : ℕ) : Qbar l) ^ k • v, ?_, ?_⟩⟩
    · have hP := hY s i
      have hQ := hY s' i'
      rw [hYv s hs, hmv] at hP
      rw [hYv s' hs', hmv] at hQ
      intro j
      fin_cases j
      · have e : ((l : ℕ) : Qbar l) ^ k • v 0 = u * (A s' i' 1 * (A s i 0 * v 0 + A s i 1 * v 1)
            - A s i 1 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 0)) * hdu
        simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hP) (mul_mem (hAO _ _ _) hQ))
      · have e : ((l : ℕ) : Qbar l) ^ k • v 1 = u * (A s i 0 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)
            - A s' i' 0 * (A s i 0 * v 0 + A s i 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 1)) * hdu
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hQ) (mul_mem (hAO _ _ _) hP))
    · intro s₀ hs₀
      rw [hYv s₀ hs₀, smul_sub, Matrix.mulVec_smul]
  · push_neg at h2
    by_cases h1 : ∃ s ∈ Ine (F := ℚ) B, ∃ i j, A s i j ≠ 0
    · obtain ⟨s, hs, i, j, hα⟩ := h1
      obtain ⟨k, u, hu, hαu⟩ := coefO_dvd_pow_l c (hAO s i j) hα
      refine ⟨k, fun Y v hY hYv => ⟨Pi.single j (u * Y s i), ?_, ?_⟩⟩
      · intro j'
        rcases eq_or_ne j' j with rfl | h
        · simpa using mul_mem hu (hY s i)
        · simp [h]
      · intro s' hs'
        have hc : Y s i = A s i 0 * v 0 + A s i 1 * v 1 := by rw [hYv s hs, hmv]
        ext i'
        rw [Pi.smul_apply, hmv, hYv s' hs', hmv, hc]
        have hdet := h2 s hs s' hs' i i'
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu + u * v 1 * hdet
        · simp only [Fin.mk_one, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu - u * v 0 * hdet
    · push_neg at h1
      refine ⟨0, fun Y v _ hYv => ⟨0, fun _ => zero_mem _, fun s hs => ?_⟩⟩
      ext i
      rw [Pi.smul_apply, hYv s hs, hmv, hmv]
      simp [h1 s hs]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameOfShCoc
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem tame_of_shCoc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (P u : Qbar l) (b : Fin 2 → Qbar l), ShCoc (mat W) ψ Y → (∀ x i, Continuous fun s => Y s x i) → (∀ s x i, Y s x i ∈ c.O) → P ∈ c.O → ‖u‖ = 1 → (∀ i, b i ∈ c.O) → (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b - b)) → (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det)) → (∀ q : Pl, q ≠ w → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ t : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, (∀ x i, t x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ x, Y s x = mat W s *ᵥ t x - t x) → Tame c W y n w ψ := by
  intro l _ Ω _ _ c W y n w ψ Y P u b hY hcont hint hP hu hb hsum hfrob hunr
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩
  refine ⟨fun s a => Y s (Multiplicative.ofAdd (-a)), P, u, b, ?_, fun s a i => hint s _ i, hP, hu, hb, ?_, ?_, hfrob, ?_⟩
  · exact continuous_pi fun a => continuous_pi fun i => hcont _ i
  · intro s t a
    simp only
    rw [hY s t (Multiplicative.ofAdd (-a))]
    congr 3
    rw [neg_sub, sub_eq_neg_add]
    rfl
  · intro s
    rw [finsum_eq_sum_of_fintype, ← hsum s]
    exact Fintype.sum_equiv ((Equiv.neg (ZMod (l ^ n))).trans Multiplicative.ofAdd) _ _ (fun a => rfl)
  · intro q hq hl
    obtain ⟨B, hB, t, ht, hts⟩ := hunr q hq hl
    exact ⟨B, hB, fun a => t (Multiplicative.ofAdd (-a)), fun a i => ht _ i, fun s hs a => hts s hs _⟩

end GlobalTheory.KZ

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KZ


open GlobalTheory.KZGlobAsm in
theorem glob_of_shapiro_system_noLayer (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (W : R2 Ω l) (c : Coef l) (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hWc : Continuous W) (hθc : Continuous θ) (hWO : ∀ s i j, mat W s i j ∈ c.O) (hWθ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hρO : ∀ s i j, ρ s i j ∈ c.O) (hχO : ∀ r x, χ r x ∈ c.O)
    (hχc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hcong : ∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hY : ∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) (hYc : ∀ r x i, Continuous fun s => Y r s x i)
    (hYO : ∀ r s x i, Y r s x i ∈ c.O)
    (hYp : ∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) :
    ∃ y : G ℚ Ω → Fin 2 → Qbar l, y ∈ Z1 (Loc.colRep W) ∧ (∀ s i, y s i ∈ c.O) ∧ Unr W y ∧
      (∀ r s i, ‖y s i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      SpLink A e χ (fun r s x => Y r s x 1) y := by
  set η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l := fun r x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x with hη
  have hηO : ∀ r x, η r x ∈ c.O := fun r x => c.O.mul_mem (inv_pow_val_mem l c e r x) (hχO r x)
  have hηn : ∀ r x, ‖η r x‖ ≤ 1 := fun r x => norm_le_one_of_mem c (hηO r x)
  have hYn : ∀ r s x i, ‖Y r s x i‖ ≤ 1 := fun r s x i => norm_le_one_of_mem c (hYO r s x i)
  have hηc := eta_compat l c e χ hχO hχc
  set a : ℕ → G ℚ Ω → Fin 2 → Qbar l := fun r => spec (η r) (Y r) with ha
  have haE : ∀ r s i, a r s i = ∑ x, η r x * Y r s x i := by
    intro r s i; simp only [ha, spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have haO : ∀ r s i, a r s i ∈ c.O := by
    intro r s i; rw [haE]; exact c.O.sum_mem fun x _ => c.O.mul_mem (hηO r x) (hYO r s x i)
  have haN : ∀ r s i, ‖a r s i‖ ≤ 1 := fun r s i => norm_le_one_of_mem c (haO r s i)
  have hstep : ∀ r s i, ‖a (r + 1) s i - a r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    spec_cauchy l Y η hYn hηn hYp hηc
  have hlim : ∀ s i, ∃ b ∈ c.O, ∀ r, ‖b - a r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    fun s i => GlobalTheory.coef_limit l c (fun r => a r s i) (fun r => haO r s i) (fun r => hstep r s i)
  choose y hyO hyA using hlim
  have happ : ∀ r s t i, ‖a r (s * t) i - (a r s + mat W s *ᵥ a r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s t i
    have h := spec_approx_cocycle l r ρ (cycMod ℚ Ω l r)⁻¹ (Y r) (η r) (fun s => (θ s : Qbar l)) (hY r)
      (fun s i j => norm_le_one_of_mem c (hρO s i j)) (hYn r) (hηn r)
      (fun s x => by simpa only [MonoidHom.inv_apply, inv_inv] using hcong r s x) s t i
    rw [hWθ s, Matrix.smul_mulVec]
    exact h
  have hcoc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t :=
    GlobalTheory.T.isCocycle_of_padic_limit_of_approx_cocycles l (mat W) a y (fun s i j => norm_le_one_of_mem c (hWO s i j)) haN happ
      (fun r s i => hyA s i r)
  have hac : ∀ r i, Continuous fun s => a r s i := by
    intro r i
    simp only [haE]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hYc r x i)
  have hyc : Continuous y := by
    refine continuous_pi fun i => ?_
    refine TendstoUniformly.continuous (F := fun r s => a r s i) (p := Filter.atTop) ?_
      (Filter.Eventually.of_forall fun r => hac r i).frequently
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hq1 : ‖((l : ℕ) : Qbar l)‖ < 1 := GlobalTheory.norm_natCast_prime_qbar l
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq1
    filter_upwards [(ht.eventually (gt_mem_nhds hε))] with r hr s
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (by simpa [norm_pow] using hyA s i r) hr
  have hZ1 : y ∈ Z1 (Loc.colRep W) := by
    refine ⟨hyc, fun g h => ?_⟩
    rw [hcoc g h]
    rfl
  refine ⟨y, hZ1, hyO, ?_, fun r s i => hyA s i r, GlobalTheory.T.kummerScalarLayerLink_of_shapiroSpecialization_approx l Ω A e χ Y y (fun r s _ _ => hyA s 1 r)⟩
  exact GlobalTheory.T.unramified_away_from_l_of_twisted_shapiro_limit l Ω W c θ ρ Y η y hWc hθc hWO hWθ hρO hYc hYO hY hYp hηO (fun r s x => hcong r s x) hZ1
    (fun r s i => hyA s i r)

theorem iwSys2_of_shCoc (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (A : ValuationSubring Ω) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ν : G ℚ Ω → (Qbar l)ˣ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hWθ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hY : ∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) (hO : ∀ r s x i, Y r s x i ∈ c.O)
    (hN : ∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)
      (Y (r + 1)) s)
    (hρ : ∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) :
    IwSys2 c A ν (fun r s x => Y r s x 1) := by
  have hρmul : ∀ s t, ρ (s * t) = ρ s * ρ t := by
    intro s t
    have h := mat_mul' W s t
    rw [hWθ, hWθ, hWθ, map_mul, Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
    exact smul_right_injective _ (mul_ne_zero (θ s).ne_zero (θ t).ne_zero) h
  refine ⟨fun s hs t ht => ?_, fun r => ⟨fun s x => hO r s x 1, fun s hs t _ x => ?_⟩, fun r s x => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, ← (hρ _ (mul_mem hs ht)).2, ← (hρ s hs).2, ← (hρ t ht).2, hρmul, Matrix.mul_apply,
      Fin.sum_univ_two, (hρ s hs).1, zero_mul, zero_add]
  · have h := congrFun (hY r s t x) 1
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, (hρ s hs).1, (hρ s hs).2, zero_mul,
      zero_add, MonoidHom.inv_apply] at h
    exact h
  · have h := congrFun (congrFun (hN r s) x) 1
    simp only [push, Finset.sum_apply] at h
    exact h

end GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem norm_sub_mul_add_le_of_ultrametric_replace {l : ℕ} [Fact l.Prime] {a b c' d P : Qbar l} {ε : ℝ} (h1 : ‖a - (P * b + d)‖ ≤ ε)
    (h2 : ‖c' - b‖ ≤ ε) (hP : ‖P‖ ≤ 1) : ‖a - (P * c' + d)‖ ≤ ε := by
  have e : a - (P * c' + d) = (a - (P * b + d)) + P * (b - c') := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rw [norm_mul, norm_sub_rev b c']
  exact (mul_le_of_le_one_left (norm_nonneg _) hP).trans h2

theorem middle_glue2 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (A : ValuationSubring Ω) (e : ℕ) (S : Finset Pl) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ)
    (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ν : G ℚ Ω → (Qbar l)ˣ)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) →
  (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) →
  (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) →
  (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) →
  (∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) →
  (∀ w : Pl, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) →
  (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∀ s ∈ Ine (F := ℚ) B, θ s = 1) →
  (∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
    KillsMu (normV w) ψ → Function.Surjective ψ →
    ∃ (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (P u : Qbar l)
      (b : ℕ → Fin 2 → Qbar l),
      (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧
      (∀ r s x i, Yw r s x i ∈ c.O) ∧
      (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
      P ∈ c.O ∧ ‖u‖ = 1 ∧ (∀ r i, b r i ∈ c.O) ∧
      (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i -
          (P • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det))) →
  ∃ (m : ℕ) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl),
    (∀ r s i, ‖y s i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    Sys W c (fun s => (((l : ℕ) : Qbar l) ^ m) • y s) S' ∧ IwSys2 c A ν (fun r s x => ((l : ℕ) : Qbar l) ^ m * Y r s x 1) ∧
    SpLink A e χ (fun r s x => ((l : ℕ) : Qbar l) ^ m * Y r s x 1) (fun s => (((l : ℕ) : Qbar l) ^ m) • y s) := by
  intro l _ Ω _ _ _ W c A e S χ θ ρ ν Y hW hθc hWO hWθ hρO hχO hχcomp hχtw hY hYc hYO hYpush hDec hunrS hθI htame
  have hLO : ((l : ℕ) : Qbar l) ∈ c.O := natCast_mem c.O l
  have hL1 : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := GlobalTheory.Ord2.FirstDer.norm_le_one_of_mem c hLO
  obtain ⟨y0, hZ1, hy0O, hUnr0, hap0, hSp⟩ :=
    glob_of_shapiro_system_noLayer l Ω W c A e χ θ ρ Y hW hθc hWO hWθ hρO hχO hχcomp hχtw hY hYc hYO hYpush
  have hIw := iwSys2_of_shCoc l Ω W c A θ ρ ν Y hWθ hY hYO hYpush hDec
  let Bq : Pl → ValuationSubring Ω := fun q => Classical.choose (GlobalTheory.exists_isPlaceOver_rat Ω q)
  have hBq : ∀ q, IsPlaceOver (Bq q) q := fun q => Classical.choose_spec (GlobalTheory.exists_isPlaceOver_rat Ω q)
  let mq : Pl → ℕ := fun q => Classical.choose (GlobalTheory.rat_unram_to_int_unram l Ω W c (Bq q) hW hWO)
  have hmq : ∀ q, ∀ (Z : G ℚ Ω → Fin 2 → Qbar l) (v : Fin 2 → Qbar l), (∀ s i, Z s i ∈ c.O) →
      (∀ s ∈ Ine (F := ℚ) (Bq q), Z s = mat W s *ᵥ v - v) → ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧
        ∀ s ∈ Ine (F := ℚ) (Bq q), (((l : ℕ) : Qbar l) ^ mq q) • Z s = mat W s *ᵥ t - t :=
    fun q => Classical.choose_spec (GlobalTheory.rat_unram_to_int_unram l Ω W c (Bq q) hW hWO)
  have hpowO : ∀ k, ((l : ℕ) : Qbar l) ^ k ∈ c.O := fun k => pow_mem hLO k
  refine ⟨S.sup mq, y0, S, fun r s i => hap0 r s i, ⟨hWO, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (Z1 (Loc.colRep W)).smul_mem _ hZ1
  · intro s i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_mem (hpowO _) (hy0O s i)
  · intro q hq
    obtain ⟨B, hB, x, hx⟩ := hUnr0 q hq
    refine ⟨B, hB, ((l : ℕ) : Qbar l) ^ S.sup mq • x, fun s hs => ?_⟩
    show ((l : ℕ) : Qbar l) ^ S.sup mq • y0 s = _
    rw [hx s hs, Matrix.mulVec_smul, smul_sub]
  · intro n hn w hwS hdiv ψ hkill hsurj
    obtain ⟨Yw, P, u, b, hYw, hYwc, hYwO, hYwpush, hP, hu, hb, happ, hfrob⟩ := htame n hn w hwS hdiv ψ hkill hsurj
    have hP1 : ‖P‖ ≤ 1 := GlobalTheory.Ord2.FirstDer.norm_le_one_of_mem c hP
    have happ' : ∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y0 s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      intro r s i
      have h1 := happ r s i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      exact norm_sub_mul_add_le_of_ultrametric_replace h1 (hap0 r s i) hP1
    obtain ⟨Yt, b', hYt, hYtc, hYtO, hb'O, hsum, hYtap⟩ :=
      GlobalTheory.T.tameClass_limit_of_normCompatible_shapiroSystem l Ω W c e n χ θ ρ ψ Yw y0 P b hWO hWθ hρO hχO hχcomp hχtw hYw hYwc hYwO hYwpush hP hb hy0O happ'
    refine GlobalTheory.KZ.tame_of_shCoc l Ω c W _ n w ψ (fun s x => ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s x) P u
      (((l : ℕ) : Qbar l) ^ S.sup mq • b') ?_ ?_ ?_ hP hu ?_ ?_ hfrob ?_
    · intro s t x
      show ((l : ℕ) : Qbar l) ^ S.sup mq • Yt (s * t) x = ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s x +
        mat W s *ᵥ (((l : ℕ) : Qbar l) ^ S.sup mq • Yt t (x * ψ s))
      rw [hYt s t x, smul_add, Matrix.mulVec_smul]
    · intro x i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact continuous_const.mul (hYtc x i)
    · intro s x i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (hpowO _) (hYtO s x i)
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (hpowO _) (hb'O i)
    · intro s
      rw [← Finset.smul_sum, hsum s, smul_add, smul_comm (((l : ℕ) : Qbar l) ^ S.sup mq) P (y0 s),
        Matrix.mulVec_smul, smul_sub]
    · intro q hqw hql
      refine ⟨Bq q, hBq q, ?_⟩
      have hψθ : ∀ s ∈ Ine (F := ℚ) (Bq q), ψ s = 1 ∧ θ s = 1 := fun s hs =>
        ⟨GlobalTheory.Ord2.FirstDer.killsMu_ine hqw hkill (hBq q) hs, hθI q hql (Bq q) (hBq q) s hs⟩
      obtain ⟨v, hv⟩ := GlobalTheory.T.tameShapiroSystem_limit_unramified_away_from_l l Ω W c n e χ θ ρ ψ Yw Yt q (Bq q) hql (hBq q) hψθ hW hWO hWθ hρO hχO
        hYw hYwc hYwO hYwpush hYtap
      by_cases hqS : q ∈ S
      · have hle : mq q ≤ S.sup mq := Finset.le_sup hqS
        have hex : ∀ a, ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) (Bq q),
            (((l : ℕ) : Qbar l) ^ mq q) • Yt s a = mat W s *ᵥ t - t :=
          fun a => hmq q (fun s => Yt s a) (v a) (fun s i => hYtO s a i) (fun s hs => hv s hs a)
        choose t ht1 ht2 using hex
        refine ⟨fun a => ((l : ℕ) : Qbar l) ^ (S.sup mq - mq q) • t a, fun a i => ?_, fun s hs a => ?_⟩
        · simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (hpowO _) (ht1 a i)
        · have hpow : ((l : ℕ) : Qbar l) ^ S.sup mq =
              ((l : ℕ) : Qbar l) ^ (S.sup mq - mq q) * ((l : ℕ) : Qbar l) ^ mq q := by
            rw [← pow_add, Nat.sub_add_cancel hle]
          show ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s a = _
          rw [hpow, mul_smul, ht2 a s hs, Matrix.mulVec_smul, smul_sub]
      · refine ⟨fun _ => 0, fun _ _ => zero_mem _, fun s hs a => ?_⟩
        have hW1 : W s = 1 := hunrS q hqS (Bq q) (hBq q) hs
        have hm1 : mat W s = 1 := by simp [mat, hW1]
        show ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s a = _
        rw [hv s hs a, hm1]
        simp
  · refine ⟨hIw.1, fun r => ⟨fun s x => ?_, fun s hs t ht x => ?_⟩, fun r s x => ?_⟩
    · exact mul_mem (hpowO _) ((hIw.2.1 r).1 s x)
    · have h := (hIw.2.1 r).2 s hs t ht x
      simp only at h ⊢
      rw [h]
      ring
    · have h := hIw.2.2 r s x
      simp only at h ⊢
      rw [h, Finset.mul_sum]
  · intro n
    obtain ⟨r0, hr0⟩ := hSp n
    refine ⟨r0, fun r hr s hs hcyc => ?_⟩
    have h := hr0 r hr s hs hcyc
    unfold Cg sp at h ⊢
    simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
    have hk : ‖((l : ℕ) : Qbar l) ^ S.sup mq‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hL1
    refine le_trans ?_ h
    rw [← Finset.sum_congr rfl fun x _ => (mul_left_comm _ (((l : ℕ) : Qbar l) ^ S.sup mq) _).symm,
      ← Finset.mul_sum, ← mul_sub, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hk

end GlobalTheory.KZ

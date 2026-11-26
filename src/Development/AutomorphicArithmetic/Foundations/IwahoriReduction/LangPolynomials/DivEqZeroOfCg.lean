module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DivAlg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.DivAlg

variable {l : ℕ} [Fact l.Prime]

private theorem prim_root : ∃ z : ℤ_[l], IsPrimitiveRoot z (l - 1) := by
  have hp : l.Prime := Fact.out
  have hl : l - 1 ≠ 0 := by have := hp.two_le; omega
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at ha
  set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l]) with hb
  have hbz : PadicInt.toZMod b = (a : ZMod l) := by simp [hb]
  have hker : ∀ x : ℤ_[l], ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := fun x => by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.mem_nonunits.symm]; rfl
  have hapow : (a : ZMod l) ^ (l - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← ha, pow_orderOf_eq_one, Units.val_one]
  let F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1
  have h1 : ‖F.aeval b‖ < 1 := by
    rw [hker]; simp [F, hbz, hapow]
  have h2 : ‖F.derivative.aeval b‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
    rw [hker] at h
    have h3 : ((l - 1 : ℕ) : ZMod l) = -1 := by
      rw [Nat.cast_sub hp.one_le]; simp
    simp [F, hbz, h3, Polynomial.derivative_X_pow] at h
  obtain ⟨z, hz, hzb, -⟩ := hensels_lemma (F := F) (a := b) (by rw [h2]; simpa using h1)
  rw [h2, hker, map_sub, hbz, sub_eq_zero] at hzb
  have hz1 : z ^ (l - 1) = 1 := by simpa [F, sub_eq_zero] using hz
  refine ⟨z, hz1, fun m hm => ?_⟩
  rw [← ha]
  apply orderOf_dvd_of_pow_eq_one
  ext
  rw [Units.val_pow_eq_pow_val, ← hzb, ← map_pow, hm, map_one, Units.val_one]

private theorem alg_norm (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  rfl

private theorem alg_inj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← norm_eq_zero, ← alg_norm, ha, norm_zero]

private theorem root_mem {w : Qbar l} (hw : w ^ (l - 1) = 1) : ∃ z : ℤ_[l], algebraMap ℤ_[l] (Qbar l) z = w := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l - 1) := ⟨by have := hp.two_le; omega⟩
  obtain ⟨z, hz⟩ := prim_root (l := l)
  obtain ⟨i, -, hi⟩ := (hz.map_of_injective (f := algebraMap ℤ_[l] (Qbar l)) alg_inj).eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

private theorem norm_nat (m : ℕ) : ‖((m : ℕ) : Qbar l)‖ = ‖((m : ℕ) : ℚ_[l])‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']

private theorem norm_nat_one {m : ℕ} (h : ¬ l ∣ m) : ‖((m : ℕ) : Qbar l)‖ = 1 := by
  rw [norm_nat]
  exact Padic.norm_natCast_eq_one_iff.2 (((Fact.out : l.Prime).coprime_iff_not_dvd).2 h)

private theorem norm_l : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [norm_nat]; exact Padic.norm_p_lt_one

private theorem small {a : ℝ} (ha : 0 < a) : ∃ n : ℕ, ∀ m, n ≤ m → ‖((l : ℕ) : Qbar l) ^ m‖ ≤ a := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha (norm_l (l := l))
  refine ⟨n, fun m hm => ?_⟩
  rw [norm_pow]
  exact (pow_le_pow_of_le_one (norm_nonneg _) norm_l.le hm).trans hn.le

private theorem phi_pow (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : φ (m : ZMod l) ^ (l - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one (by rwa [Ne, ZMod.natCast_eq_zero_iff]), map_one]

private theorem phi_norm (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : ‖φ (m : ZMod l)‖ = 1 := by
  have hl : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hl).1 (by rw [← norm_pow, phi_pow φ h, norm_one])

private theorem theta_ne (φ : DirichletCharacter (Qbar l) l) {g k N : ℕ} (h : ¬ l ∣ g) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (hN : 0 < N) : (φ (g : ZMod l) * (g : Qbar l) ^ k) ^ N ≠ 1 := by
  intro h1
  have hl : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  have h2 : ((φ (g : ZMod l) * (g : Qbar l) ^ k) ^ N) ^ (l - 1) = 1 := by rw [h1, one_pow]
  rw [← pow_mul, mul_comm N, pow_mul, mul_pow, phi_pow φ h, one_mul, ← pow_mul, ← pow_mul] at h2
  have h3 : g ^ (k * ((l - 1) * N)) = 1 := by exact_mod_cast h2
  rw [Nat.pow_eq_one] at h3
  rcases h3 with h3 | h3
  · omega
  · exact mul_ne_zero (by omega) (mul_ne_zero hl hN.ne') h3

private theorem nsub (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

private theorem iter {Γ : Type} [Group Γ] (γ : Γ) (θ : Qbar l) (hθ : ‖θ‖ ≤ 1) (q : Γ → Qbar l) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ x, ‖q (x * γ) - θ * q x‖ ≤ ε) (x : Γ) (i : ℕ) : ‖q (x * γ ^ i) - θ ^ i * q x‖ ≤ ε := by
  induction i with
  | zero => simpa using hε
  | succ i ih =>
    have e : q (x * γ ^ (i + 1)) - θ ^ (i + 1) * q x =
        (q (x * γ ^ i * γ) - θ * q (x * γ ^ i)) + θ * (q (x * γ ^ i) - θ ^ i * q x) := by
      rw [pow_succ γ, mul_assoc x]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h _) ?_)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hθ).trans ih

private theorem pow_mod_near (τ : Qbar l) (hτ : ‖τ‖ ≤ 1) (N j : ℕ) : ‖τ ^ (j % N) - τ ^ j‖ ≤ ‖τ ^ N - 1‖ := by
  have e : τ ^ (j % N) - τ ^ j = - (τ ^ (j % N) * ((∑ i ∈ Finset.range (j / N), (τ ^ N) ^ i) * (τ ^ N - 1))) := by
    rw [geom_sum_mul, ← pow_mul, mul_sub, ← pow_add, Nat.mod_add_div]; ring
  rw [e, norm_neg, norm_mul, norm_mul]
  have h1 : ‖τ ^ (j % N)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hτ
  have h2 : ‖∑ i ∈ Finset.range (j / N), (τ ^ N) ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow, norm_pow]; exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hτ)
  exact (mul_le_of_le_one_left (by positivity) h1).trans (mul_le_of_le_one_left (norm_nonneg _) h2)

private theorem inv_near {x y : Qbar l} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x⁻¹ - y⁻¹‖ = ‖x - y‖ := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have e : x⁻¹ - y⁻¹ = -(x - y) * x⁻¹ * y⁻¹ := by field_simp; ring
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv, hx, hy, norm_neg]; simp

private theorem eta_near (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {g : ℕ} (hg : ¬ l ∣ g) {r : ℕ} (hr : 1 ≤ r) (j : ℕ) :
    ‖eta φ k r (un g hg r ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hp : l.Prime := Fact.out
  have hv : ((un g hg r ^ j : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val = g ^ j % l ^ r := by
    rw [Units.val_pow_eq_pow_val, un, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
  have hd : l ∣ l ^ r := dvd_pow_self l (by omega)
  have hgj : ¬ l ∣ g ^ j := fun h => hg (hp.dvd_of_dvd_pow h)
  have hY : ¬ l ∣ g ^ j % l ^ r := by rwa [Nat.dvd_mod_iff hd]
  have hφ : ((g ^ j % l ^ r : ℕ) : ZMod l) = (g : ZMod l) ^ j := by
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 (Nat.mod_mod_of_dvd _ hd)
  simp only [eta, hv, hφ, map_pow]
  have e : ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j = (φ (g : ZMod l) ^ j)⁻¹ * (((g ^ j : ℕ) : Qbar l) ^ k)⁻¹ := by
    rw [inv_pow, mul_pow, mul_inv, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e, ← mul_sub, norm_mul, norm_inv, norm_pow, phi_norm φ hg, one_pow, inv_one, one_mul,
    inv_near (by rw [norm_pow, norm_nat_one hY, one_pow]) (by rw [norm_pow, norm_nat_one hgj, one_pow])]
  obtain ⟨m, hm⟩ := Nat.modEq_iff_dvd.1 ((Nat.mod_modEq (g ^ j) (l ^ r)).pow k).symm
  have hmQ : ((g ^ j % l ^ r : ℕ) : Qbar l) ^ k - ((g ^ j : ℕ) : Qbar l) ^ k = ((l : ℕ) : Qbar l) ^ r * (m : Qbar l) := by
    have := congrArg (fun z : ℤ => (z : Qbar l)) hm
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Nat.cast_pow, Int.cast_pow] using this
  rw [hmQ, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ m)

private theorem red_un {g : ℕ} (hg : ¬ l ∣ g) (r : ℕ) : red l r (un g hg (r + 1)) = un g hg r := by
  ext
  simp [red, un]

private theorem sum_bound (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {g : ℕ} (hg : ¬ l ∣ g)
    (hgen : ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), x ∈ Subgroup.zpowers (un g hg r))
    (μ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (hμ : ∀ r x, ‖μ r x‖ ≤ 1)
    (hn : ∀ r (x : (ZMod (l ^ r))ˣ), μ r x =
      ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ => red l r x' = x), μ (r + 1) x')
    (h0 : ∀ n : ℕ, ∃ r₀, ∀ r, r₀ ≤ r → Cg n (∑ x, eta φ k r x * μ r x) 0)
    (a : ℝ) (ha : 0 < a) (r : ℕ) (f : (ZMod (l ^ r))ˣ → Qbar l)
    (hf : ∀ j : ℕ, ‖f (un g hg r ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ a) :
    ‖∑ x, f x * μ r x‖ ≤ a := by
  have key : ∀ s, r ≤ s → ∃ f' : (ZMod (l ^ s))ˣ → Qbar l,
      (∀ j : ℕ, ‖f' (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j‖ ≤ a) ∧
        ∑ x, f' x * μ s x = ∑ x, f x * μ r x := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact ⟨f, hf, rfl⟩
    | succ s hs ih =>
      obtain ⟨f', h1, h2⟩ := ih
      refine ⟨fun y => f' (red l s y), fun j => by simpa only [map_pow, red_un] using h1 j, ?_⟩
      rw [← h2, ← Finset.sum_fiberwise Finset.univ (red l s)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hn s x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      beta_reduce
      rw [(Finset.mem_filter.1 hy).2]
  obtain ⟨n, hn'⟩ := small (l := l) ha
  obtain ⟨r₀, hr₀⟩ := h0 n
  set s := r + r₀ + n + 1 with hs
  obtain ⟨f', h1, h2⟩ := key s (by omega)
  have h3 : ‖∑ x, eta φ k s x * μ s x‖ ≤ a := by
    have := hr₀ s (by omega)
    rw [Cg, sub_zero] at this
    exact this.trans (hn' n le_rfl)
  have e : ∑ x, f' x * μ s x = ∑ x, (f' x - eta φ k s x) * μ s x + ∑ x, eta φ k s x * μ s x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [← h2, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h3)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ha.le fun x _ => ?_
  rw [norm_mul]
  refine (mul_le_of_le_one_right (norm_nonneg _) (hμ s x)).trans ?_
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hgen s x) : x ∈ Submonoid.powers (un g hg s))
  have h4 := nsub (f' (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j)
    (eta φ k s (un g hg s ^ j) - ((φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹) ^ j)
  rw [sub_sub_sub_cancel_right] at h4
  exact h4.trans (max_le (h1 j) ((eta_near φ k hg (by omega) j).trans (hn' s (by omega))))

private theorem logfun {Γ : Type} [Group Γ] [Fintype Γ] (γ : Γ) (τ : Qbar l) (μ : Γ → Qbar l) :
    ∃ f : Γ → Qbar l, (∀ j : ℕ, f (γ ^ j) = τ ^ (j % orderOf γ)) ∧
      ∑ x, f x * μ x = ∑ i ∈ Finset.range (orderOf γ), τ ^ i * μ (γ ^ i) := by
  classical
  refine ⟨fun y => ∑ i ∈ Finset.range (orderOf γ), if γ ^ i = y then τ ^ i else 0, fun j => ?_, ?_⟩
  · beta_reduce
    rw [Finset.sum_eq_single (j % orderOf γ)]
    · rw [if_pos (pow_mod_orderOf γ j)]
    · intro i hi hne
      rw [if_neg]
      intro h
      rw [pow_inj_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)] at h
      exact hne h
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ (orderOf_pos γ))) h
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

private theorem coef_norm (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  have h1 := (h β).1
  have e := congrArg (fun y : c.O => (y : Qbar l)) (β.e.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Algebra.smul_def] at e
  rw [← e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  have h2 : ‖((β.e i : c.O) : Qbar l)‖ ≤ 1 := h1 i
  rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, norm_mul, alg_norm]
  exact mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h2

private theorem coef_div (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) {t : ℤ_[l]} (ht : t ≠ 0)
    (hle : ‖x‖ ≤ ‖algebraMap ℤ_[l] (Qbar l) t‖) : x / algebraMap ℤ_[l] (Qbar l) t ∈ c.O := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  have hs := PadicInt.unitCoeff_spec ht
  set u := PadicInt.unitCoeff ht
  set m := t.valuation
  have hu : ‖algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l])‖ = 1 := by rw [alg_norm]; exact PadicInt.norm_units u
  have e : algebraMap ℤ_[l] (Qbar l) t = algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]) * (l : Qbar l) ^ m := by
    rw [hs, map_mul, map_pow, map_natCast]
  obtain ⟨y, hy⟩ := (h β).2.2.1 m ⟨x, hx⟩ (by
    rw [e, norm_mul, hu, one_mul] at hle
    simpa [Cg] using hle)
  have hy' : x = (l : Qbar l) ^ m * (y : Qbar l) := by simpa using congrArg (fun y : c.O => (y : Qbar l)) hy
  have hl : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu0 : algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]) ≠ 0 := by intro h0; simp [h0] at hu
  have e2 : x / algebraMap ℤ_[l] (Qbar l) t = (y : Qbar l) * (algebraMap ℤ_[l] (Qbar l) (u : ℤ_[l]))⁻¹ := by
    rw [e, hy']; field_simp
  rw [e2]
  exact mul_mem y.2 ((h β).2.2.2 _ (c.O.algebraMap_mem _) hu)

end UpperTheory.Kd.C7.DivAlg

open UpperTheory.Kd.C7.DivAlg in
theorem UpperTheory.Kd.C7.pDivAlg :
    UpperTheory.Kd.C7.SDivAlg := by
  intro l _ c g hg h2 hgen φ k hk
  have hθ : ‖φ (g : ZMod l) * (g : Qbar l) ^ k‖ = 1 := by
    rw [norm_mul, norm_pow, phi_norm φ hg, norm_nat_one hg, one_pow, one_mul]
  have hne := fun r => theta_ne φ hg h2 hk (orderOf_pos (un g hg r))
  obtain ⟨z, hz⟩ : ∃ z : ℤ_[l], algebraMap ℤ_[l] (Qbar l) z = (φ (g : ZMod l) * (g : Qbar l) ^ k)⁻¹ := by
    obtain ⟨w, hw⟩ := root_mem (phi_pow φ hg)
    have e : algebraMap ℤ_[l] (Qbar l) (w * (g : ℤ_[l]) ^ k) = φ (g : ZMod l) * (g : Qbar l) ^ k := by
      rw [map_mul, map_pow, map_natCast, hw]
    have hu : IsUnit (w * (g : ℤ_[l]) ^ k) := by rw [PadicInt.isUnit_iff, ← alg_norm, e, hθ]
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    refine ⟨v, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← e, ← map_mul, hv, map_one]
  have hsum := sum_bound φ k hg hgen
  generalize φ (g : ZMod l) * (g : Qbar l) ^ k = θ at hθ hne hz hsum ⊢
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  refine ⟨fun r => ?_, fun μ hμ hn h0 r => ?_⟩
  · have hpos : 0 < ‖1 - θ ^ orderOf (un g hg r)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne r).symm)
    obtain ⟨c₃, hc⟩ := small (l := l) hpos
    refine ⟨c₃, fun q n h x => ?_⟩
    have h1 := iter (un g hg r) θ hθ.le q ‖((l : ℕ) : Qbar l) ^ (n + c₃)‖ (norm_nonneg _)
      (fun x => by simpa only [Cg, sub_zero] using h x) x (orderOf (un g hg r))
    rw [pow_orderOf_eq_one, mul_one, ← one_sub_mul, norm_mul, pow_add, norm_mul] at h1
    rw [Cg, sub_zero]
    have h3 := h1.trans (mul_le_mul_of_nonneg_left (hc c₃ le_rfl) (norm_nonneg _))
    rw [mul_comm] at h3
    exact le_of_mul_le_mul_right h3 hpos
  · set γ := un g hg r with hγ
    set N := orderOf γ with hN
    set τ := θ⁻¹ with hτ
    have hτn : ‖τ‖ = 1 := by rw [hτ, norm_inv, hθ, inv_one]
    have hτ1 : τ ^ N - 1 ≠ 0 := by
      rw [sub_ne_zero, hτ, inv_pow, Ne, inv_eq_one]; exact hne r
    have hτO : τ ∈ c.O := hz ▸ c.O.algebraMap_mem z
    have hμn : ∀ r x, ‖μ r x‖ ≤ 1 := fun r x => coef_norm c (hμ r x)
    let S : (ZMod (l ^ r))ˣ → Qbar l := fun x => ∑ i ∈ Finset.range N, τ ^ i * μ r (x * γ ^ i)
    have hS : ∀ x, τ * S (x * γ) - S x = (τ ^ N - 1) * μ r x := fun x => by
      have e := Finset.sum_range_sub (fun i => τ ^ i * μ r (x * γ ^ i)) N
      rw [hN, pow_orderOf_eq_one, ← hN] at e
      simp only [pow_zero, mul_one, one_mul] at e
      rw [sub_mul, one_mul, ← e, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ' τ, pow_succ' γ, mul_assoc, mul_assoc]
    have hS1 : ‖S 1‖ ≤ ‖τ ^ N - 1‖ := by
      obtain ⟨f, hf1, hf2⟩ := logfun γ τ (μ r)
      have := hsum μ hμn hn h0 _ (norm_pos_iff.2 hτ1) r f (fun j => by
        rw [hf1]; exact pow_mod_near τ hτn.le N j)
      rw [hf2] at this
      simpa only [S, one_mul] using this
    have hSx : ∀ x, ‖S x‖ ≤ ‖τ ^ N - 1‖ := fun x => by
      obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hgen r x) : x ∈ Submonoid.powers γ)
      beta_reduce
      induction j with
      | zero => simpa using hS1
      | succ j ih =>
        have e : τ * S (γ ^ (j + 1)) = (τ ^ N - 1) * μ r (γ ^ j) + S (γ ^ j) := by
          rw [← hS, pow_succ]; ring
        have h1 : ‖τ * S (γ ^ (j + 1))‖ ≤ ‖τ ^ N - 1‖ := by
          rw [e]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hμn _ _)
        rwa [norm_mul, hτn, one_mul] at h1
    have hSO : ∀ x, S x ∈ c.O := fun x => sum_mem fun i _ => mul_mem (pow_mem hτO i) (hμ r _)
    have ht : algebraMap ℤ_[l] (Qbar l) (z ^ N - 1) = τ ^ N - 1 := by rw [map_sub, map_pow, hz, map_one]
    have ht0 : z ^ N - 1 ≠ 0 := fun h => hτ1 (by rw [← ht, h, map_zero])
    refine ⟨fun x => τ * (S x / (τ ^ N - 1)), fun x => mul_mem hτO ?_, fun x => ?_⟩
    · rw [← ht]
      exact coef_div c (hSO x) ht0 (by rw [ht]; exact hSx x)
    · have e : θ * τ = 1 := mul_inv_cancel₀ hθ0
      beta_reduce
      rw [← mul_assoc θ, e, one_mul, ← mul_div_assoc, ← sub_div, hS, mul_div_cancel_left₀ _ hτ1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.CardUn
noncomputable section

namespace UpperTheory.Kd.C7

private theorem mem_zpowers_un_of_primitive_root_mod_sq {l : ℕ} [Fact (Nat.Prime l)] (hl2 : l ≠ 2) (g : ℕ) (hg : ¬ l ∣ g)
    (ho : orderOf (g : ZMod l) = l - 1) (hnd : ¬ ((l : ℤ) ^ 2 ∣ (g : ℤ) ^ (l - 1) - 1))
    (r : ℕ) (x : (ZMod (l ^ r))ˣ) : x ∈ Subgroup.zpowers (un g hg r) := by
  have hp : l.Prime := Fact.out
  have hgl : (g : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hg
  have hf : (l : ℤ) ∣ (g : ℤ) ^ (l - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hgl, sub_self]
  obtain ⟨a, ha⟩ := hf
  have han : ¬ (l : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    exact hnd ⟨b, by rw [ha]; ring⟩
  have hga : (g : ℤ) ^ (l - 1) = 1 + l * a := by
    rw [← ha]; ring
  rcases r with _ | n
  · have : Subsingleton (ZMod (l ^ 0))ˣ := by
      rw [pow_zero]; infer_instance
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  set u := un g hg (n + 1) with hu
  have hcast : (u : ZMod (l ^ (n + 1))) = (g : ZMod (l ^ (n + 1))) := by
    simp [hu, un]
  have h1 : orderOf (u ^ (l - 1)) = l ^ n := by
    rw [← orderOf_units, Units.val_pow_eq_pow_val, hcast]
    have e : (g : ZMod (l ^ (n + 1))) ^ (l - 1) = 1 + (l : ZMod (l ^ (n + 1))) * (a : ZMod (l ^ (n + 1))) := by
      have := congrArg (Int.cast : ℤ → ZMod (l ^ (n + 1))) hga
      push_cast at this
      exact this
    rw [e]
    exact ZMod.orderOf_one_add_mul_prime hp hl2 a han n
  have hm : l ∣ l ^ (n + 1) := dvd_pow_self l (Nat.succ_ne_zero n)
  have h2 : l - 1 ∣ orderOf u := by
    have h3 : orderOf (ZMod.unitsMap hm u) = l - 1 := by
      rw [← orderOf_units]
      have : ((ZMod.unitsMap hm u : (ZMod l)ˣ) : ZMod l) = (g : ZMod l) := by
        simp [ZMod.unitsMap, hcast]
      rw [this, ho]
    rw [← h3]
    exact orderOf_map_dvd _ u
  have h4 : l ^ n ∣ orderOf u := h1 ▸ orderOf_pow_dvd _
  have hcard : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcop : Nat.Coprime (l ^ n) (l - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_self_sub_right hp.pos]
    simp
  have h5 : orderOf u = Nat.card (ZMod (l ^ (n + 1)))ˣ := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_natCard u
    · rw [hcard]
      exact hcop.mul_dvd_of_dvd_of_dvd h4 h2
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h5]
  rw [htop]
  exact Subgroup.mem_top x

theorem pGenEx : SGenEx := by
  intro l _ hl2
  have hp : l.Prime := Fact.out
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  have hc0 : (((c : ZMod l).val : ℕ) : ZMod l) = c := ZMod.natCast_zmod_val _
  set c0 : ℕ := (c : ZMod l).val with hc0def
  have hnd0 : ¬ l ∣ c0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff c0 l).mpr h
    rw [hc0] at h'
    exact c.ne_zero h'
  have hord : ∀ k : ℕ, orderOf ((c0 + l * k : ℕ) : ZMod l) = l - 1 := by
    intro k
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, hc0, orderOf_units, hc]
  have hndk : ∀ k : ℕ, ¬ l ∣ c0 + l * k := by
    intro k h
    exact hnd0 ((Nat.dvd_add_left (dvd_mul_right l k)).mp h)
  have hc2 : 2 ≤ c0 := by
    by_contra h
    push_neg at h
    have h01 : c0 = 0 ∨ c0 = 1 := by omega
    rcases h01 with h0 | h1
    · exact hnd0 (h0 ▸ dvd_zero l)
    · have h1' : (c : ZMod l) = 1 := by
        rw [← hc0, h1, Nat.cast_one]
      have hc1 : c = 1 := Units.ext h1'
      rw [hc1, orderOf_one] at hc
      have := hp.two_le
      omega
  by_cases hsq : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1) - 1
  · have hnd1 : ¬ ((l : ℤ) ^ 2 ∣ ((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1) := by
      intro hB
      have key := sq_dvd_add_pow_sub_sub (l : ℤ) (c0 : ℤ) (l - 1)
      have hsum : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by
        have e : (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) =
            (((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1)
              - (((c0 : ℤ) + l) ^ (l - 1) - (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ)
                - (c0 : ℤ) ^ (l - 1))
              - ((c0 : ℤ) ^ (l - 1) - 1) := by
          push_cast
          ring
        rw [e]
        exact dvd_sub (dvd_sub hB key) hsq
      have h6 : (l : ℤ) ∣ (c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ) := by
        have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [← mul_dvd_mul_iff_left hl0]
        have e2 : (l : ℤ) * ((c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ))
            = (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by ring
        rw [e2, ← sq]
        exact hsum
      have h7 : l ∣ c0 ^ (l - 1 - 1) * (l - 1) := by exact_mod_cast h6
      rcases (Nat.Prime.dvd_mul hp).mp h7 with h8 | h8
      · exact hnd0 (hp.dvd_of_dvd_pow h8)
      · have := hp.two_le
        have := Nat.le_of_dvd (by omega) h8
        omega
    exact ⟨c0 + l * 1, hndk 1, by omega, mem_zpowers_un_of_primitive_root_mod_sq hl2 _ (hndk 1) (hord 1) hnd1⟩
  · have h0 := hord 0
    simp only [mul_zero, add_zero] at h0
    exact ⟨c0, hnd0, hc2, mem_zpowers_un_of_primitive_root_mod_sq hl2 c0 hnd0 h0 hsq⟩

end UpperTheory.Kd.C7
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem isOpen_setOf_cycMod_eq_one (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (r : ℕ) :
    IsOpen {s : G ℚ Ω | cycMod ℚ Ω l r s = 1} := by
  have key : ∀ s : G ℚ Ω, cycMod ℚ Ω l r s = 1 ↔
      ((cycZ ℚ Ω l s : ℤ_[l])) ∈ Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(r : ℤ))) := by
    intro s
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, Units.ext_iff]
    simp [cycMod]
  have e : {s : G ℚ Ω | cycMod ℚ Ω l r s = 1} =
      (fun s => ((cycZ ℚ Ω l s : ℤ_[l]))) ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(r : ℤ))) :=
    Set.ext key
  rw [e]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : Nat.Prime l).pos
  exact (IsUltrametricDist.isOpen_closedBall _ (zpow_pos hl _).ne').preimage
    (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))

private theorem norm_natCast_prime_lt_one_qbar (l : ℕ) [Fact (Nat.Prime l)] : ‖(l : Qbar l)‖ < 1 := by
  show ‖(l : PadicAlgCl l)‖ < 1
  have h : ((l : ℚ_[l]) : PadicAlgCl l) = (l : PadicAlgCl l) := map_natCast _ l
  rw [← h, PadicAlgCl.norm_extends]
  first | exact padicNormE.norm_p_lt_one | exact Padic.norm_p_lt_one

private theorem red_un_succ (l : ℕ) [Fact (Nat.Prime l)] (r : ℕ) (g : ℕ) (hg : ¬ l ∣ g) :
    red l r (un g hg (r + 1)) = un g hg r := by
  ext
  simp [un, red, ZMod.unitOfCoprime, ZMod.cast_natCast (pow_dvd_pow l (Nat.le_succ r))]

private theorem red_cycMod_succ (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (r : ℕ)
    (s : G ℚ Ω) : red l r (cycMod ℚ Ω l (r + 1) s) = cycMod ℚ Ω l r s := by
  ext
  simp [cycMod, red, PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r)]

private theorem eta_one_of_one_le (l : ℕ) [Fact (Nat.Prime l)] (φ : DirichletCharacter (Qbar l) l) (k r : ℕ)
    (hr : 1 ≤ r) : eta φ k r 1 = 1 := by
  haveI : Fact (1 < l ^ r) := ⟨Nat.one_lt_pow (by omega) (Fact.out : Nat.Prime l).one_lt⟩
  simp [eta, ZMod.val_one]

private theorem cg_iff_norm_sub_le_norm_pow (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (a b : Qbar l) :
    Cg n a b ↔ ‖a - b‖ ≤ ‖(l : Qbar l) ^ n‖ := Iff.rfl

set_option maxHeartbeats 800000 in
theorem UpperTheory.Kd.C7.pDiv :
    UpperTheory.Kd.C7.SDiv := by
  intro l _ hl Ω _ _ _ A hA c Z hZ hC φ k hk hS
  obtain ⟨g, hg, hg2, hgen⟩ := UpperTheory.Kd.C7.pGenEx l hl
  obtain ⟨c₂, w, hw, hcob⟩ := UpperTheory.Kd.C7.pCob l hl Ω A hA c Z hZ φ k hk hS
  obtain ⟨hZint, hZcoc, hZnrm⟩ := hZ
  have hdiv := UpperTheory.Kd.C7.pDivAlg l c g hg hg2 hgen φ k hk
  obtain ⟨μ, hμ⟩ : ∃ μ : G ℚ Ω → (r : ℕ) → (ZMod (l ^ r))ˣ → Qbar l, ∀ s r x,
      μ s r x = (l : Qbar l) ^ c₂ * Z r s x -
        w * ((if x = cycMod ℚ Ω l r s then 1 else 0) - (if x = 1 then 1 else 0)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hOl : ((l : Qbar l) ^ c₂) ∈ c.O := Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ l) _
  have hμint : ∀ s ∈ Ine A, ∀ r x, μ s r x ∈ c.O := by
    intro s hs r x
    rw [hμ]
    refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hOl (hZint r s hs x)) (Subalgebra.mul_mem _ hw ?_)
    refine Subalgebra.sub_mem _ ?_ ?_ <;> split_ifs <;> simp
  have hsumind : ∀ r (y : (ZMod (l ^ r))ˣ) (a : (ZMod (l ^ (r + 1)))ˣ),
      ∑ x' with red l r x' = y, (if x' = a then (1 : Qbar l) else 0) = if y = red l r a then 1 else 0 := by
    intro r y a
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  have hμnrm : ∀ s ∈ Ine A, ∀ r x, μ s r x = ∑ x' with red l r x' = x, μ s (r + 1) x' := by
    intro s hs r x
    have e1 := hsumind r x (cycMod ℚ Ω l (r + 1) s)
    have e2 := hsumind r x 1
    rw [red_cycMod_succ] at e1
    rw [map_one] at e2
    simp only [hμ]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, e1, e2,
      ← hZnrm r s hs x]
  have heta : ∀ s ∈ Ine A, ∀ n, ∃ r₀, ∀ r, r₀ ≤ r → Cg n (∑ x, eta φ k r x * μ s r x) 0 := by
    intro s hs n
    obtain ⟨r₀, hr₀⟩ := hcob s hs n
    refine ⟨max r₀ 1, fun r hr => ?_⟩
    have h := hr₀ r (le_of_max_le_left hr)
    have hx : ∀ x, eta φ k r x * μ s r x = (l : Qbar l) ^ c₂ * (eta φ k r x * Z r s x) -
        w * (if x = cycMod ℚ Ω l r s then eta φ k r x else 0) +
        w * (if x = 1 then eta φ k r x else 0) := by
      intro x
      rw [hμ]
      split_ifs <;> ring
    have e : ∑ x, eta φ k r x * μ s r x =
        (l : Qbar l) ^ c₂ * sp (eta φ k r) (Z r) s - (eta φ k r (cycMod ℚ Ω l r s) - 1) * w := by
      rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), eta_one_of_one_le l φ k r (le_of_max_le_right hr)]
      simp only [sp]
      ring
    rw [cg_iff_norm_sub_le_norm_pow, sub_zero, e]
    rw [cg_iff_norm_sub_le_norm_pow] at h
    exact h
  have hex : ∀ s ∈ Ine A, ∀ r, ∃ q : (ZMod (l ^ r))ˣ → Qbar l, (∀ x, q x ∈ c.O) ∧
      ∀ x, μ s r x = q (x * un g hg r) - φ ↑g * ↑g ^ k * q x :=
    fun s hs => hdiv.2 (μ s) (hμint s hs) (hμnrm s hs) (heta s hs)
  obtain ⟨Z', hZ'⟩ : ∃ Z' : Sy Ω l, ∀ r, ∀ s ∈ Ine A, (∀ x, Z' r s x ∈ c.O) ∧
      ∀ x, μ s r x = Z' r s (x * un g hg r) - φ ↑g * ↑g ^ k * Z' r s x := by
    refine ⟨fun r s => @dite _ (s ∈ Ine A) (Classical.dec _) (fun h => Classical.choose (hex s h r)) (fun _ => fun _ => 0), ?_⟩
    intro r s hs
    simp only [dif_pos hs]
    exact Classical.choose_spec (hex s hs r)
  have inj : ∀ r (q : (ZMod (l ^ r))ˣ → Qbar l),
      (∀ x, q (x * un g hg r) - φ ↑g * ↑g ^ k * q x = 0) → ∀ x, q x = 0 := by
    intro r q hq x
    obtain ⟨c₃, hc₃⟩ := hdiv.1 r
    by_contra hne
    have hpos : 0 < ‖q x‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_natCast_prime_lt_one_qbar l)
    have h := hc₃ q n (fun y => by
      rw [cg_iff_norm_sub_le_norm_pow, hq y, sub_zero, norm_zero]
      exact norm_nonneg _) x
    rw [cg_iff_norm_sub_le_norm_pow, sub_zero, norm_pow] at h
    linarith
  have hIwI : IwI c A Z' := by
    refine ⟨fun r s hs x => (hZ' r s hs).1 x, ?_, ?_⟩
    · intro r s hs t ht x
      have hst : s * t ∈ Ine A := (Ine A).mul_mem hs ht
      have key := inj r (fun y => Z' r (s * t) y -
        (Z' r s y + Z' r t (y * (cycMod ℚ Ω l r s)⁻¹))) ?_ x
      · exact sub_eq_zero.mp key
      · intro y
        beta_reduce
        have e1 := (hZ' r (s * t) hst).2 y
        have e2 := (hZ' r s hs).2 y
        have e3 := (hZ' r t ht).2 (y * (cycMod ℚ Ω l r s)⁻¹)
        rw [mul_right_comm y (cycMod ℚ Ω l r s)⁻¹ (un g hg r)] at e3
        have e4 : μ (s * t) r y = μ s r y + μ t r (y * (cycMod ℚ Ω l r s)⁻¹) := by
          rw [hμ, hμ, hμ, hZcoc r s hs t ht y, map_mul]
          simp only [mul_inv_eq_iff_eq_mul, mul_inv_eq_one, one_mul,
            mul_comm (cycMod ℚ Ω l r t) (cycMod ℚ Ω l r s)]
          split_ifs <;> ring
        linear_combination -e1 + e2 + e3 + e4
    · intro r s hs x
      have key := inj r (fun y => Z' r s y - ∑ x' with red l r x' = y, Z' (r + 1) s x') ?_ x
      · exact sub_eq_zero.mp key
      · intro y
        beta_reduce
        have e1 := (hZ' r s hs).2 y
        have e2 := hμnrm s hs r y
        have e3 : ∑ x' with red l r x' = y * un g hg r, Z' (r + 1) s x' =
            ∑ x' with red l r x' = y, Z' (r + 1) s (x' * un g hg (r + 1)) := by
          symm
          refine Finset.sum_nbij' (· * un g hg (r + 1)) (· * (un g hg (r + 1))⁻¹) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            rw [map_mul, ha, red_un_succ]
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            rw [map_mul, map_inv, ha, red_un_succ, mul_inv_cancel_right]
          · intro a _
            simp
          · intro a _
            simp
          · intro a _
            rfl
        have e4 : ∑ x' with red l r x' = y, μ s (r + 1) x' =
            ∑ x' with red l r x' = y,
              (Z' (r + 1) s (x' * un g hg (r + 1)) - φ ↑g * ↑g ^ k * Z' (r + 1) s x') :=
          Finset.sum_congr rfl (fun x' _ => (hZ' (r + 1) s hs).2 x')
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at e4
        rw [e3]
        linear_combination -e1 + e2 + e4
  have hCont : UpperTheory.Kd.C7.Cont A Z' := by
    intro r n
    obtain ⟨c₃, hc₃⟩ := hdiv.1 r
    obtain ⟨U, hU, hUZ⟩ := hC r (n + c₃)
    refine ⟨U ⊓ (cycMod ℚ Ω l r).ker, ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      refine hU.inter ?_
      have hk' : ((cycMod ℚ Ω l r).ker : Set (G ℚ Ω)) = {s | cycMod ℚ Ω l r s = 1} := by
        ext s
        simp [MonoidHom.mem_ker]
      rw [hk']
      exact isOpen_setOf_cycMod_eq_one l Ω r
    · intro s hs hsI x
      rw [Subgroup.mem_inf] at hs
      obtain ⟨hsU, hsK⟩ := hs
      have hc1 : cycMod ℚ Ω l r s = 1 := hsK
      refine hc₃ (Z' r s) n (fun y => ?_) x
      rw [← (hZ' r s hsI).2 y, hμ, hc1, sub_self, mul_zero, sub_zero]
      have hz := hUZ s hsU hsI y
      rw [cg_iff_norm_sub_le_norm_pow, sub_zero] at hz ⊢
      rw [norm_mul]
      calc ‖(l : Qbar l) ^ c₂‖ * ‖Z r s y‖ ≤ 1 * ‖(l : Qbar l) ^ (n + c₃)‖ :=
            mul_le_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_natCast_prime_lt_one_qbar l).le) hz
              (norm_nonneg _) zero_le_one
        _ = ‖(l : Qbar l) ^ (n + c₃)‖ := one_mul _
  refine ⟨g, hg, c₂, Z', hIwI, hCont, ?_⟩
  intro m s hs x
  obtain ⟨hsI, hsK⟩ := hs
  have hc1 : cycMod ℚ Ω l m s = 1 := hsK
  have e := (hZ' m s hsI).2 x
  rw [hμ, hc1, sub_self, mul_zero, sub_zero] at e
  exact e

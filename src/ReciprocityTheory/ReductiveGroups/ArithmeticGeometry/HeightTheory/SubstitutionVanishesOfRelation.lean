module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZEqConstMulIrreduciblePow

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SubstitutionSplitIrreducibleOf
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PowFirstVarDvdSubstitution
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RelationMapCommTransvection
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

noncomputable def trv {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) :
    MvPolynomial (TVar D N) R →ₐ[R] Polynomial (MvPolynomial (TVar D N) R) :=
  aeval fun t => if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2)) else Polynomial.C (X t)

theorem trv_X {R : Type*} [CommRing R] {D N : ℕ} (i k : Fin (D + 1))
    (e : Polynomial (MvPolynomial (TVar D N) R)) (t : TVar D N) :
    trv i k e (X t) = if t.1 = i then Polynomial.C (X t) + e * Polynomial.C (X (k, t.2))
      else Polynomial.C (X t) := by
  unfold trv
  rw [MvPolynomial.aeval_X]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem relation_map_comm_transvection (c : ι) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    (Polynomial.mapRingHom (d.relationEliminateColumn c).toRingHom).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := Ω c) i k Polynomial.X).toRingHom.comp (d.relationEliminateColumn c).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [trv, Data.relationEliminateColumn]
  · rintro ⟨a, b⟩
    have hC : ∀ x : Ω c, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (C x) = Polynomial.C (C x) := by
      intro x
      simp [trv, Polynomial.algebraMap_apply]
    have hX : ∀ r l, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all
    have hXK : ∀ r l, trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X (X (r, l)) =
        Polynomial.C (X (r, l)) + (if r = i then Polynomial.X * Polynomial.C (X (k, l)) else 0) := by
      intro r l
      rw [trv_X]
      split_ifs <;> simp_all

    set φ : Fin (d.D + 1) → MvPolynomial (TVar d.D d.N) (Ω c) := fun r => d.relationEliminateColumn c (X (r, b)) with hφ
    have hφtrv : ∀ r, trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ r) =
        Polynomial.C (φ r) + (if r = i then Polynomial.X * Polynomial.C (φ k) else 0) := by
      intro r
      by_cases h2 : b = d.jc c
      · have e1 : ∀ r', φ r' = -∑ l ∈ Finset.univ.erase (d.jc c),
            X (r', l) * C (ratio (Ω := Ω c) (d.w l c) (d.w (d.jc c) c)) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, eq_self_iff_true, if_true]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e1 r, e1 k, map_neg, map_sum]
        by_cases h1 : r = i
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [h1, eq_self_iff_true, if_true, map_mul, hX, hC, map_neg, map_sum, add_mul,
            Finset.sum_add_distrib, mul_neg, Finset.mul_sum, mul_assoc, neg_add]
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [h1, if_false, add_zero, map_mul, hX, hC, map_neg, map_sum]
      · have e1 : ∀ r', φ r' = X (r', b) := by
          intro r'
          simp only [hφ, Data.relationEliminateColumn, MvPolynomial.aeval_X, h2, if_false]
        rw [e1 r, e1 k, hX]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_mapRingHom]
    rw [hXK a b]
    change _ = trv (R := Ω c) (D := d.D) (N := d.N) i k Polynomial.X (φ a)
    rw [hφtrv a]
    by_cases h1 : a = i
    · simp only [h1, eq_self_iff_true, if_true, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X]
      rfl
    · simp only [h1, if_false, add_zero, Polynomial.map_C]
      rfl

theorem transvection_fix_generator (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k) :
    trv i k Polynomial.X F0 = Polynomial.C F0 := by
  classical
  have h1 : ∀ n, F0 ∣ (trv i k Polynomial.X F0).coeff n := fun n => (hker _).1 (by
    have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n)
      (congrArg (fun f => f F0) (d.relation_map_comm_transvection c i k hik))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h2
    rw [h2, (hker F0).2 dvd_rfl, map_zero, Polynomial.coeff_zero])
  obtain ⟨R, hR⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 h1
  let Ψ : Polynomial (KTp K d.D d.N) →+* Polynomial (KTp K d.D d.N) :=
    Polynomial.eval₂RingHom (trv i k (-Polynomial.X)).toRingHom Polynomial.X
  have hΨ : Ψ.comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [Ψ, trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X, Ψ]
      split_ifs with h
      · simp [trv_X, h, Ne.symm hik]
      · simp [trv_X, h]
  have hneg : (Polynomial.compRingHom (-Polynomial.X)).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom =
      (trv (R := K) (D := d.D) (N := d.N) i k (-Polynomial.X)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [trv, MvPolynomial.algebraMap_eq]
    · rintro ⟨i', j⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
      split_ifs <;> simp
  have hC0 : (Polynomial.C F0 : Polynomial (KTp K d.D d.N)) ≠ 0 := by simpa using hF0
  have h3 : Polynomial.C F0 = Polynomial.C F0 * (R.comp (-Polynomial.X) * Ψ R) := by
    have e1 := congrArg (fun f => f F0) hΨ
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e1
    rw [hR, map_mul] at e1
    have e2 : Ψ (Polynomial.C F0) = trv i k (-Polynomial.X) F0 := by simp [Ψ]
    have e3 := congrArg (fun f => f F0) hneg
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_compRingHom_apply, hR, Polynomial.mul_comp, Polynomial.C_comp] at e3
    rw [e2, ← e3] at e1
    rw [← mul_assoc]; exact e1.symm
  have h4 : R.comp (-Polynomial.X) * Ψ R = 1 := (mul_left_cancel₀ hC0 (h3.symm.trans (mul_one _).symm))
  obtain ⟨u, hu, hu'⟩ := Polynomial.isUnit_iff.1 (isUnit_iff_exists_inv.2 ⟨_, h4⟩)
  have hRu : R = Polynomial.C u := by
    have e : (R.comp (-Polynomial.X)).comp (-Polynomial.X) = R := by
      rw [Polynomial.comp_assoc]; simp
    rw [← e, ← hu', Polynomial.C_comp]
  have h5 : (trv (R := K) i k Polynomial.X F0).eval 0 = F0 := by
    have : (Polynomial.evalRingHom 0).comp (trv (R := K) (D := d.D) (N := d.N) i k Polynomial.X).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [trv, MvPolynomial.algebraMap_eq]
      · rintro ⟨i', j⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, trv_X]
        split_ifs <;> simp
    exact congrArg (fun f => f F0) this
  rw [hR, hRu, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C] at h5
  have hu1 : u = 1 := mul_left_cancel₀ hF0 (h5.trans (mul_one F0).symm)
  rw [hR, hRu, hu1, map_one, mul_one]

theorem aeval_trv (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : S) :
    aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) F0 = aeval r F0 := by

  set ev : Polynomial (MvPolynomial (TVar d.D d.N) K) →+* S :=
    Polynomial.eval₂RingHom (aeval r : MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom b with hev
  have hcomp : ev.comp (trv (R := K) i k Polynomial.X).toRingHom =
      (aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) :
        MvPolynomial (TVar d.D d.N) K →ₐ[K] S).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hev, trv]
    · intro t
      by_cases h1 : t.1 = i <;> simp [hev, trv, h1] <;> ring
  have h := congrArg (fun φ => φ F0) hcomp
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
  rw [← h, transvection_fix_generator d c F0 hF0 hker i k hik]
  simp [hev]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

theorem aeval_scale_rows {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by
  have key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t =
      l ^ (s.card * d0) * ∏ t, r t ^ m t := by
    intro m hm
    have h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t =
        (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t := by
      intro t
      split_ifs <;> simp [mul_pow]
    simp_rw [h1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc ∑ b, ∑ j, (if b ∈ s then m (b, j) else 0) = ∑ b, (if b ∈ s then d0 else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs with hb
          · exact hF m hm b
          · simp
      _ = s.card * d0 := by
          rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
            smul_eq_mul]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · beta_reduce
    rw [key m hm]
    ring
  · intro i
    simp
  · intro i
    simp

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem aeval_trv_set (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (k : Fin (d.D + 1))
    (s : Finset (Fin (d.D + 1))) (hks : k ∉ s)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : Fin (d.D + 1) → S) :
    aeval (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) F0 = aeval r F0 := by
  classical
  revert hks
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hks
  have hik : i ≠ k := fun h => hks (h ▸ Finset.mem_insert_self _ _)
  have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
  rw [← ih hks', ← d.aeval_trv c F0 hF0 hker i k hik
    (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) (b i)]
  congr 2
  funext t
  by_cases h1 : t.1 = i
  · simp [h1, hi, hks']
  · simp [h1, Finset.mem_insert]

theorem pow_first_var_dvd_substitution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0) :
    (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ^ (d.D * d0) ∣
      bilinearSubstitution F0 := by
  classical
  let S := FractionRing (MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
  let φ : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K] S :=
    IsScalarTower.toAlgHom K _ S
  have hφ : Function.Injective φ := IsFractionRing.injective _ S
  let x : Fin (d.D + 2) → S := fun i => φ (X (Sum.inr i))
  let U : Fin (d.D + 2) → Fin (d.N + 1) → S := fun a j => φ (X (Sum.inl (a, j)))
  have hx : ∀ i, x i ≠ 0 := fun i h0 => X_ne_zero (R := K)
    (Sum.inr i : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) (hφ (h0.trans (map_zero φ).symm))
  have hx1 := hx 1
  let r : TVar d.D d.N → S := fun t => x 0 * U t.1.succ t.2 - x t.1.succ * U 0 t.2
  have hG : φ (bilinearSubstitution F0) = aeval r F0 := by
    rw [bilinearSubstitution, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t; simp [r, x, U]
  let s : Finset (Fin (d.D + 1)) := Finset.univ.erase 0
  have hs : s.card = d.D := by simp [s, Finset.card_erase_of_mem]
  let W : TVar d.D d.N → S := fun t => U t.1.succ t.2 - x t.1.succ / x 1 * U 1 t.2
  have e1 := d.aeval_trv_set c F0 hF0 hker 0 s (by simp [s]) r (fun i => -(x i.succ / x 1))
  have hrows : (fun t : TVar d.D d.N => if t.1 ∈ s then r t + -(x t.1.succ / x 1) * r (0, t.2) else r t) =
      fun t => if t.1 ∈ s then x 0 * (if t.1 ∈ s then W t else r t)
        else (if t.1 ∈ s then W t else r t) := by
    funext t
    split_ifs
    · simp only [r, W, Fin.succ_zero_eq_one]
      linear_combination (x t.1.succ * U 0 t.2) * mul_inv_cancel₀ hx1
    · rfl
  rw [hrows, aeval_scale_rows d0 F0 hmh _ s (x 0), hs] at e1
  have e2 := aeval_scale_rows d0 F0 hmh (fun t => if t.1 ∈ s then W t else r t) s (x 1)
  rw [hs] at e2
  let P : TVar d.D d.N → MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K := fun t =>
    if t.1 ∈ s then X (Sum.inr 1) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (1, t.2))
    else X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))
  have hP : φ (aeval P F0) = aeval (fun t => if t.1 ∈ s then x 1 * (if t.1 ∈ s then W t else r t)
      else (if t.1 ∈ s then W t else r t)) F0 := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t
    simp only [P]
    split_ifs
    · simp only [map_sub, map_mul, W, x, U]
      simp only [x] at hx1
      linear_combination (φ (X (Sum.inr t.1.succ)) * φ (X (Sum.inl (1, t.2)))) * mul_inv_cancel₀ hx1
    · simp [r, x, U]
  have key : φ (X (Sum.inr 1) ^ (d.D * d0) * bilinearSubstitution F0) = φ (X (Sum.inr 0) ^ (d.D * d0) * aeval P F0) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    show x 1 ^ (d.D * d0) * φ (bilinearSubstitution F0) = x 0 ^ (d.D * d0) * φ (aeval P F0)
    rw [hG, ← e1, hP, e2]; ring
  have key' := hφ key
  have hp : Prime (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :=
    MvPolynomial.X_prime
  have hnd : ¬ (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ∣
      X (Sum.inr 1) ^ (d.D * d0) := by
    intro h
    obtain ⟨q, hq⟩ := hp.dvd_of_dvd_pow h
    have := congrArg (MvPolynomial.eval (fun v => if v = Sum.inr 0 then (0 : K) else 1)) hq
    simp at this
  exact hp.pow_dvd_of_dvd_mul_left _ hnd ⟨_, key'⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.EvalOneBilinearSubstitution
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffPsiPNeZero
namespace ReciprocityTheory.ChartRestriction.G.T0.WH

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0

theorem wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem wt_single (v : σ) (e : ℕ) : wt p (Finsupp.single v e) = if p v then e else 0 := by
  simp only [wt]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ v) h

noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiP_monomial (s : σ →₀ ℕ) (a : K) :
    psiP p (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ wt p s := by
  have key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X
      else Polynomial.C (X v)) ^ (s v)
      = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0) := by
    intro v
    split_ifs <;> simp [mul_pow]
  rw [psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]
  ring

theorem psiP_eq_of_isWeightedHomogeneous (n : ℕ) (f : MvPolynomial σ K) (hf : ∀ s ∈ f.support, wt p s = n) :
    psiP p f = Polynomial.C f * Polynomial.X ^ n := by
  have h : ∀ s ∈ f.support, psiP p (monomial s (AddMonoidAlgebra.coeff f s))
      = Polynomial.C (monomial s (AddMonoidAlgebra.coeff f s)) * Polynomial.X ^ n := fun s hs => by
    rw [psiP_monomial, hf s hs]
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]

private theorem psiP_eq_sum_monomial (f : MvPolynomial σ K) :
    psiP p f = ∑ s ∈ f.support, Polynomial.C (monomial s (AddMonoidAlgebra.coeff f s)) * Polynomial.X ^ wt p s := by
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [psiP_monomial]

private theorem coeff_psiP (f : MvPolynomial σ K) (k : ℕ) :
    (psiP p f).coeff k = ∑ s ∈ f.support.filter (fun s => wt p s = k), monomial s (AddMonoidAlgebra.coeff f s) := by
  rw [psiP_eq_sum_monomial, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : wt p s = k
  · subst h
    simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by
  intro h
  have h' := congrArg (AddMonoidAlgebra.coeff · s) h
  rw [coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s] at h'
  · classical
    simp only [coeff_monomial, ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h'
    exact (mem_support_iff.mp hs) h'
  · classical
    intro t _ hts
    rw [coeff_monomial, ite_eq_right hts]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim

theorem hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by
  intro s hs
  by_contra hne
  apply coeff_psiP_ne_zero p f s hs
  rw [hf, Polynomial.coeff_C_mul_X_pow, ite_eq_right hne]

theorem hom_of_dvd (n : ℕ) (H A : MvPolynomial σ K) (hH0 : H ≠ 0)
    (hH : ∀ s ∈ H.support, wt p s = n) (hA : A ∣ H) : ∃ m, ∀ s ∈ A.support, wt p s = m := by
  obtain ⟨B, rfl⟩ := hA
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hH0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hH0
  have hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0 := by
    intro F hF h0
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
    exact coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])
  have hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n := by
    rw [← map_mul]
    exact psiP_eq_of_isWeightedHomogeneous p n _ hH
  have hd := congrArg Polynomial.natDegree hprod
  have ht := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.natDegree_C_mul_X_pow _ _ hH0] at hd
  rw [Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0] at ht
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)
  refine ⟨(psiP p A).natDegree, fun s hs => ?_⟩
  have hc := coeff_psiP_ne_zero p A s hs
  have h3 := Polynomial.le_natDegree_of_ne_zero hc
  have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
  omega

end ReciprocityTheory.ChartRestriction.G.T0.WH
end

namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution

open MvPolynomial

variable {K : Type} [Field K] {D N : ℕ}

abbrev V (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)

noncomputable def ev1 : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => if v = Sum.inr 0 then 1 else X v

noncomputable def thetaS (sgn : K) : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => match v with
    | Sum.inl (a, j) => if a = 0 then X (Sum.inl (a, j))
        else X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j))
    | Sum.inr i => X (Sum.inr i)

private theorem thetaS_X_inr (sgn : K) (i : Fin (D + 2)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [thetaS]

private theorem thetaS_X_inl_zero (sgn : K) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (0, j))) = X (Sum.inl (0, j)) := by
  simp [thetaS]

private theorem thetaS_X_inl_of_ne_zero (sgn : K) {a : Fin (D + 2)} (ha : a ≠ 0) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (a, j))) =
      X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j)) := by
  simp [thetaS, ha]

theorem thetaS_comp (s t : K) (hst : s + t = 0) :
    (thetaS (D := D) (N := N) s).comp (thetaS t) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (⟨a, j⟩ | i)
  · by_cases ha : a = 0
    · subst ha
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_zero]
    · have hC : (C s + C t : MvPolynomial (V D N) K) = 0 := by
        rw [← C_add, hst, C_0]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_of_ne_zero _ ha, map_add (f := _), map_mul,
        thetaS_X_inr, thetaS_X_inl_zero, algHom_C, algebraMap_eq]
      linear_combination
        (X (Sum.inr a) * X (Sum.inl (0, j)) : MvPolynomial (V D N) K) * hC
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inr]

noncomputable def theta : MvPolynomial (V D N) K ≃ₐ[K] MvPolynomial (V D N) K :=
  AlgEquiv.ofAlgHom (thetaS (-1)) (thetaS 1) (thetaS_comp _ _ (by ring)) (thetaS_comp _ _ (by ring))

def iota (p : TVar D N) : V D N := Sum.inl (p.1.succ, p.2)

theorem iota_injective : Function.Injective (iota (D := D) (N := N)) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  simp only [iota, Sum.inl.injEq, Prod.mk.injEq, Fin.succ_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem ev1_X_inr_zero :
    ev1 (K := K) (D := D) (N := N) (X (Sum.inr 0)) = 1 := by
  simp [ev1]

private theorem ev1_X_of_ne_inr_zero {v : V D N} (hv : v ≠ Sum.inr 0) :
    ev1 (K := K) (X v) = X v := by
  simp [ev1, hv]

theorem evalOne_bilinearSubstitution (F : KTp K D N) : ev1 (bilinearSubstitution F) = theta (rename iota F) := by
  have key : (ev1 (K := K) (D := D) (N := N)).comp
      (aeval fun t : ReciprocityTheory.ChartRestriction.G.T0.TVar D N =>
        (X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2)) :
          MvPolynomial (V D N) K)) =
      (thetaS (-1)).comp (rename iota) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, j⟩
    have h1 : (Sum.inl (a.succ, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    have h2 : (Sum.inr a.succ : V D N) ≠ Sum.inr 0 :=
      fun h => Fin.succ_ne_zero a (Sum.inr_injective h)
    have h3 : (Sum.inl (0, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, ev1_X_inr_zero, ev1_X_of_ne_inr_zero h1,
      ev1_X_of_ne_inr_zero h2, ev1_X_of_ne_inr_zero h3, rename_X, iota,
      thetaS_X_inl_of_ne_zero _ (Fin.succ_ne_zero a), map_neg, map_one]
    ring
  exact DFunLike.congr_fun key F

private theorem irreducible_rename_of_injective_height {α β : Type} [Fintype α] {f : α → β}
    (hf : Function.Injective f) {F : MvPolynomial α K} (hF : Irreducible F) :
    Irreducible (rename f F) := by
  have hP : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  have h1 : rename f F = rename ((↑) : Set.range f → β) (renameEquiv K (Equiv.ofInjective f hf) F) := by
    rw [renameEquiv_apply, rename_rename]
    congr 1
  have h2 : Prime (renameEquiv K (Equiv.ofInjective f hf) F) := (MulEquiv.prime_iff _).mpr hP
  rw [h1]
  exact ((prime_rename_iff (Set.range f)).mpr h2).irreducible

theorem irreducible_theta_rename (F : KTp K D N) (hF : Irreducible F) :
    Irreducible (theta (rename (iota (D := D) (N := N)) F)) :=
  (MulEquiv.irreducible_iff (theta (K := K) (D := D) (N := N))).mpr
    (irreducible_rename_of_injective_height iota_injective hF)

end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

namespace LinearSubstitution

variable {K : Type} [Field K] {D N : ℕ}

abbrev isX (v : V D N) : Prop := v.isRight = true

abbrev isU (v : V D N) : Prop := v.isLeft = true

theorem wt_isX (s : V D N →₀ ℕ) : WH.wt isX s = ∑ i, s (Sum.inr i) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isX]

theorem wt_isU (s : V D N →₀ ℕ) : WH.wt isU s = ∑ p, s (Sum.inl p) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isU]

noncomputable def gImg (t : TVar D N) : MvPolynomial (V D N) K :=
  X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))

theorem weightGrading_substitution (p : V D N → Prop) [DecidablePred p]
    (hp : ∀ t : TVar D N, WH.psiP p (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X)
    (F : KTp K D N) (d0 : ℕ) (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F) :
    WH.psiP p (bilinearSubstitution F) = Polynomial.C (bilinearSubstitution F) * Polynomial.X ^ ((D + 1) * d0) := by
  classical
  have hw : ∀ s ∈ F.support, WH.wt (fun _ : TVar D N => True) s = (D + 1) * d0 := by
    intro s hs
    simp only [WH.wt, ↓reduceIte]
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun b _ => hmh s hs b]
    simp
  have e := WH.psiP_eq_of_isWeightedHomogeneous (K := K) (fun _ : TVar D N => True) ((D + 1) * d0) F hw
  have e2 := congrArg (Polynomial.mapAlgHom (aeval fun t : TVar D N => gImg (K := K) t)) e
  have h1 : WH.psiP p (bilinearSubstitution F) =
      aeval (fun t => Polynomial.C (gImg (K := K) t) * Polynomial.X) F := by
    rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl, MvPolynomial.comp_aeval_apply]
    simp only [hp]
  rw [h1]
  unfold WH.psiP at e2
  rw [MvPolynomial.comp_aeval_apply] at e2
  convert e2 using 1
  · refine congrArg (fun f => aeval f F) (funext fun t => ?_)
    simp
  · rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl]
    simp

theorem psiX_g (t : TVar D N) :
    WH.psiP isX (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isX]
  try ring

theorem psiU_g (t : TVar D N) :
    WH.psiP isU (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isU]
  try ring

theorem eq_monomial_of_dehomog_const (A : MvPolynomial (V D N) K) (m : ℕ) (hA : ∀ s ∈ A.support, WH.wt isX s = m)
    (k : K) (h1 : ev1 A = C k) : A = C k * X (Sum.inr 0) ^ m := by
  classical
  have hev1x0 : ev1 (X (Sum.inr 0) : MvPolynomial (V D N) K) = 1 := by simp [ev1]
  have hmono : ∀ (s : V D N →₀ ℕ) (a : K),
      ev1 (monomial s a) = monomial (s.erase (Sum.inr 0)) a := by
    intro s a
    have hs : monomial s a =
        monomial (s.erase (Sum.inr 0)) a * X (Sum.inr 0) ^ (s (Sum.inr 0)) := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
    rw [hs, map_mul, map_pow, hev1x0, one_pow, mul_one, ev1, aeval_monomial, monomial_eq,
      MvPolynomial.algebraMap_eq]
    congr 1
    apply Finsupp.prod_congr
    intro v hv
    rw [if_neg]
    rintro rfl
    simp at hv
  have hcoeff : ∀ u, AddMonoidAlgebra.coeff (ev1 A) u =
      ∑ s ∈ A.support, if s.erase (Sum.inr 0) = u then AddMonoidAlgebra.coeff A s else 0 := by
    intro u
    conv_lhs => rw [A.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hmono, coeff_monomial]
  have hwt : ∀ s : V D N →₀ ℕ,
      WH.wt isX s = WH.wt isX (s.erase (Sum.inr 0)) + s (Sum.inr 0) := by
    intro s
    conv_lhs => rw [← Finsupp.erase_add_single (Sum.inr 0) s]
    rw [WH.wt_add, WH.wt_single, if_pos (show isX (Sum.inr 0 : V D N) from rfl)]
  have hwt0 : WH.wt isX (0 : V D N →₀ ℕ) = 0 := by simp [WH.wt]
  have hinj : ∀ s ∈ A.support, ∀ s' ∈ A.support,
      s.erase (Sum.inr 0) = s'.erase (Sum.inr 0) → s = s' := by
    intro s hs s' hs' he
    have h2 := hwt s
    have h3 := hwt s'
    rw [hA s hs] at h2
    rw [hA s' hs', ← he] at h3
    have h4 : s (Sum.inr 0) = s' (Sum.inr 0) := by omega
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, ← Finsupp.erase_add_single (Sum.inr 0) s', he, h4]
  have hsingle : ∀ s ∈ A.support, s.erase (Sum.inr 0) = 0 → s = Finsupp.single (Sum.inr 0) m := by
    intro s hs hs0
    have h2 := hwt s
    rw [hA s hs, hs0, hwt0, zero_add] at h2
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, hs0, zero_add, ← h2]
  ext u
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hu : u ∈ A.support
  · have e := hcoeff (u.erase (Sum.inr 0))
    rw [Finset.sum_eq_single u (fun s hs hne => if_neg (fun h => hne (hinj s hs u hu h)))
      (fun h => absurd hu h), if_pos rfl, h1, coeff_C] at e
    rw [← e]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · have h0 : 0 = u.erase (Sum.inr 0) := by
        rw [← h]
        simp
      rw [if_pos h0, if_pos h, mul_one]
    · have h0 : ¬ 0 = u.erase (Sum.inr 0) := fun h0 => h (hsingle u hu h0.symm).symm
      rw [if_neg h0, if_neg h, mul_zero]
  · have hu0 : AddMonoidAlgebra.coeff A u = 0 := by simpa using hu
    rw [hu0]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · rw [if_pos h, mul_one]
      have e := hcoeff 0
      rw [h1, coeff_C, if_pos rfl] at e
      rw [e]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg]
      intro hs0
      apply hu
      rw [← h, ← hsingle s hs hs0]
      exact hs
    · rw [if_neg h, mul_zero]

end LinearSubstitution

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem substitution_split_irreducible_of (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := by
  classical
  have hF0 : F0 ≠ 0 := hirr.ne_zero
  have hirr1 : Irreducible (LinearSubstitution.ev1 (bilinearSubstitution F0)) := by
    rw [LinearSubstitution.evalOne_bilinearSubstitution]
    exact LinearSubstitution.irreducible_theta_rename F0 hirr
  have hg0 : bilinearSubstitution F0 ≠ 0 := fun h => hirr1.ne_zero (by rw [h, map_zero])
  have hX : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isX s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isX _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isX LinearSubstitution.psiX_g F0 d0 hmh)
  have hU : ∀ s ∈ (bilinearSubstitution F0).support, WH.wt LinearSubstitution.isU s = (d.D + 1) * d0 :=
    WH.hom_of_psiP LinearSubstitution.isU _ _ (LinearSubstitution.weightGrading_substitution LinearSubstitution.isU LinearSubstitution.psiU_g F0 d0 hmh)
  have hev : LinearSubstitution.ev1 (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) = 1 := by simp [LinearSubstitution.ev1]
  have hbound : ∀ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 →
      a ≤ (bilinearSubstitution F0).totalDegree := by
    rintro a ⟨h, hh⟩
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hh, mul_zero])
    rw [hh, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) hh0, totalDegree_X_pow]
    omega
  obtain ⟨a, hPa, hle, hnot⟩ : ∃ a, (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0 ∧
      d.D * d0 ≤ a ∧ ¬ (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ (a + 1) ∣ bilinearSubstitution F0 := by
    have hP0 := d.pow_first_var_dvd_substitution c F0 hF0 hker d0 hmh
    exact ⟨Nat.findGreatest (fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
      (bilinearSubstitution F0).totalDegree,
      Nat.findGreatest_spec (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      Nat.le_findGreatest (P := fun a => (X (Sum.inr 0) : MvPolynomial (LinearSubstitution.V d.D d.N) K) ^ a ∣ bilinearSubstitution F0)
        (hbound _ hP0) hP0,
      fun h => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ h) h⟩
  obtain ⟨F1, hF1⟩ := hPa
  have hF10 : F1 ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hF1, mul_zero])
  have hev1 : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 F1 := by
    rw [hF1, map_mul, map_pow, hev, one_pow, one_mul]
  have hdvdF1 : F1 ∣ bilinearSubstitution F0 := ⟨X (Sum.inr 0) ^ a, by rw [hF1, mul_comm]⟩
  obtain ⟨deF, hdeF⟩ := WH.hom_of_dvd LinearSubstitution.isX ((d.D + 1) * d0) (bilinearSubstitution F0) F1 hg0 hX hdvdF1
  have hshift : ∀ s ∈ F1.support, s + Finsupp.single (Sum.inr 0) a ∈ (bilinearSubstitution F0).support := by
    intro s hs
    rw [mem_support_iff, hF1, mul_comm, X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    exact mem_support_iff.1 hs
  refine ⟨a, F1, deF, hF1, ⟨fun hu => ?_, fun G H hGH => ?_⟩, ?_, ?_, ?_⟩
  · exact hirr1.not_isUnit (by rw [hev1]; exact hu.map _)
  · have hmul : LinearSubstitution.ev1 (bilinearSubstitution F0) = LinearSubstitution.ev1 G * LinearSubstitution.ev1 H := by rw [hev1, hGH, map_mul]
    have key : ∀ G' : MvPolynomial (LinearSubstitution.V d.D d.N) K, G' ∣ F1 → IsUnit (LinearSubstitution.ev1 G') → IsUnit G' := by
      intro G' hG' hu
      obtain ⟨k, hk, hkG⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
      obtain ⟨m, hm⟩ := WH.hom_of_dvd LinearSubstitution.isX _ (bilinearSubstitution F0) G' hg0 hX (hG'.trans hdvdF1)
      have hG'eq := LinearSubstitution.eq_monomial_of_dehomog_const G' m hm k hkG
      cases m with
      | zero =>
        rw [hG'eq, pow_zero, mul_one]
        exact hk.map C
      | succ m =>
        exfalso
        apply hnot
        obtain ⟨Q, hQ⟩ := hG'
        refine ⟨C k * X (Sum.inr 0) ^ m * Q, ?_⟩
        rw [hF1, hQ, hG'eq]
        ring
    rcases hirr1.isUnit_or_isUnit hmul with h | h
    · exact Or.inl (key G ⟨H, hGH⟩ h)
    · exact Or.inr (key H ⟨G, by rw [hGH, mul_comm]⟩ h)
  · intro s hs
    rw [← LinearSubstitution.wt_isX]
    exact hdeF s hs
  · obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hF10
    have hs' : s ∈ F1.support := mem_support_iff.2 hs
    have h := hX _ (hshift s hs')
    rw [WH.wt_add, WH.wt_single, if_pos (show LinearSubstitution.isX (Sum.inr 0 : LinearSubstitution.V d.D d.N) from rfl),
      hdeF s hs'] at h
    have h2 : (d.D + 1) * d0 = d.D * d0 + d0 := by ring
    linarith
  · intro s hs
    have h := hU _ (hshift s hs)
    rw [WH.wt_add, WH.wt_single, if_neg (by simp [LinearSubstitution.isU]), add_zero] at h
    rw [← LinearSubstitution.wt_isU]
    exact h.le

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem ratio_self' {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have hex : ∃ a : Ω, f = a • f := ⟨1, (one_smul Ω f).symm⟩
  unfold ratio
  rw [dite_eq_left hex]
  have hs := hex.choose_spec
  have h0 : (hex.choose - 1) • f = 0 := by rw [sub_smul, ← hs, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hf

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineRowCombination (c : ι) (a : Fin (d.D + 2)) : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  ∑ k, X (a, k) * C (d.affineCoord c k)

noncomputable def pluckerSubstitution (c : ι) :
    MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  aeval fun t => d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2)

theorem substitution_comp_relation (hd : d.AxH 𝒜) (c : ι) :
    (d.linearSubstitution c).comp (MvPolynomial.aeval (fun t : TVar d.D d.N =>
      (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
        MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)) :
          MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K))) =
      ((d.pluckerSubstitution c).restrictScalars K).comp (d.relationEliminateColumn c) := by
  have hy : d.affineCoord c (d.jc c) = 1 := ratio_self' (hd.w_base c)
  have hs : ∀ a, d.affineRowCombination c a = ∑ k, X (a, k) * C (d.affineCoord c k) := fun a => rfl
  have hphi_inl : ∀ p, d.linearSubstitution c (X (Sum.inl p)) = X p := by
    intro p
    simp [Data.linearSubstitution]
  have hphi_inr : ∀ i, d.linearSubstitution c (X (Sum.inr i)) = d.affineRowCombination c i := by
    intro i
    simp [Data.linearSubstitution, Data.affineRowCombination]
  have hrho : ∀ t : TVar d.D d.N, d.pluckerSubstitution c (X t) =
      d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2) := by
    intro t
    simp [Data.pluckerSubstitution]
  apply MvPolynomial.algHom_ext
  intro t
  simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, hphi_inl, hphi_inr,
    AlgHom.restrictScalars_apply]
  simp only [Data.relationEliminateColumn, aeval_X]
  split_ifs with ht
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_mul, hrho, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

    have htot : ∑ k, (d.affineRowCombination c 0 * X (t.1.succ, k) - d.affineRowCombination c t.1.succ * X (0, k)) *
        C (d.affineCoord c k) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ← hs]
      ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c)), hy, map_one, mul_one] at htot
    have hC : ∀ r, d.pluckerSubstitution c (C r) = C r := fun r => by simp [Data.pluckerSubstitution]
    have hyd : ∀ k, ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c) = d.affineCoord c k := fun k => rfl
    simp only [hC, hyd]
    rw [ht]
    linear_combination htot
  · rw [hrho]

theorem substitution_vanishes_of_relation (hd : d.AxH 𝒜) (c : ι) (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) :
    d.linearSubstitution c (bilinearSubstitution Q) = 0 := by
  have h := congrArg (fun φ => φ Q) (d.substitution_comp_relation hd c)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hQ, map_zero] at h
  exact h

theorem substitution_split_irreducible (hd : d.AxH 𝒜) (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := d.substitution_split_irreducible_of c F0 hirr d0 hmh hker

end Data

end ReciprocityTheory.ChartRestriction.G.T0

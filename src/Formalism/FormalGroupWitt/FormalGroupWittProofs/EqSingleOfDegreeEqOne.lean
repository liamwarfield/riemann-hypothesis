module

public import Formalism.FormalGroupWitt.SubstInjectiveV

@[expose] public section

section -- merged from Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
noncomputable section

universe u v w

namespace Formalism.FG

namespace InjVAux

open MvPowerSeries

variable {R : Type*} [CommRing R] {τ : Type*}

def HasOrd (n : ℕ) (z : MvPowerSeries τ R) : Prop :=
  ∀ d : τ →₀ ℕ, d.degree < n → coeff d z = 0

theorem hasOrd_zero_left (z : MvPowerSeries τ R) : HasOrd 0 z :=
  fun _ hd => absurd hd (Nat.not_lt_zero _)

theorem hasOrd_zero (n : ℕ) : HasOrd n (0 : MvPowerSeries τ R) := fun _ _ => by simp

theorem HasOrd.mono {m n : ℕ} {z : MvPowerSeries τ R} (h : HasOrd n z) (hmn : m ≤ n) :
    HasOrd m z :=
  fun d hd => h d (lt_of_lt_of_le hd hmn)

theorem HasOrd.add {n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd n x) (hy : HasOrd n y) :
    HasOrd n (x + y) :=
  fun d hd => by rw [map_add (f := _), hx d hd, hy d hd, add_zero]

theorem HasOrd.sub {n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd n x) (hy : HasOrd n y) :
    HasOrd n (x - y) :=
  fun d hd => by rw [map_sub, hx d hd, hy d hd, sub_zero]

theorem HasOrd.mul {m n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd m x) (hy : HasOrd n y) :
    HasOrd (m + n) (x * y) := by
  classical
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' : p.1 + p.2 = d := by simpa using hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add (f := _), hp']
  by_cases h1 : p.1.degree < m
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]

def Good (N k : ℕ) (x x' : MvPowerSeries τ R) : Prop :=
  HasOrd k x ∧ HasOrd k x' ∧ HasOrd (N + k) (x - x')

theorem good_one (N : ℕ) : Good N 0 (1 : MvPowerSeries τ R) 1 :=
  ⟨hasOrd_zero_left _, hasOrd_zero_left _, by rw [sub_self]; exact hasOrd_zero _⟩

theorem Good.mul {N k l : ℕ} {x x' y y' : MvPowerSeries τ R} (hx : Good N k x x')
    (hy : Good N l y y') : Good N (k + l) (x * y) (x' * y') := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨hx1.mul hy1, hx2.mul hy2, ?_⟩
  have e : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [e]
  exact ((hx1.mul hy3).mono (by omega)).add ((hx3.mul hy2).mono (by omega))

theorem Good.pow {N k : ℕ} {x x' : MvPowerSeries τ R} (hx : Good N k x x') (n : ℕ) :
    Good N (k * n) (x ^ n) (x' ^ n) := by
  induction n with
  | zero => simpa using good_one N
  | succ n ih => rw [pow_succ, pow_succ, Nat.mul_succ]; exact ih.mul hx

theorem good_prod {N : ℕ} {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (x x' : ι → MvPowerSeries τ R) (h : ∀ i ∈ s, Good N (k i) (x i) (x' i)) :
    Good N (∑ i ∈ s, k i) (∏ i ∈ s, x i) (∏ i ∈ s, x' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one N
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem eq_single_of_degree_eq_one {ι : Type*} [Fintype ι] (e : ι →₀ ℕ)
    (he : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  rw [Finsupp.degree_eq_sum] at he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    rw [Finset.sum_eq_zero (fun k _ => hc k)] at he
    exact zero_ne_one he
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => e k) (Finset.mem_univ i)
  rw [he] at hsplit
  have hei : e i = 1 := by omega
  refine ⟨i, ?_⟩
  ext k
  by_cases hk : k = i
  · subst hk; simp [hei]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hk)]
    have : e k ≤ ∑ x ∈ Finset.univ.erase i, e x :=
      Finset.single_le_sum (f := fun x => e x) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    omega

theorem hasOrd_one_of_cc {z : MvPowerSeries τ R} (hz : constantCoeff z = 0) : HasOrd 1 z := by
  intro d hd
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst this
  simpa using hz

theorem main {ι : Type*} [Fintype ι] [DecidableEq ι] [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R) (hf : IsIdMod2 f)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ j, subst a (f j) = subst b (f j)) :
    ∀ N, ∀ i, HasOrd (N + 1) (a i - b i) := by
  have haS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero hb
  intro N
  induction N with
  | zero => intro i; exact (hasOrd_one_of_cc (ha i)).sub (hasOrd_one_of_cc (hb i))
  | succ N ih =>
    intro j d hd
    have hgood : ∀ i, Good N 1 (a i) (b i) :=
      fun i => ⟨hasOrd_one_of_cc (ha i), hasOrd_one_of_cc (hb i), ih i⟩
    have hj := congrArg (coeff d) (h j)
    rw [coeff_subst haS, coeff_subst hbS] at hj
    have hdiff := congrArg (fun t => t - finsum (fun e : ι →₀ ℕ =>
      coeff e (f j) • coeff d (e.prod fun s n => b s ^ n))) hj
    simp only [sub_self] at hdiff
    rw [← finsum_sub_distrib (coeff_subst_finite haS (f j) d)
      (coeff_subst_finite hbS (f j) d)] at hdiff
    rw [finsum_eq_single _ (Finsupp.single j 1)] at hdiff
    · rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
        hf.2 j j, if_pos rfl, one_smul, one_smul, pow_one, pow_one] at hdiff
      rw [map_sub, hdiff]
    · intro e he
      rw [← smul_sub, ← map_sub]
      rcases Nat.lt_or_ge e.degree 2 with hlt | hge
      · rcases Nat.lt_or_ge e.degree 1 with h0 | h1
        · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
          subst this
          simp
        · obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one e (by omega)
          have hij : i ≠ j := fun hij => he (by rw [hij])
          rw [hf.2 j i, if_neg hij, zero_smul]
      · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        have hg := good_prod Finset.univ (fun i => 1 * e i) (fun i => a i ^ e i)
          (fun i => b i ^ e i) (fun i _ => (hgood i).pow (e i))
        have hsum : ∑ i ∈ Finset.univ, 1 * e i = e.degree := by
          rw [Finsupp.degree_eq_sum]; simp
        rw [hsum] at hg
        rw [hg.2.2.mono (n := N + e.degree) (by omega) d hd, smul_zero]

end InjVAux

open MvPowerSeries in
theorem subst_injective_vector : Formalism.FG.SubstInjectiveV.{u, v, w} := by
  intro R _ ι _ _ τ _ f a b hf ha hb h
  funext i
  ext d
  have := InjVAux.main f a b hf ha hb h d.degree i d (by omega)
  rwa [map_sub, sub_eq_zero] at this

end Formalism.FG
end
end

section -- merged from Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector
noncomputable section

universe u v w

namespace Formalism.FG.IntegralSubstitution

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem integral_mul {A B : MvPowerSeries τ K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) (hB _)

theorem integral_one : IntegralMv (1 : MvPowerSeries τ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_pow {A : MvPowerSeries τ K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv (A ^ n) := by
  induction n with
  | zero => simpa using integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hA

theorem integral_finsuppProd {ι : Type v} (a : ι → MvPowerSeries τ K) (ha : ∀ i, IntegralMv (a i))
    (n : ι →₀ ℕ) : IntegralMv (n.prod fun s e => (a s) ^ e) := by
  classical
  unfold Finsupp.prod
  exact Finset.prod_induction _ (fun x => IntegralMv x) (fun _ _ hx hy => integral_mul hx hy)
    integral_one (fun i _ => integral_pow (ha i) _)

theorem integralSubstV {ι : Type v} [Finite ι] (g : MvPowerSeries ι K)
    (a : ι → MvPowerSeries τ K) (hg : IntegralMv g)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntegralMv (a i)) :
    IntegralMv (MvPowerSeries.subst a g) := by
  intro d
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst hs g d]
  have hfin := MvPowerSeries.coeff_subst_finite hs g d
  rw [finsum_eq_sum _ hfin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hg n) (norm_nonneg _) (integral_finsuppProd a ha n d)

end Formalism.FG.IntegralSubstitution

theorem Formalism.FG.integral_subst_vector : Formalism.FG.IntegralSubstV.{u, v, w} :=
  fun _ _ _ _ _ _ g a hg ha0 ha => Formalism.FG.IntegralSubstitution.integralSubstV g a hg ha0 ha
end
end

section -- merged from Formalism.FormalGroupWitt.FormalGroupWittProofs.FrobSqV
noncomputable section

namespace Formalism.FG

open Formalism.G

namespace PadicFrobeniusSquare

theorem padicInt_norm_le_p {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have h1 : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hy
  rw [PadicInt.ker_toZMod] at h1
  have h2 : ‖y‖ < 1 := PadicInt.mem_nonunits.1 ((IsLocalRing.mem_maximalIdeal _).1 h1)
  obtain ⟨z, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h2
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

end PadicFrobeniusSquare

theorem frobenius_lift_padic_square : Formalism.FG.FrobLiftPadicSq := by
  intro l _
  refine ⟨Fact.out, ⟨2, two_pos, rfl⟩, Padic.norm_p_lt_one, ?_⟩
  intro a ha
  have hz : ∀ z : ZMod l, z ^ l ^ 2 = z := fun z => by
    rw [pow_two, pow_mul, ZMod.pow_card, ZMod.pow_card]
  let y : ℤ_[l] := ⟨a, ha⟩
  have h := PadicFrobeniusSquare.padicInt_norm_le_p (y - y ^ l ^ 2) (by rw [map_sub, map_pow, hz, sub_self])
  rw [PadicInt.norm_def, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_natCast] at h
  show ‖a - a ^ l ^ 2‖ ≤ ‖(l : ℚ_[l])‖
  exact h

end Formalism.FG
end
end

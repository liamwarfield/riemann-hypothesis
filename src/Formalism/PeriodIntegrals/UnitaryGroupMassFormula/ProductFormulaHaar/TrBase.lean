module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase
noncomputable section

open IsDedekindDomain NumberField TensorProduct ValuativeRel

namespace PI.ProdFormulaE.Tr

structure LocFam (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) where
  P : ι → HeightOneSpectrum (𝓞 F)
  K : ι → Type
  [fld : ∀ i, Field (K i)]
  [vr : ∀ i, ValuativeRel (K i)]
  [top : ∀ i, TopologicalSpace (K i)]
  [lf : ∀ i, IsNonarchimedeanLocalField (K i)]
  [cz : ∀ i, CharZero (K i)]
  [alg : ∀ i, Algebra ℚ_[ℓ] (K i)]
  cont : ∀ i, Continuous (algebraMap ℚ_[ℓ] (K i))
  [fin : ∀ i, FiniteDimensional ℚ_[ℓ] (K i)]
  ιF : ∀ i, F →+* K i
  dense : ∀ i, DenseRange (ιF i)
  val : ∀ i (x y : F), (ιF i x ≤ᵥ ιF i y) ↔ (P i).valuation F x ≤ (P i).valuation F y

attribute [instance] LocFam.fld LocFam.vr LocFam.top LocFam.lf LocFam.cz LocFam.alg LocFam.fin

variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

def LocFam.Over (D : LocFam F ℓ ι) : Prop :=
  Function.Injective D.P ∧ ∀ p, p ∈ Set.range D.P ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal)

def LocFam.Φ (D : LocFam F ℓ ι) : ℚ_[ℓ] ⊗[ℚ] F →ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[ℓ] _) (AlgHom.pi fun i => (D.ιF i).toRatAlgHom)
    (fun _ _ => Commute.all _ _)

theorem LocFam.Φ_tmul (D : LocFam F ℓ ι) (c : ℚ_[ℓ]) (x : F) (i : ι) :
    D.Φ (c ⊗ₜ x) i = algebraMap ℚ_[ℓ] (D.K i) c * D.ιF i x := by
  simp [LocFam.Φ, Algebra.ofId_apply]

def TrSurj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → Function.Surjective D.Φ

def TrInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → Function.Injective D.Φ

def TrSum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → ∀ y : F,
      ∑ i, Algebra.trace ℚ_[ℓ] (D.K i) (D.ιF i y) = algebraMap ℚ ℚ_[ℓ] (Algebra.trace ℚ F y)

end PI.ProdFormulaE.Tr
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod
noncomputable section

open MeasureTheory ValuativeRel NumberField IsDedekindDomain
open scoped NumberField

namespace PI.ProdFormulaE


open scoped Classical in
def modF (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    (a : K) : ℝ := by
  classical
  exact if h : a = 0 then 0 else ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ)

section

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

theorem modF_zero : modF K 0 = 0 := by
  unfold modF
  rw [dite_eq_left rfl]

theorem modF_of_ne {a : K} (h : a ≠ 0) :
    modF K a = ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ) := by
  unfold modF
  rw [dite_eq_right h]

theorem modF_pos {a : K} (h : a ≠ 0) : 0 < modF K a := by
  rw [modF_of_ne h]
  have hu : IsUnit (distribHaarChar K (Units.mk0 a h)) := (Group.isUnit (Units.mk0 a h)).map (distribHaarChar K)
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)

theorem modF_mul (a b : K) : modF K (a * b) = modF K a * modF K b := by
  by_cases ha : a = 0
  · subst ha; simp [modF_zero]
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb]
  have hu : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb := by
    ext; simp
  rw [hu, map_mul, NNReal.coe_mul]

theorem modF_one : modF K 1 = 1 := by
  rw [modF_of_ne one_ne_zero]
  have hu : Units.mk0 (1 : K) one_ne_zero = 1 := by
    ext; simp
  rw [hu, map_one, NNReal.coe_one]

theorem modF_div (a b : K) : modF K (a / b) = modF K a / modF K b := by
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  have hm : modF K (a / b) * modF K b = modF K a := by
    rw [← modF_mul, div_mul_cancel₀ a hb]
  rw [eq_div_iff (modF_pos hb).ne']
  exact hm

end

def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (t : 𝒪[K]), t ≠ 0 →
      modF K (t : K) * (Nat.card (𝒪[K] ⧸ Ideal.span {t}) : ℝ) = 1


def CardStep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι → (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ (a : 𝓞 F), a ≠ 0 → ∀ t : 𝒪[K], (t : K) = ι (a : F) →
      Nat.card (𝒪[K] ⧸ Ideal.span {t}) = Ideal.absNorm (p.maxPowDividing (Ideal.span {a}))

end PI.ProdFormulaE
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.DenEqOneOfForallPadicNormLeOne
noncomputable section

open Finset

namespace PI.ProdFormulaE.Frac

private theorem padicNorm_le_one_iff_not_dvd_den {q : ℕ} [Fact q.Prime] (r : ℚ) :
    padicNorm q r ≤ 1 ↔ ¬ q ∣ r.den := by
  have hmul : padicNorm q r * padicNorm q (r.den : ℚ) = padicNorm q (r.num : ℚ) := by
    rw [← padicNorm.mul, Rat.mul_den_eq_num]
  constructor
  · intro h hd
    have h1 : padicNorm q (r.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).2 hd
    have h2 : padicNorm q (r.num : ℚ) < 1 := by
      rw [← hmul]
      calc padicNorm q r * padicNorm q (r.den : ℚ) ≤ 1 * padicNorm q (r.den : ℚ) :=
            mul_le_mul_of_nonneg_right h (padicNorm.nonneg _)
        _ < 1 := by rw [one_mul]; exact h1
    have h4 : q ∣ r.num.natAbs := Int.natCast_dvd.1 ((padicNorm.int_lt_one_iff _).1 h2)
    have h5 := Nat.dvd_gcd h4 hd
    rw [r.reduced.gcd_eq_one] at h5
    exact (Nat.Prime.not_dvd_one Fact.out) h5
  · intro hd
    have h1 : padicNorm q (r.den : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).2 hd
    rw [h1, mul_one] at hmul
    rw [hmul]
    exact padicNorm.of_int _

theorem padicNorm_le_one_of_den_pow {q l : ℕ} [hq : Fact q.Prime] (hl : l.Prime) (hne : l ≠ q)
    {a : ℚ} {n : ℕ} (ha : a.den = l ^ n) : padicNorm q a ≤ 1 := by
  rw [padicNorm_le_one_iff_not_dvd_den, ha]
  intro h
  exact hne ((Nat.prime_dvd_prime_iff_eq hq.out hl).1 (hq.out.dvd_of_dvd_pow h)).symm

theorem den_eq_one_of_forall_padicNorm_le_one {r : ℚ}
    (h : ∀ q : ℕ, q.Prime → padicNorm q r ≤ 1) : r.den = 1 := by
  by_contra hd
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
  haveI : Fact q.Prime := ⟨hq⟩
  exact (padicNorm_le_one_iff_not_dvd_den r).1 (h q hq) hqd

theorem padicNorm_le_one_of_den_eq_one {q : ℕ} [Fact q.Prime] {a : ℚ} (ha : a.den = 1) :
    padicNorm q a ≤ 1 := by
  rw [padicNorm_le_one_iff_not_dvd_den, ha]
  exact Nat.Prime.not_dvd_one Fact.out

theorem padicNorm_add_le_one {q : ℕ} [Fact q.Prime] {a b : ℚ} (ha : padicNorm q a ≤ 1)
    (hb : padicNorm q b ≤ 1) : padicNorm q (a + b) ≤ 1 := le_trans padicNorm.nonarchimedean (max_le ha hb)

theorem padicNorm_sub_le_one {q : ℕ} [Fact q.Prime] {a b : ℚ} (ha : padicNorm q a ≤ 1)
    (hb : padicNorm q b ≤ 1) : padicNorm q (a - b) ≤ 1 := by
  exact le_trans padicNorm.sub (max_le ha hb)

theorem den_sub_sum_eq_one {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (I : Finset ι) (hI : ∀ i, i ∉ I → (a i).den = 1)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (t - ∑ i ∈ I, a i).den = 1 := by
  classical
  apply den_eq_one_of_forall_padicNorm_le_one
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  have hsum : ∀ s : Finset ι, (∀ i ∈ s, padicNorm q (a i) ≤ 1) →
      padicNorm q (∑ i ∈ s, a i) ≤ 1 :=
    fun s hs => Finset.sum_induction _ (fun x => padicNorm q x ≤ 1)
      (fun x y hx hy => padicNorm_add_le_one hx hy) (by simp) hs
  have h1 : padicNorm q (∑ i ∈ fib q \ I, a i) ≤ 1 :=
    hsum _ (fun i hi => padicNorm_le_one_of_den_eq_one (hI i (Finset.mem_sdiff.1 hi).2))
  have h2 : padicNorm q (∑ i ∈ I \ fib q, a i) ≤ 1 := hsum _ (fun i hi => by
    obtain ⟨n, hn⟩ := ha i
    have hne : ℓ i ≠ q := fun h => (Finset.mem_sdiff.1 hi).2 ((hfib i q).2 h)
    exact padicNorm_le_one_of_den_pow (hℓ i) hne hn)
  have e : t - ∑ i ∈ I, a i =
      (t - ∑ i ∈ fib q, a i) + (∑ i ∈ fib q \ I, a i - ∑ i ∈ I \ fib q, a i) := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]
    ring
  rw [e]
  exact padicNorm_add_le_one (ht q hq) (padicNorm_sub_le_one h1 h2)

theorem exp_two_pi_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem exp_two_pi_of_den_eq_one {a : ℚ} (ha : a.den = 1) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 := by
  have h : (a : ℂ) = ((a.num : ℤ) : ℂ) := by
    calc (a : ℂ) = (((a.num : ℤ) : ℚ) : ℂ) :=
          congrArg (fun x : ℚ => (x : ℂ)) (Rat.coe_int_num_of_den_eq_one ha).symm
      _ = ((a.num : ℤ) : ℂ) := Rat.cast_intCast _
  rw [h]
  exact exp_two_pi_int _

theorem finprod_exp_of_padicNorm {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (hfin : {i | (a i).den ≠ 1}.Finite)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))).Finite ∧
    ∏ᶠ i, Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  classical
  set I := hfin.toFinset with hIdef
  have hI : ∀ i, i ∉ I → (a i).den = 1 := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hsub : (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))) ⊆
      (I : Set ι) := by
    intro i hi
    by_contra h
    exact hi (exp_two_pi_of_den_eq_one (hI i h))
  refine ⟨I.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Complex.exp_sum]
  have h1 := exp_two_pi_of_den_eq_one (den_sub_sum_eq_one ℓ hℓ a ha fib hfib I hI t ht)
  have key : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      2 * Real.pi * Complex.I * (((t - ∑ i ∈ I, a i : ℚ)) : ℂ) +
        ∑ i ∈ I, 2 * Real.pi * Complex.I * (a i : ℂ) := by
    push_cast
    rw [← Finset.mul_sum]
    ring
  rw [key, Complex.exp_add, h1, one_mul]

theorem finprod_exp {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (hfin : {i | (a i).den ≠ 1}.Finite) (t : ℚ)
    (ht : ∀ (q : ℕ) [Fact q.Prime], ‖(t : ℚ_[q]) - ∑ i ∈ fib q, (a i : ℚ_[q])‖ ≤ 1) :
    (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))).Finite ∧
    ∏ᶠ i, Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  refine finprod_exp_of_padicNorm ℓ hℓ a ha fib hfib hfin t ?_
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  have h := ht q
  have e : ‖((t - ∑ i ∈ fib q, a i : ℚ) : ℚ_[q])‖ = _ := Padic.eq_padicNorm (t - ∑ i ∈ fib q, a i)
  have h' : ((padicNorm q (t - ∑ i ∈ fib q, a i) : ℚ) : ℝ) ≤ 1 := by
    rw [← e]
    push_cast
    exact h
  exact_mod_cast h'

theorem den_eq_one_of_norm_le_one {l : ℕ} [hl : Fact l.Prime] {a : ℚ} {n : ℕ}
    (ha : a.den = l ^ n) {T : ℚ_[l]} (hT : ‖T‖ ≤ 1) (hTa : ‖T - (a : ℚ_[l])‖ ≤ 1) :
    a.den = 1 := by
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := by
    have e : (a : ℚ_[l]) = T + -(T - (a : ℚ_[l])) := by ring
    rw [e]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hT ?_)
    rw [norm_neg]
    exact hTa
  have h2 : padicNorm l a ≤ 1 := by
    have e : ‖((a : ℚ) : ℚ_[l])‖ = _ := Padic.eq_padicNorm a
    have h' : ((padicNorm l a : ℚ) : ℝ) ≤ 1 := by
      rw [← e]
      exact h1
    exact_mod_cast h'
  have h3 := (padicNorm_le_one_iff_not_dvd_den a).1 h2
  rw [ha] at h3 ⊢
  rcases n with _ | n
  · simp
  · exact absurd (dvd_pow_self l (Nat.succ_ne_zero n)) h3

theorem norm_sum_sub_sum_le_one {q : ℕ} [Fact q.Prime] {ι : Type*} (s : Finset ι)
    (T b : ι → ℚ_[q]) (h : ∀ i ∈ s, ‖T i - b i‖ ≤ 1) :
    ‖∑ i ∈ s, T i - ∑ i ∈ s, b i‖ ≤ 1 := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_induction _ (fun x : ℚ_[q] => ‖x‖ ≤ 1)
    (fun x y hx hy => le_trans (Padic.nonarchimedean x y) (max_le hx hy)) (by simp) h

end PI.ProdFormulaE.Frac
end
end

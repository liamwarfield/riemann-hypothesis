module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.ExtCContract
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

theorem exists_linearForm_one : ∃ ℓ : ℂ →ₗ[ℚ] ℚ, ℓ 1 = 1 := by
  have h : ¬ ∀ φ : Module.Dual ℚ ℂ, φ 1 = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact one_ne_zero
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨(φ 1)⁻¹ • φ, by simp [hφ]⟩

noncomputable def projQ (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) : MvPolynomial σ ℚ :=
  ∑ m ∈ q.support, monomial m (ℓ (AddMonoidAlgebra.coeff q m))

theorem coeff_projQ (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (projQ ℓ q) m = ℓ (AddMonoidAlgebra.coeff q m) := by
  classical
  rw [projQ, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, map_zero]

theorem projQ_add (ℓ : ℂ →ₗ[ℚ] ℚ) (a b : MvPolynomial σ ℂ) :
    projQ ℓ (a + b) = projQ ℓ a + projQ ℓ b := by
  ext m
  simp [coeff_projQ]

theorem projQ_zero (ℓ : ℂ →ₗ[ℚ] ℚ) : projQ ℓ (0 : MvPolynomial σ ℂ) = 0 := by
  ext m
  simp [coeff_projQ]

theorem projQ_map (ℓ : ℂ →ₗ[ℚ] ℚ) (hℓ : ℓ 1 = 1) (g : MvPolynomial σ ℚ) :
    projQ ℓ (MvPolynomial.map (algebraMap ℚ ℂ) g) = g := by
  ext m
  rw [coeff_projQ, coeff_map]
  have : algebraMap ℚ ℂ (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • (1 : ℂ) := by
    rw [Algebra.smul_def, mul_one]
  rw [this, map_smul, hℓ, smul_eq_mul, mul_one]

theorem projQ_map_mul (ℓ : ℂ →ₗ[ℚ] ℚ) (g : MvPolynomial σ ℚ) (h : MvPolynomial σ ℂ) :
    projQ ℓ (MvPolynomial.map (algebraMap ℚ ℂ) g * h) = g * projQ ℓ h := by
  classical
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_projQ, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_projQ]
  have : algebraMap ℚ ℂ (AddMonoidAlgebra.coeff g x.1) * AddMonoidAlgebra.coeff h x.2 = AddMonoidAlgebra.coeff g x.1 • AddMonoidAlgebra.coeff h x.2 := by
    rw [Algebra.smul_def]
  rw [this, map_smul, smul_eq_mul]

theorem comap_extC (I : Ideal (MvPolynomial σ ℚ)) :
    (extC I).comap (MvPolynomial.map (algebraMap ℚ ℂ)) = I := by
  obtain ⟨ℓ, hℓ⟩ := exists_linearForm_one
  refine le_antisymm ?_ Ideal.le_comap_map
  intro f hf
  have key : ∀ x ∈ extC I, ∀ h : MvPolynomial σ ℂ, projQ ℓ (h * x) ∈ I := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨g, hg, rfl⟩ h
      rw [mul_comm, projQ_map_mul]
      exact I.mul_mem_right _ hg
    · intro h
      rw [mul_zero, projQ_zero]
      exact I.zero_mem
    · intro a b _ _ ha hb h
      rw [mul_add, projQ_add]
      exact I.add_mem (ha h) (hb h)
    · intro a b _ hb h
      rw [smul_eq_mul, ← mul_assoc]
      exact hb (h * a)
  have := key _ hf 1
  rwa [one_mul, projQ_map ℓ hℓ] at this

end ReciprocityTheory.AnForm.R
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_int_comp :
    (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := by
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply, MvPolynomial.map_map]
  congr 1

theorem pC_eq_extC_extQ (P : Ideal (MRing ι)) : pC P = extC (extQ P) := by
  unfold pC extC extQ
  rw [Ideal.map_map, map_int_comp]
  rfl

theorem horizontal_spec {P : Ideal (MRing ι)} (h : IsHorizontal P) :
    ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
  intro m hm
  have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
  unfold IsHorizontal at h
  rw [h] at h1
  exact Ideal.mem_bot.mp h1

theorem withBot_eq_of_add_one {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : a = (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h.symm (by simp)
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      change ((⊤ : ℕ∞) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) at h
      exact (ENat.top_ne_natCast (n + 1) (WithBot.coe_injective h)).elim
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h2 : k + 1 = n + 1 := by exact_mod_cast h'
      have hk : k = n := by omega
      subst hk
      norm_cast

theorem pcEquidim : PCEquidimStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [ringKrullDim_of_mem_minimalPrimes_extC (extQ P) Q hQ]
  apply withBot_eq_of_add_one
  rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]

theorem pcMinContract : PCMinContractStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [← map_int_comp, ← Ideal.comap_comap, comap_of_mem_minimalPrimes_extC (extQ P) Q hQ, hcomap]

theorem pcContract : PCContractStatement := by
  intro K _ ι _ P e hP f hf
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨_, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  rw [pC_eq_extC_extQ] at hf
  have h1 : f ∈ (extC (extQ P)).comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := hf
  rw [← map_int_comp, ← Ideal.comap_comap, comap_extC, hcomap] at h1
  exact h1

end ReciprocityTheory.ChartRestriction.G.Geo

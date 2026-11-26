module

public import Formalism.PeriodIntegrals.UnimodGenus

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Development
open NumberField

noncomputable section

namespace PI.UG.W

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def locR (p : Ideal R) : Submodule R K := loc (K := K) p (1 : Submodule R K)

def dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (locR (K := K) p).comap ((h y).restrictScalars R)

def IsUnimodularAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Prop :=
  dualAt h p (loc (K := K) p L) = loc (K := K) p L

end Defs

def UnimodLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ),
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt (hStd E n) p N

def IsomLocStd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N →
      ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt (hStd E n) p N →
        ∃ g ∈ isom (hStd E n), gmap g (loc (K := E) p (stdLat E n)) = loc (K := E) p N

theorem unimodGenus_of (h1 : UnimodLocal) (h2 : IsomLocStd) : PI.UnimodGenus := by
  intro E _ _ _ n hE N hN hU p hp
  exact h2 E n hE N hN p hp (h1 E n N hN hU p hp)

end PI.UG.W
end
end

open NumberField

noncomputable section

namespace PI.UG.W

theorem hStd_apply (E : Type) [Field E] [StarRing E] (n : ℕ) (x y : Sp E n) :
    hStd E n x y = ∑ i, star (x i) * y i := rfl

theorem hStd_isSymm (E : Type) [Field E] [StarRing E] (n : ℕ) : (hStd E n).IsSymm := by
  refine LinearMap.isSymm_def.mpr fun x y => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hStd_apply, hStd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star, mul_comm]

theorem star_mem_range (E : Type) [Field E] [NumberField E] [StarRing E] (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  exact ⟨⟨star (algebraMap (𝓞 E) E r), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

def eStd (E : Type) [Field E] (n : ℕ) (i : Fin n) : Sp E n := Pi.single i 1

theorem hStd_eStd (E : Type) [Field E] [StarRing E] (n : ℕ) (i j : Fin n) :
    hStd E n (eStd E n i) (eStd E n j) = if i = j then 1 else 0 := by
  rw [hStd_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [eStd, hk]) (by simp)]
    simp [eStd]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [eStd, Ne.symm h]
    · simp [eStd, Pi.single_apply, hk]

end PI.UG.W

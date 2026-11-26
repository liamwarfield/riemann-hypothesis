module

public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

@[expose] public section

section -- merged from Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
noncomputable section

namespace Formalism.ThetaLiftIndependence

namespace LatticeLiftIndependence

open Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (a * b) L = gmap a (gmap b L) := by
  unfold gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [gmap]

theorem gmap_inv_gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : gmap g⁻¹ (gmap g L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]

end Gen

section Lat

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem conj_mem_autL (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    {M : Submodule (NumberField.RingOfIntegers K) V} {a : V ≃ₗ[K] V} (ha : a ∈ autL h M) :
    g * a * g⁻¹ ∈ autL h (gmap g M) := by
  refine ⟨(isom h).mul_mem ((isom h).mul_mem hg ha.1) ((isom h).inv_mem hg), ?_⟩
  show gmap (g * a * g⁻¹) (gmap g M) = gmap g M
  rw [gmap_mul, gmap_inv_gmap, gmap_mul, ha.2]

def conjEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : autL h M ≃ autL h (gmap g M) where
  toFun a := ⟨g * a * g⁻¹, conj_mem_autL h hg a.2⟩
  invFun b := ⟨g⁻¹ * b * g, by
    have := conj_mem_autL h ((isom h).inv_mem hg) b.2
    rwa [gmap_inv_gmap, inv_inv] at this⟩
  left_inv a := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem latWt_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : latWt h (gmap g M) = latWt h M := by
  unfold latWt
  rw [Nat.card_congr (conjEquiv h hg M)]

theorem reps_inv (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    {s : Finset (Submodule (NumberField.RingOfIntegers K) V)} (hs : IsClassReps h L s)
    {N N' N'' : Submodule (NumberField.RingOfIntegers K) V} (hN : N ∈ s) (hN'' : N'' ∈ s)
    {g g' : V ≃ₗ[K] V} (hg : g ∈ isom h) (hg' : g' ∈ isom h)
    (e : gmap g N' = N) (e' : gmap g' N'' = N') : N'' = N := by
  obtain ⟨N0, -, huniq⟩ := hs.2 N (hs.1 N hN)
  have h1 := huniq N ⟨hN, 1, (isom h).one_mem, gmap_one N⟩
  have h2 := huniq N'' ⟨hN'', g * g', (isom h).mul_mem hg hg', by rw [gmap_mul, e', e]⟩
  exact h2.trans h1.symm

end Lat

end LatticeLiftIndependence

open Formalism.HermitianLatticesTheory LatticeLiftIndependence

theorem latLiftIndep : LatLiftIndep := by
  intro K V _ _ _ _ _ _ _ h L f Θ hf hΘ s s' hs hs'
  classical
  have ex : ∀ {t t' : Finset (Submodule (NumberField.RingOfIntegers K) V)},
      IsClassReps h L t → IsClassReps h L t' → ∀ N ∈ t,
        ∃ N', N' ∈ t' ∧ ∃ g ∈ isom h, gmap g N' = N :=
    fun ht ht' N hN => (ht'.2 N (ht.1 N hN)).exists
  let i : ∀ N ∈ s, Submodule (NumberField.RingOfIntegers K) V :=
    fun N hN => Classical.choose (ex hs hs' N hN)
  let j : ∀ N ∈ s', Submodule (NumberField.RingOfIntegers K) V :=
    fun N hN => Classical.choose (ex hs' hs N hN)
  have hi : ∀ N (hN : N ∈ s), i N hN ∈ s' ∧ ∃ g ∈ isom h, gmap g (i N hN) = N :=
    fun N hN => Classical.choose_spec (ex hs hs' N hN)
  have hj : ∀ N (hN : N ∈ s'), j N hN ∈ s ∧ ∃ g ∈ isom h, gmap g (j N hN) = N :=
    fun N hN => Classical.choose_spec (ex hs' hs N hN)
  unfold latLift
  refine Finset.sum_bij' i j (fun N hN => (hi N hN).1) (fun N hN => (hj N hN).1) ?_ ?_ ?_
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hi N hN
    obtain ⟨-, g', hg', e'⟩ := hj (i N hN) (hi N hN).1
    exact reps_inv h L hs hN (hj _ (hi N hN).1).1 hg hg' e e'
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hj N hN
    obtain ⟨-, g', hg', e'⟩ := hi (j N hN) (hj N hN).1
    exact reps_inv h L hs' hN (hi _ (hj N hN).1).1 hg hg' e e'
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hi N hN
    conv_lhs => rw [← e]
    rw [latWt_gmap h hg, hf g hg, hΘ g hg]
end Formalism.ThetaLiftIndependence
end
end

section -- merged from Formalism.ThetaLiftIndependence.ThetaOrbitSums.GaussOp
open scoped BigOperators

namespace Formalism.ThetaLiftIndependence

namespace GaussOperatorLemmas

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

theorem sum_units_eq_sub {M : Type*} [AddCommGroup M] (f : 𝔽 → M) :
    ∑ u : 𝔽ˣ, f u = ∑ x, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left,
    Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)

theorem sum_units_char (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by
  rw [sum_units_eq_sub (fun x => ψ (a * x))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  congr 1
  have h := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
  rw [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])

theorem core (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by
  simp_rw [sum_units_char ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero,
    sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]
  simp

end GaussOperatorLemmas

open GaussOperatorLemmas in
theorem gaussOp_eq : GaussOp := by
  intro 𝔽 V _ _ _ _ _ ψ ρ hψ v hv
  have hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  constructor
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul, hρ]
    have step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v := by
      intro d
      rw [Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d) (fun e => ψ (-(d : 𝔽)) •
        ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul, hρ]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v := by
      intro c
      rw [← Fintype.sum_equiv (Equiv.mulLeft c) (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) *
        ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv

end Formalism.ThetaLiftIndependence
end

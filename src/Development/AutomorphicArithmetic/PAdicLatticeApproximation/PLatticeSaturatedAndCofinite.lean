module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMemClosure

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma exists_nsmul_mem_closure {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Set V) (w : V)
    (hw : w ∈ Submodule.span ℚ s) : ∃ k : ℕ, 0 < k ∧ k • w ∈ AddSubgroup.closure s :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure s w hw

theorem UpperTheory.p_lattice_saturated_and_cofinite :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)), UpperTheory.Gal.W2.IsPLat D M → (∀ (m : ℕ) (w : VQ D), m.Coprime p → m • w ∈ M → w ∈ M) ∧ ∀ w : VQ D, ∃ r : ℕ, p ^ r • w ∈ M := by
  intro p hp D M hM
  obtain ⟨-, s, hs, hmem⟩ := hM
  have hprime : p.Prime := hp.out
  refine ⟨?_, ?_⟩
  · intro m w hm hw
    obtain ⟨m', hm', hc⟩ := (hmem _).1 hw
    refine (hmem _).2 ⟨m' * m, Nat.Coprime.mul_left hm' hm, ?_⟩
    rwa [mul_smul]
  · intro w
    obtain ⟨k, hk, hkw⟩ := exists_nsmul_mem_closure (s : Set (VQ D)) w (by rw [hs]; trivial)
    obtain ⟨r, k', hk', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hprime.ne_one
    refine ⟨r, (hmem _).2 ⟨k', ((Nat.Prime.coprime_iff_not_dvd hprime).2 hk').symm, ?_⟩⟩
    rw [smul_smul, mul_comm]
    exact hkw
end

section -- merged from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowMulIntOfIsIntAfAlgebraMap
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap :
    ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), IsIntAf (algebraMap ℚ (AfP p) q) → ∃ (r : ℕ) (z : ℤ), (p : ℚ) ^ r * q = z := by
  intro p hp q hq
  have hp' : p.Prime := hp.out
  obtain ⟨r, m, hmp, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp'.one_lt.ne'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hden
      exact absurd hden q.den_nz
    · exact h
  have hmc : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp').mpr hmp).symm
  have hint : IsIntAf (algebraMap ℚ (AfP p) q * (p : AfP p) ^ r) := by
    intro v
    rw [map_mul, map_pow, map_natCast]
    exact mul_mem (hq v) (pow_mem (natCast_mem _ p) r)
  have hnum : ((q.num : ℤ) : ℚ) = (m : ℚ) * (q * (p : ℚ) ^ r) := by
    rw [← Rat.mul_den_eq_num]
    have : (q.den : ℚ) = (p : ℚ) ^ r * m := by exact_mod_cast hden
    rw [this]
    ring
  have hdvd : (m : ℤ) ∣ q.num := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p m hm0 hmc q.num _ hint
    rw [hnum, map_mul, map_mul, map_pow, map_natCast, map_natCast]
  have h1 : m ∣ q.num.natAbs := Int.natCast_dvd.mp hdvd
  have h2 : m ∣ q.den := ⟨p ^ r, by rw [hden, mul_comm]⟩
  have hm1 : m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 q.reduced) h2
  refine ⟨r, q.num, ?_⟩
  rw [← Rat.mul_den_eq_num]
  have : (q.den : ℚ) = (p : ℚ) ^ r := by
    rw [hden, hm1, mul_one]
    push_cast
    rfl
  rw [this, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.PAdicLatticeApproximation.FiniteFreeOfBoundedDenominatorsLattice
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private theorem UpperTheory.tensor_rat_injective_of_free {L : Type} [AddCommGroup L] [Module.Free ℤ L] :
    Function.Injective (TensorProduct.mk ℤ ℚ L (1 : ℚ)) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) :=
    fun a b h => by simpa using h
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L) (Algebra.linearMap ℤ ℚ) hf
  intro x y hxy
  apply (TensorProduct.lid ℤ L).symm.injective
  apply h
  simpa [LinearMap.rTensor_tmul] using hxy

theorem UpperTheory.finite_free_of_bounded_denominators_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a) → Module.Finite ℤ X.lat ∧ Module.Free ℤ X.lat := by
  intro p _ D X ⟨d, hd, h⟩
  haveI := D.freeLa
  haveI := D.finLa
  let ι : D.La →ₗ[ℤ] VQ D := TensorProduct.mk ℤ ℚ D.La (1 : ℚ)
  have hι : Function.Injective ι := UpperTheory.tensor_rat_injective_of_free
  let g : X.lat →ₗ[ℤ] VQ D := (d : ℤ) • (X.lat.toIntSubmodule.subtype)
  have hg : Function.Injective g := by
    intro u v huv
    have h1 : (d : ℤ) • (u : VQ D) = (d : ℤ) • (v : VQ D) := huv
    have hq : ((d : ℚ)) • (u : VQ D) = (d : ℚ) • (v : VQ D) := by
      simpa [Nat.cast_smul_eq_nsmul] using h1
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact Subtype.ext (smul_right_injective _ hd0 hq)
  have hr : ∀ w, g w ∈ LinearMap.range ι := by
    intro w
    obtain ⟨a, ha⟩ := h w w.2
    refine ⟨a, ?_⟩
    change (1 : ℚ) ⊗ₜ[ℤ] a = (d : ℤ) • (w : VQ D)
    rw [← ha]
    exact (natCast_zsmul (w : VQ D) d).symm
  let f : X.lat →ₗ[ℤ] D.La :=
    (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ g.codRestrict (LinearMap.range ι) hr
  have hf : Function.Injective f := by
    intro u v huv
    apply hg
    have := (LinearEquiv.ofInjective ι hι).symm.injective huv
    exact congrArg Subtype.val this
  refine ⟨Module.Finite.of_injective f hf, ?_⟩
  exact Module.Free.of_equiv (LinearEquiv.ofInjective f hf).symm
end

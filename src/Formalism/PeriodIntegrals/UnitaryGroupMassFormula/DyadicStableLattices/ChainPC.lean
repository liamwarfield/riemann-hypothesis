module

public import Formalism.PeriodIntegrals.GoodTwo
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPB
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPA
noncomputable section

namespace PI.GoodTwo.ChainBetweenPairs

open Module

theorem exists_pair_of_between (L L' : PeriodPair) (S : Submodule ℤ ℂ)
    (h1 : L.lattice ≤ S) (h2 : S ≤ L'.lattice) :
    ∃ P : PeriodPair, ∀ z, z ∈ P.lattice ↔ z ∈ S := by
  classical
  have hd : DiscreteTopology S :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology L'.lattice) h2
  have hs : IsZLattice ℝ S := by
    refine ⟨top_le_iff.mp ?_⟩
    rw [← (inferInstance : IsZLattice ℝ L.lattice).span_top]
    exact Submodule.span_mono h1
  have : Module.Finite ℤ S := ZLattice.module_finite ℝ S
  have hrank : finrank ℤ S = 2 := by
    rw [ZLattice.rank ℝ S, Complex.finrank_real_complex]
  let b : Module.Basis (Fin 2) ℤ S := Module.finBasisOfFinrankEq ℤ S hrank
  refine ⟨⟨b 0, b 1, ?_⟩, fun z => ?_⟩
  · have hl := (b.ofZLatticeBasis ℝ S).linearIndependent
    have heq : (![((b 0 : S) : ℂ), ((b 1 : S) : ℂ)] : Fin 2 → ℂ) = ⇑(b.ofZLatticeBasis ℝ S) := by
      ext i
      fin_cases i <;> simp [Module.Basis.ofZLatticeBasis_apply]
    rw [heq]
    exact hl
  · have hset : ({((b 0 : S) : ℂ), ((b 1 : S) : ℂ)} : Set ℂ) =
        Set.range (b.ofZLatticeBasis ℝ S) := by
      ext x
      simp [Module.Basis.ofZLatticeBasis_apply, Fin.exists_fin_two, eq_comm]
    show z ∈ Submodule.span ℤ {((b 0 : S) : ℂ), ((b 1 : S) : ℂ)} ↔ z ∈ S
    rw [hset, Module.Basis.ofZLatticeBasis_span]

end PI.GoodTwo.ChainBetweenPairs
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo.ChainBetweenPairs

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.F (scalePair MulStable)

theorem omega_sq (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 = omegaK d - (((d + 1) / 4 : ℕ) : ℂ) := by
  have hdiv : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h4 : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h4 (by norm_num)]
    push_cast
    ring
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    rfl
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  rw [hdiv]
  linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs

theorem conj_omega (d : ℕ) : conj (omegaK d) = 1 - omegaK d := by
  unfold omegaK
  simp [map_div₀, map_add (f := _), map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

theorem int_mul_mem (L : PeriodPair) (n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    (n : ℂ) * z ∈ L.lattice := by
  rw [← zsmul_eq_mul]
  exact zsmul_mem hz n

theorem pow_two_mul_mem (L : PeriodPair) (i : ℕ) {z : ℂ} (hz : z ∈ L.lattice) :
    (2 : ℂ) ^ i * z ∈ L.lattice := by
  have h := int_mul_mem L (2 ^ i) hz
  push_cast at h
  exact h

theorem stab (d : ℕ) (L : PeriodPair) (hL : HasCMBy d L) (m n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    ((m : ℂ) + n * omegaK d) * z ∈ L.lattice := by
  rw [add_mul, mul_assoc]
  exact add_mem (int_mul_mem L m hz) (int_mul_mem L n (hL z hz))

theorem not_half (d : ℕ) (L : PeriodPair) (m n : ℤ) (hn : Odd n) :
    ¬ MulStable L (((m : ℂ) + n * omegaK d) / 2) := by
  intro hS
  obtain ⟨t, N, ht, -, -⟩ := Formalism.L2.Th1.F.mulStableIntegral L _ hS
  simp only [map_div₀, map_add (f := _), map_mul, map_intCast, map_ofNat, conj_omega] at ht
  have h2 : ((2 * m + n : ℤ) : ℂ) = ((2 * t : ℤ) : ℂ) := by
    push_cast
    linear_combination 2 * ht
  have h3 : 2 * m + n = 2 * t := by exact_mod_cast h2
  obtain ⟨k, rfl⟩ := hn
  omega

theorem half_mem (L : PeriodPair) (w : ℂ) (p q : ℤ) (hw : (p : ℂ) * L.ω₁ + q * L.ω₂ = 2 * w)
    (h : (p : ZMod 2) = 0 ∧ (q : ZMod 2) = 0) : w ∈ L.lattice := by
  obtain ⟨hp, hq⟩ := h
  obtain ⟨p', rfl⟩ : (2 : ℤ) ∣ p := (ZMod.intCast_zmod_eq_zero_iff_dvd p 2).mp hp
  obtain ⟨q', rfl⟩ : (2 : ℤ) ∣ q := (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).mp hq
  have hw' : w = (p' : ℂ) * L.ω₁ + q' * L.ω₂ := by
    push_cast at hw
    linear_combination (-1 / 2 : ℂ) * hw
  rw [hw']
  exact add_mem (int_mul_mem L p' L.ω₁_mem_lattice) (int_mul_mem L q' L.ω₂_mem_lattice)

theorem two_tors (L : PeriodPair) (π : ℂ) (hπ : ¬ MulStable L (π / 2)) (hπL : MulStable L π)
    {u v : ℂ} (hu1 : π * u ∈ L.lattice) (hu2 : 2 * u ∈ L.lattice) (hu3 : u ∉ L.lattice)
    (hv1 : π * v ∈ L.lattice) (hv2 : 2 * v ∈ L.lattice) (hv3 : v ∉ L.lattice) :
    u - v ∈ L.lattice := by
  by_contra huv
  apply hπ
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 hu2
  obtain ⟨c, e, hce⟩ := PeriodPair.mem_lattice.1 hv2
  have key : ∀ p q r s : ZMod 2, ¬ (p = 0 ∧ q = 0) → ¬ (r = 0 ∧ s = 0) →
      ¬ (p - r = 0 ∧ q - s = 0) → p * s - q * r ≠ 0 := by decide
  have hdet : ((a * e - b * c : ℤ) : ZMod 2) ≠ 0 := by
    push_cast
    refine key _ _ _ _ (fun h => hu3 (half_mem L u a b hab h)) (fun h => hv3 (half_mem L v c e hce h))
      (fun h => huv (half_mem L (u - v) (a - c) (b - e) ?_ ?_))
    · push_cast
      linear_combination hab - hce
    · push_cast
      exact h
  have hodd : Odd (a * e - b * c) := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    exact hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast h2))
  obtain ⟨m, hm⟩ := hodd
  have hmC : (a : ℂ) * e - b * c = 2 * m + 1 := by exact_mod_cast hm
  have e1 : L.ω₁ / 2 = (e : ℂ) * u - b * v - m * L.ω₁ := by
    linear_combination ((e : ℂ) / 2) * hab - ((b : ℂ) / 2) * hce - (L.ω₁ / 2) * hmC
  have e2 : L.ω₂ / 2 = (a : ℂ) * v - c * u - m * L.ω₂ := by
    linear_combination ((a : ℂ) / 2) * hce - ((c : ℂ) / 2) * hab - (L.ω₂ / 2) * hmC
  have h1 : π * (L.ω₁ / 2) ∈ L.lattice := by
    have f : π * ((e : ℂ) * u - b * v - m * L.ω₁) = (e : ℂ) * (π * u) - b * (π * v) - m * (π * L.ω₁) := by
      ring
    rw [e1, f]
    exact sub_mem (sub_mem (int_mul_mem L e hu1) (int_mul_mem L b hv1))
      (int_mul_mem L m (hπL _ L.ω₁_mem_lattice))
  have h2 : π * (L.ω₂ / 2) ∈ L.lattice := by
    have f : π * ((a : ℂ) * v - c * u - m * L.ω₂) = (a : ℂ) * (π * v) - c * (π * u) - m * (π * L.ω₂) := by
      ring
    rw [e2, f]
    exact sub_mem (sub_mem (int_mul_mem L a hv1) (int_mul_mem L c hu1))
      (int_mul_mem L m (hπL _ L.ω₂_mem_lattice))
  intro w hw
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 hw
  have f : π / 2 * ((p : ℂ) * L.ω₁ + q * L.ω₂) = (p : ℂ) * (π * (L.ω₁ / 2)) + q * (π * (L.ω₂ / 2)) := by
    ring
  rw [f]
  exact add_mem (int_mul_mem L p h1) (int_mul_mem L q h2)

def S (L : PeriodPair) (π : ℂ) (i : ℕ) : Submodule ℤ ℂ where
  carrier := {z | π * z ∈ L.lattice ∧ (2 : ℂ) ^ i * z ∈ L.lattice}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [mul_add]; exact add_mem h1 h3, by rw [mul_add]; exact add_mem h2 h4⟩
  zero_mem' := by
    show π * 0 ∈ L.lattice ∧ (2 : ℂ) ^ i * 0 ∈ L.lattice
    simp
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    exact ⟨by rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1,
      by rw [mul_smul_comm]; exact Submodule.smul_mem _ c h2⟩

theorem mem_S {L : PeriodPair} {π : ℂ} {i : ℕ} {z : ℂ} :
    z ∈ S L π i ↔ π * z ∈ L.lattice ∧ (2 : ℂ) ^ i * z ∈ L.lattice := Iff.rfl

end PI.GoodTwo.ChainBetweenPairs
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo.ChainBetweenPairs

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.F (scalePair MulStable)

theorem chain_core (d : ℕ) (L : PeriodPair) (hd : d % 8 = 7) (hL : HasCMBy d L) (h : ℕ) (X Y : ℤ)
    (hY : Odd Y) (hN : X ^ 2 + X * Y + (((d + 1) / 4 : ℕ) : ℤ) * Y ^ 2 = 2 ^ h) (π : ℂ)
    (hπ : π = X + Y * omegaK d) :
    ∃ M : ℕ → PeriodPair, M 0 = L ∧ (∀ i, HasCMBy d (M i)) ∧
      (∀ i, i < h → IsIdxTwo (M i) (M (i + 1))) ∧ ∀ z, z ∈ (M h).lattice ↔ π * z ∈ L.lattice := by
  have hω2 := omega_sq d (by omega)
  set πb : ℂ := ((X + Y : ℤ) : ℂ) + ((-Y : ℤ) : ℂ) * omegaK d with hπb
  have hNc : (X : ℂ) ^ 2 + X * Y + (((d + 1) / 4 : ℕ) : ℂ) * Y ^ 2 = 2 ^ h := by
    have := congrArg (Int.cast : ℤ → ℂ) hN
    push_cast at this
    exact this
  have hprod : π * πb = 2 ^ h := by
    rw [hπ, hπb]
    push_cast
    linear_combination (-(Y : ℂ) ^ 2) * hω2 + hNc
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact (pow_ne_zero h two_ne_zero) hprod.symm
  have stπ : ∀ z ∈ L.lattice, π * z ∈ L.lattice := fun z hz => hπ ▸ stab d L hL X Y hz
  have stπb : ∀ z ∈ L.lattice, πb * z ∈ L.lattice := fun z hz => stab d L hL (X + Y) (-Y) hz
  have hle1 : ∀ i, L.lattice ≤ S L π i := fun i z hz => ⟨stπ z hz, pow_two_mul_mem L i hz⟩
  have hle2 : ∀ i, S L π i ≤ (scalePair L π⁻¹ (inv_ne_zero hπ0)).lattice := by
    intro i z hz
    rw [(Formalism.L2.Th1.F.homogeneity L π⁻¹ (inv_ne_zero hπ0)).1 z, inv_inv]
    exact hz.1
  choose P hP using fun i => exists_pair_of_between L _ (S L π i) (hle1 i) (hle2 i)
  let M : ℕ → PeriodPair := fun i => if i = 0 then L else P i
  have hM : ∀ i z, z ∈ (M i).lattice ↔ z ∈ S L π i := by
    intro i z
    by_cases hi : i = 0
    · subst hi
      simp only [M, if_pos rfl, mem_S, pow_zero, one_mul]
      exact ⟨fun hz => ⟨stπ z hz, hz⟩, fun hz => hz.2⟩
    · simp only [M, if_neg hi]
      exact hP i z

  have claimA : ∀ i u v, u ∈ S L π (i + 1) → v ∈ S L π (i + 1) → u ∉ S L π i → v ∉ S L π i →
      u - v ∈ S L π i := by
    intro i u v hu hv hu3 hv3
    have hnh : ¬ MulStable L (π / 2) := by
      rw [hπ]
      exact not_half d L X Y hY
    have key := two_tors L π hnh stπ (u := (2 : ℂ) ^ i * u) (v := (2 : ℂ) ^ i * v)
      (by rw [mul_left_comm]; exact pow_two_mul_mem L i hu.1)
      (by rw [← mul_assoc, ← pow_succ']; exact hu.2) (fun h' => hu3 ⟨hu.1, h'⟩)
      (by rw [mul_left_comm]; exact pow_two_mul_mem L i hv.1)
      (by rw [← mul_assoc, ← pow_succ']; exact hv.2) (fun h' => hv3 ⟨hv.1, h'⟩)
    refine ⟨?_, ?_⟩
    · rw [mul_sub]
      exact sub_mem hu.1 hv.1
    · rw [mul_sub]
      exact key
  refine ⟨M, by simp [M], ?_, ?_, ?_⟩
  · intro i z hz
    rw [hM] at hz ⊢
    exact ⟨by rw [mul_left_comm]; exact hL _ hz.1, by rw [mul_left_comm]; exact hL _ hz.2⟩
  · intro i hi
    have hns : ¬ MulStable L (πb / 2) := not_half d L (X + Y) (-Y) hY.neg
    unfold MulStable at hns
    push Not at hns
    obtain ⟨w, hw, hw2⟩ := hns
    obtain ⟨j, rfl⟩ : ∃ j, h = i + j + 1 := ⟨h - i - 1, by omega⟩
    have hπb' : πb = 2 ^ (i + j + 1) / π := (eq_div_iff hπ0).2 (by rw [mul_comm]; exact hprod)
    set t : ℂ := (2 : ℂ) ^ j * (w / π) with ht
    have htπ : π * t = (2 : ℂ) ^ j * w := by
      rw [ht]
      field_simp
    have ht2 : (2 : ℂ) ^ i * t = πb / 2 * w := by
      rw [ht, hπb']
      field_simp
      ring
    have ht3 : (2 : ℂ) ^ (i + 1) * t = πb * w := by
      rw [pow_succ, mul_comm ((2 : ℂ) ^ i) 2, mul_assoc, ht2]
      ring
    have hmono : ∀ z, z ∈ S L π i → z ∈ S L π (i + 1) := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rw [pow_succ, mul_comm ((2 : ℂ) ^ i) 2, mul_assoc]
      have := pow_two_mul_mem L 1 hz.2
      simpa using this
    have htS1 : t ∈ S L π (i + 1) := ⟨by rw [htπ]; exact pow_two_mul_mem L j hw, by rw [ht3]; exact stπb _ hw⟩
    have htS0 : t ∉ S L π i := fun h' => hw2 (by rw [← ht2]; exact h'.2)
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [hM]
      exact htS0
    · rw [hM]
      refine ⟨?_, ?_⟩
      · rw [mul_left_comm, htπ]
        have := pow_two_mul_mem L 1 (pow_two_mul_mem L j hw)
        simpa using this
      · rw [mul_left_comm, ht2]
        have : 2 * (πb / 2 * w) = πb * w := by ring
        rw [this]
        exact stπb _ hw
    · intro z
      rw [hM, hM, hM]
      constructor
      · intro hz
        by_cases hz' : z ∈ S L π i
        · exact Or.inl hz'
        · exact Or.inr (claimA i z t hz htS1 hz' htS0)
      · rintro (hz | hz)
        · exact hmono z hz
        · have : z = (z - t) + t := by ring
          rw [this]
          exact add_mem (hmono _ hz) htS1
  · intro z
    rw [hM, mem_S]
    constructor
    · exact fun hz => hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      have : (2 : ℂ) ^ h * z = πb * (π * z) := by rw [← hprod]; ring
      rw [this]
      exact stπb _ hz

end PI.GoodTwo.ChainBetweenPairs

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
public import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPow
open NumberField Polynomial

namespace GlobalTheory.UPel.HT

theorem charpoly_eq_pow_of_aeval_irreducible {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Module.End ℤ M) (μ : ℤ[X]) (hm : μ.Monic) (hi : Irreducible μ) (h : aeval f μ = 0) :
    ∃ s : ℕ, f.charpoly = μ ^ s := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  have hA : aeval (LinearMap.toMatrixAlgEquiv b f) μ = 0 := by
    have := Polynomial.aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f μ
    simpa [h] using this
  have hd := GlobalTheory.UnitLemma.Centraliser.charpoly_dvd_pow_of_aeval_eq_zero _ μ hA
  have hc : (LinearMap.toMatrixAlgEquiv b f).charpoly = f.charpoly := LinearMap.charpoly_toMatrix f b
  rw [hc] at hd
  obtain ⟨i, -, hi'⟩ := (dvd_prime_pow hi.prime _).1 hd
  exact ⟨i, eq_of_monic_of_associated (LinearMap.charpoly_monic f) (hm.pow i) hi'⟩

theorem Datum.charpoly_La_eq_pow (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F) :
    haveI := D.freeLa; haveI := D.finLa
    LinearMap.charpoly (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n) := by
  haveI := D.freeLa; haveI := D.finLa
  have hint : IsIntegral ℤ c := RingOfIntegers.isIntegral c
  have hm : (minpoly ℤ c).Monic := minpoly.monic hint
  have hirr : Irreducible (minpoly ℤ c) := minpoly.irreducible hint
  have hpos : 0 < (minpoly ℤ c).natDegree := minpoly.natDegree_pos hint
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow c
  have hR : LinearMap.charpoly (LinearMap.mulLeft ℤ c) = minpoly ℤ c ^ r := hr
  let ψ : 𝓞 D.F →+* Module.End ℤ D.La :=
    (Module.toModuleEnd ℤ (S := D.O) D.La).comp (algebraMap (𝓞 D.F) D.O)
  have hf : DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c) = ψ.toIntAlgHom c := rfl
  have h0 : aeval (ψ.toIntAlgHom c) (minpoly ℤ c) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨s, hs⟩ := charpoly_eq_pow_of_aeval_irreducible _ _ hm hirr h0
  have h1 := LinearMap.charpoly_natDegree (ψ.toIntAlgHom c)
  rw [hs, hm.natDegree_pow, D.rankLa] at h1
  have h2 := LinearMap.charpoly_natDegree (LinearMap.mulLeft ℤ c)
  rw [hR, hm.natDegree_pow, RingOfIntegers.rank] at h2
  have hsr : s = r * (D.m * D.n) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← h2]
    ring
  rw [hf, hs, hR, ← pow_mul, hsr]

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPowStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_la_eq_pow (p : ℕ) [Fact p.Prime]
    (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F) :
    haveI := D.freeLa
    haveI := D.finLa
    LinearMap.charpoly (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n) :=
  GlobalTheory.UPel.HT.Datum.charpoly_La_eq_pow p D c
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteInt
open Finset

namespace GlobalTheory

theorem ringHom_sep_charZero (k : Type) [Field k] [CharZero k] (C : Type) [CommRing C]
    (S : Finset (C →+* k)) (χ₀ : C →+* k) : ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert χ' S hχ' ih =>
    obtain ⟨c, hc⟩ := ih
    by_cases h0 : χ' = χ₀
    · refine ⟨c, fun χ hχ hne => ?_⟩
      rcases Finset.mem_insert.1 hχ with rfl | h
      · exact absurd h0 hne
      · exact hc χ h hne
    obtain ⟨d, hd⟩ := DFunLike.ne_iff.1 h0
    have key : ∀ χ ∈ insert χ' S, χ ≠ χ₀ →
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ).Subsingleton := by
      intro χ hχ hne n hn m hm
      simp only [Set.mem_setOf_eq, map_add (f := _), map_mul, map_natCast] at hn hm
      have hsub : ((n : k) - m) * (χ d - χ₀ d) = 0 := by linear_combination hn - hm
      rcases mul_eq_zero.1 hsub with h | h
      · exact_mod_cast sub_eq_zero.1 h
      · have hb : χ d = χ₀ d := sub_eq_zero.1 h
        rcases Finset.mem_insert.1 hχ with rfl | h'
        · exact absurd hb hd
        · exact absurd (by rw [hb] at hn; linear_combination hn) (hc χ h' hne)
    have hfin : (⋃ χ ∈ (insert χ' S).filter (· ≠ χ₀),
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ)).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun χ hχ => ?_
      rw [Finset.mem_coe, Finset.mem_filter] at hχ
      exact (key χ hχ.1 hχ.2).finite
    obtain ⟨n, hn⟩ := hfin.exists_notMem
    refine ⟨c + n * d, fun χ hχ hne heq => hn ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨χ, Finset.mem_filter.2 ⟨hχ, hne⟩, heq⟩

theorem ringHom_pow_eq_one_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (ψ : C →+* k) [Finite ψ.range] (a : C) (ha : ψ a ≠ 0) (m : ℕ)
    (hm : (Nat.card ψ.range).factorial ∣ m) : ψ a ^ m = 1 := by
  classical
  haveI := Fintype.ofFinite ψ.range
  let f : Fin (Nat.card ψ.range + 1) → ψ.range := fun i => ⟨ψ a ^ (i : ℕ), ⟨a ^ (i : ℕ), by simp⟩⟩
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hf' : ψ a ^ (i : ℕ) = ψ a ^ (j : ℕ) := congrArg Subtype.val hf
  have hpos : ∀ (u v : ℕ), u < v → v ≤ Nat.card ψ.range → ψ a ^ u = ψ a ^ v → ψ a ^ m = 1 := by
    intro u v huv hv he
    have h1 : ψ a ^ (v - u) = 1 := by
      have : ψ a ^ u * (ψ a ^ (v - u) - 1) = 0 := by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' huv.le, mul_one, he, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff'.1 h).1 ha
      · exact sub_eq_zero.1 h
    have hd : v - u ∣ m := (Nat.dvd_factorial (by omega) (by omega)).trans hm
    obtain ⟨t, rfl⟩ := hd
    rw [pow_mul, h1, one_pow]
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact hpos i j h (by omega) hf'
  · exact hpos j i h (by omega) hf'.symm

theorem ringHom_exists_generator_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (χ₀ : C →+* k) [Finite χ₀.range] :
    ∃ g : C, χ₀ g ≠ 0 ∧ ∀ b, χ₀ b ≠ 0 → ∃ n : ℕ, χ₀ b = χ₀ g ^ n := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (χ₀.range)ˣ)
  obtain ⟨g, hg⟩ := ((u : χ₀.range)).2
  refine ⟨g, ?_, fun b hb => ?_⟩
  · rw [hg]
    exact fun h => u.ne_zero (Subtype.ext h)
  · set y : χ₀.range := ⟨χ₀ b, ⟨b, rfl⟩⟩
    have hy0 : y ≠ 0 := fun h => hb (congrArg Subtype.val h)
    have hyu : IsUnit y := by
      have hpow := ringHom_pow_eq_one_of_finite_range χ₀ b hb _ dvd_rfl
      exact ⟨Units.ofPowEqOne y (Nat.card χ₀.range).factorial
        (Subtype.ext (by simpa [y] using hpow)) (Nat.factorial_ne_zero _), rfl⟩
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.2 (hu hyu.unit) : hyu.unit ∈ Submonoid.powers u)
    refine ⟨n, ?_⟩
    have h1 : ((u ^ n : (χ₀.range)ˣ) : χ₀.range) = y := by
      rw [show u ^ n = hyu.unit from hn]; rfl
    have h2 : ((u : χ₀.range) : k) ^ n = χ₀ b := by
      have := congrArg Subtype.val h1
      simpa [y] using this
    rw [hg]
    exact h2.symm

end GlobalTheory

namespace GlobalTheory

theorem ringHom_sep_of_finite_range (k : Type) [Field k] (C : Type) [CommRing C]
    (hfin : ∀ ψ : C →+* k, Finite ψ.range) (S : Finset (C →+* k)) (χ₀ : C →+* k) :
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  let M : ℕ := ∏ ψ ∈ insert χ₀ S, (Nat.card ψ.range).factorial
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hpow : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ a ≠ 0 → ψ a ^ M = 1 := fun ψ hψ a ha => by
    haveI := hfin ψ
    exact ringHom_pow_eq_one_of_finite_range ψ a ha M (Finset.dvd_prod_of_mem _ hψ)
  have hpow' : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ (a ^ M) = if ψ a = 0 then 0 else 1 := by
    intro ψ hψ a
    rw [map_pow]
    split_ifs with h
    · rw [h, zero_pow hM0]
    · exact hpow ψ hψ a h
  haveI := hfin χ₀
  obtain ⟨g, hg0, hgen⟩ := ringHom_exists_generator_of_finite_range χ₀
  have hsep : ∀ χ ∈ S, χ ≠ χ₀ → χ g = χ₀ g → ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := by
    intro χ hχ hne hgeq
    by_contra hcon
    push_neg at hcon
    have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
    have hk : ∀ b, χ₀ b = 0 → χ b = 0 := by
      intro b hb
      by_contra hb'
      have h1 := hcon (1 - b ^ M) (by rw [map_sub, map_one, map_pow, hpow χ hχ' b hb', sub_self])
      rw [map_sub, map_one, map_pow, hb, zero_pow hM0, sub_zero] at h1
      exact one_ne_zero h1
    apply hne
    ext b
    by_cases hb : χ₀ b = 0
    · rw [hb, hk b hb]
    · obtain ⟨n, hn⟩ := hgen b hb
      have h3 : χ (b - g ^ n) = 0 := hk _ (by rw [map_sub, map_pow, hn, sub_self])
      rw [map_sub, map_pow, sub_eq_zero, hgeq, ← hn] at h3
      exact h3
  let V := S.filter (fun χ => χ ≠ χ₀ ∧ χ g = χ₀ g)
  have hV : ∀ χ ∈ V, ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := fun χ hχ => by
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hχ)
    exact hsep χ h1 h2 h3
  choose! a ha using hV
  let A : C := ∏ χ ∈ V, a χ
  have hA0 : χ₀ A ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun χ hχ => (ha χ hχ).2
  have hAV : ∀ χ ∈ V, χ A = 0 := fun χ hχ => by
    rw [map_prod]
    exact Finset.prod_eq_zero hχ (ha χ hχ).1
  refine ⟨g * A ^ M, fun χ hχ hne => ?_⟩
  have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
  rw [map_mul, map_mul, hpow' χ₀ (Finset.mem_insert_self _ _), if_neg hA0, mul_one,
    hpow' χ hχ']
  by_cases hgeq : χ g = χ₀ g
  · rw [if_pos (hAV χ (Finset.mem_filter.2 ⟨hχ, hne, hgeq⟩)), mul_zero]
    exact fun h => hg0 h.symm
  · split_ifs
    · rw [mul_zero]; exact fun h => hg0 h.symm
    · rwa [mul_one]

theorem ringHom_finite_range_of_charP {k : Type} [Field k] {C : Type} [CommRing C]
    [Module.Finite ℤ C] (p : ℕ) [hp : CharP k p] (hp0 : p ≠ 0) (ψ : C →+* k) :
    Finite ψ.range := by
  haveI : Module.Finite ℤ ψ.range :=
    Module.Finite.of_surjective (ψ.rangeRestrict.toAddMonoidHom.toIntLinearMap)
      ψ.rangeRestrict_surjective
  haveI : AddGroup.FG ψ.range := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩
  apply Subtype.ext
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

theorem ringHom_exists_sep_of_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C]
    [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k),
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  intro k _ C _ _ S χ₀
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · exact ringHom_sep_of_finite_range k C
      (fun ψ => ringHom_finite_range_of_charP p hpp.ne_zero ψ) S χ₀
  · haveI := CharP.charP_to_charZero k
    exact ringHom_sep_charZero k C S χ₀

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteIntStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C] [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k), ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  first | (exact @GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (exact GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (intros; apply GlobalTheory.ringHom_exists_sep_of_moduleFinite_int  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpoly
open scoped TensorProduct

namespace GlobalTheory.WeightCount

open Module

theorem isNilpotent_perturb_mul {R : Type*} [Ring R] {A B a b : R} (hAB : Commute A B)
    (ha : ∀ z, Commute a z) (hb : ∀ z, Commute b z) (hA : IsNilpotent A) (hB : IsNilpotent B) :
    IsNilpotent ((A + a) * (B + b) - a * b) := by
  have e : (A + a) * (B + b) - a * b = A * (B + b) + a * B := by noncomm_ring
  rw [e]
  have h1 : Commute A (B + b) := hAB.add_right (hb A).symm
  have h3 : Commute (A * (B + b)) B := Commute.mul_left hAB ((Commute.refl B).add_left (hb B))
  have h2 : Commute (A * (B + b)) (a * B) := Commute.mul_right (ha _).symm h3
  exact h2.isNilpotent_add (h1.isNilpotent_mul_right hA) ((ha B).isNilpotent_mul_left hB)

theorem weight_isRingHom {k V C : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) (ψ : C → k)
    (hψ : (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥) : ∃ φ : C →+* k, ⇑φ = ψ := by
  classical
  set U := ⨅ d, (ρ d).maxGenEigenspace (ψ d) with hU
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hUm : ∀ m, Set.MapsTo (ρ m) U U := fun m v hv => by
    simp only [U, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
    exact fun i => hmaps m i (ψ i) (hv i)
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hψ
  let R : C → Module.End k U := fun m => (ρ m).restrict (hUm m)
  have hRadd : ∀ x y, R (x + y) = R x + R y := fun x y => by
    ext v
    show ρ (x + y) (v : V) = ρ x (v : V) + ρ y (v : V)
    rw [map_add (f := _)]; rfl
  have hRmul : ∀ x y, R (x * y) = R x * R y := fun x y => by
    ext v
    show ρ (x * y) (v : V) = ρ x (ρ y (v : V))
    rw [map_mul]; rfl
  have hR1 : R 1 = 1 := by ext v; simp [R, LinearMap.restrict_apply]
  have hR0 : R 0 = 0 := by ext v; simp [R, LinearMap.restrict_apply]
  have hRc : ∀ x y, Commute (R x) (R y) := fun x y => by
    show R x * R y = R y * R x
    rw [← hRmul, ← hRmul, mul_comm]
  have hnil : ∀ m, IsNilpotent (R m - algebraMap k _ (ψ m)) := by
    intro m
    have hsub : Set.MapsTo (ρ m - algebraMap k (Module.End k V) (ψ m)) (U : Set V) U := by
      intro v hv
      simp only [SetLike.mem_coe, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv ⊢
      exact U.sub_mem (hUm m hv) (U.smul_mem _ hv)
    have hn : IsNilpotent ((ρ m - algebraMap k _ (ψ m)).restrict hsub) :=
      Module.End.isNilpotent_restrict_of_le (iInf_le _ m)
        (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (ρ m) (ψ m))
    have e : R m - algebraMap k _ (ψ m) = (ρ m - algebraMap k _ (ψ m)).restrict hsub := by
      ext v
      simp only [R, LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub,
        Submodule.coe_smul]
      rfl
    rw [e]
    exact hn
  have hNc : ∀ x y, Commute (R x - algebraMap k _ (ψ x)) (R y - algebraMap k _ (ψ y)) :=
    fun x y => ((hRc x y).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commute_algebraMap_left _ _))
  have key : ∀ a : k, IsNilpotent (algebraMap k (Module.End k U) a) → a = 0 := fun a h => by
    rwa [IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective k (Module.End k U)),
      isNilpotent_iff_eq_zero] at h
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, rfl⟩
  · have h := hnil 1
    rw [hR1, ← map_one (algebraMap k (Module.End k U)), ← map_sub] at h
    exact (sub_eq_zero.1 (key _ h)).symm
  · intro x y
    have h1 := isNilpotent_perturb_mul (hNc x y) (Algebra.commute_algebraMap_left (ψ x))
      (Algebra.commute_algebraMap_left (ψ y)) (hnil x) (hnil y)
    rw [sub_add_cancel, sub_add_cancel, ← hRmul, ← map_mul] at h1
    have h2 := hnil (x * y)
    have h3 := (((Commute.refl (R (x * y))).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right
        (Algebra.commute_algebraMap_left _ _))).isNilpotent_sub h1 h2
    have e : R (x * y) - algebraMap k _ (ψ x * ψ y) - (R (x * y) - algebraMap k _ (ψ (x * y))) =
        algebraMap k (Module.End k U) (ψ (x * y) - ψ x * ψ y) := by
      rw [map_sub]; abel
    rw [e] at h3
    exact sub_eq_zero.1 (key _ h3)
  · have h := hnil 0
    rw [hR0, zero_sub, ← map_neg] at h
    exact neg_eq_zero.1 (key _ h)
  · intro x y
    have h1 := (hNc x y).isNilpotent_add (hnil x) (hnil y)
    have h2 := hnil (x + y)
    have h3 := ((hNc (x + y) x).add_right (hNc (x + y) y)).isNilpotent_sub h2 h1
    have e : R (x + y) - algebraMap k _ (ψ (x + y)) -
        (R x - algebraMap k _ (ψ x) + (R y - algebraMap k _ (ψ y))) =
        algebraMap k (Module.End k U) (ψ x + ψ y - ψ (x + y)) := by
      rw [hRadd, map_sub, map_add (f := _)]; abel
    rw [e] at h3
    exact (sub_eq_zero.1 (key _ h3)).symm

theorem exists_finset_weights {k V C : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) :
    ∃ S : Finset (C →+* k), ∀ ψ : C → k, (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥ →
      ∃ φ ∈ S, ⇑φ = ψ := by
  classical
  let U : (C → k) → Submodule k V := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hind : iSupIndep U :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps
  have hfin : {ψ | U ψ ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin.toFinset.attach.image (fun ψ => Classical.choose (weight_isRingHom ρ ψ.1
    (by have := ψ.2; rw [Set.Finite.mem_toFinset] at this; exact this))), fun ψ hψ => ?_⟩
  have hmem : ψ ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hψ
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨ψ, hmem⟩), ?_⟩
  exact Classical.choose_spec (weight_isRingHom ρ ψ hψ)

end GlobalTheory.WeightCount

namespace GlobalTheory.WeightCount

open Module

theorem maxGenEigenspace_eq_weight {k V C : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) (χ : C → k)
    (c : C) (hc : ∀ ψ : C → k, (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ χ → ψ c ≠ χ c) :
    (ρ c).maxGenEigenspace (χ c) = ⨅ d, (ρ d).maxGenEigenspace (χ d) := by
  classical
  let U : (C → k) → Submodule k V := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  have hcomm : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ
  have htop : ⨆ ψ, U ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))
  set E := (ρ c).maxGenEigenspace (χ c) with hE
  have hXE : U χ ≤ E := iInf_le _ c
  have hY : (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ≤ ⨆ μ, ⨆ (_ : μ ≠ χ c), (ρ c).maxGenEigenspace μ := by
    refine iSup₂_le fun ψ hψ => ?_
    by_cases h0 : U ψ = ⊥
    · rw [h0]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ≠ χ c) => (ρ c).maxGenEigenspace μ) (ψ c)
        (hc ψ h0 hψ) (iInf_le _ c)
  have hdisj : Disjoint E (⨆ μ, ⨆ (_ : μ ≠ χ c), (ρ c).maxGenEigenspace μ) :=
    (Module.End.independent_maxGenEigenspace (ρ c)) (χ c)
  have hsup : U χ ⊔ (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) = ⊤ := by
    rw [← htop]; exact (iSup_split_single U χ).symm
  have hEY : (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E = ⊥ := (hdisj.mono_right hY).symm.eq_bot
  calc E = (U χ ⊔ ⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E := by rw [hsup, top_inf_eq]
    _ = U χ ⊔ (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E := sup_inf_assoc_of_le _ hXE
    _ = U χ := by rw [hEY, sup_bot_eq]

theorem charpoly_lmul_includeRight (k C : Type) [Field k] [CommRing C] [Module.Free ℤ C]
    [Module.Finite ℤ C] (c : C) :
    LinearMap.charpoly (Algebra.lmul k (k ⊗[ℤ] C)
      ((Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C) c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)).map (Int.castRingHom k) := by
  have e : Algebra.lmul k (k ⊗[ℤ] C) ((Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C) c) =
      (LinearMap.mulLeft ℤ c).baseChange k := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e, LinearMap.charpoly_baseChange, algebraMap_int_eq]

theorem finrank_weight_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C]
    [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ),
    (∀ c : C, LinearMap.charpoly (σ c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) →
    ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace
          (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ r hσ χ
  classical
  let σA : C →+* Module.End k (k ⊗[ℤ] C) := (Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom
  have hA : ∀ c, LinearMap.charpoly (σA c) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)).map (Int.castRingHom k) :=
    fun c => charpoly_lmul_includeRight k C c
  obtain ⟨S1, hS1⟩ := exists_finset_weights σ
  obtain ⟨S2, hS2⟩ := exists_finset_weights σA
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int k C (S1 ∪ S2) χ
  have sepH : ∀ ψ : C → k, (⨅ d, (σ d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ ⇑χ → ψ c ≠ χ c := by
    intro ψ h hne
    obtain ⟨φ, hφS, rfl⟩ := hS1 ψ h
    exact hc φ (Finset.mem_union_left _ hφS) (fun e => hne (by rw [e]))
  have sepA : ∀ ψ : C → k, (⨅ d, (σA d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ ⇑χ → ψ c ≠ χ c := by
    intro ψ h hne
    obtain ⟨φ, hφS, rfl⟩ := hS2 ψ h
    exact hc φ (Finset.mem_union_right _ hφS) (fun e => hne (by rw [e]))
  show Module.finrank k ↥(⨅ d : C, (σ d).maxGenEigenspace (χ d)) =
    r * Module.finrank k ↥(⨅ d : C, (σA d).maxGenEigenspace (χ d))
  rw [← maxGenEigenspace_eq_weight σ χ c sepH, ← maxGenEigenspace_eq_weight σA χ c sepA,
    LinearMap.finrank_maxGenEigenspace_eq, LinearMap.finrank_maxGenEigenspace_eq, hσ c, hA c,
    Polynomial.map_pow, ← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_pow,
    Multiset.count_nsmul]

end GlobalTheory.WeightCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpolyStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WeightCount.finrank_weight_eq) | (exact GlobalTheory.WeightCount.finrank_weight_eq) | (intros; apply GlobalTheory.WeightCount.finrank_weight_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceTensorRingHomFinrankPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceTensorRingHomFinrankPos
open scoped TensorProduct

namespace GlobalTheory

theorem weightSpace_tensor_ringHom_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ χ
  let φ : k ⊗[ℤ] C →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)
  have hφs : Function.Surjective φ := fun a => ⟨algebraMap k (k ⊗[ℤ] C) a, by rw [φ.commutes]; rfl⟩
  let m : Ideal (k ⊗[ℤ] C) := RingHom.ker φ
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφs
  haveI : IsArtinianRing (k ⊗[ℤ] C) := IsArtinianRing.of_finite k (k ⊗[ℤ] C)
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (m ^ j), fun a b h => Ideal.pow_le_pow_right h⟩ :
      ℕ →o (Ideal (k ⊗[ℤ] C))ᵒᵈ)
  have hst : ∀ j, N ≤ j → m ^ N = m ^ j := fun j hj => hN j hj
  have hJJ : IsIdempotentElem (m ^ (N + 1)) := by
    show m ^ (N + 1) * m ^ (N + 1) = m ^ (N + 1)
    rw [← pow_add, ← hst (N + 1 + (N + 1)) (by omega), hst (N + 1) (by omega)]
  obtain ⟨e, he, hJe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian (m ^ (N + 1)))).mp hJJ
  have hJe' : m ^ (N + 1) = Ideal.span {e} := hJe
  have hv : (1 - e : k ⊗[ℤ] C) ≠ 0 := by
    intro h
    have h1 : e = 1 := (sub_eq_zero.mp h).symm
    have : m ^ (N + 1) = ⊤ := by rw [hJe', h1, Ideal.span_singleton_one]
    exact hm.ne_top (top_le_iff.mp (this ▸ Ideal.pow_le_self (by omega)))
  have key : ∀ x ∈ m, x ^ (N + 1) * (1 - e) = 0 := by
    intro x hx
    have hx' : x ^ (N + 1) ∈ Ideal.span {e} := hJe' ▸ Ideal.pow_mem_pow hx (N + 1)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]
  refine lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 ?_)
  rw [Submodule.ne_bot_iff]
  refine ⟨1 - e, ?_, hv⟩
  rw [Submodule.mem_iInf]
  intro c
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨N + 1, ?_⟩
  let x : k ⊗[ℤ] C := (1 : k) ⊗ₜ c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hxm : x ∈ m := by
    simp [m, x, φ, RingHom.mem_ker]
  have hf : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c) - χ c • (1 : Module.End k (k ⊗[ℤ] C))
      = Algebra.lmul k (k ⊗[ℤ] C) x := by
    ext y
    simp [x, sub_mul, Algebra.smul_def]
  rw [hf, ← map_pow]
  exact key x hxm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceTensorRingHomFinrankPosStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightSpace_tensor_ringHom_finrank_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.weightSpace_tensor_ringHom_pos) | (exact GlobalTheory.weightSpace_tensor_ringHom_pos) | (intros; apply GlobalTheory.weightSpace_tensor_ringHom_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTRank

theorem finrank_quot_mSub : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) = r := by
  intro k _ _ C _ _ _ H _ _ _ σ r hP hc χ
  have e1 := GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k C H σ r hc χ
  have e2 := GlobalTheory.T.finrank_weightSpace_projective_tensor_eq k C H σ hP χ
  have hpos := GlobalTheory.T.weightSpace_tensor_ringHom_finrank_pos k C χ
  rw [e1] at e2
  exact (Nat.eq_of_mul_eq_mul_right hpos e2).symm

theorem finrank_quot : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ i, Module.finrank k (HdR o₀.A ⧸ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤) = D.m * D.n := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht i
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o₀.A g o₀.ab hg
  haveI := hfd
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o₀.geom k (𝟙 _) β (by rw [Category.id_comp, ht])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O c)) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o₀.A o₀.ab (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.HTCount.crysAct_apply, e, GlobalTheory.T.charpoly_la_eq_pow p D c]
  have hproj := GlobalTheory.CrysProj.hdR_projective D.F k o₀.A o₀.ab (o₀.act.toF D)
  exact finrank_quot_mSub k (𝓞 D.F) (HdR o₀.A) ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O))
    (D.m * D.n) hproj hc (β.comp (b.t i))

end GlobalTheory.HTRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ i, Module.finrank k (HdR o₀.A ⧸ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤) = D.m * D.n := by
  first | (exact @GlobalTheory.HTRank.finrank_quot) | (exact GlobalTheory.HTRank.finrank_quot) | (intros; apply GlobalTheory.HTRank.finrank_quot  <;> assumption)
end

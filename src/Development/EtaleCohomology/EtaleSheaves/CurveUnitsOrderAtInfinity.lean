module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfB
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfA
namespace LateralTheory.E.E4

def LeafUnitsFG : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Group.FG (Bˣ ⧸ (Units.map (algebraMap k B).toMonoidHom).range)

theorem units_range_le_pow (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] :
    (Units.map (algebraMap k B).toMonoidHom).range ≤ (powMonoidHom q : Bˣ →* Bˣ).range := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne q)] at hz
    exact a.ne_zero hz.symm
  refine ⟨Units.map (algebraMap k B).toMonoidHom (Units.mk0 z hz0), ?_⟩
  ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
  rw [← map_pow, hz]

theorem LeafUnits_of (hFG : LeafUnitsFG) : LeafUnits := by
  intro q _ k B _ _ _ _ _ _
  have hle := units_range_le_pow q k B
  let N := (powMonoidHom q : Bˣ →* Bˣ).range
  let M := (Units.map (algebraMap k B).toMonoidHom).range
  have : Group.FG (Bˣ ⧸ M) := hFG k B
  let φ : Bˣ ⧸ M →* Bˣ ⧸ N := QuotientGroup.map M N (MonoidHom.id _) hle
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk u, rfl⟩
  have : Group.FG (Bˣ ⧸ N) := Group.fg_of_surjective hφ
  apply CommGroup.finite_of_fg_isMulTorsion
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨q, Nat.pos_of_ne_zero (NeZero.ne q), ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

end LateralTheory.E.E4
end

namespace LateralTheory.E.E4

theorem mem_range_of_isIntegral {k B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] {x : B} (hx : IsIntegral k x) : x ∈ Set.range (algebraMap k B) := by
  have h : (minpoly k x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx)
  have hm : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hx
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul, map_add (f := _),
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hm
  exact ⟨-(minpoly k x).coeff 0, by rw [map_neg]; exact hm.symm⟩

theorem fg_subgroup_mult (n : ℕ) (H : Subgroup (Multiplicative (Fin n → ℤ))) : Group.FG H := by
  have : IsNoetherian ℤ (Additive (Multiplicative (Fin n → ℤ))) :=
    isNoetherian_of_linearEquiv (AddEquiv.additiveMultiplicative (Fin n → ℤ)).symm.toIntLinearEquiv
  rw [Group.fg_iff_subgroup_fg, Subgroup.fg_iff_add_fg]
  have := IsNoetherian.noetherian (R := ℤ) H.toAddSubgroup.toIntSubmodule
  exact (Submodule.fg_iff_addSubgroup_fg _).1 this

def LeafUnitsOrd : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B],
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsFG_of (h : LeafUnitsOrd) : LeafUnitsFG := by
  intro k B _ _ _ _ _ _
  obtain ⟨n, φ, hφ⟩ := h k B
  have hker : φ.ker ≤ (Units.map (algebraMap k B).toMonoidHom).range := by
    intro u hu
    obtain ⟨a, ha⟩ := mem_range_of_isIntegral (hφ u hu)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact u.ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩
  have : Group.FG φ.range := fg_subgroup_mult n _
  have : Group.FG (Bˣ ⧸ φ.ker) :=
    Group.fg_of_surjective (f := ((QuotientGroup.quotientKerEquivRange φ).symm : φ.range →* Bˣ ⧸ φ.ker))
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map φ.ker (Units.map (algebraMap k B).toMonoidHom).range (MonoidHom.id _) hker) ?_
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk u, rfl⟩

def LeafUnitsOrdCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem isIntegral_of_isField {k B : Type} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (hB : IsField B) (x : B) : IsIntegral k x := by
  let _ := hB.toField
  have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  exact Algebra.IsIntegral.isIntegral x

theorem LeafUnitsOrd_of (h : LeafUnitsOrdCurve) : LeafUnitsOrd := by
  intro k B _ _ _ _ _ _
  by_cases hB : IsField B
  · exact ⟨0, 1, fun u _ => isIntegral_of_isField hB _⟩
  · exact h k B hB

theorem LeafUnitsFG_of_curve (h : LeafUnitsOrdCurve) : LeafUnitsFG := LeafUnitsFG_of (LeafUnitsOrd_of h)

def LeafNoetherCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ g : Polynomial k →ₐ[k] B, Function.Injective g ∧ g.Finite

def LeafOrdAtInfinity : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsOrdCurve_of (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsOrdCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨g, hg, hf⟩ := hN k B hB
  exact hV k B g hg hf

theorem LeafUnitsFG_of_leaves (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_curve (LeafUnitsOrdCurve_of hN hV)

end LateralTheory.E.E4
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafOrdInfLocalPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafOrdInfHomPf
namespace LateralTheory.E.E4

open Polynomial

def LeafOrdInfLocal : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    ∃ h : Polynomial k, h.eval 0 ≠ 0 ∧
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹,
        (Polynomial.aeval (algebraMap B (FractionRing B) (g Polynomial.X))⁻¹ h)⁻¹})
      (algebraMap B (FractionRing B) (u : B))

def LeafLocGlobInf : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L), Transcendental k t →
  ∀ (x : L) (h : Polynomial k), h.eval 0 ≠ 0 → IsIntegral (Algebra.adjoin k {t}) x →
  IsIntegral (Algebra.adjoin k {t⁻¹, (Polynomial.aeval t⁻¹ h)⁻¹}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x

theorem LeafOrdInfHom_of (hO : LeafOrdInfLocal) (hG : LeafLocGlobInf) : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B)) := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨n, φ, hφ⟩ := hO k B g hg hf
  refine ⟨n, φ, fun u hu => ?_⟩
  obtain ⟨h, h0, hloc⟩ := hφ u hu
  set L := FractionRing B
  set T : L := algebraMap B L (g Polynomial.X)
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  let G : Polynomial k →ₐ[k] L := (IsScalarTower.toAlgHom k B L).comp g
  have hG' : Function.Injective G := hinjL.comp hg
  have hT : Transcendental k T := by
    intro ⟨p, hp0, hp⟩
    apply hp0
    apply hG'
    rw [map_zero]
    have : G p = Polynomial.aeval T p := by
      rw [show G p = G (Polynomial.aeval Polynomial.X p) by simp, ← Polynomial.aeval_algHom_apply]; rfl
    rw [this]; exact hp
  have hint : IsIntegral (Algebra.adjoin k {T}) (algebraMap B L (u : B)) := by
    obtain ⟨p, hpm, hp⟩ := (RingHom.IsIntegral.of_finite hf) (u : B)
    let f : Polynomial k →ₐ[k] Algebra.adjoin k {T} := Polynomial.aeval ⟨T, Algebra.subset_adjoin rfl⟩
    have hfG : ((algebraMap (Algebra.adjoin k {T}) L).comp f.toRingHom) = (algebraMap B L).comp g.toRingHom := by
      have : (IsScalarTower.toAlgHom k (Algebra.adjoin k {T}) L).comp f = G := by
        apply Polynomial.algHom_ext; simp [f, G, T]
      exact congrArg AlgHom.toRingHom this
    refine ⟨p.map f.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hfG, ← Polynomial.hom_eval₂]
    change algebraMap B L (Polynomial.eval₂ g.toRingHom (u : B) p) = 0
    rw [hp, map_zero]
  exact hG k L T hT _ h h0 hint hloc

open Polynomial

def lgiDen {k L : Type} [Field k] [Field L] [Algebra k L] (R : Subalgebra k L) (c : L) (hc : c ∈ R) :
    Subalgebra k L where
  carrier := {y | ∃ m : ℕ, c ^ m * y ∈ R}
  mul_mem' := by
    rintro y z ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have : c ^ (m + n) * (y * z) = (c ^ m * y) * (c ^ n * z) := by ring
    rw [this]; exact R.mul_mem hm hn
  add_mem' := by
    rintro y z ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have : c ^ (m + n) * (y + z) = c ^ n * (c ^ m * y) + c ^ m * (c ^ n * z) := by ring
    rw [this]; exact R.add_mem (R.mul_mem (R.pow_mem hc _) hm) (R.mul_mem (R.pow_mem hc _) hn)
  algebraMap_mem' := fun a => ⟨0, by simpa using R.algebraMap_mem a⟩

theorem lgi_adjoin_le {k L : Type} [Field k] [Field L] [Algebra k L] (s c : L) (hc : c ∈ Algebra.adjoin k {s})
    (hc0 : c ≠ 0) : Algebra.adjoin k {s, c⁻¹} ≤ lgiDen (Algebra.adjoin k {s}) c hc := by
  rw [Algebra.adjoin_le_iff]
  rintro y (rfl | rfl)
  · exact ⟨0, by simpa using Algebra.subset_adjoin rfl⟩
  · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hc0]; exact Subalgebra.one_mem _⟩

theorem lgi_mult {k L : Type} [Field k] [Field L] [Algebra k L] (s c : L) (hc : c ∈ Algebra.adjoin k {s})
    (hc0 : c ≠ 0) (x : L) (hx : IsIntegral (Algebra.adjoin k {s, c⁻¹}) x) :
    ∃ M : ℕ, IsIntegral (Algebra.adjoin k {s}) (c ^ M * x) := by
  set R := Algebra.adjoin k {s}
  set A := Algebra.adjoin k {s, c⁻¹}
  obtain ⟨p, hpm, hp⟩ := hx
  have hD : ∀ i, ∃ m : ℕ, c ^ m * (p.coeff i : L) ∈ R := fun i => lgi_adjoin_le s c hc hc0 (p.coeff i).2
  choose m hm using hD
  set M := ∑ i ∈ Finset.range (p.natDegree + 1), m i
  have hM : ∀ i, c ^ M * (p.coeff i : L) ∈ R := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · have hle : m i ≤ M := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      rw [show M = (M - m i) + m i by omega, pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem hc _) (hm i)
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  set q : L[X] := C (c ^ M) * p.map (algebraMap A L)
  have hl : q ∈ lifts (algebraMap R L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨c ^ M * (p.coeff n : L), hM n⟩, ?_⟩
    show _ = (C (c ^ M) * p.map (algebraMap A L)).coeff n
    rw [coeff_C_mul, coeff_map]; rfl
  obtain ⟨Q, hQ0⟩ := hl
  have hQ : Q.map (algebraMap R L) = q := hQ0
  have hinj : Function.Injective (algebraMap R L) := Subtype.val_injective
  have hlc : (algebraMap R L) Q.leadingCoeff = c ^ M := by
    rw [← leadingCoeff_map_of_injective hinj, hQ]
    simp only [q, leadingCoeff_mul, leadingCoeff_C, (hpm.map (algebraMap A L)).leadingCoeff, mul_one]
  have hQx : aeval x Q = 0 := by
    rw [aeval_def, ← eval_map, hQ]
    simp only [q, eval_mul, eval_C, eval_map]
    rw [hp, mul_zero]
  refine ⟨M, ?_⟩
  have := isIntegral_leadingCoeff_smul Q x hQx
  rw [Algebra.smul_def, hlc] at this
  exact this

theorem lgi_mono {k L : Type} [Field k] [Field L] [Algebra k L] {S T : Subalgebra k L} (hST : S ≤ T) (x : L)
    (hx : IsIntegral S x) : IsIntegral T x := by
  obtain ⟨p, hm, hp⟩ := hx
  refine ⟨p.map (Subalgebra.inclusion hST).toRingHom, hm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

theorem integral_over_inverse_transcendental_of_local_at_infinity_holds : LeafLocGlobInf := by
  intro k L _ _ _ t ht x h h0 hx hloc
  have ht0 : t ≠ 0 := by rintro rfl; exact ht isAlgebraic_zero
  set s := t⁻¹
  have hs' : Transcendental k s := fun hh => ht (by simpa [s] using hh.inv)
  set R := Algebra.adjoin k {s}
  have hsR : s ∈ R := Algebra.subset_adjoin rfl
  have hs0 : s ≠ 0 := inv_ne_zero ht0

  have h1 : IsIntegral (Algebra.adjoin k {s, s⁻¹}) x := by
    refine lgi_mono ?_ x hx
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact Algebra.subset_adjoin (by simp [s])
  obtain ⟨M1, hM1⟩ := lgi_mult s s hsR hs0 x h1
  have hcR : aeval s h ∈ R := Polynomial.aeval_mem_adjoin_singleton k s
  have hh0 : h ≠ 0 := by rintro rfl; simp at h0
  have hc0 : aeval s h ≠ 0 := fun e => hs' ⟨h, hh0, e⟩
  obtain ⟨M2, hM2⟩ := lgi_mult s (aeval s h) hcR hc0 x hloc
  have hcop : IsCoprime ((X : k[X]) ^ M1) (h ^ M2) := by
    apply IsCoprime.pow
    rw [Irreducible.coprime_iff_not_dvd irreducible_X, X_dvd_iff, coeff_zero_eq_eval_zero]
    exact h0
  obtain ⟨a, b, hab⟩ := hcop
  have hab' : aeval s a * s ^ M1 + aeval s b * (aeval s h) ^ M2 = 1 := by
    have := congrArg (aeval s) hab
    simpa using this
  have hxe : x = aeval s a * (s ^ M1 * x) + aeval s b * ((aeval s h) ^ M2 * x) := by
    linear_combination (-x) * hab'
  have hA : ∀ f : k[X], IsIntegral R (aeval s f) := fun f => by
    have : aeval s f ∈ R := Polynomial.aeval_mem_adjoin_singleton k s
    exact isIntegral_algebraMap (x := (⟨_, this⟩ : R))
  rw [hxe]
  exact ((hA a).mul hM1).add ((hA b).mul hM2)

theorem LeafOrdInfHom_of_local (hO : LeafOrdInfLocal) : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B)) :=
  LeafOrdInfHom_of hO integral_over_inverse_transcendental_of_local_at_infinity_holds

end LateralTheory.E.E4
end

namespace LateralTheory.E.E4

open Polynomial

def LeafFinInf : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  Transcendental k (algebraMap B (FractionRing B) (g Polynomial.X))⁻¹ ∧
  FiniteDimensional (IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹}) (FractionRing B)

def LeafFinVal : Prop := ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  FiniteDimensional (IntermediateField.adjoin k {s}) L →
  ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 →
    ∃ (d : ℕ) (a b : ℕ → Polynomial k), (∀ i, (b i).eval 0 ≠ 0) ∧
      (x : L) ^ d + ∑ i ∈ Finset.range d, (aeval s (a i) / aeval s (b i)) * (x : L) ^ i = 0

def LeafClearDen : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  ∀ (x : L) (d : ℕ) (a b : ℕ → Polynomial k), (∀ i, (b i).eval 0 ≠ 0) →
    x ^ d + ∑ i ∈ Finset.range d, (aeval s (a i) / aeval s (b i)) * x ^ i = 0 →
    ∃ h : Polynomial k, h.eval 0 ≠ 0 ∧ IsIntegral (Algebra.adjoin k {s, (aeval s h)⁻¹}) x

theorem LeafOrdInfLocal_of (h1 : LeafFinInf) (h2 : LeafFinVal) (h3 : LeafClearDen) : LeafOrdInfLocal := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨hT, hfd⟩ := h1 k B g hg hf
  obtain ⟨n, φ, hφ⟩ := h2 k (FractionRing B) _ hT hfd
  refine ⟨n, φ.comp (Units.map (algebraMap B (FractionRing B) : B →* FractionRing B)), fun u hu => ?_⟩
  obtain ⟨d, a, b, hb, heq⟩ := hφ (Units.map (algebraMap B (FractionRing B) : B →* FractionRing B) u) hu
  exact h3 k (FractionRing B) _ hT _ d a b hb heq

theorem integral_after_clearing_polynomial_denominators_holds : LeafClearDen := by
  intro k L _ _ _ s hs x d a b hb heq
  have hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0 := fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)
  have hb0 : ∀ i, b i ≠ 0 := fun i h => hb i (by simp [h])
  set h := ∏ i ∈ Finset.range d, b i with hh
  have he : h.eval 0 ≠ 0 := by
    rw [hh, Polynomial.eval_prod]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  refine ⟨h, he, ?_⟩
  set A := Algebra.adjoin k {s, (aeval s h)⁻¹}
  have hpol : ∀ p : Polynomial k, aeval s p ∈ A := fun p =>
    Algebra.adjoin_mono (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact Or.inl rfl)
      (Polynomial.aeval_mem_adjoin_singleton k s)
  have hinv : (aeval s h)⁻¹ ∈ A := Algebra.subset_adjoin (Or.inr rfl)
  have hmem : ∀ i ∈ Finset.range d, aeval s (a i) / aeval s (b i) ∈ A := by
    intro i hi
    have hsplit : h = b i * ∏ j ∈ (Finset.range d).erase i, b j := (Finset.mul_prod_erase _ _ hi).symm
    have hr : aeval s (∏ j ∈ (Finset.range d).erase i, b j) ≠ 0 :=
      hne _ (Finset.prod_ne_zero_iff.mpr (fun j _ => hb0 j))
    have hbi : aeval s (b i) ≠ 0 := hne _ (hb0 i)
    have : aeval s (a i) / aeval s (b i) =
        aeval s (a i * ∏ j ∈ (Finset.range d).erase i, b j) * (aeval s h)⁻¹ := by
      rw [hsplit, map_mul, map_mul]; field_simp
    rw [this]; exact A.mul_mem (hpol _) hinv
  let c : ℕ → A := fun i => if hi : i ∈ Finset.range d then ⟨_, hmem i hi⟩ else 0
  have hdeg : (∑ i ∈ Finset.range d, C (c i) * X ^ i : A[X]).degree < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast Finset.mem_range.mp hi)
  refine ⟨(X ^ d + ∑ i ∈ Finset.range d, C (c i) * X ^ i : A[X]), monic_X_pow_add hdeg, ?_⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum]
  rw [← heq]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < d := Finset.mem_range.mp hi
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  congr 1
  simp only [c, Finset.mem_range, hi', dif_pos]
  rfl

theorem LeafOrdInfLocal_of' (h1 : LeafFinInf) (h2 : LeafFinVal) : LeafOrdInfLocal :=
  LeafOrdInfLocal_of h1 h2 integral_after_clearing_polynomial_denominators_holds

end LateralTheory.E.E4
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfF
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfE
namespace LateralTheory.E.E4

def LeafOrdInfHom : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B))

def LeafIntBoth : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L), Transcendental k t → ∀ x : L,
  IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x

theorem LeafOrdAtInfinity_of (hV : LeafOrdInfHom) (hI : LeafIntBoth) : LeafOrdAtInfinity := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨n, φ, hφ⟩ := hV k B g hg hf
  refine ⟨n, φ, fun u hu => ?_⟩
  set L := FractionRing B
  set T : L := algebraMap B L (g Polynomial.X)
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  let G : Polynomial k →ₐ[k] L := (IsScalarTower.toAlgHom k B L).comp g
  have hG : Function.Injective G := hinjL.comp hg
  have hT : Transcendental k T := by
    intro ⟨p, hp0, hp⟩
    apply hp0
    apply hG
    rw [map_zero]
    have : G p = Polynomial.aeval T p := by
      rw [show G p = G (Polynomial.aeval Polynomial.X p) by simp, ← Polynomial.aeval_algHom_apply]; rfl
    rw [this]; exact hp
  have hint : IsIntegral (Algebra.adjoin k {T}) (algebraMap B L (u : B)) := by
    obtain ⟨p, hpm, hp⟩ := (RingHom.IsIntegral.of_finite hf) (u : B)
    let f : Polynomial k →ₐ[k] Algebra.adjoin k {T} := Polynomial.aeval ⟨T, Algebra.subset_adjoin rfl⟩
    have hfG : ((algebraMap (Algebra.adjoin k {T}) L).comp f.toRingHom) = (algebraMap B L).comp g.toRingHom := by
      have : (IsScalarTower.toAlgHom k (Algebra.adjoin k {T}) L).comp f = G := by
        apply Polynomial.algHom_ext; simp [f, G, T]
      exact congrArg AlgHom.toRingHom this
    refine ⟨p.map f.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hfG, ← Polynomial.hom_eval₂]
    change algebraMap B L (Polynomial.eval₂ g.toRingHom (u : B) p) = 0
    rw [hp, map_zero]
  have := hI k L T hT _ hint (hφ u hu)
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom k B L) hinjL).mp this

end LateralTheory.E.E4
end

namespace LateralTheory.E.E4

open Polynomial

theorem mem_bot_of_mem_adjoin_inv {k L : Type} [Field k] [Field L] [Algebra k L] (t : L) (ht : Transcendental k t)
    (c : L) (h1 : c ∈ Algebra.adjoin k {t}) (h2 : c ∈ Algebra.adjoin k {t⁻¹}) : c ∈ (⊥ : Subalgebra k L) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h1 h2
  obtain ⟨p, rfl⟩ := h1
  obtain ⟨q, hq⟩ := h2
  have ht0 : t ≠ 0 := by
    rintro rfl; exact ht (isAlgebraic_zero)
  set N := q.natDegree
  have key : aeval t (X ^ N * p) = aeval t (reflect N q) := by
    let _ : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
    have h := eval₂_reflect_mul_pow (algebraMap k L) t⁻¹ N q le_rfl
    rw [invOf_eq_inv, inv_inv] at h
    have hq' : aeval t⁻¹ q = aeval t p := hq
    rw [aeval_def, aeval_def] at hq'
    rw [map_mul, map_pow, aeval_X, aeval_def, aeval_def, ← hq', ← h, mul_comm, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ ht0, one_pow, mul_one]
  have hinj : Function.Injective (aeval t : k[X] →ₐ[k] L) := transcendental_iff_injective.mp ht
  have heq := hinj key
  by_cases hp : p = 0
  · simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (reflect N q).natDegree ≤ N := natDegree_reflect_le.trans (by simp [N])
  have hp0 : p.natDegree = 0 := by rw [heq] at hdeg; omega
  rw [eq_C_of_natDegree_eq_zero hp0]
  simp

def LeafMinpolyCoeff : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  ∀ (F : IntermediateField k L), F = IntermediateField.adjoin k {s} → ∀ x : L, IsIntegral (Algebra.adjoin k {s}) x →
  ∀ i : ℕ, ((minpoly F x).coeff i : L) ∈ Algebra.adjoin k {s}

theorem isIntegral_adjoin_of {k L : Type} [Field k] [Field L] [Algebra k L] (s : L) (x : L)
    (hx : IsIntegral (Algebra.adjoin k {s}) x) : IsIntegral (IntermediateField.adjoin k {s}) x := by
  obtain ⟨p, hm, hp⟩ := hx
  let ι : Algebra.adjoin k {s} →+* IntermediateField.adjoin k {s} :=
    Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k {s}) |>.toRingHom
  refine ⟨p.map ι, hm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

theorem LeafIntBoth_of' (hM : LeafMinpolyCoeff) : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L),
    Transcendental k t → ∀ x : L,
    IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x := by
  intro k L _ _ _ t ht x h1 h2
  have ht' : Transcendental k t⁻¹ := fun h => ht (by simpa using h.inv)
  set F := IntermediateField.adjoin k {t}
  have hEq : F = IntermediateField.adjoin k {t⁻¹} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  have hxF : IsIntegral F x := isIntegral_adjoin_of t x h1
  have hc : ∀ i, ((minpoly F x).coeff i : L) ∈ (⊥ : Subalgebra k L) := fun i =>
    mem_bot_of_mem_adjoin_inv t ht _ (hM k L t ht F rfl x h1 i) (hM k L t⁻¹ ht' F hEq x h2 i)
  have hl : minpoly F x ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hc n)
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hxF)
  refine ⟨P, hPm, ?_⟩
  have := minpoly.aeval F x
  rw [← hP, aeval_map_algebraMap] at this
  exact this

theorem LeafIntBoth_of (hM : LeafMinpolyCoeff) : LeafIntBoth := LeafIntBoth_of' hM

theorem LeafOrdAtInfinity_of_cut (hV : LeafOrdInfHom) (hM : LeafMinpolyCoeff) : LeafOrdAtInfinity :=
  LeafOrdAtInfinity_of hV (LeafIntBoth_of hM)

end LateralTheory.E.E4
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfD
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfC
namespace LateralTheory.E.E4

def LeafNoetherDim : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] B),
  Function.Injective g → g.Finite → s = 1

theorem LeafNoetherCurve_of (hD : LeafNoetherDim) : LeafNoetherCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨s, g, hg, hf⟩ := exists_finite_inj_algHom_of_fg k B
  obtain rfl := hD k B hB s g hg hf
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
  refine ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem LeafUnitsFG_of_dim (hD : LeafNoetherDim) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_leaves (LeafNoetherCurve_of hD) hV

end LateralTheory.E.E4
end

namespace LateralTheory.E.E4

open MvPolynomial

noncomputable def killFirst (k : Type) [Field k] (s j : ℕ) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  aeval (fun i => if i.val < j then 0 else X i)

lemma killFirst_X (k : Type) [Field k] (s j : ℕ) (i : Fin s) :
    killFirst k s j (X i) = if i.val < j then 0 else X i := by
  simp [killFirst]

lemma X_mem_ker_killFirst (k : Type) [Field k] (s j : ℕ) (i : Fin s) (hi : i.val < j) :
    (X i : MvPolynomial (Fin s) k) ∈ RingHom.ker (killFirst k s j) := by
  rw [RingHom.mem_ker]; erw [killFirst_X]; simp [hi]

lemma X_not_mem_ker_killFirst (k : Type) [Field k] (s j : ℕ) (i : Fin s) (hi : ¬ i.val < j) :
    (X i : MvPolynomial (Fin s) k) ∉ RingHom.ker (killFirst k s j) := by
  rw [RingHom.mem_ker]; erw [killFirst_X]; simp [hi, X_ne_zero]

theorem LeafNoetherDim_of : LeafNoetherDim := by
  intro k B _ _ _ _ _ _ hB s g hg hf
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨fun x => hf.to_isIntegral x⟩
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) k) B) := hg
  by_contra hs
  rcases Nat.lt_or_gt_of_ne hs with h0 | h2
  ·
    obtain rfl : s = 0 := by omega
    apply hB
    rw [← Algebra.IsIntegral.isField_iff_isField hinj]
    exact MulEquiv.isField (Field.toIsField k) (isEmptyAlgEquiv k (Fin 0)).toMulEquiv
  ·
    set A := MvPolynomial (Fin s) k
    let P1 : Ideal A := RingHom.ker (killFirst k s 1)
    let P2 : Ideal A := RingHom.ker (killFirst k s 2)
    have hP1 : P1.IsPrime := RingHom.ker_isPrime _
    have hP2 : P2.IsPrime := RingHom.ker_isPrime _
    let i0 : Fin s := ⟨0, by omega⟩
    let i1 : Fin s := ⟨1, by omega⟩
    have h12 : P1 ≤ P2 := by
      intro p hp
      simp only [P1, P2, RingHom.mem_ker] at hp ⊢
      have : killFirst k s 2 = (killFirst k s 2).comp (killFirst k s 1) := by
        apply MvPolynomial.algHom_ext; intro i
        simp only [AlgHom.comp_apply, killFirst_X]
        by_cases h : i.val < 1
        · simp [h, show i.val < 2 by omega]
        · simp [h, killFirst_X]
      rw [this, AlgHom.comp_apply]; erw [hp]; simp
    have x0P1 : (X i0 : A) ∈ P1 := X_mem_ker_killFirst k s 1 i0 (by simp [i0])
    have x1P2 : (X i1 : A) ∈ P2 := X_mem_ker_killFirst k s 2 i1 (by simp [i1])
    have x1P1 : (X i1 : A) ∉ P1 := X_not_mem_ker_killFirst k s 1 i1 (by simp [i1])
    have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
    have hc0 : Ideal.under A (⊥ : Ideal B) = ⊥ := by
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨Q1, -, hQ1, hcQ1⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P1 (⊥ : Ideal B) (by rw [hc0]; exact bot_le)
    obtain ⟨Q2, hQ12, hQ2, hcQ2⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P2 Q1 (by rw [hcQ1]; exact h12)
    have hQ1ne : Q1 ≠ ⊥ := by
      rintro rfl
      rw [hc0] at hcQ1
      apply X_ne_zero (R := k) i0
      have : (X i0 : A) ∈ (⊥ : Ideal A) := hcQ1 ▸ x0P1
      simp at this
    have hQ1max : Q1.IsMaximal := hQ1.isMaximal hQ1ne
    have hne : Q1 ≠ Q2 := by
      rintro rfl
      rw [hcQ1] at hcQ2
      exact x1P1 (hcQ2 ▸ x1P2)
    have := hQ1max.eq_of_le hQ2.ne_top hQ12
    exact hne this

end LateralTheory.E.E4
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafFinValPf
namespace LateralTheory.E.E4

open Polynomial IsDedekindDomain

theorem finVal_dedekind (D L : Type) [CommRing D] [IsDedekindDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] [Finite (HeightOneSpectrum D)] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 →
      (x : L) ∈ (algebraMap D L).range := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (HeightOneSpectrum D)
  refine ⟨n, MonoidHom.mk' (fun x => Multiplicative.ofAdd
    (fun i => WithZero.log ((e.symm i).valuation L (x : L)))) ?_, ?_⟩
  · intro x y
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [Units.val_mul, Pi.add_apply, map_mul]
    exact WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  · intro x hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h : WithZero.log ((e.symm (e v)).valuation L (x : L)) = 0 :=
      congrFun (congrArg Multiplicative.toAdd hx) (e v)
    rw [e.symm_apply_apply] at h
    exact WithZero.le_exp_of_log_le h.le

theorem finVal_finite (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsDedekindDomain D]
    [Algebra A D] [Algebra.IsIntegral A D] [IsDomain A] [Module.IsTorsionFree A D] :
    Finite (HeightOneSpectrum D) := by
  have hf := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal A) D
  have := hf.to_subtype
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal A).primesOver D)
    (fun v => ⟨v.asIdeal, v.isPrime, ⟨?_⟩⟩) ?_
  · have := v.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) v.asIdeal)).symm
  · intro v w h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)

theorem finVal_sep (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  have := integralClosure.isDedekindDomain A K L
  have := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A (integralClosure A L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have := finVal_finite A (integralClosure A L)
  obtain ⟨n, φ, h⟩ := finVal_dedekind (integralClosure A L) L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  rw [← hy]
  exact y.2

theorem finVal_gen (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  obtain ⟨n, φ, h⟩ := finVal_sep A K (separableClosure K L)
  refine ⟨n, φ.comp (Units.map (Algebra.norm (separableClosure K L))), fun x hx => ?_⟩
  have h1 : IsIntegral A (Algebra.norm (separableClosure K L) (x : L)) := h _ hx
  obtain ⟨m, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K L)
    (ringExpChar (separableClosure K L)) (x : L)
  have hq : 0 < ringExpChar (separableClosure K L) ^ m := expChar_pow_pos (separableClosure K L) _ m
  have h2 : IsIntegral A (y ^ Module.finrank (separableClosure K L) L) := by
    rw [← Algebra.norm_algebraMap, hy, map_pow]
    exact h1.pow _
  have h3 : IsIntegral A y := h2.of_pow Module.finrank_pos
  have : IsScalarTower A (separableClosure K L) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h4 : IsIntegral A (algebraMap (separableClosure K L) L y) := h3.algebraMap
  rw [hy] at h4
  exact h4.of_pow hq

theorem LeafFinVal_of : LeafFinVal := by
  intro k L _ _ _ _ s hs hfd
  have hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0 := fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)
  let P : Ideal k[X] := RingHom.ker (evalRingHom (0 : k))
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let A := Localization.AtPrime P
  let K := IntermediateField.adjoin k {s}
  let t : K := ⟨s, IntermediateField.mem_adjoin_simple_self k s⟩
  have hval : ∀ p : k[X], ((aeval t p : K) : L) = aeval s p := fun p =>
    (aeval_algHom_apply K.val t p).symm
  have hne' : ∀ p : k[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h0 => hne p hp (by rw [← hval, h0]; rfl)
  have hu : ∀ y : P.primeCompl, IsUnit ((aeval t : k[X] →ₐ[k] K).toRingHom y) := by
    intro y
    refine (hne' y ?_).isUnit
    intro h0
    exact y.2 (by rw [h0]; exact P.zero_mem)
  let f : A →+* K := IsLocalization.lift (M := P.primeCompl) hu
  have hf : ∀ p : k[X], f (algebraMap k[X] A p) = aeval t p := fun p => IsLocalization.lift_eq hu p
  have hfrac : ∀ c : A, ∃ a b : k[X], b.eval 0 ≠ 0 ∧ f c = aeval t a / aeval t b := by
    intro c
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨a, b, b.2, ?_⟩
    have := congrArg f hab
    rw [map_mul, hf, hf] at this
    exact (eq_div_iff (hu b).ne_zero).mpr this
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    have h1 := congrArg f hab
    rw [map_mul, hc, zero_mul, hf] at h1
    have ha : a = 0 := by
      by_contra ha
      exact hne' a ha h1.symm
    simp only [ha, map_zero] at hab
    exact (IsLocalization.map_units A b).mul_left_eq_zero.mp hab
  let _ : Algebra A K := f.toAlgebra
  let _ : Algebra A L := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hinj
  have : IsFractionRing A K := by
    refine IsFractionRing.of_field A K (fun z => ?_)
    obtain ⟨r, q, hz⟩ := (IntermediateField.mem_adjoin_simple_iff k (z : L)).mp z.2
    refine ⟨algebraMap k[X] A r, algebraMap k[X] A q, ?_⟩
    change z = f _ / f _
    rw [hf, hf]
    apply Subtype.ext
    rw [hz, ← hval, ← hval]
    rfl
  obtain ⟨n, φ, h⟩ := finVal_gen A K L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨p, hp, hpx⟩ := h x hx
  choose a b hb hab using hfrac
  refine ⟨p.natDegree, fun i => a (p.coeff i), fun i => b (p.coeff i), fun i => hb _, ?_⟩
  rw [hp.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at hpx
  rw [← hpx]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  congr 1
  change _ = ((f (p.coeff i) : K) : L)
  rw [hab, ← hval, ← hval]
  rfl

end LateralTheory.E.E4
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafFinInfPf
namespace LateralTheory.E.E4

open Polynomial

theorem finInf_comm {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (p : Polynomial k) :
    aeval (algebraMap B L (g X)) p = algebraMap B L (g p) := by
  have h : (aeval (algebraMap B L (g X)) : Polynomial k →ₐ[k] L) =
      (IsScalarTower.toAlgHom k B L).comp g := by
    apply Polynomial.algHom_ext
    simp
  rw [h]; rfl

theorem finInf_integral {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (hf : g.Finite)
    (K : IntermediateField k L) (hT : algebraMap B L (g X) ∈ K) (b : B) :
    IsIntegral K (algebraMap B L b) := by
  have hi : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hf
  obtain ⟨p, hp, hpb⟩ := hi b
  let φ : Polynomial k →ₐ[k] K := aeval (⟨_, hT⟩ : K)
  have hc : (algebraMap K L).comp φ.toRingHom = (algebraMap B L).comp g.toRingHom := by
    refine RingHom.ext fun q => ?_
    have h1 := finInf_comm (L := L) g q
    have h2 := Polynomial.aeval_algebraMap_apply L (⟨_, hT⟩ : K) q
    exact h2.symm.trans h1
  refine ⟨p.map φ.toRingHom, hp.map _, ?_⟩
  rw [eval₂_map, hc, ← Polynomial.hom_eval₂, hpb, map_zero]

theorem LeafFinInf_of : LeafFinInf := by
  intro k B _ _ _ _ _ hft g hg hf
  have hinj : Function.Injective (algebraMap B (FractionRing B)) := IsFractionRing.injective B _
  have htr : Transcendental k (algebraMap B (FractionRing B) (g X)) := by
    rw [transcendental_iff]
    intro p hp
    rw [finInf_comm] at hp
    apply hg
    apply hinj
    simpa using hp
  refine ⟨fun h => htr (IsAlgebraic.inv_iff.mp h), ?_⟩
  set K := IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g X))⁻¹} with hK
  have hT : algebraMap B (FractionRing B) (g X) ∈ K := by
    have : (algebraMap B (FractionRing B) (g X))⁻¹ ∈ K :=
      IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    simpa using K.inv_mem this
  obtain ⟨S, hS⟩ := hft.out
  let S' : Set (FractionRing B) := algebraMap B (FractionRing B) '' (S : Set B)
  have : Finite S' := (S.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S') :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact finInf_integral g hf K hT b)
  have hB : ∀ b : B, algebraMap B (FractionRing B) b ∈ IntermediateField.adjoin K S' := by
    intro b
    have hb : b ∈ Algebra.adjoin k (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K S' ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K (FractionRing B)]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin K S' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end LateralTheory.E.E4
end

open Polynomial IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.E.CurveUnitsOrderAtInfinity

theorem minpolyCoeff : LateralTheory.E.E4.LeafMinpolyCoeff := by
  intro k L _ _ _ s hs F hF x hx i
  subst hF
  have : UniqueFactorizationMonoid (Algebra.adjoin k {s}) := hs.uniqueFactorizationMonoid_adjoin
  have : IsIntegrallyClosed (Algebra.adjoin k {s}) := inferInstance
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (IntermediateField.adjoin k {s}) hx, coeff_map]
  exact ((minpoly (Algebra.adjoin k {s}) x).coeff i).2

theorem ordInfHom : LateralTheory.E.E4.LeafOrdInfHom :=
  LateralTheory.E.E4.LeafOrdInfHom_of_local (LateralTheory.E.E4.LeafOrdInfLocal_of' LateralTheory.E.E4.LeafFinInf_of LateralTheory.E.E4.LeafFinVal_of)

theorem LeafUnits_of : LateralTheory.E.E4.LeafUnits :=
  LateralTheory.E.E4.LeafUnits_of (LateralTheory.E.E4.LeafUnitsFG_of_dim LateralTheory.E.E4.LeafNoetherDim_of
    (LateralTheory.E.E4.LeafOrdAtInfinity_of_cut ordInfHom minpolyCoeff))

end LateralTheory.E.CurveUnitsOrderAtInfinity

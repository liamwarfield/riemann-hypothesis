module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReduction
open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_splits_of_separable_residue (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (V : ValuationSubring Ω) (q : Polynomial V) (hq : q.Monic)
    (hs : (q.map (IsLocalRing.residue V)).Separable) :
    ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  have hinj : Function.Injective (algebraMap V Ω) := IsFractionRing.injective V Ω

  have hdegree : ∀ g : Polynomial Ω, Irreducible g → g ∣ q.map (algebraMap V Ω) →
      g.degree = 1 := by
    intro g hg hgd
    obtain ⟨g₀, hg₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hq hgd
    have hg0 : g ≠ 0 := hg.ne_zero
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hmap : g₀.map (algebraMap V Ω) = g * C g.leadingCoeff⁻¹ := by
      set c := g.leadingCoeff with hc
      rw [← hg₀, mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
    have hmapm : (g₀.map (algebraMap V Ω)).Monic := by
      rw [hmap]; exact monic_mul_leadingCoeff_inv hg0
    have hg₀m : g₀.Monic := monic_of_injective hinj hmapm
    have hdvd : g₀ ∣ q := by
      rw [← map_dvd_map (algebraMap V Ω) hinj hg₀m, hmap]
      refine dvd_trans (Dvd.intro (C g.leadingCoeff) ?_) hgd
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
    have hsep₀ : (g₀.map (residue V)).Separable :=
      hs.of_dvd (Polynomial.map_dvd _ hdvd)
    have hdeg : (g₀.map (residue V)).natDegree = g.natDegree := by
      rw [hg₀m.natDegree_map, ← natDegree_map_eq_of_injective hinj, hmap,
        natDegree_mul_C (inv_ne_zero hlc)]
    have hgdeg : g.natDegree ≠ 0 := fun h =>
      hg.not_isUnit (isUnit_iff_degree_eq_zero.mpr ((degree_eq_iff_natDegree_eq hg0).mpr h))
    have hder₀ : derivative (g₀.map (residue V)) ≠ 0 := by
      intro h0
      have hu : IsUnit (g₀.map (residue V)) := by
        have := hsep₀
        rw [Polynomial.Separable, h0, isCoprime_zero_right] at this
        exact this
      exact hgdeg (hdeg ▸ natDegree_eq_zero_of_isUnit hu)
    have hder : derivative g ≠ 0 := by
      intro h0
      apply hder₀
      have h1 : derivative (g₀.map (algebraMap V Ω)) = 0 := by
        rw [hmap, derivative_mul, derivative_C, h0]; simp
      rw [derivative_map] at h1 ⊢
      have h2 : derivative g₀ = 0 := by
        apply Polynomial.map_injective _ hinj
        rw [h1, Polynomial.map_zero]
      rw [h2, Polynomial.map_zero]
    exact IsSepClosed.degree_eq_one_of_irreducible Ω hg
      ((separable_iff_derivative_ne_zero hg).mpr hder)
  have hQ : (q.map (algebraMap V Ω)).Splits := by
    by_cases hq0 : q.map (algebraMap V Ω) = 0
    · simp [hq0]
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hq0
    rw [← hu]
    refine (Splits.multisetProd fun f hf ↦ ?_).mul u.isUnit.splits
    let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
    exact Splits.of_degree_eq_one (hdegree f h
      (UniqueFactorizationMonoid.dvd_of_mem_factors hf))
  have hroots : ∀ a ∈ (q.map (algebraMap V Ω)).roots, a ∈ (algebraMap V Ω).range := by
    intro a ha
    have hne : q.map (algebraMap V Ω) ≠ 0 := (hq.map _).ne_zero
    have hr : aeval a q = 0 := by
      rw [mem_roots hne, IsRoot, eval_map_algebraMap] at ha
      exact ha
    have hint : IsIntegral V a := ⟨q, hq, by rwa [← aeval_def]⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).mp hint
    exact ⟨y, hy⟩
  have hqs : q.Splits := Splits.of_splits_map_of_injective hinj hQ hroots
  exact ⟨q.roots, hqs.eq_prod_roots_of_monic hq⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicSplitsValuationSubringOfSeparableReductionStatement
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) (q : Polynomial V), q.Monic → (q.map (IsLocalRing.residue V)).Separable → ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.monic_splits_of_separable_residue | exact GlobalTheory.monic_splits_of_separable_residue | (intros; apply GlobalTheory.monic_splits_of_separable_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaRes

def toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) : R →+* V :=
  ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V (fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this)

theorem coe_toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (r : R) :
    ((toV R K Ω V hV r : V) : Ω) = algebraMap K Ω (algebraMap R K r) := rfl

theorem isLocalHom_toV (R K Ω : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) :
    IsLocalHom (toV R K Ω V hV) := by
  constructor
  intro r hr
  obtain ⟨u, hu⟩ := hr
  have hx : algebraMap K Ω (algebraMap R K r) * ((u⁻¹ : Vˣ) : V) = 1 := by
    rw [← coe_toV R K Ω V hV r, ← hu]
    exact congrArg Subtype.val u.mul_inv
  have hx0 : algebraMap R K r ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hmem : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
    change algebraMap K Ω _ ∈ V
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hx]
    exact ((u⁻¹ : Vˣ) : V).2
  rw [hV] at hmem
  obtain ⟨s, hs⟩ := hmem
  have h1 : r * s = 1 := IsFractionRing.injective R K (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
  exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

def resMap (R K Ω : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) :
    ResidueField R →+* ResidueField V :=
  haveI := isLocalHom_toV R K Ω V hV
  ResidueField.map (toV R K Ω V hV)

open Polynomial

theorem residue_algebraic (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (V : ValuationSubring Ω)
    (hV : IsAbove R K V.toSubring) (a : ResidueField V) :
    ∃ p : Polynomial (ResidueField R), p ≠ 0 ∧ p.eval₂ (resMap R K Ω V hV) a = 0 := by
  haveI : IsLocalHom (toV R K Ω V hV) := isLocalHom_toV R K Ω V hV
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨w, rfl⟩ := residue_surjective a
  obtain ⟨p, hp0, hpw⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) ((w : V) : Ω)
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  let b : nonZeroDivisors R := ⟨b, hbmem⟩
  set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
  have hφinj : Function.Injective (toV R K Ω V hV) := fun x y h =>
    IsFractionRing.injective R K ((algebraMap K Ω).injective (by
      have := congrArg Subtype.val h
      rwa [coe_toV, coe_toV] at this))
  have hq0 : q ≠ 0 :=
    (IsLocalization.integerNormalization_eq_zero_iff le_rfl p).not.mpr hp0
  have hcomp : V.subtype.comp (toV R K Ω V hV) = (algebraMap K Ω).comp (algebraMap R K) :=
    RingHom.ext fun r => coe_toV R K Ω V hV r
  have hqw : Polynomial.eval₂ (toV R K Ω V hV) w q = 0 := by
    apply Subtype.ext
    change V.subtype _ = V.subtype 0
    rw [map_zero, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hb, Algebra.smul_def,
      Polynomial.eval₂_mul]
    have : Polynomial.eval₂ (algebraMap K Ω) (V.subtype w) p = 0 := hpw
    rw [this, mul_zero]
  set pp := q.primPart
  have hpp : Polynomial.eval₂ (toV R K Ω V hV) w pp = 0 := by
    have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
    have := hqw
    rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
    exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
  refine ⟨pp.map (residue R), ?_, ?_⟩
  · intro h0
    have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
      simpa [RingHom.mem_ker] using h0
    rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, Ideal.mem_span_singleton] at hmem
    exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
  · rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((ResidueField.map (toV R K Ω V hV)).comp (residue R)) _ _ = 0
    rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]

theorem eq_of_residue_eq {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (q : A[X])
    (hs : (q.map (residue A)).Separable) (b c : A) (hb : q.IsRoot b) (hc : q.IsRoot c)
    (h : residue A b = residue A c) : b = c := by
  by_contra hne
  obtain ⟨q1, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hb
  have hc1 : q1.IsRoot c := by
    have := hc
    rw [IsRoot, eval_mul, eval_sub, eval_X, eval_C] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨q2, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hc1
  rw [← _root_.mul_assoc, Polynomial.map_mul, Polynomial.map_mul] at hs
  have h2 := hs.of_mul_left
  simp only [Polynomial.map_sub, map_X, map_C, h] at h2
  exact not_isUnit_X_sub_C _ (isCoprime_self.1 h2.isCoprime)

theorem residueField_inertiaFixed_isAlgClosed : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsAlgClosed (IsLocalRing.ResidueField (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω))) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  haveI : IsLocalHom (toV R K Ω V hV) := isLocalHom_toV R K Ω V hV
  letI : Algebra (ResidueField R) (ResidueField V) := (resMap R K Ω V hV).toAlgebra
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField V) := ⟨fun a => by
    obtain ⟨p, hp, h⟩ := residue_algebraic R K Ω V hV a
    exact ⟨p, hp, h⟩⟩
  haveI : PerfectField (ResidueField V) := Algebra.IsAlgebraic.perfectField (ResidueField R)

  have hred : ∀ s : Multiset V, ((s.map fun b => X - C b).prod).map (residue V) =
      ((s.map (residue V)).map fun a => X - C a).prod := by
    intro s
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp

  haveI : IsSepClosed (ResidueField V) := IsSepClosed.of_exists_root _ fun p hm hirr hsep => by
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective _ residue_surjective p)) hm
    obtain ⟨s, hs⟩ := GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction Ω V q hqm (by rw [hq]; exact hsep)
    rw [← hq, hs, hred] at hirr ⊢
    obtain ⟨b, hb⟩ : ∃ b, b ∈ s := by
      by_contra h0
      push_neg at h0
      rw [Multiset.eq_zero_of_forall_notMem h0] at hirr
      simp at hirr
    refine ⟨residue V b, ?_⟩
    have hr := Polynomial.roots_multiset_prod_X_sub_C (s.map (residue V))
    have hmem : residue V b ∈ ((s.map (residue V)).map fun a => X - C a).prod.roots := by
      rw [hr]; exact Multiset.mem_map_of_mem _ hb
    exact (Polynomial.mem_roots'.1 hmem).2
  haveI : IsAlgClosed (ResidueField V) := inferInstance

  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  let jV : V' →+* V := ((algebraMap K' Ω).comp V'.subtype).codRestrict V (fun x => x.2)
  haveI : IsLocalHom jV := by
    constructor
    intro x hx
    obtain ⟨u, hu⟩ := hx
    have hx1 : ((x : K') : Ω) * ((u⁻¹ : Vˣ) : V) = 1 := by
      have : ((jV x : V) : Ω) = ((x : K') : Ω) := rfl
      rw [← this, ← hu]
      exact congrArg Subtype.val u.mul_inv
    have hx0 : (x : K') ≠ 0 := by
      intro h0; rw [h0] at hx1; simp at hx1
    have hmem : (x : K')⁻¹ ∈ V' := by
      change ((((x : K')⁻¹ : K')) : Ω) ∈ V
      rw [IntermediateField.coe_inv, inv_eq_of_mul_eq_one_right hx1]
      exact ((u⁻¹ : Vˣ) : V).2
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    exact mul_inv_cancel₀ hx0
  haveI : Algebra.IsSeparable (ResidueField R) (ResidueField V) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hsurj : Function.Surjective (ResidueField.map jV) := by
    intro a
    have hsep : (minpoly (ResidueField R) a).Separable := Algebra.IsSeparable.isSeparable _ a
    have hmon : (minpoly (ResidueField R) a).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ residue_surjective _)) hmon
    set gV := g.map (toV R K Ω V hV) with hgV
    have hgV' : gV.map (residue V) = (minpoly (ResidueField R) a).map (resMap R K Ω V hV) := by
      rw [hgV, Polynomial.map_map, ← ResidueField.map_comp_residue, ← Polynomial.map_map, hg]
      rfl
    have hsepV : (gV.map (residue V)).Separable := by rw [hgV']; exact hsep.map
    obtain ⟨s, hs⟩ := GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction Ω V gV (hgm.map _) hsepV
    have hroot : a ∈ (gV.map (residue V)).roots := by
      rw [Polynomial.mem_roots ((hgm.map _).map _).ne_zero, hgV', IsRoot, Polynomial.eval_map]
      exact minpoly.aeval _ a
    rw [hs, hred, Polynomial.roots_multiset_prod_X_sub_C] at hroot
    obtain ⟨b, hbs, rfl⟩ := Multiset.mem_map.1 hroot
    have hbroot : gV.IsRoot b := by
      have : b ∈ gV.roots := by rw [hs, Polynomial.roots_multiset_prod_X_sub_C]; exact hbs
      exact (Polynomial.mem_roots'.1 this).2
    have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
      intro σ hσ
      obtain ⟨-, h2⟩ := (mem_inertia_iff V σ).1 hσ
      have hlt := h2 b b.2
      have hd : σ (b : Ω) - b ∈ V := (V.valuation_le_one_iff _).1 hlt.le
      have hmem : σ (b : Ω) ∈ V := by simpa using add_mem hd b.2
      set c : V := ⟨σ b, hmem⟩ with hc
      have hres : residue V c = residue V b := by
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        exact hlt
      have hcroot : gV.IsRoot c := by
        have key : ∀ y : V, ((gV.eval y : V) : Ω) = g.eval₂ ((algebraMap K Ω).comp (algebraMap R K)) (y : Ω) := by
          intro y
          rw [hgV, Polynomial.eval_map]
          change V.subtype _ = _
          rw [Polynomial.hom_eval₂]
          rfl
        have hb0 := key b
        rw [hbroot.eq_zero] at hb0
        have hcomm : (σ : Ω →+* Ω).comp ((algebraMap K Ω).comp (algebraMap R K)) =
            (algebraMap K Ω).comp (algebraMap R K) := by
          ext r; simp
        apply Subtype.ext
        rw [key c, show ((c : V) : Ω) = (σ : Ω →+* Ω) b from rfl, ← hcomm, ← Polynomial.hom_eval₂, ← hb0]
        simp
      have := eq_of_residue_eq gV hsepV c b hcroot hbroot hres
      exact congrArg Subtype.val this
    have hbK : (b : Ω) ∈ K' := by
      rw [hK', IntermediateField.mem_fixedField_iff]
      exact hfix
    have hbV' : (⟨b, hbK⟩ : K') ∈ V' := b.2
    refine ⟨residue V' ⟨⟨b, hbK⟩, hbV'⟩, ?_⟩
    rw [ResidueField.map_residue]
    rfl
  let e := RingEquiv.ofBijective (ResidueField.map jV) ⟨(ResidueField.map jV).injective, hsurj⟩
  exact IsAlgClosed.of_ringEquiv _ _ e.symm

end GlobalTheory.InertiaRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsAlgClosed (IsLocalRing.ResidueField (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω))) := by
  first | exact @GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed | exact GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed | (intros; apply GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertia
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

theorem isUnit_of_sub_mem_maximalIdeal' {A : Type*} [CommRing A] [IsLocalRing A] {x y : A}
    (h : x - y ∈ maximalIdeal A) (hy : IsUnit y) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have hy' : y ∈ maximalIdeal A := by
    have := Ideal.sub_mem _ hx' h
    simpa using this
  exact (mem_maximalIdeal y).1 hy' hy

theorem eq_of_isRoot_of_sub_mem_maximalIdeal {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {f : A[X]} {a₀ b b' : A} (hu : IsUnit (f.derivative.eval a₀)) (hb : f.IsRoot b) (hb' : f.IsRoot b')
    (h1 : b - a₀ ∈ maximalIdeal A) (h2 : b' - a₀ ∈ maximalIdeal A) : b' = b := by
  set h := f /ₘ (X - C b) with hh
  have hf : f = (X - C b) * h := (mul_divByMonic_eq_iff_isRoot.2 hb).symm
  have hd : f.derivative.eval b = h.eval b := by
    rw [hf]
    simp [derivative_mul]
  have hub : IsUnit (h.eval b) := by
    rw [← hd]
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hu
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b a₀ f.derivative
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  have hub' : IsUnit (h.eval b') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hub
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b' b h
    rw [hc]
    apply Ideal.mul_mem_right
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  have e : (b' - b) * h.eval b' = 0 := by
    have := hb'
    rw [IsRoot, hf] at this
    simpa using this
  rcases mul_eq_zero.1 e with e | e
  · exact sub_eq_zero.1 e
  · exact absurd e hub'.ne_zero

end GlobalTheory

namespace GlobalTheory

theorem henselianLocalRing_of_isSepClosed {Ω : Type} [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing V := by
  classical
  obtain ⟨W, rfl⟩ := exists_valuationSubring_comap_eq V (algebraMap Ω (AlgebraicClosure Ω))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  set ψ := comapToValuationSubring W (algebraMap Ω (AlgebraicClosure Ω))
  set ιW := algebraMap W (AlgebraicClosure Ω)
  set G := f.map ψ with hG
  set F := G.map ιW with hF
  have hFm : F.Monic := (hf.map ψ).map ιW
  have hint : ∀ r ∈ F.roots, ∃ r' : W, ιW r' = r := by
    intro r hr
    have hi : IsIntegral W r := ⟨G, hf.map ψ, by
      rw [← Polynomial.eval_map]
      exact (mem_roots hFm.ne_zero).1 hr⟩
    exact IsIntegrallyClosed.isIntegral_iff.1 hi
  have hψm : ψ (f.eval a₀) ∈ maximalIdeal W :=
    (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map ψ _ hu)

  obtain ⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, W.valuation (ιW (ψ a₀) - r) < 1 := by
    by_contra hne
    push_neg at hne
    have hprod : F.eval (ιW (ψ a₀)) = (F.roots.map fun r => ιW (ψ a₀) - r).prod := by
      conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
        IsAlgClosed.card_roots_eq_natDegree]
      rw [eval_multiset_prod, Multiset.map_map]
      simp
    have h1 : W.valuation (F.eval (ιW (ψ a₀))) = 1 := by
      rw [hprod, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have hle := hne y hy
      obtain ⟨y', rfl⟩ := hint y hy
      refine le_antisymm ?_ hle
      simp only [Function.comp_apply]
      rw [← map_sub]
      exact W.valuation_le_one (ψ a₀ - y')
    have h2 : W.valuation (F.eval (ιW (ψ a₀))) < 1 := by
      rw [hF, Polynomial.eval_map, eval₂_at_apply, hG, Polynomial.eval_map, eval₂_at_apply]
      exact (W.valuation_lt_one_iff _).1 hψm
    exact absurd h1 h2.ne
  obtain ⟨r', rfl⟩ := hint r hr
  have hr'm : r' - ψ a₀ ∈ maximalIdeal W := by
    rw [← neg_sub, Ideal.neg_mem_iff, W.valuation_lt_one_iff]
    simpa [ιW] using hrv
  have hGd : IsUnit (G.derivative.eval r') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ (y := G.derivative.eval (ψ a₀)) ?_
    · obtain ⟨c, hc⟩ := sub_dvd_eval_sub r' (ψ a₀) G.derivative
      rw [hc]
      exact Ideal.mul_mem_right _ _ hr'm
    · rw [hG, derivative_map, Polynomial.eval_map, eval₂_at_apply]
      exact h₂.map ψ
  have hFd : F.derivative.eval (ιW r') ≠ 0 := by
    rw [hF, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact fun e => hGd.ne_zero ((injective_iff_map_eq_zero ιW).1 (FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)) _ e)
  have hιinj : Function.Injective ιW := FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)
  have hψinj : Function.Injective ψ := fun x y e =>
    Subtype.ext ((algebraMap Ω (AlgebraicClosure Ω)).injective (congrArg Subtype.val e))

  set F₀ : Polynomial Ω := f.map (W.comap (algebraMap Ω (AlgebraicClosure Ω))).subtype with hF₀
  have hF₀F : F₀.map (algebraMap Ω (AlgebraicClosure Ω)) = F := by
    rw [hF₀, hF, hG, Polynomial.map_map, Polynomial.map_map]
    rfl
  have hintΩ : IsIntegral Ω (ιW r') := Algebra.IsIntegral.isIntegral _
  have hroot0 : aeval (ιW r') F₀ = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, hF₀F]
    exact (mem_roots hFm.ne_zero).1 hr
  obtain ⟨h, hh⟩ := minpoly.dvd Ω (ιW r') hroot0
  have hq : aeval (ιW r') (derivative (minpoly Ω (ιW r'))) ≠ 0 := by
    intro e
    apply hFd
    have : aeval (ιW r') (derivative F₀) = 0 := by
      rw [hh, derivative_mul, map_add (f := _), map_mul, map_mul, e, minpoly.aeval]
      ring
    rw [aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map, hF₀F] at this
    exact this
  have hsep : (minpoly Ω (ιW r')).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hintΩ)).2 (fun e => hq (by rw [e, map_zero]))
  have hdeg := IsSepClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hintΩ) hsep
  obtain ⟨b, hb⟩ := minpoly.natDegree_eq_one_iff.1 (natDegree_eq_of_degree_eq_some hdeg)
  have hbW : b ∈ W.comap (algebraMap Ω (AlgebraicClosure Ω)) := by
    rw [ValuationSubring.mem_comap, hb]
    exact r'.2
  have hψb : ψ ⟨b, hbW⟩ = r' := Subtype.ext hb
  have hGr : G.eval r' = 0 := by
    apply hιinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← hF]
    exact (mem_roots hFm.ne_zero).1 hr
  refine ⟨⟨b, hbW⟩, ?_, ?_⟩
  · apply hψinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hψb, ← hG]
    exact hGr
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hr'm ?_
    have := hu.map ψ
    rwa [map_sub, hψb] at this

end GlobalTheory

namespace GlobalTheory

theorem henselianLocalRing_comap_fixedField_inertia (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  classical
  haveI := henselianLocalRing_of_isSepClosed V
  set K' := IntermediateField.fixedField (inertia K V)
  set j := comapToValuationSubring V (algebraMap K' Ω)
  have hjinj : Function.Injective j := fun x y e =>
    Subtype.ext ((algebraMap K' Ω).injective (congrArg (fun z : V => (z : Ω)) e))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  have h₁' : (f.map j).eval (j a₀) ∈ maximalIdeal V := by
    rw [Polynomial.eval_map, eval₂_at_apply]
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map j _ hu)
  have h₂' : IsUnit ((f.map j).derivative.eval (j a₀)) := by
    rw [derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact h₂.map j
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian (f.map j) (hf.map j) (j a₀) h₁' h₂'

  set κ : V.comap (algebraMap K' Ω) →+* Ω := V.subtype.comp j with hκ
  have hbΩ : f.eval₂ κ (b : Ω) = 0 := by
    have : V.subtype ((f.map j).eval b) = 0 := by rw [hb.eq_zero, map_zero]
    rw [Polynomial.eval_map, hom_eval₂] at this
    exact this
  have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
    intro σ hσ
    obtain ⟨hσV, hσv⟩ := (mem_inertia_iff V σ).1 hσ
    have hmem : σ (b : Ω) ∈ V := by
      have := ValuationSubring.smul_mem_pointwise_smul σ (b : Ω) V b.2
      rwa [hσV] at this
    have hσκ : (σ : Ω →+* Ω).comp κ = κ := by
      ext x
      exact (IntermediateField.mem_fixedField_iff _ _).1 (x : K').2 σ hσ
    have hc : (f.map j).IsRoot ⟨σ b, hmem⟩ := by
      apply V.subtype_injective
      rw [map_zero, Polynomial.eval_map, hom_eval₂]
      have e := congrArg (σ : Ω →+* Ω) hbΩ
      rw [map_zero, hom_eval₂, hσκ] at e
      exact e
    have hcm : (⟨σ b, hmem⟩ : V) - j a₀ ∈ maximalIdeal V := by
      have hd : (⟨σ b, hmem⟩ : V) - b ∈ maximalIdeal V := by
        rw [V.valuation_lt_one_iff]
        exact hσv b b.2
      have := Ideal.add_mem _ hd hba
      simpa using this
    have := eq_of_isRoot_of_sub_mem_maximalIdeal h₂' hb hc hba hcm
    exact congrArg Subtype.val this
  have hbK : (b : Ω) ∈ K' := (IntermediateField.mem_fixedField_iff _ _).2 hfix
  have hbV : (⟨b, hbK⟩ : K') ∈ V.comap (algebraMap K' Ω) := b.2
  have hjb : j ⟨⟨b, hbK⟩, hbV⟩ = b := Subtype.ext rfl
  refine ⟨⟨⟨b, hbK⟩, hbV⟩, ?_, ?_⟩
  · apply hjinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hjb]
    exact hb
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hba ?_
    have := hu.map j
    rwa [map_sub, hjb] at this

theorem henselianLocalRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact henselianLocalRing_comap_fixedField_inertia K V

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertiaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  first | exact @GlobalTheory.henselianLocalRing_fixedField_inertia | exact GlobalTheory.henselianLocalRing_fixedField_inertia | (intros; apply GlobalTheory.henselianLocalRing_fixedField_inertia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaFixedSH

theorem vs_inv_mem_of_not_mem_nonunits {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ∈ A)
    (hn : x ∉ A.nonunits) : x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
  have h1 : A.valuation x = 1 := le_antisymm ((A.valuation_le_one_iff x).2 hx) hn
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem inertiaFixed_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have hc : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this
  have hinv : ∀ π : R, Irreducible π → (algebraMap K Ω (algebraMap R K π))⁻¹ ∉ V := by
    intro π hπ h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω _ ∈ V
      rwa [map_inv₀]
    rw [hV] at h'
    obtain ⟨s, hs⟩ := h'
    have hπ0 : algebraMap R K π ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨s, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hs, map_one, mul_inv_cancel₀ hπ0]
  have hc0 : ∀ π : R, Irreducible π → algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    intro π hπ h
    apply hinv π hπ
    rw [h, inv_zero]; exact V.zero_mem
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  have memV' : ∀ y : K', y ∈ V' ↔ (y : Ω) ∈ V := fun y => ValuationSubring.mem_comap
  let f : R →+* V' := ((algebraMap K K').comp (algebraMap R K)).codRestrict V' (fun r => by
      rw [memV']; simpa using hc r)
  have hf : ∀ r : R, ((f r : K') : Ω) = algebraMap K Ω (algebraMap R K r) := fun r => by simp [f]
  have unitV' : ∀ a : V', ((a : K') : Ω) ∉ V.nonunits → IsUnit a := by
    intro a ha
    obtain ⟨h0, hi⟩ := vs_inv_mem_of_not_mem_nonunits V ((memV' a).1 a.2) ha
    have hmem : (a : K')⁻¹ ∈ V' := by rw [memV']; simpa using hi
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv, OneMemClass.coe_one,
      IntermediateField.coe_one]
    exact mul_inv_cancel₀ h0
  have hfπ : ∀ π : R, Irreducible π → Irreducible (f π) := by
    intro π hπ
    refine irreducible_iff.2 ⟨fun hu => hinv π hπ ?_, fun a b hab => ?_⟩
    · obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hb' : ((f π : K') : Ω) * ((b : K') : Ω) = 1 := by
        have := congrArg (fun z : V' => ((z : K') : Ω)) hb
        simpa using this
      rw [hf] at hb'
      rw [inv_eq_of_mul_eq_one_right hb']
      exact (memV' b).1 b.2
    · by_contra hne
      push_neg at hne
      have ha : ((a : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.1 (unitV' a h)
      have hb : ((b : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.2 (unitV' b h)
      have h1 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (a : K').2 ha
      have h2 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (b : K').2 hb
      have hab' : algebraMap K Ω (algebraMap R K π) = ((a : K') : Ω) * ((b : K') : Ω) := by
        rw [← hf, hab]; simp
      apply hinv π hπ
      have h0 := hc0 π hπ
      convert mul_mem h1 h2 using 1
      rw [div_mul_div_comm, ← hab']
      field_simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdvr : IsDiscreteValuationRing V' := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f π, hfπ π hπ, fun {x} hx => ?_⟩
    have hx0 : ((x : K') : Ω) ≠ 0 := by
      intro h; apply hx; apply Subtype.ext; apply Subtype.ext; simpa using h
    classical
    have hex := GlobalTheory.T.not_mem_div_uniformizer_pow_alt R K Ω V hV π hπ _ hx0
    have hn := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h; rw [h] at hn; apply hn; simpa using (memV' x).1 x.2
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m ∈ V := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      simpa using this
    set y : K' := (x : K') / (algebraMap K K' (algebraMap R K π)) ^ m with hy
    have hyΩ : (y : Ω) = ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m := by simp [y]
    have hyV' : y ∈ V' := by rw [memV', hyΩ]; exact hmin
    have hyU : (y : Ω) ∉ V.nonunits := by
      intro hyn
      have := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ y.2 hyn
      apply hn
      rw [hm, hyΩ] at *
      convert this using 1
      rw [pow_succ, div_div]
    refine ⟨m, (unitV' ⟨y, hyV'⟩ hyU).unit, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp only [IsUnit.unit_spec, MulMemClass.coe_mul, IntermediateField.coe_mul, SubmonoidClass.coe_pow,
      IntermediateField.coe_pow]
    rw [hf, hyΩ]
    field_simp [pow_ne_zero m (hc0 π hπ)]
  exact ⟨⟨hdvr, GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt R K Ω V hV, GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt R K Ω V hV, inferInstance⟩, f, hf, hfπ⟩

end GlobalTheory.InertiaFixedSH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaFixedField_valuationRing_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  first | exact @GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian | exact GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian | (intros; apply GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrderCentralizerStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory

theorem rootOfUnity_eq_one_of_map_eq_one {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (w : R) (hw : w ^ n = 1)
    (hφ : φ w = 1) : w = 1 := by
  have hx : w - 1 ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have := h.map φ
    rw [map_sub, hφ, map_one, sub_self] at this
    exact not_isUnit_zero this
  have hres : IsLocalRing.residue R w = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hS : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn
    simpa using this
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by
    rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 h0)

theorem units_rootOfUnity_map_injective {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (u v : Rˣ) (hu : u ^ n = 1)
    (hv : v ^ n = 1) (huv : Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v) : u = v := by
  have hφ : φ (u : R) = φ (v : R) := by
    have := congrArg (fun x : Kˣ => (x : K)) huv
    simpa using this
  have hw : ((u * v⁻¹ : Rˣ) : R) = 1 := by
    apply rootOfUnity_eq_one_of_map_eq_one φ n hn
    · rw [← Units.val_pow_eq_pow_val, mul_pow, hu, inv_pow, hv, inv_one, _root_.mul_one, Units.val_one]
    · rw [Units.val_mul, map_mul, hφ, ← map_mul, Units.mul_inv, map_one]
  exact mul_inv_eq_one.1 (Units.ext hw)

theorem exists_rootOfUnity_lift {R : Type} [CommRing R] [HenselianLocalRing R] (n : ℕ)
    (hn0 : 0 < n) (hn : IsUnit (n : R)) (z : IsLocalRing.ResidueField R) (hz : z ^ n = 1) :
    ∃ a : R, a ^ n = 1 ∧ IsLocalRing.residue R a = z := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective z
  have hm : (Polynomial.X ^ n - 1 : Polynomial R).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hn0.ne'
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨a, ha, hd⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ n - 1) hm a₀ (by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp [hz]) (by
      simp [Polynomial.derivative_X_pow]
      exact ⟨hn, ha₀.pow _⟩)
  refine ⟨a, ?_, ?_⟩
  · simpa [sub_eq_zero] using ha
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hd

end GlobalTheory

namespace GlobalTheory

theorem rootsOfUnity_map_bijective_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type) [Field K] (φ : R →+* K) (n : ℕ), 0 < n →
    IsUnit (n : R) →
    (∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v → u = v) ∧
    ∀ z : Kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ Units.map φ.toMonoidHom u = z := by
  intro R _ _ _ K _ φ n hn0 hn
  refine ⟨fun u v hu hv huv => units_rootOfUnity_map_injective φ n hn u v hu hv huv, ?_⟩
  haveI : NeZero n := ⟨hn0.ne'⟩
  set ρ := IsLocalRing.residue R
  haveI : NeZero (n : IsLocalRing.ResidueField R) :=
    ⟨by simpa [ρ] using (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn⟩
  let f := restrictRootsOfUnity φ n
  let g := restrictRootsOfUnity ρ n
  have hf : ∀ x : rootsOfUnity n R, ((f x : Kˣ) : K) = φ ((x : Rˣ) : R) := fun x => by
    simp [f]
  have hg : ∀ x : rootsOfUnity n R, ((g x : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) = ρ ((x : Rˣ) : R) :=
    fun x => by simp [g]
  have ginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective ρ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n (IsLocalRing.ResidueField R) => ((w : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) hxy
    simpa [hg] using this
  have gsurj : Function.Surjective g := by
    intro ζ
    obtain ⟨a, ha, hρ⟩ := exists_rootOfUnity_lift n hn0 hn ((ζ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ζ.2, Units.val_one])
    refine ⟨⟨Units.ofPowEqOne a n ha hn0.ne', (mem_rootsOfUnity _ _).2 (Units.ext (by simp [ha]))⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hg]
    simpa using hρ
  have hcardR : Nat.card (rootsOfUnity n R) = n := by
    rw [Nat.card_eq_of_bijective g ⟨ginj, gsurj⟩, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  have finj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective φ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hxy
    simpa [hf] using this
  have fbij : Function.Bijective f :=
    finj.bijective_of_nat_card_le (by rw [hcardR]; exact card_rootsOfUnity K n)
  intro z hz
  obtain ⟨x, hx⟩ := fbij.2 ⟨z, (mem_rootsOfUnity _ _).2 hz⟩
  refine ⟨x, (mem_rootsOfUnity _ _).1 x.2, ?_⟩
  apply Units.ext
  have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hx
  simpa [hf] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem level_smul_levQ (q : LevQ Dw l) : l.M • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (level_mem l).1 trivial

theorem cSep_smul_levQ (q : LevQ Dw l) : cSep l • q = q := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have e : cSep l • y - y = (cSep l - 1) • y := by rw [sub_smul, one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (cSep_spec l).2 trivial

theorem sub_sepRep (q : LevQ Dw l) (x : Dw.La) (hx : x ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (hq : Submodule.Quotient.mk x = q) : ∃ z : Dw.La, x - cSep l • levRep q = l.M • z := by
  have h1 : x - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
    (Submodule.Quotient.eq _).1 (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)).symm)
  obtain ⟨b1, hb1⟩ := modN_smul l ((mul_comm _ _).trans l.prod) (cSep_spec l).1 h1
  obtain ⟨b2, hb2⟩ := modN_smul l l.prod (cSep_spec l).2 hx
  refine ⟨b1 - b2, ?_⟩
  rw [smul_sub, ← hb1, ← hb2, smul_sub, sub_smul, one_smul]
  abel

end GlobalTheory.DilateLevel

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

theorem dilate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  intro E _ _ _ H Dw l r n L mk m hm
  refine hm.elim fun α hβ => hβ.elim fun β hab => ?_
  have hM0 : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hsm : ∀ a, (m • mk) a = m • mk a := fun a => LinearMap.smul_apply _ _ _
  have hbez : ∀ x : Fin r → E, x = α • (m • x) + β • (l.M • x) := fun x => by
    rw [smul_smul, ← natCast_zsmul, smul_smul, ← add_smul, hab, one_smul]
  refine ⟨fun h => ?_, fun N Y => ⟨fun hmem h => ?_, fun g X bas w Λ v c => ?_⟩⟩
  · refine ⟨fun a => by rw [hsm]; exact zsmul_mem (h.mem a) m, fun a ha hu => ?_, fun v hv => ?_⟩
    · refine hu.elim fun u hu' => h.inj a ha ⟨α • u + β • mk a, add_mem (zsmul_mem hu'.1 α) (zsmul_mem (h.mem a) β), ?_⟩
      have e : m • mk a = l.M • u := (hsm a).symm.trans hu'.2
      refine (hbez (mk a)).trans ?_
      rw [e, smul_add, smul_comm α, smul_comm β]
    · have hvL : v ∈ L := Submodule.smul_le_right hv
      refine (h.surj (α • v) (zsmul_mem hv α)).elim fun a1 h1 => h1.elim fun ha1 h2 => h2.elim fun u1 h3 => ?_
      refine ⟨a1, ha1, m • u1 + β • v, add_mem (zsmul_mem h3.1 m) (zsmul_mem hvL β), ?_⟩
      have e : α • v = mk a1 + l.M • u1 := h3.2
      refine (hbez v).trans ?_
      rw [smul_comm α m, e, hsm, smul_add, smul_add, smul_comm m, smul_comm β]
      abel
  · intro q b
    have h0 := h (m • q) b
    refine ⟨?_, h0.2⟩
    refine h0.1.elim fun a0 k => k.elim fun ha0 k2 => ?_
    have hq0 : Submodule.Quotient.mk a0 = m • q b := k2.1
    have hY0 := k2.2
    set a' : Dw.La := cSep l • levRep (q b) with ha'
    have ha'm : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul (cSep_spec l).1 trivial
    have hcls : (Submodule.Quotient.mk a' : LevQ Dw l) = q b := by
      have hr : (Submodule.Quotient.mk (levRep (q b)) : LevQ Dw l) = q b :=
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))
      rw [ha', Submodule.Quotient.mk_smul, hr, cSep_smul_levQ]
    refine ⟨a', ha'm, hcls, ?_⟩
    have hm' : (Submodule.Quotient.mk (m • a') : LevQ Dw l) = m • q b := by
      rw [Submodule.Quotient.mk_smul, hcls]
    refine (sub_sepRep (m • q b) a0 ha0 hq0).elim fun z1 hz1 => ?_
    refine (sub_sepRep (m • q b) (m • a') (zsmul_mem ha'm m) hm').elim fun z2 hz2 => ?_
    have hd : a0 - m • a' = l.M • (z1 - z2) := by
      rw [smul_sub, ← hz1, ← hz2]; abel
    have key : ((l.M : E)⁻¹) • (mk a0 - (m • mk) a') = mk (z1 - z2) := by
      rw [hsm, ← map_zsmul mk, ← map_sub, hd, map_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
    have := add_mem hY0 (hmem (z1 - z2))
    rw [← key] at this
    convert this using 1
    rw [smul_sub]
    abel
  · have hk : ∀ q : Fin n → LevQ Dw l, ((l.M : ℤ)) • q = 0 := fun q => funext fun b => by
      rw [Pi.smul_apply, natCast_zsmul, level_smul_levQ]; rfl
    have hinv : ∀ q : Fin n → LevQ Dw l, α • m • q = q := fun q => by
      rw [smul_smul, show α * m = 1 - β * l.M by linear_combination hab, sub_smul, one_smul, mul_smul, hk,
        smul_zero, sub_zero]
    let e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l) :=
      { toFun := fun q => m • q
        invFun := fun q => α • q
        left_inv := fun q => hinv q
        right_inv := fun q => by
          change m • α • q = q
          rw [smul_comm]; exact hinv q }
    exact finsum_comp_equiv e (f := fun q => c q • heisG X bas (Y q) (projA X bas w (tens Λ L) v))

end GlobalTheory.DilateLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_roots_dilation_coprime_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  first | exact @GlobalTheory.DilateLevel.dilate | exact GlobalTheory.DilateLevel.dilate | (intros; apply GlobalTheory.DilateLevel.dilate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SchRing

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem subsingleton_primeSpectrum_trivSqZeroExt (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    Subsingleton (PrimeSpectrum (TrivSqZeroExt k M)) := by
  have key : ∀ (P : PrimeSpectrum (TrivSqZeroExt k M)) (a : TrivSqZeroExt k M), a ∈ P.asIdeal ↔ a.fst = 0 := by
    intro P a
    constructor
    · intro ha
      by_contra h
      have hu : IsUnit a := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    · intro h
      have ha : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      apply P.isPrime.mem_of_pow_mem 2
      rw [ha, pow_two, TrivSqZeroExt.inr_mul_inr]
      exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun a => (key P a).trans (key Q a).symm)⟩

theorem range_subset_of_fst {X : Scheme.{0}} (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
    (x : Sp k ⟶ X) (u : Sp (TrivSqZeroExt k M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom k k M).toRingHom ≫ u = x) : Set.range u.base ⊆ Set.range x.base := by
  rintro _ ⟨y, rfl⟩
  haveI := subsingleton_primeSpectrum_trivSqZeroExt k M
  let z : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨z, ?_⟩
  have hy : (spMap (TrivSqZeroExt.fstHom k k M).toRingHom).base z = y := Subsingleton.elim (α := PrimeSpectrum (TrivSqZeroExt k M)) _ _
  rw [← h, ← hy]
  rfl

theorem exists_ringHom_of_range {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (D : Type) [CommRing D]
    (g : Sp D ⟶ X) (hg : Set.range g.base ⊆ (V : Set X)) : ∃ r : Γ(X, V) →+* D, g = spMap r ≫ hV.fromSpec := by
  have h' : Set.range g ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hg
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom, ?_⟩
  have e1 : spMap (Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom = IsOpenImmersion.lift hV.fromSpec g h' := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [e1, IsOpenImmersion.lift_fac]

theorem spMap_cancel {R D : Type} [CommRing R] [CommRing D] {Y : Scheme.{0}} (G : Sp R ⟶ Y) [Mono G]
    {a b : R →+* D} (h : spMap a ≫ G = spMap b ≫ G) : a = b :=
  spMap_inj (cancel_mono G |>.mp h)

end GlobalTheory.SchRing

namespace GlobalTheory.SchRing

theorem deformation_on_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  intro B _ X s U V hU hV e d k _ x hx hyp
  obtain ⟨u, hux, hus, huniq⟩ := hyp
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range hV k x hx
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_range hV _ u ((range_subset_of_fst k _ x u hux).trans hx)
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hs : ∀ (D : Type) [CommRing D] (r : Γ(X, V) →+* D),
      spMap r ≫ hV.fromSpec ≫ s = spMap (r.comp (s.appLE U V e).hom) ≫ hU.fromSpec := by
    intro D _ r
    rw [← key, spMap_comp']
    rfl
  have hbase : ∀ (D : Type) [CommRing D] (alg : k →+* D) (r : Γ(X, V) →+* D),
      (spMap r ≫ hV.fromSpec) ≫ s = spMap alg ≫ x ≫ s ↔
        r.comp (s.appLE U V e).hom = alg.comp (φ.comp (s.appLE U V e).hom) := by
    intro D _ alg r
    rw [hφ]
    simp only [Category.assoc]
    rw [hs, ← Category.assoc (spMap alg) (spMap φ), ← spMap_comp', hs]
    constructor
    · intro h; exact spMap_inj ((cancel_mono hU.fromSpec).mp h)
    · intro h; rw [h]
  have hfst : ∀ (D : Type) [CommRing D] (f : D →+* k) (r : Γ(X, V) →+* D),
      spMap f ≫ spMap r ≫ hV.fromSpec = x ↔ f.comp r = φ := by
    intro D _ f r
    rw [hφ, ← Category.assoc, ← spMap_comp']
    constructor
    · intro h; exact spMap_cancel hV.fromSpec h
    · intro h; rw [h]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [hψ] at hux; exact (hfst _ _ _).mp hux
  · rw [hψ] at hus; exact (hbase _ _ _).mp hus
  · intro v hv1 hv2
    have h1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (spMap v ≫ hV.fromSpec) = x := (hfst _ _ _).mpr hv1
    have h2 := (hbase _ _ _).mpr hv2
    obtain ⟨c, hc, hcu⟩ := huniq _ h1 h2
    refine ⟨c, ?_, ?_⟩
    · rw [hψ, ← Category.assoc, ← spMap_comp'] at hc
      exact spMap_cancel hV.fromSpec hc
    · intro c' hc'
      apply hcu
      rw [hψ, ← Category.assoc, ← spMap_comp', ← hc']

end GlobalTheory.SchRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  first | exact @GlobalTheory.SchRing.deformation_on_sections | exact GlobalTheory.SchRing.deformation_on_sections | (intros; apply GlobalTheory.SchRing.deformation_on_sections <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefAtOfPosDef
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CoefModel

section BaseChange

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (lam : ι → DomWeight n)

theorem fockS_map_int {s : Type} (P : MvPolynomial s ℤ) (g : MvPolynomial s K) :
    fockS (map φ (map (Int.castRingHom K) P)) (map φ g) = φ (fockS (map (Int.castRingHom K) P) g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockS_eq_sum _ _ (map (Int.castRingHom K) P).support (support_map_subset _ _), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem pairK_mapVV_int (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) (P : MvPolynomial (ι × Fin n × Fin n) ℤ)
    (hx : (x : Pol K ι n) = map (Int.castRingHom K) P) :
    pairK lam (fun τ => (G τ).map φ) (mapVV φ lam x) (mapVV φ lam y) = φ (pairK lam G x y) := by
  have h1 : (map φ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map φ)ᵀ).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : map φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map φ)ᵀ) (map φ y.1) :=
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y.1) h1
  have h3 : φ (gramTw lam G) = gramTw lam fun τ => (G τ).map φ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  have h4 : φ (extNorm K lam) = extNorm ℂ lam := by
    unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← map_extremal φ n (lam τ), ← map_extremal (Int.castRingHom K) n (lam τ), fockS_map_int]
  have h5 := fockS_map_int φ P (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1)
  rw [← hx] at h5
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, mapVV_coe, mapVV_coe, ← h2, fockL_apply, fockL_apply,
    h5, map_mul, map_div₀, h3, h4]

end BaseChange

def reindexFam {ι M : Type} [Monoid M] (e : ι → ι) : (ι → M) →* (ι → M) :=
  MonoidHom.pi fun τ => Pi.evalMonoidHom (fun _ => M) (e τ)

theorem reindexFam_apply {ι M : Type} [Monoid M] (e : ι → ι) (g : ι → M) (τ : ι) : reindexFam e g τ = g (e τ) := rfl

end GlobalTheory.CoefModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

variable {D : D7}

theorem exists_coef_round_at (V : HSp D) (hV : ∀ τ, (V.gram.map (tauE D τ)).PosDef)
    (lam : D.what₂.Tau → DomWeight V.rank) (σ : D.what₂.LL →+* ℂ) (p : D.what₂.Tau ≃ D.what₂.Tau)
    (hp : ∀ τ, labE σ τ = tauE D (p τ)) :
    ∃ (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W), c.Is ∧
      (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
        ∀ v, c₁ (rhoVr (labLL D) lam γE v) = c.ρ (γ : GA D V) (c₁ v)) ∧
      (LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL lam a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤ ∧
      ∀ a y, inner ℂ (c₁ (bVV D.what₂.LL lam a)) (c₁ y) = σ (pairVr (labLL D) lam V.gram (bVV D.what₂.LL lam a) y) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨hc, hs⟩ := realGL_laws hθ V
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hG : ∀ τ, (((V.gram.map (tauE D (p τ)))⁻¹)ᵀ).PosDef := fun τ => (hV (p τ)).inv.transpose
  have hlab : ∀ τ x, σ (labLL D τ x) = tauE D (p τ) x := fun τ x => DFunLike.congr_fun (hp τ) x
  refine ⟨coefOf lam hG (invTrK.comp ((reindexFam p).comp (realGL θ V))),
    (toHilb lam hG).toLinearMap.comp (mapVV σ lam), coefOf_is lam hG _ (fun h hh => ?_) (fun h τ => ?_)
      (fun τ => ?_) (fun g hg => ?_), fun γ γE hγ v => ?_, ?_, ?_, fun a y => ?_⟩
  · have : realGL θ V h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom V h) = 1
      rw [show infHom V h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this, map_one, map_one]
  · exact invTr_unitary (g := realGL θ V h (p τ)) (GlobalTheory.RecDictModel.archM_unitary V (hθ (p τ)) h)
  · refine ((hc (p τ)).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ (p τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (reindexFam p.symm (invTrK g)) fun ρ => by
      have := invTr_unitary (hg (p.symm ρ))
      rwa [p.apply_symm_apply, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (hV ρ).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e]
    refine funext fun τ => ?_
    show inside₂ ℂ _ (inside₂ ℂ _ (g (p.symm (p τ)))) = g τ
    rw [p.symm_apply_apply, invTr_invTr]
  · show toHilb lam hG (mapVV _ lam (rhoK lam (invTrK (embGL (labLL D) γE)) v)) =
      rhoH lam hG (invTrK (reindexFam p (realGL θ V γ))) (toHilb lam hG (mapVV _ lam v))
    have e : (fun τ => Formalism.UG.bc σ (invTrK (embGL (labLL D) γE) τ)) = invTrK (reindexFam p (realGL θ V γ)) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, reindexFam_apply, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    rw [rhoH_toHilb, mapVV_rhoK, e]
  · exact (linearIndependent_mapVV σ lam).map' (toHilb lam hG).toLinearMap (LinearEquiv.ker _)
  · exact span_mapVV σ lam
  · obtain ⟨P, hP⟩ := bVVfun_int D.what₂.LL lam a
    show inner ℂ (toHilb lam hG (mapVV σ lam (bVV D.what₂.LL lam a))) (toHilb lam hG (mapVV σ lam y)) =
      σ (pairK lam (gramKd (labLL D) V.gram) (bVV D.what₂.LL lam a) y)
    rw [inner_toHilb, ← pairK_mapVV_int σ lam _ _ y P ((bVV_coe _ lam a).trans hP)]
    have e : (fun τ => ((V.gram.map (tauE D (p τ)))⁻¹)ᵀ) = fun τ => (gramKd (labLL D) V.gram τ).map σ := by
      funext τ
      have e1 : V.gram.map (tauE D (p τ)) = (V.gram.map (labLL D τ)).map σ := by
        ext a b
        exact (hlab _ _).symm
      have hu : IsUnit (V.gram.map (labLL D τ)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact ((_root_.map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)).isUnit
      rw [gramKd, Matrix.transpose_map, e1]
      congr 1
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg (fun G => pairK lam G (mapVV σ lam (bVV D.what₂.LL lam a)) (mapVV σ lam y)) e

theorem exists_coefAt_of_posDef (i : Fin D.R.m) (h : (Vc D i).IsPosDef) (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) :
    ∃ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ := by
  have hl := (GlobalTheory.GalLift.labels_overK σ).1 hσ
  have hV : ∀ τ, ((Vc D i).gram.map (tauE D τ)).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [h (tauE D τ)] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hg : gramV D i = (Vc D i).gram := by
    rw [gramV, GlobalTheory.StdFrame.neg_eq_false_of_posDef D i h, if_neg Bool.false_ne_true]
  have H := exists_coef_round_at (Vc D i) hV (lamV D i) σ (Equiv.ofBijective _ hl.1).symm fun τ =>
    (congrArg (labE σ) ((Equiv.ofBijective _ hl.1).apply_symm_apply τ).symm).trans (hl.2 _)
  obtain ⟨c, c₁, h1, h2, h3, h4, h5⟩ := H
  exact ⟨c, c₁, h1, h2, h3, h4, fun a b => hg ▸ h5 a _⟩

end GlobalTheory.CoefModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrbitCentralizerAlmostAll
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.KottAlmost

section Generic

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

def shU (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : Aˣ where
  val := (σ u).unop
  inv := (σ ((u⁻¹ : Aˣ) : A)).unop
  val_inv := by rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  inv_val := by rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem shU_inv_val (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : (((shU σ u)⁻¹ : Aˣ) : A) = (σ ((u⁻¹ : Aˣ) : A)).unop := rfl

theorem sh_mul (σ : A →+* Aᵐᵒᵖ) (a b : A) : (σ (a * b)).unop = (σ b).unop * (σ a).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem comm_sh (σ : A →+* Aᵐᵒᵖ) (a : A) (y : Aˣ) (cy : Kˣ)
    (hy : (y : A) * (σ y).unop = algebraMap K A cy) (ha : a * y = y * a) :
    (σ a).unop * y = y * (σ a).unop := by
  have hsy : (σ y).unop = ((y⁻¹ : Aˣ) : A) * algebraMap K A cy := by
    rw [← hy, ← mul_assoc, Units.inv_mul, one_mul]
  have h := congrArg (fun z => (σ z).unop) ha
  simp only [sh_mul] at h
  rw [hsy] at h
  have h' : (((y⁻¹ : Aˣ) : A) * (σ a).unop) * algebraMap K A cy =
      ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * algebraMap K A cy := by
    rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, h]; simp only [mul_assoc]
  have hk : IsUnit (algebraMap K A cy) := cy.isUnit.map (algebraMap K A)
  have h'' := hk.mul_right_cancel h'
  calc (σ a).unop * y = y * (((y⁻¹ : Aˣ) : A) * (σ a).unop) * y := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = y * ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * y := by rw [h'']
    _ = y * (σ a).unop := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

end Generic

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

section Step

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

theorem step (σ : A →+* Aᵐᵒᵖ) (hinv : ∀ a, (σ (σ a).unop).unop = a)
    (I : A → Prop) (J : K → Prop) (hJ1 : J 1)
    (h1 : ∀ a b, I a → I b → I (a * b)) (h2 : ∀ a, I a → I (σ a).unop)
    (γ : uGroup (A := K) σ)
    (h3 : ∀ g : Aˣ, I ((g⁻¹ * (γ : Aˣ × Kˣ).1 * g : Aˣ) : A) → I ((g⁻¹ * (γ : Aˣ × Kˣ).1⁻¹ * g : Aˣ) : A) →
      ∃ e : Aˣ, e * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * e ∧ I ((e⁻¹ * g : Aˣ) : A) ∧ I ((g⁻¹ * e : Aˣ) : A))
    (h4 : ∀ s : Aˣ, s * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * s → I (s : A) → I ((s⁻¹ : Aˣ) : A) →
      (σ s).unop = s → ∃ t : Aˣ, t * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * t ∧ I (t : A) ∧ I ((t⁻¹ : Aˣ) : A) ∧
        (t : A) * (σ t).unop = s)
    (g : uGroup (A := K) σ)
    (hg : I (((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1 : A) ∧
      I (((((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A)) :
    ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id _) γ, ∃ d : uGroup (A := K) σ,
      (I ((d : Aˣ × Kˣ).1 : A) ∧ I ((((d : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A) ∧ J ((d : Aˣ × Kˣ).2 : K) ∧
        J ((((d : Aˣ × Kˣ).2)⁻¹ : Kˣ) : K)) ∧ g = c * d := by
  obtain ⟨⟨g1, cg⟩, hgm⟩ := g
  obtain ⟨⟨y, cy⟩, hym⟩ := γ
  have hgm' : (g1 : A) * (σ g1).unop = algebraMap K A cg := hgm
  have hym' : (y : A) * (σ y).unop = algebraMap K A cy := hym
  have hg1 : I ((g1⁻¹ * y * g1 : Aˣ) : A) := hg.1
  have hg2 : I ((g1⁻¹ * y⁻¹ * g1 : Aˣ) : A) := by
    have e : (g1⁻¹ * y * g1 : Aˣ)⁻¹ = g1⁻¹ * y⁻¹ * g1 := by group
    rw [← e]; exact hg.2
  obtain ⟨e, he, hu1, hu2⟩ := h3 g1 hg1 hg2
  obtain ⟨u, hu⟩ : ∃ u : Aˣ, u = e⁻¹ * g1 := ⟨_, rfl⟩
  rw [← hu] at hu1
  have hu2' : I ((u⁻¹ : Aˣ) : A) := by
    have : u⁻¹ = g1⁻¹ * e := by rw [hu]; group
    rw [this]; exact hu2
  obtain ⟨s, hs⟩ : ∃ s : Aˣ, s = u * shU σ u := ⟨_, rfl⟩
  have hsv : (s : A) = (u : A) * (σ u).unop := by rw [hs]; rfl
  have hsI : I (s : A) := by rw [hsv]; exact h1 _ _ hu1 (h2 _ hu1)
  have hsI' : I ((s⁻¹ : Aˣ) : A) := by
    rw [hs, _root_.mul_inv_rev, Units.val_mul, shU_inv_val]
    exact h1 _ _ (h2 _ hu2') hu2'
  have hss : (σ s).unop = s := by
    rw [hsv, sh_mul, hinv]
  have hsval : (s : A) = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop := by
    rw [hsv, hu, Units.val_mul, sh_mul, ← hgm']
    simp only [mul_assoc]
  have hey : ((e⁻¹ : Aˣ) : A) * y = y * ((e⁻¹ : Aˣ) : A) := by
    have : e⁻¹ * y = y * e⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, he, mul_inv_cancel_right]
    exact congrArg Units.val this
  have hby := comm_sh σ ((e⁻¹ : Aˣ) : A) y cy hym' hey
  have hsy : s * y = y * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsval]
    calc ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop * y
        = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (y * (σ ((e⁻¹ : Aˣ) : A)).unop) := by rw [mul_assoc, hby]
      _ = ((e⁻¹ : Aˣ) : A) * (y * algebraMap K A cg) * (σ ((e⁻¹ : Aˣ) : A)).unop := by
          rw [mul_assoc ((e⁻¹ : Aˣ) : A), ← mul_assoc (algebraMap K A cg), Algebra.commutes]; simp only [mul_assoc]
      _ = (y : A) * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) := by
          rw [← mul_assoc ((e⁻¹ : Aˣ) : A) (y : A), hey]; simp only [mul_assoc]
  obtain ⟨t, ht, htI, htI', hts⟩ := h4 s hsy hsI hsI' hss
  have hcm : ((e * t : Aˣ) : A) * (σ ((e * t : Aˣ) : A)).unop = algebraMap K A cg := by
    rw [Units.val_mul, sh_mul]
    calc (e : A) * t * ((σ t).unop * (σ e).unop) = e * (t * (σ t).unop) * (σ e).unop := by
          simp only [mul_assoc]
      _ = e * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) * (σ e).unop := by
          rw [hts, hsval]
      _ = algebraMap K A cg * ((σ ((e⁻¹ : Aˣ) : A)).unop * (σ e).unop) := by
          simp only [← mul_assoc, Units.mul_inv, one_mul]
      _ = _ := by rw [← sh_mul, Units.mul_inv, map_one, MulOpposite.unop_one, mul_one]
  have hdm : ((t⁻¹ * u : Aˣ) : A) * (σ ((t⁻¹ * u : Aˣ) : A)).unop = algebraMap K A ((1 : Kˣ) : K) := by
    rw [Units.val_mul, sh_mul, Units.val_one, map_one]
    calc ((t⁻¹ : Aˣ) : A) * u * ((σ u).unop * (σ ((t⁻¹ : Aˣ) : A)).unop)
        = ((t⁻¹ : Aˣ) : A) * ((u : A) * (σ u).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by simp only [mul_assoc]
      _ = ((t⁻¹ : Aˣ) : A) * ((t : A) * (σ t).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by
          rw [hts, hsv]
      _ = 1 := by
          rw [← mul_assoc, Units.inv_mul, one_mul, ← sh_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  refine ⟨⟨(e * t, cg), hcm⟩, ?_, ⟨(t⁻¹ * u, 1), hdm⟩, ⟨h1 _ _ htI' hu1, ?_, hJ1, by rw [inv_one]; exact hJ1⟩, ?_⟩
  · apply Subtype.ext; apply Prod.ext
    · show e * t * y = y * (e * t)
      rw [mul_assoc, ht, ← mul_assoc, he, mul_assoc]
    · show cg * cy = cy * cg
      exact mul_comm _ _
  · show I (((t⁻¹ * u)⁻¹ : Aˣ) : A)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    exact h1 _ _ hu2' htI
  · apply Subtype.ext; apply Prod.ext
    · show g1 = e * t * (t⁻¹ * u)
      rw [hu]; group
    · show cg = cg * 1
      rw [mul_one]

end Step

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

theorem starT_starT {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R a).unop).unop = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => rw [starT_tmul, starT_tmul, G.star_star]
  | add a b ha hb => rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), MulOpposite.unop_add, ha, hb]

end GlobalTheory.OrbFinAf.KottAlmost
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSumAtPlaceDecomposition
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold.OrbitSumGen

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
  (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1))

theorem posV_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

def lineOf (z : Fin G.n → ℂ) (hz : z ≠ 0) : PLv G v β := Projectivization.mk ℂ z hz

def pairOfDat (d : Dat G v β) : Ys G v β x t hx Kf K' :=
  (LeftCosets.mk _ _ d.1, lineOf G v β d.2.1 (posV_ne_zero G v β d.2))

variable {G v β}

theorem smul_line_mk (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz =
      lineOf G v β ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
        (fun h => hz (toV_injective G v β y (by rw [Matrix.toLin'_apply, h, map_zero]))) := by
  change Projectivization.map _ _ (Projectivization.mk ℂ z hz) = _
  rw [Projectivization.map_mk]
  congr 1

theorem smul_line_eq_iff (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz = lineOf G v β z hz ↔
      FixL G v β y z := by
  rw [smul_line_mk]
  change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ ↔ _
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, Units.smul_def]⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hz
      apply toV_injective G v β y
      rw [Matrix.toLin'_apply, hc, zero_smul, map_zero]
    exact ⟨Units.mk0 c hc0, by rw [Units.smul_def, Units.val_mk0, hc]⟩

theorem fixL_smul_iff (y : grp G β) (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [Matrix.mulVec_smul, smul_smul] at he
    have := congrArg (fun w => c⁻¹ • w) he
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [this]
    congr 1
    field_simp
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [Matrix.mulVec_smul, he, smul_comm]⟩

variable (G v β)

theorem same_iff_smul (a b : Dat G v β) :
    Same G v β x t hx Kf K' a b ↔ ∃ y : grp G β, y • pairOfDat G v β x t hx Kf K' a = pairOfDat G v β x t hx Kf K' b := by
  constructor
  · rintro ⟨y, k, c, hk1, hk2, hc, h1, h2⟩
    refine ⟨y, Prod.ext ?_ ?_⟩
    · change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1
      rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1]
      change (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * (((toAfF G β x t hx).prod (toP1 G β)) y * a.1 * k) ∈ _
      rw [inv_mul_cancel_left]
      exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
    · change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _
      rw [smul_line_mk]
      change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
      rw [h2, Units.smul_def, smul_smul]
      simp [hc]
  · rintro ⟨y, hy⟩
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1 at h1
    change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _ at h2
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk] at h1
    rw [smul_line_mk] at h2
    change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ at h2
    rw [Projectivization.mk_eq_mk_iff] at h2
    obtain ⟨u, hu⟩ := h2
    refine ⟨y, (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * b.1, ((u⁻¹ : ℂˣ) : ℂ),
      (Subgroup.mem_prod.1 h1).1, (Subgroup.mem_prod.1 h1).2, Units.ne_zero _, ?_, ?_⟩
    · exact (mul_inv_cancel_left _ _).symm
    · rw [← hu, Units.smul_def, smul_smul]
      simp

def ptsToOrbit : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quot.lift (fun d => Quotient.mk (MulAction.orbitRel (grp G β) (Ys G v β x t hx Kf K')) (pairOfDat G v β x t hx Kf K' d))
    (fun a b h => by
      obtain ⟨y, hy⟩ := (same_iff_smul G v β x t hx Kf K' a b).1 h
      exact Quotient.sound ⟨y⁻¹, show y⁻¹ • _ = _ by rw [← hy, inv_smul_smul]⟩)

theorem ptsToOrbit_eq (q : Pts G v β x t hx Kf K') :
    ptsToOrbit G v β x t hx Kf K' q = Quotient.mk _ (pairOfDat G v β x t hx Kf K' (Quot.out q)) :=
  (congrArg (ptsToOrbit G v β x t hx Kf K') (Quot.out_eq q)).symm

theorem ptsToOrbit_injective : Function.Injective (ptsToOrbit G v β x t hx Kf K') := by
  intro q₁ q₂ h
  rw [ptsToOrbit_eq, ptsToOrbit_eq] at h
  obtain ⟨g, hg⟩ := Quotient.exact h
  rw [← Quot.out_eq q₁, ← Quot.out_eq q₂]
  exact (Quot.sound ((same_iff_smul G v β x t hx Kf K' _ _).2 ⟨g, hg⟩)).symm

theorem card_stab_eq (d : Dat G v β) :
    Nat.card (Stab G v β x t hx Kf K' d) =
      Nat.card (MulAction.stabilizer (grp G β) (pairOfDat G v β x t hx Kf K' d)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [MulAction.mem_stabilizer_iff, Prod.ext_iff]
  change _ ↔ y • LeftCosets.mk _ _ d.1 = LeftCosets.mk _ _ d.1 ∧
    y • lineOf G v β d.2.1 _ = lineOf G v β d.2.1 _
  rw [smul_line_eq_iff, ← MulAction.mem_stabilizer_iff, ← stab_eq_stabilizer]
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, and_assoc]

theorem cxF_pairOfDat (wt : Polynomial G.F → ℂ) (f : G.GAf → ℂ) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (f' : Gr G 1 → ℂ) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) (d : Dat G v β) (y : grp G β) :
    cxF G v wt β x t hx Kf f K' f' (pairOfDat G v β x t hx Kf K' d) y =
      if FixL G v β y d.2.1 then
        f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      else 0 := by
  obtain ⟨k, hk, e⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β)) (K := Kf.prod K') d.1
  have hz := posV_ne_zero G v β d.2
  obtain ⟨u, hu⟩ : ∃ u : ℂˣ, u • d.2.1 = Projectivization.rep (lineOf G v β d.2.1 hz) :=
    (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hz).1
      (Projectivization.mk_rep (lineOf G v β d.2.1 hz))
  have hpos : 0 < (star (Projectivization.rep (lineOf G v β d.2.1 hz)) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (lineOf G v β d.2.1 hz))).re := by
    rw [← hu]
    have := (pos_iff_smul_toV p G v β 1 d.2.1 u u.ne_zero).1 d.2.2
    simpa [Units.smul_def] using this
  have hfix : FixL G v β y (Projectivization.rep (lineOf G v β d.2.1 hz)) ↔ FixL G v β y d.2.1 := by
    rw [← hu, Units.smul_def]
    exact fixL_smul_iff y _ _ u.ne_zero
  simp only [cxF, pairOfDat, hpos, hfix, true_and, e, Prod.fst_mul, Prod.snd_mul]
  split_ifs with hF
  · rw [Subgroup.mem_prod] at hk
    have e1 : (d.1.1 * k.1)⁻¹ * toAfF G β x t hx y * (d.1.1 * k.1) =
        k.1⁻¹ * (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * k.1 := by group
    have e2 : (d.1.2 * k.2)⁻¹ * toP1 G β y * (d.1.2 * k.2) =
        k.2⁻¹ * (d.1.2⁻¹ * toP1 G β y * d.1.2) * k.2 := by group
    rw [e1, e2, hf _ hk.1, hf' _ hk.2]
  · rfl

end GlobalTheory.CxUnfold.OrbitSumGen

namespace GlobalTheory.CxUnfold.OrbitSumGen

end GlobalTheory.CxUnfold.OrbitSumGen
end
end

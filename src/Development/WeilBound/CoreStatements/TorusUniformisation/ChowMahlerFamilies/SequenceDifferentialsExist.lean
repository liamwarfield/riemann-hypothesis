module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceDifferentialsExist
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceDifferentials

theorem main (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] (p : ℕ) [hpp : Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ NumberField.discr E) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (hm : (p : A) ∈ m) (O : Type) [CommRing O] [IsLocalRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (σ : E →+* Ω) :
    (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧
      ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : IsIntegral ℤ (σ (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := A)).1 h1
    exact ⟨algebraMap A O b, by rw [← IsScalarTower.algebraMap_apply, hb]⟩
  · set n : ℕ := (NumberField.discr E).natAbs with hn
    have hx : ((n : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
      rw [hn, ← NumberField.absNorm_differentIdeal E (𝓞 E)]
      exact Ideal.absNorm_mem _
    have hpn : ¬ p ∣ n := fun h => hp (Int.natCast_dvd.2 h)
    have hnm : ((n : ℕ) : A) ∉ m := by
      intro h
      have hc : IsCoprime (p : A) (n : A) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hpp.out).2 hpn)
      obtain ⟨u, v, huv⟩ := hc
      exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one m).2
        (huv ▸ m.add_mem (m.mul_mem_left u hm) (m.mul_mem_left v h)))
    have hu : IsUnit (algebraMap A O (n : A)) :=
      IsLocalization.map_units O (⟨(n : A), hnm⟩ : m.primeCompl)
    obtain ⟨o, ho⟩ := hu.exists_left_inv
    refine ⟨(n : 𝓞 E), hx, o, ?_⟩
    have h2 := congrArg (algebraMap O Ω) ho
    simp only [map_mul, map_natCast, map_one] at h2
    have h3 : σ (((n : ℕ) : 𝓞 E) : E) = (n : Ω) := by simp
    rw [h3, h2]

end PositivityTheory.Xgn.SequenceDifferentials

theorem PositivityTheory.Xgn.sequence_differentials_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ hp A _ _ _ m _ hm O _ _ _ _ _ _ _ σ
  exact PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hp A m hm O σ
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsFunctionAtPoint
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionAtPoint

theorem germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) (a : X.presheaf.stalk (x z)) :
    ∃ r s : R, s ∉ z.asIdeal ∧ φ s * genMap ξ ⟨x z, hz⟩ a = φ r ∧ (r ∉ z.asIdeal → IsUnit a) := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hu : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hu
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := ConcreteCategory.congr_hom e4 a
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl ((x.stalkMap z).hom a)
  refine ⟨r, s, s.2, ?_, fun hr => ?_⟩
  · rw [← e5, ← hlam, ← hlam, ← map_mul, mul_comm]
    exact congrArg lam hrs
  · have h1 : IsUnit (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z) r) :=
      IsLocalization.map_units _ (⟨r, hr⟩ : z.asIdeal.primeCompl)
    rw [← hrs] at h1
    exact isUnit_of_map_unit (x.stalkMap z).hom a (isUnit_of_mul_isUnit_left h1)

theorem inv_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) {b : Ω} (hb : b ∈ regAt ξ ⟨x z, hz⟩) (w : R)
    (hw : φ w * b = 1) : φ w ∈ regAt ξ ⟨x z, hz⟩ := by
  obtain ⟨a, rfl⟩ := hb
  obtain ⟨r, s, hs, e, hu⟩ := germ_frac ξ φ hφ x hx z hz a
  have e1 : s = w * r := by
    apply hφ
    rw [map_mul, ← e, mul_left_comm, hw, _root_.mul_one]
  have hr : r ∉ z.asIdeal := fun h => hs (e1 ▸ z.asIdeal.mul_mem_left w h)
  obtain ⟨a', ha'⟩ := (hu hr).exists_right_inv
  refine ⟨a', ?_⟩
  have e2 := congrArg (genMap ξ ⟨x z, hz⟩) ha'
  rw [map_mul, map_one] at e2
  rw [← _root_.one_mul (genMap ξ ⟨x z, hz⟩ a'), ← hw, _root_.mul_assoc, e2, _root_.mul_one]

end PositivityTheory.Xgn.FunctionAtPoint

theorem PositivityTheory.Xgn.exists_function_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd p _ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' hc' P z
  have hC : HasConstants ℤ A y := (GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd A).2.2.2.1
  have hφ : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have hinv := fun {b : Ω} (hb : b ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) (w : CR O y c') =>
    PositivityTheory.Xgn.FunctionAtPoint.inv_reg 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) hb w
  obtain ⟨c'', hc''⟩ : ∃ c'', InChart 𝔐.ξ (mseg y) c'' ⟨P.x z, 𝔐.all _⟩ := 𝔐.tie.cover ⟨P.x z, 𝔐.all _⟩
  have hA : ∀ a : A, algebraMap A Ω a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ := fun a =>
    GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt ℤ y c'' _ hc'' (fun o => by simp) (hC c'' hc''.1 a)
  refine ⟨⟨hc', fun j => ?_⟩, fun o => ?_, ?_⟩
  · have h1 : mseg y c'' / mseg y c' ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hc''.2 c') ⟨mseg y c'' / mseg y c', Algebra.subset_adjoin ⟨c'', rfl⟩⟩ (by
        have h0 := hc''.1
        change mseg y c'' / mseg y c' * (mseg y c' / mseg y c'') = 1
        field_simp)
    have h2 := mul_mem (hc''.2 j) h1
    have h0 := hc''.1
    have e : mseg y j / mseg y c'' * (mseg y c'' / mseg y c') = mseg y j / mseg y c' := by field_simp
    rwa [e] at h2
  · obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj m.primeCompl o
    obtain ⟨u, hu⟩ := (IsLocalization.map_units O s).exists_left_inv
    have h1 : algebraMap O Ω u ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hA s) (algebraMap O (CR O y c') u) (by
        change algebraMap O Ω u * _ = 1
        rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu, map_one])
    have e : o = algebraMap A O a * u := by
      have has' : o * algebraMap A O s = algebraMap A O a := has
      rw [← has', _root_.mul_assoc, mul_comm _ u, hu, _root_.mul_one]
    rw [e, map_mul, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (hA a) h1
  · rintro _ ⟨a, rfl⟩
    obtain ⟨r, s, hs, e, -⟩ :=
      PositivityTheory.Xgn.FunctionAtPoint.germ_frac 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) a
    exact ⟨r, s, hs, e⟩
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StalkPointFactorization
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.StalkPointFactorization

theorem ext_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {S T : CommRingCat.{0}} (i : S ⟶ T)
    (hi : Function.Injective i.hom) (f g : Spec S ⟶ X) (hf : ∀ z, f z ∈ U) (hg : ∀ z, g z ∈ U)
    (e : Spec.map i ≫ f = Spec.map i ≫ g) : f = g := by
  have hf' : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hf z
  have hg' : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hg z
  obtain ⟨a, ha⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec f hf')
  obtain ⟨b, hb⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec g hg')
  have ea : Spec.map a ≫ hU.fromSpec = f := by rw [ha, IsOpenImmersion.lift_fac]
  have eb : Spec.map b ≫ hU.fromSpec = g := by rw [hb, IsOpenImmersion.lift_fac]
  rw [← ea, ← eb, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  have e2 : a ≫ i = b ≫ i := Spec.map_injective e
  have e3 : a = b := by
    ext s
    apply hi
    exact ConcreteCategory.congr_hom e2 s
  rw [← ea, ← eb, e3]

theorem fromSpecStalk_mem {X : Scheme.{0}} {U : X.Opens} {y : X} (hy : y ∈ U) (z : Spec (X.presheaf.stalk y)) :
    X.fromSpecStalk y z ∈ U := by
  have h : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact Specializes.mem_open h U.isOpen hy

end PositivityTheory.Xgn.StalkPointFactorization

theorem PositivityTheory.Xgn.stalk_point_factorization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (U : X.Opens), IsAffineOpen U → ∀ (R : Type) [CommRing R] (φ : R →+* Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap φ ≫ x = ξ → (∀ z, x z ∈ U) → ∀ (q : Cpt ξ), q.1 ∈ U → ∀ ψ : R →+* X.presheaf.stalk q.1, (genMap ξ q).comp ψ = φ → spMap ψ ≫ x = X.fromSpecStalk q.1 := by
  intro X Ω _ ξ hξ U hU R _ φ x hx hxU q hq ψ hψ
  refine PositivityTheory.Xgn.StalkPointFactorization.ext_of_affine hU (S := X.presheaf.stalk q.1) (T := CommRingCat.of Ω)
    (CommRingCat.ofHom (genMap ξ q)) (hξ.inj q) (spMap ψ ≫ x) (X.fromSpecStalk q.1) (fun z => hxU (spMap ψ z))
    (PositivityTheory.Xgn.StalkPointFactorization.fromSpecStalk_mem hq) ?_
  have h1 : spMap (genMap ξ q) ≫ spMap ψ = spMap φ := by
    rw [← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : spMap (genMap ξ q) ≫ spMap ψ ≫ x = ξ := by
    rw [← Category.assoc, h1, hx]
  exact h2.trans (GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk q).symm
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAtOneCompOfIsDiffOf
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionDerivativeEndomorphism

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (F : X ⟶ Y)
    (s : Γ(Y, ⊤)) :
    BT.valAt v ⊤ le_top ((F.appLE ⊤ ⊤ le_top).hom s) = BT.valAt (v ≫ F) ⊤ le_top s := by
  unfold BT.valAt
  rw [← Scheme.Hom.appLE_comp_appLE v F ⊤ ⊤ ⊤ le_top le_top]
  rfl

theorem exists_endo {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ)
    (h : Γ.IsTorsionAlong G x N i) (a : G ⟶ G) [IsMonHom a] :
    ∃ b : Γ.G ⟶ Γ.G, b.left ≫ i = i ≫ a.left := by
  let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
  have h1 : (g₀ ≫ a) ^ N = 1 := by
    rw [← MonObj.pow_comp, h0, MonObj.one_comp]
  obtain ⟨b, hb⟩ := (h.kernel Γ.G (g₀ ≫ a)).1 h1
  exact ⟨b, hb⟩

end PositivityTheory.Xgn.FunctionDerivativeEndomorphism

theorem PositivityTheory.Xgn.isDerAtOne_comp_of_isDiffOf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (B : L →ₗ[R] L), M.IsDiffOf a B → ∀ (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → ∀ (f : T → R) (w : Module.Dual R L), Γ.IsDerAtOne i M N f w → Γ.IsDerAtOne i M N (fun t => f (α t)) (w ∘ₗ B) := by
  intro R _ _ T _ Γ S G _ _ x i N h L _ _ M a _ B hB α hα f w hd
  obtain ⟨b, hb⟩ := PositivityTheory.Xgn.FunctionDerivativeEndomorphism.exists_endo Γ G x i N h a
  obtain ⟨s, hs, hv⟩ := hd
  refine ⟨(b.left.appLE ⊤ ⊤ le_top).hom s, ?_, ?_⟩
  · intro t
    rw [PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]
    have ht : Γ.pt t ≫ b = Γ.pt (α t) := h.inj _ _ _ (by
      rw [Over.comp_left, Category.assoc, hb, hα])
    have e := congrArg Over.Hom.left ht
    rw [Over.comp_left] at e
    rw [e]
    exact hs (α t)
  · intro e
    obtain ⟨v, hv1, hv2, -⟩ := hv e
    obtain ⟨v', hv1', hv2', hv3'⟩ := hv (B e)
    refine ⟨v, hv1, hv2, ?_⟩
    rw [PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]
    let Y : Over (Spec (CommRingCat.of R)) := Over.mk (v' ≫ Γ.G.hom)
    have hw : (v ≫ b.left) ≫ Γ.G.hom = Y.hom := by
      simp only [Y, Over.mk_hom, Category.assoc, Over.w]
      rw [hv1, hv1']
    have hvv := h.inj Y (Over.homMk (v ≫ b.left) hw) (Over.homMk v' rfl) (by
      simp only [Over.homMk_left, Category.assoc]
      rw [hb, ← Category.assoc, hv2, hv2', hB e, Over.comp_left, Category.assoc])
    have e2 := congrArg Over.Hom.left hvv
    simp only [Over.homMk_left] at e2
    rw [e2, hv3']
    simp only [LinearMap.comp_apply, map_one]
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SameGenericPointCharts
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SameGenericPointCharts

theorem genMap_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (w : Spec (CommRingCat.of R) ⟶ X)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫ w = ξ) (h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ w (IsLocalRing.closedPoint R)) :
    genMap ξ ⟨_, h⟩ = φ.comp (Scheme.stalkClosedPointTo w).hom := by
  have h' : ξ (IsLocalRing.closedPoint Ω) ⤳ w (IsLocalRing.closedPoint R) := h
  have key : X.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ
      = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (w (IsLocalRing.closedPoint R)))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hw, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  exact congrArg CommRingCat.Hom.hom key

theorem spec_closed {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (w : Spec (CommRingCat.of R) ⟶ X)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫ w = ξ) : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ w (IsLocalRing.closedPoint R) := by
  subst hw
  have := (IsLocalRing.specializes_closedPoint (R := R)
    (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint Ω))).map w.continuous
  exact this

theorem chart_local {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {κ : Type} (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    {R : Type} [CommRing R] [IsLocalRing R] (φ : R →+* Ω) (hφ : Function.Injective φ)
    (hx : ∀ c', x c' / x c ∈ φ.range) (w : Spec (CommRingCat.of R) ⟶ X)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫ w = ξ) :
    ∃ h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ w (IsLocalRing.closedPoint R), InChart ξ x c ⟨_, h⟩ := by
  have h := spec_closed ξ φ w hw
  refine ⟨h, hc, fun c' => ?_⟩
  obtain ⟨c₀, h0, hreg⟩ := T.cover ⟨_, h⟩
  obtain ⟨a, ha⟩ := hreg c
  obtain ⟨b, hb⟩ := hx c₀
  have ha' : φ ((Scheme.stalkClosedPointTo w).hom a) = x c / x c₀ := by
    rw [← ha, genMap_eq ξ φ w hw h]; rfl
  have hu : IsUnit ((Scheme.stalkClosedPointTo w).hom a) := by
    refine IsUnit.of_mul_eq_one b (hφ ?_)
    rw [map_mul, ha', hb, map_one]
    field_simp
  have hu' : IsUnit a := IsLocalHom.map_nonunit _ hu
  obtain ⟨a', haa⟩ := hu'.exists_right_inv
  have h1 : genMap ξ ⟨_, h⟩ a' = x c₀ / x c := by
    have := congrArg (genMap ξ ⟨_, h⟩) haa
    rw [map_mul, map_one, ha] at this
    rw [eq_inv_of_mul_eq_one_right this, inv_div]
  have : x c' / x c = x c' / x c₀ * (x c₀ / x c) := by field_simp
  rw [this]
  exact mul_mem (hreg c') ⟨a', h1⟩

theorem chart_pt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {κ : Type} (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    {B : Type} [CommRing B] [IsDomain B] (i : B →+* Ω) (hi : Function.Injective i)
    (hx : ∀ c', x c' / x c ∈ i.range) (z : Spec (CommRingCat.of B) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom i) ≫ z = ξ) (P : Spec (CommRingCat.of B)) :
    ∃ h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ z P, InChart ξ x c ⟨_, h⟩ := by
  let Q : PrimeSpectrum B := P
  have hun : ∀ y : Q.asIdeal.primeCompl, IsUnit (i y) := by
    intro y
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    have : (y : B) = 0 := hi (by rw [h, map_zero])
    rw [this]; exact Q.asIdeal.zero_mem
  let R := Localization.AtPrime Q.asIdeal
  let φ : R →+* Ω := IsLocalization.lift hun
  have hφi : φ.comp (algebraMap B R) = i := IsLocalization.lift_comp hun
  have hφ : Function.Injective φ := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h
      rw [← hφi]; exact congrArg φ h
    · intro h; rw [hi h]
  have hx' : ∀ c', x c' / x c ∈ φ.range := by
    intro c'
    obtain ⟨b, hb⟩ := hx c'
    exact ⟨algebraMap B R b, by rw [← hb, ← hφi]; rfl⟩
  have := chart_local ξ x T c hc φ hφ hx' (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφi, hz])
  have e : (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (IsLocalRing.closedPoint R) = z P := by
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap B R)) (IsLocalRing.closedPoint R) = P :=
      PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := Q.asIdeal))
    rw [← e1]; rfl
  generalize (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ z) (IsLocalRing.closedPoint R) = q at this e
  subst e
  exact this

theorem eq_of_affine {Y : Scheme.{0}} [IsAffine Y] {Ω B : Type} [CommRing Ω] [CommRing B] (i : B →+* Ω)
    (hi : Function.Injective i) (l l' : Spec (CommRingCat.of B) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom i) ≫ l = Spec.map (CommRingCat.ofHom i) ≫ l') : l = l' := by
  rw [← cancel_mono Y.isoSpec.hom]
  obtain ⟨f, hf⟩ := Spec.map_surjective (l ≫ Y.isoSpec.hom)
  obtain ⟨g, hg⟩ := Spec.map_surjective (l' ≫ Y.isoSpec.hom)
  have : f ≫ CommRingCat.ofHom i = g ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hf, hg, reassoc_of% h]
  have hfg : f = g := by
    ext a
    exact hi (congrArg (fun t => CommRingCat.Hom.hom t a) this)
  rw [← hf, ← hg, hfg]

end PositivityTheory.Xgn.SameGenericPointCharts

open PositivityTheory.Xgn.SameGenericPointCharts in
theorem PositivityTheory.Xgn.same_generic_point_charts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' := by
  intro X Ω _ ξ κ x T c hc B _ _ _ hi hx z z' hz hz'
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hr : ∀ w : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ w = ξ →
      Set.range w ⊆ Set.range U.ι := by
    rintro w hw _ ⟨P, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hmem _).2 (chart_pt ξ x T c hc _ hi hx w hw P)
  haveI : IsAffine U := hU
  have := eq_of_affine _ hi (IsOpenImmersion.lift U.ι z (hr z hz)) (IsOpenImmersion.lift U.ι z' (hr z' hz')) (by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac,
      hz, hz'])
  rw [← IsOpenImmersion.lift_fac U.ι z (hr z hz), this, IsOpenImmersion.lift_fac]
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorsionGroupBaseChange
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TorsionGroupBaseChange

theorem pow_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f') (N : ℕ)
    (g : Over.mk f ⟶ G) (g' : Over.mk f' ⟶ G) (hg : g.left = g'.left) : g ^ N = 1 ↔ g' ^ N = 1 := by
  subst h
  have : g = g' := Over.OverMorphism.ext hg
  rw [this]

theorem mul_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f')
    (u v : Over.mk f ⟶ G) (u' v' : Over.mk f' ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst h
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  rw [h1, h2]

def Kill {S Y : Scheme.{0}} (G : Over S) [GrpObj G] (N : ℕ) (g : Y ⟶ G.left) : Prop :=
  (Over.homMk g rfl : Over.mk (g ≫ G.hom) ⟶ G) ^ N = 1

theorem kernel' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (b : Y ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ G.left) (hg : g ≫ G.hom = b ≫ x) :
    Kill G N g ↔ ∃ y : Y ⟶ Γ.G.left, y ≫ Γ.G.hom = b ∧ y ≫ i = g := by
  unfold Kill
  constructor
  · intro hk
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 := (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).2 hk
    obtain ⟨y, hy⟩ := (h.kernel Y' g₀).1 hk'
    exact ⟨y.left, Over.w y, by simpa [g₀] using hy⟩
  · rintro ⟨y, hy1, hy2⟩
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 :=
      (h.kernel Y' g₀).2 ⟨Over.homMk y hy1, by simpa [g₀] using hy2⟩
    exact (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).1 hk'

theorem inj' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (y z : Y ⟶ Γ.G.left) (h1 : y ≫ Γ.G.hom = z ≫ Γ.G.hom) (h2 : y ≫ i = z ≫ i) : y = z := by
  let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (z ≫ Γ.G.hom)
  have := h.inj Y' (Over.homMk y h1) (Over.homMk z rfl) (by simpa using h2)
  simpa using congrArg Over.Hom.left this

end PositivityTheory.Xgn.TorsionGroupBaseChange

open PositivityTheory.Xgn.TorsionGroupBaseChange in
theorem PositivityTheory.Xgn.torsion_group_base_change : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F := by
  intro R R' _ _ _ _ _ T _ Γ Γ' S G _ x x' hx N i i' h h' a ha hpt
  have hKi' : Kill G N i' := (kernel' h' Γ'.G.hom i' h'.isOver).2 ⟨𝟙 _, by simp, by simp⟩
  have hi'x : i' ≫ G.hom = (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x := by
    rw [Category.assoc, hx]
    exact h'.isOver
  obtain ⟨F, hF1, hF2⟩ := (kernel' h _ i' hi'x).1 hKi'
  refine ⟨F, hF2, ?_⟩
  have lift : ∀ {Z : Scheme.{0}} (u : Z ⟶ Γ.G.left) (v : Z ⟶ Spec (CommRingCat.of R')),
      u ≫ Γ.G.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      ∃ l : Z ⟶ Γ'.G.left, l ≫ F = u ∧ l ≫ Γ'.G.hom = v := by
    intro Z u v huv
    have hk : Kill G N (u ≫ i) :=
      (kernel' h (u ≫ Γ.G.hom) (u ≫ i) (by simp only [Category.assoc, h.isOver])).2 ⟨u, rfl, rfl⟩
    have hg : (u ≫ i) ≫ G.hom = v ≫ x' := by
      rw [Category.assoc, h.isOver, ← Category.assoc, huv, Category.assoc, hx]
    obtain ⟨l, hl1, hl2⟩ := (kernel' h' v (u ≫ i) hg).1 hk
    refine ⟨l, inj' h _ _ ?_ ?_, hl1⟩
    · rw [Category.assoc, hF1, ← Category.assoc, hl1, huv]
    · rw [Category.assoc, hF2, hl2]
  have uniq : ∀ {Z : Scheme.{0}} (l₁ l₂ : Z ⟶ Γ'.G.left), l₁ ≫ F = l₂ ≫ F →
      l₁ ≫ Γ'.G.hom = l₂ ≫ Γ'.G.hom → l₁ = l₂ := by
    intro Z l₁ l₂ e1 e2
    refine inj' h' _ _ e2 ?_
    rw [← hF2, ← Category.assoc, e1, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hF1
      (fun s => Classical.choose (lift s.fst s.snd s.condition))
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).1)
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).2)
      (fun s m h1 h2 => uniq _ _ ?_ ?_))
    · rw [h1, (Classical.choose_spec (lift s.fst s.snd s.condition)).1]
    · rw [h2, (Classical.choose_spec (lift s.fst s.snd s.condition)).2]
  · intro S' u v u₀ v₀ hu hv
    apply inj' h
    · simp only [Category.assoc, hF1, Over.w, Over.w_assoc, Over.mk_hom]
    · let U₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (u₀.left ≫ i) (by simp [h.isOver])
      let V₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (v₀.left ≫ i) (by simp [h.isOver])
      let U₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (u.left ≫ i') (by simp [h'.isOver])
      let V₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (v.left ≫ i') (by simp [h'.isOver])
      have e0 := h.mul (Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) u₀ v₀ U₀ V₀ rfl rfl
      have e1 := h'.mul S' u v U₁ V₁ rfl rfl
      have e2 : (U₀ * V₀).left = (U₁ * V₁).left :=
        mul_congr (by simp [hx]) U₀ V₀ U₁ V₁ (by simp [U₀, U₁, hu, hF2]) (by simp [V₀, V₁, hv, hF2])
      rw [← e0, e2, e1, Category.assoc, hF2]
  · refine ⟨FractionRing R, inferInstance, algebraMap R (FractionRing R), RingHom.id _, a,
      fun t => (Γ.pt t).left, fun _ _ e => e, RingHom.id_comp _, ha, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · exact Over.w (Γ.pt t)
    · simp
    · apply inj' h
      · simp only [Category.assoc, Over.w, hF1, Over.w_assoc, Over.mk_hom]
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ha]
      · simp only [Category.assoc, hF2]
        exact hpt t
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfIsIntegralLoc
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceRing

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

theorem adjoin_int_le (O : Type) [CommRing O] [Algebra O Ω] (s : Set Ω) {b : Ω} (hb : b ∈ Algebra.adjoin ℤ s) :
    b ∈ Algebra.adjoin O s := by
  induction hb using Algebra.adjoin_induction with
  | mem t ht => exact Algebra.subset_adjoin ht
  | algebraMap n => simp
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

def incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (C : Subalgebra O Ω) (h : ∀ b ∈ B, b ∈ C) :
    B →+* C where
  toFun b := ⟨b.1, h b.1 b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (C : Subalgebra O Ω)
    (h : ∀ b ∈ B, b ∈ C) (b : B) : (incl B C h b : Ω) = b := rfl

theorem exists_emb (O : Type) [CommRing O] [Algebra O Ω] (s : Set Ω) :
    ∃ emb : Algebra.adjoin ℤ s →+* Algebra.adjoin O s, ∀ b, (emb b : Ω) = b :=
  ⟨incl _ _ fun _ hb => adjoin_int_le O s hb, coe_incl _ _ _⟩

theorem adjoin_le_regAt (O : Type) [CommRing O] [Algebra O Ω] {c : κ} (q : Cpt ξ) (hq : InChart ξ x c q)
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (Set.range fun j => x j / x c)) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact hq.2 j
  | algebraMap o => exact hO o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem mem_of_isIntegral (T : CoordTie ℤ ξ x) (hn : ∀ q : Cpt ξ, IsIntegrallyClosed (X.presheaf.stalk q.1))
    {c : κ} (hc : x c ≠ 0) {a : Ω} (ha : _root_.IsIntegral (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) a) :
    a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  refine (T.ring c hc a).2 fun p hp => ?_
  have hcl := hn p
  have hinj : Function.Injective (genMap ξ p) := T.gen.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.CompanionTheory.Ar.exists_frac_genMap ξ T.gen p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  let e : X.presheaf.stalk p.1 ≃+* (genMap ξ p).range :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun u v h => hinj (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩
  let emb : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* (genMap ξ p).range :=
    (algebraMap (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω).codRestrict _
      fun b => (T.ring c hc b.1).1 b.2 p hp
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := by
    refine IsIntegral.map_of_comp_eq (e.symm.toRingHom.comp emb) (RingHom.id Ω) (RingHom.ext fun b => ?_) ha
    exact congrArg Subtype.val (e.apply_symm_apply (emb b))
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

theorem exists_div (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), s ≠ 0 ∧
      s * a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  have hin := ChartPrimes.inChart_genPt T.gen x c hc
  have ha : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
    obtain ⟨s, hs⟩ := T.gen.bij.2 a
    refine ⟨s, ?_⟩
    rw [← hs]
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c _ hin a).1 ha
  exact ⟨s, hs, hu.1, hsa⟩

variable {A : Type} [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime]
  (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]

theorem exists_inv {s : A} (hs : s ∉ m) : ∃ o : O, algebraMap O Ω o * algebraMap A Ω s = 1 := by
  obtain ⟨o, ho⟩ := (IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)).exists_left_inv
  exact ⟨o, by rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul]; exact (congrArg _ ho).trans (map_one _)⟩

theorem exists_den (B : Subalgebra ℤ Ω) (hA : ∀ a : A, algebraMap A Ω a ∈ B) (s : Set Ω) (hs : s ⊆ B) {t : Ω}
    (ht : t ∈ Algebra.adjoin O s) : ∃ d : A, d ∉ m ∧ algebraMap A Ω d * t ∈ B := by
  have h1 : (1 : A) ∉ m := m.primeCompl.one_mem
  induction ht using Algebra.adjoin_induction with
  | mem t ht => exact ⟨1, h1, by simpa using hs ht⟩
  | algebraMap o =>
    obtain ⟨⟨a, d⟩, e⟩ := IsLocalization.surj m.primeCompl o
    refine ⟨d, d.2, ?_⟩
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e'
    rw [mul_comm, e']
    exact hA a
  | add u v _ _ hu hv =>
    obtain ⟨d, hd, hu⟩ := hu
    obtain ⟨d', hd', hv⟩ := hv
    refine ⟨d * d', m.primeCompl.mul_mem hd hd', ?_⟩
    have : algebraMap A Ω (d * d') * (u + v) =
        algebraMap A Ω d' * (algebraMap A Ω d * u) + algebraMap A Ω d * (algebraMap A Ω d' * v) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (hA _) hu) (mul_mem (hA _) hv)
  | mul u v _ _ hu hv =>
    obtain ⟨d, hd, hu⟩ := hu
    obtain ⟨d', hd', hv⟩ := hv
    refine ⟨d * d', m.primeCompl.mul_mem hd hd', ?_⟩
    have : algebraMap A Ω (d * d') * (u * v) = (algebraMap A Ω d * u) * (algebraMap A Ω d' * v) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem hu hv

theorem isUnit_den (C : Subalgebra O Ω) {d : A} (hd : d ∉ m) (z : C) (hz : (z : Ω) = algebraMap A Ω d) :
    IsUnit z := by
  obtain ⟨o, ho⟩ := exists_inv (Ω := Ω) m O hd
  refine IsUnit.of_mul_eq_one (algebraMap O C o) (Subtype.ext ?_)
  change (z : Ω) * algebraMap O Ω o = 1
  rw [hz, mul_comm, ho]


include m in
theorem mem_of_isIntegral_loc (s : Set Ω) (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ s)
    (hB : ∀ a : Ω, _root_.IsIntegral (Algebra.adjoin ℤ s) a → a ∈ Algebra.adjoin ℤ s) {a : Ω}
    (ha : _root_.IsIntegral (Algebra.adjoin O s) a) : a ∈ Algebra.adjoin O s := by
  let emb : Algebra.adjoin ℤ s →+* Algebra.adjoin O s :=
    incl _ _ fun _ hb => adjoin_int_le O s hb
  letI : Algebra (Algebra.adjoin ℤ s) (Algebra.adjoin O s) := emb.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin ℤ s) (Algebra.adjoin O s) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M : Submonoid (Algebra.adjoin ℤ s) := (IsUnit.submonoid (Algebra.adjoin O s)).comap emb
  haveI : IsLocalization M (Algebra.adjoin O s) := by
    refine (isLocalization_iff M _).2 ⟨fun d => d.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
    · obtain ⟨d, hd, hz⟩ := exists_den m O (Algebra.adjoin ℤ s) hA s Algebra.subset_adjoin z.2
      refine ⟨⟨⟨_, hz⟩, ⟨⟨_, hA d⟩, isUnit_den m O _ hd _ rfl⟩⟩, Subtype.ext ?_⟩
      exact mul_comm (z : Ω) (algebraMap A Ω d)
    · have : u = v := Subtype.ext (congrArg (fun z : Algebra.adjoin O s => (z : Ω)) h)
      rw [this]
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M a ha
  have h1 : ((d : Algebra.adjoin ℤ s) : Ω) * a ∈ Algebra.adjoin O s := adjoin_int_le O s (hB _ hd)
  obtain ⟨w, hw⟩ := IsUnit.exists_left_inv (show IsUnit (emb d) from d.2)
  have hw' : (w : Ω) * ((d : Algebra.adjoin ℤ s) : Ω) = 1 := congrArg Subtype.val hw
  have : a = (w : Ω) * (((d : Algebra.adjoin ℤ s) : Ω) * a) := by rw [← _root_.mul_assoc, hw', _root_.one_mul]
  rw [this]
  exact mul_mem w.2 h1


include m in
theorem loc_of_contraction (s : Set Ω) (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ s)
    (𝔮 : Ideal (Algebra.adjoin O s)) (h𝔮 : 𝔮.IsPrime) (emb : Algebra.adjoin ℤ s →+* Algebra.adjoin O s)
    (hemb : ∀ b, (emb b : Ω) = b) (R : Subring Ω) (hB : ∀ b ∈ Algebra.adjoin ℤ s, b ∈ R)
    (hI : ∀ b : Algebra.adjoin ℤ s, emb b ∉ 𝔮 ↔ ((b : Ω) ≠ 0 ∧ (b : Ω) ∈ R ∧ (b : Ω)⁻¹ ∈ R))
    (hR : ∀ a ∈ R, ∃ t ∈ Algebra.adjoin ℤ s, (t ≠ 0 ∧ t ∈ R ∧ t⁻¹ ∈ R) ∧ t * a ∈ Algebra.adjoin ℤ s) :
    (∀ o : O, algebraMap O Ω o ∈ R) ∧ ∀ a : Ω, a ∈ R ↔ ∃ u v : Algebra.adjoin O s, v ∉ 𝔮 ∧ a * (v : Ω) = (u : Ω) := by
  have hd𝔮 : ∀ d : A, d ∉ m → emb ⟨_, hA d⟩ ∉ 𝔮 := fun d hd h =>
    h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_den m O _ hd _ (hemb _)))
  have hC : ∀ z ∈ Algebra.adjoin O s, z ∈ R := fun z hz => by
    obtain ⟨d, hd, hz⟩ := exists_den m O _ hA _ Algebra.subset_adjoin hz
    obtain ⟨h0, -, hi⟩ := (hI ⟨_, hA d⟩).1 (hd𝔮 d hd)
    rw [← inv_mul_cancel_left₀ h0 z]
    exact mul_mem hi (hB _ hz)
  refine ⟨fun o => hC _ ((Algebra.adjoin O s).algebraMap_mem o), fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨t, ht, hu, hta⟩ := hR a ha
    refine ⟨emb ⟨_, hta⟩, emb ⟨t, ht⟩, (hI ⟨t, ht⟩).2 hu, ?_⟩
    rw [hemb, hemb]
    exact mul_comm a t
  · rintro ⟨u, v, hv, e⟩
    obtain ⟨d, hd, hz⟩ := exists_den m O _ hA _ Algebra.subset_adjoin v.2
    have he : emb ⟨_, hz⟩ = emb ⟨_, hA d⟩ * v := Subtype.ext (by rw [Subalgebra.coe_mul, hemb, hemb])
    have hne : emb ⟨_, hz⟩ ∉ 𝔮 := fun h => by
      rw [he] at h
      rcases h𝔮.mem_or_mem h with h1 | h1
      · exact hd𝔮 d hd h1
      · exact hv h1
    obtain ⟨h0, -, hi⟩ := (hI ⟨_, hz⟩).1 hne
    replace h0 : algebraMap A Ω d * (v : Ω) ≠ 0 := h0
    replace hi : (algebraMap A Ω d * (v : Ω))⁻¹ ∈ R := hi
    have : a = (algebraMap A Ω d * u) * (algebraMap A Ω d * v)⁻¹ := by
      rw [← e, eq_mul_inv_iff_mul_eq₀ h0]; ring
    rw [this]
    exact mul_mem (mul_mem (hB _ (hA d)) (hC _ u.2)) hi


include m in
theorem exists_point (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c))
    (𝔮 : Ideal (Algebra.adjoin O (Set.range fun j => x j / x c))) (h𝔮 : 𝔮.IsPrime) :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧
      ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ u v : Algebra.adjoin O (Set.range fun j => x j / x c),
        v ∉ 𝔮 ∧ a * (v : Ω) = (u : Ω) := by
  obtain ⟨emb, hemb⟩ := exists_emb O (Set.range fun j => x j / x c)
  obtain ⟨q, ⟨hq, hI⟩, -⟩ := chart_point_of_prime X Ω ξ ℤ κ x T c hc (𝔮.comap emb) (Ideal.comap_isPrime emb 𝔮)
  exact ⟨q, hq, loc_of_contraction m O _ hA 𝔮 h𝔮 emb hemb (regAt ξ q)
    (fun b hb => (T.ring c hc b).1 hb q hq) hI
    fun a ha => (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hq a).1 ha⟩

end

end PositivityTheory.Xgn.SequenceRing

theorem PositivityTheory.Xgn.sequence_ring_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ p _ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ c' hc
  have T : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hn : ∀ q : Cpt 𝔐.ξ, IsIntegrallyClosed (𝔐.X.presheaf.stalk q.1) := fun q => ((GlobalTheory.isNormalScheme_iff _).mp 𝔐.normal q.1).2
  have hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c') := fun a =>
    (T.ring c' hc _).2 fun q _ => IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ T.gen (hn q) _
      ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  have hF : IsFractionRing (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) Ω :=
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, h0, hz⟩ := PositivityTheory.Xgn.SequenceRing.exists_div T hc z
      exact ⟨⟨_, PositivityTheory.Xgn.SequenceRing.adjoin_int_le O _ hz⟩,
        ⟨_, PositivityTheory.Xgn.SequenceRing.adjoin_int_le O _ hs⟩, (mul_div_cancel_left₀ z h0).symm⟩
  have hN : IsNoetherianRing (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) := by
    haveI : Algebra.FiniteType O (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact Algebra.FiniteType.isNoetherianRing O _
  have hI : IsIntegrallyClosed (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) :=
    (isIntegrallyClosed_iff Ω).2 fun {a} ha =>
      ⟨⟨a, PositivityTheory.Xgn.SequenceRing.mem_of_isIntegral_loc m O _ hA
        (fun _ h => PositivityTheory.Xgn.SequenceRing.mem_of_isIntegral T hn hc h) ha⟩, rfl⟩
  exact ⟨ConstClosure.charZero_of_isArithVar hV, hN, hI, hF,
    fun q hq hO x hx => PositivityTheory.Xgn.SequenceRing.adjoin_le_regAt O q hq hO hx,
    fun 𝔮 h𝔮 => PositivityTheory.Xgn.SequenceRing.exists_point m O T hc hA 𝔮 h𝔮⟩
end

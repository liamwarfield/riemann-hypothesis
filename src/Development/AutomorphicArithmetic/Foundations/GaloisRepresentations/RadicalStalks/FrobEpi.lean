module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverFieldStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem pow_inj {R : Type*} [CommRing R] [_root_.IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (e : a ^ p = b ^ p) : a = b := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (a - b) b
  rw [sub_add_cancel, e, h] at hr
  have h0 : (a - b) ^ p = 0 := by
    simpa using hr.symm
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)

private theorem step {p : ℕ} {A B C : CommRingCat} (u : A ⟶ B) (v : A ⟶ C) (FB : B ⟶ B) (FC : C ⟶ C)
    (r : B ⟶ C) (hB : ∀ x, FB x = x ^ p) (hC : ∀ x, FC x = x ^ p)
    (hU : v ≫ FC = (u ≫ FB) ≫ r) (a : A) : (u ≫ r).hom a ^ p = v.hom a ^ p := by
  have ha := ConcreteCategory.congr_hom hU a
  simp only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha
  simpa using ha.symm

private theorem frob_epi (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X]
    (h : (p : Γ(X, ⊤)) = 0) : Epi (GlobalTheory.VB.frob X p h) := by
  have hV (V : X.Opens) : (p : Γ(X, V)) = 0 := by
    have := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h
    simpa using this
  refine ⟨fun {Y} f g e => ?_⟩
  have hx (x : X) : f x = g x := by
    have := congrArg (fun φ : X ⟶ Y => φ x) e
    simpa [GlobalTheory.VB.frob, GlobalTheory.SS.FrobField.absFrob,
      GlobalTheory.SS.FrobField.absPre] using this
  refine Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_
  have hU := Scheme.Hom.congr_app e.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hU
  ext a
  apply pow_inj (Fact.out : p.Prime) (hV _)
  exact step (p := p) (f.app U) (g.app U) ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U))
    ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _ (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a

theorem UpperTheory.Gal.Ord.epi :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0), Epi (GlobalTheory.VB.frob X p h) ∧ ∀ j, Epi (frobN p X h j) := by
  intro p _ X _ h
  have hF := frob_epi p X h
  refine ⟨hF, fun j => ?_⟩
  induction j with
  | zero => exact (inferInstance : Epi (𝟙 X))
  | succ j ih =>
    have : Epi (frobN p X h j) := ih
    exact epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RadicalStalk
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem radical_quot (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (m : Ideal R) [m.IsMaximal] : (m.map (algebraMap R B)).IsRadical := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : _root_.IsReduced ((R ⧸ m) ⊗[R] B) := GlobalTheory.T.isReduced_of_smooth_over_field' (R ⧸ m) _
  have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
  haveI : _root_.IsReduced (B ⧸ m.map (algebraMap R B)) :=
    isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr this

private theorem radical_loc (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (M : Submonoid B)
    [IsLocalization M A] (I : Ideal B) (hI : I.IsRadical) : (I.map (algebraMap B A)).IsRadical := by
  intro a ⟨n, hn⟩
  have hn' : a ^ (n + 1) ∈ I.map (algebraMap B A) := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hn
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq M a
  obtain ⟨⟨i, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hn'
  have hu : IsLocalization.mk' A b u * algebraMap B A u = algebraMap B A b := IsLocalization.mk'_spec A b u
  have e1 : algebraMap B A (b ^ (n + 1) * t) = algebraMap B A (i * u ^ (n + 1)) := by
    simp only [map_mul, map_pow]
    rw [← ht, ← hu]
    ring
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) e1
  have hy : (d : B) * t * b ∈ I := by
    apply hI
    refine ⟨n + 1, ?_⟩
    have e2 : ((d : B) * t * b) ^ (n + 1) = ((d : B) * t) ^ n * ((d : B) * (b ^ (n + 1) * t)) := by ring
    rw [e2, hd]
    exact I.mul_mem_left _ (I.mul_mem_left _ (I.mul_mem_right _ i.2))
  refine (IsLocalization.mem_map_algebraMap_iff M A).mpr
    ⟨⟨⟨_, hy⟩, u * d * t⟩, ?_⟩
  simp only [Submonoid.coe_mul, map_mul]
  rw [← hu]
  ring

private theorem radical_stalk (R : Type) [CommRing R] (m : Ideal R) [m.IsMaximal] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X) (r : CommRingCat.of R ⟶ X.presheaf.stalk z)
    (hr : Spec.map r = X.fromSpecStalk z ≫ s) : (m.map r.hom).IsRadical := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hsm : Smooth (hU.fromSpec ≫ s) := inferInstance
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hρs : ρ.hom.Smooth := by
    rw [← hρ] at hsm
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm
  have e : r = ρ ≫ X.presheaf.germ U z hzU := by
    apply Spec.map_injective
    rw [hr, Spec.map_comp, hρ, ← hU.fromSpecStalk_eq_fromSpecStalk hzU]
    simp [IsAffineOpen.fromSpecStalk]
  letI := ρ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, U) := hρs
  have h1 := radical_quot R Γ(X, U) m
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have h2 := radical_loc Γ(X, U) (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _ h1
  rw [Ideal.map_map] at h2
  rw [e]
  exact h2

private theorem kills_max (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X)
    (hmax : ∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z)
    (T : Type) [CommRing T] (φ : X.presheaf.stalk z ⟶ CommRingCat.of T) (c : R →+* T)
    (h : Spec.map φ ≫ X.fromSpecStalk z ≫ s = Spec.map (CommRingCat.ofHom c))
    (hc : ∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) :
    ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z), φ.hom x = 0 := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (X.fromSpecStalk z ≫ s)
  have hrc : r ≫ φ = CommRingCat.ofHom c := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr, h]
  have hrad := radical_stalk R (IsLocalRing.maximalIdeal R) X s z r hr
  have hprime : ∀ P : Ideal (X.presheaf.stalk z), P.IsPrime →
      (IsLocalRing.maximalIdeal R).map r.hom ≤ P → P = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    intro P hP hJ
    let y : Spec (X.presheaf.stalk z) := ⟨P, hP⟩
    have h1 : X.fromSpecStalk z y ⤳ z := by
      have : X.fromSpecStalk z y ∈ Set.range (X.fromSpecStalk z) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : s.base (X.fromSpecStalk z y) = IsLocalRing.closedPoint R := by
      have e : s.base (X.fromSpecStalk z y) = (Spec.map r).base y := by rw [hr]; rfl
      rw [e]
      apply PrimeSpectrum.ext
      have hle : IsLocalRing.maximalIdeal R ≤ P.comap r.hom := Ideal.map_le_iff_le_comap.mp hJ
      exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap r.hom).ne_top hle).symm
    have h3 := hmax _ h2 h1
    have h4 : y = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      (X.fromSpecStalk z).isEmbedding.injective (h3.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  intro x hx
  have hxJ : x ∈ (IsLocalRing.maximalIdeal R).map r.hom := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun {P} hP => ?_
    rw [hprime P hP.2 hP.1]
    exact hx
  have hker : (IsLocalRing.maximalIdeal R).map r.hom ≤ RingHom.ker φ.hom := by
    refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    have e : φ.hom (r.hom y) = c y := congrArg (fun f => f.hom y) hrc
    exact (RingHom.mem_ker).mpr (e.trans (hc y hy))
  exact hker hxJ

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.gen :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] (z : X), s.base z = IsLocalRing.closedPoint R →
      (∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (T : Type) [CommRing T] [IsLocalRing T] (v : Sp T ⟶ X) (c : R →+* T),
      v.base (IsLocalRing.closedPoint T) = z → v ≫ s = spMap c → (∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) →
      ∃ τ : X.residueField z →+* T, spMap τ ≫ X.fromSpecResidueField z = v := by
  intro R _ _ _ X s _ z _ hmax T _ _ v c hv hvs hc
  subst hv
  have hφ : Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) ≫ X.fromSpecStalk _ = v :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of T) v
  have hk := kills_max R X s _ hmax T (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) c
    (by rw [← Category.assoc, hφ]; exact hvs) hc
  refine ⟨Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk, ?_⟩
  have e : X.residue _ ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk) =
      Scheme.stalkClosedPointTo (R := CommRingCat.of T) v := by
    ext x
    rfl
  show Spec.map _ ≫ Spec.map (X.residue _) ≫ X.fromSpecStalk _ = v
  rw [← Spec.map_comp_assoc]
  exact (congrArg (fun g => Spec.map g ≫ X.fromSpecStalk _) e).trans hφ
end

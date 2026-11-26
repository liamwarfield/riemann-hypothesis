module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorus
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotient
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverSquareZeroLift
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompact
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationContinuous
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompare

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFinitePullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFinitePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem gramAt_continuous_anTop : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H :=
  @PositivityTheory.Xgn.torus_uniformization_continuous

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFinitePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_continuous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticPointsFiniteCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticPointsFiniteCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem compact_of_finite_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') :=
  @PositivityTheory.Xgn.torus_uniformization_compact

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticPointsFiniteCompactStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_points_finite_compact : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem torus_stratum_cocharacters_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  exact @PositivityTheory.Xgn.torus_uniformization_compare

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_split_pullback_generic : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveOnOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveOnOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StratLie

open GlobalTheory.CompanionTheory.Ar.TorusModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem killed_of_eq {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B : Type} [CommRing B] {b : Sp B ⟶ S}
    (h : KillsOver u Y b) {A : Type} [CommRing A] (g : B →+* A) {a : Sp A ⟶ S} (ha : a = spMap g ≫ b)
    (t : Over.mk a ⟶ splitTorus S X) (ht : ∀ y ∈ Y, charVal t y = 1) : t ≫ u = 1 := by
  subst ha
  exact h A g t ht

theorem killsOver_comp {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B C : Type} [CommRing B] [CommRing C]
    (c : B →+* C) {b : Sp B ⟶ S} (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  refine killed_of_eq h (g.comp c) ?_ t ht
  rw [← Category.assoc, spMap_comp_spMap]

theorem killsOver_descent [IsSeparated G.hom] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {κ k : Type}
    [Field κ] [Field k] (c : κ →+* k) {b : Sp κ ⟶ S} (h : KillsOver u Y (spMap c ≫ b)) : KillsOver u Y b := by
  intro A _ g t ht
  letI := g.toAlgebra
  letI := c.toAlgebra
  let i : A →+* (A ⊗[κ] k) := Algebra.TensorProduct.includeLeftRingHom
  let j : k →+* (A ⊗[κ] k) := (Algebra.TensorProduct.includeRight : k →ₐ[κ] (A ⊗[κ] k)).toRingHom
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeLeft_injective (R := κ) (S := κ) (A := A) (B := k) c.injective
  have hij : i.comp g = j.comp c := by
    ext a
    change (algebraMap κ A a) ⊗ₜ[κ] (1 : k) = (1 : A) ⊗ₜ[κ] (algebraMap κ k a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hw : spMap i ≫ spMap g ≫ b = spMap j ≫ spMap c ≫ b := by
    simp only [← Category.assoc, spMap_comp_spMap, hij]
  let φ : Over.mk (spMap j ≫ spMap c ≫ b) ⟶ Over.mk (spMap g ≫ b) := Over.homMk (spMap i) hw
  have h1 := h _ j (φ ≫ t) (fun y hy => by rw [charVal_comp i t (φ ≫ t) rfl, ht y hy, map_one])
  have h2 : φ ≫ (t ≫ u) = φ ≫ 1 :=
    (Category.assoc _ _ _).symm.trans (h1.trans (MonObj.comp_one φ).symm)
  have := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom i) hi
  refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap i) ?_)
  · rw [Over.w, Over.w]
  · exact congr($(h2).left)

theorem false_of_killsOver {u : splitTorus S X ⟶ G} {K : Type} [Field K] (b : Sp K ⟶ S) {l : ℕ} (hl : l.Prime)
    (ψ : X →+ ZMod l) (hψ : Function.Surjective ψ) (hk : KillsOver u ψ.ker b)
    (hinj : ∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
      t ≫ u = 1 → t = 1) : False := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ b)
    (MonoidHom.toHomUnits ((AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)))
  have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (ψ χ) 1 := ht
  have h1 := hk _ _ t fun y hy => by
    rw [ht', (AddMonoidHom.mem_ker).1 hy]; rfl
  have h2 := hinj _ _ t h1
  obtain ⟨χ, hχ⟩ := hψ 1
  have h3 := ht' χ
  rw [h2, charVal_one, AddMonoidAlgebra.one_def, hχ] at h3
  exact one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h3).symm

theorem killsOver_of_residue [IsSeparated G.hom] {u : splitTorus S X ⟶ G} [IsMonHom u] {Y : AddSubgroup X}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) : KillsOver u Y b := by
  refine GlobalTheory.T.killsOver_of_adic_completion S G X u Y R b fun n => ?_
  induction n with
  | zero =>
    let e : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)
    have he : e.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext a; rfl
    have := killsOver_comp e h
    rwa [← Category.assoc, spMap_comp_spMap, he] at this
  | succ n ih =>
    set m := IsLocalRing.maximalIdeal R with hm
    have hne : m ^ (n + 1 + 1) ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_eq_top_iff.1 htop |>.elim id (by simp))
    let q := Ideal.Quotient.mk (m ^ (n + 1 + 1))
    haveI : Nontrivial (R ⧸ m ^ (n + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ m ^ (n + 1 + 1)) := (m ^ (n + 1)).map q
    have hI : I ^ 2 = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ (spMap q ≫ b) I hI ?_
    let e : R ⧸ m ^ (n + 1) →+* (R ⧸ m ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp q) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    have he : e.comp (Ideal.Quotient.mk (m ^ (n + 1))) = (Ideal.Quotient.mk I).comp q := by
      ext a; rfl
    have := killsOver_comp e ih
    rw [← Category.assoc, spMap_comp_spMap, he, ← spMap_comp_spMap, Category.assoc] at this
    exact this

theorem lie_injective : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro Z _ _ G _ _ X _ _ u _ U hU hinj k _ x M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient Z G X u k x M hM δ hne hδ
  obtain ⟨z, f, hx⟩ : ∃ (z : Z) (f : Z.residueField z ⟶ CommRingCat.of k),
      x = Spec.map f ≫ Z.fromSpecResidueField z :=
    ⟨_, _, ((Scheme.SpecToEquivOfField k Z).symm_apply_apply x).symm⟩
  by_cases hz : z ∈ U
  · have hU' : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
      subst hx
      change (Z.fromSpecResidueField z) _ ∈ U
      rwa [Scheme.fromSpecResidueField_apply]
    exact false_of_killsOver x hl ψ hψ hk (hinj k x hU')
  have hgen : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hzg : z ≠ genericPoint Z := fun h => hz (h ▸ hgen)
  have hkκ : KillsOver u ψ.ker (Z.fromSpecResidueField z) :=
    killsOver_descent f.hom (hx ▸ hk)
  obtain ⟨V, hV, hA, hdom⟩ := GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof Z z hzg
  let jv : Z.presheaf.stalk z →+* V := (algebraMap (Z.presheaf.stalk z) Z.functionField).codRestrict V hA
  haveI : IsLocalHom jv := ⟨fun a ha => by
    by_contra hna
    exact ((hdom a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)) ha⟩
  let b : Sp V ⟶ Z := spMap jv ≫ Z.fromSpecStalk z
  let rm : IsLocalRing.ResidueField (Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V :=
    IsLocalRing.ResidueField.map jv
  have e1 : spMap rm ≫ Z.fromSpecResidueField z = spMap (IsLocalRing.residue V) ≫ b := by
    have e0 : spMap rm ≫ Spec.map (Z.residue z) = spMap (IsLocalRing.residue V) ≫ spMap jv := by
      rw [spMap_comp_spMap, ← IsLocalRing.ResidueField.map_comp_residue jv, ← spMap_comp_spMap]
      rfl
    simp only [b, Scheme.fromSpecResidueField]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.fromSpecStalk z) e0).trans (Category.assoc _ _ _))
  have kres : KillsOver u ψ.ker (spMap (IsLocalRing.residue V) ≫ b) := e1 ▸ killsOver_comp rm hkκ
  have kV := killsOver_of_residue b kres
  have kK := killsOver_comp V.subtype kV
  have hU'' : ⊤ ≤ (spMap V.subtype ≫ b) ⁻¹ᵁ U := by
    have e2 : spMap V.subtype ≫ b = Z.fromSpecStalk (genericPoint Z) := by
      simp only [b]
      rw [← Category.assoc, spMap_comp_spMap]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
    intro p _
    change (spMap V.subtype ≫ b) p ∈ U
    rw [e2]
    have hp : (Z.fromSpecStalk (genericPoint Z)) p ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hp
    exact Specializes.mem_open hp U.isOpen hgen
  exact false_of_killsOver _ hl ψ hψ kK (hinj _ _ hU'')

end GlobalTheory.CompanionTheory.Ar.StratLie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveOnOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_injective_on_open : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective | exact GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveLiftsPoints
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveLiftsPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem exists_lift_algClosure : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ :=
  PositivityTheory.Xgn.finite_surjective_point_lift

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveLiftsPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_surjective_lifts_points : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianSquareNormGram
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianSquareNormGram
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem sqAt_sum_eq_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re :=
  @PositivityTheory.Xgn.hermitian_norm_square_formula

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianSquareNormGramStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_square_norm_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleClosedIntegralSubscheme
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleClosedIntegralSubscheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem exists_integral_closed_subscheme : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x :=
  PositivityTheory.Xgn.exists_integral_closed_subscheme_of_irreducible

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleClosedIntegralSubschemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_closed_integral_subscheme : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegers
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem closure_finiteType_over_int : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) :=
  @PositivityTheory.Xgn.coordinate_map_finite_type

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_finite_type_over_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricTorusPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricTorusPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos

theorem core_gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).PosDef := by
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp

theorem cochar_indep {Xc : Type} [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (hβ : LinearIndependent ℤ β) :
    LinearIndependent ℂ (fun a => (Int.castAddHom ℂ).comp (β a)) := by
  let b := Module.Free.chooseBasis ℤ Xc
  let ev : (Xc →+ ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Xc → ℤ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have : f.toIntLinearMap = 0 := b.ext fun i => congrFun hf i
    ext x
    exact LinearMap.congr_fun this x
  have h1 : LinearIndependent ℤ (ev ∘ β) := hβ.map' ev hev
  have h2 : LinearIndependent ℂ (fun a => algebraMap ℤ ℂ ∘ (ev ∘ β) a) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  let evC : (Xc →+ ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ Xc → ℂ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp evC h2

theorem exists_diff {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    {R : Type} [CommRing R] {x : Sp R ⟶ S} {E F : Type} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : LieModel T x E) (N : LieModel G x F) : ∃ A : E →ₗ[R] F, ∀ e, N.pt (A e) = M.pt e ≫ u := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ u) := by
    intro e
    have h1 := (LieEx.isTanAt_iff x T _).1 (M.tan e)
    refine (LieEx.isTanAt_iff x G _).2 ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (h1 =≫ u).trans ?_
    exact MonObj.one_comp u
  choose A hA using fun e => N.onto _ (ht e)
  refine ⟨{ toFun := A, map_add' := fun e e' => N.inj ?_, map_smul' := fun c e => N.inj ?_ }, hA⟩
  · rw [N.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · apply Over.OverMorphism.ext
    rw [N.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem gramAt_posDef_of_diff_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  intro X Ω _ K J y ξ G _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β zc Mz _ hker v hv
  obtain ⟨V, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ (zc ≫ ρ)
  obtain ⟨A, hA⟩ := exists_diff u Mz (LiePull.modelPull hΦ zc MR)
  have hA' : ∀ δ, (MR.pt (A δ)).left = (Mz.pt δ ≫ u).left ≫ Φ := by
    intro δ
    rw [← hA, ← LiePull.pts_left hΦ (LiePull.eps_assoc zc)]
    exact congrArg (fun k => k.left) ((LiePull.tanPts hΦ zc).apply_symm_apply (MR.pt (A δ))).symm
  have hk : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro δ hδ
    apply hker
    rw [← hA, hδ]
    have := (LiePull.modelPull hΦ zc MR).add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hli := (cochar_indep β β.linearIndependent).map' A hk
  obtain ⟨core, hcore⟩ := h.herm (zc ≫ ρ) V MR
  have key := core_gram_posDef core _ hli
  have hv' : ∀ a, v a = MR.pt (A ((Int.castAddHom ℂ).comp (β a))) := fun a =>
    Over.OverMorphism.ext ((hv a).trans (hA' _).symm)
  have hm : RootHt.gramAt h (zc ≫ ρ) v = Matrix.of fun a b =>
      core.inner ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) a) ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) b) := by
    ext a c
    simp only [RootHt.gramAt, Matrix.of_apply, hcore, hv', Function.comp_apply]
  rw [hm]
  exact key

end GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricTorusPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_metric_torus_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieMetricHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem noeth_good {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] (Good : ℝ → T → Prop)
    (mono : ∀ C C' t, C ≤ C' → Good C t → Good C' t)
    (step : ∀ F : Set T, IsClosed F → IsIrreducible F → ∃ F' : Set T, IsClosed F' ∧ F' ⊂ F ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ F, t ∉ F' → Good C t) : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, Good C t := by
  have key : ∀ F : TopologicalSpace.Closeds T, ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ F, Good C t := by
    intro F
    induction F using WellFoundedLT.induction with
    | ind F ih =>
      by_cases hF : IsIrreducible (F : Set T)
      · obtain ⟨F', hc, hlt, C, hC, hg⟩ := step F F.isClosed hF
        obtain ⟨C', hC', hg'⟩ := ih ⟨F', hc⟩ (by
          exact lt_of_le_of_ne (fun x hx => hlt.1 hx) (fun e => hlt.2 (by rw [← e]; exact fun x hx => hx)))
        refine ⟨max C C', le_max_of_le_left hC, fun t ht => ?_⟩
        by_cases h' : t ∈ F'
        · exact mono _ _ _ (le_max_right _ _) (hg' t h')
        · exact mono _ _ _ (le_max_left _ _) (hg t ht h')
      · obtain ⟨S, hS, hirr, hsup⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible F
        have hlt : ∀ s ∈ S, s < F := fun s hs => by
          refine lt_of_le_of_ne (hsup ▸ le_sSup hs) (fun e => hF ?_)
          rw [← e]; exact hirr s hs
        choose! c hc hg using fun s (hs : s ∈ S) => ih s (hlt s hs)
        refine ⟨∑ s ∈ hS.toFinset, c s + 1, ?_, fun t ht => ?_⟩
        · have : 0 ≤ ∑ s ∈ hS.toFinset, c s :=
            Finset.sum_nonneg fun s hs => by linarith [hc s (hS.mem_toFinset.1 hs)]
          linarith
        · have ht' : t ∈ (sSup S : TopologicalSpace.Closeds T) := hsup ▸ ht
          have hsS : ∃ s ∈ S, t ∈ s := by
            have aux : ∀ A : Finset (TopologicalSpace.Closeds T), t ∈ A.sup id → ∃ s ∈ A, t ∈ s := by
              classical
              intro A
              induction A using Finset.induction_on with
              | empty =>
                intro h
                have h' : t ∈ ((⊥ : TopologicalSpace.Closeds T) : Set T) := h
                simp at h'
              | insert a A _ ih' =>
                intro h
                rw [Finset.sup_insert] at h
                have h' : t ∈ ((id a ⊔ A.sup id : TopologicalSpace.Closeds T) : Set T) := h
                rw [TopologicalSpace.Closeds.coe_sup] at h'
                rcases h' with h' | h'
                · exact ⟨a, Finset.mem_insert_self _ _, h'⟩
                · obtain ⟨s, hs, hts⟩ := ih' h'
                  exact ⟨s, Finset.mem_insert_of_mem hs, hts⟩
            have hfin : (sSup S : TopologicalSpace.Closeds T) = hS.toFinset.sup id := by
              rw [Finset.sup_id_eq_sSup, hS.coe_toFinset]
            rw [hfin] at ht'
            obtain ⟨s, hs, hts⟩ := aux _ ht'
            exact ⟨s, hS.mem_toFinset.1 hs, hts⟩
          obtain ⟨s, hs, hts⟩ := hsS
          refine mono _ _ _ ?_ (hg s hs t hts)
          have : c s ≤ ∑ s ∈ hS.toFinset, c s :=
            Finset.single_le_sum (f := c) (fun s hs => by linarith [hc s (hS.mem_toFinset.1 hs)]) (hS.mem_toFinset.2 hs)
          linarith
  obtain ⟨C, hC, h⟩ := key ⊤
  exact ⟨C, hC, fun t => h t trivial⟩

theorem isGrpPullback_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G'.left} (h : IsGrpPullback G' G f φ)
    (h' : IsGrpPullback G'' G' g ψ) : IsGrpPullback G'' G (g ≫ f) (ψ ≫ φ) := by
  refine ⟨h'.1.paste_horiz h.1, fun T x y x₀ y₀ hx hy => ?_⟩
  have key : ∀ (c : T.left ⟶ S) (_ : (T.hom ≫ g) ≫ f = c) (x₀ y₀ : Over.mk c ⟶ G), x₀.left = x.left ≫ ψ ≫ φ →
      y₀.left = y.left ≫ ψ ≫ φ → (x₀ * y₀).left = (x * y).left ≫ ψ ≫ φ := by
    rintro _ rfl x₀ y₀ hx hy
    let x₁ : Over.mk (T.hom ≫ g) ⟶ G' := Over.homMk (x.left ≫ ψ) (by
      have := h'.1.w
      simp only [Over.mk_hom, Category.assoc, this, Over.w_assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ g) ⟶ G' := Over.homMk (y.left ≫ ψ) (by
      have := h'.1.w
      simp only [Over.mk_hom, Category.assoc, this, Over.w_assoc, Over.w])
    have e₁ := h'.2 T x y x₁ y₁ rfl rfl
    have e₂ := h.2 (Over.mk (T.hom ≫ g)) x₁ y₁ x₀ y₀ (by simpa [x₁] using hx) (by simpa [y₁] using hy)
    rw [e₂, e₁]
    exact CategoryTheory.Category.assoc _ _ _
  exact key _ (Category.assoc _ _ _) x₀ y₀ hx hy

theorem dual_inl {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (a : A) :
    dualMap σ (algebraMap A (DualNumber A) a) = algebraMap B (DualNumber B) (σ a) := by
  show dualMap σ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (σ a)
  apply TrivSqZeroExt.ext <;> simp [dualMap]

def dualEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) : (B →+ ℤ) ≃ₗ[ℤ] (A →+ ℤ) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun g => g.comp e.toAddMonoidHom
      invFun := fun g => g.comp e.symm.toAddMonoidHom
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp
      map_add' := fun g g' => by ext x; simp }

theorem exists_dual_basis (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ (Xc →+ ℤ)) :=
  ⟨_, ⟨(Module.finBasis ℤ Xc).dualBasis.map (addMonoidHomLequivInt ℤ).symm⟩⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif


open scoped ComplexOrder in
theorem gram_bound (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (f : Z' ⟶ XQ X) (hf : IsFinite f) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left)
    (hP : IsGrpPullback G' G (f ≫ XQ.fst X) Φ)
    (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u]
    (hinj : ∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) (r : ℕ) (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (zc : Sp ℂ ⟶ Z') (zX : Sp ℂ ⟶ X) (_ : zc ≫ f ≫ XQ.fst X = zX)
      (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz → ∀ v : Fin r → (epsAt zX ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → ∀ w : Fin r → ℂ,
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ (star w ⬝ᵥ (RootHt.gramAt h zX v *ᵥ w)).re ∧
        (star w ⬝ᵥ (RootHt.gramAt h zX v *ᵥ w)).re ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  set ρ : Z' ⟶ X := f ≫ XQ.fst X with hρ
  have hM : ∀ zc : Sp ℂ ⟶ Z', ∃ Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ), IsCocharLie Mz :=
    fun zc => GlobalTheory.T.exists_cocharacter_lie_model Z' Xc ℂ zc
  choose Mz hMz using hM
  have hv : ∀ (zc : Sp ℂ ⟶ Z') (Mz' : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)) (a : Fin r),
      ∃ v : epsAt (zc ≫ ρ) ⟶ G, v.left = (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ := by
    intro zc Mz' a
    refine ⟨Over.homMk ((Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) ?_, rfl⟩
    have w1 : Φ ≫ G.hom = G'.hom ≫ ρ := hP.1.w
    have w2 := Over.w (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u)
    rw [CategoryTheory.Category.assoc, w1, reassoc_of% w2]
    simp [epsAt]
  choose vv hvv using fun zc => hv zc (Mz zc)
  let H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ := fun zc => RootHt.gramAt h (zc ≫ ρ) (vv zc)
  have hH : ∀ (zc : Sp ℂ ⟶ Z') (Mz' : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz' →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v := by
    intro zc Mz' hMz' v hv'
    have e : ∀ d, Mz'.pt d = (Mz zc).pt d := fun d =>
      (GlobalTheory.T.charVal_multiplicative Z' Xc (DualNumber ℂ) _).1 _ _ (fun χ => by rw [hMz', hMz])
    have : vv zc = v := by
      funext a
      apply Over.OverMorphism.ext
      rw [hvv, hv', e]
    simp only [H, this]
  have hcont := GlobalTheory.T.gram_matrix_continuous X Ω K J y ξ hall hT G Li M h Z' ρ G' Φ hP Xc u r (fun a => β a) H hH
  letI := anTop Z'
  haveI := GlobalTheory.T.analytic_points_finite_compact X Ω K J y ξ hall hT Z' f hf
  obtain ⟨C, hC, hb⟩ := GlobalTheory.CompanionTheory.GramCompact.exists_bounds (Sp ℂ ⟶ Z') Set.univ (Fin r) H isCompact_univ
    hcont.continuousOn (fun zc _ => GlobalTheory.T.lie_metric_torus_pullback X Ω K J y ξ G Li M h Z' ρ G' Φ hP Xc u r β zc (Mz zc) (hMz zc)
      (hinj zc _ (hMz zc)) (vv zc) (hvv zc))
  refine ⟨C, hC, fun zc zX hz Mz' hMz' v hv' w => ?_⟩
  subst hz
  rw [← hH zc Mz' hMz' v hv']
  exact hb zc trivial w

theorem xq_facts (X : Scheme.{0}) (h : LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X)) :
    LocallyOfFiniteType (XQ.snd X) ∧ QuasiCompact (XQ.snd X) ∧ IsLocallyNoetherian (XQ X) ∧
      TopologicalSpace.NoetherianSpace (XQ X) := by
  obtain ⟨h1, h2⟩ := h
  have a1 : LocallyOfFiniteType (XQ.snd X) := inferInstance
  have a2 : QuasiCompact (XQ.snd X) := inferInstance
  have a3 : IsLocallyNoetherian (XQ X) := LocallyOfFiniteType.isLocallyNoetherian (XQ.snd X)
  have a4 : CompactSpace (XQ X) := QuasiCompact.compactSpace_of_compactSpace (XQ.snd X)
  have a5 : IsNoetherian (XQ X) := {}
  exact ⟨a1, a2, a3, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped CategoryTheory.Obj

theorem stratum_good : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ XQ X), IsClosedImmersion i →
    ∃ (U : Z.Opens) (C : ℝ), (U : Set Z).Nonempty ∧ 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X)
      (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK),
      IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∀ zZ : Sp L ⟶ Z,
      zZ ≫ i = toXQ (spMap (algebraMap (𝓞 L) L) ≫ z) → ⊤ ≤ zZ ⁻¹ᵁ U → GoodAt h C z φ τ := by
  intro hFC X Ω _ K _ J _ y ξ hall hT G _ _ hG Li _ _ M h Z _ i hi
  have hfin := GlobalTheory.T.coords_finite_type_over_integers X Ω K J y ξ hall hT
  obtain ⟨hq1, hq2, hq3, hq4⟩ := xq_facts X hfin
  haveI := hG.smooth
  haveI := hG.separated
  let s : Z ⟶ Sp ℚ := i ≫ XQ.snd X
  haveI : LocallyOfFiniteType s := inferInstance
  haveI : QuasiCompact s := inferInstance
  let io : Z ⟶ X := i ≫ XQ.fst X
  have hGZ : IsSemiAbelian ((Over.pullback io).obj G) := IsSemiAbelian.pullback io G hG
  obtain ⟨Z', hZ', π, G', hG', φ', Xc, _, _, _, u, U, hπf, hπs, hnorm, hpb, hu, hU, hpt⟩ :=
    GlobalTheory.T.semiabelian_finite_cover_torus hFC Z s ((Over.pullback io).obj G) hGZ
  let f : Z' ⟶ XQ X := π ≫ i
  haveI hff : IsFinite f := inferInstance
  have hP : IsGrpPullback G' G (f ≫ XQ.fst X) (φ' ≫ pullback.fst G.hom io) := by
    have := isGrpPullback_comp (isGrpPullback_pullback G io) hpb
    simpa [f, io, CategoryTheory.Category.assoc] using this
  haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsSeparated G'.hom := by
    have h1 : IsSeparated ((Over.pullback io).obj G).hom := (IsSemiAbelian.separated (G := (Over.pullback io).obj G))
    exact MorphismProperty.of_isPullback (P := @IsSeparated) hpb.1 h1
  obtain ⟨r, ⟨β⟩⟩ := exists_dual_basis Xc
  have hU' : ((π ⁻¹ᵁ U : Z'.Opens) : Set Z').Nonempty := by
    obtain ⟨p, hp⟩ := hU
    obtain ⟨q, rfl⟩ := hπs.surj p
    exact ⟨q, hp⟩
  have hinj0 := GlobalTheory.T.torus_injective_on_open Z' G' Xc u (π ⁻¹ᵁ U) hU' (fun k _ x hx A _ g t ht => (hpt k x hx).1 A g t ht)
  obtain ⟨C, hC, hb⟩ := gram_bound X Ω K J y ξ hall hT G Li M h Z' f hff G' _ hP Xc u
    (fun zc Mz hMz δ hδ => hinj0 ℂ zc Mz hMz δ hδ) r β
  refine ⟨U, C, hU, hC, ?_⟩
  intro L _ _ z GK _ φ τ hGK zZ hzZ hzU
  letI := τ.addCommGroup
  let Lb := AlgebraicClosure L
  obtain ⟨x, hx⟩ := GlobalTheory.T.finite_surjective_lifts_points Z' Z π hπf hπs L zZ
  have hxρ : x ≫ f ≫ XQ.fst X = spMap (algebraMap L Lb) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) := by
    have e : zZ ≫ i ≫ XQ.fst X = spMap (algebraMap (𝓞 L) L) ≫ z := by
      rw [← CategoryTheory.Category.assoc, hzZ, toXQ_fst]
    simp only [f, CategoryTheory.Category.assoc]
    rw [reassoc_of% hx, e]
  have hxU : ⊤ ≤ (x ≫ π) ⁻¹ᵁ U := by
    rw [hx]
    intro p _
    have h1 : spMap (algebraMap L (AlgebraicClosure L)) p ∈ zZ ⁻¹ᵁ U := hzU (TopologicalSpace.Opens.mem_top _)
    simpa using h1
  obtain ⟨hi1, hi2⟩ := hpt Lb x hxU
  obtain ⟨e, he⟩ := GlobalTheory.T.torus_split_pullback_generic X Z' G G' (f ≫ XQ.fst X) _ hP Xc u L Lb x _ hxρ GK φ hGK τ hi1 hi2
  refine ⟨r, β.map (dualEquiv e), fun MT hMT B MB hF ε hε σ w => ?_⟩
  letI : Algebra L ℂ := σ.toAlgebra
  let σ' : Lb →+* ℂ := (IsAlgClosed.lift : Lb →ₐ[L] ℂ).toRingHom
  have hσ' : σ'.comp (algebraMap L Lb) = σ := by
    ext a
    exact (IsAlgClosed.lift : Lb →ₐ[L] ℂ).commutes a
  let zc : Sp ℂ ⟶ Z' := spMap σ' ≫ x
  let c : 𝓞 L →+* ℂ := σ.comp (algebraMap (𝓞 L) L)
  let zX : Sp ℂ ⟶ X := spMap c ≫ z
  have hzX : zc ≫ f ≫ XQ.fst X = zX := by
    have e1 : spMap σ' ≫ spMap (algebraMap L Lb) ≫ spMap (algebraMap (𝓞 L) L) = spMap c := by
      rw [LieTangent.spec_comp, LieTangent.spec_comp]
      simp only [c, ← RingHom.comp_assoc, hσ']
    show (spMap σ' ≫ x) ≫ f ≫ XQ.fst X = spMap c ≫ z
    rw [CategoryTheory.Category.assoc, hxρ, ← e1]
    simp only [CategoryTheory.Category.assoc]
  obtain ⟨Mz, hMz⟩ := GlobalTheory.T.exists_cocharacter_lie_model Z' Xc ℂ zc
  let v : Fin r → (epsAt zX ⟶ G) := fun a => LieTangent.epsBase c rfl ≫ MB.pt (ε a)
  have hv : ∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ (φ' ≫ pullback.fst G.hom io) := by
    intro a
    set δ' : τ.X →+ L := (Int.castAddHom L).comp ((β.map (dualEquiv e)) a) with hδ'
    let a0 : Sp (DualNumber L) ⟶ Sp L := (epsAt (𝟙 (Sp L))).hom
    let g1 : DualNumber L →+* DualNumber ℂ := dualMap σ
    let t' : Over.mk (spMap g1 ≫ a0) ⟶ splitTorus (Sp L) τ.X :=
      Over.homMk (spMap g1 ≫ (MT.pt δ').left) (by
        have := Over.w (MT.pt δ')
        simp only [Over.mk_hom, CategoryTheory.Category.assoc] at this ⊢
        rw [this]
        rfl)
    have hchar : ∀ χ, charVal t' χ = charVal (Mz.pt ((Int.castAddHom ℂ).comp (β a))) (e χ) := by
      intro χ
      have e1 := (GlobalTheory.T.charVal_multiplicative (Sp L) τ.X (DualNumber L) a0).2.2.2.2.2 (DualNumber ℂ) g1 (MT.pt δ') t' rfl χ
      rw [e1, hMT, hMz]
      simp only [g1, hδ']
      ext <;> simp [dualMap, dualEquiv]
    have e2 := he (DualNumber ℂ) ((algebraMap ℂ (DualNumber ℂ)).comp σ') (epsAt zc).hom (by
        show _ = Spec.map _ ≫ spMap σ' ≫ x
        rw [← CategoryTheory.Category.assoc, LieTangent.spec_comp]) (spMap g1 ≫ a0) (by
        show _ = spMap g1 ≫ Spec.map (CommRingCat.ofHom (algebraMap L (DualNumber L))) ≫ 𝟙 _
        rw [CategoryTheory.Category.comp_id, LieTangent.spec_comp]
        have e0 : ((algebraMap ℂ (DualNumber ℂ)).comp σ').comp (algebraMap L Lb) = g1.comp (algebraMap L (DualNumber L)) := by
          refine RingHom.ext fun a => ?_
          show algebraMap ℂ (DualNumber ℂ) (σ' (algebraMap L Lb a)) = dualMap σ (algebraMap L (DualNumber L) a)
          rw [dual_inl]
          exact congrArg (algebraMap ℂ (DualNumber ℂ)) (congrArg (fun q => q a) hσ')
        rw [e0]) (Mz.pt ((Int.castAddHom ℂ).comp (β a))) t' hchar
    refine Eq.trans ?_ e2.symm
    have e3 := hε a
    unfold LieModel.Lifts at e3
    have e4 : (v a).left = spMap (dualMap c) ≫ (MB.pt (ε a)).left :=
      (LieTangent.left_eq_iff _ _ _ _).2 rfl
    rw [e4]
    have e5 : spMap (dualMap c) = spMap g1 ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := by
      rw [LieTangent.spec_comp, ← RootHt.dualMap_comp]
    rw [e5, CategoryTheory.Category.assoc, ← e3, Over.comp_left]
    show _ = ((spMap g1 ≫ (MT.pt δ').left) ≫ τ.i.left) ≫ φ
    simp only [CategoryTheory.Category.assoc, Over.comp_left]
    rfl
  obtain ⟨hlo, hhi⟩ := hb zc zX hzX Mz hMz v hv w
  have hΓ : ∀ a b, RootHt.gramAt h zX v a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b) := by
    intro a b
    exact (hF σ (ε a) (ε b) (v a) (v b) rfl rfl).symm
  rw [GlobalTheory.T.hermitian_square_norm_gram L B σ r ε _ hΓ w]
  exact ⟨hlo, hhi⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped CategoryTheory.Obj

theorem goodAt_mono {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} (h : LieMetric M y) {C C' : ℝ} (hC : 1 ≤ C) (hCC : C ≤ C') {L : Type} [Field L] [NumberField L]
    {z : Sp (𝓞 L) ⟶ X} {GK : Over (Sp L)} [GrpObj GK] {φ : GK.left ⟶ G.left} {τ : TorusExtension GK}
    (hg : GoodAt h C z φ τ) : GoodAt h C' z φ τ := by
  letI := τ.addCommGroup
  obtain ⟨r, bs, hb⟩ := hg
  refine ⟨r, bs, fun MT hMT B MB hF ε hε σ w => ?_⟩
  obtain ⟨h1, h2⟩ := hb MT hMT B MB hF ε hε σ w
  have hS : 0 ≤ ∑ a, ‖w a‖ ^ 2 := by positivity
  have hC0 : 0 < C := by linarith
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC0 hCC) hS) h1, le_trans h2 (mul_le_mul_of_nonneg_right hCC hS)⟩

theorem torus_unif : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y), ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK), letI := τ.addCommGroup; IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier, (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) → ∀ (σ : L →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  intro hFC X Ω _ K _ J _ y ξ hc hall hT G _ _ hG Li _ _ M h
  obtain ⟨hq1, hq2, hq3, hq4⟩ := xq_facts X (GlobalTheory.T.coords_finite_type_over_integers X Ω K J y ξ hall hT)
  let Good : ℝ → XQ X → Prop := fun C t => 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X)
      (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK),
      IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ →
      toXQ (spMap (algebraMap (𝓞 L) L) ≫ z) (IsLocalRing.closedPoint L) = t → GoodAt h C z φ τ
  have key := noeth_good (T := XQ X) Good (fun C C' t hCC hg => ⟨hg.1.trans hCC, fun L _ _ z GK _ φ τ hP ht =>
    goodAt_mono h hg.1 hCC (hg.2 L z GK φ τ hP ht)⟩) ?_
  · obtain ⟨C, hC, hg⟩ := key
    exact ⟨C, hC, fun L _ _ z GK _ φ τ hP => (hg _).2 L z GK φ τ hP rfl⟩
  · intro F hF hFi
    obtain ⟨Z, hZ, i, hi, hr, hlift⟩ := GlobalTheory.T.irreducible_closed_integral_subscheme (XQ X) F hF hFi
    obtain ⟨U, C, hU, hC, hgood⟩ := stratum_good hFC X Ω K J y ξ hall hT G hG Li M h Z i hi
    refine ⟨i '' (U : Set Z)ᶜ, hi.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl, ?_, C, hC, fun t ht hnt => ?_⟩
    · have hsub : i '' (U : Set Z)ᶜ ⊆ F := by
        rintro _ ⟨p, -, rfl⟩
        exact hr ▸ Set.mem_range_self p
      refine ⟨hsub, fun hne => ?_⟩
      obtain ⟨p, hp⟩ := hU
      have hpF : i p ∈ F := hr ▸ Set.mem_range_self p
      obtain ⟨q, hq, hqp⟩ := hne hpF
      exact hq (hi.isClosedEmbedding.injective hqp ▸ hp)
    · refine ⟨hC, fun L _ _ z GK _ φ τ hP ht' => ?_⟩
      obtain ⟨x', hx'⟩ := hlift L (toXQ (spMap (algebraMap (𝓞 L) L) ≫ z)) (ht' ▸ ht)
      refine hgood L z GK φ τ hP x' hx' ?_
      intro p _
      have hpc : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
      subst hpc
      by_contra hn
      refine hnt ⟨x' (IsLocalRing.closedPoint L), hn, ?_⟩
      rw [← ht', ← hx']
      rfl

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieMetricHeightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_lie_metric_height : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y), ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK), letI := τ.addCommGroup; IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier, (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) → ∀ (σ : L →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif <;> assumption)
end

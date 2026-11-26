module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GluedLocalRegularizationsOnAtlas
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def cast {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F] [Module R F]
    (M : LieModel G x F) : LieModel G y F := h ▸ M

theorem cast_left {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F]
    [Module R F] (M : LieModel G x F) (e : F) : ((cast h M).pt e).left = (M.pt e).left := by
  subst h
  rfl

theorem exists_tr {A B : Type} [CommRing A] [CommRing B] (a : Sp A ⟶ X) (b : Sp B ⟶ X) (c : A →+* B)
    (h : spMap c ≫ a = b) {E E' : Type} [AddCommGroup E] [AddCommGroup E'] [Module A E] [Module B E']
    (M : LieModel G a E) (M' : LieModel G b E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A B c a E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  simpa [LieModel.Lifts] using this

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (dualMap d) ≫ spMap (dualMap c) = spMap (dualMap (d.comp c)) := by
  have : dualMap (d.comp c) = (dualMap d).comp (dualMap c) := by
    ext a <;> simp [dualMap]
  simp only [this, spMap, ← Spec.map_comp]
  rfl

theorem pt_left_inj {A : Type} [CommRing A] {a : Sp A ⟶ X} {E : Type} [AddCommGroup E] [Module A E]
    (M : LieModel G a E) {u v : E} (h : (M.pt u).left = (M.pt v).left) : u = v :=
  M.inj (Over.OverMorphism.ext h)

theorem exists_lift {R A : Type} [CommRing R] [CommRing A] [IsLocalRing A] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (z : Sp A ⟶ X) (h : z (IsLocalRing.closedPoint A) ∈ x.opensRange) : ∃ a : R →+* A, spMap a ≫ x = z := by
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨t, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of A) z h
    exact (this.ge (Set.mem_univ t) : t ∈ z ⁻¹ᵁ x.opensRange)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

variable [Smooth G.hom]

theorem basis_tr {R A : Type} [CommRing R] [CommRing A] (ψ : R →+* A) (x : Sp R ⟶ X) (y : Sp A ⟶ X)
    (hψ : spMap ψ ≫ x = y) {F Fy : Type} [AddCommGroup F] [Module R F] [AddCommGroup Fy] [Module A Fy]
    (MR : LieModel G x F) (My : LieModel G y Fy) {n : ℕ} (b : Module.Basis (Fin n) R F) :
    ∃ (β : F →ₛₗ[ψ] Fy) (B : Module.Basis (Fin n) A Fy), (∀ k, B k = β (b k)) ∧
      ∀ e, (My.pt (β e)).left = spMap (dualMap ψ) ≫ (MR.pt e).left := by
  obtain ⟨j, hj⟩ := exists_tr x y ψ hψ MR My
  letI : Algebra R A := ψ.toAlgebra
  letI : Module R Fy := Module.compHom Fy ψ
  haveI : IsScalarTower R A Fy :=
    ⟨fun s r e => by
      change (ψ s * r) • e = ψ s • r • e
      rw [mul_smul]⟩
  let j' : F →ₗ[R] Fy :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hbc : IsBaseChange A j' :=
    (GlobalTheory.T.lie_model_finite_base_change X G R x F MR).2.2 A Fy (cast hψ.symm My) j' fun e => by
      rw [cast_left]
      exact hj e
  refine ⟨j, (Algebra.TensorProduct.basis A b).map hbc.equiv, fun k => ?_, hj⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul]
  rfl

omit [Smooth G.hom] [GrpObj G] in
theorem mem_span_range {A Ω : Type} [CommRing A] [Field Ω] (g : A →+* Ω) {Fq E : Type} [AddCommGroup Fq]
    [Module A Fq] [AddCommGroup E] [Module Ω E] {n : ℕ} (B : Module.Basis (Fin n) A Fq) (j : Fq →ₛₗ[g] E)
    (y : Fq) : j y ∈ Submodule.span g.range (Set.range fun k => j (B k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr y, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [j.map_smulₛₗ]
  exact Submodule.smul_mem _ (⟨g (B.repr y k), _, rfl⟩ : g.range) (Submodule.subset_span ⟨k, rfl⟩)

variable [IsCommMonObj G]

theorem frame_of_basis {R : Type} [CommRing R] (x : Sp R ⟶ X) {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) {n : ℕ} (b : Module.Basis (Fin n) R F) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (φ : R →+* Ω) (hφ : spMap φ ≫ x = ξ) :
    ∃ c : Fin n → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = ⊤ ∧
      ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 →
        (genMap ξ q).comp ψ = φ → M.lat.IsFrameAt c q := by
  obtain ⟨j, B, hB, hj⟩ := basis_tr φ x ξ hφ MR M b
  have hc : (fun k => j (b k)) = B := funext fun k => (hB k).symm
  refine ⟨fun k => j (b k), ?_, ?_, fun q ψ hψ hg => ?_⟩
  · rw [hc]; exact B.linearIndependent
  · rw [hc]; exact B.span_eq
  refine ⟨by rw [hc]; exact B.linearIndependent, ?_⟩
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨β, Bq, hBq, hβ⟩ := basis_tr (A := X.presheaf.stalk q.1) ψ x (X.fromSpecStalk q.1) hψ MR Mq b
  obtain ⟨jq, hjq⟩ := exists_tr (A := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ξ (genMap ξ q)
    (spec_genMap ξ q) Mq M
  have hcomp : ∀ e, jq (β e) = j e := fun e => pt_left_inj M (by
    rw [hjq, hβ, ← Category.assoc, spMap_dual_comp, hg, hj])
  have hcq : (fun k => j (b k)) = fun k => jq (Bq k) := funext fun k => by rw [hBq, hcomp]
  refine le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
    obtain ⟨y, rfl⟩ := Mq.onto v hv.1
    have hy : e = jq y := pt_left_inj M (hv.2.trans (hjq y).symm)
    rw [hy, hcq]
    exact mem_span_range (genMap ξ q) Bq jq y
  · rintro _ ⟨k, rfl⟩
    exact (M.mem_lat_iff q _).2 ⟨Mq.pt (β (b k)), Mq.tan _, by
      change (M.pt (j (b k))).left = _
      rw [← hcomp]
      exact hjq _⟩

theorem exists_chart (G : Over X) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (y : X) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F)
      (_ : Module R F) (_ : LieModel G x F) (n : ℕ) (_ : Module.Basis (Fin n) R F), y ∈ x.opensRange := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let R₀ : Type := Γ(X, U)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨F₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R₀ x₀
  obtain ⟨hfin, hproj, hbc⟩ := GlobalTheory.T.lie_model_finite_base_change X G R₀ x₀ F₀ M₀
  let P : PrimeSpectrum R₀ := hU.primeIdealOf ⟨y, hy⟩
  have hP : x₀ P = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  haveI : Module.FinitePresentation R₀ F₀ := Module.finitePresentation_of_projective R₀ F₀
  haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl F₀) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    P.asIdeal.primeCompl (LocalizedModule.mkLinearMap P.asIdeal.primeCompl F₀) (Localization.AtPrime P.asIdeal)
  let R : Type := Localization.Away f
  let x : Sp R ⟶ X := spMap (algebraMap R₀ R) ≫ x₀
  have hopen : IsOpenImmersion (spMap (algebraMap R₀ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Localization.Away f)))))
  have hx : IsOpenImmersion x := inferInstance
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G R x
  obtain ⟨β, hβ⟩ := exists_tr x₀ x (algebraMap R₀ R) rfl M₀ MF
  letI : Module R₀ F := Module.compHom F (algebraMap R₀ R)
  haveI : IsScalarTower R₀ R F :=
    ⟨fun s r e => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  let β' : F₀ →ₗ[R₀] F :=
    { toFun := β
      map_add' := β.map_add
      map_smul' := fun r e => β.map_smulₛₗ r e }
  have hb : IsBaseChange R β' := hbc R F MF β' hβ
  haveI : IsLocalizedModule (Submonoid.powers f) β' :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) R β').2 hb
  have e : LocalizedModule (Submonoid.powers f) F₀ ≃ₗ[R] F :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) F₀) β').extendScalarsOfIsLocalization
      (Submonoid.powers f) R
  haveI : Module.Free R F := Module.Free.of_equiv e
  haveI : Module.Finite R F := (GlobalTheory.T.lie_model_finite_base_change X G R x F MF).1
  have hmem : P ∈ Set.range (spMap (algebraMap R₀ R)) := by
    have := PrimeSpectrum.localization_away_comap_range R f
    have h2 : P ∈ PrimeSpectrum.basicOpen f := hf
    rw [← SetLike.mem_coe, ← this] at h2
    exact h2
  obtain ⟨t, ht⟩ := hmem
  haveI : Nontrivial R := PrimeSpectrum.nontrivial t
  refine ⟨R, inferInstance, x, hx, F, inferInstance, inferInstance, MF, _, Module.finBasis R F, ?_⟩
  refine ⟨t, ?_⟩
  change (spMap (algebraMap R₀ R) ≫ x₀) t = y
  rw [Scheme.Hom.comp_apply, ht, hP]

end GlobalTheory.CompanionTheory.Ar.LieVB

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB in
theorem lieLat_isVB_of_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), IsCptGen ξ → Smooth G.hom → M.lat.IsVB (Module.finrank Ω Li) ⊤ ∧ M.omLat.IsVB (Module.finrank Ω Li) ⊤ := by
  intro X Ω _ ξ G _ _ Li _ _ M _ hs
  haveI := hs
  have hvb : M.lat.IsVB (Module.finrank Ω Li) ⊤ := by
    intro p _
    obtain ⟨R, _, x, hx, F, _, _, MR, n, b, hp⟩ := exists_chart G p.1
    have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω Li := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge), Fintype.card_fin]
    subst hn
    refine ⟨x.opensRange, hp, c, hsp, fun q _ hq => ?_⟩
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  exact ⟨hvb, (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat Set.univ _ hvb).1⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_omega_lattice_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), IsCptGen ξ → Smooth G.hom → M.lat.IsVB (Module.finrank Ω Li) ⊤ ∧ M.omLat.IsVB (Module.finrank Ω Li) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_isVB_of_smooth | exact GlobalTheory.CompanionTheory.Ar.lieLat_isVB_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_isVB_of_smooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (GlobalTheory.T.lie_model_finite_base_change S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  change _ ≫ _ = _ ≫ _ at h
  rw [Category.comp_id] at h
  exact h

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange | exact GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem not_inFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) {r : ℕ} (hr : r.Prime) :
    ¬ InFibre ξ r ⟨centre z, h⟩ := by
  intro hf
  apply hf
  have hs : genMap ξ ⟨centre z, h⟩ (r : X.presheaf.stalk (centre z)) = (r : Ω) := map_natCast _ r
  have hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
  have hu : IsUnit (r : X.presheaf.stalk (centre z)) := CxVal.isUnit _ (by
    rw [hz]; exact_mod_cast hr.ne_zero)
  refine ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hs⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).val, ?_⟩
  rw [map_units_inv, hu', hs]

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

theorem sabMap_cast_φ {S₁ S₂ : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f f' : S₁ ⟶ S₂} (e : f = f')
    (m : SABMap t₁ t₂ f) : (e ▸ m : SABMap t₁ t₂ f').φ = m.φ := by
  subst e
  rfl

theorem exists_sabMap (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f) :
    ∃ m : SABMap 𝔐.t 𝔐₀.t h, 𝔐.m.φ = m.φ ≫ 𝔐₀.m.φ := by
  obtain ⟨m, e⟩ := sabCancel pullCubCancel E H _ _ _ Y.t 𝔐₀.t 𝔐.t 𝔐₀.f h 𝔐₀.m (hf ▸ 𝔐.m)
  exact ⟨m, by rw [← e, sabMap_cast_φ]⟩

theorem mem_abLocus_iff (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f)
    (x : 𝔐.X) : x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus 𝔐₀.t.G := by
  obtain ⟨m, -⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  have hp : IsPullback m.φ 𝔐.t.G.hom 𝔐₀.t.G.hom h := m.cart.1
  exact (abLocus_pullback abLocusOne 𝔐₀.t.semi hp x).symm

end Cover

section Maps

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem finrank_comp' {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C) :
    (letI := (g.comp f).toAlgebra; Module.finrank A C) =
      (letI := f.toAlgebra; Module.finrank A B) * (letI := g.toAlgebra; Module.finrank B C) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank A B C).symm

theorem coordsAt_orbit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w w' : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (ho : SameOrbit w' w) : CoordsAt ξ y z w' := by
  obtain ⟨c, hc, rfl⟩ := ho
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := hw.1 k
    exact ⟨a, IsUnit.mk0 _ (mul_ne_zero (hc k) ha.ne_zero)⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := IsUnit.mk0 _ fun h0 => ha.ne_zero (by simp [h0])
    obtain ⟨h1, h2⟩ := hw.2 k a ha'
    refine ⟨h1, fun b => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 b
    exact ⟨r, hr, by simp only [e]; ring⟩

end Maps

section Orbit

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_sub_orbit {A B : HermLine J} (hab : A.a = B.a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) - Real.log (B.h w) = Real.log (A.h z) - Real.log (B.h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [log_h_smul A hc hz, log_h_smul B hc hz, hab]
  ring

theorem log_sum_orbit {X : Type} (s : Finset X) {A : HermLine J} {B : X → HermLine J}
    (hab : A.a = -∑ x ∈ s, (B x).a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ x ∈ s, Real.log ((B x).h w) = Real.log (A.h z) + ∑ x ∈ s, Real.log ((B x).h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  simp only [log_h_smul _ hc hz, Finset.sum_add_distrib]
  have : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ = -∑ x ∈ s, ∑ k, ((B x).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hab, ← Finset.sum_mul, ← neg_mul]
    simp [Finset.sum_apply]
  rw [this]
  ring

theorem pullDeg_neg_sum {K₀ : Type} {X : Type} {κ : K₀ → K} (hκ : Function.Injective κ) (s : Finset X) (f : X → K₀ → ℤ) :
    pullDeg κ (-∑ x ∈ s, f x) = -∑ x ∈ s, pullDeg κ (f x) := by
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    simp [pullDeg, hκ.extend_apply, Finset.sum_apply]
  · simp [pullDeg, Function.extend_apply' _ _ _ hk, Finset.sum_apply]

theorem log_tensor_pull {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {κ : K₀ → K}
    {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (A : HermLine J₀) (T : HermLine J) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((pullHerm hv A).tensor T).h z) = Real.log (A.h fun p => z (v p)) + Real.log (T.h z) :=
  Real.log_mul ((pullHerm hv A).pos z hz).ne' (T.pos z hz).ne'

end Orbit

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) :=
  PositivityTheory.HtPt.Htat.lie_bc

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_base_change_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_baseChange | exact GlobalTheory.CompanionTheory.Ar.lieModel_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finite_projective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E :=
  PositivityTheory.HtPt.Htat.lie_fin

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_finite_projective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective | exact GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem labels_all_once : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H)
    (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧
      Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c
  classical
  have hre : H.rt0.re = 0 := by
    have h : (H.rt0 * H.rt0).re = (-(H.d : ℂ)).re := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h
    have h' : (H.rt0 * H.rt0).im = (-(H.d : ℂ)).im := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h'
    have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
    have h1 : H.rt0.re * H.rt0.im = 0 := by linarith
    have h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0 := by nlinarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact mul_self_eq_zero.1 h3
    · nlinarith [mul_self_nonneg H.rt0.re]
  have hconj0 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h0
    have h := H.sqrt_neg_disc_sq
    rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h
    exact H.d_prime.ne_zero h
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    apply hne
    have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · exact h3
  have hsq : ∀ τ : E →+* ℂ, (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    intro τ
    have e1 := congrArg (fun x : 𝓞 E => τ (algebraMap (𝓞 E) E x)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at e1
    rw [H.sqrt_neg_disc_sq]
    exact e1
  have hpm : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 :=
    fun τ => sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ)
  have hcc : ∀ τ : E →+* ℂ, τ (IsCMField.complexConj E (H.rt : E)) = -τ (H.rt : E) := by
    intro τ
    rw [IsCMField.complexEmbedding_complexConj]
    rcases hpm τ with h | h
    · rw [h, hconj0]
    · rw [h, map_neg, hconj0]
  refine ⟨?_, ?_⟩
  · have k1 : ∀ (τ : CMType H) (x : 𝓞 E), ((labelEmb c (Sum.inl τ) x : ℂ)) = τ.1 (x : E) :=
      fun _ _ => rfl
    have k2 : ∀ (τ : CMType H) (x : 𝓞 E),
        ((labelEmb c (Sum.inr τ) x : ℂ)) = τ.1 ((H.bar x : 𝓞 E) : E) := fun _ _ => rfl
    have ext' : ∀ τ τ' : E →+* ℂ, (∀ x : 𝓞 E, τ (x : E) = τ' (x : E)) → τ = τ' := by
      intro τ τ' h
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
    rintro (τ | τ) (τ' | τ') h
    · refine congrArg Sum.inl (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h x)
      rwa [k1, k1] at e
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k1, k2, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e.symm
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k2, k1, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e
    · refine congrArg Sum.inr (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h (H.bar.symm x))
      rwa [k2, k2, RingEquiv.apply_symm_apply] at e
  · let e : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq, τ.2, hconj0]
            exact hneg⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq]
            rcases hpm τ.1 with h | h
            · exact absurd h τ.2
            · rw [h, map_neg, hconj0, neg_neg]⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq])
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq]) }
    have hc : Nat.card (CMType H ⊕ CMType H) = Nat.card (E →+* ℂ) :=
      Nat.card_congr ((Equiv.sumCongr (Equiv.refl _) e).trans (Equiv.sumCompl _))
    rw [hc, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ]

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_embedding_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧ Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.labels_all_once | exact GlobalTheory.CompanionTheory.Ar.labels_all_once | (intros; apply GlobalTheory.CompanionTheory.Ar.labels_all_once <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusLie

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {R : Type} [CommRing R]

def pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S} {a' : Sp A' ⟶ S}
    (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) : Over.mk a' ⟶ splitTorus S X :=
  Over.homMk (spMap g ≫ t.left) (by
    have h1 := Over.w t
    simp only [Over.mk_hom] at h1 ⊢
    rw [Category.assoc, h1, h])

theorem charVal_pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S}
    {a' : Sp A' ⟶ S} (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (pullPt g h t) χ = g (charVal t χ) := by
  subst h
  exact (GlobalTheory.T.charVal_multiplicative S X A _).2.2.2.2.2 A' g t _ rfl χ

def wOf (δ : X →+ R) : Multiplicative X →* DualNumber R where
  toFun χ := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]

abbrev evZ (R : Type) [CommRing R] : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

theorem base_ev (x : Sp R ⟶ S) :
    x = spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (evZ R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]; simp
  rw [← Category.assoc, this, Category.id_comp]

theorem isTanAt_iff (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) :
    IsTanAt (splitTorus S X) x v ↔ ∀ χ, (charVal v χ).fst = 1 := by
  have hT := GlobalTheory.T.charVal_multiplicative S X
  constructor
  · intro hv χ
    have e : pullPt (evZ R) (base_ev x) v = 1 := Over.OverMorphism.ext hv
    have := charVal_pullPt (evZ R) (base_ev x) v χ
    rw [e, (hT R x).2.2.1 χ] at this
    exact this.symm
  · intro hv
    have e : pullPt (evZ R) (base_ev x) v = 1 := by
      refine (hT R x).1 _ _ fun χ => ?_
      rw [charVal_pullPt, (hT R x).2.2.1 χ]
      exact hv χ
    exact congrArg (fun t => t.left) e

def ptOf (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose

theorem charVal_ptOf (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (ptOf x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose_spec χ

theorem ptOf_ext (x : Sp R ⟶ S) (v v' : epsAt x ⟶ splitTorus S X) (h : ∀ χ, charVal v χ = charVal v' χ) : v = v' :=
  (GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).1 v v' h

theorem epsMul_comp_base (c : R) (x : Sp R ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
      spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
      ext r <;> simp [epsMul]
    rw [this]
  rw [← Category.assoc, this]

def deltaOf (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) (hv : ∀ χ, (charVal v χ).fst = 1) : X →+ R :=
  AddMonoidHom.mk' (fun χ => (charVal v χ).snd) (fun χ χ' => by
    have := ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.2.2.1 v).2 χ χ'
    simp [this, TrivSqZeroExt.snd_mul, hv, add_comm])

theorem exists_lieModel_splitTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R]
    (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  intro S X _ R _ x
  refine ⟨{ pt := ptOf x, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun δ χ => charVal_ptOf x δ χ⟩
  · intro δ
    refine (isTanAt_iff x _).2 fun χ => ?_
    rw [charVal_ptOf]; simp
  · intro δ δ' h
    ext χ
    have := congrArg TrivSqZeroExt.snd
      ((charVal_ptOf x δ χ).symm.trans ((congrArg (fun t => charVal t χ) h).trans (charVal_ptOf x δ' χ)))
    simpa using this
  · intro v hv
    have hv' := (isTanAt_iff x v).1 hv
    refine ⟨deltaOf x v hv', ptOf_ext x _ _ fun χ => ?_⟩
    rw [charVal_ptOf]
    ext
    · simp [hv']
    · simp [deltaOf]
  · intro δ δ'
    refine ptOf_ext x _ _ fun χ => ?_
    rw [(GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.1, charVal_ptOf, charVal_ptOf, charVal_ptOf]
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]
  · intro c δ
    have e : ptOf x (c • δ) = pullPt (epsMul c) (epsMul_comp_base c x) (ptOf x δ) := by
      refine ptOf_ext x _ _ fun χ => ?_
      rw [charVal_pullPt, charVal_ptOf, charVal_ptOf]
      ext <;> simp [epsMul, mul_comm]
    exact congrArg (fun t => t.left) e

end GlobalTheory.CompanionTheory.Ar.TorusLie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocharacter_lie_model : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R] (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus | exact GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem eq_of_germ_comp {R : Type} [CommRing R] [IsLocalRing R] {z z' : Spec (CommRingCat.of R) ⟶ X}
    {U : X.Opens} (hU : IsAffineOpen U) (h : z (IsLocalRing.closedPoint R) ∈ U)
    (h' : z' (IsLocalRing.closedPoint R) ∈ U)
    (e : X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo z =
      X.presheaf.germ U _ h' ≫ Scheme.stalkClosedPointTo z') : z = z' := by
  have key : ∀ (t : Spec (CommRingCat.of R) ⟶ X) (ht : t (IsLocalRing.closedPoint R) ∈ U),
      t = Spec.map (X.presheaf.germ U _ ht ≫ Scheme.stalkClosedPointTo t) ≫ hU.fromSpec := by
    intro t ht
    rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk ht]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t).symm
  rw [key z h, key z' h', e]

theorem val_int {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) {A : Type} (s : Finset A) (f : A → Ω) (g : A → R)
    (h : ∀ i ∈ s, ValAt ξ z (f i) (g i)) : ValAt ξ z (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.ArchB.val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact RootHt.ArchB.val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique


open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique in
theorem GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  intro X Ω _ ξ K _ J y T _ hall z z' w hz hz'
  have hξ := T.gen
  have h := hall (centre z)
  have h' := hall (centre z')
  choose c hc using hz.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have in1 := RootHt.ArchB.in_chart (c := c) h hz hc0
  have in2 := RootHt.ArchB.in_chart (c := c) h' hz' hc0
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T in1 in2
  have hxc : x c ≠ 0 := in1.1
  obtain ⟨U, hU, hUm⟩ := T.affine c hxc
  have hzU : centre z ∈ U := (hUm _).2 ⟨h, in1⟩
  have hzU' : centre z' ∈ U := (hUm _).2 ⟨h', in2⟩

  have hval : ∀ (t : Spec (CommRingCat.of ℂ) ⟶ X), CoordsAt ξ y t w → ∀ (k : K) (i : J k),
      ValAt ξ t (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := by
    intro t ht k i
    obtain ⟨-, h2⟩ := ht.2 k (c k) (hc k)
    obtain ⟨r, hr, e⟩ := h2 i
    rw [e, mul_div_assoc, div_self (hc0 k), _root_.mul_one]
    exact hr
  have hrat : ∀ j : (k : K) → J k, x j / x c = ∏ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ := fun j => by
    rw [hx]
    exact (Finset.prod_div_distrib _ _).symm
  have key : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ r : ℂ, ValAt ξ z a r ∧ ValAt ξ z' a r := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      refine ⟨∏ k, w ⟨k, j k⟩ / w ⟨k, c k⟩, ?_, ?_⟩
      · simp only [hrat]
        exact val_prod h _ _ _ fun k _ => hval z hz k (j k)
      · simp only [hrat]
        exact val_prod h' _ _ _ fun k _ => hval z' hz' k (j k)
    | algebraMap n =>
      refine ⟨(n : ℂ), ?_, ?_⟩
      · simpa using val_int h n
      · simpa using val_int h' n
    | add a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r + s, RootHt.ArchB.val_add h1 h3, RootHt.ArchB.val_add h2 h4⟩
    | mul a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r * s, RootHt.ArchB.val_mul h1 h3, RootHt.ArchB.val_mul h2 h4⟩
  refine eq_of_germ_comp hU hzU hzU' ?_
  ext s
  have hgm : ∀ (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U),
      genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) :=
    fun p q hp hq => GlobalTheory.CompanionTheory.Ar.genMap_germ_eq_genMap_germ ξ U p q hp hq s
  have ha : genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    refine (T.ring c hxc _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hUm _).2 ⟨p.2, hp⟩
    rw [hgm ⟨centre z, h⟩ p hzU hpU]
    exact ⟨_, rfl⟩
  obtain ⟨r, h1, h2⟩ := key _ ha
  have e1 : ValAt ξ z (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hzU s)) := ⟨h, _, rfl, rfl⟩
  have e2 : ValAt ξ z' (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z').hom (X.presheaf.germ U (centre z') hzU' s)) :=
    ⟨h', _, (hgm ⟨centre z', h'⟩ ⟨centre z, h⟩ hzU' hzU), rfl⟩
  exact (RootHt.ArchB.val_unique hξ e1 h1).trans (RootHt.ArchB.val_unique hξ h2 e2)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_scheme_coords_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartFieldChange

theorem exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨P', mK, mB, h₁, h₂, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange E H S t L L' z P e
  exact ⟨P', mK, mB, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.AbPartFieldChange
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | exact GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange <;> assumption)
end
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalPshRegularizationLogBound
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

lemma mollifier_bdd {D : ℕ} (ρ : ReciprocityTheory.AnForm.A.Mollifier D) : ∃ b : ℝ, ∀ w, ρ.toFun w ≤ b := by
  have hcs : HasCompactSupport ρ.toFun := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin D → ℂ) 1) ?_
    exact ρ.support_subset.trans ball_subset_closedBall
  obtain ⟨b, hb⟩ := ρ.contDiff.continuous.bounded_above_of_compact_support hcs
  exact ⟨b, fun w => (le_abs_self _).trans (hb w)⟩

lemma polyMax_le_pmoff_same {D : ℕ} {S : Finset (Fin D)} {u w : (Fin D → ℂ) → ℝ} {R B κ : ℝ}
    (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ B)
    (hW1 : ReciprocityTheory.AnForm.A.IsPsh (ball 0 R) w)
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0,
      ∃ y ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s R' : ℝ} (hs : 0 < s) (hsR : s < R') (hR' : closedBall z R' ⊆ ball 0 R) :
    ReciprocityTheory.AnForm.A.polyMax w z s ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
  have hR'0 : 0 < R' := hs.trans hsR
  have hconv := (ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm D (ball 0 R) w z R' isOpen_ball hW1 hR'0 hR').1
  set g : ℝ → ℝ := fun σ => ReciprocityTheory.AnForm.A.polyMax w z (Real.exp σ) with hg
  have hconv' : ConvexOn ℝ (Set.Iio (Real.log R')) g :=
    hconv.subset Set.Iio_subset_Iic_self (convex_Iio _)
  have hcont : ContinuousOn g (Set.Iio (Real.log R')) := hconv'.continuousOn isOpen_Iio
  have hlog : Real.log s < Real.log R' := Real.log_lt_log hs hsR
  have hca : ContinuousAt g (Real.log s) := hcont.continuousAt (Iio_mem_nhds hlog)
  have hsub : closedBall z s ⊆ ball 0 R := (closedBall_subset_closedBall hsR.le).trans hR'
  have hle : ∀ σ ∈ Set.Iio (Real.log s), g σ ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
    intro σ hσ
    have hlt : Real.exp σ < s := by
      have := Real.exp_lt_exp.2 (Set.mem_Iio.1 hσ)
      rwa [Real.exp_log hs] at this
    exact RegularChartScaling.polyMax_le_pmo hub hW3 (Real.exp_pos σ).le hlt hsub
  have hfin : g (Real.log s) ≤ max (RegularChartScaling.pmoff S u z s) (-κ) :=
    le_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.log s))))
      (by filter_upwards [self_mem_nhdsWithin] with σ hσ using hle σ hσ)
  simpa only [hg, Real.exp_log hs] using hfin

theorem molli_trunc_near_polyMax :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D), ContinuousOn u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) u → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) → ∃ (C t₀ : ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ t₀ ≤ 1 / 8 ∧ ∀ t, 0 < t → t ≤ t₀ → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, w t z = max (u z) (-C * Real.log (Real.log (1 / t)))) ∧ ContDiffOn ℝ ∞ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (ReciprocityTheory.AnForm.A.molli ρ t (w t)) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, u z ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z) ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z t ∧ polyMaxOff S u z t - epsT C t ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ∧ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ≤ polyMaxOff S u z t := by
  intro D S m u C₅ ρ hc hp hb
  have hC₅ : 0 ≤ C₅ := RegularChartScaling.fifth_volume_constant_nonneg m (by norm_num) (by norm_num) hb
  have hub : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ C₅ :=
    fun x hx => (hb x hx).2
  obtain ⟨C₀, ℓ₀, hC₀, hosc⟩ := RegularChartScaling.oscGen m (R := 3 / 2) (by norm_num) (by norm_num)
    hc hp hb (C₁ := 2) (by norm_num)
  obtain ⟨b, hbρ⟩ := mollifier_bdd ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hbρ 0)
  set K : ℝ := Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b with hK
  have hK0 : 0 ≤ K := by positivity
  set C : ℝ := C₀ * (K + 1) with hC
  have hCC₀ : C₀ ≤ C := by rw [hC]; nlinarith
  have hKC : K * C₀ ≤ C := by rw [hC]; nlinarith
  have hC1 : 1 ≤ C := hC₀.trans hCC₀
  refine ⟨C, min (min (Real.exp (-ℓ₀)) (Real.exp (-Real.exp 1))) (1 / 8),
    fun t => RegularChartScaling.extT S (3 / 2) u (C * Real.log (Real.log (1 / t))), hC1,
    lt_min (lt_min (Real.exp_pos _) (Real.exp_pos _)) (by norm_num),
    (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _, fun t ht htt => ?_⟩
  beta_reduce
  have ht₁ : t ≤ Real.exp (-ℓ₀) := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hℓ₀ : ℓ₀ ≤ Real.log (1 / t) := by
    have h1 : Real.log t ≤ -ℓ₀ := by
      have := Real.log_le_log ht ht₁
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]; linarith
  obtain ⟨he, hCt, hz⟩ := hosc t ht hℓ₀
  set ℓ := Real.log (1 / t) with hℓ
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le he
  set κ : ℝ := C * Real.log ℓ with hκ
  obtain ⟨w, hwe, hW1, hW2, hW3⟩ := RegularChartScaling.ext_exists S (R := 3 / 2) (by norm_num) hC₅ hc hp hub κ
  rw [← hwe]
  have hwu : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ w x :=
    fun x hx => by rw [hW2 x hx]; exact le_max_left _ _
  have ht2 : 2 * t ≤ 1 / 8 := by linarith
  obtain ⟨-, hsm, hps, hbd⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ w isOpen_ball hW1).1 t ht
  have hsh : ball (0 : Fin D → ℂ) (5 / 4) ⊆ ReciprocityTheory.AnForm.A.shrink (ball (0 : Fin D → ℂ) (3 / 2)) t :=
    fun z hz' => RegularChartScaling.closedBall_sub_of hz' (by linarith)
  have hsm' := hsm.mono hsh
  refine ⟨fun z hz' => by rw [neg_mul]; exact hW2 z hz', hsm', ?_, ?_, ?_⟩
  · exact (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ isOpen_ball
      (hsm'.of_le (by norm_cast))).1 (RegularChartScaling.isPsh_mono hps hsh)
  · intro z hz'
    have hzB : z ∈ ball (0 : Fin D → ℂ) (3 / 2) :=
      ball_subset_ball (by norm_num) hz'.1
    exact (hwu z ⟨hzB, hz'.2⟩).trans (hbd z (hsh hz'.1)).1
  · intro z hzB
    obtain ⟨h16, hgap⟩ := hz z hzB
    have hsubR : ∀ s, s ≤ 1 / 4 → closedBall z s ⊆ ball 0 (3 / 2) := fun s hs =>
      RegularChartScaling.closedBall_sub_of hzB (by linarith)
    have hs16 : 0 < t / (8 * 2) := by positivity
    have hmono : ∀ s s', 0 < s → s ≤ s' → s' ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ RegularChartScaling.pmoff S u z s' := fun s s' h0 h1 h2 =>
      RegularChartScaling.pmo_mono hub h0 h1 (hsubR s' h2)
    have hκ' : -κ ≤ RegularChartScaling.pmoff S u z (t / (8 * 2)) := by
      have : C₀ * Real.log ℓ ≤ κ :=
        mul_le_mul_of_nonneg_right hCC₀ (by linarith)
      linarith
    have hlow : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 4 → -κ ≤ RegularChartScaling.pmoff S u z s :=
      fun s h1 h2 => hκ'.trans (hmono _ _ hs16 h1 h2)
    have hPM : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 8 →
        ReciprocityTheory.AnForm.A.polyMax w z s ≤ RegularChartScaling.pmoff S u z s := fun s h1 h2 => by
      have := polyMax_le_pmoff_same hub hW1 hW3 (hs16.trans_le h1)
        (by linarith : s < 1 / 4) (hsubR _ le_rfl)
      rwa [max_eq_left (hlow s h1 (by linarith))] at this
    have hMP : ∀ s, 0 < s → s ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ ReciprocityTheory.AnForm.A.polyMax w z s := fun s h0 h1 =>
      RegularChartScaling.pmo_le_polyMax hW1.1 hwu h0 (hsubR s h1)
    obtain ⟨-, hmp⟩ := hbd z (hsh hzB)
    have hlb := GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed D ρ b _ w z t isOpen_ball hW1 ht
      (hsubR _ (by linarith)) hbρ
    have ht16 : t ≤ 1 / 16 := by linarith
    have hA := hPM (2 * t) (by rw [div_le_iff₀ (by norm_num)]; linarith) ht2
    have hB : RegularChartScaling.pmoff S u z (t / (4 * 2)) ≤ ReciprocityTheory.AnForm.A.polyMax w z (t / 4) :=
      (hmono _ _ (by positivity) (by linarith) (by linarith)).trans
        (hMP _ (by positivity) (by linarith))
    have hPA : RegularChartScaling.pmoff S u z t ≤ ReciprocityTheory.AnForm.A.polyMax w z (2 * t) :=
      (hmono _ _ ht (by linarith) (by linarith)).trans (hMP _ (by positivity) (by linarith))
    have hP2 := hMP (2 * t) (by positivity) (by linarith)
    have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
    have heps : K * epsT C₀ t ≤ epsT C t := by
      simp only [epsT, ← hℓ, mul_div_assoc]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hq
    have hgap' : ReciprocityTheory.AnForm.A.polyMax w z (2 * t) - ReciprocityTheory.AnForm.A.polyMax w z (t / 4) ≤
        epsT C₀ t := by linarith
    have hKg := mul_le_mul_of_nonneg_left hgap' hK0
    have hup := hPM t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    show -C * Real.log ℓ ≤ RegularChartScaling.pmoff S u z t ∧
      RegularChartScaling.pmoff S u z t - epsT C t ≤ _ ∧ _ ≤ RegularChartScaling.pmoff S u z t
    refine ⟨?_, ?_, hmp.trans hup⟩
    · rw [neg_mul]
      exact hlow t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    · linarith

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalRegularizationGradientBound
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

lemma near_small (a c K' : ℝ) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, 0 < t → t ≤ t₁ →
      c * (Real.log (1 / t) + K') ^ a * t ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 3) / 2 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (1 / 6 : ℝ) (by norm_num)
  have h2 : Tendsto (fun y : ℝ => (c * Real.exp (K' / 6)) * (y ^ a * Real.exp (-(1 / 6) * y)))
      atTop (nhds 0) := by
    simpa [neg_mul] using h.const_mul (c * Real.exp (K' / 6))
  have h3 := h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Y, hY⟩ := eventually_atTop.1 h3
  refine ⟨Real.exp (K' - Y), Real.exp_pos _, fun t ht htle => ?_⟩
  set y := Real.log (1 / t) + K' with hy
  have hlog : Real.log t = K' - y := by
    rw [hy, one_div, Real.log_inv]; ring
  have hYy : Y ≤ y := by
    have := Real.log_le_log ht htle
    rw [Real.log_exp, hlog] at this
    linarith
  have hs := (hY y hYy).le
  have e1 : t ^ ((1 : ℝ) / 2) =
      t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)) := by
    have : Real.exp (K' / 6) * Real.exp (-(1 / 6) * y) = t ^ ((1 : ℝ) / 6) := by
      rw [← Real.exp_add, Real.rpow_def_of_pos ht, hlog]; congr 1; ring
    rw [this, ← Real.rpow_add ht]; norm_num
  have hp : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
  rw [e1]
  calc c * y ^ a * (t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)))
      = t ^ ((1 : ℝ) / 3) * (c * Real.exp (K' / 6) * (y ^ a * Real.exp (-(1 / 6) * y))) := by ring
    _ ≤ t ^ ((1 : ℝ) / 3) * (1 / 2) := mul_le_mul_of_nonneg_left hs hp.le
    _ = t ^ ((1 : ℝ) / 3) / 2 := by ring

theorem polyMaxOff_le_of_rLoc_le :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → DifferentiableOn ℝ u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ u z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, rLoc S m z ≤ Real.log (1 / t) + K → polyMaxOff S u z t ≤ u z + t ^ ((1 : ℝ) / 3) / 2 := by
  intro D S m u C₅ K hm hd hg
  have hclosed : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
    have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
      ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
    rw [this]
    exact S.finite_toSet.isClosed_biUnion
      (fun i _ => isClosed_eq (continuous_apply i) continuous_const)
  have hopen : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hclosed
  set a := |C₅| with ha
  set K' := K + RegularChartScaling.mTot S m * Real.log 4 with hK'
  obtain ⟨t₁, ht₁, hsm⟩ := near_small a (a * Real.exp (K' / 2)) K'
  refine ⟨min (min (1 / 4) (Real.exp (-K))) t₁, by positivity, fun t ht htle z hz hr => ?_⟩
  have ht4 : t ≤ 1 / 4 := htle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htK : t ≤ Real.exp (-K) := htle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht1 : t ≤ t₁ := htle.trans (min_le_right _ _)
  obtain ⟨hzB, hzD⟩ := hz
  have hzn : ∀ i, ‖z i‖ ≤ 2 :=
    RegularChartScaling.norm_coord_le_of_ball (by norm_num : (5 / 4 : ℝ) ≤ 2) hzB
  have hzi : ∀ i ∈ S, z i ≠ 0 := fun i hi h0 => hzD ⟨i, hi, h0⟩
  have hcoord : ∀ i ∈ S, 2 * t ≤ ‖z i‖ := by
    intro i hi
    have hpos : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
    have hterm : Real.log (4 / ‖z i‖ ^ 2) ≤ Real.log (1 / t) + K := by
      have h1 : (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) ≤
          ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2) :=
        Finset.single_le_sum (f := fun j => (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2))
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (RegularChartScaling.log_term_nonneg (hzn j))) hi
      have h2 : Real.log (4 / ‖z i‖ ^ 2) ≤ (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) :=
        le_mul_of_one_le_left (RegularChartScaling.log_term_nonneg (hzn i)) (by exact_mod_cast hm i hi)
      have h3 := Real.exp_pos 1
      unfold rLoc at hr
      linarith
    have hEK : Real.exp K ≤ 1 / t := by
      rw [Real.exp_neg] at htK
      rw [le_div_iff₀ ht]
      have := mul_le_mul_of_nonneg_left htK (Real.exp_pos K).le
      rwa [mul_inv_cancel₀ (Real.exp_pos K).ne'] at this
    have hE : Real.exp (Real.log (1 / t) + K) ≤ 1 / t ^ 2 := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
      calc 1 / t * Real.exp K ≤ 1 / t * (1 / t) :=
            mul_le_mul_of_nonneg_left hEK (by positivity)
        _ = 1 / t ^ 2 := by field_simp
    have h4 : 4 / ‖z i‖ ^ 2 ≤ 1 / t ^ 2 :=
      ((Real.log_le_iff_le_exp (by positivity)).1 hterm).trans hE
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
    by_contra hlt
    push_neg at hlt
    nlinarith
  set y := Real.log (1 / t) + K' with hy
  have hfar : ∀ x ∈ closedBall z t, ∀ i ∈ S, ‖z i‖ / 2 ≤ ‖x i‖ ∧ 0 < ‖x i‖ := by
    intro x hx i hi
    have h1 : ‖x i - z i‖ ≤ t :=
      (norm_le_pi_norm (x - z) i).trans (mem_closedBall_iff_norm.1 hx)
    have h2 := norm_sub_norm_le (z i) (x i)
    rw [norm_sub_rev] at h2
    have h3 := hcoord i hi
    constructor <;> linarith
  have hmem : ∀ x ∈ closedBall z t,
      x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S := by
    intro x hx
    refine ⟨RegularChartScaling.closedBall_sub_of hzB (by linarith) hx, ?_⟩
    rintro ⟨i, hi, h0⟩
    have := (hfar x hx i hi).2
    rw [h0, norm_zero] at this
    exact lt_irrefl _ this
  have hrx : ∀ x ∈ closedBall z t, rLoc S m x ≤ y := by
    intro x hx
    have key : ∀ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤
        (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) + (m i : ℝ) * Real.log 4 := by
      intro i hi
      obtain ⟨h1, h2⟩ := hfar x hx i hi
      have hzp : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [← Real.log_mul (by positivity) (by norm_num)]
      refine Real.log_le_log (by positivity) ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_self_le_mul_self (by positivity) h1]
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    unfold rLoc at hr ⊢
    simp only [hy, hK', RegularChartScaling.mTot]
    linarith
  set B := a * y ^ a * Real.exp (y / 2) with hB
  have hfd : ∀ x ∈ closedBall z t, ‖fderiv ℝ u x‖ ≤ B := by
    intro x hx
    have hxm := hmem x hx
    have hxn : ∀ i, ‖x i‖ ≤ 2 :=
      RegularChartScaling.norm_coord_le_of_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hxm.1
    have hr1 : 1 ≤ rLoc S m x := by
      have := RegularChartScaling.rLoc_ge S m hxn
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hry := hrx x hx
    have hy0 : 0 ≤ y := by linarith
    have hp : rLoc S m x ^ C₅ ≤ y ^ a :=
      (Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self C₅)).trans
        (Real.rpow_le_rpow (by linarith) hry (abs_nonneg _))
    refine (hg x hxm).trans ?_
    refine mul_le_mul (mul_le_mul (le_abs_self C₅) hp (Real.rpow_nonneg (by linarith) _)
      (abs_nonneg _)) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hy0 _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfd z (mem_closedBall_self ht.le))
  have hBt : B * t ≤ t ^ ((1 : ℝ) / 3) / 2 := by
    have hlog : Real.log t = K' - y := by
      rw [hy, one_div, Real.log_inv]; ring
    have e : Real.exp (y / 2) * t = Real.exp (K' / 2) * t ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos ht, hlog]
      nth_rewrite 1 [← Real.exp_log ht]
      rw [hlog, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc B * t = a * y ^ a * (Real.exp (y / 2) * t) := by rw [hB]; ring
      _ = a * Real.exp (K' / 2) * y ^ a * t ^ ((1 : ℝ) / 2) := by rw [e]; ring
      _ ≤ t ^ ((1 : ℝ) / 3) / 2 := hsm t ht ht1
  unfold polyMaxOff
  refine csSup_le ⟨u z, z, ⟨mem_closedBall_self ht.le, hzD⟩, rfl⟩ ?_
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u) (s := closedBall z t)
    (x := z) (y := x) (C := B)
    (fun w hw => (hd w (hmem w hw)).differentiableAt (hopen.mem_nhds (hmem w hw)))
    hfd (convex_closedBall z t) (mem_closedBall_self ht.le) hx
  have h1 : ‖x - z‖ ≤ t := mem_closedBall_iff_norm.1 hx
  have h2 : u x - u z ≤ ‖u x - u z‖ := Real.le_norm_self _
  have h3 : B * ‖x - z‖ ≤ B * t := mul_le_mul_of_nonneg_left h1 hB0
  linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.MollifyConvergesC2Rate
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mollify_converges_C2_rate :
    ∀ (D : ℕ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D) (V K : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V → ContDiffOn ℝ ∞ u V → (∀ᶠ t in 𝓝[>] (0 : ℝ), Set.EqOn (w t) u V) → TendstoUniformlyOn (fun t => ReciprocityTheory.AnForm.A.molli ρ t (w t)) (u) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) (fderiv ℝ (u)) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)))) (fderiv ℝ (fderiv ℝ (u))) (𝓝[>] 0) K ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K, ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ (u) z‖ ≤ M * t := by
  intro D ρ V K u w hV hK hKV hu hw
  obtain ⟨C, ε₀, hε₀, hC⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ V K u hV
    (by exact_mod_cast contDiffOn_infty.1 hu 3) hK hKV
  have hsmallt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε₀ / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K,
      |ReciprocityTheory.AnForm.A.molli ρ t (w t) z - u z| ≤ C * t ∧
      ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ u z‖ ≤ C * t ∧
      ‖fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) z - fderiv ℝ (fderiv ℝ u) z‖
        ≤ C * t := by
    filter_upwards [self_mem_nhdsWithin, hsmallt, hw] with t ht htε hwt z hz
    have ht0 : 0 < t := ht
    have hz2 : z ∈ ReciprocityTheory.AnForm.A.shrink V (2 * t) :=
      (hC (2 * t) (by linarith) (by linarith) z hz).1
    obtain ⟨-, h0, h1, h2⟩ := hC t ht0 (by linarith) z hz
    have hev : ReciprocityTheory.AnForm.A.molli ρ t (w t) =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.molli ρ t u := by
      filter_upwards [ball_mem_nhds z ht0] with y hy
      refine ReciprocityTheory.AnForm.A.molli_congr ρ ht0 (U := V) ?_ hwt
      intro x hx
      apply hz2
      rw [mem_closedBall] at hx ⊢
      rw [mem_ball] at hy
      linarith [dist_triangle x y z]
    rw [hev.eq_of_nhds, hev.fderiv_eq, hev.fderiv.fderiv_eq]
    exact ⟨h0, h1, h2⟩
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ t in 𝓝[>] (0 : ℝ), C * t < δ := by
    intro δ hδ
    have h : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
      have h' : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    exact h.eventually (Iio_mem_nhds hδ)
  refine ⟨?_, ?_, ?_, C, key.mono fun t ht z hz => (ht z hz).2.1⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (ht z hz).1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.2 htδ

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLeviPshRegularization
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section OneChart

variable {D : ℕ}

lemma oc_isClosed_coordDiv (S : Finset (Fin D)) : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
  have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
    ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
  rw [this]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

lemma oc_q_bounds {q : (Fin D → ℂ) → ℝ} (hq : ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) 2)) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2), |q z| ≤ Q ∧ ‖fderiv ℝ q z‖ ≤ Q := by
  have hsub : closedBall (0 : Fin D → ℂ) (3 / 2) ⊆ ball 0 2 :=
    closedBall_subset_ball (by norm_num)
  have hc : IsCompact (closedBall (0 : Fin D → ℂ) (3 / 2)) := isCompact_closedBall _ _
  obtain ⟨a, ha⟩ := hc.exists_bound_of_continuousOn (hq.continuousOn.mono hsub)
  obtain ⟨b, hb⟩ := hc.exists_bound_of_continuousOn
    ((hq.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hsub)
  refine ⟨max (max a b) 0, le_max_right _ _, fun z hz => ?_⟩
  have hz' := ball_subset_closedBall hz
  have h1 : |q z| ≤ a := by simpa using ha z hz'
  exact ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hb z hz').trans ((le_max_right _ _).trans (le_max_left _ _))⟩

lemma fderiv_add_and_second_fderiv_add {W : Set (Fin D → ℂ)} (hW : IsOpen W) {q p : (Fin D → ℂ) → ℝ}
    (hq : ContDiffOn ℝ ∞ q W) (hp : ContDiffOn ℝ ∞ p W) {z : Fin D → ℂ} (hz : z ∈ W) :
    fderiv ℝ (fun x => q x + p x) z = fderiv ℝ q z + fderiv ℝ p z ∧
    fderiv ℝ (fderiv ℝ (fun x => q x + p x)) z =
      fderiv ℝ (fderiv ℝ q) z + fderiv ℝ (fderiv ℝ p) z := by
  have hd : ∀ {f : (Fin D → ℂ) → ℝ}, ContDiffOn ℝ ∞ f W → ∀ x ∈ W, DifferentiableAt ℝ f x :=
    fun hf x hx => (hf.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hx)
  have hd2 : ∀ f : (Fin D → ℂ) → ℝ, ContDiffOn ℝ ∞ f W →
      DifferentiableAt ℝ (fderiv ℝ f) z := fun f hf => by
    have h2 : ContDiffOn ℝ 2 f W := by exact_mod_cast contDiffOn_infty.1 hf 2
    exact ((h2.fderiv_of_isOpen (m := 1) hW one_add_one_eq_two.le).differentiableOn
      (by simp)).differentiableAt (hW.mem_nhds hz)
  have he : ∀ x ∈ W, fderiv ℝ (fun x => q x + p x) x = fderiv ℝ q x + fderiv ℝ p x :=
    fun x hx => fderiv_fun_add (hd hq x hx) (hd hp x hx)
  refine ⟨he z hz, ?_⟩
  have hev : fderiv ℝ (fun x => q x + p x) =ᶠ[𝓝 z] fun x => fderiv ℝ q x + fderiv ℝ p x :=
    Filter.eventually_of_mem (hW.mem_nhds hz) he
  rw [hev.fderiv_eq]
  exact fderiv_fun_add (hd2 q hq) (hd2 p hp)

lemma oc_tuo {E ι : Type*} [NormedAddCommGroup E] {l : Filter ι} {X : Type*} {K : Set X}
    {F G : ι → X → E} {f g : X → E} (h : TendstoUniformlyOn F f l K)
    (he : ∀ᶠ t in l, ∀ z ∈ K, G t z - g z = F t z - f z) : TendstoUniformlyOn G g l K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε, he] with t ht hte z hz
  have := ht z hz
  rw [dist_comm, dist_eq_norm] at this ⊢
  rw [hte z hz]
  exact this

lemma oc_ell {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

lemma oc_eps {t C₁ C : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) (hC₁ : 1 ≤ C₁)
    (hC : C₁ ≤ C) : epsT C₁ t ≤ epsT C t ∧ epsT C₁ t ≤ C₁ * Real.log (Real.log (1 / t)) := by
  obtain ⟨h1, h2⟩ := oc_ell ht hte
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hℓ : 0 < Real.log (1 / t) := by linarith
  unfold epsT
  constructor
  · apply div_le_div_of_nonneg_right _ hℓ.le
    exact mul_le_mul_of_nonneg_right hC (by linarith)
  · rw [div_le_iff₀ hℓ]
    have : 0 ≤ C₁ * Real.log (Real.log (1 / t)) := by positivity
    nlinarith

lemma oc_rLoc_ge (S : Finset (Fin D)) (m : Fin D → ℕ) {z : Fin D → ℂ}
    (hz : z ∈ ball (0 : Fin D → ℂ) (3 / 2)) :
    1 ≤ rLoc S m z ∧ 1 ≤ Real.log (rLoc S m z) := by
  have h := RegularChartScaling.rLoc_ge S m
    (RegularChartScaling.norm_coord_le_of_ball (R := 3 / 2) (by norm_num) hz)
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨he1.trans h, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at this

lemma oc_rLoc_cont (S : Finset (Fin D)) (m : Fin D → ℕ) :
    ContinuousOn (rLoc S m) (ReciprocityTheory.AnForm.A.coordDiv S)ᶜ := by
  unfold rLoc
  refine continuousOn_const.add (continuousOn_finsetSum _ fun i hi => ?_)
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · refine continuousOn_const.div₀ (by fun_prop) ?_
    intro z hz
    have : z i ≠ 0 := fun h0 => hz ⟨i, hi, h0⟩
    positivity
  · intro z hz
    have : z i ≠ 0 := fun h0 => hz ⟨i, hi, h0⟩
    positivity

lemma oc_grad {r C₅ Q a b : ℝ} (hr : 1 ≤ r) (hC₅ : 0 ≤ C₅) (hQ : 0 ≤ Q) (ha : a ≤ Q)
    (hb : b ≤ C₅ * r ^ C₅ * Real.exp (r / 2)) :
    a + b ≤ (C₅ + Q) * r ^ (C₅ + Q) * Real.exp (r / 2) := by
  have h1 : r ^ C₅ ≤ r ^ (C₅ + Q) := Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have h2 : 1 ≤ r ^ (C₅ + Q) := Real.one_le_rpow hr (by linarith)
  have h3 : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  have h4 : 1 ≤ r ^ (C₅ + Q) * Real.exp (r / 2) := by nlinarith
  have h5 : C₅ * r ^ C₅ * Real.exp (r / 2) ≤ C₅ * (r ^ (C₅ + Q) * Real.exp (r / 2)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) hC₅
  nlinarith

end OneChart

theorem regularise_one_chart :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (q ph : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) (2)) → ContDiffOn ℝ ∞ ph (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) (fun z => q z + ph z) → (∀ z ∈ ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ ph z ∧ ph z ≤ C₅) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ ph z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ (C t₀ : ℝ) (phT : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ (∀ t, 0 < t → t ≤ t₀ → ContDiffOn ℝ ∞ (phT t) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (fun z => q z + phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ C ∧ -C * Real.log (Real.log (1 / t)) ≤ phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, ph z ≤ phT t z ∧ (rLoc S m z ≤ Real.log (1 / t) + K → phT t z ≤ ph z + t ^ ((1 : ℝ) / 3))) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), polyMaxOff S (fun x => q x + ph x) z t - epsT C t ≤ q z + phT t z ∧ q z + phT t z ≤ polyMaxOff S (fun x => q x + ph x) z t) ∧ ∀ t', t ≤ t' → t' ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ phT t' z + epsT C t') ∧ ∀ K' ⊆ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, IsCompact K' → TendstoUniformlyOn (fun t => phT t) (ph) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (phT t)) (fderiv ℝ (ph)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t))) (fderiv ℝ (fderiv ℝ (ph))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (phT t) z - fderiv ℝ (ph) z‖ ≤ M * t := by
  intro D S m q ph C₅ K hm hq hph hL hb hg
  have hAc := oc_isClosed_coordDiv S
  have hC₅ : 0 ≤ C₅ := RegularChartScaling.fifth_volume_constant_nonneg m le_rfl (by norm_num) hb
  obtain ⟨Q, hQ0, hQ⟩ := oc_q_bounds hq
  have hsub : ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S ⊆
      ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S :=
    Set.diff_subset_diff_left (ball_subset_ball (by norm_num))
  have hqA : ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    hq.mono Set.diff_subset
  have huS : ContDiffOn ℝ ∞ (fun z => q z + ph z)
      (ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S) := hqA.add hph
  have hO2 : IsOpen (ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hAc
  have hO3 : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hAc
  have hucont : ContinuousOn (fun z => q z + ph z)
      (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    huS.continuousOn.mono hsub
  have hupsh : ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S)
      (fun z => q z + ph z) :=
    (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ hO3 (hL.1.mono hsub)).2
      ⟨hL.1.mono hsub, fun z hz w => hL.2 z (hsub hz) w⟩
  have hubd : ∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S,
      -(C₅ + Q) * Real.log (rLoc S m z) ≤ q z + ph z ∧ q z + ph z ≤ C₅ + Q := by
    intro z hz
    obtain ⟨h1, h2⟩ := hb z (hsub hz)
    have h3 := abs_le.1 (hQ z hz.1).1
    have h4 := (oc_rLoc_ge S m hz.1).2
    constructor
    · nlinarith
    · linarith
  have hugrad : ∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S,
      ‖fderiv ℝ (fun z => q z + ph z) z‖ ≤
        (C₅ + Q) * rLoc S m z ^ (C₅ + Q) * Real.exp (rLoc S m z / 2) := by
    intro z hz
    rw [(fderiv_add_and_second_fderiv_add hO2 hqA hph (hsub hz)).1]
    exact (norm_add_le _ _).trans
      (oc_grad (oc_rLoc_ge S m hz.1).1 hC₅ hQ0 (hQ z hz.1).2 (hg z hz))
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨C₁, t₁, w, hC₁, ht₁, ht₁e, ht₁8, hW⟩ :=
    GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax D S m (fun z => q z + ph z) (C₅ + Q) ρ hucont hupsh hubd
  obtain ⟨t₂, ht₂, hN⟩ := GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le D S m (fun z => q z + ph z) (C₅ + Q) K hm
    ((huS.differentiableOn (by simp)).mono hsub) hugrad
  obtain ⟨phT, hphT⟩ : ∃ phT : ℝ → (Fin D → ℂ) → ℝ,
      ∀ t z, phT t z = ReciprocityTheory.AnForm.A.molli ρ t (w t) z - q z := ⟨_, fun _ _ => rfl⟩
  have hphF : ∀ t, phT t = fun z => ReciprocityTheory.AnForm.A.molli ρ t (w t) z - q z :=
    fun t => funext (hphT t)
  have hgF : ∀ t, ReciprocityTheory.AnForm.A.molli ρ t (w t) = fun z => q z + phT t z := by
    intro t; funext z; rw [hphT]; ring
  have hq54 : ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), z ∈ ball (0 : Fin D → ℂ) (3 / 2) :=
    fun z hz => ball_subset_ball (by norm_num) hz
  have hqs : ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) (5 / 4)) :=
    hq.mono (ball_subset_ball (by norm_num))
  have hsmooth : ∀ t, 0 < t → t ≤ t₁ → ContDiffOn ℝ ∞ (phT t) (ball (0 : Fin D → ℂ) (5 / 4)) := by
    intro t ht htt
    rw [hphF]
    exact (hW t ht htt).2.1.sub hqs
  have hC1 : C₁ ≤ 2 * C₁ + 2 * Q + C₅ + 1 := by linarith
  refine ⟨2 * C₁ + 2 * Q + C₅ + 1, min t₁ t₂, phT, by linarith, lt_min ht₁ ht₂,
    (min_le_left _ _).trans ht₁e, fun t ht htt => ?_, fun K' hK' hcK' => ?_⟩
  · have ht1 : t ≤ t₁ := htt.trans (min_le_left _ _)
    have ht2 : t ≤ t₂ := htt.trans (min_le_right _ _)
    have hte := ht1.trans ht₁e
    obtain ⟨-, hs, hl, hge, hM⟩ := hW t ht ht1
    obtain ⟨hℓ1, hℓ2⟩ := oc_ell ht hte
    obtain ⟨he1, he2⟩ := oc_eps ht hte hC₁ hC1
    have hcb : ∀ s, s ≤ t₁ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), closedBall z s ⊆ ball 0 (3 / 2) :=
      fun s hs z hz => RegularChartScaling.closedBall_sub_of hz (by linarith)
    refine ⟨hsmooth t ht ht1, ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_,
      fun t' htt' ht' z hz => ?_⟩
    · rw [← hgF]; exact hl
    · obtain ⟨h1, h2, h3⟩ := hM z hz
      have hup : polyMaxOff S (fun z => q z + ph z) z t ≤ C₅ + Q :=
        RegularChartScaling.pmo_le z ht fun x hx => (hubd x ⟨hcb t ht1 z hz hx.1, hx.2⟩).2
      have hqz := abs_le.1 (hQ z (hq54 z hz)).1
      rw [hphT]
      constructor
      · linarith
      · nlinarith
    · obtain ⟨h1, h2, h3⟩ := hM z hz.1
      refine ⟨?_, fun hr => ?_⟩
      · rw [hphT]; have := hge z hz; linarith
      · rw [hphT]
        have h4 := hN t ht ht2 z hz hr
        have h5 : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
        linarith
    · obtain ⟨h1, h2, h3⟩ := hM z hz
      rw [hphT]
      constructor <;> linarith
    · have ht'0 : 0 < t' := ht.trans_le htt'
      have ht'1 : t' ≤ t₁ := ht'.trans (min_le_left _ _)
      have ht'e := ht'1.trans ht₁e
      obtain ⟨-, -, -, -, hM'⟩ := hW t' ht'0 ht'1
      obtain ⟨h1, h2, h3⟩ := hM z hz
      obtain ⟨h1', h2', h3'⟩ := hM' z hz
      obtain ⟨he1', -⟩ := oc_eps ht'0 ht'e hC₁ hC1
      have hmono : polyMaxOff S (fun z => q z + ph z) z t ≤
          polyMaxOff S (fun z => q z + ph z) z t' :=
        RegularChartScaling.pmo_mono (fun x hx => (hubd x hx).2) ht htt' (hcb t' ht'1 z hz)
      rw [hphT, hphT]
      linarith
  · have hK2 : K' ⊆ (ReciprocityTheory.AnForm.A.coordDiv S)ᶜ := fun z hz => (hK' hz).2
    obtain ⟨B, hB⟩ := (hcK'.image_of_continuousOn ((oc_rLoc_cont S m).mono hK2)).bddAbove
    obtain ⟨V, hVdef⟩ : ∃ V : Set (Fin D → ℂ),
        V = (ReciprocityTheory.AnForm.A.coordDiv S)ᶜ ∩ rLoc S m ⁻¹' Set.Iio (B + 1) ∩ ball 0 (5 / 4) :=
      ⟨_, rfl⟩
    have hV : IsOpen V := by
      rw [hVdef]
      exact ((oc_rLoc_cont S m).isOpen_inter_preimage hAc.isOpen_compl isOpen_Iio).inter isOpen_ball
    have hVsub : V ⊆ ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S := by
      rw [hVdef]
      exact fun z hz => ⟨ball_subset_ball (by norm_num) hz.2, hz.1.1⟩
    have hKV : K' ⊆ V := by
      rw [hVdef]
      intro z hz
      have : rLoc S m z ≤ B := hB (Set.mem_image_of_mem _ hz)
      exact ⟨⟨hK2 hz, by simp only [Set.mem_preimage, Set.mem_Iio]; linarith⟩, (hK' hz).1⟩
    have hlog : Tendsto (fun t : ℝ => Real.log (Real.log (1 / t))) (𝓝[>] 0) atTop := by
      have h : Tendsto (fun t : ℝ => 1 / t) (𝓝[>] 0) atTop := by
        simpa only [one_div] using tendsto_inv_nhdsGT_zero
      exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h)
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min t₁ t₂ :=
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_min ht₁ ht₂))
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), Set.EqOn (w t) (fun z => q z + ph z) V := by
      filter_upwards [self_mem_nhdsWithin, hsmall,
        hlog.eventually_ge_atTop ((C₅ + Q) * Real.log (B + 1) / C₁)] with t ht htt hbig z hz
      have ht0 : 0 < t := ht
      have ht1 : t ≤ t₁ := htt.le.trans (min_le_left _ _)
      have hzV := hz
      rw [hVdef] at hz
      have hz3 := hq54 z hz.2
      have hzB : z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S :=
        ⟨hz3, hz.1.1⟩
      rw [(hW t ht0 ht1).1 z hzB]
      refine max_eq_left ?_
      have hr := oc_rLoc_ge S m hz3
      have hr2 : rLoc S m z < B + 1 := hz.1.2
      have hl : Real.log (rLoc S m z) ≤ Real.log (B + 1) :=
        Real.log_le_log (by linarith) hr2.le
      have h1 := (hubd z hzB).1
      have hC₁0 : 0 < C₁ := by linarith
      rw [div_le_iff₀ hC₁0] at hbig
      have hCQ : 0 ≤ C₅ + Q := by linarith
      nlinarith
    have huV : ContDiffOn ℝ ∞ (fun z => q z + ph z) V := huS.mono hVsub
    obtain ⟨h1, h2, h3, M, h4⟩ := mollify_converges_C2_rate D ρ V K' (fun z => q z + ph z)
      (fun t => w t) hV hcK' hKV huV hev
    have hO : IsOpen (ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
      isOpen_ball.sdiff hAc
    have hOsub : ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S ⊆
        ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S :=
      Set.diff_subset_diff_left (ball_subset_ball (by norm_num))
    have hd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        fderiv ℝ (phT t) z - fderiv ℝ ph z =
          fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ (fun z => q z + ph z) z ∧
        fderiv ℝ (fderiv ℝ (phT t)) z - fderiv ℝ (fderiv ℝ ph) z =
          fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) z -
            fderiv ℝ (fderiv ℝ (fun z => q z + ph z)) z := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htt z hz
      have ht0 : 0 < t := ht
      have hs := hsmooth t ht0 (htt.le.trans (min_le_left _ _))
      have hzO := hK' hz
      obtain ⟨a1, a2⟩ := fderiv_add_and_second_fderiv_add hO (hqs.mono Set.diff_subset) (hs.mono Set.diff_subset) hzO
      obtain ⟨b1, b2⟩ := fderiv_add_and_second_fderiv_add hO (hqs.mono Set.diff_subset) (hph.mono hOsub) hzO
      rw [hgF t, a1, a2, b1, b2]
      constructor <;> abel
    refine ⟨oc_tuo h1 ?_, oc_tuo h2 (hd.mono fun t ht z hz => (ht z hz).1),
      oc_tuo h3 (hd.mono fun t ht z hz => (ht z hz).2), M, ?_⟩
    · refine Filter.Eventually.of_forall fun t z _ => ?_
      rw [hphT]; ring
    · filter_upwards [h4, hd] with t ht htd z hz
      rw [(htd z hz).1]
      exact ht z hz

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueC2Explicit
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

open GroundTheory.Heights₂.Heights.AnalyticLimit (TendstoC2On)

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_add_small {V α : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {N : Set α} {g₀ : ℝ → α → V} {g : α → V} {l : Filter ℝ} {s : ℝ → ℝ} {q : α → V} {C : ℝ}
    (hq : ∀ z ∈ N, ‖q z‖ ≤ C) (hs : Tendsto s l (𝓝 0)) (h : TendstoUniformlyOn g₀ g l N) :
    TendstoUniformlyOn (fun t z => g₀ t z + s t • q z) g l N := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  have hs' : ∀ᶠ t in l, |s t| < ε / 2 / (|C| + 1) := by
    have := hs.eventually (Metric.ball_mem_nhds (0 : ℝ) (div_pos (half_pos hε) hC))
    filter_upwards [this] with t ht
    simpa [Real.dist_eq] using ht
  filter_upwards [h (ε / 2) (half_pos hε), hs'] with t h1 h2 z hz
  have h3 := h1 z hz
  have h4 : ‖s t • q z‖ < ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hqz : ‖q z‖ ≤ |C| + 1 := (hq z hz).trans ((le_abs_self C).trans (by linarith))
    calc |s t| * ‖q z‖ ≤ |s t| * (|C| + 1) := by gcongr
      _ < ε / 2 / (|C| + 1) * (|C| + 1) := by gcongr
      _ = ε / 2 := by field_simp
  calc dist (g z) (g₀ t z + s t • q z) ≤ dist (g z) (g₀ t z) + dist (g₀ t z) (g₀ t z + s t • q z) :=
        dist_triangle _ _ _
    _ = dist (g z) (g₀ t z) + ‖s t • q z‖ := by simp [dist_eq_norm]
    _ < ε := by linarith

theorem tendstoC2On_congr {U N : Set E} (hU : IsOpen U) (hN : N ⊆ U) {G G' : ℝ → E → ℝ} {p : E → ℝ}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, G' t z = G t z) (hc : TendstoC2On G' p N) :
    TendstoC2On G p N := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N, G' t =ᶠ[𝓝 z] G t := by
    filter_upwards [h] with t ht z hz
    filter_upwards [hU.mem_nhds (hN hz)] with y hy using ht y hy
  refine ⟨hc.1.congr ?_, hc.2.1.congr ?_, hc.2.2.congr ?_⟩
  · filter_upwards [hev] with t ht z hz using (ht z hz).eq_of_nhds
  · filter_upwards [hev] with t ht z hz using (ht z hz).fderiv_eq
  · filter_upwards [hev] with t ht z hz using (ht z hz).fderiv.fderiv_eq

theorem tendstoC2On_add_small {U N : Set E} (hU : IsOpen U) (hN : N ⊆ U) (hNc : IsCompact N)
    {a : ℝ → E → ℝ} {p Q : E → ℝ} {δ : ℝ → ℝ} (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (hQ : ContDiffOn ℝ 2 Q U) (ha : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (a t) U)
    (h : TendstoC2On a p N) :
    TendstoC2On (fun t z => a t z + δ t * Q z) p N ∧
      ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N,
        ‖fderiv ℝ (fun z => a t z + δ t * Q z) z - fderiv ℝ (a t) z‖ ≤ C * |δ t| := by
  have hD1 : ContinuousOn (fderiv ℝ Q) U := hQ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ Q)) U :=
    (hQ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M0, hM0⟩ := hNc.exists_bound_of_continuousOn (hQ.continuousOn.mono hN)
  obtain ⟨M1, hM1⟩ := hNc.exists_bound_of_continuousOn (hD1.mono hN)
  obtain ⟨M2, hM2⟩ := hNc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ Q)) (by exact hD2.mono hN)
  have hdiffQ : ∀ z ∈ U, DifferentiableAt ℝ Q z := fun z hz =>
    (hQ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hdiff2Q : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ Q) z := fun z hz =>
    ((hQ.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : ∀ t, ContDiffOn ℝ 2 (a t) U → ∀ z ∈ U,
      fderiv ℝ (fun z => a t z + δ t * Q z) z = fderiv ℝ (a t) z + δ t • fderiv ℝ Q z := by
    intro t ht z hz
    have hd : DifferentiableAt ℝ (a t) z :=
      (ht.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    have := (hd.hasFDerivAt.add ((hdiffQ z hz).hasFDerivAt.const_mul (δ t))).fderiv
    exact this
  have h2 : ∀ t, ContDiffOn ℝ 2 (a t) U → ∀ z ∈ U,
      fderiv ℝ (fderiv ℝ (fun z => a t z + δ t * Q z)) z =
        fderiv ℝ (fderiv ℝ (a t)) z + δ t • fderiv ℝ (fderiv ℝ Q) z := by
    intro t ht z hz
    have hev : fderiv ℝ (fun z => a t z + δ t * Q z) =ᶠ[𝓝 z]
        fun z => fderiv ℝ (a t) z + δ t • fderiv ℝ Q z := by
      filter_upwards [hU.mem_nhds hz] with y hy using h1 t ht y hy
    rw [hev.fderiv_eq]
    have hd : DifferentiableAt ℝ (fderiv ℝ (a t)) z :=
      ((ht.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    exact (hd.hasFDerivAt.add ((hdiff2Q z hz).hasFDerivAt.const_smul (δ t))).fderiv
  refine ⟨⟨?_, ?_, ?_⟩, |M1|, ?_⟩
  · have := tendstoUniformlyOn_add_small (q := Q) hM0 hδ h.1
    simpa [smul_eq_mul] using this
  · have := tendstoUniformlyOn_add_small (q := fderiv ℝ Q) hM1 hδ h.2.1
    refine this.congr ?_
    filter_upwards [ha] with t ht z hz
    exact (h1 t ht z (hN hz)).symm
  · have := tendstoUniformlyOn_add_small (q := fderiv ℝ (fderiv ℝ Q)) hM2 hδ h.2.2
    refine this.congr ?_
    filter_upwards [ha] with t ht z hz
    exact (h2 t ht z (hN hz)).symm
  · filter_upwards [ha] with t ht z hz
    rw [h1 t ht z (hN hz), add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hM1 z hz).trans (le_abs_self _)) (abs_nonneg _)

end General

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem chart_C2_convergence (A B : FinHolAtlas e X) (hAB : A.Compatible B) (jA : Fin A.n) (j : Fin B.n)
    (s : X → X → ℂ) (ph : X → ℝ) (hbd : IsClosed (bdry s)) (hph : A.SmoothOn (bdry s)ᶜ ph)
    {W' : Set X} (hW' : IsOpen W') (hWb : W' ⊆ chartBall B j (5 / 4)) (hWc : W' ⊆ (bdry s)ᶜ)
    (f : ℝ → X → ℝ) (hfs : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.SmoothOn (chartBall B j (5 / 4)) (f t))
    (hconv : ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t => f t ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (f t ∘ (B.chart j).symm))
        (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t ∘ (B.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        ‖fderiv ℝ (f t ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t)
    {N : Set (Fin e → ℂ)} (hNc : IsCompact N)
    (hN : N ⊆ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W') :
    TendstoC2On (fun t => f t ∘ (A.chart jA).symm) (ph ∘ (A.chart jA).symm) N ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N,
        ‖fderiv ℝ (f t ∘ (A.chart jA).symm) z - fderiv ℝ (ph ∘ (A.chart jA).symm) z‖ ≤ M * t := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  set W := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W' with hWdef
  have hWo : IsOpen W := (A.chart jA).isOpen_inter_preimage_symm hW'
  set U := ball (0 : Fin e → ℂ) (5 / 4) ∩
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ) with hUdef
  have hUo : IsOpen U :=
    isOpen_ball.inter ((B.chart j).isOpen_inter_preimage_symm hbd.isOpen_compl)
  set τ := B.chart j ∘ (A.chart jA).symm with hτdef
  have hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y := by
    intro y hy
    have ha : AnalyticAt ℂ τ y := hAB.1 jA j y ⟨hy.1, (hWb hy.2).1⟩
    have hR : AnalyticAt ℝ τ y := ha.restrictScalars
    exact hR.contDiffAt
  have hleft : ∀ y ∈ W, (B.chart j).symm (τ y) = (A.chart jA).symm y := fun y hy =>
    (B.chart j).left_inv (hWb hy.2).1
  have hWU : Set.MapsTo τ W U := by
    intro y hy
    refine ⟨(hWb hy.2).2, (B.chart j).map_source (hWb hy.2).1, ?_⟩
    show (B.chart j).symm (τ y) ∈ (bdry s)ᶜ
    rw [hleft y hy]
    exact hWc hy.2
  have hΦ : ∀ z ∈ U, ContDiffAt ℝ 2 (ph ∘ (B.chart j).symm) z := by
    intro z hz
    exact (((smoothOn_of_compatible hAB hbd.isOpen_compl hph) j).contDiffAt
      (((B.chart j).isOpen_inter_preimage_symm hbd.isOpen_compl).mem_nhds hz.2)).of_le h2
  have hG : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, ContDiffAt ℝ 2 (f t ∘ (B.chart j).symm) z := by
    filter_upwards [hfs] with t ht z hz
    have hz' : z ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' chartBall B j (5 / 4) := by
      refine ⟨hz.2.1, (B.chart j).map_target hz.2.1, ?_⟩
      show B.chart j ((B.chart j).symm z) ∈ ball (0 : Fin e → ℂ) (5 / 4)
      rw [(B.chart j).right_inv hz.2.1]
      exact hz.1
    exact (((smoothOn_of_compatible hAB (chartBall_isOpen B j _) ht) j).contDiffAt
      (((B.chart j).isOpen_inter_preimage_symm (chartBall_isOpen B j _)).mem_nhds hz')).of_le h2
  have hF : ∀ t, ∀ y ∈ W, (f t ∘ (A.chart jA).symm) y = (f t ∘ (B.chart j).symm) (τ y) := by
    intro t y hy
    simp only [Function.comp_apply]
    rw [hleft y hy]
  have hΨ : ∀ y ∈ W, (ph ∘ (A.chart jA).symm) y = (ph ∘ (B.chart j).symm) (τ y) := by
    intro y hy
    simp only [Function.comp_apply]
    rw [hleft y hy]
  have hτN : IsCompact (τ '' N) :=
    hNc.image_of_continuousOn fun y hy => (hτ y (hN hy)).continuousAt.continuousWithinAt
  have hτU : τ '' N ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    have := hWU (hN hy)
    exact ⟨this.1, this.2.2⟩
  obtain ⟨c0, c1, c2, M, hM⟩ := hconv _ hτU hτN
  refine ⟨GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.local_c2_convergence_pullback hWo hτ hWU hG hΦ hF hΨ hNc hN
    c0 c1 c2, ?_⟩
  have hτc : ContDiffOn ℝ 2 τ W := fun y hy => (hτ y hy).contDiffWithinAt
  have hD1 : ContinuousOn (fderiv ℝ τ) W := hτc.continuousOn_fderiv_of_isOpen hWo (by norm_num)
  obtain ⟨M1, hM1⟩ := hNc.exists_bound_of_continuousOn (hD1.mono hN)
  refine ⟨M * M1, ?_⟩
  filter_upwards [hM, hG] with t ht hGt z hz
  have e1 := (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.fderiv_fderiv_comp_eq hWo hτ hWU hGt
    (hF t) (hN hz)).1
  have e2 := (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.fderiv_fderiv_comp_eq hWo hτ hWU hΦ
    hΨ (hN hz)).1
  rw [e1, e2, ← ContinuousLinearMap.sub_comp]
  have h3 := ht (τ z) (Set.mem_image_of_mem τ hz)
  have h4 := hM1 z hz
  calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M * t) * M1 := mul_le_mul h3 h4 (norm_nonneg _) ((norm_nonneg _).trans h3)
    _ = M * M1 * t := by ring

end Chart

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

noncomputable section

section Glue

variable {e : ℕ} {X : Type} [TopologicalSpace X]

lemma glue_local_unif [T2Space X] (B : FinHolAtlas e X)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧
      (∀ j, y₀ ∈ chartBall B j (5 / 4) → W ⊆ chartBall B j (5 / 4)) ∧
      ∀ (f η : Fin B.n → X → ℝ) (δ Mb : ℝ), 0 ≤ δ → δ ≤ 1 →
        (∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) → (∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1) →
        (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
        (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
        ∀ j, y₀ ∉ chartBall B j (5 / 4) → ∀ y ∈ W,
          glueArg B f η δ Mb j y + δ ≤ glueArg B f η δ Mb k₀ y := by
  classical
  set Kc : Fin B.n → Set X := fun j => (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8)
  have hKsub : ∀ j, closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).target :=
    fun j => (closedBall_subset_closedBall (by norm_num)).trans (h2 j)
  have hKcl : ∀ j, IsClosed (Kc j) := fun j =>
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((B.chart j).continuousOn_symm.mono (hKsub j))).isClosed
  have hKin : ∀ j, Kc j ⊆ chartBall B j (5 / 4) := by
    rintro j _ ⟨z, hz, rfl⟩
    refine ⟨(B.chart j).map_target (hKsub j hz), ?_⟩
    rw [Set.mem_preimage, (B.chart j).right_inv (hKsub j hz)]
    exact closedBall_subset_ball (by norm_num) hz
  have hnotK : ∀ j, ∀ y, y ∉ Kc j → y ∉ chartBall B j (9 / 8) := by
    intro j y hy hb
    exact hy ⟨B.chart j y, ball_subset_closedBall hb.2, (B.chart j).left_inv hb.1⟩
  let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
  refine ⟨chartBall B k₀ 1 ∩ (⋂ j ∈ I, chartBall B j (5 / 4)) ∩ ⋂ j ∈ Iᶜ, (Kc j)ᶜ, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((chartBall_isOpen B k₀ 1).inter ?_).inter ?_
    · exact isOpen_biInter_finset fun j _ => chartBall_isOpen B j _
    · exact isOpen_biInter_finset fun j _ => (hKcl j).isOpen_compl
  · refine ⟨⟨hk₀, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter]; intro j hj; simpa [I] using hj
    · simp only [Set.mem_iInter]
      intro j hj hK
      have : y₀ ∈ chartBall B j (5 / 4) := hKin j hK
      simp [I, this] at hj
  · exact fun y hy => hy.1.1
  · intro j hj y hy
    have := hy.1.2
    simp only [Set.mem_iInter] at this
    exact this j (by simpa [I] using hj)
  · intro f η δ Mb hδ0 hδ1 hη0 hη1 hMb hov j hj y hy
    have hyK : y ∉ Kc j := by
      have := hy.2
      simp only [Set.mem_iInter] at this
      exact this j (by simpa [I] using hj)
    have hy0 : y ∈ chartBall B k₀ 1 := hy.1.1
    have hy5 : y ∈ chartBall B k₀ (5 / 4) := chartBall_mono B k₀ (by norm_num) hy0
    have hk : glueArg B f η δ Mb k₀ y = f k₀ y := by
      simp [glueArg, hy5, hη0 k₀ y hy0]
    rw [hk]
    unfold glueArg
    split_ifs with hj5
    · rw [hη1 j y (hnotK j y hyK)]
      have := hov j k₀ y ⟨hj5, hy5⟩
      have := (abs_le.1 this).2
      linarith [hδ0]
    · have := (abs_le.1 (hMb k₀ y hy5)).1
      linarith

lemma glue_loc_rep [T2Space X] (B : FinHolAtlas e X) [Nonempty (Fin B.n)]
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ (W : Set X) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧
      (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ (f η : Fin B.n → X → ℝ) (δ Mb : ℝ), 0 < δ → δ ≤ 1 →
        (∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) → (∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1) →
        (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
        (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
        ∀ y ∈ W, ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) =
          ReciprocityTheory.AnForm.A.regMax δ (fun j =>
            if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
  classical
  obtain ⟨W, hWo, hyW, hWk, hWin, hWout⟩ := glue_local_unif B h2 y₀ k₀ hk₀
  let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
  have hk₀I : k₀ ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact chartBall_mono B k₀ (by norm_num) hk₀
  refine ⟨W, I, hWo, hyW, hWk, hk₀I, fun j hj => hWin j (by simpa [I] using hj), ?_⟩
  intro f η δ Mb hδ hδ1 hη0 hη1 hMb hov y hy
  have hy5 : ∀ j ∈ I, y ∈ chartBall B j (5 / 4) := fun j hj => hWin j (by simpa [I] using hj) hy
  rw [regMax_dominated (Fin B.n) δ _ k₀ I hδ hk₀I (fun j hj =>
    hWout f η δ Mb hδ.le hδ1 hη0 hη1 hMb hov j (by simpa [I] using hj) y hy)]
  congr 1
  funext j
  have hk5 := hy5 k₀ hk₀I
  by_cases hj : j ∈ I
  · simp [hj, glueArg, hy5 j hj]
  · simp [hj, glueArg, hk5]

theorem reg_glue_explicit [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) [Nonempty (Fin B.n)]
    (Θ th : LocPot X) (hAB : A.Compatible B) (hcov : ∀ x, ∃ j, x ∈ chartBall B j 1)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hΘ : IsPotential A Θ) (hΘpos : IsPosPot A Θ) (hth : IsPotential A th)
    (η : Fin B.n → X → ℝ)
    (hη : ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (δ Mb : ℝ) (f : Fin B.n → X → ℝ), 0 < δ → δ ≤ 1 →
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f j)) →
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
      (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f j))) →
      (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
      A.Smooth (fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y)) ∧
      (∀ c₀ : ℝ, IsPsh A (th + LocPot.ofFun
        (fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) + c₀) +
          Θ.rsmul (2 * K * δ))) ∧
      ∀ j, ∀ y ∈ chartBall B j (5 / 4),
        |ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) - f j y| ≤ K * δ := by
  classical
  have hηs : ∀ j, A.Smooth (η j) := fun j => (hη j).1

  have hC : ∀ j, ∃ C : ℝ, IsPsh A (LocPot.ofFun (η j) + Θ.rsmul C) := fun j =>
    pshShift A Θ hΘ hΘpos (η j) (hηs j)
  choose Cj hCj using hC
  set K' : ℝ := ∑ j, |Cj j| with hK'
  have hK'ge : ∀ j, Cj j ≤ K' := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j))
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨4 * K' + 2, by linarith, ?_⟩
  intro δ Mb f hδ hδ1 hfs hMb hfp hov
  set F : X → ℝ := fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) with hF

  have hRM := (ReciprocityTheory.AnForm.A.regMax_thm (Fin B.n)).1 δ hδ

  have hΘlevi : ∀ x jA, ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' Θ.U x, ∀ w : Fin e → ℂ,
      0 ≤ levi (Θ.φ x ∘ (A.chart jA).symm) y w := by
    intro x jA y hy w
    by_cases hw : w = 0
    · subst hw; simp [levi_zero]
    · exact (hΘpos x jA y hy w hw).le

  have hloc : ∀ y₀ : X, ∃ (W : Set X) (k₀ : Fin B.n) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧
      W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧ (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ y ∈ W, F y = ReciprocityTheory.AnForm.A.regMax δ (fun j =>
        if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
    intro y₀
    obtain ⟨k₀, hk₀⟩ := hcov y₀
    obtain ⟨W, I, hWo, hyW, hWk, hk₀I, hWI, hrep⟩ := glue_loc_rep B h2 y₀ k₀ hk₀
    exact ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, fun y hy => hrep f η δ Mb hδ hδ1
      (fun j => (hη j).2.2.1) (fun j => (hη j).2.2.2) hMb hov y hy⟩

  have hbd : ∀ j, ∀ y ∈ chartBall B j (5 / 4), |F y - f j y| ≤ (4 * K' + 2) * δ := by
    intro j y hy
    have hup : ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) ≤ f j y + δ := by
      apply ReciprocityTheory.AnForm.A.tmax_le
      intro j'
      unfold glueArg
      split_ifs with h'
      · have h1 := (abs_le.1 (hov j' j y ⟨h', hy⟩)).2
        have h2' : 4 * δ * η j' y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) ((hη j').2.1 y).2
        linarith
      · have := (abs_le.1 (hMb j y hy)).1
        linarith
    obtain ⟨k, hk⟩ := hcov y
    have hk5 : y ∈ chartBall B k (5 / 4) := chartBall_mono B k (by norm_num) hk
    have hlow : f j y - δ ≤ ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) := by
      refine le_trans ?_ (ReciprocityTheory.AnForm.A.le_tmax _ k)
      have : glueArg B f η δ Mb k y = f k y := by
        simp [glueArg, hk5, (hη k).2.2.1 y hk]
      rw [this]
      have := (abs_le.1 (hov j k y ⟨hy, hk5⟩)).2
      linarith
    have h1 := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).1
    have h2' := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).2
    have hF' : F y = ReciprocityTheory.AnForm.A.regMax δ (fun j' => glueArg B f η δ Mb j' y) := rfl
    rw [abs_le]
    constructor <;> nlinarith

  have hsm : ∀ (jA : Fin A.n) (g : X → ℝ) (U : Set X), IsOpen U → A.SmoothOn U g →
      ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' U,
        ContDiffAt ℝ ∞ (g ∘ (A.chart jA).symm) y := fun jA g U hU hg y hy =>
    (hg jA).contDiffAt (((A.chart jA).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hsmη : ∀ (jA : Fin A.n) (j : Fin B.n), ∀ y ∈ (A.chart jA).target,
      ContDiffAt ℝ ∞ (η j ∘ (A.chart jA).symm) y := fun jA j y hy =>
    hsm jA (η j) Set.univ isOpen_univ (hηs j) y ⟨hy, trivial⟩
  refine ⟨?_, ?_, hbd⟩
  ·
    intro jA y' hy'
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    have hV : (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W ∈ nhds y' :=

      ((A.chart jA).isOpen_inter_preimage_symm hWo).mem_nhds ⟨hyt, hyW⟩
    let G : (Fin e → ℂ) → (Fin B.n → ℝ) := fun z j =>
      if j ∈ I then f j ((A.chart jA).symm z) + 4 * δ * η j ((A.chart jA).symm z)
      else f k₀ ((A.chart jA).symm z) + 4 * δ * η k₀ ((A.chart jA).symm z) - δ
    have hG : ContDiffAt ℝ ∞ G y' := by
      refine contDiffAt_pi.2 fun j => ?_
      by_cases hj : j ∈ I
      · simp only [G, hj, if_true]
        exact (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) y' ⟨hyt, hWI j hj hyW⟩).add
          (contDiffAt_const.mul (hsmη jA j y' hyt))
      · simp only [G, hj, if_false]
        exact ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
          ⟨hyt, hWI k₀ hk₀I hyW⟩).add (contDiffAt_const.mul (hsmη jA k₀ y' hyt))).sub
          contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞ (ReciprocityTheory.AnForm.A.regMax δ ∘ G) y' := hRM.1.contDiffAt.comp y' hG
    refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hV] with z hz
    exact hWeq _ hz.2
  ·
    intro c₀ x jA y' hy' w
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    have hyth : (A.chart jA).symm y' ∈ th.U x := hy'.2.1.1
    have hyΘ : (A.chart jA).symm y' ∈ Θ.U x := hy'.2.2
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    set c : ℝ := 2 * (4 * K' + 2) * δ with hc
    set V := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (W ∩ th.U x ∩ Θ.U x) with hVdef
    have hVo : IsOpen V :=
      (A.chart jA).isOpen_inter_preimage_symm ((hWo.inter (th.isOpen_U x)).inter (Θ.isOpen_U x))
    have hyV : y' ∈ V := ⟨hyt, ⟨hyW, hyth⟩, hyΘ⟩
    let P : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      th.φ x ((A.chart jA).symm z) + (if j ∈ I then f j ((A.chart jA).symm z)
        else f k₀ ((A.chart jA).symm z) - δ)
    let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      if j ∈ I then η j ((A.chart jA).symm z) else η k₀ ((A.chart jA).symm z)
    let R : (Fin e → ℂ) → ℝ := fun z => Θ.φ x ((A.chart jA).symm z)
    let u : Fin B.n → (Fin e → ℂ) → ℝ := fun j z => ((P j z + 4 * δ * Q j z) + c * R z) + c₀

    have hPs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (P j) z := by
      intro j z hz
      have hzt : z ∈ (A.chart jA).target := hz.1
      have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) z :=
        contDiffAt_of_isPotential A th hth x jA ⟨hzt, hz.2.1.2⟩
      by_cases hj : j ∈ I
      · simp only [P, hj, if_true]
        exact h1.add (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) z ⟨hzt, hWI j hj hz.2.1.1⟩)
      · simp only [P, hj, if_false]
        exact h1.add ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) z
          ⟨hzt, hWI k₀ hk₀I hz.2.1.1⟩).sub contDiffAt_const)
    have hQs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (Q j) z := by
      intro j z hz
      by_cases hj : j ∈ I
      · simp only [Q, hj, if_true]; exact hsmη jA j z hz.1
      · simp only [Q, hj, if_false]; exact hsmη jA k₀ z hz.1
    have hRs : ∀ z ∈ V, ContDiffAt ℝ ∞ R z := fun z hz =>
      contDiffAt_of_isPotential A Θ hΘ x jA ⟨hz.1, hz.2.2⟩
    have hus : ∀ j, ContDiffOn ℝ 2 (u j) V := by
      intro j z hz
      exact (((((hPs j z hz).add (contDiffAt_const.mul (hQs j z hz))).add
        (contDiffAt_const.mul (hRs z hz))).add contDiffAt_const).of_le (by norm_cast)).contDiffWithinAt

    have heq : ((th + LocPot.ofFun (fun y => F y + c₀) + Θ.rsmul c).φ x ∘ (A.chart jA).symm) =ᶠ[nhds y']
        (fun z => ReciprocityTheory.AnForm.A.regMax δ (fun j => u j z)) := by
      filter_upwards [hVo.mem_nhds hyV] with z hz
      have hF' := hWeq _ hz.2.1.1
      show th.φ x ((A.chart jA).symm z) + (F ((A.chart jA).symm z) + c₀) +
          c * Θ.φ x ((A.chart jA).symm z) = _
      rw [hF']
      set C0 : ℝ := th.φ x ((A.chart jA).symm z) + c * Θ.φ x ((A.chart jA).symm z) + c₀ with hC0
      have htr := hRM.2.2.2.2.2.2.1 (fun j => if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) C0
      have hu : (fun j => u j z) = (fun j => (if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) + C0) := by
        funext j
        by_cases hj : j ∈ I
        · simp only [u, P, Q, R, hj, if_true, hC0]; ring
        · simp only [u, P, Q, R, hj, if_false, hC0]; ring
      rw [hu, htr, hC0]
      ring
    rw [levi_congr heq w]
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm e (Fin B.n) δ V u hVo hδ hus y' hyV w 0 ?_
    intro j

    have hP2 := (hPs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hQ2 := (hQs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hR2 := (hRs y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hl1 : levi (u j) y' w = levi (P j) y' w + 4 * δ * levi (Q j) y' w + c * levi R y' w := by
      have e1 : levi (fun z => P j z + 4 * δ * Q j z) y' w =
          levi (P j) y' w + 4 * δ * levi (Q j) y' w := levi_add_smul (4 * δ) hP2 hQ2 w
      have e2 : levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w =
          levi (fun z => P j z + 4 * δ * Q j z) y' w + c * levi R y' w :=
        levi_add_smul c (hP2.add (contDiffAt_const.mul hQ2)) hR2 w
      have e3 : levi (fun z => ((P j z + 4 * δ * Q j z) + c * R z) +
            c₀ * (fun _ : Fin e → ℂ => (1 : ℝ)) z) y' w =
          levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w +
            c₀ * levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w :=
        levi_add_smul c₀ ((hP2.add (contDiffAt_const.mul hQ2)).add (contDiffAt_const.mul hR2))
          contDiffAt_const w
      have h00 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
      have hue : u j = fun z => ((P j z + 4 * δ * Q j z) + c * R z) +
          c₀ * (fun _ : Fin e → ℂ => (1 : ℝ)) z := by
        funext z; simp [u]
      rw [hue, e3, e2, e1, h00]; ring
    have hRl : 0 ≤ levi R y' w := hΘlevi x jA y' ⟨hyt, hyΘ⟩ w

    have hPl : 0 ≤ levi (P j) y' w := by
      by_cases hj : j ∈ I
      · have := hfp j x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI j hj hyW⟩ w
        have hPe : P j = (th + LocPot.ofFun (f j)).φ x ∘ (A.chart jA).symm := by
          funext z; simp only [P, hj, if_true]; rfl
        rw [hPe]; exact this
      · have := hfp k₀ x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI k₀ hk₀I hyW⟩ w
        have hg2 : ContDiffAt ℝ 2 ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) y' := by
          have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) y' :=
            contDiffAt_of_isPotential A th hth x jA ⟨hyt, hyth⟩
          exact (h1.add (hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
            ⟨hyt, hWI k₀ hk₀I hyW⟩)).of_le (by norm_cast)
        have hPe : P j = fun z => ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) z +
            (-δ) * (fun _ => (1 : ℝ)) z := by
          funext z; simp only [P, hj, if_false]; show _ = th.φ x _ + f k₀ _ + _; ring
        rw [hPe, levi_add_smul (-δ) hg2 contDiffAt_const w]
        have h0 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
        rw [h0]; linarith

    have hQl : 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
      have key : ∀ j', Q j = η j' ∘ (A.chart jA).symm → 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
        intro j' hQe
        have h0 := hCj j' x jA y' ⟨hyt, ⟨trivial, hyΘ⟩⟩ w
        have hQR : (LocPot.ofFun (η j') + Θ.rsmul (Cj j')).φ x ∘ (A.chart jA).symm =
            fun z => (η j' ∘ (A.chart jA).symm) z + Cj j' * R z := rfl
        rw [hQR, levi_add_smul (Cj j') (hsmη jA j' y' hyt |>.of_le (by norm_cast)) hR2 w] at h0
        rw [hQe]
        nlinarith [hK'ge j']
      by_cases hj : j ∈ I
      · exact key j (by funext z; simp [Q, hj])
      · exact key k₀ (by funext z; simp [Q, hj])
    rw [hl1]
    have : 0 ≤ 4 * δ * (levi (Q j) y' w + K' * levi R y' w) := by positivity
    have h2δ : 0 ≤ (4 * K' + 4) * δ * levi R y' w :=
      mul_nonneg (mul_nonneg (by linarith) hδ.le) hRl
    have hcv : c = 2 * (4 * K' + 2) * δ := hc
    rw [hcv]
    nlinarith

end Glue

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

open GroundTheory.Heights₂.Heights.AnalyticLimit (TendstoC2On)

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem glue_C2_local [T2Space X] (A B : FinHolAtlas e X) [Nonempty (Fin B.n)] (s : X → X → ℂ)
    (ph : X → ℝ) (hAB : A.Compatible B) (hcov : ∀ x, ∃ j, x ∈ chartBall B j 1)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hbd : IsClosed (bdry s)) (hph : A.SmoothOn (bdry s)ᶜ ph) (η : Fin B.n → X → ℝ)
    (hη : ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1)
    (K₀ t₀ : ℝ) (δ Mb : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ) (ht₀ : 0 < t₀)
    (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (H : ∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb t) ∧
      ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t)
    (hc : ∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm))
        (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t)
    (jA : Fin A.n) (z₀ : Fin e → ℂ)
    (hz₀ : z₀ ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (bdry s)ᶜ) :
    ∃ N ∈ 𝓝 z₀, TendstoC2On (fun t => (fun y => ReciprocityTheory.AnForm.A.regMax (δ t)
        (fun j => glueArg B (f t) η (δ t) (Mb t) j y) + K₀ * δ t) ∘ (A.chart jA).symm)
      (ph ∘ (A.chart jA).symm) N := by
  classical
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ t₀ := by
    filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht using ht
  have h2' : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  obtain ⟨k₀, hk₀⟩ := hcov ((A.chart jA).symm z₀)
  obtain ⟨W, I, hWo, hyW, hWk, hk₀I, hWI, hrep⟩ := glue_loc_rep B h2 _ k₀ hk₀
  set W' := W ∩ (bdry s)ᶜ with hW'def
  have hW'o : IsOpen W' := hWo.inter hbd.isOpen_compl
  set U := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W' with hUdef
  have hUo : IsOpen U := (A.chart jA).isOpen_inter_preimage_symm hW'o
  have hzU : z₀ ∈ U := ⟨hz₀.1, hyW, hz₀.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hUo.mem_nhds hzU)
  set N := closedBall z₀ (r / 2) with hNdef
  have hNU : N ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hNc : IsCompact N := isCompact_closedBall _ _
  refine ⟨N, closedBall_mem_nhds z₀ (half_pos hr), ?_⟩
  set p := ph ∘ (A.chart jA).symm with hp
  have hpC : ContDiffOn ℝ 2 p U :=
    ((hph jA).of_le h2').mono fun z hz => ⟨hz.1, hz.2.2⟩
  let b : Fin B.n → Fin B.n := fun j => if j ∈ I then j else k₀
  have hb : ∀ j, b j ∈ I := by
    intro j
    by_cases hj : j ∈ I
    · simpa [b, hj] using hj
    · simpa [b, hj] using hk₀I
  have hWb : ∀ j, W' ⊆ chartBall B (b j) (5 / 4) := fun j y hy => hWI _ (hb j) hy.1
  let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
    4 * η (b j) ((A.chart jA).symm z) - (if j ∈ I then 0 else 1)
  have hQ : ∀ j, ContDiffOn ℝ 2 (Q j) U := by
    intro j
    have h1 : ContDiffOn ℝ 2 (η (b j) ∘ (A.chart jA).symm) U :=
      (((hη (b j)).1 jA).of_le h2').mono fun z hz => ⟨hz.1, trivial⟩
    exact (contDiffOn_const.mul h1).sub contDiffOn_const
  have hsm : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ContDiffOn ℝ 2 (f t (b j) ∘ (A.chart jA).symm) U :=
    fun t h0 h1 j => (((H t h0 h1).2.2.1 (b j) jA).of_le h2').mono
      fun z hz => ⟨hz.1, hWb j hz.2⟩
  have hsmE : ∀ j, ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (f t (b j) ∘ (A.chart jA).symm) U :=
    fun j => ev.mono fun t ht => hsm t ht.1 ht.2 j
  have hA := fun j => chart_C2_convergence A B hAB jA (b j) s ph hbd hph hW'o (hWb j)
    Set.inter_subset_right (fun t => f t (b j))
    (ev.mono fun t ht => (H t ht.1 ht.2).2.2.1 (b j)) (hc (b j)) hNc hNU
  have hAdd := fun j => tendstoC2On_add_small hUo hNU hNc hδ (hQ j) (hsmE j) (hA j).1
  choose M hM using fun j => (hA j).2
  choose C hC using fun j => (hAdd j).2
  let u : ℝ → Fin B.n → (Fin e → ℂ) → ℝ := fun t j z =>
    (f t (b j) ∘ (A.chart jA).symm) z + δ t * Q j z
  let M' : ℝ := ∑ j, (|C j| + |M j|)
  have hM'0 : ∀ j, |C j| + |M j| ≤ M' := fun j =>
    Finset.single_le_sum (f := fun j => |C j| + |M j|) (fun _ _ => by positivity) (Finset.mem_univ j)
  have hgrad : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ N,
      ‖fderiv ℝ (u t j) x - fderiv ℝ p x‖ ≤ M' * δ t := by
    filter_upwards [ev, eventually_all.2 hM, eventually_all.2 hC] with t ht h1 h3 j x hx
    have hle := (H t ht.1 ht.2).1
    have hpos : 0 < δ t := ht.1.trans_le hle
    have a1 := h3 j x hx
    have a2 := h1 j x hx
    have a3 : C j * |δ t| ≤ |C j| * δ t := by
      rw [abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have a4 : M j * t ≤ |M j| * δ t :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) ht.1.le).trans
        (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
    have a5 : (|C j| + |M j|) * δ t ≤ M' * δ t := mul_le_mul_of_nonneg_right (hM'0 j) hpos.le
    calc ‖fderiv ℝ (u t j) x - fderiv ℝ p x‖
        = ‖(fderiv ℝ (u t j) x - fderiv ℝ (f t (b j) ∘ (A.chart jA).symm) x) +
            (fderiv ℝ (f t (b j) ∘ (A.chart jA).symm) x - fderiv ℝ p x)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ C j * |δ t| + M j * t := add_le_add a1 a2
      _ ≤ M' * δ t := by nlinarith
  have hratio : Tendsto (fun t => (M' * δ t) ^ 2 / δ t) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t => M' ^ 2 * δ t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hδ.const_mul (M' ^ 2)
    refine h0.congr' ?_
    filter_upwards [ev] with t ht
    have hpos : 0 < δ t := ht.1.trans_le (H t ht.1 ht.2).1
    field_simp
  have hucd : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ContDiffOn ℝ 2 (u t j) U :=
    fun t h0 h1 j => (hsm t h0 h1 j).add (contDiffOn_const.mul (hQ j))
  have hreg := GroundTheory.Heights₂.Heights.AnalyticLimit.RegularizedMaxConvergenceC2.proof (Fin B.n) U N p u δ
    (fun t => M' * δ t) hUo hNU hpC
    (ev.mono fun t ht => ⟨ht.1.trans_le (H t ht.1 ht.2).1, hucd t ht.1 ht.2⟩) hδ
    (fun j => (hAdd j).1) hgrad hratio
  have hevA : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2
      (fun x => ReciprocityTheory.AnForm.A.regMax (δ t) (fun j => u t j x) + δ t / 2) U := by
    filter_upwards [ev] with t ht
    have hpos : 0 < δ t := ht.1.trans_le (H t ht.1 ht.2).1
    exact (((ReciprocityTheory.AnForm.A.regMax_contDiff (ι := Fin B.n) hpos).of_le
      ReciprocityTheory.AnForm.A.two_le_inf).comp_contDiffOn (contDiffOn_pi.2 (hucd t ht.1 ht.2))).add
      contDiffOn_const
  have hfin := (tendstoC2On_add_small hUo hNU hNc hδ (Q := fun _ => K₀ - 1 / 2) contDiffOn_const
    hevA hreg).1
  refine tendstoC2On_congr hUo hNU ?_ hfin
  filter_upwards [ev] with t ht z hz
  obtain ⟨hle, hle1, -, hMb, hov⟩ := H t ht.1 ht.2
  have hpos : 0 < δ t := ht.1.trans_le hle
  have hr1 := hrep (f t) η (δ t) (Mb t) hpos hle1 (fun j => (hη j).2.2.1)
    (fun j => (hη j).2.2.2) hMb hov ((A.chart jA).symm z) hz.2.1
  have hu : (fun j => u t j z) = fun j => if j ∈ I then
      f t j ((A.chart jA).symm z) + 4 * δ t * η j ((A.chart jA).symm z)
      else f t k₀ ((A.chart jA).symm z) + 4 * δ t * η k₀ ((A.chart jA).symm z) - δ t := by
    funext j
    by_cases hj : j ∈ I
    · simp only [u, Q, b, hj, if_true, Function.comp_apply]; ring
    · simp only [u, Q, b, hj, if_false, Function.comp_apply]; ring
  simp only [Function.comp_apply]
  rw [hu, hr1]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

theorem regularization_glue_C2 : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (Θ th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ), A.Compatible B → (∀ x, ∃ j, x ∈ chartBall B j 1) → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsClosed (bdry s) → A.SmoothOn (bdry s)ᶜ ph → ∃ K : ℝ, 0 < K ∧ ∀ (t₀ : ℝ) (δ : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ), 0 < t₀ → Tendsto δ (𝓝[>] 0) (𝓝 0) → (∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧ (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧ (∃ Mb : ℝ, ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb) ∧ (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f t j))) ∧ ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t) → (∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm)) (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t) → ∃ F : ℝ → X → ℝ, (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * δ t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * δ t) ∧ IsRegFamilyC2 A s ph F := by
  intro e X _ _ _ A B Θ th s ph hAB hcov h2 hΘ hΘpos hth hbd hph
  obtain ⟨η, hη⟩ := glue_cutoff A B hAB h2
  by_cases hne : Nonempty (Fin B.n)
  swap
  · have hX : IsEmpty X := ⟨fun x => hne ⟨(hcov x).choose⟩⟩
    refine ⟨1, one_pos, fun t₀ δ f _ _ _ _ => ⟨fun _ _ => 0, fun t _ _ => ⟨?_, ?_, ?_⟩, ?_⟩⟩
    · exact fun k y _ => (hX.false ((A.chart k).symm y)).elim
    · exact fun x => (hX.false x).elim
    · exact fun j y _ => (hX.false y).elim
    · exact fun j => (hX.false ((A.chart j).symm 0)).elim
  obtain ⟨K₀, hK₀, hG⟩ := reg_glue_explicit A B Θ th hAB hcov h2 hΘ hΘpos hth η hη
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro t₀ δ f ht₀ hδ H hc
  have hMbE : ∀ t, ∃ Mb : ℝ, 0 < t → t ≤ t₀ →
      ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ t₀
    · obtain ⟨Mb, h⟩ := (H t ht.1 ht.2).2.2.2.1
      exact ⟨Mb, fun _ _ => h⟩
    · exact ⟨0, fun h1 h3 => (ht ⟨h1, h3⟩).elim⟩
  choose Mb hMb using hMbE
  refine ⟨fun t y => ReciprocityTheory.AnForm.A.regMax (δ t)
    (fun j => glueArg B (f t) η (δ t) (Mb t) j y) + K₀ * δ t, ?_, ?_⟩
  · intro t h0 h1
    obtain ⟨hle, hle1, hsm, -, hps, hov⟩ := H t h0 h1
    have hpos : 0 < δ t := h0.trans_le hle
    obtain ⟨s1, s2, s3⟩ := hG (δ t) (Mb t) (f t) hpos hle1 hsm (hMb t h0 h1) hps hov
    refine ⟨fun k => (s1 k).add contDiffOn_const, s2 _, fun j y hy => ?_⟩
    have := abs_le.1 (s3 j y hy)
    constructor <;> linarith [this.1, this.2]
  · intro jA K hKs hKc
    have hO : IsOpen ((A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (bdry s)ᶜ) :=
      (A.chart jA).isOpen_inter_preimage_symm hbd.isOpen_compl
    have hloc := fun z hz => glue_C2_local A B s ph hAB hcov h2 hbd hph η hη K₀ t₀ δ Mb f ht₀ hδ
      (fun t h0 h1 => ⟨(H t h0 h1).1, (H t h0 h1).2.1, (H t h0 h1).2.2.1, hMb t h0 h1,
        (H t h0 h1).2.2.2.2.2⟩) (fun j K' hK' hK'c => hc j K' hK' hK'c) jA z hz
    refine ⟨?_, ?_, ?_⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, h, -, -⟩ := hloc y hy
      exact ⟨N, hN, h⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, -, h, -⟩ := hloc y hy
      exact ⟨N, hN, h⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, -, -, h⟩ := hloc y hy
      exact ⟨N, hN, h⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.RefineAdaptedAtlasWithGradient
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem rLoc_rescale_bound {e : ℕ} (S : Finset (Fin e)) (m : Fin e → ℕ) (z₀ : Fin e → ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hz₀ : ‖z₀‖ < 1) (hfar : ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖) :
    ∃ c : ℝ, ∀ w ∈ closedBall (0 : Fin e → ℂ) 2, (∀ i ∈ S, z₀ i = 0 → w i ≠ 0) →
      |rLoc S m ((ρ : ℂ) • w + z₀) - rLoc (S.filter (fun i => z₀ i = 0)) m w| ≤ c := by
  classical
  set K : ℝ := Real.log (4 / ρ ^ 2) with hK
  refine ⟨∑ i ∈ S, (m i : ℝ) * K, fun w hw hne => ?_⟩
  have hw' : ∀ i, ‖w i‖ ≤ 2 := fun i =>
    (norm_le_pi_norm w i).trans (by simpa using hw)
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hone : (1 : ℝ) ≤ 1 / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]; nlinarith
  have hlog1 : Real.log (1 / ρ ^ 2) ≤ K :=
    Real.log_le_log (by positivity) (by
      apply div_le_div_of_nonneg_right (by norm_num) hρ2.le)
  have hlog0 : 0 ≤ Real.log (1 / ρ ^ 2) := Real.log_nonneg hone
  have hterm : ∀ i ∈ S, |(m i : ℝ) * Real.log (4 / ‖((ρ : ℂ) • w + z₀) i‖ ^ 2) -
      (if z₀ i = 0 then (m i : ℝ) * Real.log (4 / ‖w i‖ ^ 2) else 0)| ≤ (m i : ℝ) * K := by
    intro i hi
    have hm0 : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
    have hzi : ((ρ : ℂ) • w + z₀) i = (ρ : ℂ) * w i + z₀ i := by simp
    by_cases h0 : z₀ i = 0
    · have hwi : ‖w i‖ ≠ 0 := norm_ne_zero_iff.2 (hne i hi h0)
      have hwp : 0 < ‖w i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwi)
      have hn : ‖((ρ : ℂ) • w + z₀) i‖ = ρ * ‖w i‖ := by
        rw [hzi, h0, add_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      have hsplit : Real.log (4 / (ρ * ‖w i‖) ^ 2) =
          Real.log (4 / ‖w i‖ ^ 2) + Real.log (1 / ρ ^ 2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [if_pos h0, hn, hsplit, mul_add, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hlog1 hm0
    · have hfi := hfar i h0
      have hz1 : ‖z₀ i‖ < 1 := (norm_le_pi_norm z₀ i).trans_lt hz₀
      have hρw : ‖(ρ : ℂ) * w i‖ ≤ 2 * ρ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
        nlinarith [hw' i]
      have hlo : ρ ≤ ‖((ρ : ℂ) • w + z₀) i‖ := by
        rw [hzi]
        have h3 := norm_sub_le ((ρ : ℂ) * w i + z₀ i) ((ρ : ℂ) * w i)
        rw [add_sub_cancel_left] at h3
        linarith
      have hhi : ‖((ρ : ℂ) • w + z₀) i‖ ≤ 2 := by
        rw [hzi]
        have := norm_add_le ((ρ : ℂ) * w i) (z₀ i)
        linarith
      set t := ‖((ρ : ℂ) • w + z₀) i‖ with ht
      have ht0 : 0 < t := lt_of_lt_of_le hρ hlo
      have ht2 : 0 < t ^ 2 := by positivity
      have hA : 0 ≤ Real.log (4 / t ^ 2) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ ht2]; nlinarith
      have hB : Real.log (4 / t ^ 2) ≤ K := by
        apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_left (by norm_num) hρ2
        nlinarith
      rw [if_neg h0, sub_zero, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hB hm0
  have hdiff : rLoc S m ((ρ : ℂ) • w + z₀) - rLoc (S.filter (fun i => z₀ i = 0)) m w =
      ∑ i ∈ S, ((m i : ℝ) * Real.log (4 / ‖((ρ : ℂ) • w + z₀) i‖ ^ 2) -
        (if z₀ i = 0 then (m i : ℝ) * Real.log (4 / ‖w i‖ ^ 2) else 0)) := by
    unfold rLoc
    rw [Finset.sum_filter, add_sub_add_left_eq_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)

theorem fderiv_rescale_norm_le {e : ℕ} (f : (Fin e → ℂ) → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (z₀ w : Fin e → ℂ) :
    ‖fderiv ℝ (fun w => f ((ρ : ℂ) • w + z₀)) w‖ ≤ ‖fderiv ℝ f ((ρ : ℂ) • w + z₀)‖ := by
  have hne : ρ ≠ 0 := hρ.ne'
  let I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ) := ContinuousLinearEquiv.equivOfInverse
    (ρ • ContinuousLinearMap.id ℝ (Fin e → ℂ)) (ρ⁻¹ • ContinuousLinearMap.id ℝ (Fin e → ℂ))
    (fun x => by simp [smul_smul, hne]) (fun x => by simp [smul_smul, hne])
  have hI : ∀ u, I u = (ρ : ℂ) • u := by
    intro u
    ext i
    simp [I]
  have hfun : (fun w => f ((ρ : ℂ) • w + z₀)) = (fun u => f (u + z₀)) ∘ I := by
    funext u
    simp [hI]
  rw [hfun, I.comp_right_fderiv, fderiv_comp_add_right, hI]
  have hIn : ‖((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
    have : ((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ)) u = (ρ : ℂ) • u := hI u
    rw [this, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg u]
  calc _ ≤ ‖fderiv ℝ f ((ρ : ℂ) • w + z₀)‖ * ‖((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := by nlinarith [norm_nonneg (fderiv ℝ f ((ρ : ℂ) • w + z₀))]

theorem refine_local_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ)
    (hle : ∀ y, logNormSec L s y ≤ 0) (hAB : A.Compatible B)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hM : ∀ j, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
      (∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
      ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s →
        |rW L s ((B.chart j).symm y) - rLoc S m y| ≤ M)
    (hG : IsGradBound B L s ph C₅) (j : Fin B.n) (x : X) (hx : x ∈ (B.chart j).source)
    (hx1 : B.chart j x ∈ ball (0 : Fin e → ℂ) 1) :
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), (IsCompatChart A ψ ∧
      closedBall (0 : Fin e → ℂ) 2 ⊆ ψ.target ∧
      (∃ M' : ℝ, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
        (∀ y ∈ ψ.target, (ψ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, ψ.symm y ∉ bdry s →
          |rW L s (ψ.symm y) - rLoc S m y| ≤ M') ∧
      (∀ y ∈ ball (0 : Fin e → ℂ) (3 / 2), ψ.symm y ∉ bdry s →
        ‖fderiv ℝ (ph ∘ ψ.symm) y‖ ≤
          |C₅| * rW L s (ψ.symm y) ^ |C₅| * Real.exp (rW L s (ψ.symm y) / 2))) ∧
      x ∈ ψ.source ∧ ψ x ∈ ball (0 : Fin e → ℂ) 1 ∧ ψ.source ⊆ th.U x := by
  classical
  set c := B.chart j with hc
  set z₀ : Fin e → ℂ := c x with hz₀
  have hz₀1 : ‖z₀‖ < 1 := by simpa using hx1
  obtain ⟨S, m, hm, hb, hr⟩ := hM j
  have hOopen : IsOpen (c.target ∩ c.symm ⁻¹' th.U x) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (th.isOpen_U x)
  have hz₀O : z₀ ∈ c.target ∩ c.symm ⁻¹' th.U x :=
    ⟨c.map_source hx, by
      show c.symm (c x) ∈ th.U x
      rw [c.left_inv hx]; exact th.mem_U x⟩
  obtain ⟨r, hr0, hrO⟩ := Metric.isOpen_iff.1 hOopen z₀ hz₀O
  obtain ⟨ρ, hρ0, hρ8, hρr, hfar⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 3 * ρ ≤ r ∧
      ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖ := by
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖ := by
      refine Filter.eventually_all.2 fun i => ?_
      by_cases h : z₀ i = 0
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · have hp : 0 < ‖z₀ i‖ / 3 := by
          have := norm_pos_iff.2 h
          positivity
        filter_upwards [Ioo_mem_nhdsGT hp] with ρ hρ _
        have := hρ.2
        linarith
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Set.Ioo (0 : ℝ) (min (1 / 8) (r / 3)) :=
      Ioo_mem_nhdsGT (lt_min (by norm_num) (by positivity))
    obtain ⟨ρ, hρ, hev'⟩ := (h1.and hev).exists
    have ha := lt_of_lt_of_le hρ.2 (min_le_left _ _)
    have hb' := lt_of_lt_of_le hρ.2 (min_le_right _ _)
    exact ⟨ρ, hρ.1, ha.le, by linarith, hev'⟩
  have hs : IsOpen (c.source ∩ c ⁻¹' ball z₀ (3 * ρ)) :=
    c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have ha : ((ρ : ℂ))⁻¹ ≠ 0 := inv_ne_zero hρC
  set ψ : OpenPartialHomeomorph X (Fin e → ℂ) :=
    (c.restrOpen _ hs).transHomeomorph (pa_aff ((ρ : ℂ))⁻¹ ha z₀) with hψ
  have hinv : ∀ w, (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w = (ρ : ℂ) • w + z₀ := by
    intro w
    show (((ρ : ℂ))⁻¹)⁻¹ • w + z₀ = _
    rw [inv_inv]
  have hsymm : ∀ w, ψ.symm w = c.symm ((ρ : ℂ) • w + z₀) := by
    intro w
    show c.symm ((pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w) = _
    rw [hinv]
  have hnorm : ∀ w : Fin e → ℂ, ‖(ρ : ℂ) • w‖ = ρ * ‖w‖ := by
    intro w
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
  have hdist : ∀ w : Fin e → ℂ, ‖(ρ : ℂ) • w + z₀ - z₀‖ = ρ * ‖w‖ := by
    intro w
    rw [add_sub_cancel_right, hnorm]

  have htar1 : ∀ w : Fin e → ℂ, ‖w‖ < 3 → w ∈ ψ.target := by
    intro w hw
    have hzb : (ρ : ℂ) • w + z₀ ∈ ball z₀ (3 * ρ) := by
      rw [Metric.mem_ball, dist_eq_norm, hdist]
      nlinarith
    have hzT : (ρ : ℂ) • w + z₀ ∈ c.target := (hrO (ball_subset_ball hρr hzb)).1
    have hmem : (ρ : ℂ) • w + z₀ ∈ (c.restrOpen _ hs).target :=
      ⟨hzT, c.map_target hzT, by
        show c (c.symm ((ρ : ℂ) • w + z₀)) ∈ ball z₀ (3 * ρ)
        rw [c.right_inv hzT]
        exact hzb⟩
    show (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w ∈ (c.restrOpen _ hs).target
    rw [hinv]
    exact hmem
  have htar2 : ∀ w ∈ ψ.target, (ρ : ℂ) • w + z₀ ∈ c.target ∧
      (ρ : ℂ) • w + z₀ ∈ ball z₀ (3 * ρ) := by
    intro w hw
    have hw' : (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w ∈ (c.restrOpen _ hs).target := hw
    rw [hinv] at hw'
    obtain ⟨h1, -, h3⟩ := hw'
    refine ⟨h1, ?_⟩
    have h3' : c (c.symm ((ρ : ℂ) • w + z₀)) ∈ ball z₀ (3 * ρ) := h3
    rwa [c.right_inv h1] at h3'
  have hcl : closedBall (0 : Fin e → ℂ) 2 ⊆ ψ.target := fun w hw =>
    htar1 w (by
      have : ‖w‖ ≤ 2 := by simpa using hw
      linarith)

  have hbd : ∀ y ∈ ψ.target, (ψ.symm y ∈ bdry s ↔
      ∃ i ∈ S.filter (fun i => z₀ i = 0), y i = 0) := by
    intro w hw
    obtain ⟨hzT, hzb⟩ := htar2 w hw
    rw [hsymm, hb _ hzT]
    constructor
    · rintro ⟨i, hi, hzi⟩
      have hzi' : (ρ : ℂ) * w i + z₀ i = 0 := by simpa using hzi
      have h0 : z₀ i = 0 := by
        by_contra h0
        have h1 := hfar i h0
        have h2' : ‖z₀ i‖ ≤ ρ * ‖w‖ := by
          have h3 : z₀ i = -((ρ : ℂ) * w i) := eq_neg_of_add_eq_zero_right hzi'
          rw [h3, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w i) hρ0.le
        have h4 : ρ * ‖w‖ < 3 * ρ := by
          have := hzb
          rwa [Metric.mem_ball, dist_eq_norm, hdist] at this
        linarith
      refine ⟨i, Finset.mem_filter.2 ⟨hi, h0⟩, ?_⟩
      rw [h0, add_zero] at hzi'
      exact (mul_eq_zero.1 hzi').resolve_left hρC
    · rintro ⟨i, hi, hwi⟩
      obtain ⟨hiS, h0⟩ := Finset.mem_filter.1 hi
      exact ⟨i, hiS, by simp [hwi, h0]⟩
  obtain ⟨cc, hcc⟩ := rLoc_rescale_bound S m z₀ ρ hρ0 hρ8 hz₀1 hfar
  have hsmall : ∀ w : Fin e → ℂ, ‖w‖ ≤ 2 → ‖(ρ : ℂ) • w + z₀‖ < 3 / 2 := by
    intro w hw
    have h1 := norm_add_le ((ρ : ℂ) • w) z₀
    rw [hnorm] at h1
    nlinarith [norm_nonneg w]
  refine ⟨ψ, ⟨pa_compat_aff A _ (pa_compat_restr A _ (fun k => ⟨hAB.1 k j, hAB.2 j k⟩) _ hs) _ ha _,
    hcl, ⟨M + cc, S.filter (fun i => z₀ i = 0), m,
      fun i hi => hm i (Finset.mem_filter.1 hi).1, hbd, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw hnb
    have hw2 : ‖w‖ ≤ 2 := by simpa using hw
    have hz2 : (ρ : ℂ) • w + z₀ ∈ closedBall (0 : Fin e → ℂ) 2 := by
      have := hsmall w hw2
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have hne : ∀ i ∈ S, z₀ i = 0 → w i ≠ 0 := fun i hi h0 hwi =>
      hnb ((hbd w (hcl hw)).2 ⟨i, Finset.mem_filter.2 ⟨hi, h0⟩, hwi⟩)
    rw [hsymm] at hnb ⊢
    have h1 := hr _ hz2 hnb
    have h3 := hcc w hw hne
    rw [abs_le] at h1 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
  · intro w hw hnb
    have hw32 : ‖w‖ < 3 / 2 := by simpa using hw
    have hz : (ρ : ℂ) • w + z₀ ∈ ball (0 : Fin e → ℂ) (3 / 2) := by
      simpa using hsmall w (by linarith)
    have hfun : ph ∘ ψ.symm = fun w => (ph ∘ c.symm) ((ρ : ℂ) • w + z₀) := by
      funext u
      simp [hsymm]
    rw [hfun]
    rw [hsymm] at hnb ⊢
    have h1 := fderiv_rescale_norm_le (ph ∘ c.symm) ρ hρ0 (by linarith) z₀ w
    have h3 : ‖fderiv ℝ (ph ∘ c.symm) ((ρ : ℂ) • w + z₀)‖ ≤ _ := hG j _ hz hnb
    refine (h1.trans h3).trans ?_
    set R := rW L s (c.symm ((ρ : ℂ) • w + z₀)) with hR
    have hR1 : 1 ≤ R := by
      have h4 : Real.exp 1 ≤ R := rW_ge L s hle _
      have h5 : (1 : ℝ) ≤ Real.exp 1 := by
        simpa using Real.add_one_le_exp (0 : ℝ) |>.trans (Real.exp_le_exp.2 zero_le_one)
      linarith
    have hR0 : 0 ≤ R := by linarith
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hR1 (le_abs_self _))
      (Real.rpow_nonneg hR0 _) (abs_nonneg _)
  · exact ⟨hx, hx, mem_ball_self (by positivity)⟩
  · have : ψ x = 0 := by
      show ((ρ : ℂ))⁻¹ • (c x - z₀) = 0
      simp [hz₀]
    rw [this]
    exact mem_ball_self one_pos
  · intro y hy
    have hy' : y ∈ (c.restrOpen _ hs).source := hy
    have h1 : y ∈ c.source := hy'.1
    have h3 : c y ∈ ball z₀ (3 * ρ) := hy'.2.2
    have h4 := (hrO (ball_subset_ball hρr h3)).2
    have h5 : c.symm (c y) ∈ th.U x := h4
    rwa [c.left_inv h1] at h5

theorem refine_adapted_atlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ : ℝ), (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → IsGradBound B L s ph C₅ → ∃ (B' : FinHolAtlas e X) (x : Fin B'.n → X), IsAdaptedAtlas A B' L s ∧ IsGradBound B' L s ph |C₅| ∧ ∀ j, (B'.chart j).source ⊆ th.U (x j) := by
  intro e X _ _ _ A B L th s ph C₅ hle hAd hG
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd
  have hcov₀ := hcov
  choose jf hj hj1 using hcov₀
  have hgood := fun x : X => refine_local_chart A B L th s ph C₅ M hle hAB h2 hM hG (jf x) x (hj x) (hj1 x)
  choose φ hφg hφx hφ1 hφU using hgood
  have hU : ∀ x, φ x ⁻¹' ball 0 1 ∩ (φ x).source ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨hφ1 x, hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov' : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B', hAB', h1, h3⟩ := atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => (hφg _).1) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov' x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  choose idx hidx using h3
  have hMx := fun x => (hφg x).2.2.1
  choose Mf hMf using hMx
  refine ⟨B', fun j => (t.equivFin.symm (idx j) : X), ⟨hAB', fun j => ?_, fun x => ?_,
    ∑ i, |Mf (t.equivFin.symm i : X)|, fun j => ?_⟩, fun j => ?_, fun j => ?_⟩
  · rw [hidx j]
    exact (hφg _).2.1
  · obtain ⟨y, hy, hx⟩ := hcov' x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]
      simpa using hx.2
    · rw [hj]
      simpa using hx.1
  · obtain ⟨S, m, hm, hb, hr⟩ := hMf (t.equivFin.symm (idx j) : X)
    refine ⟨S, m, hm, ?_, ?_⟩
    · rw [hidx j]
      exact hb
    · rw [hidx j]
      intro y hy hnb
      refine (hr y hy hnb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun i => |Mf (t.equivFin.symm i : X)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (idx j))
  · rw [hidx j]
    exact (hφg _).2.2.2
  · rw [hidx j]
    exact hφU _

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviNonnegInChartOfPsh
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_nonneg_of_compat_fixedBase : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B →
    IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) →
    (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    ∀ w : Fin e → ℂ,
    0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  intro e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w
  have hp : (B.chart j).symm y ∈ (B.chart j).source := (B.chart j).map_target hy.1
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y := hAB.2 j k y ⟨hy.1, hk⟩
  have hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y :=
    (A.chart k).left_inv hk
  have htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target := (A.chart k).map_source hk
  have hthU : (B.chart j).symm y ∈ th.U x₀ := hsrc hp
  have hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀) :=
    (A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)
  have hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀ :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩
  have hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2
  have hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2
  have hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z))
      ((A.chart k ∘ (B.chart j).symm) y) := hC1.add hC2
  have hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y]
      ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘
        (A.chart k ∘ (B.chart j).symm)) := by
    have h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source :=
      ((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  rw [levi_congr hev w, levi_comp w hτ hC]
  exact hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _

end GlobalTheory.CompanionTheory.LeviChart
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartLeviNonneg
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.PshBack

theorem smoothOn_isPshOn_chartBack : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (x₀ : X) (j : Fin B.n) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → ℝ),
    A.Compatible B → IsPotential A th → (B.chart j).source ⊆ th.U x₀ → IsOpen V →
    V ⊆ (B.chart j).target → ContDiffOn ℝ ∞ g V →
    (∀ z ∈ V, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z' => th.φ x₀ ((B.chart j).symm z') + g z') z w) →
    A.SmoothOn ((B.chart j).source ∩ B.chart j ⁻¹' V) (g ∘ B.chart j) ∧
      IsPshOn A ((B.chart j).source ∩ B.chart j ⁻¹' V) (th + LocPot.ofFun (g ∘ B.chart j)) := by
  intro e X _ A B th x₀ j V g hAB hth hsrc hV hVt hg hlevi
  have hτ : ∀ (k : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart k).target →
      (A.chart k).symm y ∈ (B.chart j).source →
      AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := fun k y hy hp => hAB.1 k j y ⟨hy, hp⟩
  refine ⟨fun k y hy => ?_, fun x k y hy w => ?_⟩
  · obtain ⟨hyt, hp, hpV⟩ := hy
    have h1 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hpV)
    have h2 : ContDiffAt ℝ ∞ (B.chart j ∘ (A.chart k).symm) y :=
      ((hτ k y hyt hp).contDiffAt (n := ∞)).restrict_scalars ℝ
    exact (h1.comp y h2).contDiffWithinAt
  · obtain ⟨hyt, ⟨hpx, -⟩, hp, hpV⟩ := hy
    have hτy : AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := hτ k y hyt hp
    obtain ⟨W, hW, hpW, G, hG, hGe⟩ := hth.2 x x₀ ((A.chart k).symm y) ⟨hpx, hsrc hp⟩
    have hGa : AnalyticAt ℂ (G ∘ (A.chart k).symm) y := hG k y ⟨hyt, hpW⟩
    let h : (Fin e → ℂ) → ℝ := fun z' => th.φ x₀ ((B.chart j).symm z') + g z'
    have hB : B.SmoothOn (th.U x₀) (th.φ x₀) :=
      smoothOn_of_compatible hAB (th.isOpen_U x₀) (hth.1 x₀)
    have hτyV : (B.chart j ∘ (A.chart k).symm) y ∈ V := hpV
    have hh : ContDiffAt ℝ 2 h ((B.chart j ∘ (A.chart k).symm) y) := by
      have hmem : (B.chart j ∘ (A.chart k).symm) y ∈
          (B.chart j).target ∩ (B.chart j).symm ⁻¹' th.U x₀ := by
        refine ⟨hVt hτyV, ?_⟩
        show (B.chart j).symm (B.chart j ((A.chart k).symm y)) ∈ th.U x₀
        rw [(B.chart j).left_inv hp]
        exact hsrc hp
      have h1 : ContDiffAt ℝ ∞ (th.φ x₀ ∘ (B.chart j).symm) ((B.chart j ∘ (A.chart k).symm) y) :=
        (hB j).contDiffAt
          (((B.chart j).isOpen_inter_preimage_symm (th.isOpen_U x₀)).mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hτyV)
      exact (h1.add h2).of_le (by norm_cast)
    have hhτ : ContDiffAt ℝ 2 (h ∘ (B.chart j ∘ (A.chart k).symm)) y :=
      hh.comp y ((hτy.contDiffAt).restrict_scalars ℝ)
    have hGre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart k).symm) y').re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y ((hGa.contDiffAt).restrict_scalars ℝ)
    have hopen : IsOpen ((A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source)) :=
      (A.chart k).isOpen_inter_preimage_symm
        (((hW.inter (th.isOpen_U x)).inter (th.isOpen_U x₀)).inter (B.chart j).open_source)
    have hymem : y ∈ (A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source) :=
      ⟨hyt, ⟨⟨hpW, hpx⟩, hsrc hp⟩, hp⟩
    have hev : ((th + LocPot.ofFun (g ∘ B.chart j)).φ x ∘ (A.chart k).symm) =ᶠ[𝓝 y]
        (fun y' => (h ∘ (B.chart j ∘ (A.chart k).symm)) y' +
          1 * ((G ∘ (A.chart k).symm) y').re) := by
      filter_upwards [hopen.mem_nhds hymem] with y' hy'
      obtain ⟨-, ⟨⟨hW', hx'⟩, hx0'⟩, hs'⟩ := hy'
      have hd := hGe _ ⟨⟨hW', hx'⟩, hx0'⟩
      change th.φ x ((A.chart k).symm y') + g (B.chart j ((A.chart k).symm y')) =
        th.φ x₀ ((B.chart j).symm (B.chart j ((A.chart k).symm y'))) +
          g (B.chart j ((A.chart k).symm y')) + 1 * (G ((A.chart k).symm y')).re
      rw [(B.chart j).left_inv hs']
      linarith
    have e1 := levi_add_smul (f := h ∘ (B.chart j ∘ (A.chart k).symm))
      (g := fun y' => ((G ∘ (A.chart k).symm) y').re) (z := y) 1 hhτ hGre w
    rw [levi_congr hev w, e1, levi_re_analytic hGa w, levi_comp w hτy hh]
    have := hlevi _ hτyV (fderiv ℂ (B.chart j ∘ (A.chart k).symm) y w)
    simp only [mul_zero, add_zero]
    exact this

end GlobalTheory.CompanionTheory.Metric.PshBack
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBoundTransferBetweenRadii
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.BoundConv

theorem bound_conv_local (C₅ M : ℝ) : ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) := by
  set A := |C₅| with hA
  set M' := |M| with hM'
  have hA0 : 0 ≤ A := abs_nonneg _
  have hM0 : 0 ≤ M' := abs_nonneg _
  have hB1 : 1 ≤ (1 + M') ^ A := Real.one_le_rpow (by linarith) hA0
  have hE1 : 1 + M' ≤ Real.exp M' := by linarith [Real.add_one_le_exp M']
  have hE1' : 1 ≤ Real.exp M' := Real.one_le_exp hM0
  set K := A * (1 + M') ^ A * Real.exp M' with hK
  have hK0 : 0 ≤ K := by positivity
  have hKA : A ≤ K := by
    have : A * 1 * 1 ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1' (by norm_num) (by positivity)
    simpa using this
  have hKA' : A * (1 + M') ≤ K := by
    have : A * 1 * (1 + M') ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1 (by linarith) (by positivity)
    simpa using this
  refine ⟨K, hK0, ?_⟩
  intro x y p d hx hy hxy
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hy1 : 1 ≤ y := le_trans he1 hy
  have hx1 : 1 ≤ x := le_trans he1 hx
  have hlogy : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hy
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  have hxle : x ≤ y + M' := by
    have := (abs_le.mp (le_trans hxy (le_abs_self M))).2
    linarith
  have hxle2 : x ≤ y * (1 + M') := by nlinarith
  constructor
  · intro hp1 hp2
    refine ⟨?_, le_trans hp2 (le_trans (le_abs_self C₅) hKA)⟩
    rcases le_or_gt C₅ 0 with hC | hC
    · have h1 : 0 ≤ -C₅ * Real.log x := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ K * Real.log y := mul_nonneg hK0 (by linarith)
      linarith
    · have hAC : A = C₅ := abs_of_pos hC
      have hl1 : Real.log x ≤ Real.log (y * (1 + M')) := Real.log_le_log (by linarith) hxle2
      rw [Real.log_mul (by linarith) (by linarith)] at hl1
      have hl2 : Real.log (1 + M') ≤ M' := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + M' by linarith); linarith
      have hl3 : Real.log x ≤ Real.log y * (1 + M') := by nlinarith
      have hl4 : C₅ * Real.log x ≤ C₅ * (1 + M') * Real.log y := by
        have := mul_le_mul_of_nonneg_left hl3 hC.le; linarith
      have hl5 : C₅ * (1 + M') * Real.log y ≤ K * Real.log y :=
        mul_le_mul_of_nonneg_right (by rw [← hAC]; exact hKA') (by linarith)
      linarith
  · intro hd
    have h1 : x ^ A ≤ (y * (1 + M')) ^ A := Real.rpow_le_rpow (by linarith) hxle2 hA0
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : Real.exp (x / 2) ≤ Real.exp (y / 2) * Real.exp M' := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h3 : y ^ A ≤ y ^ K := Real.rpow_le_rpow_of_exponent_le hy1 hKA
    have hxA : 0 ≤ x ^ A := Real.rpow_nonneg (by linarith) _
    have hyK : 0 ≤ y ^ K := Real.rpow_nonneg (by linarith) _
    have hB0 : 0 ≤ (1 + M') ^ A := by linarith
    calc d ≤ A * x ^ A * Real.exp (x / 2) := hd
      _ ≤ A * (y ^ A * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hA0) h2 (Real.exp_pos _).le
          positivity
      _ ≤ A * (y ^ K * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hB0) hA0
      _ = K * y ^ K * Real.exp (y / 2) := by rw [hK]; ring

theorem bound_conv : ∀ (C₅ M : ℝ), ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) :=
  bound_conv_local

end GlobalTheory.CompanionTheory.Metric.BoundConv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem regGlobalStatement_holds : RegGlobalStatement := by
  intro e X _ _ _ A B Θ L s n m W hΘ hΘpos hL hS hSNC hs hAd th ph C₅ hSW hGB
  obtain ⟨B', x, hAd', hGB', hsrc⟩ := GlobalTheory.CompanionTheory.Ar.Giv.refine_adapted_atlas A B L th s ph C₅ hs hAd hGB
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd'
  choose S mm hm1 hbd hrl using hM
  have hcl : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨hth, hphs, hpsh, hb⟩ := hSW
  obtain ⟨C₅', hC₅'0, hconv⟩ := GlobalTheory.CompanionTheory.Metric.BoundConv.bound_conv C₅ M
  obtain ⟨hlogd, hmono, hle, htend, hsmall, hmin⟩ := GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics
  have hrWge : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hball : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      z ∈ (B'.chart j).target ∧ (B'.chart j).symm z ∉ bdry s := by
    intro j z hz
    have hzt : z ∈ (B'.chart j).target := h2 j (ball_subset_closedBall hz.1)
    exact ⟨hzt, fun hzb => hz.2 ((hbd j z hzt).1 hzb)⟩
  have hq : ∀ j, ContDiffOn ℝ ∞ (fun z => th.φ (x j) ((B'.chart j).symm z)) (ball (0 : Fin e → ℂ) 2) :=
    fun j => (smoothOn_of_compatible hAB (th.isOpen_U (x j)) (hth.1 (x j)) j).mono fun z hz =>
      ⟨h2 j (ball_subset_closedBall hz),
        hsrc j ((B'.chart j).map_target (h2 j (ball_subset_closedBall hz)))⟩
  have hphj : ∀ j, ContDiffOn ℝ ∞ (ph ∘ (B'.chart j).symm)
      (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j)) :=
    fun j => (smoothOn_of_compatible hAB hcl.isOpen_compl hphs j).mono fun z hz => hball j z hz
  have hlevi : ∀ j, ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j))
      (fun z => (fun z => th.φ (x j) ((B'.chart j).symm z)) z + (ph ∘ (B'.chart j).symm) z) := by
    intro j
    refine ⟨(((hq j).mono Set.diff_subset).add (hphj j)).of_le h2le, fun z hz w => ?_⟩
    exact GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase A B' th ph (bdry s)ᶜ (x j) j hAB hth hcl.isOpen_compl hphs hpsh (hsrc j) z (hball j z hz) w
  have hbnd : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      -C₅' * Real.log (rLoc (S j) (mm j) z) ≤ (ph ∘ (B'.chart j).symm) z ∧
        (ph ∘ (B'.chart j).symm) z ≤ C₅' := by
    intro j z hz
    obtain ⟨-, hzb⟩ := hball j z hz
    have hr := hrl j z (ball_subset_closedBall hz.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz.1)
    exact (hconv _ _ (ph ((B'.chart j).symm z)) 0 (hrWge _) hrl' hr).1 (hb _ hzb).1 (hb _ hzb).2
  have hgrad : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      ‖fderiv ℝ (ph ∘ (B'.chart j).symm) z‖ ≤
        C₅' * rLoc (S j) (mm j) z ^ C₅' * Real.exp (rLoc (S j) (mm j) z / 2) := by
    intro j z hz
    have hz2 : z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j) :=
      ⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩
    obtain ⟨-, hzb⟩ := hball j z hz2
    have hr := hrl j z (ball_subset_closedBall hz2.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz2.1)
    exact (hconv _ _ 0 _ (hrWge _) hrl' hr).2 (hGB' j z hz.1 hzb)
  have hch := fun j => GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart e (S j) (mm j) (fun z => th.φ (x j) ((B'.chart j).symm z))
    (ph ∘ (B'.chart j).symm) C₅' M (hm1 j) (hq j) (hphj j) (hlevi j) (hbnd j) (hgrad j)
  choose Cj tj g hCj1 htj0 htje hgt hgC2 using hch

  obtain ⟨C', t', ht'0, hcmp⟩ := GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare A B' L th s ph C₅ M x S mm hAB h2 hsrc hs hcl hbd hrl
    ⟨hth, hphs, hpsh, hb⟩
  set Cm : ℝ := 1 + ∑ j, |Cj j| with hCmdef
  have hCm : ∀ j, Cj j ≤ Cm := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2' := le_abs_self (Cj j)
    linarith
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ ∑ j, |Cj j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Cl : ℝ := |C'| + Cm with hCldef
  have hCl1 : 1 ≤ Cl := by have := abs_nonneg C'; linarith
  have hClj : ∀ j, Cj j ≤ Cl := fun j => by have := abs_nonneg C'; linarith [hCm j]
  obtain ⟨a, ha0, ha⟩ := hsmall Cl
  obtain ⟨tm, htm0, htm⟩ := hmin B'.n tj htj0
  set t₀ : ℝ := min (min tm t') (min a (Real.exp (-Real.exp 1))) with ht₀def
  have ht₀0 : 0 < t₀ := lt_min (lt_min htm0 ht'0) (lt_min ha0 (Real.exp_pos _))
  have ht₀j : ∀ j, t₀ ≤ tj j := fun j => ((min_le_left _ _).trans (min_le_left _ _)).trans (htm j)
  have ht₀' : t₀ ≤ t' := (min_le_left _ _).trans (min_le_right _ _)
  have ht₀a : t₀ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have ht₀e : t₀ ≤ Real.exp (-Real.exp 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hLL : ∀ t, 0 < t → t ≤ t₀ → 0 ≤ Real.log (Real.log (1 / t)) := fun t ht htt => by
    have := (log_inv_bounds ht (htt.trans ht₀e)).2; linarith

  have hy54 : ∀ j, ∀ y ∈ chartBall B' j (5 / 4), B'.chart j y ∈ ball (0 : Fin e → ℂ) (5 / 4) ∧
      B'.chart j y ∈ closedBall (0 : Fin e → ℂ) 2 ∧ (B'.chart j).symm (B'.chart j y) = y := by
    intro j y hy
    exact ⟨hy.2, ball_subset_closedBall (ball_subset_ball (by norm_num) hy.2), (B'.chart j).left_inv hy.1⟩
  have hsand : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) y + g j t (B'.chart j y) ∧
        th.φ (x j) y + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := by
    intro t ht htt j y hy
    obtain ⟨hz, -, hsy⟩ := hy54 j y hy
    have h := ((hgt j t ht (htt.trans (ht₀j j))).2.2.2.2.1 (B'.chart j y) hz)
    have h' : polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ∧
        th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := h
    rw [hsy] at h'
    exact h'
  have hloc : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ (g j t ∘ B'.chart j) y ∧
        (y ∉ bdry s → ph y ≤ (g j t ∘ B'.chart j) y ∧
          (rW L s y ≤ Real.log (1 / t) → (g j t ∘ B'.chart j) y ≤ ph y + t ^ ((1 : ℝ) / 3))) := by
    intro t ht htt j y hy
    obtain ⟨hz, hz2, hsy⟩ := hy54 j y hy
    obtain ⟨-, -, hgb, hgn, -, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    obtain ⟨hb1, hb2⟩ := hgb _ hz
    have hll := hLL t ht htt
    refine ⟨hb1.trans (hClj j), le_trans ?_ hb2, fun hyb => ?_⟩
    · have := mul_le_mul_of_nonneg_right (hClj j) hll
      show -Cl * _ ≤ -Cj j * _
      linarith
    · have hzt : B'.chart j y ∈ (B'.chart j).target := h2 j hz2
      have hzc : B'.chart j y ∉ ReciprocityTheory.AnForm.A.coordDiv (S j) := fun hc =>
        hyb (hsy ▸ (hbd j _ hzt).2 hc)
      obtain ⟨hn1, hn2⟩ := hgn _ ⟨hz, hzc⟩
      have hr := hrl j _ hz2 (by rw [hsy]; exact hyb)
      rw [hsy] at hr
      simp only [Function.comp_apply, hsy] at hn1 hn2 ⊢
      refine ⟨hn1, fun hrw => hn2 ?_⟩
      have := (abs_le.1 hr).1
      linarith
  have hmono' : ∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ (g j t' ∘ B'.chart j) y + epsT Cl t' := by
    intro t t'' ht htt' ht'' j y hy
    obtain ⟨hz, -, -⟩ := hy54 j y hy
    have h := (hgt j t ht ((htt'.trans ht'').trans (ht₀j j))).2.2.2.2.2 t'' htt' (ht''.trans (ht₀j j)) _ hz
    have := epsT_le_epsT (hClj j) (ht.trans_le htt') (ht''.trans ht₀e)
    simp only [Function.comp_apply]
    linarith

  obtain ⟨K, hK0, hgl⟩ := GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 A B' Θ th s ph hAB hcov h2 hΘ hΘpos hth hcl hphs
  have hback : ∀ t, 0 < t → t ≤ t₀ → ∀ j, A.SmoothOn (chartBall B' j (5 / 4)) (g j t ∘ B'.chart j) ∧
      IsPshOn A (chartBall B' j (5 / 4)) (th + LocPot.ofFun (g j t ∘ B'.chart j)) := by
    intro t ht htt j
    obtain ⟨hgs, hglevi, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    exact GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack A B' th (x j) j (ball (0 : Fin e → ℂ) (5 / 4)) (g j t) hAB hth (hsrc j) isOpen_ball
      (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))) hgs hglevi.2
  have hov : ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B' j (5 / 4) ∩ chartBall B' k (5 / 4),
      |(g j t ∘ B'.chart j) y - (g k t ∘ B'.chart k) y| ≤ epsT Cl t := by
    intro t ht htt j k y hy
    obtain ⟨sj1, sj2⟩ := hsand t ht htt j y hy.1
    obtain ⟨sk1, sk2⟩ := hsand t ht htt k y hy.2
    have hc := abs_le.1 (hcmp t ht (htt.trans ht₀') j k y hy)
    have hte := htt.trans ht₀e
    have e1 := epsT_le_epsT (hCm j) ht hte
    have e2 := epsT_le_epsT (hCm k) ht hte
    have e3 := epsT_le_epsT (le_abs_self C') ht hte
    have e4 : epsT Cl t = epsT |C'| t + epsT Cm t := by
      simp only [hCldef, epsT]; ring
    simp only [Function.comp_apply]
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨F, hF, hFC2⟩ := hgl t₀ (epsT Cl) (fun t j => g j t ∘ B'.chart j) ht₀0 (htend Cl)
    (fun t ht htt => ⟨hle Cl t hCl1 ht (htt.trans ht₀e), ha t ht (htt.trans ht₀a),
      fun j => (hback t ht htt j).1,
      ⟨Cl + Cl * Real.log (Real.log (1 / t)), fun j y hy => by
        obtain ⟨h1, h2', -⟩ := hloc t ht htt j y hy
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ Cl) (hLL t ht htt)
        rw [abs_le]; constructor <;> linarith⟩,
      fun j => (hback t ht htt j).2, hov t ht htt⟩)
    (fun j K' hK' hK'c => by
      have hsub : K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
        intro z hz
        have hzt : z ∈ (B'.chart j).target :=
          h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1))
        exact ⟨(hK' hz).1, fun hc => (hK' hz).2 ((hbd j z hzt).2 hc)⟩
      exact GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback (B'.chart j) (g j) (ph ∘ (B'.chart j).symm) K'
        (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1)))
        (hgC2 j K' hsub hK'c))
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Ar.RegFin.isRegFamily_of_glue A B' Θ L th s ph C₅ K Cl t₀ (fun t j => g j t ∘ B'.chart j) F hΘ hΘpos hth hs hcov
    (fun y hy => (hb y hy).1) hK0 hCl1 ht₀0 ht₀e hF hloc hmono'
  exact ⟨C, t₀, F, hC, hFC2⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHoldsStatement
open ReciprocityTheory.AnForm.P
theorem _root_.GlobalTheory.T.global_regularization_statement_holds : RegGlobalStatement :=
  GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem prov_an : Prov.An :=
  ⟨GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds, GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds,
    GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHoldsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_provision_holds : Prov.An := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.prov_an | exact GlobalTheory.CompanionTheory.Ar.Link.prov_an | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.prov_an <;> assumption)
end
end

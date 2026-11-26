module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroup
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorsQF

variable {X : Scheme.{0}} (G : Over X) [GrpObj G]

theorem pow_eq_one_of_res {A B : Scheme.{0}} (u : A ⟶ B) [Epi u] (ξ : B ⟶ X) (y : Over.mk ξ ⟶ G) (n : ℕ)
    (g : Over.mk (u ≫ ξ) ⟶ G) (hg : g.left = u ≫ y.left) (h : g ^ n = 1) : y ^ n = 1 := by
  let f : Over.mk (u ≫ ξ) ⟶ Over.mk ξ := Over.homMk u rfl
  have e : g = f ≫ y := by ext1; simpa [f] using hg
  have h1 : f ≫ y ^ n = f ≫ 1 := by rw [comp_pow, ← e, h, comp_one]
  ext1
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  exact (cancel_epi u).1 h2

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  have : Flat (spMap a) := by
    rw [spMap, Flat.SpecMap_iff]
    letI := a.toAlgebra
    exact (RingHom.flat_algebraMap_iff (R := K) (S := L)).2 inferInstance
  have : Surjective (spMap a) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨z, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact Flat.epi_of_flat_of_surjective _

theorem torsion_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (X : Scheme.{0})
    (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (n : ℕ), IsSemiAbelian G → 0 < n →
    FullTorsion G (spMap (algebraMap R (FractionRing R)) ≫ x) n →
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Q : BT.QFGroup R T) (i : Q.G.left ⟶ G.left),
      Q.IsTorsionAlong G x n i := by
  intro R _ _ _ _ X G _ x n hG hn hF
  have := hG.comm
  let ξ : Sp (FractionRing R) ⟶ X := spMap (algebraMap R (FractionRing R)) ≫ x
  let T : Subgroup (Over.mk ξ ⟶ G) := (powMonoidHom n).ker
  have hT : ∀ y : T, (y : Over.mk ξ ⟶ G) ^ n = 1 := fun y => MonoidHom.mem_ker.1 y.2
  have hfin : Finite T := by
    let L := AlgebraicClosure (FractionRing R)
    let a : FractionRing R →+* L := algebraMap (FractionRing R) L
    haveI := epi_spMap a
    let t : Sp L ⟶ X := spMap a ≫ ξ
    have h0 := GlobalTheory.finite_torsion_semiAbelian L ((Over.pullback t).obj G) (IsSemiAbelian.pullback t G hG) n hn
    have h1 : Finite {g : Over.mk t ⟶ G // g ^ n = 1} :=
      GlobalTheory.FewZeros.finite_torsion_of_mulEquiv
        (GlobalTheory.TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp L))) t (Category.id_comp t)) n h0
    let f : Over.mk t ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
    let φ : T → {g : Over.mk t ⟶ G // g ^ n = 1} := fun y => ⟨f ≫ y.1, by rw [← comp_pow, hT y, comp_one]⟩
    refine Finite.of_injective φ fun y z e => ?_
    have e1 := congrArg (fun w => (w.1 : Over.mk t ⟶ G).left) e
    simp only [φ, f, Over.comp_left, Over.homMk_left] at e1
    exact Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap a)).1 e1))
  obtain ⟨Γ, i, h, -⟩ := GlobalTheory.T.torsion_embedding_geometric_points R T X G hG x n hn T.subtype Subtype.val_injective hT
    (fun Ω _ _ a g hg => by
      obtain ⟨y, hy⟩ := hF Ω a g hg
      haveI := epi_spMap a
      exact ⟨⟨y, MonoidHom.mem_ker.2 (pow_eq_one_of_res G (spMap a) ξ y n g hy hg)⟩, hy⟩)
  exact ⟨T, inferInstance, hfin, Γ, i, h⟩

end GlobalTheory.CompanionTheory.Ar.TorsQF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_quasi_finite_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (n : ℕ), IsSemiAbelian G → 0 < n → FullTorsion G (spMap (algebraMap R (FractionRing R)) ≫ x) n → ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Q : BT.QFGroup R T) (i : Q.G.left ⟶ G.left), Q.IsTorsionAlong G x n i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup | exact GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.TorsQF.torsion_qfGroup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsEquivOfGiven
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YCompOf
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits in
theorem exists_component_equiv_of_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  intro E _ _ _ H Dw l Xo c Y T o _
  have hb₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have hb₂ : AlgebraicGeometry.Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    have hf : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact RingHom.flat_algebraMap_iff.2 hf
  have := Y.jQ_open
  have hpre : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have hfl : AlgebraicGeometry.Flat Y.j := by unfold Model.j; infer_instance
  have hg : ∀ Z : Comp Xo c, IsGenericPoint (Formalism.L2.Pj.genPt Z) (Z : Set (Xo.XF c)) := fun Z =>
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hmax : ∀ Z : Comp Xo c, ∀ x' : Y.X, x' ⤳ Y.j (Formalism.L2.Pj.genPt Z) → x' = Y.j (Formalism.L2.Pj.genPt Z) := by
    intro Z y hy
    obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Flat.generalizingMap Y.j hy
    rw [GlobalTheory.CompanionTheory.Ar.Flat.eq_genericPoint_of_specializes Z.2 (hg Z) a ha]
  choose k hk using fun Z => o.comp_onto _ (hmax Z)
  have hinj : Function.Injective k := by
    intro Z Z' h
    have h1 : Y.j (Formalism.L2.Pj.genPt Z) = Y.j (Formalism.L2.Pj.genPt Z') := by rw [← hk, ← hk, h]
    have h2 := Y.j.isEmbedding.injective h1
    exact Subtype.ext ((hg Z).def.symm.trans (h2 ▸ (hg Z').def))
  have hsurj : Function.Surjective k := by
    intro a
    let Or := o.Or 0 a
    have e₂ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt (o.Fx a).ξf := RegAtDom.map_genPt Or.g_over
    have e₃ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := RegAtDom.map_genPt Or.𝔐.fn_over
    let η : Sp (T.M 0 a).Ω ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
      pullback.lift (Or.𝔐.ξ ≫ Or.𝔐.f) (spMap Or.𝔐.cst) (by
        rw [Category.assoc, Or.𝔐.cst_over, KapEquiv.spMap_comp_eq])
    have hη : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (GlobalTheory.CompanionTheory.Ar.genPt η) =
        GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := by
      rw [← e₃]
      refine (Scheme.Hom.comp_apply η _ _).symm.trans ?_
      rw [show η ≫ pullback.fst _ _ = Or.𝔐.ξ ≫ Or.𝔐.f from pullback.lift_fst _ _ _]
      exact Scheme.Hom.comp_apply _ _ _
    have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
    have hcl : IsClosed (⋃ Z : Comp Xo c, closure {Y.jQ (Formalism.L2.Pj.genPt Z)}) :=
      isClosed_iUnion_of_finite fun _ => isClosed_closure
    have hsub : Set.range Y.jQ ⊆ ⋃ Z : Comp Xo c, closure {Y.jQ (Formalism.L2.Pj.genPt Z)} := by
      rintro _ ⟨p, rfl⟩
      refine Set.mem_iUnion.2 ⟨⟨irreducibleComponent p, irreducibleComponent_mem_irreducibleComponents p⟩, ?_⟩
      exact specializes_iff_mem_closure.1 (((hg _).specializes mem_irreducibleComponent).map Y.jQ.continuous)
    obtain ⟨Z, hZ⟩ := Set.mem_iUnion.1 (closure_minimal hsub hcl (Y.jQ_dense (GlobalTheory.CompanionTheory.Ar.genPt η)))
    have h1 := (specializes_iff_mem_closure.2 hZ).map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous
    rw [hη] at h1
    have h2 := GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.eq_of_specializes Or.𝔐.gen₀ h1
    refine ⟨Z, o.comp_inj _ _ ?_⟩
    rw [hk, ← e₂, e₃, ← h2]
    exact Scheme.Hom.comp_apply _ _ _
  exact ⟨Equiv.ofBijective k ⟨hinj, hsurj⟩, hk⟩

theorem y_comp_of : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := exists_component_equiv_of_tower

end PositivityTheory.UnitarySelfGeneration
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsEquivOfGiven
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_comp_of | exact PositivityTheory.UnitarySelfGeneration.y_comp_of
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsEquivOfGivenStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_components_equiv_of_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given | exact GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given | (intros; apply GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodQuot_transport {V P : Type} [AddCommGroup V] [Module ℂ V] [CommGroup P] (E : V → P)
    (hadd : ∀ z w, E (z + w) = E z * E w) (hsurj : Function.Surjective E) (Γ₀ : Submodule ℤ V)
    (hΓ : (Γ₀ : Set V) = {z | E z = 1}) (N : ℕ) (hN : 0 < N) (T₀ : Set P) (hT₀ : ∀ τ ∈ T₀, τ ^ N = 1) :
    ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))),
      Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) = Nat.card {p : P // p ^ N = 1} ∧
      Nat.card T = Nat.card T₀ ∧
      (∀ x : Γ₀, Submodule.Quotient.mk x ∈ T → E ((N : ℂ)⁻¹ • (x : V)) ∈ T₀) ∧
      ∀ x : Γ₀, E ((N : ℂ)⁻¹ • (x : V)) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hmem : ∀ z : V, z ∈ Γ₀ ↔ E z = 1 := fun z => by
    have := Set.ext_iff.1 hΓ z
    simpa using this
  have h0 : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hpow : ∀ (k : ℕ) (z : V), E ((k : ℂ) • z) = E z ^ k := by
    intro k z
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have hdiv : ∀ z : V, (N : ℂ) • (N : ℂ)⁻¹ • z = z := fun z => by rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]
  let Eh : V →+ Additive P := AddMonoidHom.mk' (fun z => Additive.ofMul (E z)) (fun a b => by
    rw [hadd]; rfl)
  let d : Γ₀ →+ V := (((N : ℂ)⁻¹ • (LinearMap.id : V →ₗ[ℂ] V)).toAddMonoidHom).comp Γ₀.subtype.toAddMonoidHom
  let f : Γ₀ →ₗ[ℤ] Additive P := (Eh.comp d).toIntLinearMap
  have hf : ∀ x : Γ₀, f x = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hle : LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, hf]
    have : (N : ℂ)⁻¹ • (((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀)) : V) = y := by
      have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀) : V) = (N : ℂ) • (y : V) := by
        simp [Nat.cast_smul_eq_nsmul]
      rw [this, smul_smul, inv_mul_cancel₀ hNc, one_smul]
    rw [this, (hmem _).1 y.2]
    rfl
  let φ := Submodule.liftQ _ f hle
  have hφ : ∀ x : Γ₀, φ (Submodule.Quotient.mk x) = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hφN : ∀ q, (Additive.toMul (φ q)) ^ N = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ, toMul_ofMul, ← hpow, hdiv]
    exact (hmem _).1 x.2
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ] at hq
    have h1 : E ((N : ℂ)⁻¹ • (x : V)) = 1 := hq
    have h2 : (N : ℂ)⁻¹ • (x : V) ∈ Γ₀ := (hmem _).2 h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
    have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ⟨_, h2⟩ : Γ₀) : V) = (N : ℂ) • (N : ℂ)⁻¹ • (x : V) := by
      simp [Nat.cast_smul_eq_nsmul]
    rw [this, hdiv]
  have hrange : ∀ p : P, p ^ N = 1 → ∃ q, Additive.toMul (φ q) = p := by
    intro p hp
    obtain ⟨z, rfl⟩ := hsurj p
    have h1 : (N : ℂ) • z ∈ Γ₀ := (hmem _).2 (by rw [hpow, hp])
    refine ⟨Submodule.Quotient.mk ⟨_, h1⟩, ?_⟩
    rw [hφ, toMul_ofMul]
    congr 1
    change (N : ℂ)⁻¹ • (N : ℂ) • z = z
    rw [smul_smul, inv_mul_cancel₀ hNc, one_smul]
  let ψ : (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) → P := fun q => Additive.toMul (φ q)
  have hψ : Function.Injective ψ := fun a b h => hinj (Additive.toMul.injective h)
  refine ⟨ψ ⁻¹' T₀, ?_, ?_, ?_, fun x => hφN (Submodule.Quotient.mk x)⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q, hφN q⟩) ⟨?_, ?_⟩)
    · exact fun a b h => hψ (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p hp
      exact ⟨q, Subtype.ext hq⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩)
    · exact fun a b h => Subtype.ext (hψ (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p (hT₀ p hp)
      refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
      change ψ q ∈ T₀
      rw [show ψ q = p from hq]
      exact hp
  · intro x hx
    exact hx

theorem toric_torsion_radical_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  intro E _ _ _ H R _ t g n M B ψ e dG b₀ hb₀ Γ₀ hΓ N hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨T₀, hT₁, hT₂, hT₃⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one GlobalTheory.firstFiveLaws.2.2.1 (Sp R) t.G t.semi t.PP t.cub g N ℂ
    (spMap (ψ b₀)) dG hNc
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b₀ hb₀
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_periodQuot_transport (e.ex b₀) (e.add b₀ hb₀) hsurj Γ₀ hΓ N hN T₀ hT₁
  refine ⟨T, by rw [h₁, h₂, hT₃], fun x y hx => ?_⟩
  exact hT₂ _ (h₃ x hx) _ (h₄ y)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_periods_finite_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period | exact GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

namespace GlobalTheory.CompanionTheory.Ar.Adapt


open ReciprocityTheory.AnForm.M.PLAux in
theorem exists_adaptedAtlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  intro e X _ _ _ A L s n m W hL hs hsnc _hle
  have hgood : ∀ x : X, ∃ φ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A φ ∧
      x ∈ φ.source ∧ φ x = 0 ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧
      ∃ (S : Finset (Fin e)) (μ : Fin e → ℕ) (M : ℝ), (∀ i ∈ S, 1 ≤ μ i) ∧
        (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s →
          |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
    intro x
    obtain ⟨φ, S, μ, v, hφc, hxφ, hball, hφx, hsrcU, hμ, hv, hv0, hsv⟩ :=
      GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form e X A L s n m W hsnc x
    refine ⟨φ, hφc, hxφ, hφx, hball, S, μ, ?_⟩

    have hnorm : ∀ y ∈ φ.source,
        ‖s y y‖ * Real.exp (-L.φ y y) = ‖s x y‖ * Real.exp (-L.φ x y) := fun y hy =>
      (hs.2 x y y ⟨hsrcU hy, L.mem_U y⟩).symm
    have hzero : ∀ y ∈ φ.source, (s y y = 0 ↔ s x y = 0) := by
      intro y hy
      have h := hnorm y hy
      constructor
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
    have hmono : ∀ y ∈ φ.source, (s x y = 0 ↔ ∃ i ∈ S, φ y i = 0) := by
      intro y hy
      rw [hsv y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact absurd h (hv0 y hy)
        · exact ⟨i, hi, pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi)) |>.1 h⟩
      · rintro ⟨i, hi, h⟩
        exact Or.inr ⟨i, hi, by rw [h, zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))]⟩
    have hbd : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
      intro y hy
      have hp := φ.map_target hy
      show s (φ.symm y) (φ.symm y) = 0 ↔ _
      rw [hzero _ hp, hmono _ hp, φ.right_inv hy]

    have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) 2) := isCompact_closedBall _ _
    have hF : ContinuousOn (fun z => Real.log ‖v (φ.symm z)‖) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      intro z hz
      have hzt := hball hz
      have han := analyticAt_compat_fun hφc hv hzt (φ.map_target hzt)
      exact (han.continuousAt.norm.log (by simpa using hv0 _ (φ.map_target hzt))).continuousWithinAt
    have hG : ContinuousOn (fun z => L.φ x (φ.symm z)) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      have h := contDiffOn_compat hφc (L.isOpen_U x) (hL.1 x)
      refine h.continuousOn.mono ?_
      intro z hz
      exact ⟨hball hz, hsrcU (φ.map_target (hball hz))⟩
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hF
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hG
    refine ⟨2 * C₁ + 2 * C₂ + ∑ i ∈ S, (μ i : ℝ) * Real.log 4, hμ, hbd, ?_⟩
    intro y hy hyb
    have hyt := hball hy
    have hp := φ.map_target hyt
    set p := φ.symm y with hpdef
    have hφp : φ p = y := φ.right_inv hyt
    have hspp : s p p ≠ 0 := hyb
    have hsxp : s x p ≠ 0 := fun h => hspp ((hzero p hp).2 h)
    have hyi : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 =>
      hsxp ((hmono p hp).2 ⟨i, hi, by rw [hφp]; exact h0⟩)
    have hvp : v p ≠ 0 := hv0 p hp

    have hlogN : logNormSec L s p = Real.log ‖v p‖ + ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x p := by
      unfold logNormSec
      rw [hnorm p hp, Real.log_mul (norm_ne_zero_iff.2 hsxp) (Real.exp_pos _).ne', Real.log_exp,
        hsv p hp, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hvp), norm_prod,
        Real.log_prod]
      · rw [hφp]
        congr 2
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_pow, Real.log_pow]
      · intro i hi
        rw [hφp, norm_pow]
        exact pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))
      · rw [norm_ne_zero_iff, Finset.prod_ne_zero_iff]
        intro i hi
        rw [hφp]
        exact pow_ne_zero _ (hyi i hi)
    have hloc : rLoc S μ y = Real.exp 1 + ∑ i ∈ S, (μ i : ℝ) * (Real.log 4 - 2 * Real.log ‖y i‖) := by
      unfold rLoc
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Real.log_div (by norm_num) (pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))), Real.log_pow]
      push_cast
      ring
    have hdiff : rW L s p - rLoc S μ y =
        -2 * Real.log ‖v p‖ + 2 * L.φ x p - ∑ i ∈ S, (μ i : ℝ) * Real.log 4 := by
      unfold rW
      rw [hlogN, hloc]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [show ∑ i ∈ S, (μ i : ℝ) * (2 * Real.log ‖y i‖) = 2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      ring
    rw [hdiff]
    have h1 : |Real.log ‖v p‖| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ y hy
    have h2 : |L.φ x p| ≤ C₂ := by simpa [Real.norm_eq_abs] using hC₂ y hy
    have h3 : 0 ≤ ∑ i ∈ S, (μ i : ℝ) * Real.log 4 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  choose φ hφc hφx hφ0 hφb hrest using hgood
  choose S μ M hμ hbd hbnd using hrest
  have hU : ∀ x, φ x ⁻¹' Metric.ball 0 1 ∩ (φ x).source ∈ nhds x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨by simp [hφ0 x], hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' Metric.ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B, hAB, h1, h2⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => hφc _) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_, ∑ y ∈ t, |M y|, fun j => ?_⟩
  · obtain ⟨i, hi⟩ := h2 j
    rw [hi]
    exact hφb _
  · obtain ⟨y, hy, hx⟩ := hcov x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]; simpa using hx.2
    · rw [hj]; simpa using hx.1
  · obtain ⟨i, hi⟩ := h2 j
    set y : X := (t.equivFin.symm i : X) with hydef
    have hyt : y ∈ t := (t.equivFin.symm i).2
    refine ⟨S y, μ y, hμ y, ?_, ?_⟩
    · rw [hi]; exact hbd y
    · intro z hz hzb
      rw [hi] at hzb ⊢
      refine (hbnd y z hz hzb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun y => |M y|) (fun _ _ => abs_nonneg _) hyt

end GlobalTheory.CompanionTheory.Ar.Adapt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSectionStatement
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_atlas_snc_section : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | exact GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | (intros; apply GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas <;> assumption)
end
end

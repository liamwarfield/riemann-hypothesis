module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JoinEquivEqAtReference
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct Topology GlobalTheory.AffinePoints

namespace GlobalTheory.CxPtsDense

open GlobalTheory.CxPts

variable {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) (σ : F →+* ℂ)

theorem exists_param [GeometricallyIntegral p] [LocallyOfFiniteType p] {U : X.Opens} (hU : IsAffineOpen U)
    {f : Γ(X, U)} (hf : f ≠ 0) :
    ∃ (B : Type) (_ : TopologicalSpace B) (s : B → CxPts p σ), Nonempty B ∧ Continuous s ∧
      ptsIn p σ U ⊆ Set.range s ∧ Dense (s ⁻¹' ptsIn p σ (X.basicOpen f)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F ℂ := σ.toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have : Nontrivial Γ(X, U) := nontrivial_of_ne _ _ hf
  have : NoZeroDivisors (ℂ ⊗[F] Γ(X, U)) :=
    @UnitRigidity.noZeroDivisors_tensor F Γ(X, U) _ _ _ (algX p U).toAlgebra X p _
      hU.fromSpec (inferInstanceAs (IsOpenImmersion hU.fromSpec)) hg ℂ _ _
  have hinj := Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := Γ(X, U))
      (algebraMap F ℂ).injective
  have : Nontrivial (ℂ ⊗[F] Γ(X, U)) := hinj.nontrivial
  have : IsDomain (ℂ ⊗[F] Γ(X, U)) := NoZeroDivisors.to_isDomain _
  let φ (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : Γ(X, U) →+* ℂ :=
    q.toRingHom.comp (Algebra.TensorProduct.includeRight (R := F) (A := ℂ)).toRingHom
  have hφa (q) (a) : φ q a = q (1 ⊗ₜ a) := rfl
  have hφ (q) (a : F) : φ q (algX p U a) = σ a := by
    have : ((1 : ℂ) ⊗ₜ[F] algX p U a) = algebraMap ℂ (ℂ ⊗[F] Γ(X, U)) (σ a) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := F) (A := ℂ) (B := Γ(X, U)) a).symm
    rw [hφa, this, AlgHom.commutes]
    rfl
  let s (q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ) : CxPts p σ := ofHom hU (φ q) (hφ q)
  have hsU (q) : s q ∈ ptsIn p σ U := ofHom_mem _ _ _
  have hsv (q) (a) : ev p σ U a (s q) = q (1 ⊗ₜ a) := ev_ofHom _ _ _ a
  refine ⟨_, inferInstance, s, ?_, ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℂ ⊗[F] Γ(X, U))
    let := Ideal.Quotient.field m
    have : Module.Finite ℂ ((ℂ ⊗[F] Γ(X, U)) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
    exact ⟨(IsAlgClosed.lift (R := ℂ) (S := (ℂ ⊗[F] Γ(X, U)) ⧸ m) (M := ℂ)).comp (Ideal.Quotient.mkₐ ℂ m)⟩
  · refine continuous_iff_continuousAt.2 fun q => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hsU q) (Filter.Eventually.of_forall hsU) fun a => ?_)
    have h : Continuous (ev p σ U a ∘ s) := by
      have : ev p σ U a ∘ s = fun q => q (1 ⊗ₜ a) := funext fun q => hsv q a
      rw [this]
      exact GlobalTheory.AffinePoints.continuous_eval _
    exact h.continuousAt
  · let ψ : Γ(X, U) →ₐ[F] ℂ :=
      { evHom hy with commutes' := fun a => (ev_eq hy _).symm.trans (ev_algX hy a) }
    let q : ℂ ⊗[F] Γ(X, U) →ₐ[ℂ] ℂ :=
      Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) ψ fun _ _ => Commute.all _ _
    refine ⟨q, Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hsU q) hy fun a => ?_)⟩
    refine (hsv q a).trans ?_
    simp only [q, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (ev_eq hy a).symm
  · have hf' : ((1 : ℂ) ⊗ₜ[F] f) ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
    refine (GlobalTheory.AffinePoints.dense_nonvanishing hf').mono fun q hq => ?_
    refine (mem_ptsIn_basicOpen (hsU q) f).2 ?_
    rw [hsv]
    exact hq

theorem exists_ne_zero_basicOpen_le [IsIntegral X] {U W : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) (hW : (W : Set X).Nonempty) :
    ∃ f : Γ(X, U), f ≠ 0 ∧ X.basicOpen f ≤ W := by
  obtain ⟨x, hxU, hxW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen hne hW
  obtain ⟨f, hfW, hf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
  refine ⟨f, ?_, hfW⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hf
  exact hf

theorem nonempty_and_dense_of_geometricallyIntegral [GeometricallyIntegral p] [LocallyOfFiniteType p] :
    Nonempty (CxPts p σ) ∧ ∀ W : X.Opens, (W : Set X).Nonempty → Dense (ptsIn p σ W) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton p
  refine ⟨?_, fun W hW y => ?_⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    obtain ⟨f, hf, -⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ ⟨_, hx⟩
    obtain ⟨B, _, s, ⟨b⟩, -⟩ := exists_param p σ hU hf
    exact ⟨s b⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ)))
    obtain ⟨f, hf, hfW⟩ := exists_ne_zero_basicOpen_le hU ⟨_, hx⟩ hW
    obtain ⟨B, _, s, -, hs, hr, hd⟩ := exists_param p σ hU hf
    obtain ⟨b, rfl⟩ := hr (mem_ptsIn.2 hx)
    exact closure_mono (ptsIn_mono hfW) (hs.closure_preimage_subset _ (hd b))

theorem nonempty_and_dense : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ),
    Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) :=
  fun _ _ Y σ => nonempty_and_dense_of_geometricallyIntegral Y.str σ

end GlobalTheory.CxPtsDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVarietyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_nonempty_dense_variety : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ), Nonempty (CxPts Y.str σ) ∧ ∀ W : Y.X.Opens, (W : Set Y.X).Nonempty → Dense (CxPts.ptsIn Y.str σ W) := by
  first | exact @GlobalTheory.CxPtsDense.nonempty_and_dense | exact GlobalTheory.CxPtsDense.nonempty_and_dense | (intros; apply GlobalTheory.CxPtsDense.nonempty_and_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImage
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.CarriesAt

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

theorem par_of_tri {h : Mat m K} (hd : ∀ τ i, h τ i i ≠ 0) (hl : ∀ τ i k, i < k → h τ i k = 0) : Par m ⊤ h := fun τ => by
  have hdet : (h τ).det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular (h τ) fun i j hij => hl τ i j hij]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd τ i
  exact ⟨fun _ _ => trivial, hdet, trivial, fun i j _ hij => hl τ i j hij⟩

theorem Par.diag_ne {O : Subring K} {h : Mat m K} (hp : Par m O h) (τ : ι) (i : Fin (m τ)) : h τ i i ≠ 0 := by
  have := hp.det_ne τ
  rw [Matrix.det_of_lowerTriangular (h τ) fun a b hab => (hp τ).2.2.2 a b a.2 hab] at this
  exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_cast {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x') (g : EigFrame Z φ x) :
    ∃ g' : EigFrame Z φ x', ∀ τ i, g'.v τ i = g.v τ i := by
  subst h
  exact ⟨g, fun _ _ => rfl⟩

theorem spMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (dualMap (ψ.comp ρ)) = spMap (dualMap ψ) ≫ spMap (dualMap ρ) := by
  have e : dualMap (ψ.comp ρ) = (dualMap ψ).comp (dualMap ρ) := by
    ext r <;> simp [dualMap]
  rw [e]
  simp [spMap, Spec.map_comp]

theorem coord_of_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {g : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''} {A : Mat Dw.mult R''}
    (hx : x' = spMap ρ ≫ x) (hφ : φ' = ρ.comp φ) (hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i)
    (h : f.Coord (ψ.comp ρ) g A) : f'.Coord ψ g A := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, hx, ← Category.assoc]
    congr 1
    simp [spMap, Spec.map_comp]
  · rw [h2, hφ, RingHom.comp_assoc]
  · have e : (fun k => spMap (dualMap ψ) ≫ f'.v τ k) = fun k => spMap (dualMap (ψ.comp ρ)) ≫ f.v τ k := by
      funext k
      rw [hv, spMap_dualMap_comp, Category.assoc]
    rw [e]
    exact h3 τ i

theorem algebraMap_eq_comp_specializes {X : Scheme.{0}} [IsIntegral X] {y y' : X} (h : y' ⤳ y) :
    algebraMap (X.presheaf.stalk y) X.functionField =
      (algebraMap (X.presheaf.stalk y') X.functionField).comp (X.presheaf.stalkSpecializes h).hom :=
  (congrArg CommRingCat.Hom.hom
    (TopCat.Presheaf.stalkSpecializes_comp X.presheaf (genericPoint_specializes y') h)).symm

theorem exists_adapted {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {S : Fr (ratOf C.Y) Dw.mult Dw.mult}
    {A₀ : Mat Dw.mult C.Y.Fn} (hA₀ : A₀ ∈ S.S (genericPoint C.Y.X))
    (hTied : ∀ y : C.Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* C.Y.X.presheaf.stalk y)
      (f : EigFrame Z φ (stalkPt C.Y y ≫ C.π ≫ genι Z)),
      f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (A₀ * A⁻¹))
    {K : Type} [Field K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z φ x) {y y' : C.Y.X} (hsp : y' ⤳ y)
    (ψ' : C.Y.X.presheaf.stalk y' →+* K) {φ₁ : c.F →+* C.Y.X.presheaf.stalk y}
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) {T : Mat Dw.mult C.Y.Fn} {h : Mat Dw.mult K}
    (hT1 : f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 T)
    (hT : Par Dw.mult ⊤ T)
    (hh1 : f.Coord (ψ'.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) g h) :
    ∃ A ∈ S.S y', ∃ (φ₂ : c.F →+* C.Y.X.presheaf.stalk y') (f₁ : EigFrame Z φ₂ (stalkPt C.Y y' ≫ C.π ≫ genι Z)),
      f₁.Coord (algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord ψ' g h := by
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set alg := algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField with halg
  have hρ : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y y' := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hinj : Function.Injective alg := IsFractionRing.injective _ _

  have hfS : f.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f inferInstance
  obtain ⟨f₀, hf₀⟩ := hfS (C.Y.X.presheaf.stalk y') ρ
  have hx' : spMap ρ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z = stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨f', hf'⟩ := exists_cast hx' f₀
  have hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i := fun τ i => (hf' τ i).trans (hf₀ τ i)
  have hT1' : f'.Coord alg C.f0 T :=
    coord_of_bc hx'.symm rfl hv (algebraMap_eq_comp_specializes hsp ▸ hT1)
  have hh1' : f'.Coord ψ' g h := coord_of_bc hx'.symm rfl hv hh1

  obtain ⟨A', hA'⟩ := S.nonempty y'
  obtain ⟨φ'', f'', hf''⟩ := hTied y' A' hA'
  obtain rfl : φ'' = ρ.comp φ₁ := RingHom.ext fun a => hinj (by
    have e1 := RingHom.congr_fun hf''.2.1 a
    have e2 := RingHom.congr_fun hT1'.2.1 a
    exact e1.symm.trans e2)
  have hS'' : f''.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f'' inferInstance
  have hid : stalkPt C.Y y' ≫ C.π ≫ genι Z = spMap (RingHom.id _) ≫ stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk y')) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨G, hG, -⟩, hGu⟩ := (GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ (ρ.comp φ₁) _ (RingHom.id _) inferInstance hS''
    hid (RingHom.id_comp _).symm).1 f'
  have hGd := hGu G hG
  have hcomp : f''.Coord alg C.f0 (T * G.map alg) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ f'' _ _ _ f' _ _ _ C.f0 (RingHom.id _) alg G T inferInstance hG hT1'
    rwa [RingHom.comp_id] at this
  have heq : A₀ * A'⁻¹ = T * G.map alg :=
    (((GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ _ _ alg inferInstance hS'' hf''.1 hf''.2.1).1 C.f0).1).unique hf'' hcomp
  have hAA : T⁻¹ * A₀ * A'⁻¹ = G.map alg := by
    rw [mul_assoc, heq, ← mul_assoc, Mat.inv_mul hT.det_ne, one_mul]
  have hPg : Par Dw.mult ((ratOf C.Y).O (genericPoint C.Y.X)).toSubring (A₀ * A'⁻¹) :=
    (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hA₀
  have hlow : Par Dw.mult ⊤ (G.map alg) := by
    rw [← hAA, mul_assoc]
    exact hT.inv.mul (hPg.mono le_rfl le_top)
  have hpar : Par Dw.mult ((ratOf C.Y).O y').toSubring (T⁻¹ * A₀ * A'⁻¹) := fun τ => by
    rw [hAA]
    have hdet : (G.map alg τ).det = alg (G τ).det := (alg.map_det (G τ)).symm
    obtain ⟨u, hu⟩ := hGd τ
    refine ⟨fun i j => mem_O_ratOf.2 ⟨G τ i j, rfl⟩, hlow.det_ne τ, ?_, fun i j hi hij => (hlow τ).2.2.2 i j hi hij⟩
    refine mem_O_ratOf.2 ⟨(u⁻¹ : (C.Y.X.presheaf.stalk y')ˣ), ?_⟩
    rw [hdet, ← hu]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨T⁻¹ * A₀, (Fr.mem_iff hA').2 hpar, ρ.comp φ₁, f', ?_, hh1'⟩
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hA₀
  rw [Mat.mul_inv_rev, Mat.inv_inv hT.det_ne, ← mul_assoc, Mat.mul_inv hA₀d, one_mul]
  exact hT1'

theorem carries_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C S A₀ K _ φ x g p hT
  obtain ⟨hA₀, hTied⟩ := hT
  constructor
  · rintro ⟨y, ψ, φ₁, f, t, t', hp, hf, hg⟩
    obtain ⟨T, hT1, hT2, hT3⟩ := (f.tri_iff _ C.f0 t).1 hf
    obtain ⟨h, hh1, hh2, hh3⟩ := (f.tri_iff _ g t').1 hg
    have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
      have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
        rw [hp]
        exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
      have e1 := spMap_stalkClosedPointTo p
      have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
      have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
          spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
        simp [spMap, Spec.map_comp]
      rw [e3, Category.assoc, e2, e1]
      exact hp.symm
    obtain ⟨A, hA, φ₂, f₁, c1, c2⟩ := exists_adapted C hA₀ hTied g hsp _ f hT1
      (par_of_tri (fun τ i => by rw [hT2]; exact Units.ne_zero _) hT3) (hψ ▸ hh1)
    exact ⟨A, hA, φ₂, f₁, h, c1, c2, par_of_tri (fun τ i => by rw [hh2]; exact Units.ne_zero _) hh3⟩
  · rintro ⟨A, hA, φ₁, f₁, h, h1, h2, h3⟩
    have hgen := Fr.mem_genericPoint hA
    have hP : Par Dw.mult ⊤ (A₀ * A⁻¹) := ((Fr.mem_iff hgen).1 hA₀).mono le_rfl le_top
    refine ⟨_, (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom, φ₁, f₁,
      fun τ i => Units.mk0 _ (Par.diag_ne hP τ i), fun τ i => Units.mk0 _ (Par.diag_ne h3 τ i),
      (spMap_stalkClosedPointTo p).symm, (f₁.tri_iff _ C.f0 _).2 ⟨_, h1, fun _ _ => rfl, fun τ i k hik => (hP τ).2.2.2 i k i.2 hik⟩,
      (f₁.tri_iff _ g _).2 ⟨h, h2, fun _ _ => rfl, fun τ i k hik => (h3 τ).2.2.2 i k i.2 hik⟩⟩

end GlobalTheory.ShFam.CarriesAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImageStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  first | exact @GlobalTheory.ShFam.CarriesAt.carries_iff | exact GlobalTheory.ShFam.CarriesAt.carries_iff | (intros; apply GlobalTheory.ShFam.CarriesAt.carries_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Bare

open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial

def cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ H) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e.symm : MonoidAlgebra ℂ H →ₐ[ℂ] MonoidAlgebra ℂ G).comp
    (Subalgebra.center ℂ (MonoidAlgebra ℂ H)).val).codRestrict _ fun z => by
      rw [Subalgebra.mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := (MonoidAlgebra.domCongr ℂ ℂ e.symm).surjective b
      change _ * MonoidAlgebra.domCongr ℂ ℂ e.symm z = MonoidAlgebra.domCongr ℂ ℂ e.symm z * _
      rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 z.2 c]

theorem coeff_cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (g : G) :
    (cenPull e z : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g) :=
  MonoidAlgebra.coeff_domCongr (R := ℂ) e.symm (z : MonoidAlgebra ℂ H) g

theorem cenPull_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) {z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)}
    {z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)}
    (h : ∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g)) : cenPull e z = z' := by
  apply Subtype.ext
  ext g
  rw [coeff_cenPull, h]

attribute [local instance] GlobalTheory.Mem.Top.factType


set_option synthInstance.maxHeartbeats 400000 in
def reser {R : Ranks} {H : Host R} {what₂ rows' : Rows.Data R} {N : NData R H what₂} {N' : NData R H rows'} {A : NAut N} {A' : NAut N'}
    (T : NTypes A) (T' : NTypes A')
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Mt μ j)) : NTypes A :=
  { T with
    eSer := T'.eSer
    eSer_idem := T'.eSer_idem
    eSer_central := T'.eSer_central
    eSer_orth := T'.eSer_orth
    eSer_zero := T'.eSer_zero
    eSer_sum := T'.eSer_sum
    cenAmb := a
    cenMt := b }

theorem goodElement_mem_center_groupAlgebra {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : NTypes A) :
    T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  exact (TypesInhab.good_sum (I := Σ k : Fin 2, N.PlG k) (P := fun kv => Fin R.r → ZMod (H.g kv.1))
    (fun kv p => T.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => T.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) T.e0 (fun g => rfl)
    (fun _ _ => T.eSer_idem _ _) (fun _ _ => T.eSer_central _ _)
    (fun _ p q hpq => T.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))).1

theorem exists_nStage_act {B : Base} {C C₀ : Cols B} {W₀ : RowsRest B C₀} (N₀ : NStage B C₀ W₀) {f : Fr B.toPre}
    (h₀ : GrpTrue N₀ f) (W : RowsRest B C) (hsha : ShaOK B.toPre W.shaLen) (heta : ∀ j w, W.etaJ j w = 0)
    {G : Type} [Group G] (e₀ : G ≃* G0g N₀.nd)
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Mt μ j))
    (ha : ∀ z : Subalgebra.center ℂ (MonoidAlgebra ℂ G),
      (∀ g, (z : MonoidAlgebra ℂ G).coeff g = N₀.ntypes.e0.coeff (e₀ g)) → (∀ μ, W.eOp μ = a μ z) ∧ ∀ μ j, W.eMt μ j = b μ j z) :
    ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      (∀ μ z, N.ntypes.cenAmb μ z = a μ (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z)) ∧
      ∀ μ j z, N.ntypes.cenMt μ j z = b μ j (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z) := by
  obtain ⟨ldat, hsha⟩ := hsha
  let nd := trueLayer B C W f.W ldat hsha
  have hE : IsEmpty nd.Loc := ⟨fun i : Empty => i.elim⟩
  let A : NAut nd := GaloisStage.nAut nd (fun k v => above f.P (nd.g_split k) v)
    (fun k v => div_over f.P (above_div _ _ v)) (fun k => above_injective f.P (nd.g_split k))
    (fun k v v' => not_isConjPl f.P (nd.g_split k) (above_div _ _ v) (above_div _ _ v'))
  have hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  have hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  choose s hs using fun k : Fin 2 => SerInhab.exists_isSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (B.host.g_prime k)
    B.toPre.restRowsFiniteGroupCard_pos ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
        (Finset.mem_univ k)))
  obtain ⟨T₀⟩ : Nonempty (NTypes A) := ⟨TypesInhab.types0 hl hi B.g_cond B.BB_disj tg htg s hs⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨ω, -⟩ := TypesInhab.exists_char (A := MonoidAlgebra ℂ (G0g nd)) 0 one_ne_zero (by simp)
  let eR : G ≃* G0g nd := e₀.trans (grpEquiv N₀.naut A)
  let T : NTypes A := reser (retype T₀ hl hi (fun k => labDat (B.host.g k)) ω) N₀.ntypes
    (fun μ => (a μ).comp (cenPull eR)) (fun μ j => (b μ j).comp (cenPull eR))
  have hT : TypesTrue T f.P f.W :=
    ⟨fun k v => above_div f.P (nd.g_split k) v, fun _ => rfl, fun _ _ _ => rfl, fun k p => h₀.ser k p⟩
  have hco : ∀ g, T.e0.coeff (grpEquiv N₀.naut A g) = N₀.ntypes.e0.coeff g := TypesTrue.typeIdempotent_coeff_across_layers h₀ hT
  have hc : T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g nd)) := goodElement_mem_center_groupAlgebra T
  have hz := ha (cenPull eR ⟨T.e0, hc⟩) fun g => (coeff_cenPull eR _ g).trans (hco (e₀ g))
  have htie : T.IdempotentMatchesAction := by
    refine ⟨fun μ => ?_, fun μ j => ?_⟩
    · rw [NTypes.onAmb, dite_eq_left hc]
      exact hz.1 μ
    · rw [NTypes.onMt, dite_eq_left hc]
      exact hz.2 μ j
  have hy : ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := fun x => by
    obtain ⟨g, rfl⟩ := (grpEquiv N₀.naut A).surjective x
    exact ⟨_, (N₀.nStage_trivialCharacter_coeff_eq g).trans (hco g).symm⟩
  choose e hee using hy
  let tw := GaloisStage.nTw B.LL0 nd
  have hT' : IsEmpty tw.Tw := ⟨fun i : Empty => i.elim⟩
  obtain ⟨Y, hY, ⟨th⟩⟩ := exists_nexp_nth_of_isEmpty B C W nd tw hT' e
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := A
    nbc := GaloisStage.nBC A
    nexp := Y
    ntypes := T
    nStage_trivialCharacter_compat := htie
    nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact hee g
    nth := th
    nbr := fun i => hE.elim i
    nbr_ind := fun i => hE.elim i
    self_good := fun i => hE.elim i
    ntwbr := fun i => hT'.elim i
    ntwbr_ind := fun i => hT'.elim i
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i
    etaJ_tie := fun j w _ _ => (heta j w).trans (Finset.sum_eq_zero fun i _ => hE.elim i).symm },
    hE, hT, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem read_unique {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)} {r p : ℕ} (g : ∀ P : S, GL (Fin r) (kP P.1))
    {S' : Finset (Pl E)} (g' : ∀ P : S', GL (Fin r) (kP P.1))
    (hg : ∀ (P : Pl E) (h : P ∈ S) (h' : P ∈ S'), g' ⟨P, h'⟩ = g ⟨P, h⟩) (P : S) (P' : S') (hP : P.1 = P'.1)
    (i : ZMod p ≃+* kP P.1) (i' : ZMod p ≃+* kP P'.1) {x x' : GL (Fin r) (ZMod p)}
    (h : g P = Formalism.UG.bc (i : ZMod p →+* kP P.1) x) (h' : g' P' = Formalism.UG.bc (i' : ZMod p →+* kP P'.1) x') : x = x' := by
  obtain ⟨P, hS⟩ := P
  obtain ⟨P', hS'⟩ := P'
  dsimp only at hP
  subst hP
  rw [hg P hS hS', h, Subsingleton.elim (i' : ZMod p →+* kP P) (i : ZMod p →+* kP P)] at h'
  ext a b
  exact i.injective (congrArg (fun u : GL (Fin r) (kP P) => (u : Matrix (Fin r) (Fin r) (kP P)) a b) h')

theorem e_eq_act {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m : Mat1 K G} {s : Sp1 O φ G} (t : Tie1 σ m s) {e : MonoidAlgebra K G} (h : m.Laws σ e)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (hz : ∀ g, σ (e.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) :
    s.e = s.act z := by
  refine LinearMap.ext_on_range t.forms.span fun i => ?_
  rw [t.forms.op_eq, t.cen z e hz, h.E_eq]

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem exists_bare {K : Ctx} (P : Pre2 K w) :
    ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧
        ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR := by
  letI := P.z.alg
  let e₀ : Gc B w.px ≃* G0g P.Z₀.N.nd := P.z.R.eG.trans P.z.cG
  have hgood : ∀ g, B.embLL ((idemOf P.z.Xg).coeff g) = P.Z₀.N.ntypes.e0.coeff (e₀ g) := P.z.good.2
  obtain ⟨N, hE, hN, hA, hM⟩ := exists_nStage_act P.Z₀.N P.grp (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.q.sha
    (fun _ _ => rfl) e₀ (fun μ => (P.q.p.sA true μ).act) (fun μ j => (P.q.p.sL μ j).act) fun z hz =>
      ⟨fun μ => e_eq_act (P.q.t.tA true μ) (P.q.t.lawsA true μ) z fun g => (hgood g).trans (hz g).symm,
       fun μ j => e_eq_act (P.q.p.tL μ j) (P.q.t.lawsL μ j) z fun g => (hgood g).trans (hz g).symm⟩
  have hpl : ∀ k v, P.Z₀.N.naut.plGw k ((plEquiv P.Z₀.N.naut N.naut k).symm v) = N.naut.plGw k v := fun k v => by
    rw [← TypesTrue.plGw_plEquiv P.grp hN, Equiv.apply_symm_apply]
  refine ⟨N, hE, hN, fun V S G => ⟨?_, fun eR hR => ?_⟩⟩
  · obtain ⟨plg, hp⟩ := P.grpAt.pl
    obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent
      (w.st (RowPk.Over.Z (q := P.q) ⟨_, _, V, S, N, G⟩)).toD7
    refine ⟨⟨(Equiv.sigmaCongrRight fun k => (plEquiv P.Z₀.N.naut N.naut k).symm).trans plg, fun kv => ?_⟩, hi, hc⟩
    exact ⟨(hp ⟨kv.1, _⟩).1.trans (hpl kv.1 kv.2), (hp ⟨kv.1, _⟩).2⟩
  · have he : e₀.trans (grpEquiv P.Z₀.N.naut N.naut) = eR := by
      obtain ⟨plg, iso, h1, h2⟩ := hR
      obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := P.z.pins.keep.grp
      refine MulEquiv.ext fun g => funext fun kv => ?_
      exact (read_unique g (P.z.R.eG g) (P.z.idG g) (plg kv) (plg₀ ⟨kv.1, (plEquiv P.Z₀.N.naut N.naut kv.1).symm kv.2⟩)
        ((h1 kv).trans ((k1 ⟨kv.1, _⟩).trans (hpl kv.1 kv.2)).symm) (iso kv) (iso₀ ⟨kv.1, _⟩) (h2 g kv) (k2 g ⟨kv.1, _⟩)).symm
    subst he
    exact ⟨fun μ z z' hz x => by rw [hA, cenPull_eq _ hz], fun μ j z z' hz x => by rw [hM, cenPull_eq _ hz]⟩

theorem stepW_bare : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w), ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧ ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR :=
  StepW.of_all fun _ _ _ _ _ _ _ _ P => exists_bare P

end GlobalTheory.Mem.R3.Rw.Bare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStepStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizationFreeStage_trueGroup_columnChoiceStep : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w), ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧ ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR := by
  first | exact @GlobalTheory.Mem.R3.Rw.Bare.stepW_bare | exact GlobalTheory.Mem.R3.Rw.Bare.stepW_bare | (intros; apply GlobalTheory.Mem.R3.Rw.Bare.stepW_bare <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

def St.rowsAre {P : Pre2 K w} (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) :
    R3.RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0 :=
  ⟨x.m.z, x.m.intersectionNumber_baseChange, x.r.Y, x.r.Z.full fun j v h1 h2 => (x.m.eta j v).symm ▸ hη j v h1 h2, fun t => by
    change x.r.Y.tup t = _
    rw [x.r.tup]; exact x.m.tup t⟩

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace

namespace GlobalTheory


open Scheme.IdealSheafData in
theorem vanishingIdeal_comap_of_isOpenImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (B : Closeds X) (B' : Closeds A), (∀ x : A, x ∈ B' ↔ g x ∈ B) → (Scheme.IdealSheafData.vanishingIdeal B).comap g = Scheme.IdealSheafData.vanishingIdeal B' := by
  intro A X g _ B B' h
  have hB : (vanishingIdeal B).support = B := by
    ext x
    simp
  have hr : (vanishingIdeal B).radical = vanishingIdeal B := by
    rw [← vanishingIdeal_support, hB]
  have hs : ((vanishingIdeal B).comap g).support = B' := by
    ext x
    simp [support_comap, h]
  rw [← hs, vanishingIdeal_support]
  ext U : 2
  rw [radical_ideal, ideal_comap_of_isOpenImmersion, ← Ideal.comap_radical, ← radical_ideal, hr]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix

namespace GlobalTheory.SeeSaw.TwLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def RatAt (Q : Finset (HeightOneSpectrum (𝓞 E))) : Set (GL (Fin n) (AfE F E)) :=
  {z | ∀ P : Q, ∀ i j, ∃ e : E, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e}

variable [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}


variable (hc : CMData F E) in
def RdLevOn {K : Type} [Field K] (A : Set (GL (Fin n) (AfE F E))) (U : Subgroup (GL (Fin n) (AfE F E))) (chi : U →* ℂˣ)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (Q : Finset (HeightOneSpectrum (𝓞 E)))
    (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ) : Prop :=
  ∀ z ∈ A, ∀ hz : z ∈ St (1 : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    (z ∈ U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P) ∧
      ∀ (hU : z ∈ U) (h : ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) (h' : ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P),
        ((chi ⟨z, hU⟩ : ℂˣ) : ℂ) =
          (∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹) * ∏ P : Q, ((lamQ P ⟨_, h' P⟩ : ℂˣ) : ℂ)

end GlobalTheory.SeeSaw.TwLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEtaleCompletionCompOpenImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.MemberEt

theorem isEtaleCompletion_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_comp_openImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ A), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro A X g _ R _ _ ξ h
  have hiso : IsIso (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective _ hb _ h

end GlobalTheory.MemberEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem natCast_mem_nonunits_of_induces (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : PlL D p) (W : ValuationSubring ℂ)
    (h : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) : (p : ℂ) ∈ W.nonunits := by
  have hlt : la.1.valuation D.what₂.LL (p : D.what₂.LL) < 1 := by
    have := (la.1.valuation_lt_one_iff_mem (K := D.what₂.LL) ((p : ℕ) : 𝓞 D.what₂.LL)).2 la.2
    simpa using this
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv0 : 0 < la.1.valuation D.what₂.LL (p : D.what₂.LL) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0)
  have hnot : ((p : ℂ))⁻¹ ∉ W := by
    intro hm
    have h1 : D.what₂.embLL ((p : D.what₂.LL)⁻¹) ∈ W := by simpa using hm
    have h2 := (h _).1 h1
    rw [map_inv₀, inv_le_one₀ hv0] at h2
    exact absurd hlt (not_lt.2 h2)
  rw [ValuationSubring.mem_nonunits_iff]
  by_contra hc
  apply hnot
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (not_lt.1 hc)

theorem placeW_spec (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) (h : JcPin D p la jc) :
    (∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ placeW D p la jc ↔
      a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range :=
  Classical.epsilon_spec h

theorem placeW_over : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ), JcPin D p la jc → (p : ℂ) ∈ (placeW D p la jc).nonunits ∧ ∀ x : D.what₂.LL, D.what₂.embLL x ∈ placeW D p la jc ↔ la.1.valuation D.what₂.LL x ≤ 1 :=
  fun D p _ la jc h =>
    ⟨natCast_mem_nonunits_of_induces D p la _ (placeW_spec D p la jc h).1, (placeW_spec D p la jc h).1⟩

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.Vanish

open GlobalTheory.ShFam.Descent GlobalTheory.FlagTan GlobalTheory.AllWt GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

def FrameBC (Z : Model Xo c β) : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X)
    (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem FrameBC.at (hbc : FrameBC Z) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') {x' : Sp R' ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) : ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  subst hx
  exact hbc R R' φ x f ψ

section Cpt

variable {C : FlagCpt Z e}

end Cpt

section Core

end Core

end GlobalTheory.CuspFrom.Vanish

namespace GlobalTheory.CuspFrom

end GlobalTheory.CuspFrom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.R3.Rw.rr_eta_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((v))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((Xo)) := by
  intro B C a b G _ _ Pl0 I0 T Ks _ _ iK A3 R F
  letI := alg b iK
  refine ⟨fun j v => ?_, fun y y' bb E jE jE' n c Xo hj h => ?_⟩
  · classical
    exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A3.fam3.amb3 => (
        if hj : 1 ≤ j ∧ j ≤ a.D.R.m then
          if a.D.plEq (((v :))) ∈ R.twPl then
            A3.A.fam.etaJ F.P0 F.ψ0 (A3.fam3.toSub2 X.zs) ⟨j - 1, by omega⟩ (R.mu (a.D.plEq (((v :))))) (a.D.plEq (((v :))))
          else 0
        else 0) = etaOf R F j ((by with_unfolding_all exact (v :)))) (toCx3_eq b R F)) (by with_unfolding_all rfl)) :))
  · have e : jE' = jE := eq_of_heq hj
    subst jE'
    exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun u : Parts R => ∃ h : n = ((cxW R F u).data F.cr bb).D,
      (∀ x : Fin n → a.D.what₂.LL, jE (∑ i, a.D.what₂.embLL (x i) • c i) =
        PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A3.A.v0) (E := R.HE.H)
          ((cxW R F u).iC F.cr bb A3.A.μ0 (cpt A3.A.v0.embedding (x ∘ Fin.cast h.symm)))))) ∧
      ∀ v, Xo v = (((cxW R F u).data F.cr bb).XE v).submatrix (Fin.cast h) (Fin.cast h) ∧ IsUnit (Xo v).det) (parts_eq b R F)) h) :))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((by with_unfolding_all exact (v :)))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((by with_unfolding_all exact (Xo :))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rr_eta_tr | exact GlobalTheory.Mem.R3.Rw.rr_eta_tr | (intros; apply GlobalTheory.Mem.R3.Rw.rr_eta_tr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ValCoord

open GlobalTheory.ShFam.Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ρ : A →+* B) {x' : Sp B ⟶ Z.X} (hx : spMap ρ ≫ x = x') :
    ∃ g : EigFrame Z (ρ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ρ) ≫ fr.v τ i := by
  subst hx
  exact GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A B φ x fr ρ

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) = spMap (dualMap (χ.comp ρ)) := by
  rw [sp_comp]
  congr 1
  ext z <;> simp [dualMap]

theorem tri_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    {fr : EigFrame Z φ x} {ρ : A →+* B} {x₀ : Sp B ⟶ Z.X} (hx₀ : spMap ρ ≫ x = x₀) {g₀ : EigFrame Z (ρ.comp φ) x₀}
    (hg : ∀ τ i, g₀.v τ i = spMap (dualMap ρ) ≫ fr.v τ i) {χ : B →+* C} {φ' : c.F →+* C} {x' : Sp C ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Cˣ} (h : fr.Tri (χ.comp ρ) g t) : g₀.Tri χ g t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, ← hx₀, ← Category.assoc, sp_comp]
  · rw [h2]; rfl
  · obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun k => spMap (dualMap χ) ≫ g₀.v τ k) = fun k => spMap (dualMap (χ.comp ρ)) ≫ fr.v τ k :=
      funext fun k => by rw [hg, ← Category.assoc, spMap_dualMap_comp]
    rw [e]
    exact c3

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

end GlobalTheory.ShFam.ValCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KTrivAndPolAtTensAt
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.PolFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
  {t : SAB H S} {K : Type} [Field K] {x : Sp K ⟶ S} {u : SAB H (Sp K)}

theorem exists_to_fibre (m : SABMap u t x) :
    ∃ φ : u.G.left ⟶ ((Over.pullback x).obj t.G).left, IsGrpPullback u.G ((Over.pullback x).obj t.G) (𝟙 _) φ ∧
      LBIso u.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x) (m.cart.congr (Category.id_comp _).symm rfl)
    (isGrpPullback_pullback t.G x) t.PP.isLB hM u.PP.isLB (GlobalTheory.Ex.UnifModel.iso_of_map m)
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨φ, hφ, e⟩

theorem exists_of_fibre (m : SABMap u t x) :
    ∃ φ : ((Over.pullback x).obj t.G).left ⟶ u.G.left, IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _) φ ∧
      LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull φ) := by
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB u.PP.isLB hM
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  exact ⟨φ, hφ, e⟩

theorem ample_kTriv_of_polAt (m : SABMap u t x) (hp : GlobalTheory.LN.PolAt t x) :
    RelAmple u.G u.PP.L ∧ KTriv u.G u.PP.L := by
  obtain ⟨φ, hφ, e⟩ := exists_to_fibre m
  exact amplePt _ _ (𝟙 _) _ _ φ hφ _ _ (LB.isLB_pull t.PP.isLB _) u.PP.isLB e hp.2.1 hp.2.2

theorem polAt_of_map (m : SABMap u t x) (hp : IsProper (pullback.snd t.G.hom x)) (hA : RelAmple u.G u.PP.L)
    (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨φ, hφ, e⟩ := exists_of_fibre m
  have h := amplePt _ _ (𝟙 _) _ _ φ hφ _ _ u.PP.isLB (LB.isLB_pull t.PP.isLB _) e hA hK
  exact ⟨hp, h.1, h.2⟩

end GlobalTheory.LocM.PolFibre
end
end

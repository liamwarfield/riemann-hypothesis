module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FinKer

theorem finite_of_isClosed_of_finite_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem locallyQuasiFinite_of_finite_closedFibres {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem exists_lift_of_isClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X Y : Scheme.{0}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] (u : Sp Ω ⟶ Y) (z : X) (hz : IsClosed ({z} : Set X))
    (h : u (IsLocalRing.closedPoint Ω) = g z) :
    ∃ w : Sp Ω ⟶ X, w ≫ g = u ∧ w (IsLocalRing.closedPoint Ω) = z := by
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := g) _ z h
  have : JacobsonSpace ↥(pullback u g) := LocallyOfFiniteType.jacobsonSpace (pullback.fst u g)
  have hcl : IsClosed (closure ({p} : Set ↥(pullback u g))) := isClosed_closure
  have hne : (closure ({p} : Set ↥(pullback u g)) ∩ closedPoints _).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := JacobsonSpace.closure_inter_closedPoints hcl
    rw [hc, closure_empty] at this
    exact (this.symm ▸ subset_closure (Set.mem_singleton p) : p ∈ (∅ : Set _))
  obtain ⟨q, hqp, hq₀⟩ := hne
  have hq : IsClosed ({q} : Set ↥(pullback u g)) := mem_closedPoints_iff.mp hq₀
  refine ⟨pointOfClosedPoint (pullback.fst u g) q hq ≫ pullback.snd u g, ?_, ?_⟩
  · rw [Category.assoc, ← pullback.condition, pointOfClosedPoint_comp_assoc]
  · change (pullback.snd u g) (pointOfClosedPoint (pullback.fst u g) q hq _) = z
    erw [pointOfClosedPoint_apply]
    have hs : p ⤳ q := specializes_iff_mem_closure.mpr hqp
    have := (hs.map (pullback.snd u g).continuous).mem_closed hz (by rw [hp2]; rfl)
    exact this

end GlobalTheory.AV.FinKer

namespace GlobalTheory.AV.AbVar


open GlobalTheory.AV.FinKer in
theorem isFinite_iff_finite_ker : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  intro K _ A B f
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : LocallyOfFiniteType (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ B.X.hom
  let pt : Sp (AlgebraicClosure K) := IsLocalRing.closedPoint (AlgebraicClosure K)
  constructor
  · intro hf
    let u : Sp (AlgebraicClosure K) ⟶ B.X.left := (1 : B.Pt).left
    have : IsFinite (pullback.fst u f.hom.left) := inferInstance
    have hfin := ((pullback.fst u f.hom.left).finite_preimage_singleton pt).to_subtype
    have hmem : ∀ x : (ptMap f).ker, 𝟙 _ ≫ u = x.1.left ≫ f.hom.left := fun x ↦ by
      rw [Category.id_comp, ← Over.comp_left]
      exact congrArg CommaMorphism.left (MonoidHom.mem_ker.mp x.2).symm
    refine Finite.of_injective (β := (pullback.fst u f.hom.left) ⁻¹' {pt})
      (fun x ↦ ⟨pullback.lift (𝟙 _) x.1.left (hmem x) pt, Subsingleton.elim _ _⟩) fun x y hxy ↦ ?_
    have e := ext_of_apply_closedPoint_eq (pullback.fst u f.hom.left) (pullback.lift_fst _ _ _)
      (pullback.lift_fst _ _ _) (congrArg Subtype.val hxy)
    have e2 := congrArg (· ≫ pullback.snd u f.hom.left) e
    simp only [pullback.lift_snd] at e2
    exact Subtype.ext (Over.OverMorphism.ext e2)
  · intro hker
    have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
    have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
    have : LocallyQuasiFinite f.hom.left := by
      refine locallyQuasiFinite_of_finite_closedFibres f.hom.left fun y hy ↦ ?_
      obtain ⟨a, ha, hay⟩ := exists_lift_of_isClosed A.X.hom (spMap (algebraMap K (AlgebraicClosure K)))
        y hy (Subsingleton.elim _ _)
      let x : A.Pt := Over.homMk a ha
      have hcl : IsClosed (f.hom.left ⁻¹' {f.hom.left y}) := by
        have := f.hom.left.isClosedMap _ hy
        rw [Set.image_singleton] at this
        exact this.preimage f.hom.left.continuous
      refine finite_of_isClosed_of_finite_closedPoints hcl ?_
      refine (Set.finite_range (fun k : (ptMap f).ker ↦ (x * k.1).left pt)).subset ?_
      rintro z ⟨hzS, hz⟩
      have hzS' : f.hom.left z = f.hom.left y := hzS
      obtain ⟨w, hw1, hw2⟩ := exists_lift_of_isClosed f.hom.left (a ≫ f.hom.left) z hz
        (by change f.hom.left (a pt) = _; rw [hay, hzS'])
      let w' : A.Pt := Over.homMk w (by
        change w ≫ A.X.hom = _
        rw [← hw, ← Category.assoc, hw1, Category.assoc, hw]; exact ha)
      have hk : x⁻¹ * w' ∈ (ptMap f).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact Over.OverMorphism.ext hw1.symm
      refine ⟨⟨_, hk⟩, ?_⟩
      change (x * (x⁻¹ * w')).left pt = z
      rw [mul_inv_cancel_left]
      exact hw2
    exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_iff_finite_ker' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | exact GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_finite_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieInj

open GlobalTheory.CechDR

variable {R : Type} [CommRing R]

theorem cmpForm_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) :
    Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  intro ω
  obtain ⟨-, hinj, -⟩ := (hH R A g hab hdim).2.2.2.2.1
  haveI := hab.smooth
  haveI := hab.proper
  have hb := (cechDeRham_comparison_bijective_cup_smooth hP R A.left (A.hom ≫ 𝟙 (Sp R)) inferInstance inferInstance
    inferInstance).1
  obtain ⟨c, hc⟩ := hb.2 (clForm _ ω)
  have hmem : clForm (A.hom ≫ 𝟙 (Sp R)) ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by
    rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h0 : toHO1 _ (cmp1 (A.hom ≫ 𝟙 (Sp R)) c) = 0 := by rw [hc]; exact hmem
  rw [structureSheaf_comparison_comm] at h0
  have h1 : toH1O _ c = 0 := GlobalTheory.CechDR.cmpO_injective R A.left _ (h0.trans (map_zero _).symm)
  have h2 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := h1
  rw [hodgeFiltration_eq_range] at h2
  obtain ⟨f, rfl⟩ := h2
  refine ⟨f, hinj ?_⟩
  change clForm (A.hom ≫ 𝟙 (Sp R)) (cmpForm _ f) = clForm (A.hom ≫ 𝟙 (Sp R)) ω
  rw [← comparison_formClass, hc]

section Lie

open ReciprocityTheory.ChartRestriction.G MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

theorem lie_finite_projective (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hdim : SmoothOfRelativeDimension g A.hom) (a : OAct ℤ A) :
    Module.Finite R (GlobalTheory.Serre.Lie a) ∧ Module.Projective R (GlobalTheory.Serre.Lie a) ∧
      ∀ p, Module.rankAtStalk (R := R) (GlobalTheory.Serre.Lie a) p = g := by
  haveI : Smooth A.hom := hdim.smooth
  refine GlobalTheory.LieProj.finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie a) g fun p ↦ ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := GlobalTheory.LieProj.exists_chart_lieBasis A g hdim p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a
    (isGrpPullback_pullback A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away A a r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end Lie

def valMap (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) :
    GlobalTheory.Serre.Lie a →ₗ[R] Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ by
    rw [LinearMap.add_apply, ← tanVal_mul v.isTangent w.isTangent, GlobalTheory.Serre.Lie.hom_add]
  map_smul' r v := LinearMap.ext fun f ↦ by
    rw [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, ← tanVal_epsScale, GlobalTheory.Serre.Lie.hom_smul]

theorem valMap_mem (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) (u : GlobalTheory.Serre.Lie a) :
    valMap A a u ∈ (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro f hf
  exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R A u.hom f hf

theorem valMap_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) [IsCommMonObj A] (a : OAct ℤ A) :
    Function.Surjective ((valMap A a).codRestrict _ (valMap_mem A a)) := by
  have hex := GlobalTheory.LieDual.exists_tangent_of_functional hP hH R A g hab hdim
  have key : ∀ φ : Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))),
      (∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ u : GlobalTheory.Serre.Lie a, valMap A a u = φ := by
    intro φ hφ
    obtain ⟨u, hu, hu'⟩ := hex φ hφ
    exact ⟨GlobalTheory.Serre.Lie.mk a u hu, LinearMap.ext hu'⟩
  intro ψ
  have hψ : ∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → ψ.1 f = 0 := fun f hf ↦
    (Submodule.mem_dualAnnihilator ψ.1).1 ψ.2 f (LinearMap.mem_ker.2 hf)
  exact (key ψ.1 hψ).imp fun u hu ↦ Subtype.ext hu

theorem tangent_eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w →
        (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  intro hP hH R _ A _ g hab hdim v w hv hw hvw
  haveI : IsCommMonObj A := hab.comm
  have hT := lie_finite_projective A g hdim (GlobalTheory.Serre.intAct A)
  haveI := hT.1
  haveI := hT.2.1
  have hcl : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤ := (hH R A g hab hdim).2.2.2.2.1.1
  have hG := (hH R A g hab hdim).2.2.1
  haveI : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.1
  haveI : Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.2.1
  have e1 : (Form (A.hom ≫ 𝟙 (Sp R)) ⧸ LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))) ≃ₗ[R]
      GlobForm (A.hom ≫ 𝟙 (Sp R)) :=
    ((cmpForm (A.hom ≫ 𝟙 (Sp R))).quotKerEquivOfSurjective
      (cmpForm_surjective hP hH A g hab hdim)).trans (LinearEquiv.ofTop _ hcl)
  have eN : (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator ≃ₗ[R]
      Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R))) :=
    (Submodule.dualQuotEquivDualAnnihilator _).symm.trans e1.symm.dualMap
  haveI : Module.Finite R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Finite.equiv eN.symm
  haveI : Module.Projective R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Projective.of_equiv eN.symm
  have hbij := Module.bijective_of_surjective_of_rankAtStalk_eq
    (valMap_surjective hP hH A g hab hdim (GlobalTheory.Serre.intAct A)) fun m _ ↦ by
      rw [hT.2.2, congrFun (Module.rankAtStalk_eq_of_equiv eN) _, GlobalTheory.TopExt.rankAtStalk_dual]
      exact (hG.2.2 _).symm
  have h := hbij.1 (a₁ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) v hv)
    (a₂ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) w hw) (Subtype.ext (LinearMap.ext hvw))
  exact congrArg GlobalTheory.Serre.Lie.hom h

end GlobalTheory.LieInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEqStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_tangent_eq_of_crystallineValues_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w → (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  first | exact @GlobalTheory.LieInj.tangent_eq_of_tanVal_eq | exact GlobalTheory.LieInj.tangent_eq_of_tanVal_eq | (intros; apply GlobalTheory.LieInj.tangent_eq_of_tanVal_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.WeilOver

open GlobalTheory.LatVac GlobalTheory.PlaceDatum GlobalTheory.PlaceModel Formalism.IndefR.Mult

variable {D : D7}

section Coset

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem finTens_nsmul {m n : ℕ} (α : Af D.host.F) (k : ℕ) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens α (k • M) = k • finTens α M := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, finTens_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, finTens_add, ih]

theorem exists_uniform {M : Type} [AddCommGroup M] [Module (𝓞 D.host.E) M] {A : Submodule (𝓞 D.host.E) M} (hA : A.FG)
    (B : Submodule (𝓞 D.host.E) M) (h : ∀ x ∈ A, ∃ k : ℕ, 0 < k ∧ k • x ∈ B) : ∃ k : ℕ, 0 < k ∧ ∀ x ∈ A, k • x ∈ B := by
  classical
  obtain ⟨s, rfl⟩ := hA
  choose N hN h using fun x : s => h x (Submodule.subset_span x.2)
  refine ⟨∏ x, N x, Finset.prod_pos fun x _ => hN x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : s)), mul_nsmul']
    exact nsmul_mem (h ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact B.smul_mem c hx

theorem exists_hom_le (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ homLat ΛS ΛT, k • x ∈ latRat S T ΛS ΛT := by
  let B : Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    { (latRat S T ΛS ΛT).toAddSubmonoid with smul_mem' := fun c _ hx => smul_mem_latRat c hx }
  exact exists_uniform (Module.Finite.iff_fg.1 (homLat_fg hS hT.fg)) B fun x _ =>
    GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS hT x

theorem exists_le_hom (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ latRat S T ΛS ΛT, k • x ∈ homLat ΛS ΛT := by
  classical
  obtain ⟨A, hA, ha⟩ := exists_den_fg (Λ := (D.host.AA : Submodule (𝓞 D.host.E) D.host.E))
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _) LinearMap.id
  obtain ⟨B, hB, hb⟩ := exists_den_fg_pi hS.fg
  obtain ⟨C, hC, hc⟩ := exists_den_matrix (Formalism.UG.intOE D.host.E)
    (GlobalTheory.AdIdem.exists_nat_mul_integral _) S.gram
  refine ⟨A * B * B * C, by positivity, fun x hx => ?_⟩
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha', s, hs, t, ht, rfl⟩ := hx
    intro y hy
    have hi : ∀ j k, ((A : D.host.E) * a) * (star ((B : D.host.E) * s k)) *
        ((C : D.host.E) * S.gram k j) * ((B : D.host.E) * y j) ∈ Formalism.UG.intOE D.host.E :=
      fun j k => mul_mem (mul_mem (mul_mem (ha a ⟨a, ha', rfl⟩) (star_mem_intOE (hb s hs k))) (hc k j)) (hb y hy j)
    have hz : (∑ j, ∑ k, ((A : D.host.E) * a) * (star ((B : D.host.E) * s k)) *
        ((C : D.host.E) * S.gram k j) * ((B : D.host.E) * y j)) ∈ Formalism.UG.intOE D.host.E :=
      sum_mem fun j _ => sum_mem fun k _ => hi j k
    obtain ⟨c, hc'⟩ := hz
    convert ΛT.smul_mem c ht using 1
    funext i
    change (((A * B * B * C) • genMap S T a s t) *ᵥ y) i = (c : D.host.E) * t i
    simp only [Matrix.smul_apply, Matrix.mulVec, dotProduct, genMap, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, hc', nsmul_eq_mul, Nat.cast_mul, star_mul', star_natCast,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  | zero => simp
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem isSBHalf_cosInd (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) {e : AE D}
    (he : e * e = e) (hinf : infPart D e = 0) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (κ : Cos ΛS ΛT 𝔪) :
    IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosInd e κ) := by
  obtain ⟨a, ha, h1⟩ := exists_hom_le hS hT
  obtain ⟨b, hb, h2⟩ := exists_le_hom hS.toIsLattice hT.toIsLattice
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have k1 : ∀ u ∈ latO S T ΛS ΛT fun _ => True, (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := fun u hu => by
    refine latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu
    · intro α hα X hX
      rw [← finTens_nsmul]
      refine AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩
      rw [mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
      exact Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)
    · rw [nsmul_zero]; exact zero_mem _
    · intro x y hx hy; rw [nsmul_add]; exact add_mem hx hy
    · intro x hx; rw [neg_nsmul]; exact neg_mem hx
  have k2 : ∀ u ∈ hatMx (𝔪 • homLat ΛS ΛT), a • u ∈ latO S T ΛS ΛT fun _ => True := fun u hu => by
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hw
      exact finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))
    | zero => rw [nsmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
    | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx
  have hsupp : ∀ t, cosInd e κ t ≠ 0 → t ∈ cosSet e κ := fun t ht => Set.mem_of_indicator_ne_zero ht
  refine ⟨fun t ht => (hsupp t ht).1, a * (b * Ideal.absNorm 𝔪), by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have hk : (a * (b * Ideal.absNorm 𝔪)) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
      rw [mul_nsmul']; exact nsmul_mem (k1 u hu) _
    have hi : t + (a * (b * Ideal.absNorm 𝔪)) • u ∈ cosSet e κ ↔ t ∈ cosSet e κ := by
      refine and_congr ?_ (exists_congr fun x => and_congr_right fun _ => ?_)
      · rw [isHalf_iff S T, isHalf_iff S T]
        exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((isHalf_iff S T).1 hh) _)
      · rw [add_sub_right_comm]
        exact AddSubgroup.add_mem_cancel_right _ hk
    by_cases ht : t ∈ cosSet e κ
    · exact (Set.indicator_of_mem (hi.2 ht) _).trans (Set.indicator_of_mem ht (1 : WO S T → ℂ)).symm
    · exact (Set.indicator_of_notMem (fun h => ht (hi.1 h)) _).trans (Set.indicator_of_notMem ht _).symm
  · obtain ⟨-, x, -, hx⟩ := hsupp t ht
    rw [mul_nsmul]
    refine nsmul_mem ?_ _
    have e1 : e • (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) = e • finTens 1 x.1 := by
      ext i j
      change e * incA D (x.1 i j) = e * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] x.1 i j)
      conv_lhs => rw [← mul_pair_one hinf, mul_assoc]
      congr 1
      exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).trans (by rw [mul_one, one_mul])
    have e2 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])) _
      (finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (h1 x.1 x.2))
    have e3 := add_mem (k2 _ hx) e2
    rwa [finTens_nsmul, e1, smul_comm e a, ← nsmul_add, sub_add_cancel] at e3

end Coset

theorem model_spec {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) ∧ ∃ ε : Fin V.rank → Bool,
      (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm ε ∧ cart M τ * onb M τ = onb M τ * Formalism.REAL.Jm ε := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have e1 := Matrix.mul_nonsing_inv _ hu
  have e2 := Matrix.nonsing_inv_mul _ hu
  have hs : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    rw [Formalism.REAL.Jm, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hs' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Formalism.REAL.Jm, diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  rw [← M.fr_gram τ, cart, onb]
  generalize (M.fr τ)⁻¹ = B at e1 e2
  generalize M.fr τ = A at e1 e2
  have e3 : Bᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
  refine ⟨?_, M.ε τ, ?_, by rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩
  · generalize Formalism.REAL.Jm (M.ε τ) = s at hs hs'
    have hGs : Aᴴ * s * A * (B * s * A) = Aᴴ * A := by
      calc _ = Aᴴ * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hs, Matrix.mul_one]
    refine ⟨?_, ?_, ?_⟩
    · calc _ = B * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hs, Matrix.mul_one, e2]
    · rw [Matrix.mul_assoc, hGs, conjTranspose_mul, conjTranspose_mul, hs']
      calc _ = Aᴴ * (s * (Bᴴ * Aᴴ)) * A := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e3, Matrix.mul_one]
    · rw [hGs]
      exact Matrix.PosDef.conjTranspose_mul_self A
        (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
          (Matrix.isUnit_det_of_left_inverse e2)))
  · calc _ = (Bᴴ * Aᴴ) * Formalism.REAL.Jm (M.ε τ) * (A * B) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, e3, Matrix.one_mul, Matrix.mul_one]

theorem sigOK_negSp {V : HSp D} (h : V.SigOK) : (negSp V).SigOK := fun τ => by
  have e : (negSp V).gram.map τ = -(V.gram.map τ) := Matrix.ext fun i j => map_neg τ _
  rw [e]
  exact GlobalTheory.Grid.hasSignature_neg (h τ)

def IsMaj (V : HSp D) (s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, IsCartanInv (gramAt D V τ) (s τ) ∧ ∃ ε : Fin V.rank → Bool,
    (B τ)ᴴ * gramAt D V τ * B τ = Formalism.REAL.Jm ε ∧ s τ * B τ = B τ * Formalism.REAL.Jm ε

theorem exists_maj_heq {V V' : HSp D} (h : V' = V) {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    ∃ s B, IsMaj V' s B ∧ HEq s (cart M) ∧ HEq B (onb M) := by
  subst h
  exact ⟨_, _, model_spec M, HEq.rfl, HEq.rfl⟩

theorem exists_om_heq {S S' T T' : HSp D} (h : S' = S) (h' : T' = T) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω', IsWeilDatumO ψ S' T' χS χT ω' ∧ HEq ω' ω := by
  subst h h'
  exact ⟨ω, hω, HEq.rfl⟩

theorem exists_vac_cos {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (kS : S.SigOK) (kT : T.SigOK)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ (f : WO S T → ℂ) (c : Cos ΛS ΛT 𝔪 → WO S T → ℂ), IsVacO ψ θ S T sS sT ΛS ΛT f ∧
      ∀ κ, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f (cosInd e κ) (c κ) := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ S T sS sT kS kT cS cT ΛS ΛT dS dT
  choose c hc using fun κ : Cos ΛS ΛT 𝔪 => exists_isThetaAt hψ dS dT (idemSum_mul_self he) (infPart_idemSum he)
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T ΛS ΛT dS dT P e he f hf.2.theta hf.2.lat).1
    (isSBHalf_cosInd (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ dS)
      (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ dT) (idemSum_mul_self he) (infPart_idemSum he) h𝔪 κ)
  exact ⟨f, c, hf, hc⟩

theorem exists_weil {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
    (hV : ∀ i, i ≤ D.R.m → (G.V (.grid i 0)).SigOK ∧ IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)))
    {e : AE D} (he : IsIdemSum e G.pl.W0) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) (s B : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ)
    (hs : ∀ X : Node, X.InRange D.R.m → IsMaj (G.V X) (s X) (B X))
    (om : ∀ p : Pair T, GA D (G.pS p) × GA D (G.pT p) →* Module.End ℂ (WO (G.pS p) (G.pT p) → ℂ))
    (hom : ∀ p : Pair T, p.InRange D.R.m → IsWeilDatumO ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (om p)) :
    ∃ W : G.Weil, W.ψ = ψ ∧ W.θ = θ ∧ W.cart = s ∧ W.onb = B ∧ W.om = om := by
  have h1 : ∀ i, ∃ (f : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ)
      (c : G.CosAt i → WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ), i < D.R.m →
      IsVacO ψ θ _ _ (G.cartS s (.chi i 0)) (G.onT s (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) f ∧
      ∀ κ : G.CosAt i, IsThetaAt ψ (symplO _ _) (heisO ψ _ _) e
        (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1
        f (cosInd e κ) (c κ) := fun i => by
    by_cases hi : i < D.R.m
    swap
    · exact ⟨0, 0, fun h => absurd h hi⟩
    obtain ⟨f, c, h⟩ := exists_vac_cos hψ hθ (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
      (sS := G.cartS s (.chi i 0)) (sT := G.onT s (.chi i 0)) (sigOK_negSp (hV (i + 1) hi).1) (hV i hi.le).1
      (fun τ => isCartanInv_neg (hs (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩ τ).1)
      (fun τ => (hs (.grid i 0) ⟨hi.le, Nat.zero_le _⟩ τ).1) (ΛS := G.latS (.chi i 0)) (ΛT := G.latT (.chi i 0))
      (isSelfDualC_neg (hV (i + 1) hi).2) (hV i hi.le).2 he (G.pl.modul_ne_bot sc)
    exact ⟨f, c, fun _ => h⟩
  choose f c h using h1
  exact ⟨⟨ψ, hψ, θ, hθ, s, fun X hX τ => (hs X hX τ).1, B, fun X hX τ => (hs X hX τ).2, om, hom, f,
    fun i hi => (h i hi).1, c, e, he, fun i hi => (h i hi).2⟩, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ChiGrid.WeilOver

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIntegral_isLocallyNoetherian_compactSpace :
    ∀ (K : Type) [Field K] (A : AbVar K),
      IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  intro K _ A
  have hA : IsAbelianScheme A.X := A.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  refine ⟨isIntegral_of_smooth_of_geometricallyConnected A.X.hom,
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom, ?_⟩
  exact (quasiCompact_iff_compactSpace A.X.hom).mp inferInstance

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompactStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact : ∀ (K : Type) [Field K] (A : AbVar K), IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  first | exact @GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace | exact GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace | (intros; apply GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_one {i : A.ι} {v : V n} (hv : v ∈ (A.e i).target) : A.loc 1 i v = 1 := by
  rw [HolAtlas.loc, dite_eq_left hv]; rfl

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, dite_eq_right hv, add_zero]

theorem loc_mul (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, dite_eq_right hv, mul_zero]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, dite_eq_left hv, dite_eq_left hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, dite_eq_right hv, dite_eq_right hv, smul_zero]

theorem isForm_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  intro M _ n A
  refine ⟨⟨fun i S => ?_, fun x x' _ => ?_⟩, fun c α β hα hβ => ⟨⟨fun i S => ?_, fun x x' h => ?_⟩,
    ⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩⟩
  · exact (contDiffOn_const (c := (bas n).repr (1 : Alt n) S)).congr fun v hv => by
      rw [loc_one A hv]
  · exact (map_one _).symm
  · exact ((hα.smooth i S).add (hβ.smooth i S)).congr fun v _ => by
      rw [loc_add, map_add (f := _), Finsupp.add_apply]
  · change α x + β x = pull _ (α x' + β x')
    rw [map_add (f := _), ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_complexForm_mul n n (A.loc α i) (A.loc β i)).1 _ (hα.smooth i) (hβ.smooth i) S).congr fun v _ => by
      rw [loc_mul]
  · change α x * β x = pull _ (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((hα.smooth i S).const_smul c).congr fun v _ => by
      rw [loc_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · change c • α x = pull _ (c • α x')
    rw [map_smul, ← hα.compat x x' h]

end GlobalTheory.CxForm.HolAtlas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmulStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_one_add_mul_smul : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.isForm_algebra | exact GlobalTheory.CxForm.HolAtlas.isForm_algebra | (intros; apply GlobalTheory.CxForm.HolAtlas.isForm_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstant
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.EvSquare

noncomputable def constAlg (σ : Type) (k : Type) [CommRing k] : MvPowerSeries σ k →ₐ[k] k :=
  { (constantCoeff : MvPowerSeries σ k →+* k) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

theorem evA_zero (k : Type) [CommRing k] (σ : Type) [Finite σ] (f : MvPowerSeries σ k) :
    evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero) f = constantCoeff f := by
  have h := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ k (evA k (fun _ : σ => (0 : k)) (fun _ => IsNilpotent.zero))
    (constAlg σ k) (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact IsNilpotent.zero)
    (fun i => by rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; simp [constAlg])
  rw [h]; rfl

theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ n, (∀ f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[k] 1) ∧ (∀ f, c.ev₂ n (inR f) = 1 ⊗ₜ[k] c.ev n f) ∧ (∀ s, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s)) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p k _ d G c n
  have hX : ∀ t, c.ev₂ n (X t) = c.x₂ n t := fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ t
  have hN : ∀ t, IsNilpotent (c.ev₂ n (X t)) := fun t => by rw [hX]; exact c.nil₂ n t
  refine ⟨fun f => ?_, fun f => ?_, fun s => ?_, fun s => ?_⟩
  · have hy : ∀ i, IsNilpotent (c.x n i ⊗ₜ[k] (1 : G.A n)) := fun i => c.nil₂ n (Sum.inl i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inl i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeLeft (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inL; rw [e1, ← e2]; rfl
  · have hy : ∀ i, IsNilpotent ((1 : G.A n) ⊗ₜ[k] c.x n i) := fun i => c.nil₂ n (Sum.inr i)
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (fun i => X (Sum.inr i)) (fun i => constantCoeff_X _) _ hy (fun i => hX _) f
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      Algebra.TensorProduct.includeRight (c.x n) (c.nil n) _ hy (fun i => rfl) f
    unfold inR; rw [e1, ← e2]; rfl
  · let g : G.A n ⊗[k] G.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      (Algebra.TensorProduct.comm k (G.A n) (G.A n)).toAlgHom
    have hy : ∀ i, IsNilpotent (g (c.x₂ n i)) := fun i => (c.nil₂ n i).map g
    have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n) hN
      (Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)))
      (fun i => by cases i <;> exact constantCoeff_X _) _ hy
      (fun i => by
        cases i with
        | inl i => rw [Sum.elim_inl, hX]; simp [g, Chart.x₂]
        | inr i => rw [Sum.elim_inr, hX]; simp [g, Chart.x₂]) s
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n ⊗[k] G.A n)
      g (c.x₂ n) (c.nil₂ n) _ hy (fun i => rfl) s
    unfold Katz.swap at2
    rw [e1, ← e2]; rfl
  · let L : G.A n ⊗[k] G.A n →ₐ[k] k := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n))
      (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _)
    have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 k
      L (c.x₂ n) (c.nil₂ n) (fun _ => (0 : k)) (fun _ => IsNilpotent.zero)
      (fun i => by
        cases i with
        | inl i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]
        | inr i => simp [L, Chart.x₂, Bialgebra.counitAlgHom_apply, c.aug n i]) s
    change L (c.ev₂ n s) = _
    unfold Chart.ev₂; rw [e2, evA_zero]

end GlobalTheory.EvSquare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstantStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ n, (∀ f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[k] 1) ∧ (∀ f, c.ev₂ n (inR f) = 1 ⊗ₜ[k] c.ev n f) ∧ (∀ s, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s)) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  first | exact @GlobalTheory.EvSquare.main | exact GlobalTheory.EvSquare.main | (intros; apply GlobalTheory.EvSquare.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open ReciprocityTheory.L2DbarEstimates (V cHess)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem MLine.Isom.hess_eq {L M : MLine p σ} (h : L.Isom M) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) {a : M.B.ι} {b : L.B.ι} (ha : y ∈ ptsIn p σ (M.B.U a)) (hb : y ∈ ptsIn p σ (L.B.U b)) :
    c.hess M.φ a y = c.hess L.φ b y := by
  obtain ⟨w, -, h⟩ := h
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (M.B.U a ⊓ L.B.U b),
      (ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 :=
    fun v hv => ev_ne_zero hv.2 (w.s _).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (L.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [h _ _ _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem dens_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) : dens L c y = dens M c y := by
  have e (i : Fin D) := (h i).hess_eq c hy (mem_pick (M i).φ.isLB y) (mem_pick (L i).φ.isLB y)
  simp only [dens, e]

theorem part_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (ε : ℤˣ) :
    part L ε = part M ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun ?_ ?_
  · exact measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) inter_subset_left
  · rintro _ ⟨y, hy, rfl⟩
    simp only [c.e.left_inv hy.1, dens_congr_isom h c hy.1]

theorem part_eq_of_isom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε :=
  fun _ _ _ _ _ _ _ _ _ h ε => part_congr_isom h ε

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε := by
  first | exact @GlobalTheory.Mix.part_eq_of_isom | exact GlobalTheory.Mix.part_eq_of_isom | (intros; apply GlobalTheory.Mix.part_eq_of_isom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X, Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by
  first | exact @GlobalTheory.FieldDimCoheight.coheight_eq_one_iff | exact GlobalTheory.FieldDimCoheight.coheight_eq_one_iff | (intros; apply GlobalTheory.FieldDimCoheight.coheight_eq_one_iff <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensMulPullHeadL
set_option autoImplicit false

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.LocFub.TopDens

theorem dens_smul {n : ℕ} (c : ℂ) (α : Alt n) : dens (c • α) = c * dens α := by
  simp [dens, mul_div_assoc]

theorem dens_add {n : ℕ} (α β : Alt n) : dens (α + β) = dens α + dens β := by
  simp [dens, add_div]

theorem dens_zero {n : ℕ} : dens (0 : Alt n) = 0 := by simp [dens]

end GlobalTheory.LocFub.TopDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm.FirstChern

open Filter Topology GlobalTheory.HermFrame GlobalTheory.Points
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

theorem chernAt_exp_neg {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    chernAt (fun x => (Matrix.of fun _ _ : Unit => ((Real.exp (-u x) : ℝ) : ℂ))) v 1 = ofValues (ddc u v) := by
  have h1 (G : V n → Matrix Unit Unit ℂ) : chernAt G v 1 = ofValues (chernOne G v) := by
    unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  congr 1
  funext ξ η
  rw [chernOne_line (f := fun x => Real.exp (-u x)) (Real.contDiff_exp.contDiffAt.comp v hu.neg) (Real.exp_ne_zero _)
    (Eventually.of_forall fun _ => rfl)]
  simp only [Real.log_exp, ddc, leviForm_neg]
  simp

end GlobalTheory.LineForm.FirstChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVarProj

theorem strHom_eq_and_isProjOver : ∀ (K : Type) [Field K] (A : AbVar K),
    (letI := A.algΓ; GlobalTheory.strHom K A.X.left = A.X.hom) ∧ IsProjOver A.X.hom := by
  intro K _ A
  refine ⟨?_, ?_⟩
  · letI := A.algΓ
    exact GlobalTheory.strHom_eq fun _ => rfl
  · exact (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.X.hom).1
      (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)

end GlobalTheory.AV.AbVarProj
end
end

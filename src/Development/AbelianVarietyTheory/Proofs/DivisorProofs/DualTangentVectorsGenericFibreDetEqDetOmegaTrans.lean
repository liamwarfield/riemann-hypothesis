module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.LieRel

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [QuasiSeparated G.hom]

theorem exists_prod (l : List (LieG G)) :
    ∃ z : LieG G, z.1 = (l.map fun x => x.1).prod ∧ tangent z = (l.map tangent).sum := by
  induction l with
  | nil =>
    have h1 : ptMap (TrivSqZeroExt.fstHom R R R) ≫ (1 : specO R (DualNumber R) ⟶ G) = 1 := MonObj.comp_one _
    refine ⟨⟨1, h1⟩, rfl, ?_⟩
    have h2 := tangent_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩ (OmegaGlobal.fst_mul _ _)
    have h3 : (⟨_, OmegaGlobal.fst_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩⟩ : LieG G) = ⟨1, h1⟩ :=
      Subtype.ext (_root_.mul_one _)
    rw [h3] at h2
    simpa using h2
  | cons x l ih =>
    obtain ⟨z, hz, hz'⟩ := ih
    refine ⟨⟨_, OmegaGlobal.fst_mul x z⟩, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hz]
    · rw [tangent_mul, hz', List.map_cons, List.sum_cons]

theorem isLieComb_of_tangent {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G)
    (h : tangent w = ∑ m, cst R (a m) • tangent (v m)) : IsLieComb a (fun m => (v m).1) w.1 := by
  let u : Fin n → LieG G := fun m => ⟨_, OmegaGlobal.fst_scale (a m) (v m)⟩
  obtain ⟨z, hz, hz'⟩ := exists_prod (List.ofFn u)
  have e : w = z := tangent_injective R G (by
    rw [h, hz', List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun m _ => (tangent_scale _ _ _).symm)
  refine ⟨fun m => (u m).1, fun m => ?_, ?_⟩
  · have ha : (dualScale (a m)).toRingHom = epsScaleR (a m) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v m).1.left) ha
  · rw [e, hz, List.map_ofFn]
    rfl

theorem exists_matrix {g : ℕ} {e e' : Fin g → Γ(omega G, ⊤)} (he : IsFrame e) (he' : IsFrame e') (v v' : Fin g → LieG G)
    (hv : ∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0)
    (hv' : ∀ j k, dualApp (tangent (v' j)) le_top (e' k) = if j = k then 1 else 0) :
    ∃ M : Matrix (Fin g) (Fin g) R, (∀ j, IsLieComb (M j) (fun m => (v' m).1) (v j).1) ∧
      M.det = (Scheme.ΓSpecIso (.of R)).hom (he.detUnit he' le_rfl le_rfl : Γ(Sp R, ⊤)) := by
  refine ⟨fun j m => (Scheme.ΓSpecIso (.of R)).hom (dualApp (tangent (v j)) le_top (e' m)), fun j => ?_, ?_⟩
  · refine isLieComb_of_tangent _ _ _ (he'.dual_ext le_rfl fun k => ?_)
    rw [resM_self, dualApp_sum, LinearMap.sum_apply]
    simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]
    rw [Finset.sum_congr rfl fun m _ => congrArg (cst R _ * ·) (hv' m k)]
    simp
  · have hc (j : Fin g) : dualApp (tangent (v j)) le_rfl = (he.basis le_rfl).coord j := by
      apply (he.basis le_rfl).ext
      intro k
      have hb : (he.basis le_rfl) k = e k := by rw [he.basis_apply, resM_self]
      rw [hb, hv, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [eq_comm]
    rw [IsFrame.val_detUnit, Module.Basis.det_apply]
    refine Eq.trans ?_ (RingHom.map_det (Scheme.ΓSpecIso (.of R)).hom.hom _).symm
    congr 1
    ext j m
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, resM_self]
    exact congrArg _ (congrFun (congrArg DFunLike.coe (hc j)) (e' m))

end Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {g : ℕ}

theorem pfr_eq (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) :
    pfr c ξ hc = fun k => (omegaBase (isGrpPullback_pullback G ξ)).app ⊤
      (resM _ hc (QCoh.pullbackSections ξ (omega G) (le_refl (ξ ⁻¹ᵁ c.U)) (c.e k))) :=
  funext fun _ => congrArg _ (QCoh.res_pullbackSections ξ _ _ _ _).symm

theorem isFrame_pfr (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) : IsFrame (pfr c ξ hc) := by
  rw [pfr_eq]
  exact ((c.isFrame.pullback ξ).res hc).map_iso _

theorem val_detUnit_pfr (c c' : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (hc' : ⊤ ≤ ξ ⁻¹ᵁ c'.U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ((isFrame_pfr c ξ hc).detUnit (isFrame_pfr c' ξ hc') le_rfl le_rfl : Γ(Sp R, ⊤)) =
      (ξ.appLE (c.U ⊓ c'.U) ⊤ h).hom (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right : Γ(S, c.U ⊓ c'.U)) := by
  have key {e e' f f' : Fin g → Γ(omega (bG G ξ), ⊤)} (he : IsFrame e) (he' : IsFrame e') (hf : IsFrame f)
      (hf' : IsFrame f') (h₁ : e = f) (h₂ : e' = f') :
      he.detUnit he' le_rfl le_rfl = hf.detUnit hf' le_rfl le_rfl := by
    subst h₁ h₂; rfl
  rw [key _ _ (((c.isFrame.pullback ξ).res hc).map_iso (omegaBase (isGrpPullback_pullback G ξ)))
    (((c'.isFrame.pullback ξ).res hc').map_iso (omegaBase (isGrpPullback_pullback G ξ))) (pfr_eq c ξ hc) (pfr_eq c' ξ hc'),
    IsFrame.detUnit_map_iso ((c.isFrame.pullback ξ).res hc) ((c'.isFrame.pullback ξ).res hc'),
    IsFrame.detUnit_res (c.isFrame.pullback ξ) (c'.isFrame.pullback ξ)]
  exact c.isFrame.val_detUnit_pullback c'.isFrame ξ inf_le_left inf_le_right h

theorem genPt_appLE [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    (Scheme.ΓSpecIso (.of (FF S))).hom (((genPt S).appLE U ⊤ (genPt_le U hU)).hom a) =
      S.presheaf.germ U (genericPoint S) hU a := by
  have k : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U := genPt_le U hU
  have e : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k =
      S.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE k).op :
      Opposite.op (⊤ : (Spec (S.presheaf.stalk (genericPoint S))).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  have e' : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k ≫
      (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).hom = S.presheaf.germ U _ hU := by
    rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congr($e' a)

theorem lieRel : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  intro S _ G _ _ g hG _ c c' h1 y y' ⟨hc, hy⟩ ⟨hc', hy'⟩
  choose v hv hv₁ using hy
  choose v' hv' hv₁' using hy'
  have : QuasiSeparated (bG G (genPt S)).hom :=
    MorphismProperty.of_isPullback (isGrpPullback_pullback G (genPt S)).1 inferInstance
  obtain ⟨M, hM, hd⟩ := exists_matrix (isFrame_pfr c _ hc) (isFrame_pfr c' _ hc') v v' hv₁ hv₁'
  obtain rfl : (fun j => (v j).1) = y := funext hv
  obtain rfl : (fun j => (v' j).1) = y' := funext hv'
  refine ⟨M, hM, hd.trans ?_⟩
  rw [val_detUnit_pfr c c' _ hc hc' (genPt_le _ h1)]
  exact genPt_appLE _ h1 _

end GlobalTheory.KeyVals.LieRel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTransStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualTangentVectors_genericFibre_det_eq_detOmegaTrans : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  first | exact @GlobalTheory.KeyVals.LieRel.lieRel | exact GlobalTheory.KeyVals.LieRel.lieRel | (intros; apply GlobalTheory.KeyVals.LieRel.lieRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag.LQF

theorem finite_preimage_of_finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (H : {z : Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ X | z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y}.Finite) : (f ⁻¹' {y}).Finite := by
  let k := Y.residueField y
  let K := AlgebraicClosure k
  let pt : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have hcl : closedPoints (f.fiber y) ⊆ f.fiberι y ⁻¹' ((fun z : Spec (CommRingCat.of K) ⟶ X => z pt) '' {z |
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Y.fromSpecResidueField y}) := by
    intro w hw
    have hw' : IsClosed ({w} : Set (f.fiber y)) := hw
    have h1 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w) :=
      isClosed_singleton_iff_locallyOfFiniteType.1 hw'
    have h0 : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹LocallyOfFiniteType f›
    have h2 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) := inferInstance
    have h3 : IsFinite ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 h2
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y)
    have h4 : φ.hom.Finite := by
      rw [← IsFinite.SpecMap_iff, hφ]; exact h3
    letI : Algebra k ((f.fiber y).residueField w) := φ.hom.toAlgebra
    haveI : Module.Finite k ((f.fiber y).residueField w) := h4
    haveI : Algebra.IsAlgebraic k ((f.fiber y).residueField w) := Algebra.IsIntegral.isAlgebraic
    let ι : (f.fiber y).residueField w →ₐ[k] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (f.fiber y).fromSpecResidueField w ≫ f.fiberι y, ?_, ?_⟩
    · show _ = _
      rw [Category.assoc, Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc ((f.fiber y).fromSpecResidueField w),
        ← hφ, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      exact ι.commutes a
    · show (Spec.map _ ≫ _ ≫ _) pt = _
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hfin : (closedPoints (f.fiber y)).Finite :=
    ((H.image _).preimage (f.fiberι y).isEmbedding.injective.injOn).subset hcl
  have huniv : (Set.univ : Set (f.fiber y)) = closedPoints (f.fiber y) := by
    have hc : IsClosed (closedPoints (f.fiber y)) := by
      rw [← Set.biUnion_of_singleton (closedPoints (f.fiber y))]
      exact hfin.isClosed_biUnion fun x hx => hx
    rw [← JacobsonSpace.closure_inter_closedPoints isClosed_univ, Set.univ_inter, hc.closure_eq]
  haveI : Finite (f.fiber y) := Set.finite_univ_iff.1 (huniv ▸ hfin)
  rw [← Scheme.Hom.range_fiberι]
  exact Set.finite_range _

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan initSpan_le_of_tri)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_sum_of_isCombAtG {Y : Model Xo c (RingHom.id c.F)} {K : Type} [Field K] {x x' : Sp K ⟶ Y.X} (e : x' = x)
    {m : ℕ} (u : Fin m → TanM x Y.t.G) (cf : Fin m → K) (w : TanM x Y.t.G)
    (h : IsCombAtG Y.t x' (fun j => (tv (u j)).left) cf (tv w).left) : w = ∑ j, cf j • u j := by
  subst e
  exact (GlobalTheory.LieMet.isComb_iff u cf w).1 h

theorem vecAt_left {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {K : Type}
    [Field K] (k : F.J) (z : Sp K ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (i : Fin (Dw.mult σ)) : (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx; rfl

theorem initSpan_le_of_frameTri {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {K : Type} [Field K] {φ φ' : c.F →+* K} (z z' : Sp K ⟶ Z) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x)
    (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k') (g : EigFrame Y φ (z ≫ π))
    (g' : EigFrame Y φ' (z' ≫ π)) (hg : IsFrameAt F z k hz g) (hg' : IsFrameAt F z' k' hz' g')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (ht : g.Tri (RingHom.id K) g' t) (σ : E →+* ℂ) (i : ℕ) :
    initSpan K (F.vecAt k' z' hz' hx' σ) i ≤ initSpan K (F.vecAt k z hz hx σ) i := by
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have ex : ∀ j : Fin (Dw.mult σ), ∃ cf : Fin (Dw.mult σ) → K, (∀ k, j < k → cf k = 0) ∧
      F.vecAt k' z' hz' hx' σ j = ∑ a, cf a • F.vecAt k z hz hx σ a := fun j => by
    obtain ⟨cf, -, hcf, hc⟩ := ht.2.2 σ j
    refine ⟨cf, hcf, eq_sum_of_isCombAtG hx' _ cf _ ?_⟩
    have e1 : (fun a => spMap (dualMap (RingHom.id K)) ≫ g.v σ a) =
        fun a => (tv (F.vecAt k z hz hx σ a)).left := funext fun a => by
      rw [h1, Category.id_comp, hg σ a, vecAt_left F k z hz hx σ a]
    rw [e1, hg' σ j, ← vecAt_left F k' z' hz' hx' σ j] at hc
    exact hc
  choose cf hcf e using ex
  exact initSpan_le_of_tri (B := Matrix.of fun a j => cf j a) (fun j a h => hcf a j h) e i

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.CompHS (Y₀ inc₀)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_base {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Y φ x} (h : C.Carries p g) :
    x = p ≫ C.π ≫ GlobalTheory.Toroidal.genι Y := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, -, htri⟩ := h
  rw [htri.1, hp, Category.assoc]

theorem tri_of_carries {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) (hC : CarriesTri C)
    {K : Type} [Field K] {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} (e : x = x') {p : Sp K ⟶ C.Y.X}
    (g : EigFrame Y φ x) (g' : EigFrame Y φ' x') (h : C.Carries p g) (h' : C.Carries p g') :
    ∃ t, g.Tri (RingHom.id K) g' t := by
  subst e
  exact hC K φ φ' x p g g' h h'

theorem finite_points {Y : Model Xo c (RingHom.id c.F)} (X : FlagModel Y) (C : FlagCpt Y (RingEquiv.refl c.F))
    (hC : CarriesTri C) (Z : Formalism.L2.Pj.Comp Xo c) (h : Y₀ X.toFlagCover Z ⟶ C.Y.X)
    (hR : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ X.toFlagCover Z), Rel X.F C (z ≫ inc₀ X.toFlagCover Z) (z ≫ h))
    (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ C.Y.X) : {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p} with h0 | ⟨z₁, hz₁⟩
  · rw [h0]; exact Set.finite_empty
  have hfin := X.fin K (z₁ ≫ inc₀ X.toFlagCover Z)
  refine (hfin.preimage (f := fun z => z ≫ inc₀ X.toFlagCover Z)
    (fun a _ b _ e => (cancel_mono (inc₀ X.toFlagCover Z)).1 e)).subset ?_
  intro z hz
  have key : ∀ w : Sp K ⟶ Y₀ X.toFlagCover Z, w ≫ h = p → ∃ (φ : c.F →+* K) (k : X.F.J)
      (hk : ⊤ ≤ (w ≫ inc₀ X.toFlagCover Z) ⁻¹ᵁ X.F.U k)
      (g : EigFrame Y φ ((w ≫ inc₀ X.toFlagCover Z) ≫ X.π)), IsFrameAt X.F _ k hk g ∧ C.Carries p g := by
    intro w hw
    obtain ⟨φ, k, hk, g, -, hg, hc⟩ := hR K w
    exact ⟨φ, k, hk, g, hg, hw ▸ hc⟩
  obtain ⟨φ, k, hk, g, hg, hc⟩ := key z hz
  obtain ⟨φ₁, k₁, hk₁, g₁, hg₁, hc₁⟩ := key z₁ hz₁
  have hx : (z ≫ inc₀ X.toFlagCover Z) ≫ X.π = (z₁ ≫ inc₀ X.toFlagCover Z) ≫ X.π :=
    (carries_base C hc).trans (carries_base C hc₁).symm
  refine ⟨hx, fun σ i => ?_⟩
  obtain ⟨t, ht⟩ := tri_of_carries C hC hx g g₁ hc hc₁
  obtain ⟨t', ht'⟩ := tri_of_carries C hC hx.symm g₁ g hc₁ hc
  rw [X.F.step_eq k _ hk hx, X.F.step_eq k₁ _ hk₁ rfl]
  exact le_antisymm (initSpan_le_of_frameTri X.F _ _ rfl hx k₁ k hk₁ hk g₁ g hg₁ hg t' ht' σ i)
    (initSpan_le_of_frameTri X.F _ _ hx rfl k k₁ hk hk₁ g g₁ hg hg₁ t ht σ i)

end GlobalTheory.VarFlag.LQF

theorem GlobalTheory.VarFlag.locallyQuasiFinite_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagModel Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (h : GlobalTheory.CompHS.Y₀ X.toFlagCover Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X.toFlagCover Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X.toFlagCover Z) (z ≫ h)) → LocallyQuasiFinite h := by
  intro E _ _ _ H Dw l Xo c Y X C hC Z h _ hR
  refine LocallyQuasiFinite.of_finite_preimage_singleton h fun p => ?_
  exact GlobalTheory.VarFlag.LQF.finite_preimage_of_finite_points h p
    (GlobalTheory.VarFlag.LQF.finite_points X C hC Z h hR _ _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagModel Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (h : GlobalTheory.CompHS.Y₀ X.toFlagCover Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X.toFlagCover Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X.toFlagCover Z) (z ≫ h)) → LocallyQuasiFinite h := by
  first | exact @GlobalTheory.VarFlag.locallyQuasiFinite_flag | exact GlobalTheory.VarFlag.locallyQuasiFinite_flag | (intros; apply GlobalTheory.VarFlag.locallyQuasiFinite_flag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanOneTmulEqTop
namespace GlobalTheory.TensorUnitSpanTop

open TensorProduct

theorem span_one_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  set N := Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) with hN
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
    have hm : m ∈ Submodule.span R (Set.range f) := hf ▸ Submodule.mem_top
    have h1 : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m ∈ N.restrictScalars R := by
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
      | smul r y _ hy => rw [tmul_smul]; exact Submodule.smul_mem _ r hy
    have h2 : a ⊗ₜ[R] m = a • ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact N.smul_mem a h1
  | add x y hx hy => exact add_mem hx hy

theorem main : ∀ {R M : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : AddCommGroup M] [inst_3 : Module R M] {ι : Type} (f : ι → M), Submodule.span R (Set.range f) = ⊤ → Submodule.span (IsLocalRing.ResidueField R) (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ :=
  fun f hf => span_one_tmul_eq_top f hf

end GlobalTheory.TensorUnitSpanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParameters
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

open scoped TensorProduct

namespace GlobalTheory.CoordExt

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem span_D_algebraMap_eq_top (F A R : Type) [Field F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] :
    Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y)) = ⊤ := by
  set S := Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
  have hu : IsUnit (algebraMap A R s) := IsLocalization.map_units R s
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have key : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      KaehlerDifferential.D F R (algebraMap A R y) -
        IsLocalization.mk' R y s • KaehlerDifferential.D F R (algebraMap A R s) := by
    rw [eq_sub_iff_add_eq, add_comm, ← Derivation.leibniz, IsLocalization.mk'_spec]
  have hmem : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) ∈ S := by
    rw [key]
    exact sub_mem (Submodule.subset_span ⟨y, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩))
  have : KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      v • (algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s)) := by
    rw [smul_smul, hv, one_smul]
  change _ ∈ S
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem span_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TensorUnitSpanTop.main
  | exact _root_.GlobalTheory.TensorUnitSpanTop.main
  | (apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorUnitSpanTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorUnitSpanTop.main ..)

end GlobalTheory.CoordExt


open GlobalTheory.CoordExt in
theorem GlobalTheory.exists_coords_extending_regularParams : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  classical
  intro F A R _ _ _ _ _ _ _ _ _ _ _ P _ _ n _ _ hn m a hrsp
  haveI : Algebra.FormallySmooth F (IsLocalRing.ResidueField R) := formallySmooth_of_charZero F _
  set r : Fin m → R := fun i => algebraMap A R (a i) with hr_def
  have hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R := fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩

  have hcot : LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
    have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
      rw [← hrsp.2] at this
      exact_mod_cast this
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
    have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
      apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      exact hrsp.1
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
    rw [← Set.range_comp] at hsp
    exact hsp.ge
  have hw := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := F) r hr hcot
  let φ : A → IsLocalRing.ResidueField R ⊗[R] Ω[R⁄F] :=
    fun y => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] KaehlerDifferential.D F R (algebraMap A R y)
  have hw' : LinearIndependent (IsLocalRing.ResidueField R) (φ ∘ a) := hw
  have ha : Function.Injective a := fun i j h => hw'.injective (by simp only [Function.comp_apply, h])
  have hli : LinearIndepOn (IsLocalRing.ResidueField R) φ (Set.range a) :=
    (linearIndepOn_range_iff ha φ).2 hw'
  obtain ⟨b, -, hab, hbsp, hbli⟩ := exists_linearIndepOn_extension hli (Set.subset_univ _)
  have hVsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range φ) = ⊤ :=
    span_tmul_eq_top _ (span_D_algebraMap_eq_top F A R P)
  have hbtop : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField R) (Set.range fun y : b => φ y) := by
    rw [← Set.image_eq_range, ← hVsp, ← Set.image_univ]
    exact Submodule.span_le.2 hbsp
  let bV := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis bV
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_baseChange, hn]
  let σ := Fintype.equivFinOfCardEq hcard
  let e0 : Fin m ↪ b := ⟨fun j => ⟨a j, hab ⟨j, rfl⟩⟩, fun i j h => ha (congrArg Subtype.val h)⟩
  refine ⟨fun i => ((σ.symm i : b) : A), e0.trans σ.toEmbedding, fun j => by
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rfl, ?_⟩
  let ω : Fin n → Ω[R⁄F] := fun i => KaehlerDifferential.D F R (algebraMap A R (σ.symm i : b))
  have hb' : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ω i = bV.reindex σ i := by
    intro i
    rw [Module.Basis.reindex_apply]
    exact (Module.Basis.mk_apply hbli hbtop _).symm
  have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis ω (bV.reindex σ) hb'
  have hli2 : LinearIndependent R ω :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by simp [hn])
  exact ⟨Module.Basis.mk hli2 hspan.ge, fun i => by rw [Module.Basis.mk_apply]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParametersStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_extending_regular_parameters : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  first | exact @GlobalTheory.exists_coords_extending_regularParams | exact GlobalTheory.exists_coords_extending_regularParams | (intros; apply GlobalTheory.exists_coords_extending_regularParams <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbedding
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.GoodTransport

theorem exists_equiv_of_lattices {La : Type} [AddCommGroup La] {g : ℕ} (P P' : La →+ (Fin g → ℂ))
    (hi : Function.Injective P) (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range) (hs' : Submodule.span ℝ (Set.range P') = ⊤) :
    ∃ φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ), ∀ a, φ (P a) = P' a := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  let L' : Submodule ℤ (Fin g → ℂ) := LinearMap.range P'.toIntLinearMap
  haveI : DiscreteTopology L := hd
  haveI : DiscreteTopology L' := hd'
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ L' := ⟨hs'⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hi
  let e' : La ≃ₗ[ℤ] L' := LinearEquiv.ofInjective P'.toIntLinearMap hi'
  let b := Module.Free.chooseBasis ℤ L
  let b₀ := b.map e.symm
  let b' := b₀.map e'
  let φ := (b.ofZLatticeBasis ℝ L).equiv (b'.ofZLatticeBasis ℝ L') (Equiv.refl _)
  have key : (φ.toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap = P'.toIntLinearMap := by
    refine b₀.ext fun k => ?_
    have h1 : P (b₀ k) = b.ofZLatticeBasis ℝ L k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      exact congrArg Subtype.val (e.apply_symm_apply (b k))
    have h2 : P' (b₀ k) = b'.ofZLatticeBasis ℝ L' k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      rfl
    change φ (P (b₀ k)) = P' (b₀ k)
    rw [h1, h2, Module.Basis.equiv_apply]
    rfl
  exact ⟨φ, fun a => LinearMap.congr_fun key a⟩

theorem ex_eq_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z w : Fin g → ℂ) :
    u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel] at this
  rw [← u.ker, this]
  exact mul_eq_right

def imHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (herm Hm z w).im)
    (fun _ _ _ => by simp [herm])
    (fun r z w => by
      rw [herm, herm, smul_dotProduct, Complex.smul_im])
    (fun _ _ _ => by simp [herm, Matrix.mulVec_add])
    (fun r z w => by
      rw [herm, herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, star_trivial])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem fibre_marks {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X}
    (hy : y₀ = Fu.u i P) {s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) → (Fin g → ℂ))
    (hh : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) :
    (∀ (a : 𝓞 E) z, u.ex (h z) ≫ o.t.act.act a = u.ex (h fun k => ty k (a : E) * z k)) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        o.eta a = u.ex (h ((l.M : ℂ)⁻¹ • P (Fu.t i a)))) ∧
      ∀ a, o.etaA a = u.ex (h ((l.A : ℂ)⁻¹ • P (Fu.t i a))) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y :=
    fun x y h => Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨fun a z => inj _ _ ?_, fun a ha => inj _ _ ?_, fun a => inj _ _ ?_⟩
  · rw [hh, Fu.ex_lin i P hP, Over.comp_left, Over.comp_left, ← hh, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · rw [hh, ← Fu.ex_eta i P hP a ha]
    exact m.eta a
  · rw [hh, ← Fu.ex_etaA i P hP a]
    exact m.etaA a

theorem exists_eta_eq (a : D.La) : ∃ a₁ ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta a = o.eta a₁ := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, fun o => ?_⟩
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  conv_lhs => rw [this]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hx trivial), _root_.one_mul]

theorem exists_transport {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P P' : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (hP' : IsPeriod (Fu.Di i) ty P') {y₀ y₀' : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P) (hy' : y₀' = Fu.u i P')
    {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀)
    (m' : ObjMap o' Xo.univ y₀') {g g' : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {κ : u.Λ → ℂ} {κ' : u'.Λ → ℂ}
    (hAH : u.IsAH Hm κ) (hAH' : u'.IsAH Hm' κ') : ∃ φ, IsTransport o o' u u' Hm Hm' φ := by
  obtain ⟨h, hex, hΛ, hE, -⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P y₀ s o m g u Hm κ hP hy hAH
  obtain ⟨h', hex', hΛ', hE', -⟩ :=
    FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P' y₀' s' o' m' g' u' Hm' κ' hP' hy' hAH'
  obtain ⟨a1, a2, a3⟩ := fibre_marks Fu i hP hy m u h hex
  obtain ⟨b1, b2, b3⟩ := fibre_marks Fu i hP' hy' m' u' h' hex'
  obtain ⟨φ₀, hφ₀⟩ := exists_equiv_of_lattices P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ) :=
    ((h.symm.restrictScalars ℝ).trans φ₀).trans (h'.restrictScalars ℝ)
  have hφ : ∀ z, φ (h z) = h' (φ₀ z) := fun z => congrArg (fun t => h' (φ₀ t)) (h.symm_apply_apply z)
  have lat : ∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    obtain ⟨z, rfl⟩ := h.surjective z
    rw [hφ, hΛ, hΛ']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, φ₀.injective ((hφ₀ a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hφ₀ a).symm⟩
  have exq : ∀ z w, u.ex z = u.ex w → u'.ex (φ z) = u'.ex (φ w) := fun z w hzw => by
    rw [ex_eq_iff] at hzw ⊢
    rw [← map_sub, lat]
    exact hzw
  have lin : ∀ (a : 𝓞 E) z, φ₀ (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * φ₀ z k := fun a z => by
    let T : (Fin g₀ → ℂ) →ₗ[ℝ] (Fin g₀ → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have : φ₀.toLinearMap.comp T = T.comp φ₀.toLinearMap := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
      have e1 : T (P x) = P (a • x) := funext fun k => (hP.1 a x k).symm
      have e2 : T (P' x) = P' (a • x) := funext fun k => (hP'.1 a x k).symm
      change φ₀ (T (P x)) = T (φ₀ (P x))
      rw [e1, hφ₀, hφ₀, e2]
    exact LinearMap.congr_fun this z
  have dv : ∀ (n : ℕ) x, φ₀ ((n : ℂ)⁻¹ • P x) = (n : ℂ)⁻¹ • P' x := fun n x => by
    have e : ∀ v : Fin g₀ → ℂ, (n : ℂ)⁻¹ • v = (n : ℝ)⁻¹ • v := fun v => by
      rw [← Complex.coe_smul]; simp
    rw [e, e, map_smul, hφ₀]
  refine ⟨φ, lat, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [a1] at hw
    rw [exq _ _ hw, hφ, hφ, b1, lin]
  · obtain ⟨z, rfl⟩ := h.surjective z
    obtain ⟨w, rfl⟩ := h.surjective w
    let j := (h.restrictScalars ℝ).toLinearMap
    have : (imHerm Hm').compl₁₂ (φ.toLinearMap.comp j) (φ.toLinearMap.comp j) = (imHerm Hm).compl₁₂ j j := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => LinearMap.ext_on_range hP.2.2.2.1 fun y => ?_
      change (herm Hm' (φ (h (P x))) (φ (h (P y)))).im = (herm Hm (h (P x)) (h (P y))).im
      rw [hφ, hφ, hφ₀, hφ₀, hE, hE']
    exact LinearMap.congr_fun (LinearMap.congr_fun this z) w
  · obtain ⟨a₁, ha₁, e⟩ := exists_eta_eq (l := l) a
    rw [e o, a2 a₁ ha₁] at hz
    rw [exq _ _ hz, e o', b2 a₁ ha₁, hφ, dv]
  · rw [a3] at hz
    rw [exq _ _ hz, b3, hφ, dv]

theorem hasTransport_of_goodEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  intro E _ _ _ H D l Xo c O _ β Y U e B io hU hio hr hs hpq he y y' hy hy' hyU hyU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm'
    κ κ' hAH hAH'
  let e₀ : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c e (e₀ j).1) hpq he hty
  have ov : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ toF Xo c = spMap e →
      (x ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun x hx => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, DetExtendZero.spMap_comp]
  obtain ⟨i, P, hP, hu⟩ := Fu.onto _ (ov y hy)
  obtain ⟨i', P', hP', hu'⟩ := Fu.onto _ (ov y' hy')
  obtain rfl : i = i' := GlobalTheory.T.complexPoints_component_same_periodSpace E H D l Xo c O β Y U e _ _ Fu i i' P P' y y' B io hU hio hr hs hy hy' hyU hyU'
    hP hP' hu.symm hu'.symm
  exact exists_transport Fu i hP hP' hu.symm hu'.symm m m' u u' hAH hAH'

end GlobalTheory.DetLine.GoodTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingTransport_of_cmType_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  first | exact @GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb | exact GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb | (intros; apply GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescAb

theorem abLocus_eq (X S : Scheme.{0}) (j : X ⟶ S) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (hc : ∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁)
      (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧
        ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) :
    abLocus G = Set.range j := by
  ext x
  obtain ⟨R, _, _, ξ, G₁, _, π, hx, hp, hab⟩ := hc x
  have h := abLocus_pullback abLocusOne hG hp.1 (closedPoint R)
  rw [hx] at h
  have h' := hab (closedPoint R)
  rw [hx] at h'
  exact h.trans h'

theorem relDim (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j] (hj : IsDominant j) (A : Over X) [GrpObj A]
    (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom)
    (hG : IsSemiAbelian G) (hpb : IsGrpPullback A G j e) : SmoothOfRelativeDimension g G.hom := by
  have : Smooth G.hom := hG.smooth
  have hopen : IsOpenMap G.hom := G.hom.isOpenMap
  choose n W hW hd using H1.exists_dim G.hom
  have key : ∀ y, n y = g := by
    intro y
    obtain ⟨x, w, hwW, hx⟩ := j.denseRange.exists_mem_open (hopen _ (W y).isOpen) ⟨_, ⟨y, hW y, rfl⟩⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w x hx
    refine H1.dim_base hpb.1 (hd y) hA (hpb.1.isoPullback.inv z) ?_
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    exact hwW
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  rw [← key y]; exact hd y

end GlobalTheory.DescAb

theorem GlobalTheory.DescAb.abLocus_eq_range_and_relDim : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsSemiAbelian G → IsGrpPullback A G j e → (∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁) (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧ ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) → abLocus G = Set.range j ∧ SmoothOfRelativeDimension g G.hom := by
  intro X S j _ hj A _ G _ e g _ hA hG hpb hc
  exact ⟨GlobalTheory.DescAb.abLocus_eq X S j G hG hc, GlobalTheory.DescAb.relDim X S j hj A G e g hA hG hpb⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDimStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_group_abelianLocus_and_relDim : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsSemiAbelian G → IsGrpPullback A G j e → (∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁) (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧ ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) → abLocus G = Set.range j ∧ SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.DescAb.abLocus_eq_range_and_relDim | exact GlobalTheory.DescAb.abLocus_eq_range_and_relDim | (intros; apply GlobalTheory.DescAb.abLocus_eq_range_and_relDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVertOfMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_vert_of_mem (S : Type) [CommRing S] [IsDomain S] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp S) [IsDominant p] (f : S) (hf : f ≠ 0) (hx : ∃ x : X, f ∈ (p x).asIdeal) : ∃ z : X, Vert p f z := by
  obtain ⟨x, hfx⟩ := hx
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have key : ∀ q : PrimeSpectrum Γ(X, U), f ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom f ∈ q.asIdeal := by
    intro q
    have h : p (hU.fromSpec q) = (Spec.map φ) q := by
      rw [hφ]; rfl
    rw [h]; rfl
  have key' : ∀ y : U, f ∈ (p y.1).asIdeal ↔ φ.hom f ∈ (hU.primeIdealOf y).asIdeal := by
    intro y
    rw [← key, hU.fromSpec_primeIdealOf]
  have ha : φ.hom f ≠ 0 := by
    intro h0
    have hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.basicOpen f).isOpen
    have hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩
    obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open hO hne
    obtain ⟨w, hwU, hw⟩ := nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩
    have : f ∈ (p w).asIdeal := (key' ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)
    exact hw this
  have hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ((key' ⟨x, hx⟩).1 hfx)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hQp : Q.IsPrime := hQ.1.1
  have haQ : φ.hom f ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self _)
  have h1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have h0 : Q.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    exact ha (by simpa [h] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  let P : PrimeSpectrum Γ(X, U) := ⟨Q, hQp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  clear_value z
  letI := X.presheaf.algebra_section_stalk z
  haveI := hU.isLocalization_stalk z
  refine ⟨z.1, ?_, (key' z).2 (by rw [hP]; exact haQ)⟩
  have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
    (X.presheaf.stalk (z : X))
  rw [this, hP]
  change ((Q.height : ℕ∞) : WithBot ℕ∞) = 1
  rw [hQ1]; rfl

end GlobalTheory.Desc
end

module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.KerSpan

variable {K : Type} [Field K] {σ : K →+* ℂ}

theorem semi_expand {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (f : (Fin m → K) →ₛₗ[σ] W) (v : Fin m → K) :
    f v = ∑ l, σ (v l) • f (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← map_smulₛₗ]
  congr 1
  ext k
  by_cases h : k = l
  · subst h; simp
  · simp [h]

theorem left_inv_of_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0) :
    ∃ L : Matrix (Fin d) (Fin m) K, L * Θ = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Θ)
    (LinearMap.ker_eq_bot'.2 fun a ha => hΘ a ha)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h

theorem map_mulVec_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (c : Fin d → ℂ) (hc : (Θ.map σ) *ᵥ c = 0) : c = 0 := by
  obtain ⟨L, hL⟩ := left_inv_of_inj Θ hΘ
  have h1 : (L.map σ) * (Θ.map σ) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  calc c = ((L.map σ) * (Θ.map σ)) *ᵥ c := by rw [h1, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]

theorem orth_ker_eq_span [NumberField K] [StarRing K] {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    {n d m : ℕ} (j : (Fin n → K) →ₛₗ[σ] V) (H : Matrix (Fin n) (Fin n) K)
    (hinner : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y))
    (hspan : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤)
    (Z : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hp : Formalism.DivisionValues.IsOrthProj H Z Pr)
    (θ : V →ₗ[ℂ] W) (jW : (Fin m → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (hθ : ∀ x, θ (j x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ)ᗮ = Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) := by
  set U := Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) with hU
  set r : (Fin n → K) → V := fun x => j (x - Z *ᵥ (Pr *ᵥ x)) with hr
  set R := Submodule.span ℂ (Set.range r) with hR
  have hPZ : ∀ a, Pr *ᵥ (Z *ᵥ a) = a := fun a => by rw [Matrix.mulVec_mulVec, hp.1, Matrix.one_mulVec]
  have hθr : ∀ x, θ (r x) = 0 := fun x => by
    simp only [hr]
    rw [hθ, Matrix.mulVec_sub, hPZ, sub_self, Matrix.mulVec_zero, map_zero]
  have horth : ∀ a x, inner ℂ (j (Z *ᵥ a)) (r x) = 0 := fun a x => by
    simp only [hr]
    rw [hinner, map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self, map_zero]
  have hRk : R ≤ LinearMap.ker θ := Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hθr x)
  have hUR : U ≤ Rᗮ := by
    have h : U ⟂ R := Submodule.isOrtho_span.2 (by rintro _ ⟨a, rfl⟩ _ ⟨x, rfl⟩; exact horth a x)
    exact h
  have htop : ∀ y : V, ∃ a ∈ U, ∃ b ∈ R, y = a + b := by
    intro y
    have hle : (⊤ : Submodule ℂ V) ≤ U ⊔ R := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have e : j (Pi.single k 1) = j (Z *ᵥ (Pr *ᵥ Pi.single k 1)) + r (Pi.single k 1) := by
        simp only [hr]; rw [map_sub, add_sub_cancel]
      rw [SetLike.mem_coe]
      dsimp only
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle Submodule.mem_top)
    exact ⟨a, ha, b, hb, e.symm⟩
  have hinj : ∀ y ∈ U, θ y = 0 → y = 0 := by
    intro y hy h0
    have hsub : U ≤ Submodule.span ℂ (Set.range fun k => j (Z *ᵥ Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe]
      dsimp only
      rw [show j (Z *ᵥ a) = (j.comp (Matrix.mulVecLin Z)) a from rfl, semi_expand]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsub hy)
    have hc : (Θ.map σ) *ᵥ c = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h0
      simp only [map_smul, hθ, hPZ] at h0
      have e : ∀ k, jW (Θ *ᵥ Pi.single k 1) = ∑ l, σ (Θ l k) • jW (Pi.single l 1) := fun k => by
        rw [semi_expand jW]
        simp
      have h1 : ∑ k, c k • jW (Θ *ᵥ Pi.single k 1) = ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
        simp only [e, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1] at h0
      exact funext (Fintype.linearIndependent_iff.1 hli _ h0)
    have hc0 := map_mulVec_inj Θ hΘ c hc
    subst hc0
    simp
  have hker : LinearMap.ker θ = R := by
    refine le_antisymm (fun y hy => ?_) hRk
    obtain ⟨a, ha, b, hb, rfl⟩ := htop y
    have hb0 : θ b = 0 := hRk hb
    have ha0 : θ a = 0 := by
      rw [LinearMap.mem_ker, map_add (f := _), hb0, add_zero] at hy; exact hy
    rw [hinj a ha ha0, zero_add]; exact hb
  rw [hker]
  refine le_antisymm (fun y hy => ?_) hUR
  obtain ⟨a, ha, b, hb, rfl⟩ := htop y
  have hb' : b ∈ Rᗮ := by
    have h := Rᗮ.sub_mem hy (hUR ha); rwa [add_sub_cancel_left] at h
  have hb0 : b = 0 := by
    have h : b ∈ R ⊓ Rᗮ := Submodule.mem_inf.2 ⟨hb, hb'⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h
    exact (Submodule.mem_bot ℂ).1 h
  rw [hb0, add_zero]; exact ha


set_option maxHeartbeats 2000000 in
theorem orth_ker_thetaP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR : ComplexDataConditionsBaseLevel A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) 1 (U2.eigensystemChoice A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hH.prim.hecke.2.choose) hH.prim.hecke.1.choose hH.prim.hecke.2.choose (R.gEx F) (R.gWx F) := by
    have hUnitary := U2.unitary_two_package A3 (R.toCx3 F) 1 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.prim.hecke.2.choose (R.gWx F) hH.ok
      (RealDat3.kFormR_of hP.char.base.models) (RealDat3.kFormL_of hP.char.base.models) (RealDat3.jIsoR_of hP.char.base.models)
      (RealDat3.jIsoL_of hP.char.base.models) hH.prim.rowTest hH.prim.liftTest hH.prim.heckeL hH.prim.hecke.2.choose_spec hH.prim.gUnit.2 hH.prim.gEquiv.2 hH.prim.levW
      hH.prim.sumW (hH.prim.liftOnto _ hH.prim.hecke.2.choose_spec)
    exact {
      kFormR := RealDat3.kFormR_of hP.char.base.models
      kFormL := RealDat3.kFormL_of hP.char.base.models
      jIsoR := RealDat3.jIsoR_of hP.char.base.models
      jIsoL := RealDat3.jIsoL_of hP.char.base.models
      npTie := ⟨rfl, rfl⟩
      ok := hH.ok
      sep := hH.sep
      heckeR := hH.prim.heckeR
      heckeL := hH.prim.heckeL
      thetaR := hH.prim.hecke.1.choose_spec
      thetaL := hH.prim.hecke.2.choose_spec
      gUnit := hH.prim.gUnit.1
      gEquiv := hH.prim.gEquiv.1
      lev0 := hH.prim.levE.1
      lev1 := hH.prim.levE.2
      h2P := hH.prim.h2P
      gUnitL := hH.prim.gUnit.2
      gEquivL := hH.prim.gEquiv.2
      lower_level_lift_type := hH.prim.levW
      inBlock := hH.prim.block
      rowTest := hH.prim.rowTest
      liftTest := hH.prim.liftTest
      pos := hH.prim.pos
      h0 := RealDat3.height_change_of_D0 hP.char.tup
      h4pos := ⟨fun _ => hH.prim.posScal.1, hH.prim.posScal.2, RealDat.nP_pos⟩
      thmBop := RealDat3.thmBop_of hH.prim.thmB
      partsE := hH.prim.sumE
      kForm := RealDat3.kForm_of hH.prim.unif false
      mLat := hH.prim.mLat
      ewNorm := RealDat3.ewNorm false
      thmAop := RealDat3.thmAop_of hP.char.phase hH.prim.thmA false
      partsW := hH.prim.sumW
      base_lift_test := hH.prim.liftTestB
      galD := hH.prim.scalConj
      dimParts := hH.prim.dimParts
      eig0 := hUnitary.1
      typ0 := hUnitary.2
    }
  have hOk := hH.ok.ok2
  have hT := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hΘ : ∀ a, ((A3.indefDown (s0Of R F)).θ i t) *ᵥ a = 0 → a = 0 := by
    intro a ha
    have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false hR.lifts0.1 hR.ratTh i t a
    have h6 := CxData.tC_cpt_eq (R.toCx3 F) F.cr false i t a
    have ha' : (R.toCx3 F).liftMat F.cr false i t *ᵥ a = 0 := ha
    have h7 : (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) = (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding 0) := by
      rw [h6, ← h2, ha']
      have hz : ∀ {k : ℕ}, cpt A3.fam3.base3.v0.embedding (0 : Fin k → D.what₂.LL) = 0 := fun {k} => by
        funext l; simp [cpt]
      simp only [hz, map_zero]
    exact cpt_injective _ ((hR.lifts0.1 i t).1 h7)
  exact GlobalTheory.Mem.KerSpan.orth_ker_eq_span _ _ (Y.formsL i t).inner (Y.formsL i t).span _ _ hp
    (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (Z.jW i) (hT.1.li i) _ hΘ (fun x => hT.2 i t x)

end GlobalTheory.Mem.KerSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpanStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  first | exact @GlobalTheory.Mem.KerSpan.orth_ker_thetaP | exact GlobalTheory.Mem.KerSpan.orth_ker_thetaP | (intros; apply GlobalTheory.Mem.KerSpan.orth_ker_thetaP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have h1 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h1

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem stalkPt_genStr (B : GlobalTheory.ProjVar.Var F) (e : F ≃+* c.F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (z : B.X) (φA : c.F →+* B.X.presheaf.stalk z)
    (hφ : constF e B = (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp φA) :
    stalkPt B z ≫ j ≫ genStr Z = spMap φA := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (stalkPt B z ≫ j ≫ genStr Z)
  have hgen : spMap (algebraMap (B.X.presheaf.stalk z) B.X.functionField) ≫ stalkPt B z = genericPt B :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec B.X).specializes trivial)
  have hpt : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := (ratOf B).pt_s
  have key : ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ.hom).comp e.toRingHom =
      algebraMap F B.Fn := by
    apply spMap_inj'
    rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, ← hpt, ← hj, ← hgen,
      show spMap ψ.hom = stalkPt B z ≫ j ≫ genStr Z from hψ]
    simp only [Category.assoc]
  have hψeq : ψ.hom = φA := by
    ext a
    apply IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField
    have e1 := RingHom.congr_fun key (e.symm a)
    have e2 := RingHom.congr_fun hφ a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at e1
    simp only [constF, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at e2
    exact e1.trans e2
  rw [← hψ, ← hψeq]
  try rfl

private theorem coord_unique' {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x}
    {ψ₁ ψ₂ : R →+* R'} {g : EigFrame Z φ' x'} {M₁ M₂ : Mat Dw.mult R'} (hψ : ψ₁ = ψ₂)
    (h₁ : f.Coord ψ₁ g M₁) (h₂ : f.Coord ψ₂ g M₂) : M₁ = M₂ := by
  subst hψ
  obtain ⟨hx, hφ, -⟩ := id h₁
  exact ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ₁ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g).1.unique h₁ h₂

private theorem coord_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [IsLocalRing R'']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X}
    {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} {k : EigFrame Z φ'' x''}
    {ψ : R →+* R'} {ψ' : R' →+* R''} {M : Mat Dw.mult R'} {M' : Mat Dw.mult R''}
    (h₁ : f.Coord ψ g M) (h₂ : g.Coord ψ' k M') : f.Coord (ψ'.comp ψ) k (M' * M.map ψ') :=
  GlobalTheory.T.lie_eigenspace_frame_coordinates_comp _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ g _ _ _ k ψ ψ' M M' inferInstance h₁ h₂

private theorem exists_coord_unit_det_of_baseChange {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* R') (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (g : EigFrame Z φ' x') :
    ∃ M : Mat Dw.mult R', f.Coord ψ g M ∧ ∀ τ, IsUnit (M τ).det := by
  have H := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g
  obtain ⟨M, hM, -⟩ := H.1
  exact ⟨M, hM, H.2 M hM⟩

section Lifts

variable (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
  (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn)
  (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X)

theorem coord_iff (hπ : C.π = f ≫ j) (hT : Tied e B j f₀ S A₀) (hT' : Tied e C.Y C.π C.f0 S' A₁)
    (hC : f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹)) (hR : Refines S S' φ f)
    {K : Type} [Field K] {χ : c.F →+* K} {x : Sp K ⟶ gen Z} (p : Sp K ⟶ C.Y.X) (hx : (p ≫ f) ≫ j = x)
    (g : EigFrame Z χ (x ≫ genι Z))
    {A : Mat Dw.mult B.Fn} (_hA : A ∈ S.S (f (p (IsLocalRing.closedPoint K))))
    {φA : c.F →+* B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))}
    {fA : EigFrame Z φA (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z)}
    (hfA : fA.Coord (algebraMap _ B.X.functionField) f₀ (A₀ * A⁻¹))
    {h : Mat Dw.mult K} (hh : fA.Coord (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom g h)
    {A' : Mat Dw.mult C.Y.Fn} (hA' : A' ∈ S'.S (p (IsLocalRing.closedPoint K)))
    {φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))}
    {f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)}
    (hf₁ : f₁.Coord (algebraMap _ C.Y.X.functionField) C.f0 (A₁ * A'⁻¹)) :
    (∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0) ∧
    ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' ↔
      h = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := by
  obtain ⟨hA₀g, -⟩ := id hT
  obtain ⟨hA₁g, -⟩ := id hT'
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁g
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := by
    intro τ
    have e0 : ((A₀.map φ) τ).det = (φ : B.Fn →+* C.Y.Fn) (A₀ τ).det :=
      (RingHom.map_det (φ : B.Fn →+* C.Y.Fn) (A₀ τ)).symm
    rw [e0]
    exact (map_ne_zero _).2 (Fr.det_ne hA₀g τ)
  have hσ : (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField).comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom =
      (φ : B.Fn →+* C.Y.Fn).comp (algebraMap (B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))) B.X.functionField) := by
    ext a
    exact (map_algebraMap_stalk hR.hom _ a).symm
  have hxC : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (f.stalkMap (p (IsLocalRing.closedPoint K))).hom ≫ (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z) := by
    rw [hπ]
    show C.Y.X.fromSpecStalk _ ≫ (f ≫ j) ≫ genι Z =
      Spec.map (f.stalkMap _) ≫ B.X.fromSpecStalk _ ≫ j ≫ genι Z
    simp only [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  obtain ⟨-, hφf₁, -⟩ := id hf₁
  obtain ⟨-, hφfA, -⟩ := id hfA
  have hφ₁ : φ₁ = (f.stalkMap (p (IsLocalRing.closedPoint K))).hom.comp φA := by
    ext a
    apply IsFractionRing.injective (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField
    have e1 := RingHom.congr_fun hφf₁ a
    have e2 := RingHom.congr_fun hφfA a
    have e3 := RingHom.congr_fun hσ (φA a)
    simp only [RingHom.comp_apply] at e1 e2 e3 ⊢
    rw [← e1, e3, ← e2]
    simp [constF]
  obtain ⟨N, hN, hNu⟩ := exists_coord_unit_det_of_baseChange fA (f.stalkMap (p (IsLocalRing.closedPoint K))).hom hxC hφ₁ f₁
  have h2 := coord_comp' hfA hC
  have h4 := coord_comp' hN hf₁
  have h5 := coord_unique' hσ h4 h2
  rw [Mat.map_mul, Mat.map_inv] at h5
  try simp only [AlgHom.coe_toRingHom] at h5
  have hNeq : N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = A' * (A.map φ)⁻¹ := by
    calc N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = (A' * A₁⁻¹) * (A₁ * A'⁻¹ * N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, Mat.mul_inv hA'd, one_mul]
      _ = (A' * A₁⁻¹) * (A₁ * (A₀.map φ)⁻¹ * (A₀.map φ * (A.map φ)⁻¹)) := by rw [h5]
      _ = A' * (A.map φ)⁻¹ := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, mul_assoc A' (A₀.map φ)⁻¹ (A₀.map φ),
            Mat.inv_mul hA₀φ, mul_one]
  have hval : ∀ n : C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)),
      (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := by
    intro n
    calc (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n)
        = (ratOf C.Y).val (spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ C.Y.X.fromSpecStalk (p (IsLocalRing.closedPoint K))) ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) := by
          exact congrArg (fun q : Sp K ⟶ C.Y.X => (ratOf C.Y).val q ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n))
            (spMap_stalkClosedPointTo p).symm
      _ = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := val_ratOf _ _
  have hM : (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) = N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    rw [← hNeq]
    funext τ
    ext a b
    exact hval (N τ a b)
  have hdetN : ∀ τ, ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det ≠ 0 := by
    intro τ
    have e0 : ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det = (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ).det := (RingHom.map_det (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ)).symm
    rw [e0]
    exact ((hNu τ).map _).ne_zero
  have hdetM : ∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0 := by
    rw [hM]; exact hdetN
  have hev : (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom := by
    rw [Scheme.stalkClosedPointTo_comp]; try rfl
  have fwd : ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' → h = h' * N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    intro h' hh'
    exact coord_unique' hev hh (coord_comp' hN hh')
  obtain ⟨hxg, hχ, -⟩ := id hh
  have hxg' : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) := by
    rw [hxC, hxg, hev, spMap_comp_moduli_spaces, Category.assoc]
  have hχ' : χ = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp φ₁ := by
    rw [hχ, hev, hφ₁, RingHom.comp_assoc]
  obtain ⟨h'', hh'', -⟩ := exists_coord_unit_det_of_baseChange f₁ (Scheme.stalkClosedPointTo (R := .of K) p).hom hxg' hχ' g
  refine ⟨hdetM, fun h' => ⟨fun hh' => ?_, fun heq => ?_⟩⟩
  · rw [fwd h' hh', hM]
  · have e1 := fwd h'' hh''
    rw [← hM] at e1
    have e2 : h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) =
        h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := e1.symm.trans heq
    have e3 : h'' = h' := by
      calc h'' = h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
        _ = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [e2]
        _ = h' := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
    rw [← e3]
    exact hh''

end Lifts

theorem flagex_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C B j f₀ S A₀ S' A₁ φ f hj hπ hT hT' hC hR K _ χ x x' hx' hxs g
  obtain ⟨A, hA⟩ := S.nonempty (x' (IsLocalRing.closedPoint K))
  obtain ⟨-, hTie⟩ := id hT
  obtain ⟨φA, fA, hfA⟩ := hTie _ A hA
  have hx'f : spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K)) = x' := spMap_stalkClosedPointTo x'
  obtain ⟨-, hφA, -⟩ := id hfA
  have hsg := stalkPt_genStr B e j hj (x' (IsLocalRing.closedPoint K)) φA hφA
  have hχ : χ = (Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA := by
    apply spMap_inj'
    calc spMap χ = x ≫ genStr Z := hxs.symm
      _ = (x' ≫ j) ≫ genStr Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genStr Z := by rw [hx'f]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genStr Z) := by simp only [Category.assoc]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ spMap φA := by rw [hsg]
      _ = spMap ((Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA) := (spMap_comp_moduli_spaces _ _).symm
  have hxg : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genι Z) := by
    calc x ≫ genι Z = (x' ≫ j) ≫ genι Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genι Z := by rw [hx'f]
      _ = _ := by simp only [Category.assoc]
  obtain ⟨h, hh, hu⟩ := exists_coord_unit_det_of_baseChange fA (Scheme.stalkClosedPointTo (R := .of K) x').hom hxg hχ g
  have hPar : Par (0 : (E →+* ℂ) → ℕ) ⊤ h := fun τ =>
    ⟨fun _ _ => Subring.mem_top _, (hu τ).ne_zero, Subring.mem_top _, fun i _ hi => by simp at hi⟩
  obtain ⟨p, ⟨hp1, hp2⟩, huniq⟩ := hR.lifts K x' A hA h hPar
  obtain ⟨-, hTie'⟩ := id hT'
  have key : ∀ q : Sp K ⟶ C.Y.X, q ≫ f = x' → (Bears S' φ A h q ↔ C.Carries q g) := by
    intro q hq
    subst hq
    rw [GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image _ _ _ _ _ _ _ _ _ _ e C S' A₁ K χ (x ≫ genι Z) g q hT']
    constructor
    · rintro ⟨A', hA', hPar'⟩
      obtain ⟨φ₁, f₁, hf₁⟩ := hTie' _ A' hA'
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', φ₁, f₁, h * ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val q))⁻¹, hf₁, ?_, hPar'⟩
      rw [hci.2, mul_assoc, Mat.inv_mul hci.1, mul_one]
    · rintro ⟨A', hA', φ₁, f₁, h', hf₁, hh', hPar'⟩
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', ?_⟩
      rw [(hci.2 h').1 hh', mul_assoc, Mat.mul_inv hci.1, mul_one]
      exact hPar'
  exact ⟨p, ⟨hp1, (key p hp1).1 hp2⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).2 hq.2⟩⟩

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpaceStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  first | exact @GlobalTheory.ShFam.flagex_lifts | exact GlobalTheory.ShFam.flagex_lifts | (intros; apply GlobalTheory.ShFam.flagex_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl.RowWt

theorem fockDeg_cast (D : D7) (h : DV.KapDef D) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ D.R.m) :
    ((fockDeg D n : ℤ) : ℚ) = ∑ τ, (∑ a : Fin (D.R.sigW n).1, |DV.aPlusQ D n τ a| +
      ∑ c : Fin (D.R.sigW n).2, |DV.aMinusQ D n τ c|) := by
  unfold fockDeg
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [(h n h1 h2 τ).1 a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h n h1 h2 τ).2 c, abs_neg]

theorem fockDeg_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z Z' : w.Lt)
    (h : DV.KapDef (w.D Z)) (h' : DV.KapDef (w.D Z')) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ (w.D Z).R.m) :
    fockDeg (w.D Z) n = fockDeg (w.D Z') n := by
  have e := fockDeg_cast (w.D Z) h n h1 h2
  have e' := fockDeg_cast (w.D Z') h' n h1 h2
  exact_mod_cast e.trans e'.symm

theorem forcedContent_eq_over_same_choices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt), DV.KapDef (w.D Z) →
    DV.KapDef (w.D Z') → F0K K.s (w.D Z) = F0K K.s (w.D Z') := by
  intro K B f T w Z Z' h h'
  funext y j
  have hT : FTypeG (w.D Z) (j.1 + 1) = FTypeG (w.D Z') (j.1 + 1) := by
    unfold FTypeG
    rw [fockDeg_eq w Z Z' h h' (j.1 + 1) (Nat.succ_pos _) j.2]
  unfold F0K FK
  rw [hT]
  rfl

end GlobalTheory.Mem.Top.Bl.RowWt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.F0K_eq_of_kapDef : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt), DV.KapDef (w.D Z) →
    DV.KapDef (w.D Z') → F0K K.s (w.D Z) = F0K K.s (w.D Z') := by
  first | exact @GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices | exact GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices | (intros; apply GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw


open Classical in
noncomputable def wtPre (P : Pre) (j : ℕ) (aP : Tau P.R → Fin (P.R.sigW j).1 → ℕ) (aM : Tau P.R → Fin (P.R.sigW j).2 → ℕ)
    (x : (P.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : Tau P.R, ((if x.1 = P.host.emb t.1 then Formalism.L2.Pj.ext0 (aP t) x.2 else 0) +
    if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (P.host.emb t.1) then Formalism.L2.Pj.ext0 (aM t) x.2 else 0)

theorem cusp_type_congr {P₁ P₂ : Pre} (hP : P₂ = P₁)
    {H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₁.host.E} {H₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₂.host.E}
    {l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁} {l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₂}
    {c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁} {c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂}
    {Dw₁ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₁} {Dw₂ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₂}
    {Xo₁ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₁ j) l₁} {Xo₂ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₂ j) l₂}
    {U₁ : ∀ j (σ : c₁.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₁ j) c₁ σ P₁.R.r}
    {U₂ : ∀ j (σ : c₂.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₂ j) c₂ σ P₂.R.r}
    {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    {aP₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).1 → ℕ} {aP₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).1 → ℕ}
    {aM₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).2 → ℕ} {aM₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).2 → ℕ}
    {n₁ n₂ : ℕ} (hn : n₂ = n₁)
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hDw : HEq Dw₂ Dw₁) (hXo : HEq Xo₂ Xo₁) (hU : HEq U₂ U₁)
    (haP : HEq aP₂ aP₁) (haM : HEq aM₂ aM₁) :
    ↥(Formalism.L2.Pj.cusp (Xo₂ j₂) c₂ (U₂ j₂) (wtPre P₂ j₂ aP₂ aM₂) n₂) =
      ↥(Formalism.L2.Pj.cusp (Xo₁ j₁) c₁ (U₁ j₁) (wtPre P₁ j₁ aP₁ aM₁) n₁) := by
  subst hP hj hn
  cases hH; cases hl; cases hc; cases hDw; cases hXo; cases hU; cases haP; cases haM
  rfl

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 4000000 in
theorem Ext.cuspA_type_eq : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX i₁ i₂ hi
  have hk := hX.κ i₁ i₂ hi
  exact (cusp_type_congr hE.left (congrArg (fun x ↦ x + 1) hi) hk.right.right hX.H hX.l hX.c hX.Dw hX.Xo hX.U hk.left hk.right.left)

end GlobalTheory.Mem.R3.Rw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormType_eq_at_corresponding_lifts : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  exact @GlobalTheory.Mem.R3.Rw.Ext.cuspA_type_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProduct
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ProjFinProd

theorem exists_isProjOver_finite_prod : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  intro O _ ι _ X s
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro Y f hs hf
    rename_i α β
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (e i)) (fun i => f (e i)) hs (fun i => hf _)
    have key : ∀ j : β, ∃ q : P ⟶ Y j, q ≫ f j = p0 ≫ s ∧ ∀ i (h : e i = j), q = p i ≫ eqToHom (congrArg Y h) := by
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      refine ⟨p i, hp i, fun i' h => ?_⟩
      obtain rfl := e.injective h
      simp
    choose q hq1 hq2 using key
    have hq : ∀ i, q (e i) = p i := fun i => by simpa using hq2 (e i) i rfl
    refine ⟨P, p0, q, hP, hq1, fun Z a b hb => ?_⟩
    obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (e i)) (fun i => hb _)
    refine ⟨h, ⟨h1, fun j => ?_⟩, fun h' hh => h3 h' ⟨hh.1, fun i => ?_⟩⟩
    · obtain ⟨i, rfl⟩ := e.surjective j
      rw [hq]; exact h2 i
    · rw [← hq]; exact hh.2 _
  | h_empty =>
    intro Y f hs hf
    refine ⟨X, 𝟙 X, fun i => i.elim, by simpa using hs, fun i => i.elim, fun Z a b _ => ?_⟩
    exact ⟨a, ⟨by simp, fun i => i.elim⟩, fun h hh => by simpa using hh.1⟩
  | h_option ih =>
    intro Y f hs hf
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (some i)) (fun i => f (some i)) hs (fun i => hf _)
    refine ⟨pullback (p0 ≫ s) (f none), pullback.fst _ _ ≫ p0,
      fun i => match i with
        | none => pullback.snd _ _
        | some i => pullback.fst _ _ ≫ p i, ?_, ?_, fun Z a b hb => ?_⟩
    · rw [Category.assoc]
      exact isProjOver_pullback hP (hf none)
    · rintro (_ | i)
      · simp only [Category.assoc]; exact pullback.condition.symm
      · simp only [Category.assoc]; rw [hp i]
    · obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (some i)) (fun i => hb _)
      refine ⟨pullback.lift h (b none) (by rw [reassoc_of% h1, hb]), ⟨?_, ?_⟩, fun h' hh => ?_⟩
      · rw [pullback.lift_fst_assoc, h1]
      · rintro (_ | i)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h2 i)
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine h3 _ ⟨by simpa using hh.1, fun i => ?_⟩
          simpa using hh.2 (some i)
        · rw [pullback.lift_snd]; exact hh.2 none

end GlobalTheory.ProjFinProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProductStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isProjOver_finite_fibreProduct : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  first | exact @GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | exact GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | (intros; apply GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomain
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibreInt

theorem dens_neg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : dens (-B) y = dens B y := by
  unfold dens
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_neg, Matrix.neg_mul, lminor, lminor, submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg]
  simp

theorem shear_neg_J {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (-Jpq p q) Z = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
  simp [shear, Jpq, hQ, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_neg_add]

theorem flagConst_pos (m : ℕ) : 0 < flagConst m :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem lintegral_dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  intro r p q e he A hA v hv
  set Z := toMat v with hZ
  have hH : (hQ Z).PosDef := hv
  have hd := hH.det_pos
  have hu : IsUnit (hQ Z).det := hd.ne'.isUnit
  set B : Matrix (Fin p) (Fin p) ℂ := 1 + Z * (hQ Z)⁻¹ * Zᴴ with hB
  have hBp : B.PosDef := PosDef.one.add_posSemidef (hH.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hs : schur (shear (-Jpq p q) Z) = -B := by
    rw [shear_neg_J, schur, hB]
    simp
    abel
  have h22 : (shear (-Jpq p q) Z).toBlocks₂₂ = hQ Z := by rw [shear_neg_J, toBlocks_fromBlocks₂₂]
  have hdet : B.det = ((hQ Z).det)⁻¹ := by
    have e1 : (1 : Matrix (Fin q) (Fin q) ℂ) + (hQ Z)⁻¹ * Zᴴ * Z = (hQ Z)⁻¹ := by
      rw [Matrix.mul_assoc, ← nonsing_inv_mul _ hu, ← Matrix.mul_add, hQ, sub_add_cancel, Matrix.mul_one]
    rw [hB, Matrix.mul_assoc, det_one_add_mul_comm, e1, det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨d, hd0, hdd⟩ : ∃ d : ℝ, 0 < d ∧ (hQ Z).det = d := by
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hd
    exact ⟨_, h1, Complex.ext (by simp) (by simp [← h2])⟩
  have hpt : ∀ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) =
      (ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) b.1)) * ENNReal.ofReal (dens B b.2) := by
    intro b
    rw [GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular r p q e he A (v, b) (by rw [hA]; exact h22 ▸ hu), hA]
    simp only [← hZ]
    rw [h22, hs, dens_neg, hdd, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (dens_nonneg _ _)),
      mul_comm (dens (hQ Z) b.1)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, lintegral_prod_mul
    (f := fun y => ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) y))
    (g := fun y => ENNReal.ofReal (dens B y))
    ((measurable_dens _).ennreal_ofReal.const_mul _).aemeasurable (measurable_dens _).ennreal_ofReal.aemeasurable,
    lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hH, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hBp, hdet, hdd,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  have hp := flagConst_pos p
  have hq := flagConst_pos q
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [_root_.inv_zpow', ← mul_div_assoc _ _ (flagConst q), div_mul_div_comm, ← zpow_add₀ hd0.ne', ← zpow_add₀ hd0.ne', mul_comm (flagConst q)]
  congr 2
  push_cast
  ring

end GlobalTheory.FlagFibreInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomainStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  first | exact @GlobalTheory.FlagFibreInt.lintegral_dens_glue | exact GlobalTheory.FlagFibreInt.lintegral_dens_glue | (intros; apply GlobalTheory.FlagFibreInt.lintegral_dens_glue <;> assumption)
end
end

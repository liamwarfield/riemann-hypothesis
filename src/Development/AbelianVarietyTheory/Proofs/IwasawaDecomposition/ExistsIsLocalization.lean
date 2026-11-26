module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.BCEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {p : ℕ} {W : ValuationSubring ℂ}

section Local

variable {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Local

section Global

variable {l : Level H} {c : Coeff l}

theorem exists_isLocalization (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ M : Submonoid (𝓞 c.F), letI := b.toAlgebra; IsLocalization M (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  letI := b.toAlgebra
  refine ⟨v.asIdeal.primeCompl, IsLocalization.isLocalization_of_algEquiv _ (S := v.valuationSubringAtPrime c.F)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hv)) fun x => ?_)⟩
  exact Subtype.ext (hb x).symm

variable {Xo : Moduli Dw l}

end Global

end GlobalTheory.ShFam.Pad.BCEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqWeightRatio
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram

theorem coef_eq_coW_change {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin j => coef X x x' τ.1 b i) = (coW X hj x' τ)⁻¹ * coW X hj x τ := by
  have hd' : IsUnit (mat x' τ).det := (hx' τ).1.isUnit
  have hN : frameCo X hj x τ = frameCo X hj x' τ * reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) := by
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd']
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hW : coW X hj x τ = coW X hj x' τ * (reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ)).toBlocks₁₁ := by
    unfold coW
    rw [h, hN, moeb_zero]
    generalize frameCo X hj x' τ = g at *
    generalize reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) = N
    have e11 : (g * N).toBlocks₁₁ = g.toBlocks₁₁ * N.toBlocks₁₁ + g.toBlocks₁₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]
    have e21 : (g * N).toBlocks₂₁ = g.toBlocks₂₁ * N.toBlocks₁₁ + g.toBlocks₂₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    rw [e11, e21]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu']
    abel
  rw [hW, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 ((isUnit_iff_isUnit_det _).2 (isUnit_coW X hj hp hx' τ))), Matrix.one_mul]
  ext b i
  have hb : X.p0 + (b : ℕ) < r := by have := b.2; have := X.p0_le; omega
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; have := X.p0_le; omega
  have eb : (idx hj).symm (Sum.inl b) = ⟨X.p0 + b, hb⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (b : ℕ) = X.p0 + b; omega)
  have ei : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (i : ℕ) = X.p0 + i; omega)
  simp only [of_apply, coef, dif_pos τ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, toBlocks₁₁, reindex_apply,
    submatrix_apply, eb, ei]

end GlobalTheory.FramePairGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbPartActIsAdj
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Vert GlobalTheory.LocM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocM

open ReciprocityTheory.ChartRestriction.G.Out (RosatiAdj rosatiφ rosatiε)
open GlobalTheory.CechPic

theorem abPartAct_isAdj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (t : SAB H (Sp R)) (U : PELUnif I t) :
    GlobalTheory.HermTensor.IsAdj (abPartAct U) U.D.toPre.P.L := by
  intro c
  have hr : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (star c)) := by
    have h : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (H.bar c)) := by
      letI := H.starRing
      exact U.oD.onB.rosati c
    rw [← bar_eq_star H]
    exact h
  obtain ⟨V, hV, g, hg⟩ := hr (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have hL : U.D.toPre.P.L.IsLB := U.D.toPre.P.isLB
  have hgen : ∃ u : LB.Gen (LB.LinComb U.D.toPre.P.L
      (rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c))) rosatiε), u.IsGen := by
    have e : rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) = fun i =>
        (U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv ≫ ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).hom ⁻¹ᵁ ⊤).ι ≫
          rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) i :=
      funext fun i => ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv_hom_id_assoc _).symm
    rw [e]
    exact ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hg _⟩
  obtain ⟨u, hu⟩ := hgen
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩
  rw [cls_linComb hL, Fin.sum_univ_six] at h0
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1 ?_
  refine (cls_cube_two hL _ _ _).trans (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
  have pm : ∀ a b : U.D.toPre.P.A ⊗ U.D.toPre.P.A ⟶ U.D.toPre.P.A, padd U.D.toPre.P.A a b = a * b := fun _ _ => rfl
  simp only [rosatiφ, rosatiε, lam, pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    one_smul, neg_smul, Fin.isValue] at h0 ⊢
  rw [← sub_eq_zero, ← h0]
  abel

end GlobalTheory.LocM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlatSec

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_trans {R k : Type} [CommRing R] [Field k] {φ : c.F →+* R} {φ' φ'' : c.F →+* k} {x : Sp R ⟶ Z.X}
    {x' x'' : Sp k ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* k} {g : EigFrame Z φ' x'} {g' : EigFrame Z φ'' x''}
    {t d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (h : f.Tri ψ g t) (h' : g.Tri (RingHom.id k) g' d) :
    f.Tri ψ g' (fun τ i => t τ i * d τ i) := by
  have h1 : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id k)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨e1, e2, h'⟩ := h'
  rw [h1, Category.id_comp] at e1
  subst e1
  refine ⟨rfl, e2, fun τ i => ?_⟩
  choose a a1 a2 a3 using h τ
  obtain ⟨cf, b1, b2, b3⟩ := h' τ i
  simp only [h3, Category.id_comp] at b3
  let A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k := fun j i => a i j
  have hA : A.BlockTriangular id := fun j k hk => a2 k j hk
  obtain ⟨c1, c2⟩ := Guard.tri_mulVec hA b2
  refine ⟨A.mulVec cf, ?_, c1, tanLinG _ (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)) _ A cf _ a3 b3⟩
  rw [c2, b1, show A i i = t τ i from a1 i, Units.val_mul]

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

variable {K : Type} [Field K] (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ)

end Gen

end GlobalTheory.ShFam.FlatSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.LiftOnto

set_option maxHeartbeats 1000000 in
theorem thetaMap_surjective : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t _
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hTh.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  refine ⟨D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z)), ?_⟩
  have hz' : lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) = z := by
    refine (Matrix.mulVec_mulVec _ _ _).trans ?_
    exact (congrArg (fun M => M *ᵥ z) hp.1).trans (Matrix.one_mulVec z)
  show _ = Z.jW i (Pi.single k 1)
  rw [hθ i t]
  exact congrArg (Z.jW i) ((congrArg (((A3.indefDown (s0Of R F)).θ i t).mulVec) hz').trans hz)

end GlobalTheory.Mem.LiftOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTupleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.Mem.LiftOnto.thetaMap_surjective | exact GlobalTheory.Mem.LiftOnto.thetaMap_surjective | (intros; apply GlobalTheory.Mem.LiftOnto.thetaMap_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqOmegaRatio
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePairGram

theorem coef_conj_eq_coOm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin (r - j) => coef X x x' (conjEmb τ.1) b i) =
      (((coOm X hj x τ)⁻¹ * coOm X hj x' τ)ᵀ).submatrix Fin.rev Fin.rev := by
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ =
      reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have h12 : (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₁₂ = 0 := by
    ext a c
    simp only [toBlocks₁₂, of_apply, reindex_apply, submatrix_apply, Matrix.zero_apply]
    apply PointWell.block_of_moeb_eq X hj hp hx hx' τ h
    · rw [idx_symm_inl, hp]; omega
    · rw [idx_symm_inr, hp]; exact c.2
  have hO : (coOm X hj x τ)⁻¹ * coOm X hj x' τ =
      (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
    have e : frameCo X hj x' τ = frameCo X hj x τ * reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
      rw [← hN, mul_nonsing_inv_cancel_left _ _ hf]
    have e2 : coOm X hj x' τ = coOm X hj x τ * (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
      rw [coOm, coOm, e]
      conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x τ),
        ← fromBlocks_toBlocks (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)), fromBlocks_multiply,
        toBlocks_fromBlocks₂₂]
      rw [h12, Matrix.mul_zero, zero_add]
    rw [e2, ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_coOm X hj hp hx τ), Matrix.one_mul]
  have cc : conjEmb (conjEmb τ.1) = τ.1 := RingHom.ext fun a => by simp [conjEmb]
  have hcc : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [cc]; exact τ.2
  have hc : conjEmb τ.1 ∉ X.Ψ := fun hc => ((X.cmType τ.1).mp τ.2) hc
  have hs : (⟨conjEmb (conjEmb τ.1), hcc⟩ : X.Ψ) = τ := Subtype.ext cc
  rw [hO]
  ext b i
  have hb := b.2
  have hi := i.2
  have hl : X.p0 - 1 - (i : ℕ) < r ∧ X.p0 - 1 - (b : ℕ) < r := by omega
  simp only [of_apply, submatrix_apply, transpose_apply, coef, dif_neg hc, dif_pos hcc, ent, dif_pos hl, hs,
    toBlocks₂₂, reindex_apply]
  refine congrArg₂ _ (Fin.ext ?_) (Fin.ext ?_) <;> simp [idx_symm_inr, Fin.val_rev, hp] <;> omega

end GlobalTheory.FramePairGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : P.D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ P.D χ).choose

theorem isQ_qv : QForm.IsQ P.D.toPre ϖ (qv P hϖ) := fun χ => (QForm.exists_QVal hϖ P.D χ).choose_spec

def beF : LinearMap.BilinForm ℤ P.D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D (isQ_qv P hϖ) a b)
    (fun a a' b => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : P.D.toPre.X) : beF P hϖ a b = beF P hϖ b a := QForm.bOf_comm P.D a b

theorem beF_self (a : P.D.toPre.X) : beF P hϖ a a = 2 * qv P hϖ a :=
  (QForm.two_Q_eq hϖ P.D (isQ_qv P hϖ) a).symm

theorem beF_adj (x : 𝓞 E) (a b : P.D.toPre.X) : beF P hϖ (x • a) b = beF P hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ P.D GlobalTheory.abelianSchemeLaws_all.1 P.oD (isQ_qv P hϖ) x a b

theorem beF_w0 (a : P.D.toPre.X) : beF P hϖ a (H.w0 • a) = qv P hϖ a := by
  have h₁ := beF_adj P hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm P hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self P hϖ a
  omega

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

def tF (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b))

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist P.D.toPre H.w0 (tF P hϖ)

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)

end ThetaShiftProofs

end GlobalTheory.ArcBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorFrHolo

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)

theorem isDerivAt0_of_cart {g : ℕ} {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) (pt : Sp ℂ ⟶ X') {e : (Fin g → ℂ) → (Sp ℂ ⟶ G')} (he : ∀ z, e z ≫ h' = pt)
    (hol : IsHolTo Set.univ fun z => e z ≫ φ) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ G'}
    (hv : v ≫ h' = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ pt) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  have H := (IsPullback.of_hasPullback h' pt).paste_horiz hc
  have key := FibreDeriv.isDerivAt0_of_isPullback H
    (e := fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp]))
    (fun z => pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hol)
    (v := pullback.lift v _ hv) (pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hd)
  simpa only [pullback.lift_fst] using isDerivAt0_comp_hom key (pullback.fst h' pt)

theorem isHolTo_lift {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) {n g : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (a : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (ha : IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => a bz.1 bz.2) (hp : IsHolTo B p)
    (w : ∀ b z, a b z ≫ h = p b ≫ f) :
    IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => hc.lift (a bz.1 bz.2) (p bz.1) (w _ _) := by
  let L : (Fin (n + g) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin g → ℂ) :=
    ((LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin g) ℂ ℂ)).toContinuousLinearEquiv
  have hC : IsOpen (L ⁻¹' (B ×ˢ Set.univ)) := (hB.prod isOpen_univ).preimage L.continuous
  have h1 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => a (L c).1 (L c).2 :=
    LocLift.isHolTo_comp ha hC L.differentiableOn fun _ h => h
  have h2 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => p (L c).1 :=
    LocLift.isHolTo_comp hp hC (β := fun c => (L c).1) (by fun_prop) fun _ h => h.1
  have h3 := holPair _ _ _ h f _ _ _ _ (fun c => w (L c).1 (L c).2) hC h1 h2
  have h4 := isHolTo_comp h3 hc.isoPullback.inv
  have key : ∀ c, pullback.lift (a (L c).1 (L c).2) (p (L c).1) (w _ _) ≫ hc.isoPullback.inv =
      hc.lift _ _ (w (L c).1 (L c).2) := fun c => hc.hom_ext
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.lift_fst]
      exact pullback.lift_fst _ _ _)
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_snd, IsPullback.lift_snd]
      exact pullback.lift_snd _ _ _)
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h4 ((hB.prod isOpen_univ)) (β := L.symm)
    L.symm.differentiableOn fun q hq => by simpa using hq) fun q _ => ?_
  refine Eq.trans ?_ (key (L.symm q)).symm
  simp only [L.apply_symm_apply]

section Family

open GlobalTheory.TrueCx.TorHolo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

end Family

end GlobalTheory.TrueCx.TorFrHolo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaMulRationalVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaMulRationalVectors
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric

set_option maxHeartbeats 2000000 in
theorem inner_theta_rat_eq_lam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) a b, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p a b hyp
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT : ∀ c, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding c)) = Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c)))) := by
    intro c
    rw [GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t, CxData.tC_cpt_eq]
    show Tw.out (R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) _)) = _
    have h3 := GlobalTheory.Mem.LiftForms.lvlForm_lE (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1) c
    have h3' : ((crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc).toL (R.toCx3 F).zs false i t) c = liftForm A3.A F.P0 F.ψ0 i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c) := h3.symm
    rw [hP.phs i, one_smul]
    show R.thG i t (R.jV i t (((crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc).toL (R.toCx3 F).zs false i t) c)) = _
    exact congrArg (fun z => R.thG i t (R.jV i t z)) h3'
  have hW : (R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a) ∈ (R.toCx3 F).Wp i p := by
    show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a)) ∈ R.Wp3 i p
    exact (congrArg (· ∈ R.Wp3 i p) (hT a)).mpr hyp
  have hA := hR.lifts0.2 i t p a hW b
  have hL : ⟪(R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a), (R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding b)⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) ⟪Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))⟫_ℂ := by
    refine (Tw.inner_eq (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) _ _).trans ?_
    exact congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrArg₂ (fun x y => ⟪x, y⟫_ℂ) (hT a) (hT b))
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin ((lv (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs) false).dZ i t))) ((lv (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs) false).XT i t) A3.fam3.base3.v0 a b = A3.A.v0.embedding (star a ⬝ᵥ ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) *ᵥ b) := by
    have hm : metOf ((A3.A.fam.L i t).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t) A3.A.v0) = ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)).map A3.A.v0.embedding :=
      (BlockDat.XQ_herm hOk.conj (hOk.lifts i t) hOk.irr).2
    show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((A3.A.fam.L i t).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) A3.A.v0 a b = _
    rw [Formalism.L2.DIV.majAt_eq, hm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : A3.A.v0.embedding (star (a k)) = starRingEnd ℂ (A3.A.v0.embedding (a k)) := hOk.conj (a k)
    rw [hc]
    rfl
  have hU : ⟪(D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = D.what₂.embLL (star a ⬝ᵥ ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) *ᵥ b) := by
    have hf := (Y.formsL i t).inner (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)
    have hl := BlockDat.lf_lE_form (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1)
    refine hf.trans ?_
    congr 1
    exact (GlobalTheory.Mem.LiftForms.hform_mulVec (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) a b).trans (congrArg (fun M => star a ⬝ᵥ M *ᵥ b) hl)
  have hv : ∀ c, A3.A.v0.embedding c = cj (twAt D.what₂.embLL A3.A.v0) (D.what₂.embLL c) := by
    intro c
    rw [emb_eq D.what₂.embLL A3.A.v0 c, sgAt_mk _ R.hv0]
  have hN := GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i) (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))
  have h1 : cj (twAt D.what₂.embLL A3.A.v0) (((RealDat.nP F.lv2 false : ℝ) : ℂ) * ⟪(D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))), (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))⟫_ℂ) = ((RealDat.nP F.lv2 false * R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * cj (twAt D.what₂.embLL A3.A.v0) ⟪(D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ := by
    rw [← hN, ← hL, hA, hmaj, hv, hU]
    rfl
  have h2 := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) h1
  rw [Links.cj_cj, map_mul, cj_ofReal, Links.cj_cj] at h2
  have hnp : ((RealDat.nP F.lv2 false : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (RealDat.nP_pos (F := F.lv2) false).ne'
  apply mul_left_cancel₀ hnp
  rw [h2]
  push_cast
  ring

end GlobalTheory.Mem.R3.LamMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaMulRationalVectorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) a b, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))⟫_ℂ := by
  first | exact @GlobalTheory.Mem.R3.LamMetric.inner_theta_rat_eq_lam | exact GlobalTheory.Mem.R3.LamMetric.inner_theta_rat_eq_lam | (intros; apply GlobalTheory.Mem.R3.LamMetric.inner_theta_rat_eq_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtEx

theorem nonempty_basis_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n : ℕ} {v : Fin n → (epsR R ⟶ G')} (hb : IsLieBasis v) :
    Nonempty (Module.Basis (Fin n) R (TanM x G)) := by
  let u : Fin n → TanM x G := fun j => mkT (pushHom h (epsR R) (v j)) ((PullbackSections.isTangent_iff h _).1 (hb.1 j))
  have hcomb : ∀ (a : Fin n → R) (w : epsR R ⟶ G'), IsLieComb a v w ↔
      pushHom h (epsR R) w = tv (∑ i, a i • u i) := fun a w => by
    rw [PullbackSections.isLieComb_iff h, GlobalTheory.FlagMod.tv_sum']
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination R u) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact tv_mem W)
    refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
  exact ⟨(Pi.basisFun R (Fin n)).map (LinearEquiv.ofBijective _ hbij)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_keyAt_of_sabMap (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hg : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, th, ⟨hw, hr⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev z M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev z M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ z he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp R ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  refine ⟨⟨GlobalTheory.GenericPol.toPolAV t M.n hg hp hA hK, hn, t.PP.rig, t.PP.rigGen, th, fun s => ?_, v, hb⟩, rfl,
    m.φ, he, w, rfl, m.cart, hw, hrig ▸ hr, fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, h₁, h₂⟩ := hne s
    exact ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  · refine (hth (j PUnit.unit) i _ h le_rfl).trans ?_
    exact congrArg (· * _) (GlobalTheory.LB.resG_self _ _)
  · exact hm' ▸ hv i

theorem smoothOfRelativeDimension_fibre {K : Type} [Field K] {z : Sp K ⟶ Y.X} {t : SAB H (Sp K)} (m : SABMap t Y.t z)
    (h : Set.range z ⊆ Set.range Y.j) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom := by
  obtain ⟨K', _, i, y, e⟩ := GlobalTheory.GenericPol.exists_lift z Y.j h
  obtain ⟨t', ⟨m₁⟩⟩ := GlobalTheory.ModFam.exists_sabPull (Out.specOf i) t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t' Y.j y Y.m (e ▸ n)
  have h₁ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m'.cart.1
      (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace ↥t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have h₂ : SmoothOfRelativeDimension d t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m₁.cart.1 hd
  rw [← H1.dim_unique _ h₂ h₁ (eSec t'.G (default : PrimeSpectrum K'))]
  exact hd

theorem exists_keyAt_model (M : GChart Y) {K : Type} [Field K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (h : Set.range z ⊆ Set.range Y.j) (hpos : 1 ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) :
    ∃ x : KeyIn K, x.P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull z Y.t
  obtain ⟨hp, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv m h
  have hg := smoothOfRelativeDimension_fibre m h
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis t.G hg
  obtain ⟨b⟩ := nonempty_basis_of_isLieBasis m.cart hv
  have hn : Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = M.n := by
    simpa using Fintype.card_congr (b.indexEquiv (GlobalTheory.FlagMod.lieBasis M.toMChart z hz))
  rw [hn] at hg hpos ⊢
  exact exists_keyAt_of_sabMap M z hz m hp hA hK hg hpos

end GlobalTheory.KeyAtEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtBC

theorem appLE_eq_iff_stalk {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {V : X.Opens} (hV : ∀ y, F y ∈ V) (s : ∀ j, Γ(X, V ⊓ L.U j)) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ (V ⊓ L.U (j PUnit.unit))),
      (F.appLE _ _ hle).hom (s (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ (V ⊓ L.U j) := fun y hy => ⟨hV y, mem_pull.1 hy.1⟩
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

theorem mem_of_comm {X X' T T' : Scheme.{0}} {F : X' ⟶ X} {π : X ⟶ T} {π' : X' ⟶ T'} {z : T' ⟶ T}
    (e : F ≫ π = π' ≫ z) {U : T.Opens} (hz : ⊤ ≤ z ⁻¹ᵁ U) (y : X') : F y ∈ π ⁻¹ᵁ U := by
  show π (F y) ∈ U
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hz (Set.mem_univ _)

theorem spMap_comp₀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : GChart Y} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {z : Sp R ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U}
  {x : KeyIn R} {x' : KeyIn R'}

theorem keyAt_of_keyPB (h : KeyAt M z hz x) (h' : KeyPB x' x f) :
    KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x' := by
  obtain ⟨φ, he, w, hg, hp, hw, hr, hs, hv⟩ := h
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := h'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x.P.isLB w w' g g' Y.t.PP.isLB x'.P.isLB
  have he'' : eSec x'.P.A ≫ φ' ≫ φ = (spMap f ≫ z) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [Chart.dualMapR])
  have hq := hp'.comp hp
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, hq, (isGen_iff w'').2 (T.pgen_comp x.P.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _
      (rigPull_le φ z he Y.t.PP.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ' (spMap f) he' x.P.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
      (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp x.P.isLB (fun _ => he') r₀ r₁)
  · refine (appLE_eq_iff_stalk w'' (mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ x'.th).2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x.P.isLB (φ' (q y))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.1.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).1 hs' Z q y i k hi hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [← Category.assoc, hv', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
      hF, Category.assoc]
    rfl

theorem keyPB_of_keyAt (h : KeyAt M z hz x) (h' : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x') :
    KeyPB x' x f := by
  obtain ⟨φ, he, w, hg, hc, hw, hr, hs, hv⟩ := h
  obtain ⟨φ'', he'', w'', hg'', hc'', hw'', hr'', hs'', hv''⟩ := h'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x'.P.A.left ⟶ x.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x.P.A.hom = x'.P.A.hom ≫ spMap f :=
    ⟨hp.lift φ'' (x'.P.A.hom ≫ spMap f) (by rw [hc''.1.w, Category.assoc]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x'.P.A ≫ φ' = spMap f ≫ eSec x.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', Category.assoc, Category.assoc, he]
    · have a₁ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      have a₂ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel Y.t.PP.isLB w w'' g g'' x.P.isLB x'.P.isLB
  have r := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _ (rigPull_le φ z he Y.t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
    (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).1 hr''
  refine ⟨φ', he', w', hg''.trans hg.symm, Chart.dualMapR f, hc.cancel hc'' hw0,
    (isGen_iff w').2 (T.pgen_cancel Y.t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ' (spMap f) he' x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel Y.t.PP.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).2 fun Z q y i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (φ (φ' (q y)))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (appLE_eq_iff_stalk w'' (mem_of_comm hc''.1.w (le_preimage_comp _ hz)) M.θ x'.th).1 hs'' Z q y j k hj hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
        Category.assoc]
      rfl
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyAtBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem spMap_fromSpec_mem_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [Field K]
    (ψ : Γ(X, U) →+* K) (p : Γ(X, U)) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ X.basicOpen p ↔ ψ p ≠ 0 := by
  have h : spMap ψ s ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen p ↔ ψ p ≠ 0 := by
    rw [hU.fromSpec_preimage_basicOpen]
    change ψ p ∉ (show PrimeSpectrum K from s).asIdeal ↔ _
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum K from s).asIdeal, Ideal.mem_bot]
  exact h

theorem spMap_fromSpec_mem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {K : Type} [CommRing K]
    (ψ : Γ(X, U) →+* K) (s : Sp K) :
    (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) s ∈ U := by
  have h : hU.fromSpec (spMap ψ s) ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨_, rfl⟩
  exact h

end GlobalTheory.ShFam.BdArc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LineNorm

end GlobalTheory.LineNorm

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm

end GlobalTheory.LineNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPsiCoord
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
open Formalism.MainNotions.DIV.Cons (intO)

noncomputable section

namespace GlobalTheory.LocM.FJ.MultiData

theorem psiCoord_rescale {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (q : D.X → (FractionRing R)ˣ)
    {χ : D.X} {r s : R} (hr : PsiCoord D χ r)
    (hq : ((q χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s) :
    PsiCoord (GlobalTheory.TauTwist.rescale D q) χ (s * r) := by
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 hr
  refine (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D q) χ (s * r)).2
    ⟨q χ * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi χ) j h, ⟨j, h, hj, ?_⟩, ?_⟩
  · dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (q χ : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (q χ : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  · rw [Units.val_mul, hq, e, map_mul]

theorem exists_unit_psiCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : Out.DegPre R) (χ : D.X)
    (h : PsiUnitOn D χ Set.univ) : ∃ v : Rˣ, PsiCoord D χ v := by
  obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D χ
  have hh := GlobalTheory.PsiCoordLocal.generic_le D χ j hj
  obtain ⟨s, hs, e⟩ := h j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
  obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 s
  have hu : IsUnit r := (MulEquiv.isUnit_map
    (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤) GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 hs
  exact ⟨hu.unit, j, hj, hh, e⟩

end GlobalTheory.LocM.FJ.MultiData

namespace GlobalTheory.LocM.FJ.MultiData

end GlobalTheory.LocM.FJ.MultiData
end
end

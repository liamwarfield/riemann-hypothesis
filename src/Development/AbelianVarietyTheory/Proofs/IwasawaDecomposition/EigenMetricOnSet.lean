module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigMet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem gram_eq_of_isMap {σ : c.F →+* ℂ} (G : EigMet Z σ) {y : CxPts (genStr Z) σ} {R : Type} [CommRing R]
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {F : EigFrame Z φ x} {ψ : R →+* ℂ} {f f' : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) ψ f) (hf' : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) ψ f') (τ : E →+* ℂ) : G.gram y f' τ = G.gram y f τ := by
  have hc : f.co f' τ = 1 := by
    rw [← f.co_self τ]
    exact EigFrame.co_eq fun i => by rw [hf' τ i, ← hf τ i]; exact f.co_spec f τ i
  rw [G.change y f f' τ, hc, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem eq_comp_evHom {σ : c.F →+* ℂ} {V : (gen Z).affineOpens} {φ : c.F →+* Γ(gen Z, V.1)}
    (hV : LogKS.chart V ≫ genStr Z = spMap φ) {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1) :
    σ = (evHom h).comp φ := by
  have e : spMap σ = spMap ((evHom h).comp φ) := by
    rw [← y.2, ← spMap_evHom h, Category.assoc, hV, ← Spec.map_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem smoothOn_of_locally {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ))
    (hloc : ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S,
      y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ),
        IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧
        (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧
        ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
          (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (evHom hy) f → G.gram y f τ a b = g y) :
    G.SmoothOn (manifold Z σ) S := by
  classical
  intro V φ F τ a b hV
  have hx : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom h) ≫ LogKS.chart V ≫ genι Z := fun h => by
    rw [← Category.assoc, spMap_evHom h]
  have hex : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), (_root_.GlobalTheory.ShFam.EigFrame.IsMap F) (evHom h) f := fun h =>
    F.exists_isMap (evHom h) (eq_comp_evHom hV h) (hx h)
  let g : CxPts (genStr Z) σ → ℂ := fun y =>
    if h : y ∈ ptsIn (genStr Z) σ V.1 then G.gram y (hex h).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
      (_root_.GlobalTheory.ShFam.EigFrame.IsMap F) (evHom hy) f → G.gram y f τ a b = g y := fun y hy f hf => by
    simp only [g, dif_pos hy]
    rw [gram_eq_of_isMap G (hex hy).choose_spec hf τ]
  let ι := {y₀ // y₀ ∈ S ∧ y₀ ∈ ptsIn (genStr Z) σ V.1}
  choose T gl hT hmem hre him hagree using fun j : ι => hloc V φ F τ a b hV j.1 j.2.1 j.2.2
  have hc : ∀ y ∈ S ∩ ptsIn (genStr Z) σ V.1, ∃ j, y ∈ T j := fun y hy => ⟨⟨y, hy⟩, hmem _⟩
  have heq : ∀ j, ∀ y ∈ (S ∩ ptsIn (genStr Z) σ V.1) ∩ T j, g y = gl j y := fun j y hy =>
    (hg y hy.1.2 _ (hex hy.1.2).choose_spec).symm.trans (hagree j y hy.2 hy.1.2 _ (hex hy.1.2).choose_spec)
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun j => ((hre j).mono Set.inter_subset_right).congr fun y hy => ?_,
    AnRead.smoothOn_of_cover hT hc fun j => ((him j).mono Set.inter_subset_right).congr fun y hy => ?_,
    fun y _ hy f hf => hg y hy f hf⟩
  · exact congrArg Complex.re (heq j y hy)
  · exact congrArg Complex.im (heq j y hy)

end GlobalTheory.ShFam.EigMet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

end GlobalTheory.HTPres
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

section Pt

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pull_one_eq_zero (L : RigLB G) {T : Over S} :
    pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
  rw [cls_pull L.isLB] at a
  rw [Hom.one_def, Over.comp_left, pull_comp]
  change pull _ (pull (eSec G) _) = 0
  rw [a, map_zero]

theorem pull_inv (L : RigLB G) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (hs : s.IsGen) {T : Over S} (x : T ⟶ G) :
    pull x⁻¹.left (cls L.L L.isLB) = pull x.left (cls L.L L.isLB) := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).2 ⟨s, hs⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_smul, neg_smul] at e
  have e' : pull (ι[G]).left (cls L.L L.isLB) = cls L.L L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact e
  rw [Hom.inv_def, Over.comp_left, pull_comp, e']

theorem lam_self [IsCommMonObj G] (L : RigLB G) (hΘ : ∃ t : LB.Gen (Theta G L.L), t.IsGen)
    (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    {T : Over S} (x : T ⟶ G) :
    lam (cls L.L L.isLB) x x = 2 • pull x.left (cls L.L L.isLB) := by
  have h := lam_mul_left L.isLB hΘ x⁻¹ x x
  rw [inv_mul_cancel, lam_one_left] at h
  have h2 : lam (cls L.L L.isLB) x⁻¹ x = - pull x⁻¹.left (cls L.L L.isLB) - pull x.left (cls L.L L.isLB) := by
    simp only [lam, inv_mul_cancel, pull_one_eq_zero]; abel
  calc lam (cls L.L L.isLB) x x
      = (lam (cls L.L L.isLB) x⁻¹ x + lam (cls L.L L.isLB) x x) - lam (cls L.L L.isLB) x⁻¹ x := by abel
    _ = 2 • pull x.left (cls L.L L.isLB) := by rw [← h, h2, pull_inv L s hs]; abel

theorem lam_pull_fst {S' : Scheme.{0}} (f : S' ⟶ S) (c : Pic G.left) {T : Over S'}
    (x y : T ⟶ (Over.pullback f).obj G) :
    lam (CechPic.pull (pullback.fst G.hom f) c) x y =
      lam c (pushPt (isGrpPullback_pullback G f).1.w x) (pushPt (isGrpPullback_pullback G f).1.w y) := by
  have h := isGrpPullback_pullback G f
  have e1 : (x * y).left ≫ pullback.fst G.hom f = (pushPt h.1.w x * pushPt h.1.w y).left :=
    congrArg (fun z => z.left) (map_mul (pushHom h T) x y)
  have e0 : (1 : T ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  simp only [lam, ← pull_comp, e1, e0]
  rfl

end Pt

end GlobalTheory.SquareOfGeneric

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

theorem diag_lam_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (U : Unif (maximalIdeal R) D A G) (L : LB ((Over.pullback (jK R)).obj G).left) (hL : L.IsLB)
    (eL : LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (h : (abelian₂ ((Over.pullback (jK R)).obj G) L).IsLB) :
    CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left
        (cls _ h) = 2 • CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) := by
  have e₁ : cls _ h = lam (cls L hL) (fst _ _) (snd _ _) := cls_cube_two hL _ _ h
  have e₂ : cls L hL = CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) :=
    (cls_eq_iff hL (pull_isLB U.LG.isLB _)).2 eL
  rw [e₁, pull_lam, lift_fst, lift_snd, e₂, lam_pull_fst,
    lam_self U.LG ⟨U.cubG.t, U.cubG.isGen⟩ U.symG U.symG_gen]
  rfl

end GlobalTheory.SquareOfGeneric

open GlobalTheory.CechPic MonoidalCategory CartesianMonoidalCategory MonObj in
theorem GlobalTheory.squares_iso_of_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (L L' : LB ((Over.pullback (jK R)).obj G).left), L.IsLB → L'.IsLB → LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso L' (U'.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (abelian₂ ((Over.pullback (jK R)).obj G) L') → LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' L L' hL hL' eL eL' eΛ
  have hΛ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL' _ _)).2 eΛ
  have key := congrArg (CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G))
    (𝟙 ((Over.pullback (jK R)).obj G))).left) hΛ
  have k₁ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D A U L hL eL (LB.isLB_linComb hL _ _)
  have k₂ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D' A' U' L' hL' eL' (LB.isLB_linComb hL' _ _)
  replace key := k₁.symm.trans (key.trans k₂)
  refine GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base R hR.1 hR.2.1 G.left G.hom (eSec G) hG.smooth hG.quasiCompact
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ _ (LB.isLB_linComb U'.LG.isLB _ _) (LB.isLB_linComb U.LG.isLB _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _) (pull_isLB (LB.isLB_linComb U.LG.isLB _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb U'.LG.isLB _ _), cls_pull (LB.isLB_linComb U.LG.isLB _ _),
    cls_linComb U'.LG.isLB, cls_linComb U.LG.isLB]
  simp only [Fin.sum_univ_one, pull_id, map_zsmul]
  rw [two_zsmul, two_zsmul, ← two_nsmul, ← two_nsmul]
  exact key.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm.Chart

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

section Alg

theorem exists_minor_ne_zero {K : Type} [Field K] {m g k : ℕ} (a : Fin m → Fin g → K) (ha : LinearIndependent K a)
    (hk : k ≤ m) : ∃ s, minor a hk s ≠ 0 := by
  classical
  let M : Matrix (Fin k) (Fin g) K := Matrix.of fun l i => a (Fin.castLE hk l) i
  have hM : LinearIndependent K M.row := ha.comp _ (Fin.castLE_injective hk)
  obtain ⟨κ, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite κ := Finite.of_injective b hb
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : φ (minor a hk s) = minor (fun l i => φ (a l i)) hk s := by
  rw [minor, RingHom.map_det]; rfl

end Alg

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Z : Scheme.{0}}
    (v : Sp (DualNumber R) ⟶ Z) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ v = spMap (dualMap (ψ.comp φ)) ≫ v := by
  rw [← Category.assoc, spMap_comp']
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m g : ℕ}

theorem comb_iff {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) (a : Fin m → R)
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ l, a l • tanOf (hu l))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ l, a l • tanOf (hu l))).left := (isComb_iff (fun l => tanOf (hu l)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  exact ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans
    ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h0)

theorem comb_tan {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x u a w) : IsTanAtG t x w :=
  (comb_iff hu a w).1 h ▸ isTan_tv _

theorem sum_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) (c : Fin m → R) :
    ∑ l, c l • tanOf (hu l) = ∑ i, (∑ l, c l • a l) i • tanOf (he i) := by
  have h : ∀ l, tanOf (hu l) = ∑ i, a l i • tanOf (he i) := fun l => tan_ext ((comb_iff he _ _).1 (ha l))
  simp only [h, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem comb_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) {c : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (hw : IsCombAtG t x u c w) : IsCombAtG t x e (∑ l, c l • a l) w := by
  have hu := fun l => comb_tan he (ha l)
  rw [comb_iff he, ← sum_comb he hu ha]
  exact (comb_iff hu _ _).1 hw

end Tan

section Geo

theorem ringHom_ext {S : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    {φ φ' : Γ(S, V) →+* R} (h : spMap φ ≫ hV.fromSpec = spMap φ' ≫ hV.fromSpec) : φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Geo

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}

theorem coord_map {R S : Type} [CommRing R] [CommRing S] (α : A →+* R) (ψ : R →+* S) {a : Fin g → R}
    {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) a w) :
    IsCombAtG t (spMap (ψ.comp α) ≫ x₀) (fun i => spMap (dualMap (ψ.comp α)) ≫ e i) (fun i => ψ (a i))
      (spMap (dualMap ψ) ≫ w) := by
  have := GlobalTheory.LatDRFree.comb_map t ψ h
  simp only [dual_comp] at this
  rwa [← Category.assoc, spMap_comp'] at this

end Coord

end GlobalTheory.LineNorm.Chart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundary
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_eq_comp_linearEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : Sp ℂ ⟶ X) (g g' : ℕ) (ex : (Fin g → ℂ) → (Over.mk p ⟶ t.G)) (e' : (Fin g' → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p ex → IsHolTo Set.univ (fun w => (ex w).left) → IsExpAt t p e' → IsHolTo Set.univ (fun w => (e' w).left) → ∃ L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' z = ex (L z) := by
  intro E _ _ _ H X t p g g' ex e' hex hhol he' hhol'
  have one : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), (∀ z w, f (z + w) = f z * f w) → f 0 = 1 := by
    intro m f hf
    have h := hf 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have der : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p f →
      ∀ v : epsPt p ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (f 0).left →
        ∃! w, IsDerivAt0 (fun z => (f z).left) w v.left := by
    intro m f hf v hv
    refine hf.2.2 v.left ⟨Over.w v, ?_⟩
    rw [hv, one f hf.1]
  have H3 := (GlobalTheory.holomorphic_hom_determined X t.G).2.2.1 p
  obtain ⟨h, hh, -⟩ := H3 (Fin g' → ℂ) g e' ex he'.1 hex.1 hhol' hhol (der ex hex)
  obtain ⟨h', hh', -⟩ := H3 (Fin g → ℂ) g' ex e' hex.1 he'.1 hhol hhol' (der e' he')
  obtain ⟨k, -, hk⟩ := H3 (Fin g' → ℂ) g' e' e' he'.1 he'.1 hhol' hhol' (der e' he')
  obtain ⟨k', -, hk'⟩ := H3 (Fin g → ℂ) g ex ex hex.1 hex.1 hhol hhol (der ex hex)
  have c1 : h' ∘ₗ h = LinearMap.id :=
    (hk _ fun z => by rw [LinearMap.comp_apply, ← hh', ← hh]).trans (hk _ fun z => rfl).symm
  have c2 : h ∘ₗ h' = LinearMap.id :=
    (hk' _ fun z => by rw [LinearMap.comp_apply, ← hh, ← hh']).trans (hk' _ fun z => rfl).symm
  exact ⟨LinearEquiv.ofLinear h h' c2 c1, hh⟩

theorem exists_hermForm_transport : ∀ (g g' : ℕ) (L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Hm₀ : Matrix (Fin g') (Fin g') ℂ), Hm₀.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (hermForm Hm₀ z z).re) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ v w, hermForm Hm (L v) (L w) = hermForm Hm₀ v w := by
  intro g g' L Hm₀ hH hpos
  let A : Matrix (Fin g') (Fin g) ℂ := LinearMap.toMatrix' L.symm.toLinearMap
  have hA : ∀ v, A.mulVec v = L.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have key : ∀ v w, hermForm (Aᵀ * Hm₀ * A.map star) v w = hermForm Hm₀ (L.symm v) (L.symm w) := by
    intro v w
    simp only [hermForm, ← hA]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    congr 1
    ext j
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  refine ⟨Aᵀ * Hm₀ * A.map star, ?_, fun z hz => ?_, fun v w => ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    congr 1
    · ext a b
      simp [Matrix.conjTranspose_apply]
  · rw [key]
    exact hpos _ (by simpa using hz)
  · rw [key, L.symm_apply_apply, L.symm_apply_apply]

theorem exists_pushed_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X), IsPeriod (Fu.Di i) ty P → Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) → y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p → ∃ e' : (Fin g → ℂ) → (Over.mk p ⟶ Z.t.G), IsExpAt Z.t p e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ z, e' z = 1 ↔ z ∈ P.range) ∧ ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hP hu hp
  exact ⟨pushEx Z Fu y i P p hu hp, GlobalTheory.T.isExponential_modelFiber_of_uniformisationExp E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP⟩

theorem kernel_lattice_of_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g x ex hσ hpq hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  let e₀ : Fin (Fintype.card (Letter Dw)) ≃ Letter Dw := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c σ (e₀ j).1) hpq hσ hty
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ Fu y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨Hm, hH, hpos, ?_, ?_, ?_⟩
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(Fu.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner | exact GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner | (intros; apply GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RiemSmooth

def stdR (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g) :
    Hm p q = ((imForm Hm (stdR g ⟨p, 1⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) +
      ((imForm Hm (stdR g ⟨p, 0⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [imForm_apply, stdR, hermForm, Pi.basis_apply]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

def coordMat {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) :
    Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ :=
  Matrix.of fun a k => (stdR g).repr (u k) a

theorem std_eq_sum {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) (hM : (coordMat u).det ≠ 0)
    (a : Σ _ : Fin g, Fin 2) :
    stdR g a = ∑ k, ((coordMat u)⁻¹ k a) • u k := by
  apply (stdR g).repr.injective
  ext a'
  have h1 : coordMat u * (coordMat u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)
  have h2 : ∑ k, coordMat u a' k * (coordMat u)⁻¹ k a = if a = a' then 1 else 0 := by
    rw [← Matrix.mul_apply, h1, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.smul_apply, Finset.sum_apply', smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem imForm_std {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ))
    (hM : (coordMat u).det ≠ 0) (F : (Σ _ : Fin g, Fin 2) → (Σ _ : Fin g, Fin 2) → ℝ)
    (hF : ∀ k l, (hermForm Hm (u k) (u l)).im = F k l) (a c : Σ _ : Fin g, Fin 2) :
    imForm Hm (stdR g a) (stdR g c) =
      ∑ k, ∑ l, (coordMat u)⁻¹ k a * (coordMat u)⁻¹ l c * F k l := by
  rw [std_eq_sum u hM a, std_eq_sum u hM c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    imForm_apply, hF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem contDiffOn_det_real {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s)
    (hdet : ∀ x ∈ s, (M x).det ≠ 0) (k a : ι) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ k a) s := by
  have hadj : ContDiffOn ℝ ∞ (fun x => (M x).adjugate k a) s := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det_real fun i j => ?_
    by_cases hi : i = a
    · subst hi; simpa [Matrix.updateRow_apply] using contDiffOn_const
    · simpa [Matrix.updateRow_apply, hi] using h i j
  refine ((contDiffOn_det_real h).inv hdet |>.mul hadj).congr fun x hx => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [smul_eq_mul]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

theorem contDiffOn_of_im_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : Type} [AddCommGroup L] {g : ℕ}
    {B : Set X} (hB : IsOpen B) (P : X → (L →+ (Fin g → ℂ))) (F : L → L → ℝ)
    (hP : ∀ v, ContDiffOn ℝ ∞ (fun b => P b v) B)
    (hspan : ∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤)
    (Hm : X → Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ b ∈ B, ∀ x y, (hermForm (Hm b) (P b x) (P b y)).im = F x y) (p q : Fin g) :
    ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  refine contDiffOn_of_locally_contDiffOn fun b₀ hb₀ => ?_
  obtain ⟨t, ht, hts, hli⟩ := exists_linearIndependent ℝ (Set.range (P b₀))
  rw [hspan b₀ hb₀] at hts
  let bt : Module.Basis t ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hts])
  let e := bt.indexEquiv (stdR g)
  have hv : ∀ k, ∃ v, P b₀ v = bt (e.symm k) := fun k => by
    obtain ⟨v, hv⟩ := ht (e.symm k).2
    exact ⟨v, by rw [hv, Module.Basis.mk_apply]⟩
  choose v hv using hv
  let M : X → Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ := fun b => coordMat fun k => P b (v k)
  have hMs : ∀ a k, ContDiffOn ℝ ∞ (fun b => M b a k) B := fun a k => by
    let ℓ : (Fin g → ℂ) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap ((Finsupp.lapply a).comp (stdR g).repr.toLinearMap)
    exact ℓ.contDiff.comp_contDiffOn (hP (v k))
  have hdet0 : (M b₀).det ≠ 0 := by
    have : M b₀ = (stdR g).toMatrix (bt.reindex e) := by
      ext a k
      simp [M, coordMat, Module.Basis.toMatrix_apply, hv]
    rw [this, ← Module.Basis.det_apply]
    exact ((stdR g).isUnit_det _).ne_zero
  have hcont : ContinuousAt (fun b => (M b).det) b₀ :=
    (contDiffOn_det_real hMs).continuousOn.continuousAt (hB.mem_nhds hb₀)
  obtain ⟨U, hU, hUo, hb₀U⟩ := eventually_nhds_iff.1 (hcont.eventually_ne hdet0)
  refine ⟨U, hUo, hb₀U, ?_⟩
  have hdet : ∀ b ∈ B ∩ U, (M b).det ≠ 0 := fun b hb => hU b hb.2
  have hN := contDiffOn_inv_entry (fun a k => (hMs a k).mono Set.inter_subset_left) hdet
  have hsum : ∀ a c, ContDiffOn ℝ ∞ (fun b => ∑ k, ∑ l, (M b)⁻¹ k a * (M b)⁻¹ l c * F (v k) (v l)) (B ∩ U) :=
    fun a c => ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      ((hN k a).mul (hN l c)).mul contDiffOn_const
  refine ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 1⟩ ⟨q, 0⟩)).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 0⟩ ⟨q, 0⟩)).mul (contDiffOn_const (c := Complex.I)))).congr
    fun b hb => ?_
  have hF : ∀ k l, (hermForm (Hm b) (P b (v k)) (P b (v l))).im = F (v k) (v l) :=
    fun k l => hH b hb.1 _ _
  have h1 := entry_eq (Hm b) p q
  rw [imForm_std (Hm b) _ (hdet b hb) _ hF, imForm_std (Hm b) _ (hdet b hb) _ hF] at h1
  exact h1

theorem exists_riem_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → ∃ Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ, (∀ b ∈ B, IsRiem Fu i (P b) (Hm b)) ∧ ∀ p q, ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i d B P hB hper hhol
  classical
  let Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ :=
    fun b => if h : b ∈ B then Classical.choose (hper b h).2.2.2.2 else 0
  have hHm : ∀ b (h : b ∈ B), Hm b = Classical.choose (hper b h).2.2.2.2 := fun b h => dif_pos h
  have hR : ∀ b ∈ B, IsRiem Fu i (P b) (Hm b) := fun b h => by
    rw [hHm b h]
    exact Classical.choose_spec (hper b h).2.2.2.2
  refine ⟨Hm, hR, fun p q => ?_⟩
  refine contDiffOn_of_im_eq hB P (fun x y => ((Fu.Di i).EF x y : ℝ)) (fun v => ?_)
    (fun b h => (hper b h).2.2.2.1) Hm (fun b h x y => (hR b h).2.2 x y) p q
  exact contDiffOn_pi.2 fun j =>
    GlobalTheory.ChartGlue.contDiffOn_real hB ((differentiableOn_pi.1 (hhol v)) j)

end GlobalTheory.RiemSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem period_growth_mono_bound (x C : ℝ) (k K : ℕ) (hx : 0 ≤ x) (hk : k ≤ K) :
    C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ K := by
  have h1 : (1:ℝ) ≤ 1 + x := by linarith
  calc C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + x) ^ K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hk) (le_max_right _ _)

theorem period_matrix_polynomial_growth : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a d τ c hτ hpos hc

  have key : ∀ v : Fin d → ℝ, v ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
      ‖∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro v hv
    apply GlobalTheory.upper_half_growth n a
    · have hij : ∀ i j, DifferentiableOn ℂ (fun s => τ s i j) (logDom n a) :=
        fun i j => differentiableOn_pi.1 (differentiableOn_pi.1 hτ i) j
      fun_prop
    · intro s hs; exact hpos s hs v hv
  have e1 : ∀ (M : Fin d → Fin d → ℂ) (i : Fin d),
      ∑ i', ∑ j', (((Pi.single i (1:ℝ) : Fin d → ℝ) i' : ℝ) : ℂ) * M i' j' * (((Pi.single i (1:ℝ) : Fin d → ℝ) j' : ℝ) : ℂ) = M i i := by
    intro M i
    simp [Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
  have e2 : ∀ (M : Fin d → Fin d → ℂ) (i j : Fin d),
      ∑ i', ∑ j', ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) i' : ℝ) : ℂ) * M i' j' * ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) j' : ℝ) : ℂ) = M i i + M j j + M i j + M j i := by
    intro M i j
    simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
    ring
  have ne1 : ∀ i : Fin d, (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
    intro i h
    have := congrFun h i
    simp at this
  have ne2 : ∀ i j : Fin d, (Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ) ≠ 0 := by
    intro i j h
    have := congrFun h i
    simp [Pi.single_apply] at this
    split_ifs at this <;> linarith

  have entry : ∀ i j : Fin d, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s i j‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro i j
    obtain ⟨C1, k1, h1⟩ := key _ (ne2 i j)
    obtain ⟨C2, k2, h2⟩ := key _ (ne1 i)
    obtain ⟨C3, k3, h3⟩ := key _ (ne1 j)
    refine ⟨(max C1 0 + max C2 0 + max C3 0 + ‖c i j‖) / 2, max k1 (max k2 k3), by positivity, ?_⟩
    intro s hs hl him
    set K := max k1 (max k2 k3)
    have hx : 0 ≤ ‖s‖ := norm_nonneg _
    have b1 := (h1 s hs hl him).trans (period_growth_mono_bound ‖s‖ C1 k1 K hx (by omega))
    have b2 := (h2 s hs hl him).trans (period_growth_mono_bound ‖s‖ C2 k2 K hx (by omega))
    have b3 := (h3 s hs hl him).trans (period_growth_mono_bound ‖s‖ C3 k3 K hx (by omega))
    rw [e2] at b1
    rw [e1] at b2 b3
    have hP : 1 ≤ (1 + ‖s‖) ^ K := one_le_pow₀ (by linarith)
    have hcc : ‖c i j‖ ≤ ‖c i j‖ * (1 + ‖s‖) ^ K := le_mul_of_one_le_right (norm_nonneg _) hP
    have hid : (2:ℂ) * τ s i j = (τ s i i + τ s j j + τ s i j + τ s j i) - τ s i i - τ s j j + c i j := by
      rw [← hc s hs i j]; ring
    have h2n : ‖(2:ℂ) * τ s i j‖ ≤ ‖τ s i i + τ s j j + τ s i j + τ s j i‖ + ‖τ s i i‖ + ‖τ s j j‖ + ‖c i j‖ := by
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    rw [norm_mul] at h2n
    norm_num at h2n
    nlinarith
  choose Ce ke hCe hke using entry
  refine ⟨∑ i, ∑ j, Ce i j, Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2), ?_⟩
  intro s hs hl him
  set K := Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2)
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hP : 0 ≤ (1 + ‖s‖) ^ K := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, Ce i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCe i j
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hk : ke i j ≤ K := Finset.le_sup (f := fun p : Fin d × Fin d => ke p.1 p.2) (Finset.mem_univ (i, j))
  have b := (hke i j s hs hl him).trans (period_growth_mono_bound ‖s‖ (Ce i j) (ke i j) K hx hk)
  rw [max_eq_left (hCe i j)] at b
  have hle : Ce i j ≤ ∑ i, ∑ j, Ce i j :=
    (Finset.single_le_sum (f := fun j => Ce i j) (fun j _ => hCe i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Ce i j) (fun i _ => Finset.sum_nonneg fun j _ => hCe i j) (Finset.mem_univ i))
  exact b.trans (mul_le_mul_of_nonneg_right hle hP)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydiscStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodMatrix_polynomialGrowth_puncturedPolydisc : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.period_matrix_polynomial_growth | exact GlobalTheory.period_matrix_polynomial_growth | (intros; apply GlobalTheory.period_matrix_polynomial_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrank
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem finite_projective_int_of_ringOfIntegers :
    ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  intro E _ _ X _ _ _ _
  have hfin : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hflat : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  have hfree : Module.Free ℤ X := inferInstance
  refine ⟨hfin, inferInstance, ?_⟩
  rw [finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrankStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegers_projective_module_int_finrank : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  first | exact @GlobalTheory.finite_projective_int_of_ringOfIntegers | exact GlobalTheory.finite_projective_int_of_ringOfIntegers | (intros; apply GlobalTheory.finite_projective_int_of_ringOfIntegers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamLab

theorem adj_eig {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (θ : X →ₗ[ℂ] Y) (c : ℝ) (x₀ : X)
    (h : ∀ x', ⟪θ x₀, θ x'⟫_ℂ = (c : ℂ) * ⟪x₀, x'⟫_ℂ) : θ (LinearMap.adjoint θ (θ x₀)) = (c : ℂ) • θ x₀ := by
  have ha : LinearMap.adjoint θ (θ x₀) = (c : ℂ) • x₀ := by
    refine ext_inner_right ℂ fun x' => ?_
    rw [LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]
  rw [ha, map_smul]

theorem eigenvalue_eq_of_label : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne
  refine Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
  set K := (LinearMap.ker θ)ᗮ
  have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
    have := K.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at this
  have he : θ (K.starProjection x) = θ x := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
  have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
    rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
  have key := GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
    (K.starProjection_apply_mem x) hW
  have := adj_eig θ (R.lam3 i t p A3.A.v0) _ key
  rw [he] at this
  exact this

end GlobalTheory.Mem.R3.LamLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalarStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftScalar_eq_labelScalar : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  first | exact @GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label | exact GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label | (intros; apply GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label <;> assumption)
end
end

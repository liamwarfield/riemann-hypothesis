module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFrameChangeTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM

theorem exists_isGaloisCover_of_isQProjOver_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ _ X s Ga _ _ ρ hs h1 hm hρ hfree
  let τ := autOfRightAction ρ h1 hm
  have horbits : GlobalTheory.OrbitsInAffineOpens τ :=
    GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hs τ
  have hτg : ∀ g : Ga, (τ g).asIso.hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).asIso.hom ≫ s = s := fun g ↦ hρ g⁻¹
  have hfreeτ : GlobalTheory.IsFreeAction τ := by
    refine GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  obtain ⟨Y, π, hQ⟩ := (GlobalTheory.exists_isAffineQuotient_iff τ).mpr horbits
  let sY := hQ.desc s hτs
  have hπs : π ≫ sY = s := hQ.comp_desc s hτs
  obtain ⟨hsep, hlft, hqc⟩ := isSeparated_finiteType_of_isQProjOver hs
  refine ⟨Y, π, sY, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      hQ.isFinite_of_isFreeAction hfreeτ, hQ.etale_of_isFreeAction hfreeτ, hQ.surjective, ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ := (hQ.comp_eq_comp_iff y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ sY) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated sY
  · haveI : LocallyOfFiniteType (π ≫ sY) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType sY
  · haveI : QuasiCompact (π ≫ sY) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact sY

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  first | exact @GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian | exact GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian | (intros; apply GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem square_hom_ext (A : Over S) {Z : Scheme.{0}} {f g : Z ⟶ (A ⊗ A).left}
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem eSec_fst (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (fst A A).left = eSec A := by
  show (η[A ⊗ A] ≫ fst A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_snd (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (snd A A).left = eSec A := by
  show (η[A ⊗ A] ≫ snd A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_lift_one (A : Over S) [GrpObj A] : eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

theorem exists_bundle_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  intro X Y π Ga _ ρ A _ A₀ _ φ ν P hπ hA hA₀ gp hν hνρ ν₁ νm hP ⟨t₀, ht₀⟩ hsq
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hA₂ : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  choose ν₂ hν₂ iν₂ using hsq
  have ν₂m : ∀ a c, ν₂ (a * c) = ν₂ a ≫ ν₂ c := fun a c => square_hom_ext A
    (by rw [(hν₂ _).1, Category.assoc, (hν₂ c).1, reassoc_of% (hν₂ a).1, νm])
    (by rw [(hν₂ _).2, Category.assoc, (hν₂ c).2, reassoc_of% (hν₂ a).2, νm])
  have wA : (fst A A).left ≫ A.hom = (snd A A).left ≫ A.hom := (Over.w (fst A A)).trans (Over.w (snd A A)).symm
  let φ₂ : (G2 A).left ⟶ (G2 A₀).left := pullback.lift ((fst A A).left ≫ φ) ((snd A A).left ≫ φ)
    (by rw [Category.assoc, Category.assoc, gp.1.w, reassoc_of% wA])
  have hsqφ : IsSquare φ φ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsqφ
  have hu : ∀ a, ν₂ a ≫ (G2 A).hom = (G2 A).hom ≫ ρ a := fun a => by
    rw [← Over.w (fst A A), reassoc_of% (hν₂ a).1, (hνρ a).1.w, Category.assoc]
  have hinv : ∀ a, ν₂ a ≫ φ₂ = φ₂ := fun a => square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% (hν₂ a).1, hν.inv a])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% (hν₂ a).2, hν.inv a])
  have hφ₂ : IsGaloisCover Ga ν₂ φ₂ := ((galoisCover_descent X Y π Ga ρ hπ).2.2 (G2 A).left (G2 A₀).left φ₂ ν₂
    (G2 A).hom (G2 A₀).hom hu hpb.w.symm).2 hpb.flip hinv
  have he : eSec (G2 A) ≫ (G2 A).hom = 𝟙 X := Over.w η[G2 A]
  have hτ : ∀ a, eSec (G2 A) ≫ ν₂ a = ρ a ≫ eSec (G2 A) := fun a => square_hom_ext A
    (by rw [Category.assoc, (hν₂ a).1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_fst])
    (by rw [Category.assoc, (hν₂ a).2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_snd])
  have hc0 : cls _ (pull_isLB hP (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 := (cls_eq_zero_iff _).2 ⟨t₀, ht₀⟩
  have hPe : pull (eSec (G2 A)) (cls P hP) = 0 := by
    rw [← eSec_lift_one, pull_comp, ← cls_pull hP _ (pull_isLB hP _), hc0, map_zero]
  obtain ⟨r, hr⟩ := (cls_eq_zero_iff (pull_isLB hP (eSec (G2 A)))).1 hPe
  obtain ⟨u, hu₁, hu₂⟩ := GlobalTheory.TripleDescent.exists_linearisation hP (G2 A).hom (eSec (G2 A)) he (hG _ _ hA₂).2 ρ ν₂
    hπ.mul ν₂m hτ r hr iν₂
  obtain ⟨M, hM, iM⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ₂ Ga ν₂ P hφ₂ hP u hu₁ hu₂
  have hMP : pull φ₂ (cls M hM) = cls P hP := ((cls_eq_iff hP (pull_isLB hM φ₂)).2 iM).symm
  have he₀ : eSec (G2 A₀) ≫ (G2 A₀).hom = 𝟙 Y := Over.w η[G2 A₀]
  have hφe : eSec (G2 A) ≫ φ₂ = π ≫ eSec (G2 A₀) := square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_fst])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_snd])
  let P₀ : LB (G2 A₀).left := LB.LinComb M (K := Fin 2) ![𝟙 _, (G2 A₀).hom ≫ eSec (G2 A₀)] ![1, -1]
  have hP₀ : P₀.IsLB := LB.isLB_linComb hM _ _
  have hc : cls P₀ hP₀ = cls M hM - pull ((G2 A₀).hom ≫ eSec (G2 A₀)) (cls M hM) := by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp [pull_id, sub_eq_add_neg]
  refine ⟨P₀, φ₂, hP₀, hsqφ, ?_, ?_⟩
  · refine (cls_eq_iff hP (pull_isLB hP₀ φ₂)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, hMP, ← Category.assoc, hpb.w, Category.assoc, ← hφe,
      ← Category.assoc, pull_comp, hMP, pull_comp, hPe, map_zero, sub_zero]
  · refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, ← Category.assoc, he₀]
    erw [Category.id_comp, sub_self]

end GlobalTheory.SquareDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareBundle_descent_galoisCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  first | exact @GlobalTheory.SquareDescent.exists_bundle_descent | exact GlobalTheory.SquareDescent.exists_bundle_descent | (intros; apply GlobalTheory.SquareDescent.exists_bundle_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifTrait

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


set_option maxHeartbeats 1000000 in
theorem exists_intFr_frBor (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt) (hzs : z ≫ pullback.snd _ _ = spMap io) :
    letI := io.toAlgebra
    ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1 := by
  let _ := io.toAlgebra
  intro y₀ hy0
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T io O β Y yt z hz hzs _ m
  have hx : (z ≫ pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨x₀, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ := y₀
  change x₀ = z ≫ pullback.fst _ _ at hy0
  subst hy0
  obtain ⟨ub, u, hub, htan, heig, hbas, htri⟩ := lieFree Xo c T io _ t' _ m1 m2 hx u₀ htan₀ heig₀ hbas₀
  obtain ⟨θ, s, hθ, hmatch, hgen, a, ha⟩ :=
    GlobalTheory.DepthSum.thetaFrame_trait Xo c T io O β Y yt z hz hzs _ m t' m1 m2 s₀ hgen₀
  let y : FrPt Xo c T.Fr := ⟨z ≫ pullback.fst _ _, hx, u, htan, heig, hbas, s, hgen⟩
  choose cf hcf using htri
  let tt : Ix Dw → T.Frˣ := fun o => match o with
    | none => a
    | some p => (hcf p.1 p.2).1.unit
  have hFB : FrBor tt ⟨z ≫ pullback.fst _ _, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ y := by
    refine ⟨rfl, fun τ i => ⟨cf τ i, (hcf τ i).1.unit_spec.symm, (hcf τ i).2.1, (hcf τ i).2.2⟩, 𝟙 _,
      Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    change (Scheme.Hom.appLE (𝟙 (Gx (z ≫ pullback.fst _ _))) _ _ h).hom
      (scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i) = s.f i
    rw [ha i, Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp, show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨⟨y, GlobalTheory.Frames.framedPoint_field_fromTest GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c T.Fr y, _, t', m1, m2, ⟨ub, hub⟩, θ, hθ, hmatch⟩, tt, hFB⟩

end Frames

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

section Split

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem charZero_residue_of_map {K : Type} [Field K] [CharZero K] (V : Type) [CommRing V] [IsLocalRing V]
    (f : Sp V ⟶ Sp K) : CharZero (ResidueField V) :=
  charZero_of_injective_ringHom ((residue V).comp (Spec.preimage f).hom).injective

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, Sx, ⟨d⟩⟩ := GlobalTheory.UnifAfterExt.exists_finite_split _ h₀
  have : Algebra.IsSeparable (ResidueField W) k' := inferInstance
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, -, -, e, he⟩ := GlobalTheory.unramExt W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) Sx _ d)⟩

end Split

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

open IsLocalRing


end GlobalTheory.UnifTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelAmpleQProjNoeth

open GlobalTheory.RelAmpleQProj

theorem isQProjOver_of_relAmple_noeth : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0})
    (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L →
    IsQProjOver (A.hom ≫ s) := by
  rintro K _ _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProjNoeth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  first | exact @GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | exact GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | (intros; apply GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GaloisQuotientRing
open GlobalTheory.GaloisQuotient

theorem isQProjOver_of_isGaloisCover : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  intro K _ _ X Y π sY Ga _ ρ hG _ _ hX
  have := hG.finite
  let τ : Ga →* Aut X := MonoidHom.mk'
    (fun a => Aut.of (⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩ :
      X ≅ X))
    fun a c => Aut.ext (Iso.ext (by
      change ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹
      rw [mul_inv_rev, hG.mul]))
  have := OrbitsInAffineOpens.of_isQProjOver hX τ
  obtain ⟨Y', q, hq⟩ := (exists_isAffineQuotient_iff τ).mpr inferInstance
  have hD := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hG).1
  obtain ⟨u, hu, -⟩ := hD _ q fun a => by
    simpa only [inv_inv] using (show ρ a⁻¹⁻¹ ≫ _ = _ from hq.comp_eq a⁻¹)
  let v := hq.desc π fun a => hG.inv a⁻¹
  have hv : q ≫ v = π := hq.comp_desc _ _
  have : IsIso u := ⟨v, (hD Y π hG.inv).unique (by rw [reassoc_of% hu, hv]) (Category.comp_id _),
    hq.hom_ext (by rw [reassoc_of% hv, hu, Category.comp_id])⟩
  obtain ⟨L, hL⟩ := exists_isAmpleLB_of_isAffineQuotient hq hX
  exact (hL.pull_of_isAffineHom u).isQProjOver sY

end GlobalTheory.GaloisQuotientRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_target_galoisCover_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtScale


set_option maxHeartbeats 1000000 in
theorem exists_ext_chart_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ φ : ℝ, HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), y'.IsAlg ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ HasPhi y' (r * φ) ∧ (∀ (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e → OverLa la T'.V io' (r * e)) ∧ (∀ m : ℕ, m ≠ 0 → vV T'.V (m : T'.Fr) = (r : ℤ) * vV T.V (m : T.Fr)) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y hy φ hφ
  obtain ⟨S', io', z', r, hz', hr, hU, ψA, hv, hm⟩ := GlobalTheory.T.exists_extension_all_models_uniformized _ _ _ _ Xo c T io y hy
  have hphi : ∀ φ' : ℝ, HasPhi z' φ' → φ' = r * φ := fun φ' h' =>
    GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex _ _ _ _ Xo c T S' io io' y z' r hr ⟨ψA, hv, hm⟩ φ φ' hφ h'
  letI := io.toAlgebra
  let ψ : T.Fr →+* S'.Fr := letI := io'.toAlgebra; ψA.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (ψA.commutes a).symm
  have hv' : ∀ a : T.Fr, vV S'.V (ψ a) = (r : ℤ) * vV T.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hev : ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∀ f ∈ thGen Xo c nab a n, ψ (evI y f) = evI z' f := fun nab hn a n f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ Xo c nab hn T S' io io' y z' ψA hm a n f hf
  clear_value ψ
  clear hm hv ψA
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ H _ _ Xo c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  obtain ⟨φ', hφ'⟩ := exists_hasPhi z' C.I.G C.I.t' C.I.m1 C.I.m2 P
  have e1 := hphi φ' hφ'
  subst e1
  refine ⟨S', ψ.comp io, z', r, C, P, hz', hr, hCh, hP, hφ', fun la e ho => ho.bc ψ hr hv', fun m _ => ?_,
    fun nab hn a n e s f hf => ?_⟩
  · rw [← hv' (m : T.Fr), map_natCast]
  · rw [← hev nab hn a n f hf, RingHom.comp_apply, ← map_mul, nval_bc ψ hr hv']

end GlobalTheory.ExtScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScaleStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ φ : ℝ, HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), y'.IsAlg ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ HasPhi y' (r * φ) ∧ (∀ (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e → OverLa la T'.V io' (r * e)) ∧ (∀ m : ℕ, m ≠ 0 → vV T'.V (m : T'.Fr) = (r : ℤ) * vV T.V (m : T.Fr)) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  first | exact @GlobalTheory.ExtScale.exists_ext_chart_scale | exact GlobalTheory.ExtScale.exists_ext_chart_scale | (intros; apply GlobalTheory.ExtScale.exists_ext_chart_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] {k : Type} [CommRing k]

theorem functionFieldMap_comp_constFn (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] :
    (functionFieldMap f).comp (Cartier.constFn p) = Cartier.constFn (f ≫ p) := by
  ext a
  simp only [RingHom.comp_apply, Cartier.constFn]
  have h1 := algebraMap_germ (X := W) (U := ⊤) (x := f (genericPoint M)) trivial (algX p ⊤ a)
  have h2 := algebraMap_germ (X := M) (U := ⊤) (x := genericPoint M) trivial (algX (f ≫ p) ⊤ a)
  rw [← h1, ← h2, functionFieldMap_algebraMap]
  congr 1
  have e : f.app ⊤ (algX p ⊤ a) = algX (f ≫ p) ⊤ a := by
    simp only [algX, RingHom.comp_apply, Scheme.Hom.appLE,
      ← CommRingCat.comp_apply, Scheme.Hom.comp_app, Category.assoc]
    rw [f.naturality]
    rfl
  rw [← e]
  exact Scheme.Hom.germ_stalkMap_apply f ⊤ _ trivial _

def ratPull (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] (n : ℕ) :
    RatForms p n →ₛₗ[functionFieldMap f] RatForms (f ≫ p) n :=
  TopForm.formMap n (functionFieldMap f) (functionFieldMap_comp_constFn p f)

end GlobalTheory.EtaleKlt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
noncomputable section

namespace GlobalTheory.CovTop.LevelIndex

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.DIV

theorem index_comap_le {K G : Type*} [Group K] [Group G] [Finite G] (f : K →* G) (H : Subgroup G) :
    (H.comap f).index ≠ 0 ∧ (H.comap f).index ≤ Nat.card G := by
  rw [Subgroup.index_comap, Subgroup.relIndex]
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  exact (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _))

section Gen

variable {E : Type} [Field E] [NumberField E]

instance finite_kP (PP : Pl E) : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

theorem card_GL_le (R : Type) [CommRing R] [Finite R] (r : ℕ) : Nat.card (GL (Fin r) R) ≤ Nat.card R ^ (r ^ 2) := by
  have h : Nat.card (GL (Fin r) R) ≤ Nat.card (Matrix (Fin r) (Fin r) R) :=
    Nat.card_le_card_of_injective (fun x : GL (Fin r) R => (x : Matrix (Fin r) (Fin r) R)) Units.val_injective
  refine h.trans (le_of_eq ?_)
  change Nat.card (Fin r → Fin r → R) = _
  simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← pow_mul, sq]

theorem card_levelQuotientGroup_le_prod_absNorm_pow_sq (Pg : Finset (Pl E)) (r : ℕ) :
    Nat.card (G0 Pg r) ≤ (∏ PP ∈ Pg, Ideal.absNorm PP.asIdeal) ^ (r ^ 2) := by
  rw [Nat.card_pi, ← Finset.prod_pow, ← Finset.prod_coe_sort Pg]
  refine Finset.prod_le_prod' fun PP _ => ?_
  simpa only [Ideal.absNorm_eq_natCard] using card_GL_le (kP PP.1) r

theorem prod_absNorm_le (Pg : Finset (Pl E)) {N : ℕ} (hN : N ≠ 0) (h : ∀ PP ∈ Pg, ((N : ℕ) : 𝓞 E) ∈ PP.asIdeal) :
    ∏ PP ∈ Pg, Ideal.absNorm PP.asIdeal ≤ N ^ Module.finrank ℚ E := by
  have hd : ∏ PP ∈ Pg, PP.asIdeal ∣ Ideal.span {((N : ℕ) : 𝓞 E)} := by
    refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun PP hP => Ideal.dvd_span_singleton.2 (h PP hP)
    exact Ideal.isCoprime_iff_sup_eq.2 (P.isMaximal.coprime_of_ne Q.isMaximal fun e => hPQ (HeightOneSpectrum.ext e))
  have h2 := map_dvd Ideal.absNorm hd
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  exact Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hN) _) h2

variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]


open scoped TensorProduct in
theorem relIndex_lev_le (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n)
    (B : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (hB : B = parLev hc J β L) :
    (lev hc J β L).relIndex B ≠ 0 ∧ (lev hc J β L).relIndex B ≤ Nat.card (G0 L.Pg L.r) := by
  subst hB
  have e : (lev hc J β L).subgroupOf (parLev hc J β L) = L.P.H.comap (rHom hc J β L) := by
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [Subgroup.relIndex, e]
  exact index_comap_le _ _

open scoped TensorProduct in
theorem lev_full (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    lev hc J β { L with P := LevelP.full L.Pg L.r LL } = parLev hc J β L := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩

end Gen

end GlobalTheory.CovTop.LevelIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}

theorem uvec_cv (b : A.B) (w : Pm Dw.mult) (z : Let Dw.mult) (r : Fin (A.N + 1)) :
    uvec (A.cv b) w z r = ((A.A b).map (cC A b) * uC A b w z.1) r z.2 := by
  obtain ⟨τ, j⟩ := z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [uvec, cellVec, Atlas.cv, uC, cellMat, cC, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul, id,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
  ring

variable {Z : Scheme.{0}} {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem eq_spMap_ev (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    spMap ((ev z _ hz).comp (cellθ κ k).toRingHom) ≫ κ k.1 k.2 = z := by
  rw [← spMap_comp', Category.assoc, spMap_cellθ, spMap_ev]

end GlobalTheory.FlagMod.FieldFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOffOfUnramPts
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatTw

theorem intOff_of_unramPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), UnramPts Xo c B → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z la δ), IntOff B (δ + s.rho_vw) := by
  intro E _ _ _ H Dw l Xo c r U x B hB Z la δ s w hw
  obtain ⟨v, hv, hint⟩ := hB Z w hw
  have he := s.val_eq hv
  rcases hint s.sig with h | ⟨n, hn⟩
  · rw [he] at h; exact absurd h (EReal.coe_ne_top _)
  · rw [he] at hn
    exact ⟨n, EReal.coe_eq_coe_iff.1 hn⟩

end GlobalTheory.FlatTw
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.FlatTwisting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem wtOf_parWt_anti (w : Psi H → ℤ) (τ : E →+* ℂ) (i j : ℕ) (hij : i ≤ j) (hj : j < Dw.mult τ) :
    (wtOf Dw (parWt Dw w) 0).1 (τ, j) ≤ (wtOf Dw (parWt Dw w) 0).1 (τ, i) := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : j < Dw.p := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ j hp
    have e2 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ i (by omega)
    exact (e1.trans e2.symm).le
  · have hq : j < Dw.q := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ j hq
    have e2 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ i (by omega)
    simp only [AllWt.conjEmb_conjEmb] at e1 e2
    exact (e1.trans e2.symm).le

theorem wtOf_parWt_neg (w : Psi H → ℤ) : wtOf Dw (parWt Dw (-w)) 0 = -wtOf Dw (parWt Dw w) 0 := by
  have h := wtOf_add' (Dw := Dw) (parWt Dw (-w)) (parWt Dw w)
  have h0 : parWt Dw (-w) + parWt Dw w = 0 := by funext τ i; simp [parWt]
  rw [h0, wtOf_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mul_sig_mem_cuspOn (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c} {w : Psi H → ℤ} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ}
    (s : ConstSec U x Z (parWt Dw w) δ) :
    ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s.sig ∈ cuspOn U Z (G + wtOf Dw (parWt Dw w) 0) :=
  GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ s.sig hK hU hpq (even_wtOf _ _) (wtOf_parWt_anti w) s.sig_mem
    s.sig_mem_suppOn fun σ hσ => ⟨s.cInf σ, by
      have e : goodOf c σ = σ := if_pos hσ
      have h : ∀ z ∈ framesOn (U (goodOf c σ)) Z,
          homN (U (goodOf c σ)) x (wtOf Dw (parWt Dw w) 0) s.sig z ≤ s.cInf σ := fun z hz => (s.homN_eq hz).le
      rw [e] at h
      exact h⟩

theorem exists_twSec_of_const {B : Finset ℕ} (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) (Z : Comp Xo c) (w : Psi H → ℤ)
    (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ) (hδ : (Function.support δ).Finite) :
    ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
      t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo := by
  refine ⟨TwSec.ofConst s hδ (mul_sig_mem_cuspOn hK hU hpq s) fun G hG f hf => ?_, rfl, rfl, rfl, rfl,
    intOff_of_unramPts E H Dw l Xo c r U x B hB Z _ δ s⟩
  have h := mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl) (G + wtOf Dw (parWt Dw w) 0)
    (Even.add hG (even_wtOf _ _)) f hf
  rw [wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem finite_sum_flDefect (w : Psi H → ℤ) :
    (Function.support (∑ τ, (-w τ) • flDefect_vw Dw c τ)).Finite := by
  refine (Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun la hla => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
  exact hla (by simp [Finset.sum_apply, hn])

theorem finsum_sum_flDefect (w : Psi H → ℤ) :
    ∑ᶠ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
  have h1 : ∀ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      ∑ τ, (-(w τ : ℝ)) * (flDefect_vw Dw c τ la * lw c.F la) := fun la => by
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]; push_cast; ring
  rw [finsum_congr h1, finsum_sum_comm _ _ fun τ _ =>
    (fin_mul (finite_flDefect_vw τ) (lw c.F)).subset (Function.support_mul_subset_right _ _),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← mul_finsum, sum_flDefect_vw]; ring

theorem twSec_of_flat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ) (B : Finset ℕ) (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) :
    (∀ (Z : Comp Xo c) (w : Psi H → ℤ) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ),
      (Function.support δ).Finite → ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
        t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo) ∧
    (FlatExists U x → ∀ (Z : Comp Xo c) (w : Psi H → ℤ), HasPts U Z →
      ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), IntOff B t.lo ∧
        t.degLo = (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) ∧
        (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * lrd E * (∑ τ, |(w τ : ℝ)|) ≤ t.degLo) := by
  refine ⟨exists_twSec_of_const hK hU hpq hB, fun hF Z w hp => ?_⟩
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF.nonempty Z τ).some
  have hδ := finite_sum_flDefect (Dw := Dw) (c := c) w
  obtain ⟨s, hdeg⟩ : ∃ s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ),
      s.deg = ∑ τ, (w τ : ℝ) * c1 U x τ :=
    ⟨(FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _), (hF.deg_shift hp sF w).trans (by congr; exact Subsingleton.elim _ _)⟩
  obtain ⟨t, -, h2, h3, -, h5⟩ := exists_twSec_of_const hK hU hpq hB Z w _ s hδ
  have key := lineDeg_mul (r := 1) (fun _ => one_pos) s.cInf_pos hδ s.finite_rho
  rw [one_mul] at key
  have hd : t.degLo =
      (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) := by
    have h1 : lineDeg (1 : (c.F →+* ℂ) → ℝ) (∑ τ, (-w τ) • flDefect_vw Dw c τ) =
        -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
      rw [lineDeg, finsum_sum_flDefect]; simp
    rw [TwSec.degLo, h2, h3, key, h1, ← hdeg, ConstSec.deg]; ring
  refine ⟨t, h5, hd, ?_⟩
  have hA := GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le E H
  have hs : (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ) ≤ lrd E * ∑ τ, |(w τ : ℝ)| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
  have := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) Dw.q)
  rw [hd, mul_assoc, mul_assoc]
  linarith

end GlobalTheory.FlatTwisting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Vert

namespace GlobalTheory.FlagChain

section Sub

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

end Sub

section Bundles

variable {X Y Z : Scheme.{0}} {A B E E' H : X.Modules} {r : ℕ}

end Bundles

section Covers

variable {k : Type} [CommRing k] {D : ℕ} {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] {p : X ⟶ Sp k} {A E L H : X.Modules} {r : ℕ}

def IsCov (p : X ⟶ Sp k) (D : ℕ) (ρ : Y ⟶ X) : Prop :=
  IsArithVar (ρ ≫ p) D ∧ ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0

end Covers

end GlobalTheory.FlagChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevCalc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {d d' d'' : ℕ}

theorem sRel_comp {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨ψ, hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  refine ⟨ψ ≫ φ, hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sRel_cancel {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨χ, hχ, ⟨χ₂, hs', hw'⟩, hl'⟩ := m'
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨F₂, ⟨h₁, h₂⟩, ?_⟩, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a ^ d'').left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a ^ d'')
      have a₂ : (c'.lev a ^ d').left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a ^ d')
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem sRel_principal {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f)
    (hc : c.Principal) : c'.Principal := by
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

theorem sRel_mul {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f) (e : ℕ) :
    SRel c' c (d' * e) (d * e) f := by
  obtain ⟨φ, pb, sq, hl⟩ := m
  refine ⟨φ, pb, sq, fun a => ?_⟩
  rw [pow_mul, pow_mul]
  exact pow_section pb _ _ (hl a) e

theorem sRel_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m =>
    ⟨⟨sRel_comp m, sRel_cancel m⟩, sRel_principal m, sRel_mul m⟩

end GlobalTheory.SiegLevCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObjectPullbackLevelPower_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f := by
  first | exact @GlobalTheory.SiegLevCalc.sRel_calculus | exact GlobalTheory.SiegLevCalc.sRel_calculus | (intros; apply GlobalTheory.SiegLevCalc.sRel_calculus <;> assumption)
end
end

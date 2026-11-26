module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionRestrictionUnitTwist
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultiple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.resG_eq_of_thMul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N N' σ σ' c hσ hσ' j O h h'
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hO.ne
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N : Q.G.left.Opens) := fun y hy => (h (hm' hy)).1
  have hV' : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N' : Q.G.left.Opens) := fun y hy => (h' (hm' hy)).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (h (hm' hy)).2 0
  have e := (hσ K β g r jP jL h1 h2 h3 hL hV).symm.trans (hσ' K β g r jP jL h1 h2 h3 hL hV')
  refine (valR_res _ h hm _).trans (Eq.trans ?_ (valR_res _ h' hm _).symm)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultipleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_eq_of_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  first | exact @GlobalTheory.ZH.ZHPre.resG_eq_of_thMul | exact GlobalTheory.ZH.ZHPre.resG_eq_of_thMul | (intros; apply GlobalTheory.ZH.ZHPre.resG_eq_of_thMul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem extPt_comp_eq_integral_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT F ψ hM a W h hE hV x hx yW hyW
  obtain ⟨-, -, hK, hK0⟩ := hT
  obtain ⟨hF, hψ1, hψ2, hψ3⟩ := hM
  obtain ⟨hh, hE⟩ := hE
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hsep : IsSeparated Q.G.hom := Q.semi.separated
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hφ : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hFw : F ≫ Q.G.hom = u.G.hom ≫ yV := hF.1.w
  let sec : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hs1 : sec ≫ pullback.fst _ _ = Q.u₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have hs2 : sec ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hs3 : sec ≫ Q.φ ≫ Q.G.hom = U₀.ι := by
    rw [hφ, ← Category.assoc, hs2, Category.id_comp]
  let N : M.Z.Opens := W ⊓ U₀
  let iW : N.toScheme ⟶ W.toScheme := M.Z.homOfLE inf_le_left
  let iU : N.toScheme ⟶ U₀.toScheme := M.Z.homOfLE inf_le_right
  have hiW : iW ≫ W.ι = N.ι := M.Z.homOfLE_ι _
  have hiU : iU ≫ U₀.ι = N.ι := M.Z.homOfLE_ι _
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← hyW]
      exact (yW (jK u.V w)).2
    · rw [← hK]
      exact (yK w).2
  let k : Sp (FractionRing u.V) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (jK u.V ≫ yV) hr
  have hk : k ≫ N.ι = jK u.V ≫ yV := IsOpenImmersion.lift_fac _ _ _
  have hkW : k ≫ iW = jK u.V ≫ yW := by
    rw [← cancel_mono W.ι, Category.assoc, hiW, hk, Category.assoc, hyW]
  have hkU : k ≫ iU = yK := by
    rw [← cancel_mono U₀.ι, Category.assoc, hiU, hk, hK]
  have hne : (N : Set M.Z).Nonempty :=
    ⟨_, (k (IsLocalRing.closedPoint (FractionRing u.V))).2⟩
  have hg : Set.range M.pt ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let g : Sp Ω ⟶ N.toScheme := IsOpenImmersion.lift N.ι M.pt hg
  have hgN : g ≫ N.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (g ≫ N.ι) := by rw [hgN]; infer_instance
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g N.ι
  have key : iW ≫ h = iU ≫ sec ≫ Q.φ := by
    refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ g ?_
    · simp only [Category.assoc]
      rw [hh, hs3, hiW, hiU]
    · have h1 : (g ≫ iU) ≫ U₀.ι = M.pt := by rw [Category.assoc, hiU, hgN]
      have := hE (g ≫ iW) (g ≫ iU ≫ sec) (by rw [Category.assoc, hiW, hgN])
        (by simp only [Category.assoc]; rw [hs3, hiU, hgN])
        (by
          simp only [Category.assoc]
          rw [hs1, ← Q.u₀_gen _ h1]
          simp only [Category.assoc])
      simpa only [Category.assoc] using this
  have hxψ : yK ≫ sec = x ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hs1, Category.assoc, hψ1, ← Category.assoc, hK0]
      exact hx4.symm
    · rw [Category.assoc, hs2, Category.assoc, hψ2, ← Category.assoc, hx3, Category.comp_id, Category.id_comp]
  have : IsDominant (jK u.V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap u.V (FractionRing u.V))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective u.V (FractionRing u.V))]
      exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ (jK u.V) ?_
  · simp only [Category.assoc]
    rw [hh, hyW, hFw, ← Category.assoc, hx1, Category.id_comp]
  · rw [← Category.assoc, ← hkW, Category.assoc, key, ← Category.assoc, hkU, ← Category.assoc, hxψ,
      Category.assoc, hψ3, ← Category.assoc, hx2, Category.assoc]

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionSectionEqIntegralPointAtTestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSection_eq_integral_point_at_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  first | exact @GlobalTheory.ZH.extPt_comp_eq_integral_point | exact GlobalTheory.ZH.extPt_comp_eq_integral_point | (intros; apply GlobalTheory.ZH.extPt_comp_eq_integral_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ZH.MulExtend
open GlobalTheory.TorsFrameInt

variable {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {K K' : Type} [Fintype K] [Fintype K']

theorem exists_move_charts (hL : L.IsLB) (hM : M.IsLB) {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ))
    (hw : w.IsGen) (φX : K → (X ⟶ X)) (φY : K → (Y ⟶ Y)) (φH : K → (H ⟶ H)) (ε : K → ℤ)
    (h₁ : ∀ k, φY k ≫ ψ = ψ ≫ φX k) (h₂ : ∀ k, φY k ≫ f = f ≫ φH k)
    (α : LB.Gen (LB.LinComb L φX ε)) (hα : α.IsGen) :
    ∃ a : LB.Gen (LB.LinComb M (fun k => f ≫ φH k) ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → M.ι),
        (∀ k, (r ≫ φY k ≫ ψ) z ∈ L.U (p k)) → (∀ k, (r ≫ φY k ≫ f) z ∈ M.U (q k)) →
        gm (r ≫ ψ) z (LB.wchart L φX p) (α.s p) = (∏ k, gw w (r ≫ φY k) z (p k) (fun _ => q k) ^ ε k) *
          gm r z (LB.wchart M (fun k => f ≫ φH k) q) (a.s q) := by
  obtain ⟨b, hb, H⟩ := H1.exists_gen_move hL (pull_isLB hM f) w ((isGen_iff w).1 hw) φX φY ε ψ h₁ α hα
  have le : ∀ j : K → M.ι, LB.wchart M (fun k => f ≫ φH k) j ≤ LB.wchart (M.pull f) φY (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      have : (f ≫ φH k) y ∈ M.U (j k) := Set.mem_iInter.1 hy k
      rw [← h₂ k] at this; exact this)
  refine ⟨⟨fun j => res (le j) (b.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z p q hp hq => ?_⟩
  · refine (gm_res _ y _ hj _).trans ((gen_trans hb (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ y _ hj' _).symm))
    refine (gm_pull_g M f (𝟙 Y ≫ φY k) y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc, h₂]
  · have m : r z ∈ LB.wchart M (fun k => f ≫ φH k) q := Set.mem_iInter.2 fun k => by
      have := hq k
      rw [h₂ k] at this; exact this
    exact (H Z r z p (fun k _ => q k) hp (fun k => Set.mem_iInter.1 (le _ m) k)).trans
      (congrArg₂ (· * ·) rfl (gm_res _ z _ m _).symm)

theorem corr_of_field [IsReduced Y] [Nonempty K] (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (ψ : Y ⟶ X) (h : ∀ k, φ k = ψ) (h' : ∀ k, φ' k = ψ)
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (F : Type) [Field F] (r : Sp F ⟶ Y) (z : Sp F) J, Good L z J → val t r z J = val t' r z J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (GenericExtend.eq_of_valR_eq fun x hx ↦ ⟨Y.residueField x, inferInstance,
    Y.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
  have ho : ∀ o, (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) o = x :=
    fun o ↦ Scheme.fromSpecResidueField_apply x o
  generalize (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) = r at ho
  have z : Sp (Y.residueField x) := IsLocalRing.closedPoint _
  have hz : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := (ho z).symm ▸ hx
  obtain ⟨k₀⟩ := ‹Nonempty K›
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ ψ) (fun _ => j k₀) (fun _ _ _ => rfl)
    (fun _ => by rw [← h k₀]; exact Set.mem_iInter.1 hz.1 k₀)
  have q := H _ r z J hJ
  rw [val_of t r z J j (fun k => by rw [h]; exact (e PUnit.unit).trans (c₁ _ _ ((h _).trans (h _).symm))),
    val_of t' r z J j' (fun k => by rw [h']; exact (e PUnit.unit).trans (c₃ _ _ ((h _).trans (h' _).symm)))] at q
  refine (toStk z).injective ?_
  exact (toStk_valF r _ z hz _).trans ((congrArg Units.val ((gm_res r z _ hz _).trans
    (q.trans (gm_res r z _ hz _).symm))).trans (toStk_valF r _ z hz _).symm)

theorem core {S U HU B : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU)
    (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j)
    (h₁ : eU ≫ jH = j ≫ e) (hL : L.IsLB) (hM : M.IsLB) (eX : B ⟶ X) (u : U ⟶ B) (ψ : HU ⟶ X)
    (h₃ : eU ≫ ψ = u ≫ eX) (nH : H ⟶ H) (nU : HU ⟶ HU) (nX : X ⟶ X)
    (c₁ : nU ≫ ψ = ψ ≫ nX) (c₂ : nU ≫ jH = jH ≫ nH) (c₃ : eU ≫ nU = eU) (c₄ : e ≫ nH = e)
    (w : LB.Iso (M.pull jH) (L.pull ψ)) (hw : w.IsGen)
    (rig : LB.Gen (L.pull eX)) (rigM : LB.Gen (M.pull e)) (hrigM : rigM.IsGen) (N : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![N, -1])) (hα : α.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (t : Z ⟶ B) (z : Z) J, Good L z J →
      val α (t ≫ eX) z J = val rig t z J ^ N * (val rig t z J)⁻¹)
    (hr : ∀ (F : Type) [Field F] (x : Sp F ⟶ U) (z : Sp F) J J', Good L z J → Good M z J' →
      val rig (x ≫ u) z J = wv w (x ≫ eU) z J J' * val rigM (x ≫ j) z J') :
    ∃ κ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 H, nH] ![N, -1]), κ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z) (a a' : L.ι) (b b' : M.ι),
        (r ≫ ψ) z ∈ L.U a → ((r ≫ nU) ≫ ψ) z ∈ L.U a' → (r ≫ jH) z ∈ M.U b → ((r ≫ nU) ≫ jH) z ∈ M.U b' →
        gm (r ≫ ψ) z (LB.wchart L ![𝟙 X, nX] ![a, a']) (α.s ![a, a']) * gw w (r ≫ nU) z a' (fun _ => b') =
          gw w r z a (fun _ => b) ^ N * gm (r ≫ jH) z (LB.wchart M ![𝟙 H, nH] ![b, b']) (κ.s ![b, b']) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have d₁ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ ψ = ψ ≫ ![𝟙 X, nX] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₁]
  have d₂ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ jH = jH ≫ ![𝟙 H, nH] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₂]
  obtain ⟨t, ht, htv⟩ := exists_move_charts hL hM w hw ![𝟙 X, nX] ![𝟙 _, nU] ![𝟙 H, nH] ![N, -1] d₁ d₂ α hα
  have ee : ∀ k : Fin 2, e ≫ ![𝟙 H, nH] k = e := fun k => by fin_cases k; exacts [Category.comp_id _, c₄]
  have eeU : ∀ k : Fin 2, eU ≫ ![𝟙 _, nU] k = eU := fun k => by fin_cases k; exacts [Category.comp_id _, c₃]
  let σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => e) (fun _ => N - 1)) := ⟨fun i => rigM.s i ^ (N - 1)⟩
  have hσ : σ.IsGen := isGen_of_gm _ fun y i i' hi hi' => by
    refine (map_zpow _ _ _).trans ((congrArg (· ^ (N - 1)) (gen_trans hrigM (𝟙 _) y hi hi')).trans
      ((mul_zpow _ _ _).trans (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
    simp only [trF, Fintype.prod_unique, zpow_one]
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hM (φ' := fun k : Fin 2 => e ≫ ![𝟙 H, nH] k) (ε' := ![N, -1])
    (fun G _ h => by
      simp only [ee, Fintype.prod_unique, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← zpow_add]; rfl) σ hσ
  obtain ⟨κ, ⟨hκ, hc⟩, -⟩ := GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hs hg he hP h₁ M hM
    (Fin 2) ![𝟙 H, nH] ![N, -1] t ρ ht hρ (corr_of_field hM (j ≫ e)
      (fun k => by rw [← Category.assoc, h₁, Category.assoc, ee]) (fun k => by rw [ee])
      fun F _ x z J' hJ' => by
        choose J hJ using fun χ : Sp F ⟶ X => exists_chart hL (χ z)
        rw [val_pull hJ', val_pull hJ', hρv _ _ z J' hJ']
        have q := htv _ (x ≫ eU) z (fun k => J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
          (fun k => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k))
          (fun k => by rw [d₁, ← Category.assoc]; exact hJ _) (fun k => by rw [d₂]; exact hJ' _)
        have q₁ : ∀ k : Fin 2, gw w ((x ≫ eU) ≫ ![𝟙 _, nU] k) z (J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
            (fun _ => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k)) = wv w (x ≫ eU) z J J' := fun k => by
          rw [Category.assoc (x ≫ eU) ψ, ← d₁, ← d₂, ← Category.assoc _ _ ψ, ← Category.assoc _ _ jH,
            Category.assoc x eU, eeU]
          rfl
        simp only [q₁] at q
        have q₂ : val α ((x ≫ eU) ≫ ψ) z J = _ * val t (x ≫ eU) z J' := q
        rw [Category.assoc, h₃, ← Category.assoc, hn _ _ z J hJ, hr F x z J J' hJ hJ', Fin.prod_univ_two] at q₂
        refine Eq.trans ?_ (map_zpow _ _ _).symm
        change _ = val rigM (x ≫ j) z J' ^ (N - 1)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at q₂
        apply Additive.ofMul.injective
        replace q₂ := congrArg Additive.ofMul q₂
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at q₂ ⊢
        linear_combination (norm := module) -q₂)
  refine ⟨κ, hκ, fun Z r z a a' b b' ha ha' hb hb' => ?_⟩
  have hq : ∀ k : Fin 2, (r ≫ ![𝟙 _, nU] k ≫ jH) z ∈ M.U (![b, b'] k) := fun k => by
    fin_cases k; exacts [hb, hb']
  have q := htv _ r z ![a, a'] ![b, b'] (fun k => by fin_cases k; exacts [ha, ha']) hq
  rw [← hc, gm_pullGen M _ _ κ jH r z _ (Set.mem_iInter.2 fun k => by
    have := hq k
    rw [d₂] at this; exact this), Fin.prod_univ_two] at q
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at q
  rw [q, zpow_neg_one, mul_right_comm, inv_mul_cancel_right]

theorem exists_gen_mulRel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hS n α hα hn
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have : Nonempty U₀.toScheme := hS.ne.to_subtype
  have gq := isGrpPullback_pullback ρ.P.A Q.u₀
  let eU : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := η[(Over.pullback Q.u₀).obj ρ.P.A].left
  let nU : pullback ρ.P.A.hom Q.u₀ ⟶ pullback ρ.P.A.hom Q.u₀ := (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left
  have h₁ : eU ≫ Q.φ = U₀.ι ≫ eSec Q.G := one_comm Q.cart
  have h₃ : eU ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := one_comm gq
  have c₁ : nU ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (mulA ρ.P.A n).left := mulA_comm gq n
  have c₅ : nU ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)
  have rg : ∀ {F : Type} [Field F] {Y : Scheme.{0}} (g : Sp F ⟶ Y) (V : Y.Opens) (z : Sp F), g z ∈ V →
      Set.range g ⊆ V := fun g V z hz => by
    rintro _ ⟨y, rfl⟩
    exact (top_le_iff_mem g V z).2 hz (x := y) trivial
  obtain ⟨κ, hκ, H⟩ := core hS.normal U₀.ι Q.G.hom (eSec Q.G) Q.φ _ eU Q.semi.smooth
    (grpObj_geometricallyIntegral_of_smooth _ Q.G) (Over.w η[Q.G]) Q.cart.1 h₁ ρ.P.isLB Q.L.isLB (eSec ρ.P.A) Q.u₀
    (pullback.fst _ _) h₃ (mulA Q.G n).left nU (mulA ρ.P.A n).left c₁ (mulA_comm Q.cart n) (one_mulA n) (one_mulA n)
    Q.w Q.w_gen ρ.rig Q.L.rig Q.L.rigGen ((n : ℤ) ^ 2) α hα (fun Z t z J hJ => by
      have q := val_corr hJ hn t
      rw [val_pull hJ, val_mul hJ, val_inv] at q
      exact q.trans (congrArg (· * _) (map_zpow _ _ _))) (fun F _ x z J J' hJ hJ' => by
      have e₁ : (x ≫ eU) ≫ Q.φ = (x ≫ U₀.ι) ≫ eSec Q.G := by rw [Category.assoc, h₁, Category.assoc]
      have e₃ : (x ≫ eU) ≫ pullback.fst _ _ = (x ≫ Q.u₀) ≫ eSec ρ.P.A := by rw [Category.assoc, h₃, Category.assoc]
      have q := congrArg (toStk z) (Q.w_rig F (x ≫ eU) (x ≫ U₀.ι) (x ≫ Q.u₀) _ _ e₁ e₃ (rg _ _ z (hJ _))
        (rg _ _ z (hJ' _)))
      rw [map_mul, toStk_valF _ _ z (mem_pull.2 (by have := hJ ((x ≫ eU) ≫ pullback.fst _ _); rwa [e₃] at this ⊢)),
        toStk_valF (x ≫ eU) _ z (And.intro (mem_pull.2 (hJ ((x ≫ eU) ≫ pullback.fst _ _)))
          (mem_pull.2 (hJ' ((x ≫ eU) ≫ Q.φ)))),
        toStk_valF _ _ z (mem_pull.2 (by have := hJ' ((x ≫ eU) ≫ Q.φ); rwa [e₁] at this ⊢))] at q
      rw [val_of _ _ z J (fun _ => J ((x ≫ eU) ≫ pullback.fst _ _)) (fun _ => by rw [e₃]),
        val_of _ _ z J' (fun _ => J' ((x ≫ eU) ≫ Q.φ)) (fun _ => by rw [e₁])]
      exact Units.ext q)
  refine ⟨κ, hκ, fun K _ g g' jP jP' jL jL' k₁ k₂ m₁ m₂ m₃ m₄ => ?_⟩
  obtain rfl : g' = g ≫ nU := pullback.hom_ext (by rw [k₁, Category.assoc, c₁]) (by rw [k₂, Category.assoc, c₅])
  have z : Sp K := IsLocalRing.closedPoint _
  have a₁ := m₁ ⟨z, rfl⟩
  have a₂ := m₂ ⟨z, rfl⟩
  have a₃ := m₃ ⟨z, rfl⟩
  have a₄ := m₄ ⟨z, rfl⟩
  have q := congrArg Units.val (H _ g z jP jP' jL jL' a₁ a₃ a₂ a₄)
  have pw : ∀ {G : Type} [Group G] (x : G), x ^ ((n : ℤ) ^ 2) = x ^ (n ^ 2) := fun x => by
    rw [← Nat.cast_pow, zpow_natCast]
  rw [pw] at q
  refine (toStk z).injective ?_
  rw [map_mul, map_mul, map_pow, toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₁
      · rw [Category.assoc, c₁] at a₃; exact a₃),
    toStk_valF (g ≫ nU) _ z (And.intro (mem_pull.2 a₃) (mem_pull.2 a₄)),
    toStk_valF g _ z (And.intro (mem_pull.2 a₁) (mem_pull.2 a₂)),
    toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₂
      · rw [Category.assoc, show nU ≫ Q.φ = _ from mulA_comm Q.cart n] at a₄; exact a₄)]
  exact q

end GlobalTheory.ZH.MulExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_normalised_mulByN_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  first | exact @GlobalTheory.ZH.MulExtend.exists_gen_mulRel | exact GlobalTheory.ZH.MulExtend.exists_gen_mulRel | (intros; apply GlobalTheory.ZH.MulExtend.exists_gen_mulRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_point_of_inter {V K O C : Type} [CommRing V] [Field K] [CommRing O] [IsLocalRing O] [Field C]
    (i : V →+* K) (j : V →+* O) (k : K →+* C) (l : O →+* C) (hi : Function.Injective i) (hl : Function.Injective l)
    (hc : ∀ v, l (j v) = k (i v)) (hint : ∀ (a : K) (c : O), k a = l c → ∃ v, i v = a)
    {X : Scheme.{0}} (x : Sp K ⟶ X) (b : Sp O ⟶ X) (h : spMap k ≫ x = spMap l ≫ b) :
    ∃ y : Sp V ⟶ X, spMap i ≫ y = x ∧ spMap j ≫ y = b := by
  obtain ⟨U, hU, hb, -⟩ := exists_isAffineOpen_le b (le_preimage_top b)
  have hlb : ⊤ ≤ (spMap l ≫ b) ⁻¹ᵁ U := le_preimage_comp _ b hb (le_preimage_top _)
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ (spMap k ≫ x) ⁻¹ᵁ U := h ▸ hlb
    intro w _
    rw [Subsingleton.elim w (spMap k (IsLocalRing.closedPoint C))]
    exact h1 (x := IsLocalRing.closedPoint C) trivial
  have hv : ∀ f, k ((valMap x U hx).hom f) = l ((valMap b U hb).hom f) := fun f => by
    rw [← valR_eq, ← valR_eq, ← valR_spMap_comp k x U hx, ← valR_spMap_comp l b U hb, h]
  choose g hg using fun f => hint _ _ (hv f)
  let ψ : Γ(X, U) →+* V :=
    { toFun := g
      map_one' := hi (by simp only [hg, map_one])
      map_mul' := fun a c => hi (by simp only [hg, map_mul])
      map_zero' := hi (by simp only [hg, map_zero])
      map_add' := fun a c => hi (by simp only [hg, map_add (f := _)]) }
  have e1 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom i = valMap x U hx := by
    ext f
    exact hg f
  have e2 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom j = valMap b U hb := by
    ext f
    exact hl ((hc _).trans ((congrArg k (hg f)).trans (hv f)))
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, e1, specMap_valMap_fromSpec]
  · rw [← Category.assoc, ← Spec.map_comp, e2, specMap_valMap_fromSpec]

theorem pushHom_inj_of_cartesian {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := fun a b e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))

theorem torsion_integral_descends : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u jV hj b hb
  haveI := u.U.gen_hom
  let k : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  have hsq : gPt p ≫ spMap jV = spMap k ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => spMap φ) (RingHom.ext hj)
  have hbw : b.left ≫ u.G.hom = spMap jV := Over.w b
  let T : Over (Sp (FractionRing u.V)) := Over.mk (spMap k)
  let wl : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (gPt p ≫ b.left) (spMap k) (by rw [Category.assoc, hbw, hsq])
  have w1 : wl ≫ pullback.fst _ _ = gPt p ≫ b.left := pullback.lift_fst _ _ _
  have w2 : wl ≫ pullback.snd _ _ = spMap k := pullback.lift_snd _ _ _
  let w : T ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk wl w2
  let W : Over.mk (T.hom ≫ jK u.V) ⟶ Over.mk (spMap jV) := Over.homMk (gPt p) hsq
  have hp := isGrpPullback_pullback u.G (jK u.V)
  have e0 : pushHom hp T w = preHom W b := Over.OverMorphism.ext w1
  have hw : w ^ (S.r * S.N) = 1 := pushHom_inj_of_cartesian hp T (by
    rw [map_pow, e0, ← map_pow, hb, map_one, map_one])
  have hw' : (w ≫ u.U.gen.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hw, MonObj.one_comp]
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) (T.hom ≫ spMap u.yK) (pushHom u.cart T (w ≫ u.U.gen.hom))
    (by rw [← map_pow, hw', map_one])
  have ha' : (spMap k ≫ spMap u.yK) ≫ (ρ.pt a).left = (wl ≫ u.U.gen.hom.left) ≫ u.φ :=
    congrArg (fun z => z.left) ha
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hg : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd _ _ := Over.w u.U.gen.hom
  have hg' : u.U.gen.inv.left ≫ pullback.snd _ _ = u.A.A.hom := Over.w u.U.gen.inv
  have hih : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.inv_hom_id
  have hhi : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.hom_inv_id
  obtain ⟨x', x1, x2⟩ : ∃ x' : Sp (FractionRing u.V) ⟶ u.A.A.left,
      x' ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left ∧ x' ≫ u.A.A.hom = 𝟙 _ :=
    ⟨u.cart.1.lift (spMap u.yK ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa, Category.id_comp]; exact Category.comp_id _), u.cart.1.lift_fst _ _ _,
      u.cart.1.lift_snd _ _ _⟩
  have hx' : spMap k ≫ x' = wl ≫ u.U.gen.hom.left := by
    refine u.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, x1, ← Category.assoc]
      exact ha'
    · rw [Category.assoc, x2, Category.comp_id, Category.assoc]
      exact ((congrArg (wl ≫ ·) hg).trans w2).symm
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) := x' ≫ u.U.gen.inv.left
  have hx : spMap k ≫ x = wl := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.U.gen.inv.left) hx').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (wl ≫ ·) hhi).trans (Category.comp_id _))
  have hxs : x ≫ pullback.snd _ _ = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) hg').trans x2)
  obtain ⟨hV, h1, h2⟩ := exists_point_of_inter (algebraMap u.V (FractionRing u.V)) jV k (OO p).subtype
    (IsFractionRing.injective _ _) Subtype.val_injective hj
    (fun a c e => (u.norm_le a).1 ((mem_OO_iff _).1 (by
      have e' : algebraMap _ (PadicAlgCl p) a = c := e
      rw [e']; exact c.2)))
    (x ≫ pullback.fst _ _) b.left (by rw [← Category.assoc, hx, w1])
  refine ⟨a, hV, x, ⟨?_, h1.symm, hxs, ?_⟩, h2⟩
  · rw [← Spec.map_preimage (hV ≫ u.G.hom), ← Spec.map_id]
    congr 1
    have h3 : Spec.preimage (hV ≫ u.G.hom) ≫ CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) =
        CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc]
      refine (congrArg (· ≫ u.G.hom) h1).trans ?_
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, Category.id_comp]
    ext v
    exact IsFractionRing.injective u.V (FractionRing u.V) (congrArg (fun φ => φ.hom v) h3)
  · refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (x' ≫ ·) ?_) x1)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) hih).trans (Category.id_comp _))

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_torsion_point_descends_to_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  first | exact @GlobalTheory.ZH.torsion_integral_descends | exact GlobalTheory.ZH.torsion_integral_descends | (intros; apply GlobalTheory.ZH.torsion_integral_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrder
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ZJ.exists_torsion_lift_of_residue :
    ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  intro p _ B G _ hG y n hn t ht
  have := hG.comm
  have := hG.smooth
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G n
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  have w : t.left ≫ (mulN G n).left =
      (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ht, e]
  obtain ⟨c, hc₁, hc₂⟩ := ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y
    (hP.lift _ _ w) (hP.lift_snd _ _ w)
  let b : Over.mk y ⟶ G := Over.homMk (c ≫ (torsion.ι G n).left) (by
    rw [Category.assoc, Over.w]; exact hc₁)
  refine ⟨b, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (c ≫ (torsion.ι G n).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hc₁]
  · change _ ≫ c ≫ (torsion.ι G n).left = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrderStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder : ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  first | exact @GlobalTheory.ZJ.exists_torsion_lift_of_residue | exact GlobalTheory.ZJ.exists_torsion_lift_of_residue | (intros; apply GlobalTheory.ZJ.exists_torsion_lift_of_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem exists_iso_of_existsUnique_ext {B B' : Scheme.{0}} (j : B' ⟶ B) (G G' : Over B) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hext : ∀ (G G' : Over B) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f)
    (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj G') (he : IsMonHom e.hom) :
    ∃ E : G ≅ G', IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hext G G' hG hG' e.hom he
  obtain ⟨b, ⟨hb, hb'⟩, -⟩ := hext G' G hG' hG e.inv inferInstance
  refine ⟨⟨a, b, ?_, ?_⟩, ha, ha'⟩
  · exact (hext G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (hext G' G' hG' hG' (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ZHPre.exists_testMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  intro hext o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT
  obtain ⟨-, -, h₁, h₂⟩ := hT
  have := u.U.gen_hom
  have gp₁ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  have gp₂ := ((isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)).congr h₂ rfl
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso gp₁ gp₂
  have gp₃ := ((((isGrpPullback_of_iso e₁).comp
    (isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK)).congr (Category.id_comp _) rfl).comp Q.cart).congr h₁ rfl
  have gp₄ := (isGrpPullback_pullback ((Over.pullback yV).obj Q.G) (jK u.V)).comp (isGrpPullback_pullback Q.G yV)
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso gp₃ gp₄
  obtain ⟨E, mE, hE⟩ := exists_iso_of_existsUnique_ext (jK u.V) u.G ((Over.pullback yV).obj Q.G) u.semi
    (IsSemiAbelian.pullback _ Q.G Q.semi) (fun G G' _ _ => hext u.V (FractionRing u.V) G G') e₂ m₂
  refine ⟨E.hom.left ≫ pullback.fst Q.G.hom yV,
    e₁.hom.left ≫ pullback.fst ((Over.pullback Q.u₀).obj ρ.P.A).hom yK,
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback Q.G yV)).congr (Category.id_comp _) rfl, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans he₁
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (e₁.hom.left ≫ ·) (pullback.condition (f := ((Over.pullback Q.u₀).obj ρ.P.A).hom) (g := yK))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ yK) (Over.w e₁.hom))
  · refine he₂.symm.trans ?_
    have a : ((Over.pullback (jK u.V)).map E.hom).left ≫ pullback.fst ((Over.pullback yV).obj Q.G).hom (jK u.V) =
        pullback.fst u.G.hom (jK u.V) ≫ E.hom.left := pullback.lift_fst _ _ _
    rw [← hE]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst Q.G.hom yV) a).trans (Category.assoc _ _ _))

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelEqPullbackGroupSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testMap_of_testFac : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_testMap | exact GlobalTheory.ZH.ZHPre.exists_testMap | (intros; apply GlobalTheory.ZH.ZHPre.exists_testMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultiple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GlueTheta

theorem res_res {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem glue_secOn {X : Scheme.{0}} (L : LB X) {I : Type} (V : I → X.Opens) (W : X.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : ∀ x ∈ W, ∃ i, x ∈ V i) (σ : ∀ i j, Γ(X, V i ⊓ L.U j)) (hσ : ∀ i, σ i ∈ secOn L (V i))
    (hc : ∀ i i' j (O : X.Opens) (h : O ≤ V i ⊓ L.U j) (h' : O ≤ V i' ⊓ L.U j),
      resG X h (σ i j) = resG X h' (σ i' j)) :
    ∃ s ∈ secOn L W, ∀ i j, resG X (inf_le_inf_right _ (hle i)) (s j) = σ i j := by
  have key : ∀ j, ∃ s : Γ(X, W ⊓ L.U j), ∀ i, resG X (inf_le_inf_right _ (hle i)) s = σ i j := by
    intro j
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V i ⊓ L.U j) (W ⊓ L.U j)
      (fun i => homOfLE (inf_le_inf_right _ (hle i)))
      (fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi, hx.2⟩)
      (fun i => σ i j) (fun i i' => hc i i' j _ inf_le_left inf_le_right)
    exact ⟨s, hs⟩
  choose s hs using key
  refine ⟨s, fun j k => ?_, fun i j => hs j i⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V i ⊓ L.U j ⊓ L.U k) (W ⊓ L.U j ⊓ L.U k)
    (fun i => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hle i))))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcov x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hi, hx.1.2⟩, hx.2⟩) _ _ fun i => ?_
  have h := hσ i j k
  rw [← hs j i, ← hs k i, res_res, res_res] at h
  change resG X _ _ = resG X _ _
  rw [map_mul, res_res, res_res, res_res]
  exact h

theorem exists_glue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q c huniq W hloc
  choose N σ hz hNW hsec hth hne using fun z : W => hloc z.1 z.2
  obtain ⟨s, hs, hres⟩ := glue_secOn Q.LOne (fun z : W => Q.G.hom ⁻¹ᵁ N z) (Q.G.hom ⁻¹ᵁ W)
    (fun z x hx => hNW z hx) (fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩) σ hsec
    (fun z z' => huniq _ _ _ _ (hth z) (hth z'))
  have hval : ∀ (K : Type) [Field K] (g : Sp K ⟶ Q.G.left) (z : W) (j : Q.LOne.ι),
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) → valF g _ (σ z j) = valF g _ (s j) := by
    intro K _ g z j h
    rw [← hres z j]
    exact GlobalTheory.Points.valR_res g _ h _
  refine ⟨s, hs, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    let z : W := ⟨Q.G.hom ((g ≫ Q.φ) (IsLocalRing.closedPoint K)), h5 ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z) := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U fun _ => jL) := fun t ht =>
      ⟨hN ht, Set.mem_iInter.2 fun _ => h4 ⟨t, rfl⟩⟩
    rw [← hval K _ z _ hU]
    exact hth z K β g r jP jL h1 h2 h3 h4 (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
  · intro K _ _ x hx
    let z : W := ⟨x (IsLocalRing.closedPoint K), hx ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ x ⁻¹ᵁ N z := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    obtain ⟨g, j, hg, hv⟩ := hne z K x (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
    refine ⟨g, j, hg, ?_⟩
    have hU : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) := by
      by_contra hU
      exact hv (dif_neg hU)
    rwa [← hval K g z j hU]

end GlobalTheory.ZH.GlueTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultipleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_sections_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  first | exact @GlobalTheory.ZH.GlueTheta.exists_glue | exact GlobalTheory.ZH.GlueTheta.exists_glue | (intros; apply GlobalTheory.ZH.GlueTheta.exists_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibres
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
open GlobalTheory.Points
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_thMul (h1 : Laws) (h2 : Laws2) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hN : (N : Set M.Z).Nonempty) : ∃ c, Q.ThMul c N σ := by
  have hpt : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt ov.ne) ⟨w, rfl⟩
  have heta : IsOpenImmersion.lift U₀.ι M.pt hpt ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_genericFibre_section_of_model_section o Ω S ρ M U₀ Q N σ _ hσ hN heta
  obtain ⟨c, hc⟩ := GlobalTheory.T.sec_generic_eq_mul_theta_alt h1 h2 o Ω S ρ s
  refine ⟨c, ?_⟩
  intro K _ β g r jP jL hg hr hP hL _
  have hg' : g ≫ pullback.snd _ _ = spMap β ≫ IsOpenImmersion.lift U₀.ι M.pt hpt := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, heta]
    exact hg
  have hcomm : spMap β ≫ spMap S.R.val.toRingHom = (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ≫ ρ.P.A.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg', Category.assoc, Q.u₀_gen _ heta]
  let q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left :=
    pullback.lift (spMap β) (g ≫ pullback.fst _ _) hcomm
  have hq1 : q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β :=
    pullback.lift_fst _ _ _
  have hq2 : q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left =
      g ≫ pullback.fst _ _ :=
    pullback.lift_snd _ _ _
  have e1 := hs K β q g jP jL hq1 hq2.symm hg' hP hL
  have e2 := hc K β q r jP hq1 (hr.trans hq2.symm) (by rw [hq2]; exact hP)
  simp only [Finset.univ_unique, Finset.sum_singleton, zpow_one]
  rw [← e2, e1]

theorem exists_good_label (h0 : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)) (hs : GlobalTheory.Published.SemistableReductionSt) (hU : ThmUSt) (h1 : Laws) (h2 : Laws2)
    (hT : UTorsSt) (big : S.Big) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hne : Q.FibNe N σ) (z : M.Z) (hz : IsClosed ({z} : Set M.Z))
    (hzN : z ∈ N) : ∃ a ∈ S.HH M z, ∀ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme),
      Q.ExtPt a W h → W.ι w = z → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι),
        Set.range x = {w} ∧ valF (x ≫ h) _ (σ j) ≠ 0 := by
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  obtain ⟨⟨p, hp, y, hy⟩, -⟩ := (classical_points_and_local_regularity o Ω M U₀ ov.normal).1 U₀ le_rfl ov.ne z hz
  obtain ⟨y₀, Fs, hAt, hint, hfac⟩ := GlobalTheory.T.exists_classical_point_factor_large_model o Ω S ρ M U₀ Q ov z p y hy
  obtain ⟨u, l, τ, hmatch, hFs⟩ := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hs hU h1 h2 hT o Ω S ρ).2 p y₀ Fs hint
  obtain ⟨jV, yV, yK, hTF⟩ := hfac u hFs
  obtain ⟨F, ψ, hTM⟩ := GlobalTheory.T.exists_testMap_of_testFac h0 o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF
  have hLB := GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM
  have hyN : y (cPt p) ∈ N := by rw [hy.1]; exact hzN
  obtain ⟨t, ht, j, hj⟩ := GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero h1 h2 o Ω S ρ M U₀ Q big p y y₀ u jV yV yK hTF F ψ hTM hLB N σ hσ hne hyN
  have hn : IsUnit ((S.r * S.N : ℕ) : Γ(Sp u.V, ⊤)) := by
    have hv : IsUnit ((S.r * S.N : ℕ) : u.V) := by
      have he : ((S.r * S.N : ℕ) : o) * ↑(S.unit.unit⁻¹) = 1 := S.unit.mul_val_inv
      have hnorm : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (u.yK (algebraMap o S.R ↑(S.unit.unit⁻¹)))‖ ≤ 1 := by
        have hf := RingHom.congr_fun u.fac (algebraMap o S.R ↑(S.unit.unit⁻¹))
        rw [RingHom.comp_apply] at hf
        rw [hf]
        exact hint _
      obtain ⟨v, hvE⟩ := (u.norm_le _).1 hnorm
      have hmul : ((S.r * S.N : ℕ) : u.V) * v = 1 := by
        apply IsFractionRing.injective u.V (FractionRing u.V)
        rw [map_mul, map_one, hvE, map_natCast, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R),
          ← map_mul, ← map_mul, he, map_one, map_one]
      exact ⟨⟨_, v, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    simpa using hv.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom
  obtain ⟨b, hb, hbt⟩ := GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder p (Sp u.V) u.G u.semi (spMap jV) (S.r * S.N) hn t ht
  obtain ⟨a, hV, x, ⟨hV1, hx1, hx2, hx3⟩, hbV⟩ := GlobalTheory.T.integral_torsion_point_descends_to_model o Ω S ρ p y₀ u jV hTF.1 b hb
  have hker : a ∈ τ.yy.ker := by
    obtain ⟨e, -, he⟩ := hmatch
    have hl : l.yy a = 0 := (AddMonoidHom.mem_ker).1 ((l.ker_iff a).2 ⟨hV, x, hV1, hx1, hx2, hx3⟩)
    have h0' : τ.yy a = QuotientAddGroup.mk 0 := (he a 0).2 (by rw [hl, map_zero]; rfl)
    rw [AddMonoidHom.mem_ker, h0']
    rfl
  have hHH := (ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ ov z p y y₀ τ hy hAt).2
  refine ⟨a, by rw [hHH]; exact hker, ?_⟩
  intro W h w hExt hwz
  haveI := isLocalHom_of_test u jV hTF.1
  have hzW : z ∈ W := by
    have hr : z ∈ Set.range W.ι := ⟨w, hwz⟩
    rwa [Scheme.Opens.range_ι] at hr
  have hVz : yV (IsLocalRing.closedPoint u.V) = z := by
    rw [← hy.1, ← hTF.2.1, Scheme.Hom.comp_apply]
    congr 1
    exact (IsLocalRing.comap_closedPoint jV).symm
  have hsp : ∀ v, yV v ⤳ z := fun v => hVz ▸ (IsLocalRing.specializes_closedPoint v).map yV.continuous
  have hrange : Set.range yV ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff yV W).1 (top_le_preimage_of_specializes hsp hzW)
  have hyW : IsOpenImmersion.lift W.ι yV hrange ≫ W.ι = yV := IsOpenImmersion.lift_fac _ _ _
  have hcomp := GlobalTheory.T.torsionSection_eq_integral_point_at_test o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM a W h hExt hV x
    ⟨hV1, hx1, hx2, hx3⟩ _ hyW
  refine ⟨IsLocalRing.ResidueField (OO p), inferInstance,
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange, j, ?_, ?_⟩
  · rw [Set.range_unique]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [hwz, ← Scheme.Hom.comp_apply]
    simp only [Category.assoc, hyW, hTF.2.1]
    rw [Scheme.Hom.comp_apply, ← hy.1]
    congr 1
    rw [show (default : Sp (IsLocalRing.ResidueField (OO p))) = IsLocalRing.closedPoint _ from
      Subsingleton.elim _ _]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  · have hx : (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange) ≫ h =
        t.left ≫ F := by
      rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc (spMap jV), hbV, ← Category.assoc, hbt]
    rw [hx]
    exact hj

theorem exists_theta_div : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  intro h0 hs hU h1 h2 hT o Ω _ _ _ _ S ρ M U₀ Q big ov hSec hLoc W x₀ hx₀
  refine GlobalTheory.T.exists_glue_sections_same_theta_multiple o Ω S ρ M U₀ Q (S.th x₀)⁻¹
    (fun N N' σ σ' hσ hσ' j O h h' => GlobalTheory.T.restrict_eq_of_same_theta_multiple o Ω S ρ M U₀ Q ov N N' σ σ' _ hσ hσ' j O h h') W ?_
  intro z hzW
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : JacobsonSpace M.Z := (classical_points_and_local_regularity o Ω M U₀ ov.normal).2
  obtain ⟨N₀, σ₀, hzN₀, hσ₀, hne₀⟩ := GlobalTheory.T.exists_localThetaSection_fibreNonzero o Ω S ρ M U₀ Q hLoc z
  obtain ⟨c₀, hc₀⟩ := Q.exists_thMul h1 h2 ov N₀ σ₀ hσ₀ ⟨z, hzN₀⟩
  have hext : ∀ (z' : M.Z), ∀ b ∈ S.HH M z', ∃ (Wb : M.Z.Opens) (hb : Wb.toScheme ⟶ Q.G.left) (wb : Wb.toScheme),
      Q.ExtPt b Wb hb ∧ Wb.ι wb = z' ∧ Q.FrameUnit b Wb hb wb := by
    intro z' b hb
    obtain ⟨Wb, hb', hz'Wb, hb1, hb2⟩ := hSec z' b hb
    obtain ⟨wb, hwb⟩ : z' ∈ Set.range Wb.ι := by rw [Scheme.Opens.range_ι]; exact hz'Wb
    have hE : Q.ExtPt b Wb hb' := ⟨hb1, hb2⟩
    exact ⟨Wb, hb', wb, hE, hwb, GlobalTheory.T.torsionFrame_isUnit_along_section o Ω S ρ M U₀ Q ov
      (fun α hα hn => GlobalTheory.T.exists_generator_normalised_mulByN_iso o Ω S ρ M U₀ Q ov (S.r * S.N) α hα hn) b Wb hb' wb hE⟩
  have hcl : ∀ z' : M.Z, IsClosed ({z'} : Set M.Z) → z' ∈ N₀ → z' ∈ W →
      c₀ * S.th x₀ ≠ 0 ∧ c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    intro z' hz' hz'N hz'W
    obtain ⟨a, ha, hgood⟩ := Q.exists_good_label h0 hs hU h1 h2 hT big ov N₀ σ₀ hσ₀ hne₀ z' hz' hz'N
    obtain ⟨Wa, ha', wa, hEa, hwa, hFa⟩ := hext z' a ha
    have hwaN : Wa.ι wa ∈ N₀ := by rw [hwa]; exact hz'N
    have hxa := GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ a Wa ha' wa hEa hFa hwaN
    obtain ⟨K, _, x, j, hx, hv⟩ := hgood Wa ha' wa hEa hwa
    obtain ⟨hne, hinv⟩ := hxa.2 K x j hx hv
    have hx₀' : x₀ ∈ S.supI M z' := hx₀ z' hz'W
    obtain ⟨Wb, hb', wb, hEb, hwb, hFb⟩ := hext z' x₀ (AddSubgroup.subset_closure hx₀')
    have hwbN : Wb.ι wb ∈ N₀ := by rw [hwb]; exact hz'N
    have hxb := (GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ x₀ Wb hb' wb hEb hFb hwbN).1
    rw [hwa] at hinv
    rw [hwb] at hxb
    have hdiv : M.Div S.th x₀ z' := hx₀'
    obtain ⟨hth, hdivs⟩ := hdiv
    have hc : c₀ ≠ 0 := left_ne_zero_of_mul hne
    have hta : S.th a ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨mul_ne_zero hc hth, hxb, ?_⟩
    have heq : (c₀ * S.th x₀)⁻¹ = S.th a / S.th x₀ * (c₀ * S.th a)⁻¹ := by
      field_simp
    rw [heq]
    exact Subalgebra.mul_mem _ (hdivs a) hinv
  have hopen : IsOpen {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'} :=
    (M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)
  have hall : ∀ z' : M.Z, z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₂, hz₂N, hz₂W, hbad⟩ := hcon
    have hZ : (((N₀ : Set M.Z) ∩ (W : Set M.Z)) ∩
        {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}ᶜ).Nonempty :=
      ⟨z₂, ⟨hz₂N, hz₂W⟩, fun h => hbad h.1 h.2⟩
    obtain ⟨z', ⟨⟨hz'N, hz'W⟩, hz'bad⟩, hz'c⟩ := nonempty_inter_closedPoints hZ
      ⟨_, _, N₀.isOpen.inter W.isOpen, hopen.isClosed_compl, rfl⟩
    obtain ⟨-, h1', h2'⟩ := hcl z' hz'c hz'N hz'W
    exact hz'bad ⟨h1', h2'⟩
  obtain ⟨z₁, ⟨hz₁N, hz₁W⟩, hz₁c⟩ := nonempty_inter_closedPoints
    (⟨z, hzN₀, hzW⟩ : ((N₀ : Set M.Z) ∩ (W : Set M.Z)).Nonempty) (N₀.isOpen.inter W.isOpen).isLocallyClosed
  have hf0 : c₀ * S.th x₀ ≠ 0 := (hcl z₁ hz₁c hz₁N hz₁W).1
  obtain ⟨σ', hσ', hth', hne'⟩ := GlobalTheory.T.theta_section_restriction_unit_twist o Ω S ρ M U₀ Q N₀ (N₀ ⊓ W) σ₀ c₀ (c₀ * S.th x₀)⁻¹ inf_le_left
    (fun z' hz' => by
      obtain ⟨hz'N, hz'W⟩ := hz'
      obtain ⟨h1', h2'⟩ := hall z' hz'N hz'W
      exact ⟨inv_ne_zero hf0, h2', by rw [inv_inv]; exact h1'⟩) hσ₀ hc₀ hne₀
  have hc₀0 : c₀ ≠ 0 := left_ne_zero_of_mul hf0
  have hth0 : S.th x₀ ≠ 0 := right_ne_zero_of_mul hf0
  have hfc : (c₀ * S.th x₀)⁻¹ * c₀ = (S.th x₀)⁻¹ := by
    field_simp
  rw [hfc] at hth'
  exact ⟨N₀ ⊓ W, σ', ⟨hzN₀, hzW⟩, inf_le_right, hσ', hth', hne'⟩

end GlobalTheory.ZH.ZHPre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibresStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDividedByConstant_nonvanishing_fibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_theta_div | exact GlobalTheory.ZH.ZHPre.exists_theta_div | (intros; apply GlobalTheory.ZH.ZHPre.exists_theta_div <;> assumption)
end

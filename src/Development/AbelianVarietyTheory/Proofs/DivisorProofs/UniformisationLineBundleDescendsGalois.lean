module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameOffClosedFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantLocalFramesUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameNearClosedFibrePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameBundleNearClosedPointFiniteEtaleExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RigCubCarry

theorem pmaps_of_pullGen {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (H : PMaps w φ' (fun k => h ≫ φ k) ε a (LB.pullGen L φ ε t h) (𝟙 Y')) : PMaps w φ' φ ε a t h := by
  intro Z r z p q hp hq
  have e := H Z r z p q hp hq
  rw [Category.comp_id] at e
  have hm' : ∀ k, (h ≫ φ k) (r z) ∈ L.U (p k) := fun k => by
    rw [← hc k]; exact hp k
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 hm'
  have hm2 : h (r z) ∈ LB.wchart L φ p := Set.mem_iInter.2 hm'
  refine Eq.trans ?_ e
  exact ((gm_res r z _ hm _).trans (gm_pull r h z _ hm2 _)).symm


open RigidIsoCube in
theorem surjective_appTop_tripleProduct_uniformisedGroup (R : Type) [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom := by
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)

theorem cubeMap_tripleProduct_unit_eq {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G') :
    (lift (1 : 𝟙_ (Over S) ⟶ G') (lift 1 1)).left ≫ m.F3 =
      (lift (1 : Over.mk (m.e ≫ (𝟙_ (Over S)).hom) ⟶ G') (lift 1 1)).left := by
  have ht : (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom))).left = m.e := by
    have w := Over.w (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom)))
    simpa using w
  apply hom_ext_triple
  intro i
  rw [Category.assoc, cubeMap_comp_proj_three m i, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  have h1 : ∀ {T : Over S}, lift (1 : T ⟶ G') (lift 1 1) ≫ x3 G' i = 1 := by
    intro T; fin_cases i <;> simp [x3]
  rw [h1, h1, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ht]
  have e₁ : (toUnit (𝟙_ (Over S))).left = 𝟙 _ := by simp
  rw [e₁, Category.id_comp]
  exact m.e_comm

end GlobalTheory.Mum.RigCubCarry

namespace GlobalTheory.Mum


set_option maxHeartbeats 2000000 in
open RigidIsoCube RigCubCarry in
theorem rigidified_galois_lin_carries_rig_and_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  intro R _ _ _ hB R' _ _ _ ρ hF hGal D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact σ h bc hbc hP
  obtain ⟨hw, he, hrig, -⟩ := Classical.choose_spec hP.lg
  refine ⟨(maps_iff _ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) _
    (rigPull_le _ _ he U'.LG.L) (fun _ => rfl)).1 hrig, fun hc => ?_⟩
  have sj := surjective_appTop_tripleProduct_uniformisedGroup R' G' U'.toUnifPre
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 G' := lift 1 (lift 1 1)
  have he3 : e.left ≫ (snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have pg := (isGen_iff _).1 hw
  have hψ : ∀ k : thK.{0}, thφ G' (x3 G') k ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) =
      (cubeMapOf hc).F3 ≫ thφ G' (x3 G') k := fun k => (cubeMapOf hc).psum_comm k.down
  have eF := cubeMap_tripleProduct_unit_eq (cubeMapOf hc)
  refine pmaps_of_pullGen hψ (pmaps_of_section pg U'.LG.isLB U'.LG.isLB U'.cubG.t U'.cubG.isGen
    (LB.pullGen _ _ _ U'.cubG.t (cubeMapOf hc).F3) (DVR.pullGen_isGen _ _ _ _ U'.cubG.isGen _) hψ _ e.left he3 sj
    fun y J J' hJ hJ' => ?_)
  refine ((val_pull hJ _ _ _).trans (congrArg (fun r => val U'.cubG.t r y J) eF)).trans ?_
  have face {T : Over (Sp R')} {z : T.left} {I : (T.left ⟶ G'.left) → U'.LG.L.ι}
      (hI : Good U'.LG.L z I) (x y : T ⟶ G') :
      val U'.cubG.t (lift 1 (lift x y)).left z I = 1 := by
    have hv := val_corr hI (U'.cubG.face 0) (lift x y).left
    rw [val_one] at hv
    refine (Eq.trans ?_ (val_pull hI _ _ _).symm).trans hv
    congr 1
    rw [← Over.comp_left]
    simp [faceMap, x2, pzero, Hom.one_def]
  have f1 := face (T := Over.mk ((cubeMapOf hc).e ≫ (𝟙_ (Over (Sp R'))).hom)) hJ 1 1
  have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ G') 1 1
    (fun q => gw (Classical.choose hP.lg) q y (J (q ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)))) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  refine f1.trans (Eq.trans ?_ (congrArg₂ (· * ·) p (face hJ' 1 1)).symm)
  simp

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificatiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  first | exact @GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube | exact GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube | (intros; apply GlobalTheory.Mum.rigidified_galois_lin_carries_rig_and_cube <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCube
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCube
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CarriedCubeGen

section
variable {X Y Y₀ : Scheme.{0}} {L : LB X}

abbrev TestClass (L : LB X) (Y : Scheme.{0}) : Type 1 :=
  ∀ (f : X ⟶ X) (_ : LB.Iso L (L.pull f)) (Z : Scheme.{0}) (_ _ : Z ⟶ Y), Prop

def CTriv (L : LB X) (Y : Scheme.{0}) (A : TestClass L Y)
    (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ f w Z r r', A f w Z r r' → ∀ (z : Z) (J J' : (Z ⟶ X) → L.ι), Good L z J → Good L z J' →
      val t r' z J' = F _ (fun ψ => gw w (r ≫ ψ) z (J' ((r ≫ ψ) ≫ f)) (J (r ≫ ψ))) * val t r z J

variable {A : TestClass L Y}

theorem CTriv.congr {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F)
    (e : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), F U g = F' U g) : CTriv L Y A F' := by
  obtain ⟨K, _, φ, ε, t, ht, e₁, e₂⟩ := h
  exact ⟨K, inferInstance, φ, ε, t, ht, fun U _ g => (e₁ U g).trans (e U g),
    fun f w Z r r' hA z J J' hJ hJ' => (e₂ f w Z r r' hA z J J' hJ hJ').trans (by rw [e])⟩

theorem CTriv.mul {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F)
    (h' : CTriv L Y A F') : CTriv L Y A (fun U _ g => F U g * F' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e', c'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g)),
    fun f w Z r r' hA z J J' hJ hJ' => ?_⟩
  rw [val_mul hJ', val_mul hJ, c f w Z r r' hA z J J' hJ hJ', c' f w Z r r' hA z J J' hJ hJ']
  exact _root_.mul_mul_mul_comm _ _ _ _

theorem CTriv.inv {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F) :
    CTriv L Y A (fun U _ g => (F U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_,
    fun f w Z r r' hA z J J' hJ hJ' => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, e U g]
  · rw [val_inv, val_inv, c f w Z r r' hA z J J' hJ hJ', mul_inv]

theorem CTriv.exists_gen (hL : L.IsLB) {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv L Y A F)
    (g : Y ⟶ X) (hg : ∀ (U : Type) [CommGroup U] (u : (Y ⟶ X) → U), F U u = u g) :
    ∃ t : LB.Gen (L.pull g), t.IsGen ∧ ∀ f w Z r r', A f w Z r r' → ∀ (z : Z) (J J' : (Z ⟶ X) → L.ι),
      Good L z J → Good L z J' →
      val t r' z J' = gw w (r ≫ g) z (J' ((r ≫ g) ≫ f)) (J (r ≫ g)) * val t r z J := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  obtain ⟨t', ht', hv⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => g) (ε' := fun _ => 1)
    (fun U _ u => by rw [e, hg]; simp) t ht
  refine ⟨t', ht', fun f w Z r r' hA z J J' hJ hJ' => ?_⟩
  rw [hv _ _ z J hJ, hv _ _ z J' hJ', c f w Z r r' hA z J J' hJ hJ', hg]

theorem ctriv_of_pmaps {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (p : Y ⟶ Y₀)
    (hA : ∀ f w Z r r', A f w Z r r' → ∃ h : Y₀ ⟶ Y₀, PMaps w φ φ ε t t h ∧ (∀ k, φ k ≫ f = h ≫ φ k) ∧
      r' ≫ p = (r ≫ p) ≫ h) :
    CTriv L Y A (fun _ _ g => ∏ k, g (p ≫ φ k) ^ ε k) := by
  refine ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p, DVR.pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun f w Z r r' H z J J' hJ hJ' => ?_⟩
  obtain ⟨h, hm, hc, e⟩ := hA f w Z r r' H
  rw [val_pull hJ', val_pull hJ, e, val_of t _ z J' (fun k => J' (((r ≫ p) ≫ φ k) ≫ f))
    (fun k => by simp only [Category.assoc, hc]),
    hm Z (r ≫ p) z _ (fun k => J ((r ≫ p) ≫ φ k)) (fun k => hJ' (((r ≫ p) ≫ φ k) ≫ f))
      (fun k => hJ ((r ≫ p) ≫ φ k))]
  refine congrArg₂ (· * ·) ?_ rfl
  simp only [Category.assoc]

theorem gm_stalk {Z : Scheme.{0}} (κ : Z ⟶ Y) (z : Z) (r : Y ⟶ X) (U : X.Opens) (h : r (κ z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  rw [gm_val (κ ≫ r) z U h]
  show _ = (κ.stalkMap z).hom (gm r (κ z) U a).val
  rw [gm_val r (κ z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem gs_stalk {Z : Scheme.{0}} (κ : Z ⟶ Y) (z : Z) (r : Y ⟶ X) (U : X.Opens) (h : r (κ z) ∈ U)
    (a : Γ(X, U)) : gs (κ ≫ r) z U a = (κ.stalkMap z).hom (gs r (κ z) U a) := by
  rw [gs_eq (κ ≫ r) z U h, gs_eq r (κ z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem secCarried_along {θ : L.Sec} {f : X ⟶ X} {w : LB.Iso L (L.pull f)} (h : SecCarried L θ f w)
    {Z : Scheme.{0}} (ψ : Z ⟶ X) (z : Z) (j k : L.ι) (hk : ψ z ∈ L.U k) (hj : f (ψ z) ∈ L.U j) :
    gs (ψ ≫ f) z (L.U j) (θ.f j) = (gw w ψ z j k).val * gs ψ z (L.U k) (θ.f k) := by
  have e := congrArg (ψ.stalkMap z).hom (h (ψ z) j k hk hj)
  have e₁ := gs_stalk ψ z (𝟙 X) (L.U k) hk (θ.f k)
  have e₂ := gm_stalk ψ z (𝟙 X) ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hj, hk⟩ (w.s (fun _ => j, k))
  rw [Category.comp_id] at e₁ e₂
  rw [gs_stalk ψ z f _ hj, gs_eq f _ _ hj, e, map_mul, e₁, gs_eq (𝟙 X) (ψ z) _ hk, gw, gw, e₂]
  rfl

theorem ctriv_of_sec (θ : L.Sec) (g : Y ⟶ X) (hg : ∀ y, g y ∈ secNz θ)
    (hA : ∀ f w Z r r', A f w Z r r' → SecCarried L θ f w ∧ r' ≫ g = (r ≫ g) ≫ f) :
    CTriv L Y A (fun _ _ u => u g) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ g).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hg y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ g hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  let t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ ↦ g) fun _ ↦ ((1 : ℕ) : ℤ)) := ⟨fun j => (hu j).unit⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      (val t r z J).val = gs (r ≫ g) z (L.U (J (r ≫ g))) (θ.f _) := fun Z r z J hJ => by
    have hm := hJ.mem (fun _ : Fin 1 => g) r
    exact (gs_unit r z _ hm _).symm.trans ((gs_res r z (LB.wchart_le L (fun _ : Fin 1 => g) _ 0) hm _).trans
      (gs_pull r g z _ (hJ (r ≫ g)) _))
  refine ⟨Fin 1, inferInstance, _, _, t,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ g).compat i j), fun U _ u => by simp,
    fun f w Z r r' H z J J' hJ hJ' => Units.ext ?_⟩
  obtain ⟨hs, e⟩ := hA f w Z r r' H
  rw [Units.val_mul, hv _ _ z J hJ, hv _ _ z J' hJ', e]
  exact secCarried_along hs (r ≫ g) z _ _ (hJ _) (hJ' ((r ≫ g) ≫ f))

theorem stalk_units_injective {Z : Scheme.{0}} (i : Z ⟶ Y) [IsOpenImmersion i] (z : Z) :
    Function.Injective (Units.map (i.stalkMap z).hom.toMonoidHom) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (i.stalkMap z)).1 (congrArg Units.val h))

theorem exists_units (x : Y ⟶ X) (W : Y.Opens) (t : LB.Gen (L.pull (W.ι ≫ x))) :
    ∃ τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (k : L.ι), x (W.ι (r z)) ∈ L.U k →
      gm (r ≫ W.ι) z _ (τ k) = gm r z (LB.wchart L (fun _ : PUnit => W.ι ≫ x) (fun _ => k)) (t.s fun _ => k) := by
  have le : ∀ k, W.ι ⁻¹ᵁ (W ⊓ x ⁻¹ᵁ L.U k) ≤ LB.wchart L (fun _ : PUnit => W.ι ≫ x) (fun _ => k) :=
    fun k y hy => Set.mem_iInter.2 fun _ => hy.2
  have ex : ∀ k, ∃ u : Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ, pullU W.ι _ u = res (le k) (t.s fun _ => k) := fun k => by
    have : IsIso (W.ι.app (W ⊓ x ⁻¹ᵁ L.U k)) := W.ι.isIso_app _ (by simp)
    refine ⟨Units.map (CategoryTheory.inv (W.ι.app (W ⊓ x ⁻¹ᵁ L.U k))).hom.toMonoidHom
      (res (le k) (t.s fun _ => k)), Units.ext ?_⟩
    exact CategoryTheory.IsIso.inv_hom_id_apply (W.ι.app (W ⊓ x ⁻¹ᵁ L.U k)) _
  choose τ hτ using ex
  refine ⟨τ, fun Z r z k hk => ?_⟩
  have hm : W.ι (r z) ∈ W ⊓ x ⁻¹ᵁ L.U k := ⟨(r z).2, hk⟩
  rw [← gm_pull r W.ι z _ hm, hτ]
  exact gm_res r z (le k) hm _

theorem exists_frame (hL : L.IsLB) (x : Y ⟶ X) (W : Y.Opens) (t : LB.Gen (L.pull (W.ι ≫ x))) (ht : t.IsGen) :
    ∃ τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ, FrameAlong L x W τ ∧
      ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)) (h : Y ⟶ Y), x ≫ f = h ≫ x →
        (∀ (Z : Scheme.{0}) (r r' : Z ⟶ W), r' ≫ W.ι = (r ≫ W.ι) ≫ h → ∀ (z : Z) (J J' : (Z ⟶ X) → L.ι),
          Good L z J → Good L z J' → val t r' z J' =
            gw w (r ≫ W.ι ≫ x) z (J' ((r ≫ W.ι ≫ x) ≫ f)) (J (r ≫ W.ι ≫ x)) * val t r z J) →
        FrameCarriedAlong L x W τ f w h := by
  obtain ⟨τ, hτ⟩ := exists_units x W t
  refine ⟨τ, fun z k k' hz hk hk' => ?_, fun f w h hx H z j k hz hz' hk hj => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y : W, W.ι y = z := ⟨⟨z, hz⟩, rfl⟩
    apply stalk_units_injective W.ι y
    have a := hτ _ (𝟙 _) y k hk
    have a' := hτ _ (𝟙 _) y k' hk'
    rw [Category.id_comp] at a a'
    rw [map_mul, ← gm_stalk W.ι y (𝟙 Y) (W ⊓ x ⁻¹ᵁ L.U k) ⟨hz, hk⟩,
      ← gm_stalk W.ι y (𝟙 Y) (W ⊓ x ⁻¹ᵁ L.U k') ⟨hz, hk'⟩,
      ← gm_stalk W.ι y x (L.U k ⊓ L.U k') ⟨hk, hk'⟩, Category.comp_id, a, a']
    refine (gen_trans ht (𝟙 _) y (j := fun _ => k) (j' := fun _ => k') (Set.mem_iInter.2 fun _ => hk)
      (Set.mem_iInter.2 fun _ => hk')).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (Fintype.prod_unique _).trans ((zpow_one _).trans ?_)
    rw [Category.id_comp]
  · obtain ⟨Z, i, hi, r, r', y, rfl, e, e'⟩ : ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsOpenImmersion i) (r r' : Z ⟶ W)
        (y : Z), i y = z ∧ r ≫ W.ι = i ∧ r' ≫ W.ι = i ≫ h :=
      ⟨(W ⊓ h ⁻¹ᵁ W : Y.Opens), (W ⊓ h ⁻¹ᵁ W).ι, inferInstance, Y.homOfLE inf_le_left,
        IsOpenImmersion.lift W.ι ((W ⊓ h ⁻¹ᵁ W).ι ≫ h) (by
          rintro _ ⟨y, rfl⟩
          exact ⟨⟨h y.1, y.2.2⟩, rfl⟩), ⟨z, hz, hz'⟩, rfl, Scheme.homOfLE_ι _ _, IsOpenImmersion.lift_fac _ _ _⟩
    subst e
    have hfx : f (x (W.ι (r y))) ∈ L.U j := by
      have : (x ≫ f) (W.ι (r y)) = (h ≫ x) (W.ι (r y)) := by rw [hx]
      exact (show f (x (W.ι (r y))) = x (h (W.ι (r y))) from this) ▸ hj
    have hj' : x (W.ι (r' y)) ∈ L.U j := by
      have : (r' ≫ W.ι) y = ((r ≫ W.ι) ≫ h) y := by rw [e']
      exact (show W.ι (r' y) = h (W.ι (r y)) from this) ▸ hj
    obtain ⟨J, hJ, eJ⟩ := exists_good L hL y (fun _ : PUnit => r ≫ W.ι ≫ x) (fun _ => k) (fun _ _ _ => rfl)
      (fun _ => hk)
    obtain ⟨J', hJ', eJ'⟩ := exists_good L hL y (fun _ : PUnit => (r ≫ W.ι ≫ x) ≫ f) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => hfx)
    have c := H Z r r' e' y J J' hJ hJ'
    rw [val_of t r y J (fun _ => k) eJ, val_of t r' y J' (fun _ => j) (fun u => by
      rw [← eJ' u, ← Category.assoc, e']; simp only [Category.assoc, hx]), eJ ⟨⟩, eJ' ⟨⟩,
      ← hτ _ r y k hk, ← hτ _ r' y j hj', e'] at c
    apply stalk_units_injective (r ≫ W.ι) y
    rw [map_mul, ← gm_stalk (r ≫ W.ι) y h (W ⊓ x ⁻¹ᵁ L.U j) ⟨hz', hj⟩,
      ← gm_stalk (r ≫ W.ι) y (𝟙 Y) (W ⊓ x ⁻¹ᵁ L.U k) ⟨hz, hk⟩, Category.comp_id, c]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [← Category.assoc]
    exact gm_stalk (r ≫ W.ι) y x ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hfx, hk⟩ _

end

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {f : G.left ⟶ G.left} {fS : S ⟶ S}

theorem exists_subgroup (hc : IsGrpPullback G G fS f) (h : T.left ⟶ T.left) (hh : h ≫ T.hom = T.hom ≫ fS) :
    ∃ H : Subgroup (T ⟶ G), ∀ g, g ∈ H ↔ g.left ≫ f = h ≫ g.left :=
  ⟨(pushHom hc T).eqLocus (preHom (Over.homMk h hh : Over.mk (T.hom ≫ fS) ⟶ T)), fun _ =>
    ⟨fun e => congrArg (fun q => q.left) e, fun e => Over.OverMorphism.ext e⟩⟩

theorem lift_comm [IsCommMonObj G] (hc : IsGrpPullback G G fS f) (h : T.left ⟶ T.left)
    (hh : h ≫ T.hom = T.hom ≫ fS) (x u v : T ⟶ G) (hx : x.left ≫ f = h ≫ x.left) (hu : u.left ≫ f = h ≫ u.left)
    (hv : v.left ≫ f = h ≫ v.left) :
    (lift x (lift u v)).left ≫ (cubeMapOf hc).F3 = h ≫ (lift x (lift u v)).left := by
  let U : Over.mk (T.hom ≫ fS) ⟶ T := Over.homMk h hh
  let V : Over.mk (T.hom ≫ fS) ⟶ Over.mk ((G3 G).hom ≫ fS) := Over.homMk (lift x (lift u v)).left (by
    show (lift x (lift u v)).left ≫ (G3 G).hom ≫ fS = T.hom ≫ fS
    rw [← Category.assoc, Over.w])
  have key : ∀ (i : Fin 3) (g : T ⟶ G), lift x (lift u v) ≫ x3 G i = g → g.left ≫ f = h ≫ g.left →
      V ≫ pushPt hc.1.w (x3 G i) = U ≫ g := fun i g e hg => Over.OverMorphism.ext (by
    show (lift x (lift u v)).left ≫ (x3 G i).left ≫ f = h ≫ g.left
    rw [← Category.assoc, ← Over.comp_left, e, hg])
  have e : V ≫ lift (pushPt hc.1.w (x3 G 0)) (lift (pushPt hc.1.w (x3 G 1)) (pushPt hc.1.w (x3 G 2))) =
      U ≫ lift x (lift u v) := by
    rw [comp_lift, comp_lift, comp_lift, comp_lift, key 0 x (by simp [x3]) hx, key 1 u (by simp [x3]) hu,
      key 2 v (by simp [x3]) hv]
  exact congrArg (fun q => q.left) e

end

end GlobalTheory.Mum.CarriedCubeGen

namespace GlobalTheory.Mum

open CarriedCubeGen

theorem exists_carried_frame_of_cubeTen {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G')
    (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens)
    (hW : ∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) :
    ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧
      ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)),
        w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS →
        PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w →
        ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left →
          b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  let B : Subgroup (T ⟶ G') := Subgroup.closure {x, a, b, c'}
  have Bx : x ∈ B := Subgroup.subset_closure (by simp)
  have Ba : a ∈ B := Subgroup.subset_closure (by simp)
  have Bb : b ∈ B := Subgroup.subset_closure (by simp)
  have Bc : c' ∈ B := Subgroup.subset_closure (by simp)
  let A : TestClass L.L W := fun f w Z r r' => ∃ (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (hT : T.left ⟶ T.left),
    PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS ∧
    PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 ∧ SecCarried L.L θ f w ∧
    hT ≫ T.hom = T.hom ≫ fS ∧ (∀ g ∈ B, g.left ≫ f = hT ≫ g.left) ∧ r' ≫ W.ι = (r ≫ W.ι) ≫ hT
  have s : ∀ g ∈ cubeTen x a b c', g ∈ B → CTriv L.L W A (fun _ _ u => u (W.ι ≫ g.left)) := fun g hg gB =>
    ctriv_of_sec θ _ (fun y => hW g hg y.2) (by
      rintro f w Z r r' ⟨fS, hc, hT, -, -, hs, -, hB, e⟩
      refine ⟨hs, ?_⟩
      rw [← Category.assoc, e]
      simp only [Category.assoc, hB g gB])
  have cub : ∀ u ∈ B, ∀ v ∈ B, CTriv L.L W A (fun _ _ h =>
      h (W.ι ≫ (x * u * v).left) * (h (W.ι ≫ (x * u).left))⁻¹ * (h (W.ι ≫ (x * v).left))⁻¹ *
        (h (W.ι ≫ (u * v).left))⁻¹ * h (W.ι ≫ x.left) * h (W.ι ≫ u.left) * h (W.ι ≫ v.left) *
        (h (W.ι ≫ (1 : T ⟶ G').left))⁻¹) := fun u hu v hv =>
    (ctriv_of_pmaps (L := L.L) (φ := thφ G' (x3 G')) (ε := thε) c.t c.isGen (W.ι ≫ (lift x (lift u v)).left) (by
      rintro f w Z r r' ⟨fS, hc, hT, -, hm, -, hh, hB, e⟩
      refine ⟨_, hm, fun I => (cubeMapOf hc).psum_comm I.down, ?_⟩
      rw [← Category.assoc, e]
      simp only [Category.assoc, lift_comm hc hT hh x u v (hB x Bx) (hB u hu) (hB v hv)])).congr fun U _ g => by
      simp only [Category.assoc]
      exact prod_cub x u v (fun ψ => g (W.ι ≫ ψ))
  have e : CTriv L.L W A (fun _ _ h => h (W.ι ≫ (1 : T ⟶ G').left)) :=
    (ctriv_of_pmaps (L := L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) L.rig L.rigGen (W.ι ≫ T.hom) (by
      rintro f w Z r r' ⟨fS, hc, hT, hm, -, -, hh, -, e⟩
      refine ⟨_, hm, fun _ => (cubeMapOf hc).e_comm, ?_⟩
      show r' ≫ W.ι ≫ T.hom = (r ≫ W.ι ≫ T.hom) ≫ fS
      rw [← Category.assoc, e]
      simp only [Category.assoc, hh])).congr fun U _ g => by
      rw [Fintype.prod_unique, zpow_one]
      exact congrArg g (Category.assoc _ _ _)
  have Bbc := B.mul_mem Bb Bc
  have s₁ := s (x * a) (by simp [cubeTen]) (B.mul_mem Bx Ba)
  have s₂ := s (x * a⁻¹) (by simp [cubeTen]) (B.mul_mem Bx (B.inv_mem Ba))
  have s₃ := s a (by simp [cubeTen]) Ba
  have s₄ := s a⁻¹ (by simp [cubeTen]) (B.inv_mem Ba)
  have s₅ := s (x * b) (by simp [cubeTen]) (B.mul_mem Bx Bb)
  have s₆ := s (x * c') (by simp [cubeTen]) (B.mul_mem Bx Bc)
  have s₇ := s (x * (b * c')⁻¹) (by simp [cubeTen]) (B.mul_mem Bx (B.inv_mem Bbc))
  have s₈ := s b (by simp [cubeTen]) Bb
  have s₉ := s c' (by simp [cubeTen]) Bc
  have s₀ := s (b * c')⁻¹ (by simp [cubeTen]) (B.inv_mem Bbc)
  have c₁ := cub a Ba a⁻¹ (B.inv_mem Ba)
  have c₂ := cub b Bb c' Bc
  have c₃ := cub (b * c') Bbc (b * c')⁻¹ (B.inv_mem Bbc)
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  obtain ⟨t, ht, hv⟩ := ((t₃.mul t₂.inv).mul e).exists_gen L.isLB (W.ι ≫ x.left) fun U _ g => by
    simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ, hτ, hcar⟩ := exists_frame L.isLB x.left W t ht
  refine ⟨τ, hτ, fun f fS hc w _ hr hm hs hT hh hx ha hb hc' => hcar f w hT hx fun Z r r' er =>
    hv f w Z r r' ⟨fS, hc, hT, hr, hm, hs, hh, ?_, er⟩⟩
  obtain ⟨H, hH⟩ := exists_subgroup hc hT hh
  have le : B ≤ H := (Subgroup.closure_le H).2 (by
    rintro g (rfl | rfl | rfl | rfl)
    exacts [(hH _).2 hx, (hH _).2 ha, (hH _).2 hb, (hH _).2 hc'])
  exact fun g hg => (hH g).1 (le hg)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCubeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carriedFrame_theoremOfCube : ∀ {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G') (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens), (∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) → ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧ ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)), w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS → PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w → ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left → b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_of_cubeTen | exact GlobalTheory.Mum.exists_carried_frame_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_carried_frame_of_cubeTen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameBundleNearClosedPointFiniteEtaleExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem exists_carried_frame_upstairs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ₁ : R →+* R₁), FinExt ρ₁ ∧ ρ₁.Etale ∧ ∃ V₀ : G.left.Opens, y ∈ V₀ ∧ ∃ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ ∧ (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ hθ O hO hOθ y hyc hy
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hN : IsNoetherianRing R := hR.1
  have hI : IsIntegrallyClosed R := hR.2.2.1
  have := hS.smooth
  have hρf : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ)).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hρf
  have hgi : GeometricallyIrreducible G.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun Ω _ s => GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hS Ω s⟩
  have s₂ : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : GeometricallyIrreducible (G ⊗ G).hom := GeometricallyIrreducible.comp (pullback.fst G.hom G.hom) G.hom
  have s₃ : Smooth (G ⊗ G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom))
  have i₃ : GeometricallyIrreducible (G ⊗ G ⊗ G).hom :=
    GeometricallyIrreducible.comp (pullback.fst G.hom (G ⊗ G).hom) G.hom
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  obtain ⟨g, hgO, hg⟩ := hO
  have hgO' : g ∈ O' := fun g' e => by
    subst e
    exact hOθ g' hgO hg
  have hfin : IsFinite (G.left.fromSpecResidueField y ≫ G.hom) :=
    ClosedPt.isFinite_fromSpec G.hom y hyc (by rw [hy]; exact isClosed_singleton_closedPoint R)
  obtain ⟨N, hN₁, hN₂⟩ := ClosedPt.exists_open_good G.hom (G ⊗ G ⊗ G).hom y (ClosedPt.ten G)
    (fun f => f.left ⁻¹ᵁ O') fun f hf => by
      obtain ⟨q, h₁, h₂⟩ := ClosedPt.ten_meets G y g (hy.trans hg.symm) f hf
      exact ⟨q, show f.left q ∈ O' from h₁ ▸ hgO', h₂⟩
  rw [hy] at hN₁
  obtain ⟨R₁, _, _, _, ρ₁, t, hρ₁, het, ht, htN⟩ := GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR (G ⊗ G ⊗ G) s₃ N hN₁
  have hρ₁f : IsFinite (spMap ρ₁) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ₁)).2 hρ₁.2.2
  let m : pullback G.hom (spMap ρ₁) ⟶ pullback G.hom (G ⊗ G ⊗ G).hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by rw [Category.assoc, ht]; exact pullback.condition)
  have m₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ t := pullback.lift_snd _ _ _
  have hU : IsOpen {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} := by
    have : {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} =
        ⋂ f ∈ {f | f ∈ ClosedPt.ten G}, m ⁻¹' (f.left ⁻¹' O') := by ext; simp
    rw [this]
    exact (List.finite_toSet _).isOpen_biInter fun f _ => (O'.isOpen.preimage f.left.continuous).preimage m.continuous
  let V : G.left.Opens := ⟨_, ((pullback.fst G.hom (spMap ρ₁)).isClosedMap _ hU.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨p, hp, hpy⟩
    refine hp (hN₂ (m p) ?_ ?_)
    · rw [← Scheme.Hom.comp_apply, m₁, hpy]
    · rw [← Scheme.Hom.comp_apply, m₂, Scheme.Hom.comp_apply]
      exact htN ⟨_, rfl⟩
  have hgood : ∀ p : (pullback G.hom (spMap ρ₁) : Scheme.{0}), pullback.fst G.hom (spMap ρ₁) p ∈ V →
      ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O' := fun p hp => by
    by_contra h
    exact hp ⟨p, h, rfl⟩
  let q := pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)
  let s := pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)
  have hqs : (q ≫ β) ≫ G.hom = s ≫ spMap ρ₁ := by
    rw [Category.assoc, hβ.1.w]; exact pullback.condition
  let n' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback G.hom (spMap ρ₁) := pullback.lift (q ≫ β) s hqs
  have n₁ : n' ≫ pullback.fst _ _ = q ≫ β := pullback.lift_fst _ _ _
  have n₂ : n' ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  let ζ : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ (G ⊗ G ⊗ G ⊗ G).left := n' ≫ m
  let T : Over (Sp R') := Over.mk (q ≫ G'.hom)
  have hζ : ζ ≫ (fst G (G ⊗ G ⊗ G)).left = q ≫ β := by
    change (n' ≫ m) ≫ pullback.fst G.hom (G ⊗ G ⊗ G).hom = _
    rw [Category.assoc, m₁, n₁]
  have hw : ζ ≫ (G ⊗ G ⊗ G ⊗ G).hom = T.hom ≫ spMap ρ := by
    rw [← Over.w (fst G (G ⊗ G ⊗ G)), ← Category.assoc, hζ, Category.assoc, hβ.1.w]
    exact (Category.assoc _ _ _).symm
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv (Sp R) (Sp R') (spMap ρ) G G' β hβ T (G ⊗ G ⊗ G ⊗ G) ζ hw
  obtain ⟨a₁, ha⟩ := hl (snd _ _ ≫ fst _ _)
  obtain ⟨b₁, hb⟩ := hl (snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨c₁, hc₁⟩ := hl (snd _ _ ≫ snd _ _ ≫ snd _ _)
  let x : T ⟶ G' := Over.homMk q rfl
  have hx : x.left ≫ β = ζ ≫ (fst G _).left := hζ.symm
  have mu := fun u v u' v' h₁ h₂ => (hm u v u' v' h₁ h₂).1
  have iv := fun u u' h₁ => (hm u u u' u' h₁ h₁).2
  have key : ∀ f' ∈ cubeTen x a₁ b₁ c₁, ∃ f ∈ ClosedPt.ten G, f'.left ≫ β = ζ ≫ f.left := by
    intro f hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ ha)⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ (mu _ _ _ _ hb hc₁))⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ (mu _ _ _ _ hb hc₁)⟩
  have hten : ∀ g ∈ cubeTen x a₁ b₁ c₁, q ⁻¹ᵁ (β ⁻¹ᵁ V) ≤ g.left ⁻¹ᵁ secNz θ := by
    intro g' hg' z hz
    obtain ⟨f, hf, e⟩ := key g' hg'
    have hzV : pullback.fst G.hom (spMap ρ₁) (n' z) ∈ V := by
      rw [← Scheme.Hom.comp_apply, n₁, Scheme.Hom.comp_apply]; exact hz
    have h1 := hgood (n' z) hzV f hf
    refine h1 (g'.left z) ?_
    have e' := congrArg (fun φ => φ z) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact e'
  obtain ⟨τ, hτ, hcar⟩ := GlobalTheory.T.exists_carriedFrame_theoremOfCube G' U'.LG U'.cubG θ T x a₁ b₁ c₁ (q ⁻¹ᵁ (β ⁻¹ᵁ V)) hten
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hρ₁, het, V, hyV, τ, hτ, ?_⟩
  intro σ h bc hbc hP hPO f' hf'q hf's
  have hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) :=
    hbc ▸ a.cart σ
  have hrc := GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact σ h bc hbc hP
  have hTw : f' ≫ T.hom = T.hom ≫ spMap (Gal.hom σ) := by
    change f' ≫ q ≫ G'.hom = (q ≫ G'.hom) ≫ _
    rw [← Category.assoc, hf'q, Category.assoc, (a.cart σ).1.w, Category.assoc]
  have hfn : f' ≫ n' = n' := by
    apply pullback.hom_ext
    · rw [Category.assoc, n₁, ← Category.assoc, hf'q, Category.assoc, hact]
    · rw [Category.assoc, n₂, hf's]
  have hfζ : f' ≫ ζ = ζ := by
    change f' ≫ n' ≫ m = n' ≫ m
    rw [← Category.assoc, hfn]
  have lift_eq : ∀ (u₁ : T ⟶ G') (u : G ⊗ G ⊗ G ⊗ G ⟶ G), u₁.left ≫ β = ζ ≫ u.left →
      u₁.left ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) = f' ≫ u₁.left := by
    intro u₁ u hu
    rw [hbc]
    apply hβ.1.hom_ext
    · rw [Category.assoc, hact, hu, Category.assoc f', hu, ← Category.assoc, hfζ]
    · have e₁ : u₁.left ≫ G'.hom = T.hom := Over.w u₁
      rw [Category.assoc, (a.cart σ).1.w, ← Category.assoc, e₁, Category.assoc, e₁, hTw]
  exact hcar (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (specOf (Gal.hom σ)) hc
    (Classical.choose hP.lg) (Classical.choose_spec hP.lg).1 hrc.1 (hrc.2 hc) (hθ σ h bc hbc hP hPO) f' hTw
    (by rw [hbc]; exact hf'q.symm) (lift_eq a₁ _ ha) (lift_eq b₁ _ hb) (lift_eq c₁ _ hc₁)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameBundleNearClosedPointFiniteEtaleExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_bundle_near_closedPoint_finite_etale_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ₁ : R →+* R₁), FinExt ρ₁ ∧ ρ₁.Etale ∧ ∃ V₀ : G.left.Opens, y ∈ V₀ ∧ ∃ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ ∧ (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_upstairs | exact GlobalTheory.Mum.exists_carried_frame_upstairs | (intros; apply GlobalTheory.Mum.exists_carried_frame_upstairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameNearClosedFibrePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem FrameCarried.exists_near_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ hθ O hO hnz y hyc hy
  obtain ⟨R₁, _, _, _, ρ₁, hF₁, hE₁, V₀, hV₀, τ, hτ, hτc⟩ := GlobalTheory.T.exists_frame_bundle_near_closedPoint_finite_etale_ext R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact θ hθ O hO hnz y hyc hy
  exact GlobalTheory.T.frameCarried_descend_finiteEtale_extension R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact R₁ ρ₁ hF₁ hE₁ V₀ y hV₀ τ hτ hτc

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameNearClosedFibrePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_near_closedFibre_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.exists_near_closed_point | exact GlobalTheory.Mum.FrameCarried.exists_near_closed_point | (intros; apply GlobalTheory.Mum.FrameCarried.exists_near_closed_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closed_spec {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (hS : IsSemiAbelian G)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ y₀ : G.left, y ⤳ y₀ ∧ IsClosed ({y₀} : Set G.left) ∧ G.hom y₀ = closedPoint R := by
  have : QuasiCompact G.hom := hS.quasiCompact
  have hc : CompactSpace G.left := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := G.hom) Set.univ isOpen_univ isCompact_univ
    simpa using this
  obtain ⟨y₀, hy₀, hcl⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
  refine ⟨y₀, hsp, hcl, ?_⟩
  have h1 : G.hom y ⤳ G.hom y₀ := hsp.map G.hom.continuous
  rw [hy] at h1
  have h2 := specializes_iff_mem_closure.1 h1
  exact (isClosed_singleton_closedPoint R).closure_subset h2


set_option maxHeartbeats 1000000 in
theorem FrameCarried.exists_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  obtain ⟨y₀, hsp, hcl, hy₀c⟩ := closed_spec G hS y hy
  obtain ⟨V, hV, rest⟩ := GlobalTheory.T.exists_frame_near_closedFibre_point R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact θ hθ O hO hnz y₀ hcl hy₀c
  exact ⟨V, hsp.mem_open V.isOpen hV, rest⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameNearClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carried_frame_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre | exact GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre | (intros; apply GlobalTheory.Mum.FrameCarried.exists_near_closed_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantLocalFramesUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_lb_frames_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact
  have key : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · exact GlobalTheory.T.exists_carried_frame_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
    · exact GlobalTheory.T.exists_carried_frame_off_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  choose V hV T hT hI using key
  refine ⟨V, T, hV, hT, ?_⟩
  intro y y' r hr σ h
  obtain ⟨hh, bc, hf, hP, hPO⟩ := a.unif σ
  have i₁ := hI y σ hh bc hf hP hPO
  have i₂ := hI y' σ hh bc hf hP hPO
  revert h
  rw [← hf]
  intro h
  exact FrameCarried.ratio_fixed U'.LG.isLB i₁ i₂ (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.1)
    (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.2) r hr h

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantLocalFramesUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisInvariant_local_frames_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := by
  first | exact @GlobalTheory.Mum.unif_lb_frames_gal | exact GlobalTheory.Mum.unif_lb_frames_gal | (intros; apply GlobalTheory.Mum.unif_lb_frames_gal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisBaseChangeSemiAbelianInvariantUnitsDescend
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisBaseChangeSemiAbelianInvariantUnitsDescend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvUnit

theorem exists_unit_of_mem_range {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (u : Bˣ) (h : u.val ∈ Set.range f) (h' : (u⁻¹).val ∈ Set.range f) : ∃ g : Aˣ, Units.map (f : A →* B) g = u := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  have e : g * g' = 1 := hf (by rw [map_mul, hg, hg', map_one, Units.mul_inv])
  exact ⟨⟨g, g', e, (mul_comm g' g).trans e⟩, Units.ext hg⟩

theorem map_inv_eq {B : Type} [CommRing B] (t : B →+* B) (u : Bˣ) (h : t u.val = u.val) :
    t (u⁻¹).val = (u⁻¹).val := by
  have e : u.val * t (u⁻¹).val = 1 := by
    conv_lhs => rw [← h]
    rw [← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem invariant_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  intro R _ _ _ _ R' _ _ _ ρ hF hG G' _ G _ _ β act hS hβ hact hinv O
  have := hS.smooth
  have H := GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hF hG G.left G'.left G.hom G'.hom β inferInstance hβ.1 act hinv
    (fun σ => (hact σ).1.w) O
  refine ⟨H.1, fun u hu => ?_⟩
  exact exists_unit_of_mem_range (β.app O).hom H.1 u (H.2 _ hu) (H.2 _ fun σ h => map_inv_eq _ u (hu σ h))

end GlobalTheory.Mum.InvUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisBaseChangeSemiAbelianInvariantUnitsDescendStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisBaseChange_semiAbelian_invariant_units_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  first | exact @GlobalTheory.Mum.InvUnit.invariant_units | exact GlobalTheory.Mum.InvUnit.invariant_units | (intros; apply GlobalTheory.Mum.InvUnit.invariant_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLineBundleDescendsGalois
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBGal
open GlobalTheory.Mum.LBDesc

theorem lemD : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := GlobalTheory.T.galoisBaseChange_semiAbelian_invariant_units_descend

theorem lemF : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := GlobalTheory.T.exists_galoisInvariant_local_frames_uniformisation

theorem eq_of_gm_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O) (congrArg Units.val e))

theorem isLB_descLB_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom)
    (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB := {
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel }

end GlobalTheory.Mum.LBGal

namespace GlobalTheory.Mum
open GlobalTheory.Mum.LBDesc GlobalTheory.Mum.LBGal

theorem unif_lb_descend_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ L : LB G.left, L.IsLB ∧ LBIso U'.LG.L (L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hG' U' a G _ _ β hGs hβ hact
  have hDl := lemD R hR R' ρ hρ hG G' G β a.act hGs hβ a.cart hact
  obtain ⟨V, T, hyV, hT, hinv⟩ := lemF R hR R' ρ hρ hG D D' hD A' G' hG' U' a G β hGs hβ hact
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hc : ∀ (y : G.left) {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (k k' : U'.LG.L.ι), f w ∈ β ⁻¹ᵁ V y →
      f w ∈ U'.LG.L.U k → f w ∈ U'.LG.L.U k' →
      gm f w _ (T y k) = gm f w (U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat U'.LG.L _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio β U'.LG.L hL' (T y) (T y') (hc y) (hc y')
  have hri : ∀ y y' σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))),
      ((a.act σ).appLE _ _ h).hom (r y y').val = (r y y').val :=
    fun y y' => hinv y y' (r y y') (fun z k hz hk => hr y y' (𝟙 _) z k hz hk)
  choose g hg using fun y y' => (hDl (V y ⊓ V y')).2 (r y y') (hri y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (y y' : G.left) (k : U'.LG.L.ι), β (f w) ∈ V y →
      β (f w) ∈ V y' → f w ∈ U'.LG.L.U k →
      gm (f ≫ β) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f β w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB_inj β (fun O => (hDl O).1) U'.LG.L hL' V hyV T g key, descIso β U'.LG.L V T g,
    isGen_descIso β U'.LG.L V T g hc key⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLineBundleDescendsGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_lineBundle_descends_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ L : LB G.left, L.IsLB ∧ LBIso U'.LG.L (L.pull β) := by
  first | exact @GlobalTheory.Mum.unif_lb_descend_gal | exact GlobalTheory.Mum.unif_lb_descend_gal | (intros; apply GlobalTheory.Mum.unif_lb_descend_gal <;> assumption)
end

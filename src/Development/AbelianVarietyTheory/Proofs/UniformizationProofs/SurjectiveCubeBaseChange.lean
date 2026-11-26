module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ValueForm

theorem gen_unique_of_injective {X Y Y' S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (ρ : Y' ⟶ Y) (hρ : ∀ U : Y.Opens, Function.Injective (ρ.app U).hom)
    (p : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (e ≫ ρ) y J = val u' (e ≫ ρ) y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u' hu'
  have key := gen_unique hM p e he hp (DVR.pullGen_isGen _ _ _ _ hu ρ) (DVR.pullGen_isGen _ _ _ _ ht ρ)
    (fun y J hJ => (val_pull hJ _ _ _).trans (((h y J hJ).trans (hv _ _ y J hJ).symm).trans (val_pull hJ _ _ _).symm))
  have e₁ : ∀ j, u.s j = t.s j := fun j => by
    apply Units.map_injective (f := (ρ.app (LB.wchart M φ j)).hom.toMonoidHom) (hρ _)
    refine unit_ext fun y hy => ?_
    choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    have hy' : ρ y ∈ LB.wchart M φ j := hy
    have k := (val_pull hI _ _ _).symm.trans ((key _ (𝟙 Y') y I hI).trans (val_pull hI _ _ _))
    rw [Category.id_comp] at k
    refine (gm_pull (𝟙 Y') ρ y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') ρ y _ hy' _).symm)
    rw [Category.id_comp]
    exact (gen_trans hu ρ y hy' (Good.mem hI φ ρ)).trans ((congrArg _ k).trans
      (gen_trans ht ρ y hy' (Good.mem hI φ ρ)).symm)
  exact (congrArg (gm r z _) (e₁ _)).trans (hv Z r z J hJ)

theorem sym_cub_of_baseChange {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (hi : ∀ U, Function.Injective ((pullback.fst (G3 G).hom f).app U).hom)
    (h3 : Function.Surjective (pullback.snd (G3 G).hom f).appTop.hom) {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L))
    (T : Over S) (x y u : T ⟶ G) (z : T.left) (J) (hJ : Good L.L z J) :
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J *
        val sym u.left z J := by
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let sy := fun p : G3 G ⟶ G => LB.pullGen L.L _ _ sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hs _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vs : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (sy p) σ.left z J = val sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a⁻¹ b⁻¹ d⁻¹) (sy (a * b)))
    (sy (a * d))) (sy (b * d))
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a b d)
    (sy (a * b * d))) (sy a)) (sy b)) (sy d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a)⁻¹ (σ ≫ b)⁻¹ (σ ≫ d)⁻¹ * val sym ((σ ≫ a) * (σ ≫ b)).left z J *
        val sym ((σ ≫ a) * (σ ≫ d)).left z J * val sym ((σ ≫ b) * (σ ≫ d)).left z J ∧
      val t₂ σ.left z J = cubV c z J (σ ≫ a) (σ ≫ b) (σ ≫ d) * val sym ((σ ≫ a) * (σ ≫ b) * (σ ≫ d)).left z J *
        val sym (σ ≫ a).left z J * val sym (σ ≫ b).left z J * val sym (σ ≫ d).left z J := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul, ← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv,
        ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
  let e : Over.mk f ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 G := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique_of_injective L.isLB (fun V _ k => ?_) (pullback.fst (G3 G).hom f) hi (pullback.snd _ _)
      (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp f).symm)) (pullback.lift_snd _ _ _) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _))
        (gs _)) (gs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _)) (gs _)) (gs _)) (gs _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := ((thK ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a b d k) (prod_sym (a * b * d) k))
            (prod_sym a k)) (prod_sym b k)) (prod_sym d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a⁻¹ b⁻¹ d⁻¹ k) (prod_sym (a * b) k))
            (prod_sym (a * d) k)) (prod_sym (b * d) k)).symm)
      simp only [← mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val sym (1 : Over.mk f ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI sym (eSec G) _).symm.trans ((val_corr hI hr _).trans (val_one _))
      rw [pullback.lift_fst]
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, e₂]
      simp only [inv_one, _root_.mul_one, s1]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁, r₂] at this

theorem app_generic_injective {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p] (U : Y.Opens) :
    Function.Injective ((pullback.fst p (jK R)).app U).hom := by
  have hd : IsSchemeTheoreticallyDominant (jK R) := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have i : Function.Injective ((jK R).appTop ≫ (Scheme.ΓSpecIso _).hom).hom := by
      rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
      exact (IsFractionRing.injective R (FractionRing R)).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at i
    exact i.of_comp
  have pb := (IsPullback.of_hasPullback p (jK R)).flip
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) := .of_isPullback pb
  have : QuasiCompact (pullback.fst p (jK R)) := inferInstance
  exact (pullback.fst p (jK R)).app_injective U

theorem surjective_cube_baseChange (hG : GlobalFnsSt) {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {A : Over S'}
    [GrpObj A] (hA : IsAbelianScheme A) (gen : (Over.pullback f).obj G ≅ A) :
    Function.Surjective (pullback.snd (G3 G).hom f).appTop.hom := by
  have := hA.comm
  let e : (Over.pullback f).obj (G3 G) ≅ G3 A := (Functor.Monoidal.μIso (Over.pullback f) G (G ⊗ G)).symm ≪≫
    (gen ⊗ᵢ ((Functor.Monoidal.μIso (Over.pullback f) G G).symm ≪≫ (gen ⊗ᵢ gen)))
  have hw : e.hom.left ≫ (G3 A).hom = pullback.snd (G3 G).hom f := Over.w e.hom
  have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have : IsIso e.hom.left.appTop := inferInstanceAs (IsIso (e.hom.left.app ⊤))
  rw [← hw]
  exact surj_comp (ConcreteCategory.bijective_of_isIso e.hom.left.appTop).2 (surjective_cube hG hA)

section Clauses

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

def modelCP (hG : GlobalFnsSt) : CP G where
  L := U.LG
  c := U.cubG
  sym := U.symG
  sym_gen := U.symG_gen
  sym_rig := U.symG_rig
  sym_cub := by
    have := U.smooth
    have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    exact sym_cub_of_baseChange (jK R) (app_generic_injective _) (surjective_cube_baseChange hG _ A.isAb U.gen)
      U.cubG U.symG U.symG_gen U.symG_rig

theorem rig_val (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) {z : T.left}
    {N : (T.left ⟶ G.left) → U.LG.L.ι} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) :
    val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        (T.hom ≫ thick R I e) z J =
      TorusInvariance.wVal U e z J N (1 : T ⟶ thickObj R I e G).left *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (T.hom ≫ thick R I e) z N := by
  have hp : (T.hom ≫ eSec (thickObj R I e G)) ≫ (U.gt e).pG.left = (T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (T.hom ≫ ·) (UnifPullRig.eSec_pG I (U.gt e))).trans
      (Category.assoc _ _ _).symm)
  have hf : (T.hom ≫ eSec (thickObj R I e G)) ≫ (fstG I e G).left = (T.hom ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (T.hom ≫ ·) (UnifPullRig.eSec_fstG I e G)).trans
      (Category.assoc _ _ _).symm)
  rw [one_left, TorusInvariance.wVal, hp, hf]
  obtain ⟨j, hj⟩ : ∃ j, J ((T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((T.hom ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((T.hom ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : T.hom z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : T.hom z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : T.hom z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm T.hom z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

theorem compat_val (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (j : D.toPre.P.L.ι)
    (k : U.LG.L.ι) (hj : (U.gt e).pG.left (x z) ∈ D.toPre.P.L.U j) (hk : (fstG I e G).left (x z) ∈ U.LG.L.U k) :
    gw (U.w (e + 1)) (x ≫ thickMap R I e G) z j (fun _ => k) = gw (U.w e) x z j (fun _ => k) := by
  have m₁ : x z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => j) ⊓
      (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g (x z) ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hj),
      mem_pull.2 ((congrArg (fun g => g (x z) ∈ U.LG.L.U k) (UnifPullRig.thickMap_fstG I e G)).mpr hk)⟩
  have m₂ : x z ∈ (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓
      (U.LG.L.pull (fstG I e G).left).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  have W := congrArg (gm x z _) (U.w_compat e (fun _ => j, fun _ => k) (_ ⊓ _) inf_le_left inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨m₁, m₂⟩) _).trans (gm_pull _ _ z _ m₁ _)).symm.trans
    (W.trans (gm_res _ z _ (by exact ⟨m₁, m₂⟩) _))

def toPreU (hG : GlobalFnsSt) (hS : IsSemiAbelian G)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) :
    PreU I D.toPre A G where
  semi := hS
  gen := U.gen
  gen_hom := U.gen_hom
  P := modelCP U hG
  wA := w
  wA_gen := hw
  gt := U.gt
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals e T z N J hN hJ W hW := by
    obtain rfl : W = fun x => TorusInvariance.wVal U e z J N x.left := funext hW
    refine ⟨rig_val U e T hN hJ, fun x => TorusInvariance.even_val U x.left hJ hN, fun x y u => ?_⟩
    exact cub_alg ((TorusInvariance.cube_val U ![x, y, u] hJ hN).trans (congrArg₂ (· * ·)
      (TorusInvariance.prod_psum x y u (TorusInvariance.wVal U e z J N)) rfl))
  w_compat := compat_val U

end Clauses

theorem exists_preU_match :
    GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U' : UnifPre I D A G), IsSemiAbelian G → ∀ w : LB.Iso (A.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen → ∃ U : PreU I D.toPre A G, Match U U' ∧ HEq U.wA w :=
  fun hG _ _ _ _ _ _ _ _ _ U' hS w hw =>
    ⟨toPreU U' hG hS w hw, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩, HEq.rfl⟩

end GlobalTheory.ValueForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaRep

theorem finrank_secM (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {n : ℕ}
    (hn : 1 ≤ n) {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ S) :
    Module.finrank Γ((Over.mk q).left, ⊤) (SecM P.A P.L n (Over.mk q)) = n ^ P.g := by
  obtain ⟨U, hU, b, hb⟩ := hS S P n hn (q (IsLocalRing.closedPoint F))
  have hr : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    exact ⟨⟨_, hU⟩, rfl⟩
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver S) U).left := IsOpenImmersion.lift U.ι q hr
  have ht : t ≫ (overRes (T := baseOver S) U).hom = q := by
    show IsOpenImmersion.lift U.ι q hr ≫ (U.ι ≫ 𝟙 _) = q
    rw [Category.comp_id, IsOpenImmersion.lift_fac]
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L n (baseAt t)),
      IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨h₁, h₂⟩ := hb F t b' hb'
  rw [← ht]
  haveI : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (Module.finrank_eq_card_basis (Module.Basis.mk h₁ h₂.ge)).trans (Fintype.card_fin _)

theorem eq_one_of_weilIs (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S) {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk q ⟶ P.A)
    (hx : x ^ n = 1) (h : ∀ y : Over.mk q ⟶ P.A, y ^ n = 1 → WeilIs P.A P.L n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hL.polBaseChange S _ q P
  have hp : IsGrpPullback P'.A P.A q g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  let ρ : Over.mk q ⟶ Over.mk (𝟙 _ ≫ q) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  let Φ : (baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) →* (Over.mk q ⟶ P.A) :=
    MonoidHom.mk' (fun y => ρ ≫ toBase hg.w y) (fun a b => by rw [hm, MonObj.comp_mul])
  have hΦ : ∀ y, (Φ y).left = y.left ≫ g := fun y => Category.id_comp _
  have inj : Function.Injective Φ := fun a b e => Over.OverMorphism.ext (hg.hom_ext
    ((hΦ a).symm.trans ((congrArg CommaMorphism.left e).trans (hΦ b))) ((Over.w a).trans (Over.w b).symm))
  let x' : baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp q).symm)) (hg.lift_snd _ _ _)
  have ex : Φ x' = x := Over.OverMorphism.ext ((hΦ x').trans (hg.lift_fst _ _ _))
  have hx' : x' ^ n = 1 := inj (by rw [map_pow, ex, hx, map_one])
  have := hL.weilNondeg F P' n hn x' hx' fun y hy =>
    (GlobalTheory.weilIs_grpPullback_iff hL.globalFns hL.cube P P' hp w hw (t := q) (t' := 𝟙 _) (Category.id_comp q).symm n x' y hx' hy x (Φ y)
      ((congrArg CommaMorphism.left ex).symm.trans (hΦ x')) (hΦ y) 1).1 (h _ (by rw [← map_pow, hy, map_one]))
  rw [← ex, this, map_one]

theorem exists_projective_rep : Laws → Laws2 → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → ∃ (Φ : {x : Over.mk p ⟶ P.A // x ^ N = 1} → (SecM P.A P.L N (Over.mk p) ≃ₗ[Γ((Over.mk p).left, ⊤)] SecM P.A P.L N (Over.mk p))) (e : {x : Over.mk p ⟶ P.A // x ^ N = 1} → {x : Over.mk p ⟶ P.A // x ^ N = 1} → Γ((Over.mk p).left, ⊤)ˣ), Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) = N ^ P.g ∧ (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ (SecM.toSec P.A v) (SecM.toSec P.A (Φ a v))) ∧ (∀ a b c, c.1 = a.1 * b.1 → ∃ r : Γ((Over.mk p).left, ⊤)ˣ, ∀ v, Φ c v = r.val • Φ a (Φ b v)) ∧ (∀ a b, WeilIs P.A P.L N a.1 b.1 (e a b) ∧ ∀ v, Φ a (Φ b v) = (e a b).val • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a.1 = 1) := by
  intro hL _ S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  haveI : Subsingleton (Over.mk p).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (Over.mk p).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨ρ, hact, hcomm, hrat, hmul⟩ := thetaGrp_acts_linearly hL.globalFns S P N (Over.mk p)
  choose θ hθ using fun a : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    BoxTheta.exists_theta hL.kerPow P hN1 (T := Over.mk p) a.1 a.2
  choose e he using fun a b : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    ((hL.weil S P N (Over.mk p)).1 a.1 b.1 a.2 b.2).exists
  refine ⟨fun a => ρ (θ a), e, finrank_secM hL.secBaseChange P hN1 p,
    fun a => ⟨θ a, hθ a, fun v => (hact _ _ _).2 rfl⟩, fun a b c hc => ?_, fun a b => ⟨he a b, ?_⟩, fun a ha => ?_⟩
  · obtain ⟨θ', h₁, h₂⟩ := hmul (θ a) (θ b)
    obtain ⟨r, hr⟩ := hrat θ' (θ c) (by rw [h₁, hθ, hθ, hθ, hc])
    exact ⟨r, fun v => by rw [← h₂]; exact hr v⟩
  · refine hcomm _ _ _ ((GlobalLift.weilIs_iff_commIsOf hL.globalFns P.isAb P.isLB _ _ _).1 ?_)
    rw [hθ, hθ]
    exact he a b
  · exact eq_one_of_weilIs hL P p hN a.1 a.2 fun y hy => ha ⟨y, hy⟩ ▸ he a ⟨y, hy⟩

end GlobalTheory.ThetaRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AbPackage

theorem exists_unit_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val u r z J * (val u' r z J)⁻¹ :=
    (gm_res r z le trivial _).trans ((val_of t r z J PEmpty.elim (fun k => k.elim)).symm.trans
      ((hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ (val_inv _ _)))))
  exact (inv_mul_cancel_right _ _).symm.trans (congrArg (· * val u' r z J) e.symm)

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]


omit [IsCommMonObj B] in
theorem exists_rigidified_sym {L : LB B.left} (hL : L.IsLB)
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec B)) (LB.oneGen L) := by
  have he : eSec B ≫ (ι[B]).left = eSec B :=
    congrArg (fun q => q.left) (show η[B] ≫ GrpObj.inv = η[B] by simp)
  let n : B.left ⟶ B.left := (toUnit B).left ≫ eSec B
  have hn : eSec B ≫ n = eSec B := by
    rw [← Category.assoc, show eSec B ≫ (toUnit B).left = 𝟙 _ from
      congrArg (fun q => q.left) (show η[B] ≫ toUnit B = 𝟙 _ by simp), Category.id_comp]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(ι[B]).left, 𝟙 _]) (ε' := ![1, -1])
    (fun V _ k => by
      have e : n ≫ (ι[B]).left = n := by rw [Category.assoc, he]
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, e])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, hn, mul_inv_cancel, val_one]

theorem exists_cp (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (L : RigLB B)
    (h₁ : ∃ t : LB.Gen (Theta B L.L), t.IsGen)
    (h₂ : ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) :
    ∃ M : CP B, M.L = L := by
  obtain ⟨t, ht⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised L.isLB t ht
  obtain ⟨u, hu, hr⟩ := exists_rigidified_sym L.isLB s hs
  exact ⟨CP.ofSurjective (surjective_cube hG hB) L (GlobalTheory.AbLaw.Cube.cubicalOfNormalised hG hB L t' ht' hn) u hu hr, rfl⟩

theorem exists_isCPMap_of_iso (hG : GlobalFnsSt) {S' : Scheme.{0}} {f : S' ⟶ S} {B' : Over S'} [GrpObj B']
    [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B') {β : B'.left ⟶ B.left}
    {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen) : ∃ v, IsCPMap M' M f β hw v := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec B') (ε := fun _ => 1) hr M'.L.rigGen
  let b : Γ(B'.left, ⊤)ˣ := pullU B'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ B') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ β)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull β).U (fun _ => J (x.left ≫ β)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ β)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left B'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ β) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

theorem abelian_cp : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  intro hG S B _ _ hB
  refine ⟨exists_cp hG hB, fun S' f B' _ _ hB' M M' β h _ ⟨w, hg⟩ => ⟨h, ?_⟩⟩
  exact exists_isCPMap_of_iso hG hB' M M'
    (fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm) w hg

end GlobalTheory.AbPackage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMapsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  first | exact @GlobalTheory.AbPackage.abelian_cp | exact GlobalTheory.AbPackage.abelian_cp | (intros; apply GlobalTheory.AbPackage.abelian_cp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PullSec

section General
variable {X X' W Y Y₂ : Scheme.{0}}

theorem sec_eq {M : LB X} {s t : LB.Sec M} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t; congr; funext i; exact h i

theorem exists_pullSec {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y₂ ⟶ X)} {φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (h : Y ⟶ Y₂) (hc : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  have h1 : (LB.oneGen L (Y := Y)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨s', hs⟩ := exists_sec hL (φ' := φ') (ε' := ε) (fun U _ g => by
      refine ((Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) rfl (Fintype.prod_empty _)).trans
        (_root_.mul_one _))).trans ?_
      exact Finset.prod_congr rfl fun k _ => by rw [hc]; rfl) (pullMulSec s h (LB.oneGen L) h1)
  refine ⟨s', fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec s h _ h1 r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem exists_sec_of_iso {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y₀ : Y ⟶ W) (h : Y ⟶ Y₂) (a : Y ⟶ X') (b : Y₂ ⟶ X)
    (ha : y₀ ≫ F' = a) (hb : y₀ ≫ F = h ≫ b) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => b) (fun _ => (k : ℤ)))) :
    ∃ t : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => a) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι) (j : L'.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U j →
        (gw w (r ≫ y₀) z i (fun _ => j)).val ^ k *
            gs r z (LB.wchart L' (fun _ : Fin 1 => a) (fun _ => j)) (t.f fun _ => j) =
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
  subst ha
  have pw := (isGen_iff w).1 hw
  have pt : ∀ y : Y, b (h y) = F (y₀ y) := fun y => congrArg (fun g => g y) hb.symm
  have mb : ∀ (y : Y) (i : L.ι), F (y₀ y) ∈ L.U i → h y ∈ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) :=
    fun y i hi => Set.mem_iInter.2 fun _ => show b (h y) ∈ L.U i by rw [pt]; exact hi
  have tw : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i i' : L.ι) (j j' : L'.ι), F (y₀ (r z)) ∈ L.U i →
      F (y₀ (r z)) ∈ L.U i' → F' (y₀ (r z)) ∈ L'.U j → F' (y₀ (r z)) ∈ L'.U j' →
      ((gw w (r ≫ y₀) z i (fun _ => j))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) =
        (gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') ^ (k : ℤ)).val *
          (((gw w (r ≫ y₀) z i' (fun _ => j'))⁻¹ ^ k).val *
            gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i')) (σ.f fun _ => i')) := by
    intro Z r z i i' j j' hi hi' hj hj'
    have e := pw Z (r ≫ y₀) z i i' (fun _ => j) (fun _ => j') hi hi' (mem_pull.2 hj) (mem_pull.2 hj')
    rw [gm_pull_g L' F' (r ≫ y₀) z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
    rw [sec_trans σ (r ≫ h) z (mb _ i hi) (mb _ i' hi'), trF, Fintype.prod_unique, e, ← _root_.mul_assoc,
      ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    rw [Category.assoc r h b, ← hb, Category.assoc r y₀ F, Category.assoc r y₀ F', zpow_natCast, zpow_natCast,
      ← mul_pow, ← mul_pow]
    congr 1
    generalize gm (r ≫ y₀ ≫ F) z (L.U i ⊓ L.U i') (L.g i i') = P
    generalize gm (r ≫ y₀ ≫ F') z (L'.U j ⊓ L'.U j') (L'.g j j') = Q
    generalize gw w (r ≫ y₀) z i' (fun _ => j') = C
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : Fin 1 → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), F (y₀ (r z)) ∈ L.U i → F' (y₀ (r z)) ∈ L'.U (j 0) →
        gs r z _ s = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) := by
    intro j
    obtain ⟨V, hV⟩ : ∃ V : L.ι → Y.Opens, ∀ i y, y ∈ V i ↔ F (y₀ y) ∈ L.U i ∧ F' (y₀ y) ∈ L'.U (j 0) :=
      ⟨fun i => y₀ ⁻¹ᵁ (F ⁻¹ᵁ L.U i) ⊓ y₀ ⁻¹ᵁ (F' ⁻¹ᵁ L'.U (j 0)), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, V i ≤ LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j := fun i y hy =>
      Set.mem_iInter.2 fun c => by rw [Subsingleton.elim c 0]; exact ((hV i y).1 hy).2
    have l₁ : ∀ i, V i ≤ y₀ ⁻¹ᵁ ((L.pull F).U (fun _ => i) ⊓ (L'.pull F').U (fun _ => j 0)) := fun i y hy =>
      ⟨mem_pull.2 ((hV i y).1 hy).1, mem_pull.2 ((hV i y).1 hy).2⟩
    have l₂ : ∀ i, V i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => b) (fun _ => i) := fun i y hy =>
      mb y i ((hV i y).1 hy).1
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, V i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L.ι), r z ∈ V i →
        gs r z (V i) (u i) = ((gw w (r ≫ y₀) z i (fun _ => j 0))⁻¹ ^ k).val *
          gs (r ≫ h) z (LB.wchart L (fun _ : Fin 1 => b) (fun _ => i)) (σ.f fun _ => i) :=
      ⟨fun i => ((res (l₁ i) (pullU y₀ _ (w.s (fun _ => i, fun _ => j 0))))⁻¹ ^ k).val *
          (Y.presheaf.map (homOfLE (l₂ i)).op).hom ((h.app _).hom (σ.f fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val
          ((map_pow _ _ _).trans (congrArg (· ^ k) ((map_inv _ _).trans (congrArg (·⁻¹)
            ((gm_res r z (l₁ i) hz _).trans (gm_pull r y₀ z _ (l₁ i hz) _))))))))
          ((gs_res r z (l₂ i) hz _).trans (gs_pull r h z _ (l₂ i hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V (LB.wchart L' (fun _ : Fin 1 => y₀ ≫ F') j)
      (fun i => homOfLE (l₀ i)) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hV i y).2 ⟨hi, Set.mem_iInter.1 hy 0⟩⟩) u
      (fun i i' => fn_ext (V := V i ⊓ V i') fun y hy => by
        have h₁ := (hV i y).1 hy.1
        have h₂ := (hV i' y).1 hy.2
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, tw _ (𝟙 Y) y i i' (j 0) (j 0) h₁.1 h₂.1 h₁.2 h₁.2,
          gm_self hL' (𝟙 Y ≫ y₀ ≫ F') y h₁.2, one_zpow, Units.val_one, _root_.one_mul])
    refine ⟨s, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ V i := (hV i _).2 ⟨h₁, h₂⟩
    exact (gs_res r z (l₀ i) hz s).symm.trans ((congrArg (gs r z (V i)) (hs i)).trans (hu Z r z i hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j hi hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL (F (y₀ y))
    have m : F' (y₀ y) ∈ L'.U (j 0) := Set.mem_iInter.1 hy.1 0
    have m' : F' (y₀ y) ∈ L'.U (j' 0) := Set.mem_iInter.1 hy.2 0
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L' _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (hs j _ (𝟙 Y) y i hi m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y i hi m')).symm)
    rw [Fin.prod_univ_one]
    exact tw _ (𝟙 Y) y i i (j 0) (j' 0) hi hi m m'
  · refine (congrArg _ (hs (fun _ => j) Z r z i hi hj)).trans ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one, _root_.one_mul]

end General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem existsUnique_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (σ : U.SecGT T k) :
    ∃! t, U.PullG F φ k σ t := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have hi : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₁ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := exists_sec_of_iso U.P.L.isLB A.isLB U.wA U.wA_gen y₀ h _ (snd T G).left ha h₂.symm k σ
  have key : U.PullG F φ k σ t := by
    intro Z rA y rG e₁ e₂ e₃ z JA JG hA hG
    obtain rfl : y = rA ≫ y₀ := by
      have := congrArg (· ≫ U.gen.inv.left) e₁
      simp only [Category.assoc, hi, Category.comp_id] at this
      exact this.symm
    obtain rfl : rG = rA ≫ h := by
      refine pullback.hom_ext (e₃.trans ?_) (e₂.trans ?_)
      · exact ((Category.assoc _ _ _).trans (congrArg (rA ≫ ·) h₁)).symm
      · exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (rA ≫ ·) h₂)).symm
    rw [sval_of (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) t rA z JA
        (fun _ => JA ((rA ≫ y₀) ≫ U.gen.hom.left)) (fun _ => congrArg JA e₁),
      sval_of σ (rA ≫ h) z JG (fun _ => JG ((rA ≫ y₀) ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG e₂)]
    exact ht Z rA z _ _ (hG ((rA ≫ y₀) ≫ pullback.fst G.hom (jK R))) (hA ((rA ≫ y₀) ≫ U.gen.hom.left))
  refine ⟨t, key, fun t' key' => sec_eq fun j => sec_ext_val A.isLB (fun z JA hA => ?_) j⟩
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₁.trans (Category.id_comp _).symm
  have := (key' _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans (key _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).symm
  rw [← Units.val_pow_eq_pow_val] at this
  exact (Units.mul_right_inj _).1 this

theorem existsUnique_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃! s, PullB D F φ k f s := by
  have hc : ∀ (α : D.X) (i : Fin 4), DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D T α i := fun α i => by
    have u : φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd T D.P.A := (whiskerRight_snd _ _).symm
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  choose s hs using fun α => exists_pullSec D.P.isLB (φ ▷ D.P.A).left (hc α) (f α)
  have key : PullB D F φ k f s := fun α z J hJ => (hs α _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp])
  exact ⟨s, key, fun s' key' => funext fun α => sec_eq fun j => sec_ext_val D.P.isLB
    (fun z J hJ => (key' α z J hJ).trans (key α z J hJ).symm) j⟩

theorem pullEx : (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (T : Over (Spec (CommRingCat.of V))) (φ : TF (R := V) F ⟶ T) (k : ℕ), (∀ σ, ∃! t, U.PullG F φ k σ t) ∧ ∀ f, ∃! s, PullB D F φ k f s) :=
  fun _ _ _ _ _ D _ _ _ _ U F _ _ _ φ k => ⟨existsUnique_pullG U F φ k, existsUnique_pullB D F φ k⟩

end GlobalTheory.UU.PullSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_unit_val_eq_mul {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ c.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← Units.mul_inv_eq_iff_eq_mul, ← Units.val_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ,
    val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem exists_psiScal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V), ∃ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a := by
  intro V _ _ _ D
  choose ga hga using fun χ : D.X =>
    DVR.exists_gen_of_local (V := V) D.P.L D.P.isLB (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have key := fun χ : D.X => exists_unit_val_eq_mul D.P.isLB (D.psi_gen χ)
    (DVR.pullGen_isGen D.P.L _ _ (ga χ) (hga χ) (toUnit (TK V)).left)
  choose c hc using key
  refine ⟨ga, fun χ => Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom.toMonoidHom (c χ),
    fun χ => ⟨hga χ, fun T κ z J hJ => ?_⟩⟩
  have e : κ.left ≫ (toUnit (TK V)).left = (toUnit T).left := by
    rw [← Over.comp_left, comp_toUnit]
  refine (hc χ T.left κ.left z J hJ).trans ?_
  refine congrArg₂ (· * ·) ?_ (congrArg Units.val ((val_pull hJ (ga χ) _ κ.left).trans (by rw [e])))
  have e₂ : scal κ.left ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (c χ).val) =
      κ.left.appTop.hom (c χ).val :=
    congrArg κ.left.appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))) _)
  refine Eq.trans ?_ (congrArg (gs (𝟙 _) z ⊤) e₂).symm
  exact (congrArg (fun q => gs q z ⊤ (c χ).val) (Category.id_comp κ.left)).symm.trans
    (gs_pull (𝟙 _) κ.left z ⊤ trivial _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

theorem sval_comb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' t'' : LB.Sec (LB.LinComb L φ ε)} (a : Γ(Y, ⊤))
    (h : ∀ j, t''.f j = (Y.presheaf.map (homOfLE le_top).op).hom a * t.f j + t'.f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t'' r z J = gs r z ⊤ a * sval t r z J + sval t' r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_add _ _ _ hm _ _).trans (congrArg (· + _) ((gs_mul _ _ _ hm _ _).trans (congrArg (· * _) ?_)))
  exact gs_res r z le_top hm a

theorem gs_scal_mul {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (a b : R) : gs r z ⊤ (scal p (a * b)) = gs r z ⊤ (scal p a) * gs r z ⊤ (scal p b) := by
  rw [← gs_mul r z ⊤ trivial]
  simp only [scal, map_mul]

theorem sum_append {α β M : Type*} [AddCommMonoid M] {n m : ℕ} (g : α → β → M) (c : Fin n → α) (c' : Fin m → α)
    (s : Fin n → β) (s' : Fin m → β) :
    ∑ i, g (Fin.append c c' i) (Fin.append s s' i) = ∑ i, g (c i) (s i) + ∑ i, g (c' i) (s' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem expF_linear : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' t'' s s' s'' (c : F), U.ExpF F k t s → U.ExpF F k t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → (∀ α j, (s'' α).f j = DegPre.constBF D F c _ * (s α).f j + (s' α).f j) → U.ExpF F k t'' s'') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k t t' t'' s s' s'' c ⟨n, a, σ, f, h1, h2, h3⟩ ⟨m, a', σ', f', h1', h2', h3'⟩ ht hs
  refine ⟨n + m, Fin.append (fun i => c * a i) a', Fin.append σ σ', Fin.append f f', fun i => ?_,
    fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e z J hJ => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact h1 i
    · simp only [Fin.append_right]; exact h1' i
  · rw [sum_append (fun x y => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left x) * sval y rG z JG),
      ← h2' Z rA y rG e1 e2 z JA JG hA hG]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 Z rA y rG e1 e2 z JA JG hA hG,
      sval_comb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (scal (fst (TFK (R := V) F) A.A).left c) ht rA z hA]
    ring
  · rw [sum_append (fun x (y : ∀ α, SecBT D (𝟙_ _) k α) =>
      gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left x) * sval (y α) rB z J), ← h3' α Z rF rB e z J hJ]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 α Z rF rB e z J hJ]
    exact sval_comb (scal (fst (TF (R := V) F) D.P.A).left c) (hs α) rF z hJ

end GlobalTheory.UU.ExpLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntExp

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [gs_eq f (r z) U h, gs_eq (r ≫ f) z U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J) (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem gs_scal_one {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : Y ⟶ Spec (CommRingCat.of F)) :
    gs r z ⊤ (scal p (1 : F)) = 1 := by
  rw [gs_eq r z ⊤ trivial]
  simp only [scal, map_one]

theorem expF_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s := by
  intro R _ _ I D A G _ _ U F _ _ k σ f t s hE hG hB
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    rw [Fin.sum_univ_one]
    refine (hG Z rA y rG h₁ h₂ ?_ z JA JG hJA hJG).trans ?_
    · have e₁ : (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left = (snd (𝟙_ _) G).left ≫ G.hom := by
        have a := Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        have b := Over.w (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        exact ((Category.comp_id _).symm.trans a).trans b.symm
      have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
        have a := Over.w (toUnit (TF (R := R) F))
        exact (Category.comp_id _).symm.trans a
      have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
      calc rG ≫ (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left
          = (rG ≫ (snd (𝟙_ _) G).left) ≫ G.hom := by rw [e₁]; exact (Category.assoc _ _ _).symm
        _ = y ≫ pullback.fst G.hom (jK R) ≫ G.hom := by rw [h₂]; exact Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK R := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := R) F) A.A).left) ≫ A.A.hom ≫ jK R := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F) ≫ jK R := by rw [e₃]; simp only [Category.assoc]
        _ = _ := by rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
    · exact ((congrArg (· * _) (gs_scal_one rA z _)).trans (one_mul _)).symm
  · intro α Z rF rB h z J hJ
    rw [Fin.sum_univ_one]
    refine Eq.trans ?_ ((congrArg (· * _) (gs_scal_one rF z _)).trans (one_mul _)).symm
    have e : rB = rF ≫ (toUnit (TF (R := R) F) ▷ D.P.A).left := by
      have w : (toUnit (TF (R := R) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
        congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) D.P.A)
      have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left := by
        rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
      rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left, Category.assoc, w, h]
    rw [e, sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)), ← sval_comp (s α) _ rF z J hJ,
      Category.comp_id]

end GlobalTheory.UU.IntExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullBValues
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem pullB_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T₀ : Over (Spec (CommRingCat.of R))) (φ : TF (R := R) F ⟶ T₀) (k : ℕ) (f : ∀ α, SecBT D T₀ k α) (s : Raw D F k), PullB D F φ k f s → ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TF (R := R) F) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (s α) (lift ρ x).left z J = sval (f α) (lift (ρ ≫ φ) x).left z J := by
  intro R _ _ D F _ _ T₀ φ k f s h α T ρ x z J hJ
  have e : (lift ρ x).left ≫ (φ ▷ D.P.A).left = (lift (ρ ≫ φ) x).left := by
    rw [← Over.comp_left, lift_whiskerRight]
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) (lift ρ x).left z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left (lift ρ x).left z J hJ).2.1 (f α)
  have hJ' : Good D.P.L ((lift ρ x).left z) (fun ψ => J ((lift ρ x).left ≫ ψ)) := fun ψ => hJ _
  rw [e] at b
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

end GlobalTheory
end

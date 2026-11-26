module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelAmpleExt

theorem pw_pw' {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X)) (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ M : LB G.left, M.IsLB → Out.RelAmple A (M.pull φ) → Out.RelAmple G M := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ M hM hA
  have hAab : IsAbelianScheme A := by
    haveI := hG.comm
    have hcomm : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hcomm,
      MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hG.geomConnected⟩
  obtain ⟨d, hd, hex⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy L A (M.pull φ) (pull_isLB hM φ)).1 hA

  rw [← GlobalTheory.TrivLocus.pull_pw M φ (d : ℤ)] at hex
  obtain ⟨m, s, hs⟩ := hex
  set f := spMap (algebraMap W L) with hf
  set g := spMap (algebraMap L L) with hg
  have hg1 : g = 𝟙 _ := by
    simp [hg, spMap]
  haveI : IsIso g := by rw [hg1]; infer_instance
  have h1 : inv (pullback.fst A.hom g) ≫ pullback.snd A.hom g = A.hom := by
    rw [IsIso.inv_comp_eq, pullback.condition, hg1, Category.comp_id]
  let i : pullback G.hom f ≅ pullback A.hom g :=
    hφ.1.isoPullback.symm ≪≫ (asIso (pullback.fst A.hom g)).symm
  have hi : i.hom ≫ pullback.snd A.hom g = pullback.snd G.hom f := by
    simp only [i, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h1]
    exact hφ.1.isoPullback_inv_snd
  let e : (Over.pullback f).obj G ≅ (Over.pullback g).obj A := Over.isoMk i hi
  have he : e.hom.left ≫ pullback.fst A.hom g = hφ.1.isoPullback.inv := by
    simp [e, i]
  have hMd := GlobalTheory.AbLaw.isLB_pw hM (d : ℤ)
  obtain ⟨w, hw⟩ : LBIso ((GlobalTheory.AbLaw.pw M (d : ℤ)).pull (pullback.fst G.hom f))
      (((GlobalTheory.AbLaw.pw M (d : ℤ)).pull φ).pull (e.hom.left ≫ pullback.fst A.hom g)) :=
    LBIso.chartPull
      (chartPullSame (GlobalTheory.AbLaw.pw M (d : ℤ)) (fun _ : PUnit => pullback.fst G.hom f) (fun _ => φ) (fun _ => 1)
        (e.hom.left ≫ pullback.fst A.hom g) fun _ => by rw [he]; exact hφ.1.isoPullback_inv_fst.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) ⟨_, Geo.Tor.idIso_isGen (pull_isLB hMd φ)⟩
  obtain ⟨n, hn, hex2⟩ := GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic L W L A hAab G hG e
    ((GlobalTheory.AbLaw.pw M (d : ℤ)).pull φ) m s (GlobalTheory.AbLaw.pw M (d : ℤ)) w (pull_isLB hMd φ) hs hMd hw
  rw [pw_pw', show (d : ℤ) * (n : ℤ) = ((d * n : ℕ) : ℤ) by push_cast; rfl] at hex2
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy W G M hM).2 ⟨d * n, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
    (Nat.one_le_iff_ne_zero.1 hd) (Nat.one_le_iff_ne_zero.1 hn)), hex2⟩

end GlobalTheory.ModelAmpleExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DiagAmpleExt

theorem diag_comm {S S' : Scheme.{0}} {G : Over S} {A : Over S'} (φ : A.left ⟶ G.left)
    (φ₂ : (G2 A).left ⟶ (G2 G).left) (h : IsSquare φ φ₂) :
    φ ≫ (lift (𝟙 G) (𝟙 G)).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ := by
  apply pullback.hom_ext
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (fst G G).left
    rw [h.1, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (snd G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (snd G G).left
    rw [h.2, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]

theorem relAmple_diag_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hφ hsq P P' hP hP' e hA
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hG.proper
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
        gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  set dG := (lift (𝟙 G) (𝟙 G)).left
  set dA := (lift (𝟙 A) (𝟙 A)).left
  have hM : (P'.pull dG).IsLB := pull_isLB hP' _
  refine GlobalTheory.ModelAmpleExt.relAmple_of_generic W L G A φ hG hφ (P'.pull dG) hM ?_
  have i1 : LBIso ((P'.pull dG).pull φ) (P'.pull (φ ≫ dG)) :=
    GlobalTheory.OriginCohom.lbIso_pull_pull_comp hP' dG φ
  have i2 : LBIso (P'.pull (dA ≫ φ₂)) ((P'.pull φ₂).pull dA) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP' dA rfl
  have i3 : LBIso ((P'.pull φ₂).pull dA) (P.pull dA) :=
    GlobalTheory.GenSpread.lbIso_pullback e.symm dA
  rw [diag_comm φ φ₂ hsq] at i1
  have hφ2 := pull_isLB hP' φ₂
  have j : LBIso (P.pull dA) ((P'.pull dG).pull φ) :=
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP' _) (pull_isLB hP dA) i1 (LBIso.trans (pull_isLB hP' _)
      (pull_isLB hφ2 dA) (pull_isLB hP dA) i2 i3)).symm
  have hsq' : IsPullback (𝟙 A.left) A.hom A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hsq' (pull_isLB hP dA) (pull_isLB hM φ)
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP dA) (pull_isLB (pull_isLB hP dA) _) j.symm
      (GlobalTheory.GenSpread.lbIso_pull_pull hP (𝟙 _) (a := dA) (Category.id_comp _).symm)) hA

end GlobalTheory.DiagAmpleExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGenericStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_extendedBundle_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) := by
  first | exact @GlobalTheory.DiagAmpleExt.relAmple_diag_of_generic | exact GlobalTheory.DiagAmpleExt.relAmple_diag_of_generic | (intros; apply GlobalTheory.DiagAmpleExt.relAmple_diag_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem exists_centred_ext_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act _ 𝔗 z₂ hz V _ _ _ ev hV hev _
  subst hz

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ := (X₁.M.stalkHom (𝔗.p z₂)).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ (𝔗.p z₂)
  letI : Algebra (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := (𝔗.X₂.M.stalkHom z₂).toAlgebra
  obtain ⟨hdom₂, hfr₂, hic₂, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i 𝔗.X₂ z₂
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.Poinc.integralClosure_galois_finite_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom (𝔗.p z₂))).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdom; haveI := hfr; haveI := hic; haveI := hdom₂; haveI := hfr₂; haveI := hic₂
  haveI : Algebra.IsInvariant (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) :=
    ⟨fun b hb => hfix b hb⟩
  haveI : Module.Finite (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfin
  haveI : Finite (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfinA
  have hcard : Nat.card (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) = Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (galRestrict (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)).toEquiv).symm

  have hn1 : IsUnit ((X₁.ρ.n : ℕ) : X₁.o₁) := by
    have hu := X₁.S.unit
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [X₁.ρ.N_eq]
      exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self _ (by have := X₁.ρ.two_le; omega)) two_ne_zero) _
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hnA : IsUnit ((X₁.ρ.n : ℕ) : (X₁.M.Z.presheaf.stalk (𝔗.p z₂))) := by
    obtain ⟨u, hu⟩ := hn1
    have hm : algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) ∈ X₁.M.O (𝔗.p z₂) := Subalgebra.algebraMap_mem _ _
    refine IsUnit.of_mul_eq_one ((X₁.M.stalkEquiv _).symm ⟨_, hm⟩) (X₁.M.stalkHom_injective _ ?_)
    rw [map_mul, map_one, map_natCast, ← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    change ((X₁.ρ.n : ℕ) : X₁.Ω₁) * algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) = 1
    rw [← map_natCast (algebraMap X₁.o₁ X₁.Ω₁), ← hu, ← map_mul, Units.mul_inv, map_one]
  have hnV : IsUnit ((X₁.ρ.n : ℕ) : V) := by simpa using hnA.map ev
  have hdegV : IsUnit ((Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ : ℕ) : V) := by
    obtain ⟨e, he⟩ := 𝔗.deg
    rw [he, Nat.cast_pow]
    exact hnV.pow e

  haveI : CharZero V := hV.2.2.2
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨K', _, _, β, hK'fd, hK'dvd, hβ⟩ := GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) hinj (FractionRing V)
    ((algebraMap V (FractionRing V)).comp ev)
  haveI := hK'fd
  have hK'u : IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) := by
    rw [hcard] at hK'dvd
    obtain ⟨c, hc⟩ := hK'dvd
    rw [hc, Nat.cast_mul] at hdegV
    exact isUnit_of_mul_isUnit_left hdegV
  obtain ⟨V', _, _, _, io, j, hV', hioi, hiof, hiol, hcon, hjinj, hj, hjr⟩ := GlobalTheory.T.exists_complete_normal_integralClosure_unit_degree V hV K' hK'u
  have hβmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, β b ∈ j.range := by
    intro b
    obtain ⟨P, hPm, hP⟩ := integralClosure.isIntegral b
    obtain ⟨y, hy⟩ := hjr (β b) ⟨P.map ev, hPm.map ev, by
      rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hβ, ← Polynomial.hom_eval₂, hP, map_zero]⟩
    exact ⟨y, hy⟩
  let jr : V' ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hjinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let β' : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* V' := jr.symm.toRingHom.comp (β.codRestrict j.range hβmem)
  have hβ' : ∀ b, j (β' b) = β b := fun b => congrArg Subtype.val (jr.apply_symm_apply ⟨β b, hβmem b⟩)

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) := (𝔗.p.stalkMap z₂).hom.toAlgebra
  have hg1 : ∀ x : (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), 𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) :=
    fun x => (GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p 𝔗.p_pt z₂ x)
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq fun x => (hg1 x).symm
  have hinj₂ := 𝔗.X₂.M.stalkHom_injective z₂
  have hBmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, (b : 𝔗.X₂.Ω₁) ∈ (𝔗.X₂.M.stalkHom z₂).range := fun b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (𝔗.X₂.M.Z.presheaf.stalk z₂)) (K := 𝔗.X₂.Ω₁)).1
      (IsIntegral.tower_top (A := (𝔗.X₂.M.Z.presheaf.stalk z₂)) b.2)
    exact ⟨y, hy⟩
  let e₂ : (𝔗.X₂.M.Z.presheaf.stalk z₂) ≃+* (𝔗.X₂.M.stalkHom z₂).range := RingEquiv.ofBijective (𝔗.X₂.M.stalkHom z₂).rangeRestrict
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), (𝔗.X₂.M.stalkHom z₂).rangeRestrict_surjective⟩
  let f : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* (𝔗.X₂.M.Z.presheaf.stalk z₂) :=
    e₂.symm.toRingHom.comp (((integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁).val : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] 𝔗.X₂.Ω₁).toRingHom.codRestrict _ hBmem)
  have hf : ∀ b, 𝔗.X₂.M.stalkHom z₂ (f b) = b := fun b => congrArg Subtype.val (e₂.apply_symm_apply ⟨_, hBmem b⟩)
  have hfB : ∀ (t : (𝔗.X₂.M.Z.presheaf.stalk z₂)) (h : 𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁), f ⟨_, h⟩ = t :=
    fun t h => hinj₂ (hf _)
  have hloc : IsLocalHom (f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁))) := by
    have h : f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = (𝔗.p.stalkMap z₂).hom :=
      RingHom.ext fun a => hinj₂ (by rw [RingHom.comp_apply, hf, hg1]; rfl)
    rw [h]; infer_instance
  have hint : ∀ t : (𝔗.X₂.M.Z.presheaf.stalk z₂), (∃ P : Polynomial (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), P.Monic ∧ P.eval₂ (𝔗.p.stalkMap z₂).hom t = 0) →
      𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := by
    rintro t ⟨P, hPm, hP⟩
    refine ⟨P, hPm, ?_⟩
    have h : algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ = (𝔗.X₂.M.stalkHom z₂).comp (𝔗.p.stalkMap z₂).hom := RingHom.ext fun x => (hg1 x).symm
    rw [h, ← Polynomial.hom_eval₂, hP, map_zero]
  have hsurj : ∀ y : (𝔗.X₂.M.Z.presheaf.stalk z₂), ∃ b s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ y * f s = f b := by
    intro y
    obtain ⟨b, s, hs, hys, hb, hs'⟩ := GlobalTheory.T.finite_stalk_germ_quotient_integral_unit_denominator _ _ 𝔗.p 𝔗.p_fin z₂ y
    refine ⟨⟨_, hint b hb⟩, ⟨_, hint s hs'⟩, ?_, ?_⟩
    · rw [hfB]; exact hs
    · rw [hfB, hfB]; exact hys
  have hker : ∀ b, f b = 0 → ∃ s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ s * b = 0 := fun b hb =>
    ⟨1, by rw [map_one]; exact isUnit_one, by
      rw [_root_.one_mul]; exact Subtype.ext (by rw [← hf b, hb, map_zero]; rfl)⟩
  haveI := hiol; haveI := hev
  have hβ'A : β'.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = io.comp ev := RingHom.ext fun a =>
    hjinj ((hβ' _).trans ((RingHom.congr_fun hβ a).trans (RingHom.congr_fun hj (ev a)).symm))
  obtain ⟨ev₂, hev₂, hcomp⟩ := GlobalTheory.T.twisted_lift_invariantExtension_localisation (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (𝔗.X₂.M.Z.presheaf.stalk z₂)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) f hloc hsurj hker V' (io.comp ev) β' inferInstance hβ'A
  refine ⟨V', inferInstance, inferInstance, inferInstance, io, ev₂, hV', hioi, hiof, hiol, hcon, hev₂, fun x x₂ hx => ?_⟩
  have h : x₂ = f (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) x) := hinj₂ (by rw [hf]; exact hx)
  rw [h]
  exact RingHom.congr_fun hcomp x

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.exists_centred_ext_tower | exact GlobalTheory.Poinc.Sep.exists_centred_ext_tower | (intros; apply GlobalTheory.Poinc.Sep.exists_centred_ext_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureLowerTriangularPositiveDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureLowerTriangularPositiveDiagonal
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem conn_lowerTriangular {n s : ℕ} {T : V n → Matrix (Fin s) (Fin s) ℂ} {x : V n}
    (h0 : ∀ᶠ y in 𝓝 x, ∀ i j, i < j → T y i j = 0) (hd : ∀ i, T x i i ≠ 0) (ξ : V n) :
    (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
  have hT : (T x)ᵀ.BlockTriangular id := fun i j hij => h0.self_of_nhds j i hij
  have hu' : IsUnit (T x)ᵀ.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have hu : IsUnit (T x).det := by rwa [Matrix.det_transpose] at hu'
  have hD : (mdel T x ξ)ᵀ.BlockTriangular id := fun i j hij => by
    rw [Matrix.transpose_apply, mdel_apply,
      del_congr (g := fun _ => (0 : ℂ)) (h0.mono fun y hy => hy j i hij)]
    simp
  letI := Matrix.invertibleOfIsUnitDet _ hu'
  have hc : (conn T x ξ).BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular hT).mul hD
  refine ⟨fun i j hij => hc hij, fun i => ?_⟩
  have h := congrFun (congrFun (transpose_mul_conn hu ξ) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.transpose_apply, Matrix.transpose_apply,
    mdel_apply] at h
  · rw [← h, inv_mul_cancel_left₀ (hd i)]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hT (show id k < id i from hk), zero_mul]
    · rw [hc (show id i < id k from hk), mul_zero]
  · simp

theorem curv_lowerTriangular : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  intro n s T d v hT hd he ξ η
  have h0 : ∀ᶠ y in 𝓝 v, ∀ i j, i < j → T y i j = 0 := he.mono fun _ h => h.1
  have hv : ∀ i, T v i i ≠ 0 := fun i => by
    rw [he.self_of_nhds.2 i]; exact_mod_cast (hd i).ne'
  have hne : ∀ᶠ y in 𝓝 v, ∀ i, T y i i ≠ 0 :=
    eventually_all.2 fun i => (hT i i).continuousAt.eventually_ne (hv i)
  have hc : ∀ᶠ x in 𝓝 v, (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
    filter_upwards [h0.eventually_nhds, hne] with x h1 h2
    exact conn_lowerTriangular h1 h2 ξ
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [curv, Matrix.neg_apply, mdbar_apply,
      dbar_congr (g := fun _ => (0 : ℂ)) (hc.mono fun y hy => hy.1 i j hij)]
    simp
  · let H : V n → Matrix (Fin 1) (Fin 1) ℂ := fun x => Matrix.of fun _ _ => T x i i
    have hH : ∀ᶠ x in 𝓝 v, conn T x ξ i i = conn H x ξ 0 0 := by
      filter_upwards [hc, hne] with x h1 h2
      rw [h1.2 i, (conn_lowerTriangular (T := H)
        (Eventually.of_forall fun _ a b hab => absurd (Subsingleton.elim a b) hab.ne)
        (fun _ => h2 i) ξ).2 0]
      rfl
    have hs : ContDiffAt ℝ 2 (d i) v := by
      have h1 : ContDiffAt ℝ 2 (fun x => (T x i i).re) v :=
        Complex.reCLM.contDiff.contDiffAt.comp v ((hT i i).of_le (by norm_cast))
      refine h1.congr_of_eventuallyEq (he.mono fun x hx => ?_)
      simp [hx.2 i]
    rw [← curv_line (H := H) hs (hd i).ne' (he.mono fun x hx => hx.2 i) ξ η 0 0, curv, curv,
      Matrix.neg_apply, Matrix.neg_apply, mdbar_apply, mdbar_apply, dbar_congr hH]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureLowerTriangularPositiveDiagonalStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_lowerTriangular_positive_diagonal : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  first | exact @GlobalTheory.ChernCalc.curv_lowerTriangular | exact GlobalTheory.ChernCalc.curv_lowerTriangular | (intros; apply GlobalTheory.ChernCalc.curv_lowerTriangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernForms
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTri

theorem coeff_charpolyRev_neg_of_tri {R : Type} [CommRing R] {s : ℕ} (F : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, j < i → F i j = 0) (k : ℕ) :
    (Matrix.charpolyRev (-F)).coeff k = ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, F i i := by
  rw [Matrix.charpolyRev, Matrix.det_of_upperTriangular]
  · have e : ∀ i, ((1 : Matrix (Fin s) (Fin s) (Polynomial R)) -
        (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) i i = 1 + Polynomial.C (F i i) * Polynomial.X := by
      intro i
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, smul_eq_mul,
        mul_neg, sub_neg_eq_add, mul_comm]
    simp only [e]
    rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, Polynomial.coeff_C_mul_X_pow]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp [eq_comm]
  · intro i j hij
    have hij' : j < i := hij
    simp [h i j hij', hij'.ne']

theorem chernAt_tri : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ j, chernAt T v j = aeval (fun i => ofValues (ddc (fun x => -Real.log (d i x)) v)) (esymm (Fin s) ℂ j) := by
  intro n s T d v hT hd htri j
  have key := GlobalTheory.T.chernCurvature_lowerTriangular_positive_diagonal n s T d v hT hd htri
  rw [chernAt, chernPoly, coeff_charpolyRev_neg_of_tri _ (fun a b hab => by
    simp [curvPoly, fun ξ η => (key ξ η).1 a b hab]), esymm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod, aeval_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have e (i : Fin s) : ofValues (ddc (fun x => -Real.log (d i x)) v) =
      kappa • (aeval sym (curvPoly T v i i) : Ev n) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ofValues, ddc, curvPoly, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X, Finset.smul_sum,
      fun ξ η => (key ξ η).2 i, leviForm_neg, ← Algebra.smul_def, smul_smul, ContinuousLinearMap.neg_apply]
  simp only [e]
  rw [Finset.prod_smul, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

end GlobalTheory.ChernTri
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernFormsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ j, chernAt T v j = aeval (fun i => ofValues (ddc (fun x => -Real.log (d i x)) v)) (esymm (Fin s) ℂ j) := by
  first | exact @GlobalTheory.ChernTri.chernAt_tri | exact GlobalTheory.ChernTri.chernAt_tri | (intros; apply GlobalTheory.ChernTri.chernAt_tri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbar
set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory.CxForm GlobalTheory.GoodMetric GlobalTheory.CxForm.DensPow GlobalTheory.GrassModel GlobalTheory.GrassModel.TopRead

namespace GlobalTheory.ChernCalc.DensTop

variable {n : ℕ}

theorem bas_mul_smul (S T : Finset (Fin (n + n))) : ∃ c : ℂ, bas n S * bas n T = c • bas n (S ∪ T) := by
  by_cases h : Disjoint S T
  · obtain ⟨ε, e⟩ := bas_mul h
    exact ⟨_, by rw [e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]⟩
  · have := ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
      (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
    have e : bas n S * bas n T = 0 := this
    exact ⟨0, by rw [e, zero_smul]⟩

theorem prod_sym_eq {ι : Type} [DecidableEq ι] (x : ι → Fin n × Fin n) (s : Finset ι) :
    ∃ (c : ℂ) (S : Finset (Fin (n + n))), S.card ≤ 2 * s.card ∧ ((∏ j ∈ s, sym (x j) : Ev n) : Alt n) = c • bas n S := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, ∅, by simp, by simp [bas_empty]⟩
  | insert a s ha ih =>
    obtain ⟨c, S, hS, e⟩ := ih
    obtain ⟨c₁, h₁⟩ := bas_mul_smul {finSumFinEquiv (.inl (x a).1)} {finSumFinEquiv (.inr (x a).2)}
    obtain ⟨c₂, h₂⟩ := bas_mul_smul ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) S
    refine ⟨c₁ * c * c₂, ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) ∪ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le ({finSumFinEquiv (.inl (x a).1)} : Finset (Fin (n + n)))
        {finSumFinEquiv (.inr (x a).2)}
      rw [Finset.card_singleton, Finset.card_singleton] at this
      omega
    · rw [Finset.prod_insert ha, Subalgebra.coe_mul, e,
        show (sym (x a) : Alt n) = dz (x a).1 * dzb (x a).2 from rfl, dz, dzb, ← bas_singleton,
        ← bas_singleton, h₁, smul_mul_smul_comm, h₂, smul_smul]

theorem prod_sym_not_inj {m : ℕ} (x : Fin m → Fin n × Fin n) (h : ¬ Function.Injective fun j => (x j).1) :
    (∏ j, sym (x j) : Ev n) = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  have h0 : sym (x i) * sym (x j) = 0 := by
    apply Subtype.ext
    change dz (x i).1 * dzb (x i).2 * (dz (x j).1 * dzb (x j).2) = 0
    rw [hij]
    exact ι_mul_ι_mul_ι_mul_ι_left _ _ _
  rw [← Finset.mul_prod_erase Finset.univ (fun a => sym (x a)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => sym (x a))
      (Finset.mem_erase.2 ⟨fun e => hne e.symm, Finset.mem_univ j⟩), ← mul_assoc, h0, zero_mul]

theorem dens_zero' : dens (0 : Alt n) = 0 := by simp [dens]

theorem dens_add' (x y : Alt n) : dens (x + y) = dens x + dens y := by simp [dens, add_div]

theorem dens_prod_diag : dens ((∏ a, sym (a, a) : Ev n) : Alt n) = ((Complex.I / 2) ^ n)⁻¹ := by
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dens_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    dens ((∏ j, sym (x j) : Ev n) : Alt n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) /
        (Complex.I / 2) ^ n := by
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero, zero_div]
    rcases lt_or_gt_of_ne hm with h | h
    · obtain ⟨c, S, hS, e⟩ := prod_sym_eq x Finset.univ
      have hne : S ≠ Finset.univ := by
        rintro rfl
        simp at hS
        omega
      rw [e]
      simp [dens, Finsupp.single_apply, hne]
    · rw [prod_sym_not_inj x, Subalgebra.coe_zero, dens_zero']
      intro hi
      have := Fintype.card_le_of_injective _ hi
      simp at this
      omega
  subst hm
  rw [topForm_self, topForm_self]
  by_cases ha : Function.Injective fun j => (x j).1
  swap
  · rw [prod_sym_not_inj x ha, Subalgebra.coe_zero, dens_zero', det_single_not_inj _ ha, zero_mul, zero_div]
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp ha)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have e1 : (∏ j, sym (x j) : Ev m) = ∏ c, row c (Pi.single (x (π.symm c)).2 1) := by
    rw [← Equiv.prod_comp π fun c => row c (Pi.single (x (π.symm c)).2 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Equiv.symm_apply_apply, ← hπ]
    simp [row, Pi.single_apply]
  have e2 := prod_row (n := m) (Matrix.of fun c => Pi.single (x (π.symm c)).2 1)
  have e3 : (Matrix.of fun c => (Pi.single (x (π.symm c)).2 1 : Fin m → ℂ)).det =
      (Pi.basisFun ℂ (Fin m)).det ((fun j => Pi.single (x j).2 1) ∘ π.symm) := by
    rw [Pi.basisFun_det]; rfl
  rw [e1]
  refine (congrArg (fun z : Ev m => dens (z : Alt m)) e2).trans ?_
  simp only [hπ, det_single_perm]
  rw [Subalgebra.coe_smul, dens_smul, dens_prod_diag, e3, AlternatingMap.map_perm, Equiv.Perm.sign_symm,
    Units.smul_def, zsmul_eq_mul, ← div_eq_mul_inv]

theorem dens_aeval_sym (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, dens_smul, map_prod]
    simp only [aeval_X]
    rw [dens_prod, ← topCoeff_prod, ← mul_div_assoc]
    congr 1
    unfold topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add (f := _), Subalgebra.coe_add, dens_add', hp, hq, ← add_div]
    congr 1
    unfold topCoeff
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.ChernCalc.DensTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbarStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  first | exact @GlobalTheory.ChernCalc.DensTop.dens_aeval_sym | exact GlobalTheory.ChernCalc.DensTop.dens_aeval_sym | (intros; apply GlobalTheory.ChernCalc.DensTop.dens_aeval_sym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem exists_embed_integral {V W K : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Field K]
    [IsAlgClosed K] (g : V →+* W) (hg : g.IsIntegral) (hgi : Function.Injective g) (j : V →+* K)
    (hj : Function.Injective j) : ∃ j' : W →+* K, j'.comp g = j ∧ Function.Injective j' := by
  letI := g.toAlgebra
  letI := j.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨hg⟩
  haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hgi
  haveI : Module.IsTorsionFree V K := Module.isTorsionFree_iff_algebraMap_injective.2 hj
  let f : W →ₐ[V] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hc : f.toRingHom.comp (algebraMap V W) = j := RingHom.ext fun a => f.commutes a
  refine ⟨f.toRingHom, hc, ?_⟩
  have hk : (RingHom.ker f.toRingHom).comap (algebraMap V W) = ⊥ := by
    rw [RingHom.comap_ker, hc]
    exact (RingHom.injective_iff_ker_eq_bot j).1 hj
  exact (RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot hk)

theorem prim_descend {V W K K' : Type} [CommRing V] [CommRing W] [Field K] [Field K'] (g : V →+* W)
    (hg : g.IsIntegral) (i : V →+* K) (k : K →+* K') (i' : W →+* K') (h : i'.comp g = k.comp i) {J : Type}
    (c : J → K) (hp : Prim i' (fun a => k (c a))) : Prim i c := by
  have up : ∀ x : K', i'.IsIntegralElem x → (k.comp i).IsIntegralElem x := by
    intro x hx
    letI := g.toAlgebra
    letI := i'.toAlgebra
    letI := (k.comp i).toAlgebra
    haveI : Algebra.IsIntegral V W := ⟨hg⟩
    haveI : IsScalarTower V W K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun h a).symm
    exact isIntegral_trans (R := V) (A := W) x hx
  have down : ∀ y : K, (k.comp i).IsIntegralElem (k y) → i.IsIntegralElem y := by
    rintro y ⟨p, hm, he⟩
    refine ⟨p, hm, k.injective ?_⟩
    rw [map_zero, Polynomial.hom_eval₂]
    exact he
  refine ⟨fun a => down _ (up _ (hp.1 a)), ?_⟩
  obtain ⟨a, ha, hinv⟩ := hp.2
  refine ⟨a, fun e => ha (by simp [e]), down _ ?_⟩
  rw [map_inv₀]
  exact up _ hinv

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (g : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hc, hL⟩ := h
  have g₁ := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left,
      ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ :=
    hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ) :=
    (GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm
  have hq := amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L
    (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩

theorem thList_move {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {T : Over S} (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    (h₁ : Over.mk x₁ ⟶ T) (h₂ : Over.mk x₂ ⟶ T) (hl : h₁.left = h₂.left) {N : ℕ} (pt : Fin N → (Over.mk x₁ ⟶ G))
    (c : Fin N → K) (hT : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ s) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ s) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext hl
  exact ⟨pt, hT⟩

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem prim_of_polFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S), PolFib t.G t.PP.L g (jK V ≫ χ) → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t g V _ _ _ hV χ hpf σ hσ m N hm hm3 hmu K _ i pt c hi hT
  obtain ⟨hd, hc, h0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  haveI := hd
  haveI := h0
  obtain ⟨t₁, ⟨m₁⟩⟩ : ∃ t₁ : SAB H (Sp V), Nonempty (SABMap t₁ t χ) := by
    obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, m', -⟩ := sabPull Out.CubePf.cubePull χ t
    exact ⟨_, ⟨m'⟩⟩
  obtain ⟨W, _, _, _, _, gW, hcW, hgi, hginj, hgl, Ex, hEx⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hc t₁.G t₁.semi
  obtain ⟨t₂, m₂, hS⟩ : ∃ (t₂ : SAB H (Sp W)) (_ : SABMap t₂ t₁ (spMap gW)),
      ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t₂.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m', -⟩ := sabPull Out.CubePf.cubePull (spMap gW) t₁
    exact ⟨_, m', Ex, hEx⟩
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
  have hp0 : GlobalTheory.LN.PolAt t (jK V ≫ χ) := polAt_of_polFib t g _ hpf
  have hp1 := GlobalTheory.DatUniq.polAt_pull m₁ hp0 (jK V) (𝟙 _) (Category.id_comp _)
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp gW) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  let gam : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg' : ∀ r, gam (algebraMap _ _ r) = algebraMap W _ (gW r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value gam
  have hgam : spMap gam ≫ jK V = jK W ≫ spMap gW := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg'))
  have hp2 := GlobalTheory.DatUniq.polAt_pull m₂ hp1 (jK W) (spMap gam) hgam
  have hW : GlobalTheory.LN.CDvr W := (GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hcW, inferInstance⟩
  obtain ⟨U, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t₂ hp2 hS
  have hσ' := nz_pull S t.G t.PP.L t.PP.isLB t.semi V W χ σ gW hσ
  have hmuW : IsUnit (m : W) := by simpa using hmu.map gW
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨i', hi'c, hi'⟩ := exists_embed_integral gW hgi hginj (k.comp i) (k.injective.comp hi)
  obtain ⟨pt₁, -, hT₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K (AlgebraicClosure K) k
    (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c hT
  let a₁ : Over.mk (spMap k ≫ spMap i ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (spMap k) rfl
  let a₂ : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let b₁ : Over.mk (spMap i' ≫ spMap gW ≫ χ) ⟶ Over.mk (spMap gW ≫ χ) := Over.homMk (spMap i') rfl
  let b₂ : Over.mk (spMap gW ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap gW) rfl
  have e₁ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) k = VVRank.pullS t.G _ (a₁ ≫ a₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have e₂ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ gW) i' = VVRank.pullS t.G _ (b₁ ≫ b₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have hx : spMap i' ≫ spMap gW = spMap k ≫ spMap i := by
    rw [spMap_comp_eq', spMap_comp_eq', hi'c]
  rw [e₁] at hT₁
  obtain ⟨pt₂, hT₂⟩ := thList_move t.G t.PP.L t.PP.rig m σ (by rw [← Category.assoc, ← hx, Category.assoc])
    (a₁ ≫ a₂) (b₁ ≫ b₂) (by simp [a₁, a₂, b₁, b₂, hx]) pt₁ _ hT₁
  rw [← e₂] at hT₂
  exact prim_descend gW hgi i k i' hi'c c
    (GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H S t W hW (spMap gW ≫ χ) t₂ ⟨n⟩ ⟨U⟩ _ hσ' m N hm hm3 hmuW _ i' pt₂ _ hi' hT₂)

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_primitive_principallyPolarised_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S), PolFib t.G t.PP.L g (jK V ≫ χ) → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  first | exact @GlobalTheory.UMin.prim_of_polFib | exact GlobalTheory.UMin.prim_of_polFib | (intros; apply GlobalTheory.UMin.prim_of_polFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubst
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem semiHom_constantCoeff_and_ev : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, (s.app 0).counit_map, c.aug, map_zero]
  refine ⟨hconst, fun n g => ?_⟩
  have hy : ∀ j, IsNilpotent (s.app n (c.x n j)) := fun j => (c.nil n j).map (s.app n).toRingHom
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k' (Fin d) (G'.A n)).1 (Fin e) (c'.ev n)
    (fun t => by
      change IsNilpotent (evA k' (c'.x n) (c'.nil n) (X t))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c'.nil n t) φ hconst _ hy (fun j => hφ n j) (MvPowerSeries.map σ g)
  rw [h1]
  letI : Algebra k (G'.A n) := ((algebraMap k' (G'.A n)).comp σ).toAlgebra
  let S : G.A n →ₐ[k] G'.A n :=
    { (s.app n).toRingHom with commutes' := fun r => (s.app n).map_algebraMap r }
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G'.A n) S (c.x n) (c.nil n) _ hy (fun _ => rfl) g
  change _ = S (evA k (c.x n) (c.nil n) g)
  rw [h2]
  let M : MvPowerSeries (Fin d) k →ₐ[k] G'.A n :=
    { (evA k' _ hy : MvPowerSeries (Fin d) k' →+* G'.A n).comp (MvPowerSeries.map σ) with
      commutes' := fun r => by
        change evA k' _ hy (MvPowerSeries.map σ (algebraMap k _ r)) = algebraMap k' _ (σ r)
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.map_C, ← (evA k' _ hy).commutes (σ r), MvPowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  have hM : M = evA k _ hy := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) (G'.A n) M _
    (fun i => by
      change IsNilpotent (evA k' _ hy (MvPowerSeries.map σ (X i)))
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact hy i)
    (fun i => by
      change evA k' _ hy (MvPowerSeries.map σ (X i)) = _
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate])
  exact AlgHom.congr_fun hM g

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubstStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  first | exact @GlobalTheory.Katz.semiHom_constantCoeff_and_ev | exact GlobalTheory.Katz.semiHom_constantCoeff_and_ev | (intros; apply GlobalTheory.Katz.semiHom_constantCoeff_and_ev <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8FibrationAlgebraicallyClosedField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementCoefficientFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSpecializationField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpEighthPowerRelativeDimensionEqEightMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpEighthPowerRelativeDimensionEqEightMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharpRef_relDim : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  intro W V V₁ _ _ _ _ Q ρ D e h
  obtain ⟨pr, w, hmon, huniv, -⟩ := h
  have lim : IsLimit (Fan.mk D.P.A pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose)
      (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).unique hm (huniv s.pt s.proj).choose_spec.1)
  let eI : D.P.A ≅ powObj ((Over.pullback (spMap ρ)).obj Q.B) 8 :=
    lim.conePointUniqueUpToIso (powIsLimit _ 8)
  have hB : SmoothOfRelativeDimension Q.g ((Over.pullback (spMap ρ)).obj Q.B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback Q.B.hom (spMap ρ)) Q.smoothDim
  have h8 := GlobalTheory.smoothOfRelativeDimension_powObj _ Q.g hB 8
  have hne : Nonempty (Sp V₁) := inferInstance
  exact GlobalTheory.relDim_unique_of_iso_grp (Sp V₁) hne D.P.A _ eI.hom inferInstance _ _ D.P.smoothDim h8

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpEighthPowerRelativeDimensionEqEightMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  first | exact @GlobalTheory.Poinc.Sep.sharpRef_relDim | exact GlobalTheory.Poinc.Sep.sharpRef_relDim | (intros; apply GlobalTheory.Poinc.Sep.sharpRef_relDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isProd_pullback_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  intro S S' f A B _ _ pr hpr P _ i hi
  obtain ⟨hmon, huniv⟩ := hpr
  refine ⟨fun a => ?_, fun T y => ?_⟩
  · haveI := hmon a
    infer_instance
  · let adj := Over.mapPullbackAdj f
    obtain ⟨x', hx', hu⟩ := huniv ((Over.map f).obj T) (fun a => (adj.homEquiv T B).symm (y a))
    refine ⟨adj.homEquiv T A x' ≫ i.hom, fun a => ?_, fun x hx => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Adjunction.homEquiv_naturality_right, hx' a, Equiv.apply_symm_apply]
    · have h1 : (adj.homEquiv T A).symm (x ≫ i.inv) = x' := by
        apply hu
        intro a
        rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, hx a]
      rw [← h1, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerProjections_baseChange_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso | exact GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isPPFib_baseChange : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (g : ℕ) (M : RigLB G), E8Fibration.IsPPFib G g M → ∃ M' : RigLB ((Over.pullback f).obj G), M'.L = M.L.pull (pullback.fst G.hom f) ∧ E8Fibration.IsPPFib ((Over.pullback f).obj G) g M' := by
  intro S S' f G _ g M hM
  obtain ⟨hA, hg, ⟨c⟩, ha, hK⟩ := hM
  have hA' : IsAbelianScheme ((Over.pullback f).obj G) := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · change Smooth (pullback.snd G.hom f)
      infer_instance
    · change IsProper (pullback.snd G.hom f)
      infer_instance
    · change GeometricallyConnected (pullback.snd G.hom f)
      infer_instance
  have := hA.comm
  have := hA'.comm
  have := hA.proper
  have h := isGrpPullback_pullback G f
  obtain ⟨hL, hr, c', -⟩ := GlobalTheory.PullSharp.cube_pull_sharp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h) M c
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hL
  exact ⟨(ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h).rigLB M hL hr, rfl, hA',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hg, ⟨c'⟩,
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback M.isLB ha h.1,
    kTriv_pull h M.isLB hL ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principallyPolarisedFibre_baseChange : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (g : ℕ) (M : RigLB G), E8Fibration.IsPPFib G g M → ∃ M' : RigLB ((Over.pullback f).obj G), M'.L = M.L.pull (pullback.fst G.hom f) ∧ E8Fibration.IsPPFib ((Over.pullback f).obj G) g M' := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.isPPFib_baseChange | exact GlobalTheory.Poinc.Sep.E8Fibration.isPPFib_baseChange | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.isPPFib_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSpecializationField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem lamPts_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (hB : IsGrpPullback B' B f φ) {T' : Over S'} {T : Over S} (h : Over.mk (T'.hom ≫ f) ⟶ T)
    (x' y' : T' ⟶ B') (x y : T ⟶ B) (hx : x'.left ≫ φ = h.left ≫ x.left) (hy : y'.left ≫ φ = h.left ≫ y.left)
    (k : Fin 4) : lamPts x' y' k ≫ φ = h.left ≫ lamPts x y k := by
  fin_cases k
  · have e := hB.2 T' x' y' (h ≫ x) (h ≫ y) (by rw [Over.comp_left, hx]) (by rw [Over.comp_left, hy])
    show (x' * y').left ≫ φ = h.left ≫ (x * y).left
    rw [← e, ← MonObj.comp_mul, Over.comp_left]
  · exact hx
  · exact hy
  · show (1 : T' ⟶ B').left ≫ φ = h.left ≫ (1 : T ⟶ B).left
    have e := hB.2 T' 1 1 (pushPt hB.1.w 1) (pushPt hB.1.w 1) rfl rfl
    rw [_root_.mul_one] at e
    have e1 : pushPt hB.1.w (1 : T' ⟶ B') = 1 := by
      have : pushPt hB.1.w (1 : T' ⟶ B') * pushPt hB.1.w 1 = pushPt hB.1.w 1 := Over.OverMorphism.ext e
      exact mul_eq_left.1 this
    have e2 : (pushPt hB.1.w (1 : T' ⟶ B')).left = (1 : T' ⟶ B').left ≫ φ := rfl
    rw [← e2, e1, ← Over.comp_left, MonObj.comp_one]

theorem fibre_exists : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (gQ : ℕ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]
  (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (K : Type) [Field K] (ev : V₁ →+* K),
  ∃ (P' : PolAV (Sp K)) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ P'.A.left) (B : Over (Sp K)) (_ : GrpObj B)
    (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
    P'.g = 8 * gQ ∧ IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) P'.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (P'.L.pull ψ) ∧
    E8Fibration.IsPPFib B gQ M ∧ E8Fibration.IsProd pr ∧ E8Fibration.IsE8WeightedBundle W pr P'.L M.L ∧
    ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ n = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ y' : Out.baseOver (Sp K) ⟶ P'.A, y'.left = q ≫ ψ ∧ y' ^ n = 1 := by
  intro W gQ V V₁ _ _ _ _ Q hQ ρ hρ D e hS K _ ev
  have hS' := hS
  obtain ⟨pr₀, w, hmon, huniv, hw, -, -⟩ := hS'
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap ev) D.P
  have hgp : IsGrpPullback P'.A D.P.A (spMap ev) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap ev)) hgp
  haveI := hi
  have hinv : i.inv.left ≫ pullback.fst D.P.A.hom (spMap ev) = φ := by
    rw [← hiφ, ← Category.assoc, ← Over.comp_left, i.inv_hom_id, Over.id_left, Category.id_comp]

  have hQP : IsPPFib Q.B Q.g Q.M := ⟨Q.isAb, Q.smoothDim, ⟨Q.cub⟩, Q.ample, Q.ktriv⟩
  obtain ⟨M₁, hM₁, hP₁⟩ := GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ρ) Q.B Q.g Q.M hQP
  obtain ⟨M, hM, hP⟩ := GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ev) _ Q.g M₁ hP₁
  let B₁ := (Over.pullback (spMap ρ)).obj Q.B
  let pr : Fin 8 → (P'.A ⟶ (Over.pullback (spMap ev)).obj B₁) :=
    fun a => i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)
  have hpr : IsProd pr := GlobalTheory.T.eighthPowerProjections_baseChange_iso (spMap ev) pr₀ ⟨hmon, huniv⟩ P'.A i hi
  refine ⟨P', i.hom.left, (Over.pullback (spMap ev)).obj B₁, inferInstance, M, pr, ?_, isGrpPullback_of_iso i, ?_,
    hQ ▸ hP, hpr, ?_, ?_⟩
  · rw [hg, GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul W V V₁ Q ρ D e hS, hQ]
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    exact LBIso.trans (LB.isLB_pull D.P.isLB _) (LB.isLB_pull (LB.isLB_pull D.P.isLB _) _) (LB.isLB_pull P'.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull D.P.isLB i.hom.left hiφ.symm) (GlobalTheory.GenSpread.lbIso_pullback ht' i.hom.left)
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    have H : LBIso M.L (Q.M.L.pull (pullback.fst B₁.hom (spMap ev) ≫ pullback.fst Q.B.hom (spMap ρ))) := by
      rw [hM, hM₁]
      exact LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull Q.M.isLB _ rfl)
    have hx : ∀ a, (pr a).left ≫ pullback.fst B₁.hom (spMap ev) = φ ≫ (pr₀ a).left := fun a => by
      show (i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)).left ≫ _ = _
      rw [Over.comp_left, Category.assoc]
      have hp : ((Over.pullback (spMap ev)).map (pr₀ a)).left ≫ pullback.fst B₁.hom (spMap ev) =
          pullback.fst D.P.A.hom (spMap ev) ≫ (pr₀ a).left := pullback.lift_fst _ _ _
      rw [hp, ← Category.assoc, hinv]
    have ha := GlobalTheory.ShapePull.iso_linComb_pull H (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2)
      (fun k => lamPts (pr₀ k.1.1) (pr₀ k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)) φ
      (fun k => by
        rw [← Category.assoc, lamPts_pull (isGrpPullback_pullback B₁ (spMap ev)) (Over.homMk φ hφ.w) (pr k.1.1) (pr k.1.2)
          (pr₀ k.1.1) (pr₀ k.1.2) (hx _) (hx _) k.2, Category.assoc]
        rfl)
    have hb := GlobalTheory.GenSpread.lbIso_pullback (⟨w, hw⟩ : LBIso D.P.L _) φ
    exact LBIso.trans P'.isLB (LB.isLB_pull D.P.isLB _) (LB.isLB_linComb M.isLB _ _) (LBIso.symm ht')
      (LBIso.trans (LB.isLB_pull D.P.isLB _) (LB.isLB_pull (LB.isLB_linComb Q.M.isLB _ _) _) (LB.isLB_linComb M.isLB _ _)
        hb (LBIso.symm ha))
  · intro n y hy q hq1 hq2
    have hw' : (q ≫ i.hom.left) ≫ P'.A.hom = (baseOver (Sp K)).hom := by
      rw [Category.assoc, Over.w i.hom]
      exact hq2
    refine ⟨Over.homMk (q ≫ i.hom.left) hw', rfl, ?_⟩
    rw [← GlobalTheory.Raynaud.pow_eq_one_iff_of_isGrpPullback hgp]
    let c : Over.mk (spMap ev) ⟶ Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) := Over.homMk (𝟙 _) (by simp)
    let c' : Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) ⟶ Over.mk (spMap ev) := Over.homMk (𝟙 _) (by simp)
    have hcc : c' ≫ c = 𝟙 _ := by ext; simp [c, c']
    have hy' : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) = y := by
      ext
      show 𝟙 _ ≫ (q ≫ i.hom.left) ≫ φ = y.left
      rw [Category.id_comp, Category.assoc, hiφ, hq1]
    have h1 : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) ^ n = 1 := by
      rw [MonObj.comp_pow, hy', hy]
    have h2 := congrArg (c' ≫ ·) h1
    simp only [← Category.assoc, hcc, Category.id_comp, MonObj.comp_one] at h2
    exact h2

end GlobalTheory.Poinc.Sep.E8Fibration
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSpecializationFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarized_specialization_field : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (gQ : ℕ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]
  (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (K : Type) [Field K] (ev : V₁ →+* K),
  ∃ (P' : PolAV (Sp K)) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ P'.A.left) (B : Over (Sp K)) (_ : GrpObj B)
    (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
    P'.g = 8 * gQ ∧ IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) P'.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (P'.L.pull ψ) ∧
    E8Fibration.IsPPFib B gQ M ∧ E8Fibration.IsProd pr ∧ E8Fibration.IsE8WeightedBundle W pr P'.L M.L ∧
    ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ n = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ y' : Out.baseOver (Sp K) ⟶ P'.A, y'.left = q ≫ ψ ∧ y' ^ n = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists | exact GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open Matrix

theorem quad_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    (t • x) ⬝ᵥ M *ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ M *ᵥ x) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem exists_nat_posDef {n : ℕ} (E A : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef) (hA : A.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • E - A).PosDef := by
  have hq : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ E *ᵥ x := fun x hx => by
    simpa using hE.dotProduct_mulVec_pos hx
  have hc : ContinuousOn (fun x : Fin n → ℝ => (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun x hx => (hq x ?_).ne'
    rintro rfl
    simp at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_bound_of_continuousOn hc
  refine ⟨⌈C⌉₊ + 1, fun κ hκ => PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hE.1.eq, hA.eq, star_trivial]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
    have hb := hC _ hy
    rw [quad_smul, quad_smul, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hx0.ne'))] at hb
    have hqx := hq x hx
    have h1 : (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x) ≤ C := le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at hb)
    have h2 : (x ⬝ᵥ A *ᵥ x) ≤ C * (x ⬝ᵥ E *ᵥ x) := (div_le_iff₀ hqx).1 h1
    have h3 : C < (κ : ℝ) := by
      have := Nat.le_ceil C
      have : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ κ := by exact_mod_cast hκ
      push_cast at this
      linarith
    have h4 : C * (x ⬝ᵥ E *ᵥ x) < κ * (x ⬝ᵥ E *ᵥ x) := mul_lt_mul_of_pos_right h3 hqx
    have h5 : x ⬝ᵥ ((κ : ℝ) • E) *ᵥ x = κ * (x ⬝ᵥ E *ᵥ x) := by
      first
        | rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        | rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, h5]
    linarith

theorem exists_kappa (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ κ : ℕ, ∀ i : Fin 2,
      ((((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) +
        ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  have key : ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ →
      ((((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ)).PosDef := by
    intro m
    have hs : (m.transpose * (W + W.transpose) * m).transpose = m.transpose * (W + W.transpose) * m := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, add_comm,
        Matrix.mul_assoc]
    have hA : ((m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ)).IsHermitian := by
      refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.map_apply, star_trivial]
      exact congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hs i) j)
    obtain ⟨κ₀, h⟩ := exists_nat_posDef _ _ hW.1 hA
    refine ⟨κ₀, fun κ hκ => ?_⟩
    have e : (((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ) = (κ : ℝ) • (W + W.transpose).map (Int.cast : ℤ → ℝ) -
          (m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ) := by
      have e' : ((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose =
          (κ : ℤ) • (W + W.transpose) - m.transpose * (W + W.transpose) * m := by
        simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]
        abel
      rw [e']
      ext a b
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact h κ hκ
  obtain ⟨κ₀, h₀⟩ := key (actMat W 0)
  obtain ⟨κ₁, h₁⟩ := key (actMat W 1)
  refine ⟨max κ₀ κ₁, fun i => ?_⟩
  fin_cases i
  · exact h₀ _ (le_max_left _ _)
  · exact h₁ _ (le_max_right _ _)

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open GlobalTheory.SS GlobalTheory.CechPic


set_option maxRecDepth 20000 in
theorem exists_bound_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  intro W hW
  obtain ⟨κ, hκ⟩ := exists_kappa W hW
  refine ⟨κ, ?_⟩
  intro gQ K _ _ P' B _ _ M pr hPP hpr hE act _ hact i
  obtain ⟨hB, -, ⟨cub⟩, ha, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  let c := GlobalTheory.EighthPowerFactor.siegOne hG hB M.isLB gQ
  have hdiag : Out.RelAmple c.A c.diag :=
    GlobalTheory.EighthPowerFactor.relAmple_diag_lam hB M.isLB ⟨cub.t, cub.isGen⟩ ha
  have hamp := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG gQ 1 8 K _ (Sp K) (𝟙 _) c P'.A pr
    ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) hpr.1 hpr.2 hdiag (hκ i)
  have := P'.isAb.proper
  have hL := P'.isLB
  have hT := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hT (LB.isLB_linComb c.isLB _ _) (N := 1) le_rfl ?_ hamp
  rw [one_smul]
  set f := act i with hf
  set m := actMat W i with hm
  have hflat := LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))
  have hPL : cls P'.L hL = ∑ uv : Fin 8 × Fin 8,
      W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    rw [(cls_eq_iff hL hflat).2 hE, cls_linComb M.isLB, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have hlam : cls c.P c.isLB = lam (cls M.L M.isLB) (fst B B) (snd B B) := cls_cube_two M.isLB _ _ c.isLB
    erw [hlam]
    erw [pull_lam, lift_fst, lift_snd]
    rw [Fin.sum_univ_four]
    simp only [lam, lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_sub, smul_add, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    module
  have hsub := (cls_eq_iff (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb c.isLB _ _)).2
    (GlobalTheory.BilinCalc.main (Sp K) c.A c.P c.isLB
      (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp K) c.A c.diag c.ab (pull_isLB c.isLB _) hdiag c.P c.isLB
        c.rig₁ c.rig₂)
      c.symm P'.A 8 8 pr W (m.transpose * W * m) m (by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc]))
  rw [cls_linComb c.isLB, cls_linComb c.isLB] at hsub
  have hpf : pull f.left (cls P'.L hL) = ∑ uv : Fin 8 × Fin 8,
      (m.transpose * W * m) uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPL, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_) hsub.symm
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hact i uv.1, hact i uv.2]
    rfl
  rw [cls_linComb hL, cls_linComb c.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]
  rw [pull_id, hpf, hPL]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib,
    Finset.smul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  first
    | exact neg_one_smul ℤ _
    | exact neg_one_zsmul _
    | simp

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_act_linComb_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | exact GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  intro S A B _ _ _ pr hP m
  letI cG : ∀ Z : Over S, CommGroup (Z ⟶ B) := fun Z => Hom.commGroup
  have mc : ∀ {T : Over S} (u v : T ⟶ A) (e : A ⟶ B), IsMonHom e → (u * v) ≫ e = (u ≫ e) * (v ≫ e) := by
    intro T u v e he
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
  have pc : ∀ {T : Over S} (x : T ⟶ A) (a : Fin 8),
      x ≫ (∏ b, pr b ^ m a b : A ⟶ B) = ∏ b, (x ≫ pr b) ^ m a b := by
    intro T x a
    let φ : (A ⟶ B) →* (T ⟶ B) :=
      { toFun := fun u => x ≫ u, map_one' := MonObj.comp_one x, map_mul' := fun u v => MonObj.comp_mul x u v }
    have := map_prod φ (fun b => pr b ^ m a b) Finset.univ
    simp only [map_zpow] at this
    exact this
  obtain ⟨f, hf, -⟩ := hP.2 A (fun a => ∏ b, pr b ^ m a b)
  refine ⟨f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_, hf⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  rw [mc _ _ _ (hP.1 a), Category.assoc, Category.assoc, Category.assoc, hf, pc, pc, pc,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [mc _ _ _ (hP.1 b), mul_zpow]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | exact GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem eighthPowerFibre_thetaObj : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.e8_act_linComb_relAmple W hW
  obtain ⟨Mat, hMat⟩ := GlobalTheory.T.e8_fibration_algebraically_closed_field W hW gQ
  refine ⟨Fin 2, inferInstance, Mat, κ, 0, 1, ?_⟩
  intro l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q hQ ρ hρ D e hS K _ _ ev k₀ hk₀
  obtain ⟨P', ψ, B, _, M, pr, hg, hψ, hL, hB, hpr, hE, hpt⟩ := GlobalTheory.T.exists_polarized_specialization_field W gQ V V₁ Q hQ ρ hρ D e hS K ev
  haveI : IsCommMonObj B := hB.1.comm
  choose act hact1 hact2 using fun i : Fin 2 => GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix _ _ _ pr hpr (E8Fibration.actMat W i)
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨bT, pt, htor, hbij, hpair, hsh⟩ := hMat l hl hlo j hj K k₀ hk₀ hlK P' hg B M pr hB hpr hE act hact1 hact2
  let t : TObj (8 * gQ) ((l ^ j) ^ 2) (Fin 2) bT (spMap k₀.subtype) :=
    { A := P'.A, grp := P'.grp, ab := P'.isAb, dim := hg ▸ P'.smoothDim, L := P'.L, isLB := P'.isLB,
      rigid := P'.rigid, sym := P'.sym, ample := P'.ample, ktriv := P'.ktriv, pt := pt, torsion := htor,
      bij := hbij, pairing := hpair, act := act, hom := hact1 }
  refine ⟨bT, t, ψ, ?_, ?_, hψ, hL, ?_⟩
  · exact fun a => ⟨hsh a, hκ gQ K P' B M pr hB hpr hE act hact1 hact2 a⟩
  · exact GlobalTheory.T.e8_act_prod_eq_one W hW gQ K P' B M pr hB hpr hE act hact1 hact2
  · intro y hy q hq1 hq2
    obtain ⟨y', hy'1, hy'2⟩ := hpt _ y hy q hq1 hq2
    obtain ⟨c, hc, -⟩ := hbij K (𝟙 _) y' hy'2
    refine ⟨c, ?_⟩
    rw [← hy'1, ← hc]
    have h0 : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; simp
    simp only [h0, Category.id_comp]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_refinement_odd_prime_localization : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj | exact GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_theta_object : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨J, hJ, Mat, κ, w, w', hA⟩ := GlobalTheory.T.sharp_refinement_odd_prime_localization W hW gQ
  refine ⟨J, hJ, Mat, κ, w, w', ?_⟩
  intro l hl ho j hj V V₁ _ _ _ _ _ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨bT, t, ψ, h1, h2, h3, h4, h5⟩ := hA l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS K ev k₀ hk₀
  obtain ⟨v, hv⟩ := GlobalTheory.T.sharp_refinement_coefficient_family W hW gQ J l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr bT t ψ h3 h4
  exact ⟨bT, t, v, ψ, h1, h2, hv, h3, h4, h5⟩

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_eighth_power_theta_object_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  first | exact @GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | exact GlobalTheory.Poinc.Sep.sharp_fibre_theta_object | (intros; apply GlobalTheory.Poinc.Sep.sharp_fibre_theta_object <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsThirdToSixthOfLaws
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.EndoExtend

open GlobalTheory.CechPic

theorem pic_ext {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) [Smooth P.hom]
    [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X) {a b : Pic P.left}
    (h₁ : CechPic.pull e a = CechPic.pull e b)
    (h₂ : CechPic.pull (pullback.fst P.hom j) a = CechPic.pull (pullback.fst P.hom j) b) : a = b := by
  rw [← sub_eq_zero, ← map_sub] at h₁ h₂
  rw [← sub_eq_zero]
  obtain ⟨N, hN, hc⟩ := cls_surj (a - b)
  rw [← hc] at h₁ h₂ ⊢
  exact (cls_eq_zero_iff hN).2 (GenericExtend.exists_isGen_of_densePart X U j hn ‹_› ‹_› ‹_› ‹_› P e N he ‹_› ‹_› hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₂))

section Cube

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • CechPic.pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls G x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (u : T' ⟶ T)
    (h : ∀ i, x' i = u ≫ x i) (c : Pic G.left) : CechPic.pull u.left (cubeCls G x c) = cubeCls G x' c := by
  obtain rfl : x' = fun i => u ≫ x i := funext h
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z : T' ⟶ G => _ • CechPic.pull z.left c) (psum_hom (preHom u) x I.down)

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : CechPic.pull (eSec G) c = 0) :
    cubeCls G (fun _ : Fin n => (η[G] : 𝟙_ (Over S) ⟶ G)) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have : psum G (fun _ : Fin n => (1 : 𝟙_ (Over S) ⟶ G)) I.down = 1 := by
    unfold psum
    induction (List.finRange n).filter (· ∈ I.down) with
    | nil => rfl
    | cons k l ih => exact (_root_.one_mul _).trans ih
  rw [e₁] at this
  rw [this]
  exact (congrArg (_ • ·) hc).trans (smul_zero _)

variable {G} in
theorem push_cubeCls {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : T'.left ⟶ T.left) (hu : u ≫ T.hom = T'.hom ≫ f)
    (hx : ∀ i, (x' i).left ≫ φ = u ≫ (x i).left) (c : Pic G.left) :
    CechPic.pull u (cubeCls G x c) = cubeCls G' x' (CechPic.pull φ c) := by
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp,
    psum_push h x' x (Over.homMk u hu) (fun i => Over.OverMorphism.ext (hx i)) I.down]
  rfl

end Cube

theorem hypS_of_densePart {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over X) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G)
    (hext : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback j).map F = f)
    (h : HypS ((Over.pullback j).obj G) (L.L.pull (pullback.fst G.hom j))) : HypS G L.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := h
  obtain ⟨w, ⟨hw, rfl⟩, -⟩ := hext w' hw'
  obtain ⟨wd, ⟨hwd, rfl⟩, -⟩ := hext wd' hwd'
  have hL := L.isLB
  have hL' := pull_isLB hL (pullback.fst G.hom j)
  have hG := isGrpPullback_pullback G j
  have A : ∀ {Y Z : Over X} (a : Y ⟶ Z),
      ((Over.pullback j).map a).left ≫ pullback.fst Z.hom j = pullback.fst Y.hom j ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  have h0 : CechPic.pull (eSec G) (cls L.L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨L.rig, L.rigGen⟩
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · refine (hext (𝟙 _) inferInstance).unique ⟨Serre.isMonHom_mul w wd, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_mul, hs]
  · refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cubeLB G _ hL).symm)
    refine pic_ext j hn G (eSec G) (Over.w η[G]) (h0.trans ?_) ?_
    · refine ((pull_cubeCls G _ (fun _ => η[G]) η[G] (fun i => ?_) _).trans (cubeCls_one G _ h0)).symm
      fin_cases i <;> simp
    · have e := ((cls_eq_iff hL' (LB.isLB_linComb hL' _ _)).2 hp).trans (cls_cubeLB ((Over.pullback j).obj G) _ hL')
      have e' := push_cubeCls hG (T' := (Over.pullback j).obj G) (T := G) ![𝟙 _, (Over.pullback j).map w] ![𝟙 G, w]
        (pullback.fst G.hom j) pullback.condition (fun i => by
          fin_cases i
          · simp
          · exact A w) (cls L.L hL)
      exact e.trans e'.symm
  · refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
    refine pic_ext j hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
    · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
        (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
      fin_cases i <;> simp
    · let δ := lift ((Over.pullback j).map (fst G G)) ((Over.pullback j).map (snd G G))
      have e := congrArg (CechPic.pull δ.left) ((cls_cubeLB ((Over.pullback j).obj G) _ hL').symm.trans
        (((cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL' _ _)).2 ha).trans
          (cls_cubeLB ((Over.pullback j).obj G) _ hL')))
      have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hG (T' := (Over.pullback j).obj (G ⊗ G)) (T := G ⊗ G)
        (fun i => (Over.pullback j).map (x i)) x (pullback.fst (G ⊗ G).hom j) pullback.condition (fun i => A _)
        (cls L.L hL)
      rw [pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G ≫ w, snd G G] i)) δ
          (fun i => by fin_cases i <;> simp [δ]),
        pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G, snd G G ≫ wd] i)) δ
          (fun i => by fin_cases i <;> simp [δ])] at e
      exact (e' _).trans (e.trans (e' _).symm)

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isIso_stalkClosedPointTo : IsIso (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) := by
  have e : M.stalkHom (M.pt (IsLocalRing.closedPoint Ω)) =
      (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom := by
    unfold RatModel.stalkHom
    erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  change Function.Bijective (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom
  rw [← e]
  refine ⟨M.stalkHom_injective _, fun x => ?_⟩
  have hx : x ∈ M.O (M.pt (IsLocalRing.closedPoint Ω)) := by
    have h := M.O_genericPoint
    rw [← M.pt_apply (IsLocalRing.closedPoint Ω)] at h
    exact h.ge trivial
  obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem isPreimmersion_pt : IsPreimmersion M.pt := by
  have := isIso_stalkClosedPointTo M
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

theorem flat_pt : Flat M.pt := by
  have := isIso_stalkClosedPointTo M
  have := GenericExt.flat_fromSpecStalk M.Z (M.pt (IsLocalRing.closedPoint Ω))
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

end Model

theorem hypS_and_endo_and_iso_extend : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → HypS Q.G Q.L.L ∧ (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f → ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧ (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 → LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) → LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  intro hdvr o Ω _ _ _ hA S ρ M U₀ Q hO
  have := hA.ded
  have := hA.ft
  have := hA.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hX : Geo.Tor.IsNormalScheme M.Z ∧ ∃ z : M.Z ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z :=
    ⟨hO.normal, _, MinorModel.locallyOfFiniteType_int M, MinorModel.flat_int M _⟩
  have := isPreimmersion_pt M
  have := flat_pt M
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have hL := Q.L.isLB
  refine ⟨?_, GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ M.pt hX ‹_› ‹_› inferInstance inferInstance _ _ Q.semi Q.semi, ?_⟩
  · have : Nonempty U₀ := hO.ne.to_subtype
    have : IsDominant U₀.ι := ⟨by
      rw [DenseRange, Scheme.Opens.range_ι]
      exact U₀.isOpen.dense hO.ne⟩
    have := ρ.P.isAb.comm
    refine hypS_of_densePart U₀.ι hO.normal Q.G Q.L (GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ U₀.ι hX inferInstance inferInstance
      inferInstance inferInstance _ _ Q.semi Q.semi) ?_
    have hP := ρ.P.isLB
    have h₁ : HypS ((Over.pullback Q.u₀).obj ρ.P.A) (Q.L.L.pull Q.φ) :=
      SymBaseChange.hypS_baseChange _ _ ρ.P.A ((Over.pullback Q.u₀).obj ρ.P.A) Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) _ _ hP (pull_isLB hL _)
        (isGrpPullback_pullback _ _) ⟨Q.w, Q.w_gen⟩ ρ.hypS
    let ψ := Q.cart.1.lift (pullback.fst Q.G.hom U₀.ι) (pullback.snd _ _) pullback.condition
    have hψ : ψ ≫ Q.φ = pullback.fst Q.G.hom U₀.ι := Q.cart.1.lift_fst _ _ _
    refine SymBaseChange.hypS_baseChange _ _ ((Over.pullback Q.u₀).obj ρ.P.A) ((Over.pullback U₀.ι).obj Q.G) (𝟙 _) ψ _ _ (pull_isLB hL _) (pull_isLB hL _)
      (Q.cart.cancel ((isGrpPullback_pullback Q.G U₀.ι).congr (Category.id_comp _).symm hψ.symm)
        ((Q.cart.1.lift_snd _ _ _).trans (Category.comp_id _).symm)) ?_ h₁
    refine (cls_eq_iff (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)).1 ?_
    exact (congrArg (CechPic.pull · (cls _ hL)) hψ.symm).trans (pull_comp ψ Q.φ (cls _ hL))
  · intro n x x' hx ε ε' _ _ h
    have := smooth_tensorObj_hom Q.G Q.G
    have := geometricallyIntegral_tensorObj_hom Q.G Q.G
    have h0 : CechPic.pull (eSec Q.G) (cls Q.L.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨Q.L.rig, Q.L.rigGen⟩
    have key : ∀ (y : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)) (δ : Fin n → ℤ), (∀ i, IsMonHom (y i)) →
        CechPic.pull (η[Q.G ⊗ Q.G]).left (cls _ (LB.isLB_linComb hL (fun i => (y i).left) δ)) = 0 := by
      intro y δ hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [cls_linComb hL, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, ← pull_comp, ← Over.comp_left, (hy i).one_hom]
      exact (congrArg (_ • ·) h0).trans (smul_zero _)
    refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      (pic_ext M.pt hO.normal (Q.G ⊗ Q.G) (η[Q.G ⊗ Q.G]).left (Over.w _)
        ((key x ε fun i => (hx i).1).trans (key x' ε' fun i => (hx i).2).symm) ?_)
    exact (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2 h

end GlobalTheory.ZH.EndoExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endo_lbIso_symmetryHypothesis_extend_normalModel : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → HypS Q.G Q.L.L ∧ (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f → ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧ (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 → LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) → LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  first | exact @GlobalTheory.ZH.EndoExtend.hypS_and_endo_and_iso_extend | exact GlobalTheory.ZH.EndoExtend.hypS_and_endo_and_iso_extend | (intros; apply GlobalTheory.ZH.EndoExtend.hypS_and_endo_and_iso_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.EighthPowerFactor

open CechPic

theorem relAmple_diag_lam {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hN : ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hι : (M.pull ((𝟙 B)⁻¹ : B ⟶ B).left).IsLB := pull_isLB hM _
  have hD1 : (LB.div ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) M).IsLB := LB.isLB_div hN hM
  have hD := LB.isLB_div hD1 hι
  haveI : IsProper B.hom := IsAbelianScheme.proper
  have hI : ((𝟙 B)⁻¹ : B ⟶ B) ≫ (𝟙 B)⁻¹ = 𝟙 B := by
    first
    | rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    | rw [GrpObj.inv_def, Category.id_comp, GrpObj.inv_inv]
    | simp [GrpObj.comp_inv]
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := ⟨⟨_, hI, hI⟩⟩
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left :=
    ⟨⟨((𝟙 B)⁻¹ : B ⟶ B).left, by rw [← Over.comp_left, hI, Over.id_left],
      by rw [← Over.comp_left, hI, Over.id_left]⟩⟩
  have h0 : ∀ (L : LB (Sp k)), L.IsLB → ∃ t : LB.Gen L, t.IsGen := by
    intro L hL
    have hcov : ∀ y : Sp k, ∃ i, y ∈ L.U i := fun y => by
      have hy : y ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hy
    have hs : ∀ y y' : Sp k, y = y' := fun y y' => Subsingleton.elim (α := PrimeSpectrum k) y y'
    obtain ⟨y₀⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    obtain ⟨i₀, hi₀⟩ := hcov y₀
    exact GlobalTheory.DescendedPrincipal.exists_gen_of_chart hL i₀ fun y => by rw [← hs y₀ y]; exact hi₀
  set c := GlobalTheory.CechPic.cls M hM
  have e1 : (1 : B ⟶ B).left = (toUnit B).left ≫ η[B].left := rfl
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left c = 0 := by
    rw [e1, GlobalTheory.CechPic.pull_comp]
    obtain ⟨L, hL, hLc⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull η[B].left c)
    rw [← hLc, (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (h0 L hL), map_zero]
  have e5 : GlobalTheory.CechPic.lam c (𝟙 B)⁻¹ (𝟙 B) = -GlobalTheory.CechPic.pull ((𝟙 B)⁻¹ : B ⟶ B).left c - c := by
    unfold GlobalTheory.CechPic.lam
    rw [inv_mul_cancel, Over.id_left, GlobalTheory.CechPic.pull_id, h1]
    abel
  have e3 := GlobalTheory.CechPic.lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, GlobalTheory.CechPic.lam_one_left, e5] at e3
  have e2 : GlobalTheory.CechPic.cls (abelian₂ B M) (LB.isLB_linComb hM _ _) = GlobalTheory.CechPic.lam c (fst B B) (snd B B) :=
    GlobalTheory.CechPic.cls_cube_two hM _ _ _
  have hc : GlobalTheory.CechPic.cls _ hD = 0 := by
    rw [GlobalTheory.CechPic.cls_div hD1 hι hD, GlobalTheory.CechPic.cls_div hN hM hD1,
      GlobalTheory.CechPic.cls_pull (L := abelian₂ B M) (LB.isLB_linComb hM _ _) _ hN, GlobalTheory.CechPic.cls_pull hM _ hι, e2,
      GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
    rw [eq_comm, ← sub_eq_zero] at e3
    rw [← e3]
    abel
  have H := (GlobalTheory.CechPic.cls_eq_zero_iff hD).1 hc
  have hMa := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hM).1 ha
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 (hMa.tensor (hMa.pull_of_isFinite _) hN H)

theorem weilIs_one_one (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB A.left} (hM : M.IsLB) (T : Over S) : Out.WeilIs A M 1 (1 : T ⟶ A) 1 1 := by
  refine GlobalTheory.DescendedPrincipal.weilIs_one_right hG hA hM fun _ => ⟨⊤, trivial, ?_⟩
  exact match GlobalTheory.DescendedPrincipal.exists_theta_one (A := A) hM _ with
  | ⟨θ, hθ, _⟩ => ⟨θ, hθ.trans (MonObj.comp_one _).symm⟩


open SiegelOfPolarised PrimNorm in
def siegOne (hG : Out.GlobalFnsSt) {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (g : ℕ) :
    SiegPre g 1 ((1 : kˣ) : k) (𝟙 (Sp k)) where
  A := B
  ab := hB
  P := abelian₂ B M
  isLB := LB.isLB_linComb hM _ _
  rig₁ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  symm := lbIso_lam_pull hM _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact weilIs_one_one hG hB (pull_isLB (LB.isLB_linComb hM _ _) _) _

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : (W + W.transpose).det = 1) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  have hu : IsUnit (W + W.transpose).det := by rw [hW]; exact isUnit_one
  refine ⟨fun j => Sum.elim (fun p => Matrix.single p.1 p.2 1)
      (fun b => if b then (W + W.transpose)⁻¹ * W else (W + W.transpose)⁻¹ * W.transpose) j,
    Sum.inr true, Sum.inr false, ?_, ?_, fun u v => ⟨Sum.inl (u, v), rfl⟩⟩
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]

theorem isMonHom_of_coord {S : Scheme.{0}} {A G X : Over S} [GrpObj A] [GrpObj G] [GrpObj X] {n : ℕ}
    {pr : Fin n → (G ⟶ A)} (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) {f : X ⟶ G}
    (hf : ∀ u, IsMonHom (f ≫ pr u)) : IsMonHom f := by
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun x x' h =>
    (hu _ (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  constructor
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

theorem exists_polAV_hypS_retract : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Out.KTriv B M → ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  intro k _ _ B _ g hB hd M hM ha hK
  obtain ⟨hL1, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG : Out.GlobalFnsSt := hL1.globalFns
  letI : IsCommMonObj B := hB.comm
  have hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen := GlobalTheory.exists_gen_theta_of_isAbelianScheme k B hB M hM
  let b : GlobalTheory.ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp [IsPrimitiveRoot.one]⟩
  let c := siegOne hG hB hM g
  have hc : c.Principal :=
    ⟨relAmple_diag_lam hB hM hΘ ha, fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  obtain ⟨t, hsh, hp⟩ := GlobalTheory.exists_isSharp_and_prim hL1 hL2 GlobalTheory.Moduli.cube_of_isLB g (8 * g) W _ a w w' bas
    hW hb hw hw' hs 1 k b (Sp k) (𝟙 _) c (show (1 : kˣ) ^ 1 = 1 from one_pow 1) odd_one hc hd
  obtain ⟨pr, hpr, hu, -, -, -⟩ := hsh
  obtain ⟨i, hi, -⟩ := hu B (fun _ => 𝟙 B)
  letI := t.ab.comm
  refine ⟨t.pol, i, pr 0, ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩, ?_, hpr 0, hi 0⟩
  exact isMonHom_of_coord hpr hu (fun u => by rw [hi u]; exact (inferInstance : IsMonHom (𝟙 B)))

end GlobalTheory.EighthPowerFactor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TestFibre

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev cF (R : Type) [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] (c : F) :
    Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c

def IsComb {k : ℕ} {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) : Prop :=
  ∀ j, t.f j = ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j

abbrev FrameAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValIs {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsNormPull (ρ : LB.Gen (A.L.pull (eSec A.A))) (m N : ℕ) (th : SecA A F 1) (s : SecA A F N) : Prop :=
  ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ^ m).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ)]),
    α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left)
      (rigT A.A A.L ρ (TFK (R := R) F) ((N : ℤ) - 1)) ∧
    IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s

end

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

def PtsOver (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) : Prop :=
  ∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left

def SecsOver (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A)))
    (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N) : Prop :=
  rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧
  (∀ a, ValIs u.A th (x a) (e a) (y₀ ⟨S.th a, S.th_mem a⟩)) ∧
  (∀ i a, ValIs u.A (s i) (x a) (e a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)) ∧
  IsNormPull u.A rig (ρ.n ^ ρ.k) S.N th (s ρ.i₀) ∧
  ∀ a, ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)),
    SymLift u.A.A u.A.L S.N S.N (x (S.r • a)) θ ∧ ∀ i σ, IsActOf u.A.A u.A.L S.N θ (s i) σ →
      IsComb u.A s (fun j => y₀ (algebraMap o S.R (S.ρ a j i))) σ

def NormIs (l : u.Lab) (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ) : Prop :=
  0 < lam ∧ QForm.IsQ u.D.toPre ϖ Q ∧ (∀ χ, l.q χ = lam * Q χ) ∧
  (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔ ‖c‖ ≤ Real.exp (-(lam * r))) ∧
  ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔ ‖c‖ = Real.exp (-(lam * r))

theorem laws_all (h : Laws) (h₂ : Laws2) :
    LL ∧ TwistBCSpanStatement ∧ TWM.VRatioGtStatement ∧ TWStatement ∧ UUStatement := by
  have hS : SecBaseChangeSt := h.secBaseChange
  have hT : TwistBCSpanStatement := twistBCSpan_of twistBaseChange
  exact ⟨⟨h, h₂, laws3, uniformisationLaws_of_baseChange_laws polBaseChange_holds globalFns_holds hS twistBaseChange,
      laws5 globalFns_holds hS⟩, hT, RatioVal.main, TWM.tw_of globalFns_holds hT RatioVal.main,
    UnitBallFree.main globalFns_holds twistBaseChange⟩

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.nonempty_level_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (M : ℕ) (ze : kˣ), (M : k) ≠ 0 → IsPrimitiveRoot ze M → Nonempty (Out.Level P M (unitOn ze)) := by
  intro k _ _ P M ze hM hz
  have hz0 : IsPrimitiveRoot (ze : k) M := IsPrimitiveRoot.coe_units_iff.mpr hz

  have hinj : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Sp k),
      Function.Injective ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    intro K _ s
    exact Function.Injective.of_comp
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
        ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    fun a b h => hinj k (𝟙 _) (by rw [RingHom.comp_apply, RingHom.comp_apply, h])

  have hu : IsPrimitiveRoot (unitOn ze) M := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz0.map_of_injective hinv
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.ConstThetaLevel.exists_symplectic_points hL k P rfl M hM (unitOn ze) hu

  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing GlobalTheory.globalFns_holds hL.weil hL.mulN (Sp k) P M (unitOn ze) hu
    (fun K _ s => by
      refine ⟨fun h0 => hM ?_, ?_⟩
      · have hf := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
          ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
        exact hf (by rw [map_natCast, map_zero]; exact h0)
      · rw [← IsPrimitiveRoot.coe_units_iff]
        exact hz0.map_of_injective (hinj K s))
    x hx1 hx2
  exact ⟨lev⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS


open UnramifiedEndFlat in
theorem flat_of_isDominant_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IrreducibleSpace G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') [IsMonHom φ]
    [QuasiCompact φ.left] [IsDominant φ.left] : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : LocallyOfFiniteType (φ.left ≫ G'.hom) := by rw [Over.w φ]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G'.hom
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left := by
    have h := (genericPoint_spec G.left).image φ.left.continuous
    rw [Set.image_univ, φ.left.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec G'.left)
  obtain ⟨W, hW, H⟩ := IntDiv.exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

theorem flat_and_surjective_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], SmConn G → SmConn G' → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Flat i.left ∧ Surjective i.left := by
  intro k _ _ G G' _ _ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ i _ hi
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have := grpObj_geometricallyIntegral_of_smooth _ G'
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have : IsIntegral G'.left := GeometricallyIntegral.isIntegral_of_subsingleton G'.hom
  have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact i.left := .of_comp _ G'.hom
  have : Surjective i.left := DivisiblePart.surjective_of_rationalPoints i hi
  exact ⟨flat_of_isDominant_grpHom k G G' i, this⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem isAbelianScheme_overPullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) := by
  constructor
  · have := h.comm
    infer_instance
  · have := h.smooth
    change Smooth (pullback.snd A.hom f)
    infer_instance
  · have := h.proper
    change IsProper (pullback.snd A.hom f)
    infer_instance
  · have := h.geomConnected
    change GeometricallyConnected (pullback.snd A.hom f)
    infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionGalois

theorem pow_fix {M : Type} [CommGroup M] (l : ℕ) (f : Monoid.End M) (h : ∀ x : M, x ^ l = 1 → f x = x) (n : ℕ) :
    ∀ x : M, x ^ l ^ n = 1 → (f ^ l ^ n) x = x := by
  have hp : ∀ (g : Monoid.End M) (x : M), g x = x → ∀ k : ℕ, (g ^ k) x = x := by
    intro g x hx k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ]; show (g ^ k) (g x) = x; rw [hx, ih]
  induction n with
  | zero => intro x hx; rw [pow_zero, pow_one] at hx; rw [hx, map_one]
  | succ n ih =>
    intro x hx
    set g := f ^ l ^ n with hg
    have h1 : g (x ^ l) = x ^ l := ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)
    have hd : (g x * x⁻¹) ^ l = 1 := by rw [mul_pow, ← map_pow, h1, inv_pow, mul_inv_cancel]
    have hgd : g (g x * x⁻¹) = g x * x⁻¹ := hp f _ (h _ hd) _
    have hk : ∀ k : ℕ, (g ^ k) x = x * (g x * x⁻¹) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ']
        show g ((g ^ k) x) = _
        rw [ihk, map_mul, map_pow, hgd, pow_succ', ← _root_.mul_assoc, mul_comm (g x) x⁻¹, mul_inv_cancel_left]
    rw [pow_succ, pow_mul, ← hg, hk, hd, _root_.mul_one]

theorem spMap_comp' {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

noncomputable def tw (τ : Ω ≃ₐ[K] Ω) : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    show spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K Ω) = spMap (algebraMap K Ω)
    rw [← spMap_comp']
    congr 1
    ext c
    exact τ.commutes c)

theorem tw_one : tw (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap (RingHom.id Ω) = 𝟙 _
  exact Spec.map_id _

theorem tw_mul (τ σ : Ω ≃ₐ[K] Ω) : tw (τ * σ) = tw τ ≫ tw σ := by
  apply Over.OverMorphism.ext
  exact spMap_comp' σ.toRingEquiv.toRingHom τ.toRingEquiv.toRingHom

theorem tw_pow_fix (P : Out.PolAV (Sp K)) (l : ℕ) (τ : Ω ≃ₐ[K] Ω)
    (h : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 → tw τ ≫ x = x) (n : ℕ)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) (hx : x ^ l ^ n = 1) : tw (τ ^ l ^ n) ≫ x = x := by
  have := P.isAb.comm
  let f : Monoid.End (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) :=
    MonoidHom.mk' (fun x => tw τ ≫ x) (fun a b => MonObj.comp_mul _ _ _)
  have hf : ∀ (k : ℕ) x, (f ^ k) x = tw (τ ^ k) ≫ x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero, tw_one, Category.id_comp]; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, tw_mul, Category.assoc, ← ih]; rfl
  rw [← hf]
  exact pow_fix l f h n x hx

theorem exists_field [CharZero K] [IsAlgClosure K Ω] (P : Out.PolAV (Sp K)) (l n : ℕ)
    (hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1})
    (h : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 → tw τ ≫ x = x) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧
      ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 →
        ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left := by
  have hpr := P.isAb.proper
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1},
      ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
        (∀ τ : Ω ≃ₐ[K] Ω, τ ∈ L.fixingSubgroup ↔ tw τ ≫ x.1 = x.1) ∧
        ∀ L' : IntermediateField K Ω, L ≤ L' → ∃ y : Sp L' ⟶ P.A.left, spMap (algebraMap L' Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, h1, h2, h3⟩ := GlobalTheory.T.exists_field_of_definition_of_point P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    refine ⟨L, hL, fun τ => ?_, fun L' hL' => (h2 L' (algebraMap L' Ω)).1 fun c hc => ⟨⟨c, hL' hc⟩, rfl⟩⟩
    have e : spMap (RingHom.id Ω) ≫ x.1.left = x.1.left := by
      have e₀ : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
      rw [e₀]; exact Category.id_comp _
    have := h1 τ.toRingEquiv.toRingHom (RingHom.id Ω)
    rw [e] at this
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun hh => Over.OverMorphism.ext (this.2 hh), fun hh => this.1 (congrArg CommaMorphism.left hh)⟩
  choose F hF1 hF2 hF3 using key
  have hmem : ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ (⨆ x, F x).fixingSubgroup ↔
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l ^ n = 1 → tw τ ≫ x = x := by
    intro τ
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
    simp only [IntermediateField.le_iff_le, Subgroup.zpowers_le, hF2]
    exact ⟨fun hh x hx => hh ⟨x, hx⟩, fun hh x => hh x.1 x.2⟩
  have hn : (⨆ x, F x).fixingSubgroup.Normal := ⟨fun τ hτ σ => by
    rw [hmem] at hτ ⊢
    intro x hx
    have hx' : (tw σ⁻¹ ≫ x) ^ l ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    rw [tw_mul, tw_mul, Category.assoc, Category.assoc, hτ _ hx', ← Category.assoc, ← tw_mul, mul_inv_cancel,
      tw_one, Category.id_comp]⟩
  have hg : IsGalois K (⨆ x, F x : IntermediateField K Ω) := (InfiniteGalois.normal_iff_isGalois _).1 hn
  refine ⟨⨆ x, F x, IntermediateField.finiteDimensional_iSup_of_finite, hg.to_normal, fun g => ?_,
    fun x hx => hF3 ⟨x, hx⟩ _ (le_iSup F _)⟩
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := (⨆ x, F x : IntermediateField K Ω)) Ω g
  refine ⟨n, ?_⟩
  rw [← map_pow, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hmem]
  exact tw_pow_fix P l τ (h τ) n

theorem exists_pairing (hL : Out.Laws) (P : Out.PolAV (Sp K)) :
    ∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ,
      ∀ (k : ℕ) x y, x ^ k = 1 → y ^ k = 1 → ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ e k x y = u := by
  classical
  have key : ∀ (k : ℕ) (x y : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), ∃ v : Ωˣ, x ^ k = 1 → y ^ k = 1 →
      ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ v = u := by
    intro k x y
    by_cases hh : x ^ k = 1 ∧ y ^ k = 1
    · obtain ⟨c, hc, hu⟩ := (hL.weil _ P k _).1 x y hh.1 hh.2
      let E := Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv
      refine ⟨E c, fun _ _ u => ⟨fun H => ?_, fun H => ?_⟩⟩
      · rw [← hu _ H]
        exact E.apply_symm_apply u
      · subst H
        have : Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (E c) = c :=
          E.symm_apply_apply c
        rw [this]; exact hc
    · exact ⟨1, fun a b => (hh ⟨a, b⟩).elim⟩
  choose e he using key
  exact ⟨e, he⟩

end GlobalTheory.TorsionGalois


open GlobalTheory.TorsionGalois in
theorem GlobalTheory.torsion_points_galois_module : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ), l.Prime → (∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))) ∧ (∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ ∀ (τ : Ω ≃ₐ[K] Ω) n (x y x' y' : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l ^ n = 1 → y ^ l ^ n = 1 → x'.left = spMap τ.toRingEquiv.toRingHom ≫ x.left → y'.left = spMap τ.toRingEquiv.toRingHom ≫ y.left → (e n x y : Ω) ^ l ^ n = 1 ∧ (e n x' y' : Ω) = τ (e n x y)) ∧ ((∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ n, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧ ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 → ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left) := by
  intro K _ _ P Ω _ _ _ l hl
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hne : ∀ n, ((l ^ n : ℕ) : Ω) ≠ 0 := fun n => Nat.cast_ne_zero.2 (pow_ne_zero n hl.ne_zero)
  have hcard : ∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} =
      l ^ (n * (2 * P.g)) := fun n => by
    rw [pow_mul]
    exact (hL.mulN _ P (l ^ n) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero n hl.ne_zero))).2.2.2.2 Ω _ (hne n)
  refine ⟨hcard, ?_, fun h n => exists_field P l n
    (Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero))
    fun τ x hx => Over.OverMorphism.ext (h τ x hx)⟩
  have := P.isAb.comm
  obtain ⟨e, he⟩ := exists_pairing (Ω := Ω) hL P
  have hmul : ∀ (k : ℕ) x x' y, x ^ k = 1 → x' ^ k = 1 → y ^ k = 1 → e k (x * x') y = e k x y * e k x' y := by
    intro k x x' y hx hx' hy
    rw [← he k _ _ (by rw [mul_pow, hx, hx', _root_.mul_one]) hy, map_mul]
    exact (hL.weil _ P k _).2.1 x x' y _ _ ((he k _ _ hx hy _).2 rfl) ((he k _ _ hx' hy _).2 rfl)
  refine ⟨fun n => e (l ^ n), ⟨fun n x x' y hx hx' hy => ⟨hmul _ _ _ _ hx hx' hy, ?_⟩, fun n x y hx hy => ?_,
    fun n x hx h => ?_⟩, fun τ n x y x' y' hx hy hx' hy' => ⟨?_, ?_⟩⟩
  · rw [← he _ _ _ hy hx, map_inv]
    exact GlobalTheory.CommPairing.weilIs_symm P.isLB ((he _ _ _ hx hy _).2 rfl)
  · have hxl : (x ^ l) ^ l ^ n = 1 := by rw [← pow_mul, ← pow_succ']; exact hx
    have hu : IsUnit ((l ^ n * l : ℕ) : Γ((Over.mk (spMap (algebraMap K Ω))).left, ⊤)) := by
      have := (IsUnit.mk0 _ (hne (n + 1))).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
      rw [map_natCast, pow_succ] at this
      exact this
    have H := ((hL.weil _ P (l ^ n) _).2.2.2 l x y _ hu (by rw [← pow_succ]; exact hx) hy).2
      ((he _ _ _ hxl hy _).2 rfl)
    rw [← Nat.cast_mul, ← pow_succ] at H
    exact (he _ _ _ hx (by rw [pow_succ, pow_mul, hy, one_pow]) _).1 H
  · refine GlobalTheory.ThetaRep.eq_one_of_weilIs hL P _ (hne n) x hx fun y hy => ?_
    have H := (he _ _ _ hx hy _).2 (h y hy)
    rwa [map_one] at H
  · have h1 : e (l ^ n) 1 y = 1 := by
      have := hmul (l ^ n) 1 1 y (one_pow _) (one_pow _) hy
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have hp : ∀ m : ℕ, e (l ^ n) (x ^ m) y = e (l ^ n) x y ^ m := by
      intro m
      induction m with
      | zero => rw [pow_zero x, pow_zero, h1]
      | succ m ih =>
        rw [pow_succ x, hmul _ _ _ _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) hx hy, ih, pow_succ]
    show (e (l ^ n) x y : Ω) ^ l ^ n = 1
    rw [← Units.val_pow_eq_pow_val, ← hp, hx, h1, Units.val_one]
  · obtain rfl : x' = tw τ ≫ x := Over.OverMorphism.ext hx'
    obtain rfl : y' = tw τ ≫ y := Over.OverMorphism.ext hy'
    have H := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (tw τ) ((he _ _ _ hx hy _).2 rfl)
    have E : Units.map (tw τ).left.appTop.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (e (l ^ n) x y)) =
        Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
          (Units.map τ.toRingEquiv.toRingHom.toMonoidHom (e (l ^ n) x y)) :=
      Units.ext (congrArg (fun q => q.hom (e (l ^ n) x y).val)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ.toRingEquiv.toRingHom))).symm
    rw [E] at H
    exact congrArg Units.val ((he _ _ _ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) _).1 H)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGaloisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_polarised_abelianVariety_galois : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ), l.Prime → (∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))) ∧ (∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ ∀ (τ : Ω ≃ₐ[K] Ω) n (x y x' y' : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l ^ n = 1 → y ^ l ^ n = 1 → x'.left = spMap τ.toRingEquiv.toRingHom ≫ x.left → y'.left = spMap τ.toRingEquiv.toRingHom ≫ y.left → (e n x y : Ω) ^ l ^ n = 1 ∧ (e n x' y' : Ω) = τ (e n x y)) ∧ ((∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ n, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧ ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 → ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left) := by
  first | exact @GlobalTheory.torsion_points_galois_module | exact GlobalTheory.torsion_points_galois_module | (intros; apply GlobalTheory.torsion_points_galois_module <;> assumption)
end
end

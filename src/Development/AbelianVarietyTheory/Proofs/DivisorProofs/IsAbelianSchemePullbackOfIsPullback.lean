module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverSymmBundlePowerDecompositStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfLbPowLbIsoLinComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePowLinComb

open GlobalTheory.CechPic

def genClasses (X : Scheme.{0}) : AddSubmonoid (Pic X) where
  carrier := {c | ∃ (A : LB X) (hA : A.IsLB), IsGenerated A ∧ cls A hA = c}
  zero_mem' := ⟨_, LB.isLB_triv X, isGenerated_triv X, rfl⟩
  add_mem' := by
    rintro _ _ ⟨A, hA, gA, rfl⟩ ⟨B, hB, gB, rfl⟩
    exact ⟨tens A B, isLB_tens hA hB, AmpleModelPos.isGenerated_tens gA gB, cls_tens hA hB _⟩

theorem isAmpleLB_of_lbPow_lbIso_linComb : ∀ (X : Scheme.{0}) (L M : LB X), IsAmpleLB M → L.IsLB →
    ∀ (N a₀ r : ℕ) (a : Fin r → ℕ) (β : Fin r → (X ⟶ X)), 1 ≤ N → 1 ≤ a₀ →
    LBIso (lbPow L N) (LB.LinComb M (K := Option (Fin r)) (fun o => o.elim (𝟙 X) fun i => β i)
      fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) → IsAmpleLB L := by
  intro X L M hM hL N a₀ r a β hN ha₀ H
  obtain ⟨k, hk, gk⟩ := hM.exists_isGenerated_pow
  have hMk := isLB_lbPow hM.isLB k

  set c : Pic X := ∑ i, a i • pull (β i) (cls _ hMk) with hc
  have hcmem : c ∈ genClasses X := by
    refine AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.nsmul_mem _ ?_ _
    exact ⟨_, pull_isLB hMk (β i), gk.pull (β i), cls_pull hMk (β i) _⟩
  obtain ⟨A, hA, gA, hAc⟩ := hcmem
  have hLN := isLB_lbPow hL (N * k)
  have hMa := isLB_lbPow hM.isLB (a₀ * k)
  have hAmp : IsAmpleLB (lbPow M (a₀ * k)) :=
    (isAmpleLB_pow_iff hM.isLB (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2 hM
  have h₁ := LB.isLB_div hLN hMa
  have h₂ := LB.isLB_div h₁ hA
  have hLpow : IsAmpleLB (lbPow L (N * k)) := hAmp.tensor_isGenerated gA hLN ((cls_eq_zero_iff h₂).1 ?_)
  · exact (isAmpleLB_pow_iff hL (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1 hLpow
  have hE := (cls_eq_iff (isLB_lbPow hL N) (LB.isLB_linComb hM.isLB _ _)).2 H
  rw [cls_lbPow hL, cls_linComb hM.isLB, Fintype.sum_option] at hE
  rw [cls_div h₁ hA, cls_div hLN hMa, hAc, hc, cls_lbPow hL, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [Option.elim, pull_id] at hE
  simp only [map_nsmul]
  have e1 : (N * k) • cls L hL = k • (N • cls L hL) := by rw [smul_smul, mul_comm]
  rw [e1, hE]
  simp only [natCast_zsmul, smul_add, Finset.smul_sum, smul_smul]
  rw [sub_sub, sub_eq_zero, mul_comm a₀ k]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

end GlobalTheory.AmplePowLinComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteBase

theorem isAmpleLB_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) π → ∀ L : LB G.left, L.IsLB → IsAmpleLB (L.pull π) → IsAmpleLB L := by
  intro R R' _ _ _ _ _ _ _ _ _ _ ρ hinj hfin G _ G' _ π hG h L hL hA
  have := hG.smooth
  have := hG.quasiCompact
  have hF : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hfin
  have hS : Surjective (spMap ρ) := ⟨hfin.to_isIntegral.comap_surjective hinj⟩
  have : IsFinite π := MorphismProperty.of_isPullback (P := @IsFinite) h.1.flip hF
  have hs : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hS
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hN : GlobalTheory.IsNormalScheme G.left := isNormalScheme_of_smooth G.hom
  exact GlobalTheory.NormalDescent.isAmpleLB_of_pull G.left G'.left π ⟨⟩
    (fun x => ⟨hN.1 x, hN.2 x⟩) inferInstance hs.surj L hL hA

end GlobalTheory.AmpleFiniteBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGenericSemiAb

theorem isAmpleLB_of_generic_of_symm (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R]
    (hc : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (hA : IsAbelianScheme ((Over.pullback (jK R)).obj G)) (L : LB G.left) (hL : L.IsLB)
    (hLK : RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))))
    (hs : LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L) : IsAmpleLB L := by
  obtain ⟨M, hMa, hMs⟩ := GlobalTheory.T.exists_ample_symmetric_lineBundle_semiAbelian R G hG hA
  have hMK : RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) := by
    have : IsProper ((Over.pullback (jK R)).obj G).hom := hA.proper
    have h1 : IsAffineHom (jK R) := by unfold jK; infer_instance
    have : IsAffineHom (pullback.fst G.hom (jK R)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback G.hom (jK R)).flip h1
    exact (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_linComb hMa.isLB _ _)).2
      (hMa.pull_of_isAffineHom _)
  obtain ⟨R', _, _, _, _, _, ρ, G', _, π, hinj, hfin, hpb, N, a₀, r, a, β, hN, ha₀, -, hiso⟩ :=
    GlobalTheory.T.exists_finiteNormalCover_symmBundle_power_decomposition R hc G hG hA L M hL hMa.isLB hLK hMK hs hMs
  have : IsFinite π := by
    have : IsFinite (spMap ρ) := by
      unfold spMap
      rw [IsFinite.SpecMap_iff]; exact hfin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.1.flip this
  have hamp := GlobalTheory.AmplePowLinComb.isAmpleLB_of_lbPow_lbIso_linComb _ (L.pull π) (M.pull π)
    (hMa.pull_of_isFinite π) (LB.isLB_linComb hL _ _) N a₀ r a (fun i => (β i).left) hN ha₀ hiso
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  exact GlobalTheory.AmpleFiniteBase.isAmpleLB_of_pull R R' ρ hinj hfin G G' π hG hpb L hL hamp

theorem isAmpleLB_of_generic : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R],
    IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB →
    RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) →
    LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L :=
  fun R _ _ _ _ hc G _ hG hA L hL hLK hs => isAmpleLB_of_generic_of_symm R hc G hG hA L hL hLK hs

end GlobalTheory.AmpleGenericSemiAb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic | exact GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic | (intros; apply GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetricOfSymmetricGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetricOfSymmetricGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGenericExt

theorem symm_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  intro R _ _ _ _ _ G _ hG L hL h
  have e := GlobalTheory.SymBaseChange.inv_left_fst _ _ G (jK R)
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R))
    (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom (jK R)) e
  refine GlobalTheory.GenericDec.lbIso_of_generic G hG (pull_isLB hL _) hL ?_
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h2)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h1 h)

end GlobalTheory.SymGenericExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetricOfSymmetricGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_symmetric_of_symmetric_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  first | exact @GlobalTheory.SymGenericExt.symm_of_generic | exact GlobalTheory.SymGenericExt.symm_of_generic | (intros; apply GlobalTheory.SymGenericExt.symm_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.PullOpen

open GlobalTheory.Cartier.DomPull

theorem isDominant_of_gen {X V : Scheme.{0}} [IsIntegral X] (φ : V ⟶ X) (v : V)
    (hv : φ v = genericPoint X) : IsDominant φ := by
  refine ⟨?_⟩
  have hd : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)

theorem gp_apply {X : Scheme.{0}} [IsIntegral X] (q : Sp X.functionField) : gp X q = genericPoint X := by
  have h1 : gp X q ⤳ genericPoint X := by
    have : gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact (h1.antisymm (genericPoint_specializes _)).eq

theorem ffm_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {V : Y.Opens} [IsIntegral V.toScheme]
    [IsDominant V.ι] {φ : V.toScheme ⟶ X} [IsDominant φ] {θ : X.functionField →+* Y.functionField}
    (h : PFF V.ι φ θ) : (GlobalTheory.functionFieldMap V.ι).comp θ = GlobalTheory.functionFieldMap φ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, h₁]
    exact GlobalTheory.specMap_functionFieldMap V.ι
  have e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X =
      Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X := by
    refine Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← h₂]
    rw [← Category.assoc, e1]
  haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))

theorem lbIso_pull : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (φ : V.toScheme ⟶ X)
    (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D₁ : CartierDiv Y),
    PFF V.ι φ θ → PPull V.ι φ θ D D₁ → LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := by
  intro X Y _ _ V φ θ D D₁ hF hP
  obtain ⟨l, h₁, h₂⟩ := hF
  obtain ⟨q⟩ : Nonempty (Sp Y.functionField) := inferInstance
  haveI : Nonempty V := ⟨l q⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by
    rw [← Scheme.Hom.comp_apply, h₁, gp_apply])
  haveI : IsDominant φ := isDominant_of_gen φ (l q) (by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])
  have key := ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩
  have hE : pullback V.ι D₁ = pullback φ D := CartierDiv.ext_of_isEqn fun v => by
    obtain ⟨g, hg⟩ := D.exists_isEqn (φ v)
    refine ⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩
    have := isEqn_pullback V.ι D₁ (hP v g hg)
    convert this using 1
    ext
    simp only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm
  exact (presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)

end GlobalTheory.Desc.PullOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.GenericFibreChart

theorem isPullback_of_fac_mono {C : Type*} [Category C] {P V G S T : C} {p : P ⟶ G} {q : P ⟶ T}
    {h : G ⟶ S} {j : T ⟶ S} (H : IsPullback p q h j) (i : V ⟶ G) [Mono i] (l : P ⟶ V)
    (hl : l ≫ i = p) : IsPullback l q (i ≫ h) j := by
  have w : l ≫ i ≫ h = q ≫ j := by rw [← Category.assoc, hl, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ i) s.snd (by rw [Category.assoc]; exact s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    rw [← cancel_mono i, Category.assoc, hl, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, ← h1, Category.assoc, hl]
    · rw [H.lift_snd, h2]

theorem isPullback_of_comp_mono {C : Type*} [Category C] {P X Y W Z : C} {p : P ⟶ X} {q : P ⟶ Y}
    {a : X ⟶ W} {g : Y ⟶ W} (m : W ⟶ Z) [Mono m] (H : IsPullback p q (a ≫ m) (g ≫ m)) :
    IsPullback p q a g := by
  have w : p ≫ a = q ≫ g := by
    rw [← cancel_mono m, Category.assoc, Category.assoc, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift s.fst s.snd (by
      rw [← Category.assoc, ← Category.assoc, s.condition])) ?_ ?_ ?_⟩⟩
  · intro s
    exact H.lift_fst _ _ _
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, h1]
    · rw [H.lift_snd, h2]

theorem exists_isPullback_generic :
    ∀ (R₀ : Type) [CommRing R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) (R : Type)
      [CommRing R] [IsDomain R] (ρ : R₀ →+* R), ρ f ≠ 0 →
      ∀ (G : Over (Sp R)) (V : G.left.Opens) (φ : V.toScheme ⟶ A.left),
      (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) →
      IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ GlobalTheory.Desc.awayMap f) (spMap ρ) →
      ∃ (g : Sp (FractionRing R) ⟶ Sp (Localization.Away f))
        (l : pullback G.hom (jK R) ⟶ V.toScheme),
        l ≫ V.ι = pullback.fst G.hom (jK R) ∧
          IsPullback (l ≫ φ) (pullback.snd G.hom (jK R)) A.hom g := by
  intro R₀ _ f A R _ _ ρ hf G V φ hV hP
  have hu : IsUnit (((algebraMap R (FractionRing R)).comp ρ) f) := by
    rw [isUnit_iff_ne_zero, RingHom.comp_apply]
    exact fun h => hf ((IsFractionRing.injective R (FractionRing R)) (by rw [h, map_zero]))
  let ψ : Localization.Away f →+* FractionRing R := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R₀ (Localization.Away f)) =
      (algebraMap R (FractionRing R)).comp ρ := IsLocalization.Away.lift_comp f hu
  have hg : spMap ψ ≫ GlobalTheory.Desc.awayMap f = jK R ≫ spMap ρ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
  have hr : Set.range (pullback.fst G.hom (jK R)) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (hV _).2 ?_
    have hx : G.hom (pullback.fst G.hom (jK R) x) = jK R (pullback.snd G.hom (jK R) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [hx]
    intro hmem
    have hmem' : algebraMap R (FractionRing R) (ρ f) ∈
        (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).asIdeal := hmem
    exact (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem' hu)
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  refine ⟨spMap ψ, IsOpenImmersion.lift V.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have h1 := isPullback_of_fac_mono (IsPullback.of_hasPullback G.hom (jK R)) V.ι
    (IsOpenImmersion.lift V.ι _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h2 := h1.paste_horiz hP
  refine isPullback_of_comp_mono (GlobalTheory.Desc.awayMap f) ?_
  rw [hg]
  exact h2

end GlobalTheory.GenericFibreChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGrpPull

theorem inv_left_comp {S T : Scheme.{0}} (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S)
    (α : B.left ⟶ A.left) (h : IsGrpPullback B A y α) :
    (GrpObj.inv : B ⟶ B).left ≫ α = α ≫ (GrpObj.inv : A ⟶ A).left := by
  have hw : α ≫ A.hom = B.hom ≫ y := h.1.w
  let f : (B ⟶ B) → (Over.mk (B.hom ≫ y) ⟶ A) := fun x =>
    Over.homMk (x.left ≫ α) (by
      change (x.left ≫ α) ≫ A.hom = B.hom ≫ y
      rw [Category.assoc, hw, ← Category.assoc, Over.w x])
  have hmul : ∀ x z : B ⟶ B, f (x * z) = f x * f z := fun x z =>
    Over.OverMorphism.ext (h.2 B x z (f x) (f z) rfl rfl).symm
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [← hmul, _root_.mul_one, _root_.mul_one]
    exact mul_left_cancel e
  have hinv : f (𝟙 B)⁻¹ = (f (𝟙 B))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, _root_.inv_mul_cancel, h1]
  have e := congrArg CommaMorphism.left hinv
  have e' : ((𝟙 B ≫ GrpObj.inv : B ⟶ B)).left ≫ α = (f (𝟙 B) ≫ GrpObj.inv).left := e
  simpa [f] using e'

theorem symm_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  intro S T A _ B _ y α h L hL hs
  have e := inv_left_comp A B y α h
  have h1 := GenSpread.lbIso_pull_pull hL (a := α) (GrpObj.inv : B ⟶ B).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : A ⟶ A).left) α e
  have h3 := GenSpread.lbIso_pullback hs α
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymGrpPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  first | exact @GlobalTheory.SymGrpPull.symm_pull | exact GlobalTheory.SymGrpPull.symm_pull | (intros; apply GlobalTheory.SymGrpPull.symm_pull <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_pullback_of_isPullback : ∀ (S T S' : Scheme.{0}) (G : Over S) [GrpObj G] (t : T ⟶ S) (A : Over S') [GrpObj A] (a : pullback G.hom t ⟶ A.left) (g : T ⟶ S'), IsSemiAbelian G → IsAbelianScheme A → IsPullback a (pullback.snd G.hom t) A.hom g → IsAbelianScheme ((Over.pullback t).obj G) := by
  intro S T S' G _ t A _ a g hG hA sq
  exact
  { comm := by have := hG.comm; infer_instance
    smooth := by have := hG.smooth; change Smooth (pullback.snd G.hom t); infer_instance
    proper := by
      have := hA.proper; change IsProper (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    geomConnected := by
      have := hA.geomConnected; change GeometricallyConnected (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq inferInstance }

theorem ampleDiv_closure_on_chart : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ D : CartierDiv A.left, AmpleDiv D → LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (ρ : R₀ →+* R), ρ.Flat → ρ f ≠ 0 → ∀ (G : Over (Sp R)) [GrpObj G] [IsIntegral G.left], IsSemiAbelian G → ∀ (V : G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* G.left.functionField) (D₁ : CartierDiv G.left), (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) → IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ awayMap f) (spMap ρ) → ∀ (y : Sp (FractionRing R) ⟶ Sp (Localization.Away f)) (α : pullback G.hom (jK R) ⟶ A.left), IsGrpPullback ((Over.pullback (jK R)).obj G) A y α → (∀ (T : Scheme.{0}) (t : T ⟶ pullback G.hom (jK R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ α = t' ≫ φ) → PFF V.ι φ θ → PPull V.ι φ θ D D₁ → AmpleDiv D₁ := by
  intro R₀ _ _ f A _ _ hA D hD hsym R _ _ _ _ hR ρ hflat hρf G _ _ hG V φ θ D₁ hV hsq y α hα hcomp hff hpp
  obtain ⟨g, l, hl, sq⟩ := GlobalTheory.GenericFibreChart.exists_isPullback_generic R₀ f A R ρ hρf G V φ hV hsq
  have hGK : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    isAbelianScheme_pullback_of_isPullback _ _ _ G (jK R) A (l ≫ φ) g hG hA sq
  haveI : IsProper ((Over.pullback (jK R)).obj G).hom := hGK.proper
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hAD : IsAmpleLB (toLB D) := (ampleDiv_iff_isAmpleLB A.left D).1 hD
  have h1 : IsAmpleLB ((toLB D).pull (l ≫ φ)) := hAD.pull_of_isPullback sq
  have h3 : LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := GlobalTheory.Desc.PullOpen.lbIso_pull _ _ V φ θ D D₁ hff hpp
  have hL₁ := isLB_toLB D₁
  have h4 : LBIso ((toLB D₁).pull (pullback.fst G.hom (jK R))) ((toLB D).pull (l ≫ φ)) := by
    rw [← hl]
    exact LBIso.trans (LB.isLB_pull hL₁ _) (LB.isLB_pull (LB.isLB_pull hL₁ _) _)
      (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL₁ V.ι l).symm
      (LBIso.trans (LB.isLB_pull (LB.isLB_pull hL₁ _) _) (LB.isLB_pull (LB.isLB_pull (isLB_toLB D) _) _)
        (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.Mum.UExt.lbIso_pull h3 l)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (isLB_toLB D) φ l))
  have h5 : IsAmpleLB ((toLB D₁).pull (pullback.fst G.hom (jK R))) := h1.of_lbIso (LB.isLB_pull hL₁ _) h4
  have h6 := (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_pull hL₁ _)).2 h5
  have hlα : α = l ≫ φ := by
    have := hcomp _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rwa [Category.id_comp] at this
  have hs1 := GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback _ _ A ((Over.pullback (jK R)).obj G) y α hα (toLB D) (isLB_toLB D) hsym
  rw [hlα] at hs1
  have hK₁ := LB.isLB_pull hL₁ (pullback.fst G.hom (jK R))
  have hK := LB.isLB_pull (isLB_toLB D) (l ≫ φ)
  have hs2 : LBIso (((toLB D₁).pull (pullback.fst G.hom (jK R))).pull
      (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left)
      ((toLB D₁).pull (pullback.fst G.hom (jK R))) :=
    LBIso.trans (LB.isLB_pull hK₁ _) (LB.isLB_pull hK _) hK₁ (GlobalTheory.Mum.UExt.lbIso_pull h4 _)
      (LBIso.trans (LB.isLB_pull hK _) hK hK₁ hs1 h4.symm)
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hs3 := GlobalTheory.T.lineBundle_symmetric_of_symmetric_generic_fibre R G hG (toLB D₁) hL₁ hs2
  have h7 := GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian R hR G hG hGK (toLB D₁) hL₁ h6 hs3
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  exact (ampleDiv_iff_isAmpleLB G.left D₁).2 h7

end GlobalTheory.Desc

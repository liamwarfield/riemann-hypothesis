module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRigidifiedTwist
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.RigidifyTwist

open CechPic

theorem pull_cls_eq_zero {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (r : Z ⟶ X) (i : L.ι)
    (hi : ∀ z, r z ∈ L.U i) : CechPic.pull r (cls L hL) = 0 := by
  rw [← cls_pull hL r (pull_isLB hL r), cls_eq_zero_iff]
  refine (iso_triv_iff _).1 (iso_of_chart (pull_isLB hL r) ⟨fun _ _ => i, fun _ y _ => mem_pull.2 (hi y), ?_⟩)
  intro y p q hp hq
  rw [gm_pull_g L r (𝟙 Z) y (fun _ => i) (fun _ => i) (mem_pull.2 (hi y)) (mem_pull.2 (hi y))]
  have hy : (𝟙 Z ≫ r) y ∈ L.U i := by
    simpa using hi y
  rw [gm_self hL _ y hy]
  exact map_one _

theorem eSec_hom {S : Scheme.{0}} (A : Over S) [GrpObj A] : eSec A ≫ A.hom = 𝟙 S := by
  unfold eSec
  exact (Over.w _).trans rfl

private theorem cls_pull_tens_dual_eq_sub {S Y : Scheme.{0}} (A : Over S) (M : LB A.left) (hM : M.IsLB) (N : LB S)
    (hN : N.IsLB) (f : Y ⟶ A.left) (h : ((tens M (dual (N.pull A.hom))).pull f).IsLB) :
    cls _ h = pull f (cls M hM) - pull (f ≫ A.hom) (cls N hN) := by
  have hP := pull_isLB hN A.hom
  rw [cls_pull (isLB_tens hM (isLB_dual hP)) f h, cls_tens hM (isLB_dual hP), cls_dual hP,
    cls_pull hN A.hom, map_add, map_neg, pull_comp, sub_eq_add_neg]

private theorem pGen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) : PGen w := by
  intro Y f y j1 j2 k1 k2 h1 h2 h3 h4
  unfold gw
  have m1 : f y ∈ (L.pull F).U (fun _ => j1) := mem_pull.2 h1
  have m2 : f y ∈ (L.pull F).U (fun _ => j2) := mem_pull.2 h2
  have hV : f y ∈ ((L.pull F).div L').U (fun _ => j1, k1) ⊓ ((L.pull F).div L').U (fun _ => j2, k2) :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j1, k1) (fun _ => j2, k2))
  rw [map_mul, gm_res f y _ hV, gm_res f y _ hV, gm_div' (L.pull F) L' f y _ _ ⟨m1, h3⟩ ⟨m2, h4⟩,
    gm_pull_g L F f y _ _ m1 m2] at e
  exact e

private theorem lbIso_tens_dual_pull_eSec_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB)
    (U : S.Opens) (j : (M.pull (eSec A)).ι) (hU : U ≤ (M.pull (eSec A)).U j) :
    LBIso ((tens M (dual ((M.pull (eSec A)).pull A.hom))).pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hT := isLB_tens hM (isLB_dual (pull_isLB hN A.hom))
  have hz : ∀ z : U.toScheme, U.ι z ∈ (M.pull (eSec A)).U j := fun z => by
    exact hU z.2
  refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
  rw [cls_pull_tens_dual_eq_sub A M hM _ hN, ← morphismRestrict_ι, pull_comp, pull_cls_eq_zero hN U.ι j hz, map_zero,
    sub_zero, cls_pull hM]

theorem exists_rigidified_twist : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left), M.IsLB → ∃ M' : LB A.left, M'.IsLB ∧ Out.Rigidified A M' ∧ (∀ p : S, ∃ U : S.Opens, p ∈ U ∧ LBIso (M'.pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι)) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), φ ≫ A.hom = π ≫ x → LBIso (M'.pull φ) (M.pull φ)) ∧ (IsProper A.hom → Out.RelAmple A M → Out.RelAmple A M') := by
  intro S A _ M hM
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hP : ((M.pull (eSec A)).pull A.hom).IsLB := pull_isLB hN _
  have hT : (tens M (dual ((M.pull (eSec A)).pull A.hom))).IsLB := isLB_tens hM (isLB_dual hP)
  refine ⟨tens M (dual ((M.pull (eSec A)).pull A.hom)), hT, ?_, ?_, ?_, ?_⟩
  · unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hT _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, eSec_hom A, pull_id, cls_pull hM (eSec A) hN, sub_self]
  · intro p
    obtain ⟨j, hj⟩ := exists_chart hN p
    exact ⟨_, hj, lbIso_tens_dual_pull_eSec_restrict A M hM _ j le_rfl⟩
  · intro K _ x X φ π hφ
    obtain ⟨j, hj⟩ := exists_chart hN (x (Classical.arbitrary (Sp K)))
    have hx : ∀ z, x z ∈ (M.pull (eSec A)).U j := fun z => by
      rw [Subsingleton.elim z (Classical.arbitrary _)]
      exact hj
    refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, hφ, pull_comp, pull_cls_eq_zero hN x j hx, map_zero, sub_zero, cls_pull hM]
  · intro hpr hamp
    have := hpr
    refine AmpleLocal.relAmple_of_locally S A _ hT inferInstance inferInstance fun s => ?_
    obtain ⟨j, hj⟩ := exists_chart hN s
    obtain ⟨V, hV, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hj
    obtain ⟨w, hw⟩ := lbIso_tens_dual_pull_eSec_restrict A M hM V j hVle
    have hpw : PGen w := pGen_of_isGen w hw
    exact ⟨V, hsV, relAmple_pull (A' := Over.mk (A.hom ∣_ V)) (isPullback_morphismRestrict A.hom V).flip hM
      (pull_isLB hT _) (w := w) hpw V hV (fun y => y.2) hamp⟩

end GlobalTheory.RigidifyTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.EffectiveCube

theorem unitAt_pull {X Y : Scheme.{0}} {N : LB X} (s : N.Sec) (φ : Y ⟶ X) (y : Y)
    (h : φ y ∈ Out.nonzeroLocus s) : UnitAt N (K := PUnit) (fun _ => φ) (fun _ => 1) y := by
  have h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact h
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h'
  exact ⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩

theorem exists_mem_of_unitAt {X Y : Scheme.{0}} {N : LB X} (hN : N.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt N φ ε y) :
    ∃ u : (LB.LinComb N φ ε).Sec, y ∈ Out.nonzeroLocus u := by
  obtain ⟨u, hu⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)
  exact ⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩

theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] [JacobsonSpace X] (M : LB X)
    (h : ∀ y : X, IsClosed {y} → ∃ u : M.Sec, y ∈ Out.nonzeroLocus u) :
    ∃ (r : ℕ) (u : Fin r → M.Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X) := by
    intro y _
    by_contra hy
    have ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)) :=
      isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints
      (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed
    obtain ⟨u, hu⟩ := h c hcl
    exact hc (Set.mem_iUnion.2 ⟨u, hu⟩)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hy

theorem exists_sections_cube_cover :
    (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro hcube K _ _ P N s hN ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hcube _ P N hN
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip
  have : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let π : P.A ⟶ T := Over.homMk P.A.hom (Category.comp_id _)
  have hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply P.A.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)
  have good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end GlobalTheory.EffectiveCube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVarietyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.EffectiveCube.exists_sections_cube_cover | exact GlobalTheory.EffectiveCube.exists_sections_cube_cover | (intros; apply GlobalTheory.EffectiveCube.exists_sections_cube_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLinComb
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingComb

open CommutatorPairing

theorem exists_gen_linComb {X X' Y' : Scheme.{0}} {D : LB X} {I K : Type} [Fintype I] [Fintype K]
    (F : I → (X' ⟶ X)) (e : I → ℤ) (ψ : K → (Y' ⟶ X')) (ε : K → ℤ) {Y : I → Scheme.{0}} (h : ∀ i, Y' ⟶ Y i)
    (φ : ∀ i, K → (Y i ⟶ X)) (hc : ∀ i k, ψ k ≫ F i = h i ≫ φ i k)
    (t : ∀ i, LB.Gen (LB.LinComb D (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb D F e) ψ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₀ : (Z ⟶ X) → D.ι), Good D z J₀ →
        val u r z (fun χ i => J₀ (χ ≫ F i)) = ∏ i, val (t i) (r ≫ h i) z J₀ ^ e i := by
  have le : ∀ (jj : K → I → D.ι) (i : I), LB.wchart (LB.LinComb D F e) ψ jj ≤
      h i ⁻¹ᵁ LB.wchart D (φ i) (fun k => jj k i) := fun jj i y hy => Set.mem_iInter.2 fun k => by
    have h₁ : (ψ k ≫ F i) y ∈ D.U (jj k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
    rw [hc] at h₁
    exact h₁
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jj : K → I → D.ι), r z ∈ LB.wchart (LB.LinComb D F e) ψ jj →
      gm r z (LB.wchart (LB.LinComb D F e) ψ jj) (∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i) =
        ∏ i, gm (r ≫ h i) z (LB.wchart D (φ i) fun k => jj k i) ((t i).s fun k => jj k i) ^ e i := by
    intro Z r z jj hz
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, gm_res r z _ hz]
    exact congrArg (· ^ e i) (gm_pull r (h i) z _ (le jj i hz) _)
  refine ⟨⟨fun jj => ∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i⟩,
    (CechPic.isGen_iff_germ _).2 fun y j j' hj hj' => ?_, fun Z r z J₀ hJ => ?_⟩
  · refine (v _ (𝟙 Y') y j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_linComb (LB.LinComb D F e) ψ ε (𝟙 Y') y j j' hj hj') (v _ (𝟙 Y') y j' hj')).symm)
    have a : ∀ i, gm (𝟙 Y' ≫ h i) y (LB.wchart D (φ i) fun k => j k i) ((t i).s fun k => j k i) = _ := fun i =>
      gen_trans (ht i) (𝟙 Y' ≫ h i) y (le j i hj) (le j' i hj')
    have b : ∀ k, _ := fun k => gm_linComb D F e (𝟙 Y' ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)
    simp only [a, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    refine Eq.trans ?_ (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (b k)).symm
    simp only [trF, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, hc]
    rw [Finset.prod_comm]
    simp only [mul_comm]
  · have hz : r z ∈ LB.wchart (LB.LinComb D F e) ψ (fun k i => J₀ ((r ≫ ψ k) ≫ F i)) :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => hJ ((r ≫ ψ k) ≫ F i)
    refine (v Z r z _ hz).trans (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_)
    exact (val_of (t i) (r ≫ h i) z J₀ _ fun k => by rw [Category.assoc, Category.assoc, hc]).symm

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] {D : LB A.left} {I : Type} [Fintype I]

theorem exists_theta_linComb (φ : I → (G ⟶ A)) (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S}
    {T' : I → Over S} (m : ∀ i, T ⟶ T' i) (x : T ⟶ G) (θ₀ : ∀ i, ThetaGrp A D n (T' i))
    (hx : ∀ i, m i ≫ (θ₀ i).pt = x ≫ φ i) :
    ∃ θ : ThetaGrp G (LB.LinComb D (fun i => (φ i).left) e) n T, θ.pt = x ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ G) (z : Z.left) (J₀), Good D z J₀ →
        thetaVal θ t a z (fun χ i => J₀ (χ ≫ (φ i).left)) = ∏ i, thetaVal (θ₀ i) (t ≫ m i) (a ≫ φ i) z J₀ ^ e i := by
  have hc : ∀ i (k : Fin 2), ![(snd T G).left, (translPt G x).left] k ≫ (φ i).left =
      (lift (fst T G ≫ m i) (snd T G ≫ φ i)).left ≫ ![(snd (T' i) A).left, (translPt A (θ₀ i).pt).left] k := by
    intro i k
    have := hφ i
    fin_cases k
    · exact congrArg CommaMorphism.left (lift_snd (fst T G ≫ m i) (snd T G ≫ φ i)).symm
    · refine congrArg CommaMorphism.left (?_ : translPt G x ≫ φ i = _ ≫ translPt A (θ₀ i).pt)
      rw [lift_translPt, Category.assoc, hx]
      show ((fst T G ≫ x) * snd T G) ≫ φ i = _
      rw [MonObj.mul_comp, Category.assoc]
  obtain ⟨u, hu, hv⟩ := exists_gen_linComb (fun i => (φ i).left) e _ ![n, -n] _ _ hc (fun i => (θ₀ i).φ)
    (fun i => (θ₀ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J₀ hJ => (hv _ (lift t a).left z J₀ hJ).trans ?_⟩
  refine Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  rfl

theorem weilIs_linComb (hG : GlobalFnsSt) (hA : IsAbelianScheme G) (hD : D.IsLB) (φ : I → (G ⟶ A))
    (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S} {x y : T ⟶ G} (c : I → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A D n (x ≫ φ i) (y ≫ φ i) (c i)) :
    WeilIs G (LB.LinComb D (fun i => (φ i).left) e) n x y (∏ i, c i ^ e i) := by
  have hL := LB.isLB_linComb hD (fun i => (φ i).left) e
  refine WeilIsogeny.weilIs_of_local hG hA hL fun p => ?_
  choose V hV H using fun i => h i p
  choose θx₀ θy₀ ex ey using fun i => (H i).1
  let V₀ : T.left.Opens := ⟨⋂ i, (V i : Set T.left), isOpen_iInter_of_finite fun i => (V i).isOpen⟩
  have le : ∀ i, V₀ ≤ V i := fun i _ hz => Set.mem_iInter.1 hz i
  obtain ⟨θx, fx, vx⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ x) θx₀
    (fun i => by rw [ex, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ y) θy₀
    (fun i => by rw [ey, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨c', hc'⟩ := exists_commIsOf hG hA hL θx θy
  refine ⟨V₀, Set.mem_iInter.2 hV, θx, θy, fx, fy, ?_⟩
  obtain rfl : c' = unitRes V₀ (∏ i, c i ^ e i) := by
    refine unit_ext fun z _ => ?_
    choose J₀ hJ₀ using fun χ : (overRes V₀).left ⟶ A.left => exists_chart hD (χ z)
    have e₁ := (commIsOf_iff hL _ _ _).1 hc' _ (𝟙 _) 1 z (fun χ i => J₀ (χ ≫ (φ i).left))
      (fun χ => Set.mem_iInter.2 fun i => hJ₀ (χ ≫ (φ i).left))
    have e₂ : ∀ i, _ := fun i => (commIsOf_iff hD _ _ _).1 ((H i).2 (θx₀ i) (θy₀ i) (ex i) (ey i)) _
      (𝟙 _ ≫ overLE (le i)) (1 ≫ φ i) z J₀ hJ₀
    have gx : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θx₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θx.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ex, fx, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have gy : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θy₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θy.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ey, fy, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have e₃ : ∀ i, gm (𝟙 _ ≫ overLE (le i)).left z ⊤ (unitRes (V i) (c i)) = gm (𝟙 _ ≫ V₀.ι) z ⊤ (c i) := fun i => by
      refine (gm_unitRes (V i) (c i) _ z).trans ?_
      exact congrArg (fun q => gm q z ⊤ (c i)) (congrArg CommaMorphism.left
        ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) (overLE_ι (le i)))))
    refine e₁.symm.trans (Eq.trans ?_ (gm_unitRes V₀ _ (𝟙 _) z).symm)
    unfold commVal
    rw [vx _ _ _ _ _ hJ₀, vx _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, map_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← e₃, ← e₂, commVal, gx, gy]
    simp only [mul_zpow, inv_zpow]
  exact hc'

end GlobalTheory.PairingComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsValuesLineFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HZeroPullbackFieldConstant
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.HolSec

theorem exists_sec_pull {X X' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (W : X.Opens) (mem : ∀ x, F x ∈ W)
    (θ₀ : ∀ j, Γ(X, W ⊓ L.U j)) (hθ₀ : θ₀ ∈ secOn L W) :
    ∃ t : LB.Sec (L.pull F), ∀ j (x : Sp ℂ ⟶ X'), ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull F).U (fun _ => j)) (t.f (fun _ => j)) = valAt' (x ≫ F) (W ⊓ L.U j) (θ₀ j) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ (W ⊓ L.U (J PUnit.unit)) := fun J x hx => ⟨mem x, mem_pull.1 hx⟩
  have ev : ∀ y J, y ∈ (L.pull F).U J → gs (𝟙 _) y _ ((F.appLE _ _ (le J)).hom (θ₀ _)) = gs F y _ (θ₀ (J PUnit.unit)) :=
    fun y J h => (gs_appLE F _ _ (le J) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ₀ _), fun J J' => fn_ext fun y hy => ?_⟩, fun j x hx => ?_⟩
  · have h := mem_pull.1 hy.1
    have h' := mem_pull.1 hy.2
    have hm : F y ∈ W ⊓ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨⟨mem y, h⟩, h'⟩
    have e := congrArg (gs F y _) (hθ₀ (J PUnit.unit) (J' PUnit.unit))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y (L.U _ ⊓ L.U _) ⟨h, h'⟩] at e
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, ev y J hy.1, ev y J' hy.2,
      gm_pull_g L F (𝟙 _) y J J' hy.1 hy.2, Category.id_comp]
    exact e
  · exact valAt'_appLE x F _ _ (le _) _ (fun p hp => mem_pull.2 (hx hp))

end GlobalTheory.HolSec
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open scoped Matrix Topology

namespace GlobalTheory.ThetaFamily

theorem exists_values_line (hT : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) :
    ∃ v : P.L.ι → (Sp ℂ ⟶ P.A.left) → ℂ, ∀ s : P.L.Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ P.A.left), x ≫ P.A.hom = 𝟙 _ →
      ⊤ ≤ x ⁻¹ᵁ P.L.U i → valAt' x (P.L.U i) (s.f i) = a * v i x := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  refine ⟨fun i x => valAt' x _ ((β i₀).f (fun _ => i)), fun s => ?_⟩
  obtain ⟨a, ha, -⟩ := hβ (secToPow s 1)
  refine ⟨a i₀, fun i x hx hi => ?_⟩
  have hi' : ⊤ ≤ x ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
  have e := (congrArg (valAt' x _) ((ha (fun _ => i)).trans (su _))).trans ((valAt'_mul x _ _ _).trans
    (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi')))
  refine Eq.trans ?_ e
  exact ((valAt'_res x _ (s.f i ^ 1) hi').trans (by rw [pow_one])).symm

theorem exists_values_line_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (z : Sp ℂ ⟶ S) :
    ∃ v : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).ι → (Sp ℂ ⟶ pullback o.t.G.hom z) → ℂ,
      ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ pullback o.t.G.hom z),
        x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i →
        valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i) (s.f i) = a * v i x := by
  have h := isGrpPullback_pullback o.t.G z
  obtain ⟨hL, hr, ⟨c', w, g, -⟩, hs⟩ := Out.CubePf.cubePull S _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have := o.t.semi.smooth
  have : Smooth ((Over.pullback z).obj o.t.G).hom :=
    MorphismProperty.of_isPullback (P := @Smooth) h.1 o.t.semi.smooth
  obtain ⟨am, kt⟩ := amplePt _ _ z _ _ _ h _ _ o.t.PP.isLB hL ⟨w, g⟩ o.ample o.ktriv
  have := o.t.semi.geomConnected
  have : GeometricallyConnected ((Over.pullback z).obj o.t.G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 o.t.semi.geomConnected
  have : ConnectedSpace ((Over.pullback z).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback z).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback z).obj o.t.G).hom
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback z).obj o.t.G).hom
    (eSec ((Over.pullback z).obj o.t.G) (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  exact exists_values_line hT
    { A := (Over.pullback z).obj o.t.G, g := d, smoothDim := hd, L := o.t.PP.L.pull (pullback.fst o.t.G.hom z),
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨_, hr⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

theorem exists_ratio_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (u : Sp ℂ ⟶ S) (V : S.Opens) (θ₀ : ∀ j, Γ(o.t.G.left, o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j))
    (hθ₀ : θ₀ ∈ secOn o.t.PP.L (o.t.G.hom ⁻¹ᵁ V))
    (nz : ∀ y ∈ V, ∃ (x : o.t.G.left) (j : o.t.PP.L.ι), o.t.G.hom x = y ∧ x ∈ o.t.G.left.basicOpen (θ₀ j))
    (hu : ⊤ ≤ u ⁻¹ᵁ V) (σ : LB.Sec (o.t.PP.L.pull (pullback.fst o.t.G.hom u))) :
    ∃ a : ℂ, ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u),
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j)) (σ.f (fun _ => j)) =
        a * valAt' (x ≫ pullback.fst _ _) (o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j) (θ₀ j) := by
  have := o.t.semi.smooth
  have mem : ∀ x, pullback.fst o.t.G.hom u x ∈ o.t.G.hom ⁻¹ᵁ V := fun x =>
    (congrArg (fun q => q x ∈ V) (pullback.condition (f := o.t.G.hom) (g := u))).mpr (hu (Set.mem_univ _))
  obtain ⟨t, ht⟩ := HolSec.exists_sec_pull o.t.PP.L _ _ mem θ₀ hθ₀
  obtain ⟨v, hv⟩ := exists_values_line_fibre hT o u
  obtain ⟨g₀, j₀, hg₀, hb₀⟩ := nz _ (hu (Set.mem_univ (default : PrimeSpectrum ℂ)))
  obtain ⟨g, hg₁, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback o.t.G.hom u) g₀ _ hg₀
  obtain ⟨x₀, hx₀, hx₁⟩ := ComplexPoints.exists_point_mem (pullback.snd o.t.G.hom u)
    (Z := (pullback.fst o.t.G.hom u ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) : Scheme.Opens _))
    (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨g, by
      show pullback.fst o.t.G.hom u g ∈ o.t.G.left.basicOpen (θ₀ j₀)
      rw [hg₁]; exact hb₀⟩
  have hx₂ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) := fun p _ => hx₁ p
  obtain ⟨c, hc⟩ := hv t
  obtain ⟨a, ha⟩ := hv σ
  have m : ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u), ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j) := fun j x h p hp => mem_pull.2 (h hp)
  have hj₀ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.PP.L.U j₀ :=
    top_le_preimage_mono _ ((o.t.G.left.basicOpen_le _).trans inf_le_right) hx₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine (top_le_preimage_basicOpen_iff _ _ _).1 hx₂ ?_
    rw [← ht j₀ x₀ hj₀, hc _ x₀ hx₀ (m _ _ hj₀), zero_mul]
  refine ⟨a / c, fun j x h₁ h₂ => ?_⟩
  rw [← ht j x h₂, hc _ x h₁ (m _ _ h₂), ha _ x h₁ (m _ _ h₂)]
  field_simp

theorem exists_sec_const_mul {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp ℂ) (s : L.Sec) (a : ℂ) :
    ∃ t : L.Sec, ∀ i (x : Sp ℂ ⟶ X), x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i →
      valAt' x (L.U i) (t.f i) = a * valAt' x (L.U i) (s.f i) := by
  refine ⟨⟨fun i => constFn p _ a * s.f i, fun i j => ?_⟩, fun i x hx hi =>
    (valAt'_mul x _ _ _).trans (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi))⟩
  rw [map_mul, map_mul, s.compat i j, mul_left_comm]
  congr 2
  have r : ∀ (U W : X.Opens) (h : W ≤ U), (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p W a :=
    fun U W h => (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op) :)
  rw [r, r]

theorem thetaChar_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ≠ 0 := by
  have hs : ((2 : ℂ)⁻¹ • (τ + τᵀ)).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hi : ((2 : ℂ)⁻¹ • (τ + τᵀ)).map Complex.im = τ.map Complex.im := by
    ext i j
    have := congrFun (congrFun hp.1 i) j
    simp at this
    simp [this]
    ring
  have h := CanTh.thetaChar_ne_zero hs (hi ▸ hp) a b
  have e : ∀ v : Fin g → ℂ, v ⬝ᵥ ((2 : ℂ)⁻¹ • (τ + τᵀ)) *ᵥ v = v ⬝ᵥ τ *ᵥ v := fun v => by
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm v (v ᵥ* τ), ← Matrix.dotProduct_mulVec, smul_eq_mul]
    ring
  unfold thetaChar at h ⊢
  simpa only [e] using h

end GlobalTheory.ThetaFamily
end
end

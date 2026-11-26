module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatKernelSymmetricBirigidifiedBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPair
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KerAxes

theorem triv_of_local_evc {S : Scheme.{0}} {G T : Over S} [GrpObj G] (hG : IsAbelianScheme G)
    {P : LB (G ⊗ G).left} (hP : P.IsLB) (h2 : Triv (ev P (𝟙 G) (1 : G ⟶ G))) (x : T ⟶ G)
    (hloc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over S) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ x) g = 0) :
    Triv (ev P (snd G T ≫ x) (fst G T)) := by
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (snd G T ≫ x) (fst G T))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (G ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (snd G T ≫ x) (fst G T)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd G T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hG T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, lift_snd_assoc, Category.id_comp, lift_fst]
    exact evc_one_right hP h2 x
  · intro p
    obtain ⟨V, hV, hz⟩ := hloc p
    refine ⟨V, hV, ?_⟩
    let U := (snd G T).left ⁻¹ᵁ V
    let Y : Over S := Over.mk (U.ι ≫ (G ⊗ T).hom)
    let i : Y ⟶ G ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, ← Category.assoc]
    exact hz Y _ _ (fun z ↦ z.2)

theorem triv_of_memKL_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  intro R _ _ G _ hG P hP h1 h2 hs T a b hx
  have hs' : (swap P).IsLB := pull_isLB hP _
  have h1' : Triv (ev P (1 : G ⟶ G) (𝟙 G)) := h1
  have h2' : Triv (ev P (𝟙 G) (1 : G ⟶ G)) := h2
  have add1 := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hG hG hP h1' h2')
  have add2 := (isAdditive_iff hs').1 (CubeNoeth.isAdditive_swap_of_triv_axes hG hG hP h1' h2')
  have symm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP v u = evc hP u v := by
    intro Y u v
    have e := congrArg (CechPic.pull (lift v u).left) ((cls_eq_iff hP hs').2 hs)
    exact e.trans (evc_swap hP hs' v u)
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over (Sp R)) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ a) g = 0 ∧ evc hP (t ≫ b) g = 0 := by
    intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    refine ⟨V, hV, fun Y t g ht ↦ ?_⟩
    have mk : ∀ u v : Y ⟶ G, evc hP ((t ≫ a) * u) ((t ≫ b) * v) = evc hP u v := by
      intro u v
      have e := pull_mul_eq hP hTV t ht (lift u v)
      have q : (t ≫ lift a b) * lift u v = lift ((t ≫ a) * u) ((t ≫ b) * v) := by
        ext <;> simp [MonObj.mul_comp]
      rw [q] at e
      exact e
    have e0 := mk 1 1
    rw [_root_.mul_one, _root_.mul_one, evc_one_left hP h1'] at e0
    constructor
    · have e1 := mk 1 g
      rw [_root_.mul_one, evc_one_left hP h1'] at e1
      have s := add2 Y (t ≫ b) g (t ≫ a)
      rw [evc_swap hP hs', evc_swap hP hs', evc_swap hP hs'] at s
      rw [s, e0, zero_add] at e1
      exact e1
    · have e3 := mk g 1
      rw [_root_.mul_one, evc_one_right hP h2'] at e3
      have s := add1 Y (t ≫ a) g (t ≫ b)
      rw [s, e0, zero_add] at e3
      rw [symm]
      exact e3
  refine ⟨triv_of_local_evc hG hP h2' a fun p ↦ ?_, triv_of_local_evc hG hP h2' b fun p ↦ ?_⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).1⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).2⟩

end GlobalTheory.KerAxes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPairStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.KerAxes.triv_of_memKL_pair | exact GlobalTheory.KerAxes.triv_of_memKL_pair | (intros; apply GlobalTheory.KerAxes.triv_of_memKL_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem retract_flat_of_finite (R : Type) [CommRing R] (H K : Over (Sp R)) (s : H ⟶ K) (r : K ⟶ H)
    (hsr : s ≫ r = 𝟙 H) (hH : IsFinite H.hom) (hK : IsFinite K.hom) (hKf : Flat K.hom) :
    Flat H.hom := by
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  haveI : IsAffine K.left := isAffine_of_isAffineHom K.hom
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)] at hKf ⊢
  have wr : r.left ≫ H.hom = K.hom := Over.w r
  have ws : s.left ≫ K.hom = H.hom := Over.w s
  have hid : s.left ≫ r.left = 𝟙 H.left := by rw [← Over.comp_left, hsr, Over.id_left]
  letI := H.hom.appTop.hom.toAlgebra
  letI := K.hom.appTop.hom.toAlgebra
  have hKf' : Module.Flat Γ(Sp R, ⊤) Γ(K.left, ⊤) := hKf
  show Module.Flat Γ(Sp R, ⊤) Γ(H.left, ⊤)
  let rs : Γ(H.left, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(K.left, ⊤) :=
    { toFun := r.left.appTop.hom
      map_add' := map_add _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        congr 1
        show (H.hom.appTop ≫ r.left.appTop) a = _
        rw [← Scheme.Hom.comp_appTop, wr]; rfl }
  let ss : Γ(K.left, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(H.left, ⊤) :=
    { toFun := s.left.appTop.hom
      map_add' := map_add _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        congr 1
        show (K.hom.appTop ≫ s.left.appTop) a = _
        rw [← Scheme.Hom.comp_appTop, ws]; rfl }
  refine Module.Flat.of_retract rs ss ?_
  ext x
  show (r.left.appTop ≫ s.left.appTop) x = x
  rw [← Scheme.Hom.comp_appTop, hid]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlatStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_finite_retract_of_finite_flat : ∀ (R : Type) [CommRing R] (H K : Over (Sp R)) (s : H ⟶ K) (r : K ⟶ H), s ≫ r = 𝟙 H → IsFinite H.hom → IsFinite K.hom → Flat K.hom → Flat H.hom := by
  first | exact @GlobalTheory.retract_flat_of_finite | exact GlobalTheory.retract_flat_of_finite | (intros; apply GlobalTheory.retract_flat_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundle
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_lift_one_of_triv_ev : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  intro R _ _ G _ hG P hP h0l h0r _ T a ha
  have hadd : IsAdditive P := CubeNoeth.isAdditive_of_triv_axes hG hG hP h0l h0r
  have hD : (Out.translDiff (G ⊗ G) P (lift a (1 : T ⟶ G))).IsLB := LB.isLB_linComb hP _ _
  have hz : cls _ hD = 0 := by
    have e₁ := pull_translDiff hP (lift a (1 : T ⟶ G)) hD (fst T (G ⊗ G)) (snd T (G ⊗ G))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have em : (fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G) =
        lift ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp [MonObj.mul_comp]
    have eu : snd T (G ⊗ G) = lift (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp
    have k₁ : CechPic.pull ((fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G)).left (cls P hP) =
        evc hP ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [em]; rfl
    have k₂ : CechPic.pull (snd T (G ⊗ G)).left (cls P hP) =
        evc hP (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [evc, ← eu]
    have k₃ : evc hP (fst T (G ⊗ G) ≫ a) (snd T (G ⊗ G) ≫ snd G G) = 0 := by
      have e := congrArg (CechPic.pull (lift (snd T (G ⊗ G) ≫ snd G G) (fst T (G ⊗ G))).left)
        ((triv_ev_iff hP _ _).1 ha)
      rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
    rw [e₁, k₁, k₂, (isAdditive_iff hP).1 hadd, add_sub_cancel_right, k₃]
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, hz, map_zero]

end GlobalTheory.AbDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_lift_one_of_axis_trivial_bundle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  first | exact @GlobalTheory.AbDual.memKL_lift_one_of_triv_ev | exact GlobalTheory.AbDual.memKL_lift_one_of_triv_ev | (intros; apply GlobalTheory.AbDual.memKL_lift_one_of_triv_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatKernelSymmetricBirigidifiedBundle
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlatP

theorem flat_of_finite_rep : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [GrpObj B],
    IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∀ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left → IsFinite H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x) → Flat H.hom := by
  intro R _ _ B _ hB N hN hamp M hM H j hj hfin hrep
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  refine GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal R H hfin (fun m _ => ?_)
  set f := spMap (algebraMap R (Localization.AtPrime m)) with hf
  have hB' : IsAbelianScheme ((Over.pullback f).obj B) := GlobalTheory.isAbelianScheme_pullback_obj f B hB
  haveI := hB'.comm
  have hpb := IsPullback.of_hasPullback B.hom f
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B N hB hN hamp
    (Localization.AtPrime m) f _ _ _ hpb
  have hML : (M.pull (pullback.fst B.hom f)).IsLB := pull_isLB hM _
  have hrep' := GlobalTheory.T.memKernelOfLineBundle_baseChange_representable _ _ f B M hM H j hrep
  have hth := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ ((Over.pullback f).obj B) hB' hP _ hML
  have hcl : IsClosedImmersion ((Over.pullback f).map j).left := by
    exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f j hj
  have hfin' : IsFinite ((Over.pullback f).obj H).hom := by
    first
    | exact MorphismProperty.pullback_snd (P := @IsFinite) _ _ hfin
    | (haveI := hfin; exact (inferInstance : IsFinite (pullback.snd H.hom f)))
  exact GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local hG (Localization.AtPrime m) ((Over.pullback f).obj B) hB' hP _ hML hth _ _ hcl hrep' hfin'

theorem exists_closed_rep : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∃ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left ∧
      ∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro R _ B _ hB N hN hamp M hM
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hP : IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B hN hamp
  obtain ⟨h0, -, h2⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B M hM
  obtain ⟨H, j, hj, hrep⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG R B hB hP M (AbLaw.pw M 0) hM h0
  refine ⟨H, j, hj, fun T x => ?_⟩
  rw [← GlobalTheory.UU.inK_iff_memKL, h2 _ rfl T x]
  exact hrep T x

private theorem isFinite_of_closedImmersion_factor_through_finite {S : Scheme.{0}} {H F G : Over S} (j : H ⟶ G) (i : F ⟶ G)
    (m : H ⟶ F) (hm : m ≫ i = j) (hj : IsClosedImmersion j.left) (hF : IsFinite F.hom) : IsFinite H.hom := by
  haveI : IsSeparated (i.left ≫ G.hom) := by rw [Over.w i]; infer_instance
  haveI : IsSeparated i.left := IsSeparated.of_comp i.left G.hom
  haveI : IsClosedImmersion (m.left ≫ i.left) := by rw [← Over.comp_left, hm]; exact hj
  haveI : IsClosedImmersion m.left := IsClosedImmersion.of_comp m.left i.left
  rw [← Over.w m]; infer_instance

end GlobalTheory.KerFlatP

namespace GlobalTheory


open GlobalTheory.KerFlatP in
theorem kernel_finiteFlat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G2 G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P.pull (lift (𝟙 G) (𝟙 G)).left) → ∃ (H : Over (Sp R)) (i : H ⟶ G), IsClosedImmersion i.left ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
  intro R _ _ G _ hG P hP h1 h2 hsym hamp
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  obtain ⟨HL, _, iL, -, -, hfinL, -, hrepL⟩ := GlobalTheory.kernel_finiteFlat_subgroup R G hG _ hL hamp
  have hGG : IsAbelianScheme (G ⊗ G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper (G ⊗ G).hom := by
    show IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hL1 := pull_isLB hL (fst G G).left
  have hL2 := pull_isLB hL (snd G G).left
  have hN := GlobalTheory.CechPic.isLB_tens hL1 hL2
  have hNamp : Out.RelAmple (G ⊗ G) (GlobalTheory.CechPic.tens _ _) :=
    GlobalTheory.MumProd.SumPol.relAmple_prod G G hL hL hN
      (by rw [GlobalTheory.CechPic.cls_tens hL1 hL2 hN, GlobalTheory.CechPic.cls_pull hL _ hL1, GlobalTheory.CechPic.cls_pull hL _ hL2])
      hamp hamp

  obtain ⟨K, k, hk, hrepK⟩ := exists_closed_rep R (G ⊗ G) hGG _ hN hNamp P hP

  have hmemK : GlobalTheory.MemKL (G ⊗ G) P (lift (k ≫ fst G G) (k ≫ snd G G)) := by
    rw [lift_comp_fst_snd]; exact (hrepK K k).2 ⟨𝟙 K, Category.id_comp _⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair R G hG P hP h1 h2 hsym K _ _ hmemK
  obtain ⟨za, hza⟩ := (hrepL K _).1 (GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym K _ ha)
  obtain ⟨zb, hzb⟩ := (hrepL K _).1 (GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym K _ hb)
  have hfinHL2 : IsFinite (HL ⊗ HL).hom := by
    haveI := hfinL
    show IsFinite (pullback.fst HL.hom HL.hom ≫ HL.hom)
    infer_instance
  have hfinK : IsFinite K.hom := by
    refine isFinite_of_closedImmersion_factor_through_finite k (lift (fst HL HL ≫ iL) (snd HL HL ≫ iL)) (lift za zb) ?_ hk hfinHL2
    apply CartesianMonoidalCategory.hom_ext <;> simp [hza, hzb]
  have hflatK : Flat K.hom := flat_of_finite_rep R (G ⊗ G) hGG _ hN hNamp P hP K k hk hfinK hrepK

  set e : G ⟶ G ⊗ G := lift (𝟙 G) (1 : G ⟶ G) with he
  have hxe : ∀ {T : Over (Sp R)} (x : T ⟶ G), x ≫ e = lift x (1 : T ⟶ G) := by
    intro T x
    apply CartesianMonoidalCategory.hom_ext <;> simp [e]
  let H : Over (Sp R) := Over.mk (pullback.snd k.left e.left ≫ G.hom)
  let i : H ⟶ G := Over.homMk (pullback.snd k.left e.left) rfl
  haveI := hk
  have hi : IsClosedImmersion i.left := by
    show IsClosedImmersion (pullback.snd k.left e.left)
    infer_instance
  have hwK : pullback.fst k.left e.left ≫ K.hom = H.hom := by
    show _ = pullback.snd k.left e.left ≫ G.hom
    rw [← Over.w k, pullback.condition_assoc, Over.w e]
  let s : H ⟶ K := Over.homMk (pullback.fst k.left e.left) hwK
  have hs : s ≫ k = i ≫ e :=
    Over.OverMorphism.ext (by rw [Over.comp_left, Over.comp_left]; exact pullback.condition)
  have hmemH : ∀ (T : Over (Sp R)) (x : T ⟶ G),
      (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
    intro T x
    constructor
    · intro htr
      obtain ⟨z, hz⟩ := (hrepK T _).1 (GlobalTheory.T.mem_kernel_lift_one_of_axis_trivial_bundle R G hG P hP h1 h2 hsym T x htr)
      have hz' : z.left ≫ k.left = x.left ≫ e.left := by
        rw [← Over.comp_left, hz, ← hxe, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left x.left hz') ?_, ?_⟩
      · show pullback.lift z.left x.left hz' ≫ pullback.snd k.left e.left ≫ G.hom = T.hom
        rw [pullback.lift_snd_assoc, Over.w x]
      · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact pullback.lift_snd _ _ _)
    · rintro ⟨y, rfl⟩
      have hm : GlobalTheory.MemKL (G ⊗ G) P (lift (y ≫ i) (1 : T ⟶ G)) := by
        refine (hrepK T _).2 ⟨y ≫ s, ?_⟩
        rw [Category.assoc, hs, ← Category.assoc, hxe]
      exact (GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair R G hG P hP h1 h2 hsym T _ _ hm).1

  have hLi : GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) i :=
    GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym H i ((hmemH H i).2 ⟨𝟙 H, Category.id_comp _⟩)
  obtain ⟨zH, hzH⟩ := (hrepL H i).1 hLi
  have hfinH : IsFinite H.hom := isFinite_of_closedImmersion_factor_through_finite i iL zH hzH hi hfinL

  obtain ⟨r, hr⟩ := (hmemH K (k ≫ fst G G)).1 ha
  have hsr : s ≫ r = 𝟙 H := by
    haveI : Mono i.left := by
      show Mono (pullback.snd k.left e.left)
      infer_instance
    have h3 : s ≫ r ≫ i = 𝟙 H ≫ i := by
      rw [hr, ← Category.assoc, hs, Category.assoc]; simp [e]
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).1 (by simpa [Over.comp_left] using congrArg CommaMorphism.left h3)
  exact ⟨H, i, hi, hfinH, GlobalTheory.T.flat_of_finite_retract_of_finite_flat R H K s r hsr hfinH hfinK hflatK, hmemH⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatKernelSymmetricBirigidifiedBundleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteFlat_kernel_symmetric_birigidified_bundle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G2 G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P.pull (lift (𝟙 G) (𝟙 G)).left) → ∃ (H : Over (Sp R)) (i : H ⟶ G), IsClosedImmersion i.left ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
  first | exact @GlobalTheory.kernel_finiteFlat | exact GlobalTheory.kernel_finiteFlat | (intros; apply GlobalTheory.kernel_finiteFlat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerExt

theorem kernel_killed : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hab hpb hsq P P' hP hP' hPP' h1 h2 hsym hamp m hA T x hx
  obtain ⟨H, i, -, -, hflat, hker⟩ := GlobalTheory.T.finiteFlat_kernel_symmetric_birigidified_bundle W G hab P' hP' h1 h2 hsym hamp
  obtain ⟨y, rfl⟩ := (hker T x).1 hx
  have key : i ^ m = 1 := by
    haveI := hab.proper
    haveI : IsOpenImmersion (spMap (algebraMap W L)) := isOpenImmersion_spMap_of_isDiscreteValuationRing W L
    haveI : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine GrpDense.hom_ext_of_points (spMap (algebraMap W L)) (fun T' t => ?_)
    obtain ⟨z, hz⟩ := GrpDense.pushPt_surjective hpb.1 T' (t ≫ i)
    have hzl : z.left ≫ φ = t.left ≫ i.left := congrArg (fun q => q.left) hz
    let F := (lift (snd G H ≫ i) (fst G H)).left
    obtain ⟨s, hs⟩ : ∃ s : (P'.pull F).Gen, s.IsGen := (hker H i).2 ⟨𝟙 H, Category.id_comp _⟩
    let c := (lift (snd A T' ≫ z) (fst A T')).left
    let q : Over.mk ((A ⊗ T').hom ≫ spMap (algebraMap W L)) ⟶ H :=
      Over.homMk ((snd A T').left ≫ t.left) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [Over.w t]
        show (snd A T').left ≫ T'.hom ≫ _ = _
        rw [← Category.assoc, Over.w (snd A T')])
    let Ψ := (lift (pushPt hpb.1.w (fst A T')) q).left
    have hΨ1 : Ψ ≫ (fst G H).left = (fst A T').left ≫ φ := by rw [← Over.comp_left, lift_fst]; rfl
    have hΨ2 : Ψ ≫ (snd G H).left = (snd A T').left ≫ t.left := by rw [← Over.comp_left, lift_snd]; rfl
    have hF1 : F ≫ (fst G G).left = (snd G H).left ≫ i.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
    have hF2 : F ≫ (snd G G).left = (fst G H).left := by rw [← Over.comp_left, lift_snd]
    have hc1 : c ≫ (fst A A).left = (snd A T').left ≫ z.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
    have hc2 : c ≫ (snd A A).left = (fst A T').left := by rw [← Over.comp_left, lift_snd]
    have hc : Ψ ≫ F = c ≫ φ₂ := by
      apply Over.tensorObj_ext
      · change (Ψ ≫ F) ≫ (fst G G).left = (c ≫ φ₂) ≫ (fst G G).left
        rw [Category.assoc, Category.assoc, hsq.1, hF1, ← Category.assoc, hΨ2, ← Category.assoc, hc1,
          Category.assoc, Category.assoc, hzl]
      · change (Ψ ≫ F) ≫ (snd G G).left = (c ≫ φ₂) ≫ (snd G G).left
        rw [Category.assoc, Category.assoc, hsq.2, hF2, hΨ1, ← Category.assoc, hc2]
    have e1 : LBIso (P.pull c) (P'.pull (Ψ ≫ F)) := GenSpread.lbIso_pull_of_lbIso hPP' c hc
    have e2 : LBIso (P'.pull (Ψ ≫ F)) ((P'.pull F).pull Ψ) := GenSpread.lbIso_pull_pull hP' Ψ rfl
    obtain ⟨s', hs'⟩ := RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP' F) Ψ) (pull_isLB hP' _) e2.symm
      (LB.genPull _ s Ψ) (LB.isGen_genPull _ s hs Ψ)
    have hzk := RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hP c) e1.symm s' hs'
    have hzm : z ^ m = 1 := hA T' z hzk
    rw [MonObj.comp_pow, MonObj.comp_one, ← hz]
    show pushHom hpb T' z ^ m = 1
    rw [← map_pow, hzm, map_one]
  rw [← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.KerExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGenericStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_kernel_killed_over_dvr_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  first | exact @GlobalTheory.KerExt.kernel_killed | exact GlobalTheory.KerExt.kernel_killed | (intros; apply GlobalTheory.KerExt.kernel_killed <;> assumption)
end

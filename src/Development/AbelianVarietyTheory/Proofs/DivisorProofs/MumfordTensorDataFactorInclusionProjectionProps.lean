module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem degPre_c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero, padd, ← Hom.mul_def] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem tens_inc_pr_facts (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r) :
    IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧
      ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]
  · simpa using T.inc_pr' i₀ i₀
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', Tens.act_pr]
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl, Category.comp_id, Finset.prod_eq_single i]
      · simp [Matrix.single_apply]
      · intro j _ hj
        simp [Matrix.single_apply, Ne.symm hj]
      · simp
    · rw [if_neg h, comp_one]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp [Matrix.single_apply, Ne.symm h]
  · intro y
    apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', T.c_pr]
    by_cases h : i = i₀
    · subst h
      simp [Tens.xi]
    · rw [if_neg h, comp_one]
      simp [Tens.xi, Pi.single_apply, h, degPre_c_zero]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionPropsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r), IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧ ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  first | exact @GlobalTheory.Mum.tens_inc_pr_facts | exact GlobalTheory.Mum.tens_inc_pr_facts | (intros; apply GlobalTheory.Mum.tens_inc_pr_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.range_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') :
    (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧
    (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  constructor
  · intro g hg
    obtain ⟨p, hp⟩ : ∃ p, p = E.H.ι g := ⟨_, rfl⟩
    rw [← hp] at hg
    let Ω := G'.left.residueField p
    let x0 : Sp Ω ⟶ G'.left := G'.left.fromSpecResidueField p
    let x : Sp Ω ⟶ S := x0 ≫ G'.hom
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, x0, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hg
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    let w : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ x) :=
      pullback.lift (spMap io ≫ x0) (𝟙 _) (by simp [x])
    let w0 : Sp Ω' := closedPoint Ω'
    have hw : pullback.fst G'.hom (spMap io ≫ x) (w w0) = p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    have hlw : l (w w0) = g := by
      apply E.H.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hl1, ← hp]
      exact hw
    refine ⟨pullback.fst E.Y.hom (spMap (io.comp κ)) (e.hom.left (w w0)), ?_⟩
    rw [← hlw, ← Scheme.Hom.comp_apply, hl2]
    simp only [Scheme.Hom.comp_apply]
  · intro hπ y
    obtain ⟨s, hs⟩ := hπ.surj (closedPoint R)
    let Ω := S.residueField s
    let x : Sp Ω ⟶ S := S.fromSpecResidueField s
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    obtain ⟨w', hw'⟩ := (pullback.fst E.Y.hom (spMap (io.comp κ))).surjective y
    let w := e.inv.left w'
    have hew : e.hom.left w = w' := by
      simp only [w]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
      rfl
    refine ⟨l w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply l E.H.ι, hl1,
        ← Scheme.Hom.comp_apply (pullback.fst G'.hom (spMap io ≫ x)) G'.hom, pullback.condition]
      simp only [Scheme.Hom.comp_apply, x]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    · rw [← Scheme.Hom.comp_apply, hl2]
      simp only [Scheme.Hom.comp_apply]
      rw [hew, hw']

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_range_eq_fixedGroup_image : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (E : Emb π G'), (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧ (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  first | exact @GlobalTheory.Mum.Emb.range_closed | exact GlobalTheory.Mum.Emb.range_closed | (intros; apply GlobalTheory.Mum.Emb.range_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CompletedStalk

theorem essFiniteType_int_stalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.Poinc.CompletedStalk

theorem GlobalTheory.Poinc.CompletedStalk.exists_completion_unif : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧ ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  intro o' Ω _ _ _ hA S ρ hB M U₀ EE FinalForm hAdm hEE x hx
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hAdm.1.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _,
    isGrpPullback_pullback _ _, hL, hP⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigCube

theorem genericPoints_subset_abLocus {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) : genericPoints (Sp R) ⊆ abLocus G := by
  have : IsProper ((Over.pullback (jK R)).obj G).hom := hp
  refine Set.Subset.trans ?_ (range_subset_abLocus_of_isProper (G' := (Over.pullback (jK R)).obj G) hG
    (IsPullback.of_hasPullback G.hom (jK R)))
  rw [genericPoints_eq_singleton, genericPoint_eq_bot_of_affine]
  rintro _ rfl
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))

theorem exists_gen_theta_generic {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) {M : LB G.left} (hM : M.IsLB) :
    ∃ t : ((Theta G M).pull (pullback.fst (G3 G).hom (jK R))).Gen, t.IsGen := by
  let j := jK R
  let A : Over (Spec (CommRingCat.of (FractionRing R))) := (Over.pullback j).obj G
  have gp : IsGrpPullback A G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  have hA : IsSemiAbelian A := IsSemiAbelian.pullback j G hG
  have : IsProper A.hom := hp
  have hAb : IsAbelianScheme A := AbelianSchemeGerms.isAbelianScheme_of_proper A hA
  have := hA.comm
  let P : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk (pullback.snd (G3 G).hom j)
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (gp.1.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (gp.1.lift_snd _ _ _)
  let U : Over.mk (P.hom ≫ j) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom j) pullback.condition
  have hx : ∀ i, pushPt gp.1.w (x i) = U ≫ x3 G i := fun i => Over.OverMorphism.ext (gp.1.lift_fst _ _ _)
  let πA := pullback.fst G.hom j
  let pf := pullback.fst (G3 G).hom j
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.CubeTop.cubeTheorem _ A hAb (M.pull πA) (pull_isLB hM _) P (x 0) (x 1) (x 2)
  obtain ⟨t₁, ht₁⟩ := CubeDescent.exists_gen_comp M πA _ _ t₀ ht₀
  let y : Fin 3 → (Over.mk (P.hom ≫ j) ⟶ G) := fun i => U ≫ x3 G i
  have key : ∀ z : P ⟶ A, z.left ≫ πA = (pushHom gp P z).left := fun z => rfl
  have hxp : ∀ i, pushHom gp P (x i) = y i := hx
  have e : lift (y 0) (lift (y 1) (y 2)) = U := by ext <;> simp [y, x3]
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hM (φ' := fun I => pf ≫ thφ G (x3 G) I) (ε' := thε) (fun V _ h => by
    have hθ := prod_cub (y 0) (y 1) (y 2) h
    rw [e] at hθ
    refine Eq.trans ?_ hθ.symm
    simp only [Fin.prod_univ_eight, key, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, map_mul, map_one, hxp, zpow_one, zpow_neg_one]
    simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, key, map_mul, map_one, hxp,
      zpow_one, zpow_neg_one]) t₁ ht₁
  let c := CechPic.cls M hM
  refine (CechPic.cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hM _ _) pf)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CechPic.cls_pull (LB.isLB_linComb hM _ _), CechPic.cls_linComb hM, map_sum]
  simp only [map_zsmul, ← CechPic.pull_comp]
  have h2 := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hM (fun I => pf ≫ thφ G (x3 G) I) thε)).2 ⟨t₂, ht₂⟩
  rw [CechPic.cls_linComb hM] at h2
  exact h2

theorem exists_rigLB_cubicalStr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ M : LB G.left, M.IsLB → ∃ (L : RigLB G) (_ : CubicalStr G L), L.L = M := by
  intro R _ _ _ _ _ G _ _ hG hp M hM
  have hab := genericPoints_subset_abLocus G hG hp
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨a₂, b₂, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G G a₁ a₁ b₁ b₁
  obtain ⟨a₃, b₃, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G _ a₁ a₂ b₁ b₂
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := R) (M.pull (eSec G)) (pull_isLB hM _)
  let L : RigLB G := ⟨M, r, hM, hr⟩
  have hΘ : (Theta G M).IsLB := LB.isLB_linComb hM _ _
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  let e : 𝟙_ (Over (Sp R)) ⟶ G3 G := lift 1 (lift 1 1)
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (G3 G) e.left (Theta G M) (Over.w e) a₃ b₃ hΘ
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hΘ _)) (exists_gen_theta_generic G hG hp hM)
  obtain ⟨c⟩ := (CubeGen.cubical_and_symmetric (Sp R) G L hG ⟨inferInstance, hab⟩).1 ⟨t, ht⟩
  exact ⟨L, c, rfl⟩

end GlobalTheory.RigCube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackCoordinateCombinationRatioAndVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackCoordinateCombinationRatioAndVanish
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.PullCoordComb

def evalF {X : Scheme.{0}} (L : LB X) (i : L.ι) : LB.Sec L →+ Γ(X, L.U i) where
  toFun s := s.f i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (s : Fin n → LB.Sec L)
    (i : L.ι) : (∑ k, a k • s k).f i = ∑ k, resG X le_top (a k) * (s k).f i := by
  change evalF L i (∑ k, a k • s k) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

theorem linComb_ratio_and_vanish : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    (∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
          ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i)) ∧
    (y ≠ 0 → ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, algebraMap K Ω (lam k : K) * y k = 0 →
        ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) := by
  intro K Ω _ _ _ _ m y X _ p g ψ hbase hratio
  have hA : ∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι)
      (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
      ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
        ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) := by
    intro lam l i h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_smul_f, map_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, fnOf_resG, ← hbase, map_mul, mul_left_comm (ψ (y l)), hratio l k i h]
    ring
  refine ⟨hA, fun hy lam hsum => ?_⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, y k₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  apply GlobalTheory.LB.f_injective
  funext i
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have e := hA lam k₀ i hU
  rw [hsum, map_zero, zero_mul] at e
  have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
  rw [GlobalTheory.LB.zero_f, map_zero]
  exact (mul_eq_zero.1 e).resolve_left hψ

end GlobalTheory.PullCoordComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackCoordinateCombinationRatioAndVanishStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBack_coordinate_combination_ratio_and_vanish : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    (∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
          ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i)) ∧
    (y ≠ 0 → ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, algebraMap K Ω (lam k : K) * y k = 0 →
        ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) := by
  first | exact @GlobalTheory.PullCoordComb.linComb_ratio_and_vanish | exact GlobalTheory.PullCoordComb.linComb_ratio_and_vanish | (intros; apply GlobalTheory.PullCoordComb.linComb_ratio_and_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem exists_matEnd {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! z : T' ⟶ B, ∀ a, z ≫ pr a = y a) (a b : Fin 8) :
    ∃ f : B ⟶ B, MatEnd pr a b f := by
  obtain ⟨f, hf, -⟩ := hu B (fun w => if w = a then pr b else 1)
  have ext : ∀ {T : Over S} (z z' : T ⟶ B), (∀ w, z ≫ pr w = z' ≫ pr w) → z = z' := by
    intro T z z' h
    obtain ⟨_, -, hz⟩ := hu T (fun w => z' ≫ pr w)
    exact (hz z h).trans (hz z' fun _ => rfl).symm
  have mul : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    intro T x y
    refine ext _ _ fun w => ?_
    have hw := hpr w
    have e : ((x ≫ f) * (y ≫ f)) ≫ pr w = (x ≫ f ≫ pr w) * (y ≫ f ≫ pr w) := by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc]
    rw [e, Category.assoc, hf]
    split_ifs
    · have := hpr b
      rw [MonObj.mul_comp]
    · simp
  refine ⟨f, ⟨?_, ?_⟩, hf⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ B) ≫ f = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (B ⊗ B) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem matOn_exists : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (C : Over (Sp S.R)) [GrpObj C] [IsCommMonObj C] (pr : Fin 8 → (ρ.P.A ⟶ C)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp S.R)) (y : Fin 8 → (T' ⟶ C)), ∃! z : T' ⟶ ρ.P.A, ∀ a, z ≫ pr a = y a) → ∀ a b, ∃ f, MatOn FinalForm pr a b f := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm hU C _ _ pr hpr hu a b
  obtain ⟨f₁, hf₁⟩ := exists_matEnd pr hpr hu a b
  have : IsMonHom f₁ := hf₁.1

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ f₁
  have hw'l : w'.left ≫ ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ f₁.left := by
    have := congrArg (fun z => z.left) (pa (𝟙 _))
    simpa [pushPt] using this
  obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
  refine ⟨F, hF, f₁, hf₁, ?_⟩
  have hsep : IsSeparated FinalForm.G.hom := FinalForm.semi.separated
  have hsm : Smooth FinalForm.G.hom := FinalForm.semi.smooth
  have hQf : Flat Q.hom := MorphismProperty.of_isPullback (P := @Flat) FinalForm.cart.1 inferInstance
  have hqc : QuasiCompact M.pt := by
    have : IsSeparated M.s := M.sep
    have : QuasiCompact (M.pt ≫ M.s) := by rw [M.pt_s]; infer_instance
    exact QuasiCompact.of_comp M.pt M.s
  have hdom : IsSchemeTheoreticallyDominant M.pt := .of_isDominant M.pt
  let p : pullback ρ.P.A.hom FinalForm.u₀ ⟶ M.Z := Q.hom ≫ U₀.ι
  let j := pullback.fst p M.pt
  have hj : j ≫ Q.hom = pullback.snd p M.pt ≫ x := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, hx]
    exact pullback.condition
  let k : pullback p M.pt ⟶ pullback FinalForm.G.hom M.pt := pullback.lift (j ≫ FinalForm.φ) (pullback.snd p M.pt) (by
    rw [Category.assoc, FinalForm.cart.1.w]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst FinalForm.G.hom M.pt = j ≫ FinalForm.φ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd p M.pt := pullback.lift_snd _ _ _
  have hkν : k ≫ ν = j := by
    apply FinalForm.cart.1.hom_ext
    · rw [Category.assoc, hν₁, hk₁]
    · rw [Category.assoc, hν₂, ← Category.assoc, hk₂, hj]
  have hF' : ((Over.pullback M.pt).map F).left ≫ pullback.fst FinalForm.G.hom M.pt = pullback.fst FinalForm.G.hom M.pt ≫ F.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hw₂ : w'.left ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd FinalForm.G.hom M.pt := Over.w w'
  have key : k ≫ w'.left ≫ ν = j ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hw'l]
      simp only [← Category.assoc]
      rw [hkν]
      simp only [Category.assoc, Over.pullback_map_left]
      exact congrArg (j ≫ ·) (pullback.lift_fst _ _ _).symm
    · have e : ((Over.pullback FinalForm.u₀).map f₁).left ≫ Q.hom = Q.hom := Over.w ((Over.pullback FinalForm.u₀).map f₁)
      show (k ≫ w'.left ≫ ν) ≫ Q.hom = (j ≫ ((Over.pullback FinalForm.u₀).map f₁).left) ≫ Q.hom
      simp only [Category.assoc]
      rw [hν₂, e, hj, ← Category.assoc w'.left, hw₂, ← Category.assoc, hk₂]
  refine GlobalTheory.SS.GenProj.ext_of_dense j FinalForm.G.hom ?_ ?_
  · have e1 : j ≫ FinalForm.φ ≫ F.left = k ≫ w'.left ≫ ν ≫ FinalForm.φ := by
      rw [hν₁, ← hFw, hF', ← Category.assoc k, hk₁, Category.assoc]
    rw [e1]
    simp only [← Category.assoc] at key ⊢
    rw [key]
  · rw [Category.assoc, Category.assoc, Over.w F, FinalForm.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.Poinc.Eq8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeGen

section
variable {X Y Z : Scheme.{0}} {L : LB X}

def Triv (L : LB X) (Y : Scheme.{0}) (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h

theorem Triv.mul {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (h' : Triv L Y F') :
    Triv L Y (fun U _ g => F U g * F' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g))⟩

theorem Triv.inv {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) :
    Triv L Y (fun U _ g => (F U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_⟩
  simp only [zpow_neg, Finset.prod_inv_distrib, e U g]

theorem Triv.pull {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F) (r : Z ⟶ Y) :
    Triv L Z (fun U _ g => F U (fun ψ => g (r ≫ ψ))) := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  exact ⟨K, inferInstance, _, _, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _,
    fun U _ g => e U (fun ψ => g (r ≫ ψ))⟩

theorem Triv.exists_gen (hL : L.IsLB) {F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : Triv L Y F)
    (f : Y ⟶ X) (hf : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), F U g = g f) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  obtain ⟨K, _, φ, ε, t, ht, e⟩ := h
  obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => f) (ε' := fun _ => 1)
    (fun U _ g => by rw [e, hf]; simp) t ht
  exact ⟨t', ht'⟩

theorem triv_of_sec (θ : L.Sec) (f : Y ⟶ X) (hf : ∀ y, f y ∈ secNz θ) : Triv L Y (fun _ _ g => g f) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ f).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hf y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ f hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  exact ⟨Fin 1, inferInstance, _, _, ⟨fun j => (hu j).unit⟩,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ f).compat i j), fun U _ g => by simp⟩

end

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {T : Over S}

theorem triv_cub (c : CubicalStr G L) (x x' y : T ⟶ G) : Triv L.L T.left (fun _ _ h =>
    h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G).left)⁻¹) :=
  ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub x x' y h⟩

theorem triv_one (L : RigLB G) (T : Over S) : Triv L.L T.left (fun _ _ h => h (1 : T ⟶ G).left) :=
  ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ => eSec G) (fun _ => 1) L.rig T.hom,
    DVR.pullGen_isGen _ _ _ _ L.rigGen _, fun _ _ h => by rw [GlobalTheory.UU.one_left]; simp⟩

end GlobalTheory.Mum.CubeGen

namespace GlobalTheory.Mum

open CubeGen

theorem exists_gen_of_cubeTen (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G)
    (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens)
    (hW : ∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) :
    ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  have s : ∀ f ∈ cubeTen x a b c, Triv P.L.L W (fun _ _ g => g (W.ι ≫ f.left)) := fun f hf =>
    triv_of_sec θ _ fun y => hW f hf y.2
  have s₁ := s (x * a) (by simp [cubeTen])
  have s₂ := s (x * a⁻¹) (by simp [cubeTen])
  have s₃ := s a (by simp [cubeTen])
  have s₄ := s a⁻¹ (by simp [cubeTen])
  have s₅ := s (x * b) (by simp [cubeTen])
  have s₆ := s (x * c) (by simp [cubeTen])
  have s₇ := s (x * (b * c)⁻¹) (by simp [cubeTen])
  have s₈ := s b (by simp [cubeTen])
  have s₉ := s c (by simp [cubeTen])
  have s₀ := s (b * c)⁻¹ (by simp [cubeTen])
  have e := (triv_one P.L T).pull W.ι
  have c₁ := (triv_cub P.c x a a⁻¹).pull W.ι
  have c₂ := (triv_cub P.c x b c).pull W.ι
  have c₃ := (triv_cub P.c x (b * c) (b * c)⁻¹).pull W.ι
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  refine ((t₃.mul t₂.inv).mul e).exists_gen P.L.isLB _ fun U _ g => ?_
  simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens), (∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) → ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_of_cubeTen | exact GlobalTheory.Mum.exists_gen_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_gen_of_cubeTen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpac
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormalModel

open TopologicalSpace

theorem exists_normal_model : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  intro K Ω _ _ _ _ D m y X _ p g ψ ⟨hgp, hX, hψ, hK, hy⟩
  obtain ⟨W, hne, hn⟩ := GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety (𝓞 K) X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom (𝓞 K))) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom (𝓞 K)) = algebraMap ℤ (𝓞 K) := RingHom.ext_int _ _
      change (Int.castRingHom (𝓞 K)).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom (𝓞 K))) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X W.toScheme
      (p ≫ spMap (Int.castRingHom (𝓞 K))) W (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty W.toScheme := hne.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ W.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = W.ι := by rw [hpb.w, Category.id_comp]
  have hoi : IsOpenImmersion (e ≫ ν) := by rw [hfac]; infer_instance
  have hg : e (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : ν (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : ν.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver (ν ≫ p) := isProjOver_comp_of_isFinite ν hX.isProjOver
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom (𝓞 K))) := by rwa [Category.assoc]
  have har : IsArithVar (ν ≫ p) D := ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq (𝓞 K) X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩

  have hη : ν (genericPoint Y) ⤳ genericPoint X := specializes_of_eq hgen
  have hWη : W.ι (genericPoint W.toScheme) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have heη : e (genericPoint W.toScheme) ⤳ genericPoint Y := specializes_of_eq hg
  have hbij : Function.Bijective (SmallSec.fnMap ν hη) := by
    refine ⟨(SmallSec.fnMap ν hη).injective, fun u => ?_⟩
    obtain ⟨t, ht⟩ := SmallSec.fnMap_surjective W.ι hWη (SmallSec.fnMap e heη u)
    refine ⟨t, (SmallSec.fnMap e heη).injective ?_⟩
    rw [← ht, ← ProjSpace.fnMap_comp e ν heη hη (ProjSpace.comp_genericPoint_specializes _ _ heη hη)]
    exact ProjSpace.fnMap_congr hfac _ _ t
  refine ⟨Y, ‹_›, ν ≫ p, ν ≫ g, (SmallSec.fnMap ν hη).comp ψ, by rw [Category.assoc, hgp], har, hnY,
    hbij.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · have e₁ : ν.app ⊤ (algX p ⊤ a) = algX (ν ≫ p) ⊤ a := by
      simp only [algX, RingHom.comp_apply]
      rw [← Scheme.Hom.appLE_comp_appLE ν p ⊤ ⊤ ⊤ (by simp) (by simp)]
      rw [Scheme.Hom.app_eq_appLE ν]
      rfl
    rw [RingHom.comp_apply, hK, SmallSec.fnMap_fnOf ν hη _ (Opens.mem_top _), e₁]
    rfl
  · have hX' : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := (pull_U _ g i).ge (by
      have h' : ν (genericPoint Y) ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      rw [hgen] at h'
      exact h')
    have key (a : Fin (m + 1)) : fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) (ν ≫ g)).f i) =
        SmallSec.fnMap ν hη (fnOf _ hX' ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) := by
      have h₁ : genericPoint Y ∈ (ν ≫ g) ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      have h₂ : genericPoint X ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ g i).le hX'
      change fnOf _ h (resG Y _ _) = SmallSec.fnMap ν hη (fnOf _ hX' (resG X _ _))
      rw [fnOf_resG, fnOf_resG, SmallSec.fnMap_fnOf ν hη h₂ h₁, Scheme.Hom.comp_app]
      rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, key, key, ← map_mul, ← map_mul, hy k l i hX']

end GlobalTheory.NormalModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpacStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_arithmeticVariety_model_projectiveSpace : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  first | exact @GlobalTheory.NormalModel.exists_normal_model | exact GlobalTheory.NormalModel.exists_normal_model | (intros; apply GlobalTheory.NormalModel.exists_normal_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHom
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagQ

theorem eq_genericPoint_of_krullDim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) (x : X) :
    x = genericPoint X := by
  by_contra hx
  have hlt : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ : TopologicalSpace.IrreducibleCloseds X) <
      ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    refine lt_of_le_of_ne ?_ ?_
    · exact (specializes_iff_closure_subset.1 (genericPoint_specializes x))
    · intro he
      have : closure ({x} : Set X) = closure {genericPoint X} := congrArg TopologicalSpace.IrreducibleCloseds.carrier he
      exact hx ((specializes_iff_closure_subset.2 this.ge).antisymm (genericPoint_specializes x)).eq
  have : (0 : WithBot ℕ∞) < topologicalKrullDim X := Order.krullDim_pos_iff.2 ⟨_, _, hlt⟩
  rw [h] at this
  exact lt_irrefl _ this

end GlobalTheory.FlagQ
end
end

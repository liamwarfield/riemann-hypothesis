module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystems
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystems
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.LocalIsomorphism

theorem fix_of_mem {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b)
    (x : B) (hx : x ∈ I.map (algebraMap R B)) : e x = x := by
  set J := I.map (algebraMap R B) with hJdef
  have hδ : ∀ y, e y - y ∈ J := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  have hsq : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := fun a ha b hb ↦ by
    have : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hJ] at this
    simpa using this
  let T : Ideal B :=
    { carrier := {x | ∀ y, e (x * y) = x * y}
      add_mem' := fun {a b} ha hb y ↦ by simp only [Set.mem_setOf_eq] at *; rw [add_mul, map_add (f := _), ha, hb]
      zero_mem' := fun y ↦ by simp
      smul_mem' := fun c {a} ha y ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [mul_assoc, mul_left_comm, ha, mul_left_comm] }
  have hIT : J ≤ T := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr y
    show e (algebraMap R B r * y) = algebraMap R B r * y
    have hr' : algebraMap R B r ∈ J := Ideal.mem_map_of_mem _ hr
    rw [map_mul, AlgHom.commutes]
    have h0 := hsq _ hr' _ (hδ y)
    rw [mul_sub] at h0
    exact sub_eq_zero.1 h0
  have := hIT hx 1
  simpa using this

theorem bij {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b) :
    Function.Bijective e := by
  have hδ : ∀ y, e y - y ∈ I.map (algebraMap R B) := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  refine ⟨(injective_iff_map_eq_zero e).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
  · have hb' : b ∈ I.map (algebraMap R B) := (hker b).1 (by rw [← he, hb, map_zero])
    rw [← fix_of_mem I hJ p hker e he b hb', hb]
  · refine ⟨c - (e c - c), ?_⟩
    rw [map_sub, fix_of_mem I hJ p hker e he _ (hδ c)]
    ring

theorem nil {R C D : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (I : Ideal R)
    (q : C →ₐ[R] D) (h : ∀ b, q b = 0 ↔ b ∈ I.map (algebraMap R C)) (h2 : I.map (algebraMap R C) ^ 2 = 0) :
    IsNilpotent (RingHom.ker (q : C →+* D)) := ⟨2, by
  have : RingHom.ker (q : C →+* D) = I.map (algebraMap R C) := Ideal.ext fun b ↦ by
    rw [RingHom.mem_ker]; exact h b
  rw [this, h2]⟩

theorem exists_iso {R R₀ B B' B₀ : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] [CommRing B₀] [Algebra R₀ B₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (p : B →+* B₀) (p' : B' →+* B₀) (hp : SemiHom π p) (hp' : SemiHom π p')
    (hs : Function.Surjective p) (hs' : Function.Surjective p')
    (hk : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (hk' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    [Algebra.FormallySmooth R B] [Algebra.FormallySmooth R B'] :
    ∃ φ : B ≃ₐ[R] B', ∀ b, p' (φ b) = p b := by
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  let P : B →ₐ[R] B₀ := { p with commutes' := fun r ↦ hp.map_algebraMap r }
  let P' : B' →ₐ[R] B₀ := { p' with commutes' := fun r ↦ hp'.map_algebraMap r }
  have hJ := map_sq hI B
  have hJ' := map_sq hI B'
  let φ : B →ₐ[R] B' := Algebra.FormallySmooth.liftOfSurjective P P' hs' (nil I P' hk' hJ')
  let ψ : B' →ₐ[R] B := Algebra.FormallySmooth.liftOfSurjective P' P hs (nil I P hk hJ)
  have hφ : ∀ b, p' (φ b) = p b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P P' hs' (nil I P' hk' hJ') b
  have hψ : ∀ b, p (ψ b) = p' b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P' P hs (nil I P hk hJ) b
  have b1 := bij I hJ p hk (ψ.comp φ) fun b ↦ by simp [hψ, hφ]
  have b2 := bij I hJ' p' hk' (φ.comp ψ) fun b ↦ by simp [hψ, hφ]
  refine ⟨AlgEquiv.ofBijective φ ⟨fun x y h ↦ b1.1 (by simp [h]), fun c ↦ ?_⟩, hφ⟩
  obtain ⟨d, hd⟩ := b2.2 c
  exact ⟨ψ d, hd⟩

end GlobalTheory.LiftSys.LocalIsomorphism

namespace GlobalTheory.LiftSys

theorem locIso_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S S' : Sys I π s₀, Nonempty (S.LocIso S') := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ S S'
  have h : ∀ U, ∃ φ : S.F.obj U ≃ₐ[R] S'.F.obj U, ∀ b, S'.p U (φ b) = S.p U b := fun U ↦ by
    haveI := (S.smooth U).formallySmooth
    haveI := (S'.smooth U).formallySmooth
    exact LocalIsomorphism.exists_iso I hI π (S.p U) (S'.p U) (S.semi U) (S'.semi U) (S.surj U) (S'.surj U)
      (S.ker U) (S'.ker U)
  exact ⟨⟨fun U ↦ (h U).choose, fun U ↦ (h U).choose_spec⟩⟩

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystemsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S S' : Sys I π s₀, Nonempty (S.LocIso S') := by
  first | exact @GlobalTheory.LiftSys.locIso_nonempty | exact GlobalTheory.LiftSys.locIso_nonempty | (intros; apply GlobalTheory.LiftSys.locIso_nonempty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifAdjoint

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin a
  obtain ⟨hno, -, hic, -⟩ := hR
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  have ha := oG.hom a
  have hsa := oG.hom (star a)
  have hgen := U.gen_hom
  have hL := U.LG.isLB
  have hA := A.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance
  have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩

  have eA : cubeCls A.A ![fst A.A A.A ≫ oA.act a, snd A.A A.A] (cls A.L hA) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] (cls A.L hA) :=
    (cls_cubeLB A.A _ hA).symm.trans (((cls_eq_iff (LB.isLB_linComb hA _ _) (LB.isLB_linComb hA _ _)).2
      (GlobalTheory.FullPoint.lbIso_of_rosatiAdj hA (oA.rosati a))).trans (cls_cubeLB A.A _ hA))
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
      CechPic.pull U.gen.hom.left (cls A.L hA) := by
    obtain ⟨w, hw⟩ := U.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm

  have hgK : cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act a),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) =
      cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act (star a))]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) := by
    rw [hc']
    let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
      (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
    have hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e₁ := hlin.ext a
    have e₂ := hlin.ext (star a)
    rw [← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A ≫ oA.act a, snd A.A A.A] u.left hu (fun i => ?_),
      ← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] u.left hu
        (fun i => ?_), eA]
    · fin_cases i
      · show (fst _ _ ≫ U.gen.hom).left = (u ≫ fst A.A A.A).left
        congr 1; simp [u]
      · show ((snd _ _ ≫ (Over.pullback (jK R)).map (oG.act (star a))) ≫ U.gen.hom).left = (u ≫ snd A.A A.A ≫ oA.act (star a)).left
        congr 1; simp [u, e₂]
    · fin_cases i
      · show ((fst _ _ ≫ (Over.pullback (jK R)).map (oG.act a)) ≫ U.gen.hom).left = (u ≫ fst A.A A.A ≫ oA.act a).left
        congr 1; simp [u, e₁]
      · show (snd _ _ ≫ U.gen.hom).left = (u ≫ snd A.A A.A).left
        congr 1; simp [u]
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  refine pic_ext (jK R) hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
  · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
      (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
    fin_cases i <;> simp
  · have hGp := isGrpPullback_pullback G (jK R)
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    let δ := lift ((Over.pullback (jK R)).map (fst G G)) ((Over.pullback (jK R)).map (snd G G))
    have e := congrArg (CechPic.pull δ.left) hgK
    have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hGp (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G)
      (fun i => (Over.pullback (jK R)).map (x i)) x (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    rw [pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G ≫ oG.act a, snd G G] i)) δ
        (fun i => by fin_cases i <;> simp [δ]),
      pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G, snd G G ≫ oG.act (star a)] i)) δ
        (fun i => by fin_cases i <;> simp [δ])] at e
    exact (e' _).trans (e.trans (e' _).symm)

end GlobalTheory.Mum.UnifAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_ringAction_adjoint_cubeBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  first | exact @GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star | exact GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star | (intros; apply GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGenericFibreGaloisExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGenericFibreGaloisExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelGalois

theorem exists_galois (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Module.Finite F E] (n : ℕ)
    (hn : 0 < n) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω) (i : E →+* Ω) (ζ : Ωˣ), FiniteDimensional F Ω ∧ IsGalois F Ω ∧
      i.comp (algebraMap F E) = algebraMap F Ω ∧ IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : CharZero E := (algebraMap F E).charZero_iff (algebraMap F E).injective |>.1 inferInstance
  let C := CyclotomicField n E
  haveI : Module.Finite E C := IsCyclotomicExtension.finite {n} E C
  haveI : Module.Finite F C := Module.Finite.trans E C
  let L := AlgebraicClosure C
  haveI : IsAlgClosure F L := IsAlgClosure.ofAlgebraic F C L
  let Ω := IntermediateField.normalClosure F C L
  have hz := (IsCyclotomicExtension.zeta_spec n E C).map_of_injective (algebraMap C Ω).injective
  obtain ⟨ζ, hζ⟩ := hz.isUnit hn.ne'
  refine ⟨Ω, inferInstance, inferInstance, (algebraMap C Ω).comp (algebraMap E C), ζ, inferInstance, ?_, ?_,
    IsPrimitiveRoot.coe_units_iff.1 (hζ ▸ hz)⟩
  · exact { }
  · rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq F E C, ← IsScalarTower.algebraMap_eq F C Ω]


open MonObj in
theorem nonempty_level_of_rational {F : Type} [Field F] [CharZero F] (P : PolAV (Sp F)) (n : ℕ) (hn : 0 < n) (ζ : Fˣ)
    (hζ : IsPrimitiveRoot ζ n) (Q : PolAV (Sp (AlgebraicClosure F))) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsPolFibre (algebraMap F (AlgebraicClosure F)) P Q φ)
    (H : ∀ y, y ^ n = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y) : Nonempty (Out.Level P n (unitOn ζ)) := by
  let σ := algebraMap F (AlgebraicClosure F)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : F →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) n := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hp : IsPrimitiveRoot (unitOn ζ) n := by
    have := nt F
    exact prim (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨l⟩ := GlobalTheory.nonempty_level_of_isAlgClosed _ Q n (Units.map σ.toMonoidHom ζ) (Nat.cast_ne_zero.2 hn.ne') (prim σ)
  have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
      {X : Scheme} (y y' : Sp K ⟶ X) (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
    obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
    have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
        spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
          (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
      intro q ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
    rw [e, e] at h
    have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h2
    obtain ⟨rfl, h3⟩ := h2
    have h4 : φ = φ' := by
      have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
      ext x
      apply gam.injective
      have := congrArg (fun f => f.hom x) h5
      simpa using this
    rw [h4]
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext (spec_map_field_cancel σ _ _ (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H (l.pt a) (l.torsion a)
  have tors : ∀ a, t a ^ n = 1 := fun a => hinj (by rw [map_pow, ht, map_one]; exact l.torsion a)
  have uz : ∀ {R : Type} [CommRing R] (u : Rˣ) (m : ℤ), unitOn (u ^ m) = unitOn u ^ m := fun {R} _ u m =>
    map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) u m
  have hg : 2 * P.g = 2 * Q.g := by rw [hQ.1]
  have hs : ∀ i j, stdSymp Q.g (Fin.cast hg i) (Fin.cast hg j) = stdSymp P.g i j := fun i j => by
    simp only [stdSymp, Fin.val_cast, hQ.1]
  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp F) P n (unitOn ζ) hp
    (fun F' _ s => by
      have := nt F'
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn.ne')) (fun i => t (Fin.cast hg i)) (fun i => tors _)
    (fun i j => by
      have h := l.pairing (Fin.cast hg i) (Fin.cast hg j)
      rw [hs, ← uz, ← map_zpow, ← ht, ← ht] at h
      rw [← uz]
      exact LevelAfterExt.weilIs_of_ext σ hQ n _ _ _ (tors _) (tors _) h)
  exact ⟨lev⟩

theorem exists_level_galois : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (ι : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (K : ℕ), 0 < K → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp ι)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro Ω₁ _ _ R₁ _ ι P₁ K hK
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  obtain ⟨P₀, φ₀, h₀⟩ := exists_isPolFibre hB ι P₁
  obtain ⟨E, _, _, hfin, H⟩ := LevelAfterExt.exists_ext_torsion Ω₁ P₀ K hK
  obtain ⟨Ω₂, _, _, i, ζ, hfd, hgal, hi, hζ⟩ := exists_galois Ω₁ E K hK
  haveI : CharZero Ω₂ := (algebraMap Ω₁ Ω₂).charZero_iff (algebraMap Ω₁ Ω₂).injective |>.1 inferInstance
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre hB (algebraMap Ω₁ Ω₂) P₀
  obtain ⟨Q', ψ', hQ'⟩ := exists_isPolFibre hB (algebraMap Ω₂ (AlgebraicClosure Ω₂)) Q
  refine ⟨Ω₂, inferInstance, inferInstance, Q, ψ ≫ φ₀, ζ, hfd, hgal, hζ, hQ.1.trans h₀.1,
    (hQ.2.1.comp h₀.2.1).congr (GlobalTheory.spMap_comp_spMap _ _) rfl, ?_,
    nonempty_level_of_rational Q K hK ζ hζ Q' ψ' hQ' (H Ω₂ _ i _ hi Q ψ hQ _ Q' ψ' hQ')⟩
  exact LBIso.trans Q.isLB (pull_isLB P₀.isLB _) (pull_isLB P₁.isLB _) hQ.2.2.symm
    (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P₁.L _ _ _ ψ fun _ => rfl) h₀.2.2.symm)

end GlobalTheory.LevelGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGenericFibreGaloisExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_genericFibre_galoisExtension : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (ι : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (K : ℕ), 0 < K → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp ι)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  first | exact @GlobalTheory.LevelGalois.exists_level_galois | exact GlobalTheory.LevelGalois.exists_level_galois | (intros; apply GlobalTheory.LevelGalois.exists_level_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExists
noncomputable section

namespace GlobalTheory.ThK.Partner

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

theorem pure_smul (c : ℂ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    pure (c • f) φ = c • pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem polData_sum {B : Base F E} {M : Model σ X Y} {Φ} (h : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ Fam M (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
  choose f hf φ hφ hv hΦ using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pure_smul, ← hΦ i]

theorem finite_bad {M : Model σ X Y} {m : ℕ} {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h : ∀ i, Fam M (φ i)) : {v | ∃ i, φ i v ≠ M.vac v}.Finite := by
  have e : {v | ∃ i, φ i v ≠ M.vac v} = ⋃ i, {v | φ i v ≠ M.vac v} := by ext; simp
  rw [e]
  exact Set.finite_iUnion fun i => eventually_cofinite.1 (h i).2

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem partner_of_big (hK : KP) (hM : IsMatched B G X om om' R Rf) {Φ} (hΦ : Φ ∈ PolData B G.M) :
    ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' := by
  have hco : Coinv B G X om om' Rf := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
  obtain ⟨m, f, φ, hfφ, rfl⟩ := polData_sum hΦ
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfin.toFinset
  have hXT : X.T ⊆ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have h1 : B.v₁ ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M'.Pol B.ψ B.emb, R.p' g = R.p (f i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot'.onto ▸ Submodule.mem_top)
  choose f' hf' ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ = Rf.p v (φ i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto' v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  have hso : ∀ i, ∃ ζ ∈ G.M'.SoLoc B.ψ B.τ₁, Rf.p' B.v₁ ζ = Rf.p B.v₁ (φ i B.v₁) := fun i =>
    (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁ _
  choose ζ hζ eζ using hso
  let φ₀ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M'.vac v
  let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i => Function.update (φ₀ i) B.v₁ (ζ i)
  have fam₀ : ∀ i, Fam G.M' (φ₀ i) := fun i => by
    refine ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => if_neg hv⟩
    by_cases hv : v ∈ T
    · simp only [φ₀, if_pos hv]; exact hχ i v
    · simp only [φ₀, if_neg hv]; exact (hM.triple.geo.hM'.vac v).1
  have fam' : ∀ i, Fam G.M' (φ' i) := fun i => (fam₀ i).update B.v₁ (hζ i).1
  have out' : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    have hne : v ≠ B.v₁ := fun e => hv (e ▸ h1)
    simp only [φ', Function.update_of_ne hne, φ₀, if_neg hv]
  refine ⟨∑ i, pure (f' i) (φ' i), Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨f' i, φ' i, (fam' i).1, (fam' i).2, by simp only [φ', Function.update_self]; exact hζ i, rfl⟩, ?_⟩
  refine ⟨T, hXT, m, m, f, φ, f', φ', fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩,
    fun i => ⟨hf' i, (fam' i).1, out' i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  by_cases hv : v = B.v₁
  · subst hv
    simp only [φ', Function.update_self, eζ]
  · simp only [φ', Function.update_of_ne hv, φ₀, if_pos hvT, eχ]

theorem partner_of_small (hM : IsMatched B G X om om' R Rf) {Φ'} (hΦ' : Φ' ∈ PolData B G.M') :
    ∃ Φ, PolMatch B G X R Rf Φ Φ' := by
  obtain ⟨m, f', φ', hfφ, rfl⟩ := polData_sum hΦ'
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ hfin.toFinset
  have hXT : X.T ⊆ T := Finset.subset_union_left
  have hout : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M.Pol B.ψ B.emb, R.p g = R.p' (f' i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot.onto ▸ Submodule.mem_top)
  choose f hf ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = Rf.p' v (φ' i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  let φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M.vac v
  have hφ : ∀ i v, φ i v ∈ SB _ := fun i v => by
    by_cases hv : v ∈ T
    · simp only [φ, if_pos hv]; exact hχ i v
    · simp only [φ, if_neg hv]; exact (hM.triple.geo.hM.vac v).1
  refine ⟨∑ i, pure (f i) (φ i), T, hXT, m, m, f, φ, f', φ', fun i => ⟨hf i, hφ i, fun v hv => if_neg hv⟩,
    fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  simp only [φ, if_pos hvT, eχ]

theorem match_of_polMatch (hM : IsMatched B G X om om' R Rf) {Φ Φ'} (hS : Φ' ∈ G.M'.So B.ψ B.τ₁)
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' ∧ Match B G X R Rf Φ Φ' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, e1, e2, -⟩ := id h
  have fam : ∀ i, Fam G.M (φ i) := fun i => ⟨(hi i).2.1, T.eventually_cofinite_notMem.mono (hi i).2.2⟩
  have fam' : ∀ j, Fam G.M' (φ' j) := fun j => ⟨(hj j).2.1, T.eventually_cofinite_notMem.mono (hj j).2.2⟩
  refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (fam i).1, (fam i).2, rfl⟩,
    e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (fam' j).1, (fam' j).2, rfl⟩,
    hS, m, m', fun i => finPartFn (φ i), f, fun _ => f, fun j => finPartFn (φ' j), f', fun _ => f',
    fun i => ⟨(fam i).sb hM.triple.geo.hM, tendsto_const_nhds⟩, fun j => ⟨(fam' j).sb hM.triple.geo.hM', tendsto_const_nhds⟩,
    e1, e2, fun _ => ⟨?_, ?_⟩⟩
  · show ∑ j, pure (f' j) (φ' j) ∈ _
    rw [← e2]; exact hS
  · show PolMatch B G X R Rf (∑ i, pure (f i) (φ i)) (∑ j, pure (f' j) (φ' j))
    rw [← e1, ← e2]; exact h

end GlobalTheory.ThK.Partner

namespace GlobalTheory.ThK

end GlobalTheory.ThK

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImplocusOpenClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem implocus_open_closed : ∀ (Y : Scheme.{0}) (Z : Over Y) (P Q : ∀ T : Over Y, (T ⟶ Z) → Prop), IsFinite Z.hom → Etale Z.hom → GlobalTheory.LevCover.ClopenCond Z P → GlobalTheory.LevCover.ClopenCond Z Q → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ z : Over.mk x ⟶ Z, P _ z → Q _ z := by
  intro Y Z P Q hfin het hP hQ
  obtain ⟨U, hUc, HU⟩ := hP
  obtain ⟨V, hVc, HV⟩ := hQ
  let B : Set Z.left := (U : Set Z.left) \ V
  have hBo : IsOpen B := U.isOpen.sdiff hVc
  have hBc : IsClosed B := hUc.sdiff V.isOpen
  have c1 : ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ (Z.hom.base '' B)ᶜ ↔
      ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z := by
    intro Tb t
    constructor
    · intro hW T σ hσ z hPz
      rw [HU] at hPz
      rw [HV]
      rintro _ ⟨w, rfl⟩
      by_contra hv
      have hb : z.left.base w ∈ B := ⟨hPz ⟨w, rfl⟩, hv⟩
      apply hW ⟨σ.base w, rfl⟩
      refine ⟨_, hb, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w z, ← hσ, Scheme.Hom.comp_apply]
    · intro H
      rintro _ ⟨τ, rfl⟩ ⟨u, hu, hτ⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback τ u hτ.symm
      let O : (pullback t Z.hom).Opens := (pullback.snd t Z.hom) ⁻¹ᵁ ⟨B, hBo⟩
      let T : Over Y := Over.mk (O.ι ≫ pullback.fst t Z.hom ≫ t)
      let z : T ⟶ Z := Over.homMk (O.ι ≫ pullback.snd t Z.hom) (by simp [T, pullback.condition])
      have hmem : ∀ w, O.ι.base w ∈ (O : Set _) := fun w => by
        rw [← Scheme.Opens.range_ι O]; exact ⟨w, rfl⟩
      have hPz : P T z := by
        rw [HU]
        rintro _ ⟨w, rfl⟩
        exact (hmem w).1
      have hQz := H T (O.ι ≫ pullback.fst t Z.hom) (Category.assoc _ _ _) z hPz
      rw [HV] at hQz
      have hpO : p ∈ Set.range O.ι.base := by
        rw [Scheme.Opens.range_ι O]
        show (pullback.snd t Z.hom).base p ∈ B
        rw [hp2]; exact hu
      obtain ⟨w, hw⟩ := hpO
      apply hu.2
      have := hQz ⟨w, rfl⟩
      simpa [z, Scheme.Hom.comp_apply, hw, hp2] using this
  refine ⟨(Z.hom.base '' B)ᶜ, (Z.hom.isClosedMap _ hBc).isOpen_compl,
    (Z.hom.isOpenMap _ hBo).isClosed_compl, c1, ?_⟩
  intro k _ _ x
  constructor
  · intro hW z hPz
    exact (c1 (Sp k) x).1 hW (Over.mk x) (𝟙 _) (Category.id_comp _) z hPz
  · intro H
    rintro _ ⟨s, rfl⟩ ⟨u, hu, hs⟩
    let Bo : Z.left.Opens := ⟨B, hBo⟩
    haveI : IsClosedImmersion Bo.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hBc)
    have huB : u ∈ Set.range Bo.ι.base := by rw [Scheme.Opens.range_ι]; exact hu
    obtain ⟨v, hv⟩ := huB
    obtain ⟨w, hw⟩ := GlobalTheory.LevCover.exists_lift_geom (Bo.ι ≫ Z.hom) x (by
      rintro _ ⟨s', rfl⟩
      refine ⟨v, ?_⟩
      rw [Subsingleton.elim s' s, Scheme.Hom.comp_apply, hv, hs])
    let z : Over.mk x ⟶ Z := Over.homMk (w ≫ Bo.ι) (by simpa using hw)
    have hPz : P _ z := by
      rw [HU]
      rintro _ ⟨y, rfl⟩
      have : (Bo.ι.base (w.base y)) ∈ (Bo : Set Z.left) := by
        rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
      exact this.1
    have hQz := H z hPz
    rw [HV] at hQz
    let y0 : Sp k := (⊥ : PrimeSpectrum k)
    have h1 : (Bo.ι.base (w.base y0)) ∈ (Bo : Set Z.left) := by
      rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
    exact h1.2 (hQz ⟨y0, rfl⟩)

end GlobalTheory.LevCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem clopenCond_comp_eq_one {Y : Scheme.{0}} (Zt B : Over Y) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : IsUnit (n : Γ(Y, ⊤))) (g : Zt ⟶ B) (hg : g ^ n = 1) :
    ClopenCond Zt (fun _ z => z ≫ g = 1) := by
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hn
  obtain ⟨u, hu, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n g hg
  obtain ⟨u', hu', -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n (1 : Zt ⟶ B) (one_pow n)
  refine (clopenCond_eq u u').congr fun T z => ⟨fun h => ?_, fun h => ?_⟩
  · have hz : (z ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion B n (z ≫ g) hz).unique ?_ ?_
    · rw [Category.assoc, hu]
    · rw [Category.assoc, hu', MonObj.comp_one, h]
  · rw [← hu, ← Category.assoc, h, Category.assoc, hu', MonObj.comp_one]

theorem kerlocus_open_closed : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  intro Y A _ _ n J _ B _ f B' _ f' hA hB hB' hf hf' hn
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  have hι : torsion.ι A n ^ n = 1 := GlobalTheory.LatticeTorsion.torsionι_pow_eq_one A n
  have hpow : ∀ (C : Over Y) [GrpObj C] (g : A ⟶ C) [IsMonHom g], (torsion.ι A n ≫ g) ^ n = 1 := by
    intro C _ g _
    rw [← MonObj.pow_comp, hι, MonObj.one_comp]
  obtain ⟨W, hWo, hWc, H1, H2⟩ := implocus_open_closed Y (torsion A n)
    (fun _ z => ∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) (fun _ z => z ≫ (torsion.ι A n ≫ f') = 1) hfin het
    (ClopenCond.forall_finite fun i =>
      clopenCond_comp_eq_one _ (B i) (hB i) n hn _ (hpow (B i) (f i)))
    (clopenCond_comp_eq_one _ B' hB' n hn _ (hpow B' f'))
  have key : ∀ T : Over Y, (∀ z : T ⟶ torsion A n, (∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) →
      z ≫ (torsion.ι A n ≫ f') = 1) ↔
      ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
    intro T
    constructor
    · intro H a ha hfa
      obtain ⟨z, hz, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A n a ha
      have h := H z (fun i => by rw [← Category.assoc, hz, hfa i])
      rwa [← Category.assoc, hz] at h
    · intro H z hz
      have h := H (z ≫ torsion.ι A n) (by rw [← MonObj.comp_pow, hι, MonObj.comp_one])
        (fun i => by rw [Category.assoc]; exact hz i)
      rwa [Category.assoc] at h
  refine ⟨W, hWo, hWc, fun Tb t => (H1 Tb t).trans ?_, fun k _ _ x => (H2 k x).trans (key _)⟩
  exact forall_congr' fun T => forall_congr' fun σ => forall_congr' fun _ => key T

end GlobalTheory.LevCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_torsion_kernel_locus : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  first | (exact @GlobalTheory.LevCover.kerlocus_open_closed) | (exact GlobalTheory.LevCover.kerlocus_open_closed) | (intros; apply GlobalTheory.LevCover.kerlocus_open_closed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLabelCommonGenericFibrePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLabelCommonGenericFibrePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

open MonObj

namespace GlobalTheory.Poinc.DeepLab

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

section Push
variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun _ _ e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

end Push

theorem exists_lab {Γ₁ Γ₂ H : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Group H] (L : ℕ)
    (f : Multiplicative Γ₂ →* H) (s : Multiplicative Γ₁ →* H)
    (uniq : ∀ z : H, z ^ L = 1 → ∃! b : Γ₂, f (Multiplicative.ofAdd b) = z)
    (hsL : ∀ a : Γ₁, s (Multiplicative.ofAdd a) ^ L = 1) :
    ∃ lab : Γ₁ →+ Γ₂, ∀ a, f (Multiplicative.ofAdd (lab a)) = s (Multiplicative.ofAdd a) := by
  choose l hl hu using fun a => uniq _ (hsL a)
  refine ⟨AddMonoidHom.mk' l fun a b => (hu (a + b) _ ?_).symm, hl⟩
  simp only [ofAdd_add, map_mul, hl]

theorem nsmul_self_eq_zero {κ : Type} (L : ℕ) (a : κ → ZMod L) : L • a = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem map_pow_self {κ H : Type} [Group H] (L : ℕ) (p : Multiplicative (κ → ZMod L) →* H) (a : κ → ZMod L) :
    p (Multiplicative.ofAdd a) ^ L = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_self_eq_zero, ofAdd_zero, map_one]

end GlobalTheory.Poinc.DeepLab

namespace GlobalTheory.Poinc.DeepLab

theorem exists_lab_same : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (φ : Ω₁ →+* Ω₂) (h : S₁.R →+* S₂.R) (ψ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), (∀ a, ((h a : S₂.R) : Ω₂) = φ a) → IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap h) ψ → LBIso ρ₂.P.L (ρ₁.P.L.pull ψ) → (∀ E, (ε₂ E).left ≫ ψ = ψ ≫ (ε₁ E).left) → S₁.r * S₁.N ∣ S₂.r * S₂.N → ∃ lab : S₁.Gam →+ S₂.Gam, Same ρ₁ ε₁ ρ₂ ε₂ lab φ ∧ ∀ x : S₂.Gam, ∃ a, lab a = (S₂.r * S₂.N / (S₁.r * S₁.N)) • x := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ ε₁ ε₂ φ h ψ hh hpb hL hε hd
  have hcomp : S₂.R.val.toRingHom.comp h = φ.comp S₁.R.val.toRingHom := RingHom.ext fun a => hh a
  have hsp : spMap (φ.comp S₁.R.val.toRingHom) = spMap S₂.R.val.toRingHom ≫ spMap h := by
    rw [← hcomp, spMap_comp]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap h) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ ψ = spMap h ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have uniq : ∀ z : Over.mk x₀ ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, (preHom V₂).comp p₂ (Multiplicative.ofAdd b) = z := fun z hz =>
    ρ₂.pt_bij K x₀ z hz
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    obtain ⟨c, hc⟩ := hd
    rw [hc, pow_mul, map_pow_self, one_pow]
  have hsL : ∀ a : S₁.Gam, (preHom V₂).comp σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [MonoidHom.comp_apply, ← map_pow, hσL, map_one]
  obtain ⟨lab, hlab⟩ := exists_lab _ _ _ uniq hsL
  have hlabl : ∀ a : S₁.Gam, x₀ ≫ (ρ₂.pt (lab a)).left = x₀ ≫ (σ (Multiplicative.ofAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hlab a)
  haveI := epi_spMap_field (algebraMap Ω₂ K)
  refine ⟨lab, ?_, ?_⟩
  · let P₀ := GlobalTheory.StrictPull.polPull ρ₂.P (spMap S₂.R.val.toRingHom)
    refine ⟨P₀, pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ ψ,
      pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom),
      fun E => (Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E), ?_, isGrpPullback_pullback _ _, ?_,
      GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, ?_, ?_⟩
    · rw [hsp]; exact IsGrpPullback.comp (isGrpPullback_pullback _ _) hpb
    · exact GlobalTheory.PolDeg.lbIso_pull_comp hL _ rfl
    · intro E
      have e₁ : ((Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E)).left ≫
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) =
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ (ε₂ E).left := pullback.lift_fst _ _ _
      refine ⟨?_, e₁⟩
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) e₁).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (hε E)).trans (Category.assoc _ _ _).symm)))
    · intro x
      refine ⟨pullback.lift (spMap S₂.R.val.toRingHom ≫ (ρ₂.pt (lab x)).left) (𝟙 _) ?_, ?_,
        pullback.lift_fst _ _ _⟩
      · rw [Category.assoc, Over.w]; simp
      · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (pullback.lift_fst _ _ _)).trans ?_)
        rw [hsp, ← cancel_epi (spMap (algebraMap Ω₂ K))]
        have e₂ := congrArg (· ≫ ψ) (hlabl x)
        simp only [x₀, Category.assoc] at e₂ ⊢
        rw [e₂, hσl]
        rfl
  · intro x
    set y := (S₂.r * S₂.N / (S₁.r * S₁.N)) • x with hy
    have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
      rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, Nat.mul_div_cancel' hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
    let T₀ : Over (Sp S₂.R) := Over.mk x₀
    let V₁ : Over.mk (x₀ ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap h) (by simp)
    let z₁ : Over.mk (x₀ ≫ spMap h) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
    have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
      have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
        have h3 := congrArg (preHom V₂) hyL
        rwa [map_pow, map_one] at h3
      show (pushHom hpb T₀) _ ^ _ = 1
      rw [← map_pow, h0, map_one]
    obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap h) z₁ hz₁
    refine ⟨a, ?_⟩
    have hpush : pushHom hpb T₀ (V₂ ≫ σ (Multiplicative.ofAdd a)) = V₁ ≫ ρ₁.pt a := by
      apply Over.OverMorphism.ext
      show (V₂ ≫ σ _).left ≫ ψ = (V₁ ≫ ρ₁.pt a).left
      simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
      rw [hσl]
      rfl
    have h1 : V₂ ≫ σ (Multiplicative.ofAdd a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
    have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
      rwa [map_pow, map_one] at h3
    exact (uniq _ h2).unique ((hlab a).trans h1) rfl

end GlobalTheory.Poinc.DeepLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLabelCommonGenericFibrePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLabel_common_generic_fibre_pullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (φ : Ω₁ →+* Ω₂) (h : S₁.R →+* S₂.R) (ψ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), (∀ a, ((h a : S₂.R) : Ω₂) = φ a) → IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap h) ψ → LBIso ρ₂.P.L (ρ₁.P.L.pull ψ) → (∀ E, (ε₂ E).left ≫ ψ = ψ ≫ (ε₁ E).left) → S₁.r * S₁.N ∣ S₂.r * S₂.N → ∃ lab : S₁.Gam →+ S₂.Gam, Same ρ₁ ε₁ ρ₂ ε₂ lab φ ∧ ∀ x : S₂.Gam, ∃ a, lab a = (S₂.r * S₂.N / (S₁.r * S₁.N)) • x := by
  first | exact @GlobalTheory.Poinc.DeepLab.exists_lab_same | exact GlobalTheory.Poinc.DeepLab.exists_lab_same | (intros; apply GlobalTheory.Poinc.DeepLab.exists_lab_same <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompSquare
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SharpIdent

theorem lift_comp_square {S S' : Scheme.{0}} {G : Over S} {G₁ G₂ T : Over S'} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G.left} {φ₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {ψ₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (hφ : IsSquare φ φ₂) (hψ : IsSquare ψ ψ₂) (x x' : T ⟶ G₁) (y y' : T ⟶ G₂) (h : x.left ≫ φ = y.left ≫ ψ)
    (h' : x'.left ≫ φ = y'.left ≫ ψ) : (lift x x').left ≫ φ₂ = (lift y y').left ≫ ψ₂ := by
  have e₁ : ((lift x x').left ≫ φ₂) ≫ (fst G G).left = ((lift y y').left ≫ ψ₂) ≫ (fst G G).left := by
    rw [Category.assoc, Category.assoc, hφ.1, hψ.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_fst, h]
  have e₂ : ((lift x x').left ≫ φ₂) ≫ (snd G G).left = ((lift y y').left ≫ ψ₂) ≫ (snd G G).left := by
    rw [Category.assoc, Category.assoc, hφ.2, hψ.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_snd, lift_snd, h']
  exact pullback.hom_ext e₁ e₂

end GlobalTheory.Poinc.SharpIdent
end
end

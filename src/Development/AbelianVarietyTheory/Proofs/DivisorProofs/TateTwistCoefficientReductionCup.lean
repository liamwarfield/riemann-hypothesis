module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolution
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedQis

theorem quasiIso_of_cone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone {R : Type} [CommRing R] (F : Shv R) (hF : FlatS F) (T : Cx R) (hT : ∀ t, FlatS (T.X t))
    (ε : sgl F ⟶ T) (n : ℤ) : FlatS ((mappingCone ε).X n) := by
  obtain ⟨hiso, hzero⟩ := GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero R
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod ε n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ (hT n))
  by_cases h : n + 1 = 0
  · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
  · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

theorem quasiIso_extCx_of_flat : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q))
    [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε →
    QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  intro Q q _ h F T _ hF hT ε hε
  have hK : (mappingCone ε).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  haveI : (mappingCone ε).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  have hE := GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow Q q h (mappingCone ε) (-1) (flatS_cone F hF T hT ε) hK
  have hC : (mappingCone (((extSh (ZMod.castHom h (ZMod q))).mapHomologicalComplex _).map ε)).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso ε (extSh (ZMod.castHom h (ZMod q))))
  exact quasiIso_of_cone_acyclic _ hC

end GlobalTheory.EtC.RedQis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolutionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q)) [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε → QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  first | exact @GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat | exact GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat | (intros; apply GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolution
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ScalarExt

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

theorem agree_on_twist {Q q : ℕ} [NeZero Q] (k : ℤ) {T : Cx (ZMod Q)} {J : Cx (ZMod q)} (ε : sgl (tw Q k) ⟶ T)
    (σ σ' : SemiMap T J)
    (he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))))
    (U : Scheme.{0}) (y : Sec (tw Q k) U) :
    σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) = σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) := by
  refine ((GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (J.X 0) U).1 _ _ (loc_mono ((GlobalTheory.T.tateTwist_sections_locally_generated Q k).1 U y) fun V g hg => ?_))
  rw [σ.nat, σ'.nat, sec_map_res, sec_map_res]
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · rw [h0]; simp
  · have hm : ∀ {A B : Shv (ZMod Q)} (φ : A ⟶ B) (x : Sec A V), Sec.map φ (c • x) = c • Sec.map φ x :=
      fun φ x => map_nsmul (φ.hom.app (op V)).hom c x
    rw [hc, hm, hm, map_nsmul, map_nsmul, he]

end GlobalTheory.EtC.ScalarExt

namespace GlobalTheory.EtC.ScalarExt

theorem semiMap_op_eq_of_flat_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  intro Q q _ h k T e hT hflat σ σ' hσ E n x
  obtain ⟨hge, ε, hqi, hεe⟩ := hT
  haveI := hge
  have hl := zmod_semilinear h σ
  have hl' := zmod_semilinear h σ'
  let εb : sgl ((ext (ZMod.castHom h (ZMod q))).obj (tw Q k)) ⟶ (extCx (ZMod.castHom h (ZMod q))).obj T :=
    ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv ≫ (extCx (ZMod.castHom h (ZMod q))).map ε
  have hq2 : QuasiIso ((extCx (ZMod.castHom h (ZMod q))).map ε) :=
    GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution Q q h (tw Q k) T (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q k) hflat ε hqi
  haveI : IsIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := Iso.isIso_inv _
  have hq1 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := quasiIso_of_isIso _
  haveI : QuasiIso εb := quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _
  haveI : (res (ZMod q) (tw q k)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q k)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsStrictlyGE 0)
  haveI : IsIso (sglι (tw Q k)) := by unfold sglι; exact Iso.isIso_inv _
  have he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) := fun U ζ => by
    rw [hεe]; exact hσ U ζ
  have hcomp : εb ≫ semiBar σ hl = εb ≫ semiBar σ' hl' := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst hi
      have key : (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ hl).f 0 =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ' hl').f 0 := by
        change (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ hl 0) =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ' hl' 0)
        rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        rw [← cancel_epi (sglι (tw Q k))]
        ext U y
        exact agree_on_twist k ε σ σ' he U.unop y
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp only [εb]
      erw [HomologicalComplex.comp_f, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) key
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ _ εb).2 _ _ hcomp
  have h1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ (semiBar σ hl) (semi_factor σ hl)).1 E n x
  have h2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ' (semiBar σ' hl') (semi_factor σ' hl')).1 E n x
  rw [h1, h2, ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 _ _ ⟨H⟩ _ n).2]

end GlobalTheory.EtC.ScalarExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolutionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  first | (exact @GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (exact GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (intros; apply GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section

namespace GlobalTheory.EtC.SemiTens

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.map f z) = Sec.map f (Sec.res g z) := by
  have := congrArg (fun k => k.hom z) (f.hom.naturality g.op)
  simpa using this.symm

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (z : Sec F U) :
    Sec.map (0 : F ⟶ G) z = 0 := by
  first
  | rfl
  | (show ((0 : F ⟶ G).hom.app (op U)).hom z = 0
     rw [Sheaf.Hom.zero_hom]; rfl)
  | (simp [Sec.map, Sheaf.zero_val])

variable {Q : ℕ} {R : Type} [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R}

def pairHom (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →+ Sec (J.X t) U →+ Sec (K'.X w) U :=
  AddMonoidHom.mk' (fun a => ((ν.mul U s t w h (ρ₁.app U s a)).toAddMonoidHom).comp (ρ₂.app U t))
    (fun a₁ a₂ => by ext b; simp)

theorem pairHom_smul (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (r : ULift.{1} (ZMod Q)) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    pairHom ν ρ₁ ρ₂ U s t w h (r • a) b = pairHom ν ρ₁ ρ₂ U s t w h a (r • b) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ULift.{1} (ZMod Q)) = r :=
    ⟨(r.down.cast : ℤ), ULift.ext (by change ((r.down.cast : ℤ) : ZMod Q) = r.down; exact ZMod.intCast_zmod_cast _)⟩
  simp [pairHom, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply]

def bmap (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →+ Sec (K'.X w) U := by
  classical
  exact DirectSum.toAddMonoid fun p =>
    TensorProduct.liftAddHom (pairHom ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2) (pairHom_smul ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2)

theorem bmap_of (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    bmap ν ρ₁ ρ₂ U w (DirectSum.of _ p (a ⊗ₜ b)) = ν.mul U p.1.1 p.1.2 w p.2 (ρ₁.app U _ a) (ρ₂.app U _ b) := by
  unfold bmap
  rw [DirectSum.toAddMonoid_of]
  simp [pairHom]

theorem lift_of (τ : Pair I J T) (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.of _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.toModule_lof]
  simp

theorem tensRes_of {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p (a ⊗ₜ b)) = DirectSum.of _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  unfold Tens.res
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.lmap_lof]
  simp [DirectSum.lof_eq_of]

theorem bmap_nat (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (bmap ν ρ₁ ρ₂ U w x) = bmap ν ρ₁ ρ₂ V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [bmap_of, tensRes_of, bmap_of, ν.nat, ρ₁.nat, ρ₂.nat]
    | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add (f := _)] using e
  | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add (f := _)] using e

end GlobalTheory.EtC.SemiTens

namespace GlobalTheory.EtC


open SemiTens in
theorem semiMap_of_tensorPair : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T),
    τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K',
    ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  intro Q R _ I J T I' J' K' τ hτ ν ρ₁ ρ₂
  have H := fun w => GlobalTheory.T.sheafComplexPairing_tensor_universal_property (ZMod Q) R τ hτ w (K'.X w) (fun U => bmap ν ρ₁ ρ₂ U w)
    (fun V U g x => bmap_nat ν ρ₁ ρ₂ g w x)
  choose φ hnat hlift using H
  have hmul : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      φ w U (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
    intro U s t w h a b
    have := hlift w U (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))
    rw [lift_of, bmap_of] at this
    exact this
  have key : ∀ (V : Scheme.{0}) (s : ℤ) (x : Tens I J V s),
      Sec.map (K'.d s (s + 1)) (bmap ν ρ₁ ρ₂ V s x) = φ (s + 1) V (Sec.map (T.d s (s + 1)) (τ.lift V s x)) := by
    intro V s x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        obtain ⟨⟨s₁, t₁⟩, hp⟩ := p
        rw [bmap_of, lift_of, ν.leibniz, τ.leibniz, map_add (f := _), Units.smul_def, Units.smul_def, map_zsmul, hmul, hmul,
          ρ₁.comm, ρ₂.comm]
      | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add (f := _)] using e
    | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add (f := _)] using e
  refine ⟨⟨fun U w => φ w U, fun g w a => hnat w _ _ g a, ?_⟩, hmul⟩
  intro U s t y
  by_cases hst : (ComplexShape.up ℤ).Rel s t
  · have ht : t = s + 1 := hst.symm
    subst ht
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R (K'.X (s + 1)) U).1
    obtain ⟨S, hS, hP⟩ := hτ.1 U s y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    rw [res_map, hnat, ← hx, hlift, key, hnat, res_map, ← hx]
  · rw [T.shape s t hst, K'.shape s t hst, map_zero', map_zero', map_zero]

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiMap_of_tensorPairing : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K', ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  first | (exact @GlobalTheory.EtC.semiMap_of_tensorPair) | (exact GlobalTheory.EtC.semiMap_of_tensorPair) | (intros; apply GlobalTheory.EtC.semiMap_of_tensorPair  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocForallFinset
open CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.LocalizedFinsetForAll

theorem loc_forall_finset {U : Scheme.{0}} {ι : Type u} (s : Finset ι)
    {P : ι → (V : Scheme.{0}) → (V ⟶ U) → Prop} (h : ∀ i ∈ s, GlobalTheory.EtC.Loc U (P i)) :
    GlobalTheory.EtC.Loc U fun (V : Scheme.{0}) (g : V ⟶ U) ↦ ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨S, hS, hSP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨T, hT, hTP⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨S ⊓ T, GrothendieckTopology.intersection_covering _ hS hT, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hSP V g hg.1
    · exact hTP V g hg.2 i hi

end GlobalTheory.LocalizedFinsetForAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexes
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC.FlatTens

section Loc
variable {U : Scheme.{0}}

theorem loc_mono {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g → Q V g) (hP : Loc U P) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

theorem loc_of_forall {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := hP
  obtain ⟨T, hT, hQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_trans {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hTP using hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hTP V g hg W k hk

theorem loc_finset {ι : Type*} (s : Finset ι) {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  first
  | exact @_root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset
  | exact _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset
  | (apply _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset ..)

end Loc

variable {R : Type} [CommRing R]

def locZero (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) : Submodule (ULift.{1} R) (M.obj (op U)) where
  carrier := {x | Loc U fun V g => (M.map g.op).hom x = 0}
  zero_mem' := loc_of_forall fun V g => map_zero _
  add_mem' {x y} hx hy := loc_mono (fun V g h => by simp [h.1, h.2]) (loc_and hx hy)
  smul_mem' r x hx := loc_mono (fun V g h => by simp [h]) hx

def locIm {A M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : A ⟶ M) (U : Scheme.{0}) :
    Submodule (ULift.{1} R) (M.obj (op U)) where
  carrier := {x | Loc U fun V g => (M.map g.op).hom x ∈ LinearMap.range (f.app (op V)).hom}
  zero_mem' := loc_of_forall fun V g => by simp
  add_mem' {x y} hx hy := loc_mono (fun V g h => by simpa using add_mem h.1 h.2) (loc_and hx hy)
  smul_mem' r x hx := loc_mono (fun V g h => by simpa using Submodule.smul_mem _ r h) hx

def tensP {ι : Type} (A B : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (⨁ i, (A i).obj U ⊗[ULift.{1} R] (B i).obj U)
  map g := ModuleCat.ofHom (DirectSum.lmap fun i => TensorProduct.map ((A i).map g).hom ((B i).map g).hom)
  map_id U := by
    classical
    ext1
    refine DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun a b => ?_
    simp [DirectSum.lof_eq_of, DirectSum.lmap_of]
  map_comp f g := by
    classical
    ext1
    refine DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun a b => ?_
    simp [DirectSum.lof_eq_of, DirectSum.lmap_of]

theorem tensP_map_of {ι : Type} [DecidableEq ι] (A B : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (i : ι) (a : (A i).obj U) (b : (B i).obj U) :
    ((tensP A B).map g).hom (DirectSum.of (fun i => (A i).obj U ⊗[ULift.{1} R] (B i).obj U) i (a ⊗ₜ b)) =
      DirectSum.of (fun i => (A i).obj V ⊗[ULift.{1} R] (B i).obj V) i (((A i).map g).hom a ⊗ₜ ((B i).map g).hom b) := by
  exact (DirectSum.lmap_of (fun i => TensorProduct.map ((A i).map g).hom ((B i).map g).hom) i (a ⊗ₜ b)).trans
    (by rw [TensorProduct.map_tmul])

def tensMap {ι : Type} {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : ∀ i, A i ⟶ M i)
    (g : ∀ i, B i ⟶ N i) : tensP A B ⟶ tensP M N where
  app U := ModuleCat.ofHom (DirectSum.lmap fun i => TensorProduct.map ((f i).app U).hom ((g i).app U).hom)
  naturality U V k := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => DFinsupp.ext fun i => ?_)
    have hf : ((f i).app V).hom ∘ₗ ((A i).map k).hom = ((M i).map k).hom ∘ₗ ((f i).app U).hom :=
      congrArg ModuleCat.Hom.hom ((f i).naturality k)
    have hg : ((g i).app V).hom ∘ₗ ((B i).map k).hom = ((N i).map k).hom ∘ₗ ((g i).app U).hom :=
      congrArg ModuleCat.Hom.hom ((g i).naturality k)
    let y : ⨁ i, (A i).obj U ⊗[ULift.{1} R] (B i).obj U := x
    change TensorProduct.map ((f i).app V).hom ((g i).app V).hom (TensorProduct.map ((A i).map k).hom ((B i).map k).hom (y i)) =
      TensorProduct.map ((M i).map k).hom ((N i).map k).hom (TensorProduct.map ((f i).app U).hom ((g i).app U).hom (y i))
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hf, hg, TensorProduct.map_comp, LinearMap.comp_apply]

theorem tensMap_of {ι : Type} [DecidableEq ι] {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    (f : ∀ i, A i ⟶ M i) (g : ∀ i, B i ⟶ N i) (U : Scheme.{0}ᵒᵖ) (i : ι) (a : (A i).obj U) (b : (B i).obj U) :
    ((tensMap f g).app U).hom (DirectSum.of (fun i => (A i).obj U ⊗[ULift.{1} R] (B i).obj U) i (a ⊗ₜ b)) =
      DirectSum.of (fun i => (M i).obj U ⊗[ULift.{1} R] (N i).obj U) i (((f i).app U).hom a ⊗ₜ ((g i).app U).hom b) := by
  exact (DirectSum.lmap_of (fun i => TensorProduct.map ((f i).app U).hom ((g i).app U).hom) i (a ⊗ₜ b)).trans
    (by rw [TensorProduct.map_tmul])

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) [DecidableEq {p : ℤ × ℤ // p.1 + p.2 = w}]
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p
      (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  convert DirectSum.toModule_lof (ULift.{1} R) (φ := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
    TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2)) p (a ⊗ₜ b) using 2
  · congr; exact Subsingleton.elim _ _
  · rfl
  · simp

def liftN {I J K : Cx R} (μ : Pair I J K) (w : ℤ) :
    tensP (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => (I.X p.1.1).obj) (fun p => (J.X p.1.2).obj) ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality U V k := by
    have h : μ.lift V.unop w ∘ₗ Tens.res k.unop w = ((K.X w).obj.map k).hom ∘ₗ μ.lift U.unop w := by
      classical
      refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, Tens.res, DirectSum.lmap_of, TensorProduct.map_tmul]
      rw [lift_of, lift_of]
      exact (μ.nat k.unop p.1.1 p.1.2 w p.2 a b).symm
    exact ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.congr_fun h x)

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) :=
  congr(($((liftN μ w).naturality g.op)).hom x)

end GlobalTheory.EtC.FlatTens

namespace GlobalTheory.EtC.FlatTens
open TensorProduct LinearMap

theorem exists_fg_tens {S A B : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (y : A ⊗[S] B) : ∃ (A0 : Submodule S A) (B0 : Submodule S B) (y0 : A0 ⊗[S] B0), A0.FG ∧ B0.FG ∧
      TensorProduct.map A0.subtype B0.subtype y0 = y := by
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
    exact ⟨S ∙ a, S ∙ b, ⟨a, Submodule.mem_span_singleton_self a⟩ ⊗ₜ ⟨b, Submodule.mem_span_singleton_self b⟩,
      Submodule.fg_span_singleton a, Submodule.fg_span_singleton b, rfl⟩
  | add x y hx hy =>
    obtain ⟨A1, B1, x1, hA1, hB1, rfl⟩ := hx
    obtain ⟨A2, B2, y2, hA2, hB2, rfl⟩ := hy
    refine ⟨A1 ⊔ A2, B1 ⊔ B2, TensorProduct.map (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_left) x1 +
      TensorProduct.map (Submodule.inclusion le_sup_right) (Submodule.inclusion le_sup_right) y2, hA1.sup hA2, hB1.sup hB2, ?_⟩
    rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp,
      ← TensorProduct.map_comp]
    rfl

theorem comm_lTensor {S M N N' : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup N'] [Module S N'] (h : N →ₗ[S] N') (z : M ⊗[S] N) :
    TensorProduct.comm S M N' (lTensor M h z) = rTensor M h (TensorProduct.comm S M N z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem key_alg {S A B I J : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup I] [Module S I] [AddCommGroup J] [Module S J] (f : A →ₗ[S] I) (g : B →ₗ[S] J) (y : A ⊗[S] B)
    (hy : TensorProduct.map f g y = 0) :
    ∃ (A0 : Submodule S A) (B0 : Submodule S B) (I1 : Submodule S I) (J1 : Submodule S J) (hA : A0 ≤ I1.comap f)
      (hB : B0 ≤ J1.comap g) (y0 : A0 ⊗[S] B0), I1.FG ∧ J1.FG ∧ TensorProduct.map A0.subtype B0.subtype y0 = y ∧
      TensorProduct.map (f.restrict hA) (g.restrict hB) y0 = 0 := by
  obtain ⟨A0, B0, y0, hA0, hB0, rfl⟩ := exists_fg_tens y
  set I0 := A0.map f
  set J0 := B0.map g
  set z0 : I0 ⊗[S] J0 := TensorProduct.map (f.submoduleMap A0) (g.submoduleMap B0) y0 with hz0
  have hz : TensorProduct.map I0.subtype J0.subtype z0 = 0 := by
    rw [hz0, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    exact (congrArg (fun h => h y0) (TensorProduct.map_comp f g A0.subtype B0.subtype)).trans hy
  have h1 : rTensor J I0.subtype (lTensor I0 J0.subtype z0) = rTensor J I0.subtype 0 := by
    rw [map_zero, ← LinearMap.comp_apply, rTensor_comp_lTensor]; exact hz
  obtain ⟨I1, hI1, hle, e1⟩ := (hA0.map f).exists_rTensor_fg_inclusion_eq h1
  rw [map_zero] at e1
  set z1 : I1 ⊗[S] J0 := rTensor J0 (Submodule.inclusion hle) z0 with hz1
  have hl : lTensor I1 J0.subtype z1 = 0 := by
    rw [hz1, ← LinearMap.comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor, LinearMap.comp_apply]
    exact e1
  have h2 : rTensor I1 J0.subtype (TensorProduct.comm S I1 J0 z1) = rTensor I1 J0.subtype 0 := by
    rw [map_zero, ← comm_lTensor, hl, map_zero]
  obtain ⟨J1, hJ1, hle', e2⟩ := (hB0.map g).exists_rTensor_fg_inclusion_eq h2
  rw [map_zero] at e2
  have hA : A0 ≤ I1.comap f := fun a ha => hle (Submodule.mem_map_of_mem ha)
  have hB : B0 ≤ J1.comap g := fun b hb => hle' (Submodule.mem_map_of_mem hb)
  refine ⟨A0, B0, I1, J1, hA, hB, y0, hI1, hJ1, rfl, ?_⟩
  have ef : f.restrict hA = Submodule.inclusion hle ∘ₗ f.submoduleMap A0 := LinearMap.ext fun _ => rfl
  have eg : g.restrict hB = Submodule.inclusion hle' ∘ₗ g.submoduleMap B0 := LinearMap.ext fun _ => rfl
  rw [ef, eg, TensorProduct.map_comp, LinearMap.comp_apply, ← hz0, ← lTensor_comp_rTensor, LinearMap.comp_apply, ← hz1]
  apply (TensorProduct.comm S I1 J1).injective
  rw [comm_lTensor, e2, map_zero]

end GlobalTheory.EtC.FlatTens

namespace GlobalTheory.EtC.FlatTens
open TensorProduct

variable {R : Type} [CommRing R]

def locZero2 (A B : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (V : Scheme.{0}) :
    Submodule (ULift.{1} R) (A.obj (op V) ⊗[ULift.{1} R] B.obj (op V)) where
  carrier := {z | Loc V fun W k => TensorProduct.map (A.map k.op).hom (B.map k.op).hom z = 0}
  zero_mem' := loc_of_forall fun W k => map_zero _
  add_mem' {x y} hx hy := loc_mono (fun W k h => by simp [h.1, h.2]) (loc_and hx hy)
  smul_mem' r x hx := loc_mono (fun W k h => by simp [h]) hx

theorem nat_apply {A M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : A ⟶ M) {U V : Scheme.{0}ᵒᵖ} (k : U ⟶ V)
    (a : A.obj U) : (f.app V).hom ((A.map k).hom a) = (M.map k).hom ((f.app U).hom a) := by
  have := congr(($(f.naturality k)).hom a)
  simpa using this

theorem tensor_locally_zero_of_exact {A B M N : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : A ⟶ M) (g : B ⟶ N)
    (hfs : ∀ (U : Scheme.{0}) (y : M.obj (op U)), Loc U fun V k => ∃ x, (f.app (op V)).hom x = (M.map k.op).hom y)
    (hgs : ∀ (U : Scheme.{0}) (y : N.obj (op U)), Loc U fun V k => ∃ x, (g.app (op V)).hom x = (N.map k.op).hom y)
    (hfi : ∀ (U : Scheme.{0}) (x : A.obj (op U)), (f.app (op U)).hom x = 0 → x ∈ locZero A U)
    (hgi : ∀ (U : Scheme.{0}) (x : B.obj (op U)), (g.app (op U)).hom x = 0 → x ∈ locZero B U)
    (U : Scheme.{0}) (y : A.obj (op U) ⊗[ULift.{1} R] B.obj (op U))
    (hy : TensorProduct.map (f.app (op U)).hom (g.app (op U)).hom y = 0) : y ∈ locZero2 A B U := by
  obtain ⟨A0, B0, I1, J1, hA, hB, y0, ⟨sI, hsI⟩, ⟨sJ, hsJ⟩, rfl, hy0⟩ := key_alg _ _ y hy
  have cI := loc_finset sI (fun m _ => hfs U m)
  have cJ := loc_finset sJ (fun m _ => hgs U m)
  refine loc_trans (loc_mono (fun V k h => ?_) (loc_and cI cJ))
  obtain ⟨hI, hJ⟩ := h
  have lI : I1 ≤ (LinearMap.range (f.app (op V)).hom).comap (M.map k.op).hom := by
    rw [← hsI, Submodule.span_le]
    intro m hm
    obtain ⟨x, hx⟩ := hI m hm
    exact ⟨x, hx⟩
  have lJ : J1 ≤ (LinearMap.range (g.app (op V)).hom).comap (N.map k.op).hom := by
    rw [← hsJ, Submodule.span_le]
    intro m hm
    obtain ⟨x, hx⟩ := hJ m hm
    exact ⟨x, hx⟩
  set yV := TensorProduct.map (A.map k.op).hom (B.map k.op).hom (TensorProduct.map A0.subtype B0.subtype y0) with hyV
  have e1 : (f.app (op V)).hom.rangeRestrict ∘ₗ (A.map k.op).hom ∘ₗ A0.subtype =
      ((M.map k.op).hom.restrict (fun x hx => lI hx)) ∘ₗ (f.app (op U)).hom.restrict hA :=
    LinearMap.ext fun a => Subtype.ext (nat_apply f k.op a.1)
  have e2 : (g.app (op V)).hom.rangeRestrict ∘ₗ (B.map k.op).hom ∘ₗ B0.subtype =
      ((N.map k.op).hom.restrict (fun x hx => lJ hx)) ∘ₗ (g.app (op U)).hom.restrict hB :=
    LinearMap.ext fun a => Subtype.ext (nat_apply g k.op a.1)
  have hker : yV ∈ LinearMap.ker (TensorProduct.map (f.app (op V)).hom.rangeRestrict (g.app (op V)).hom.rangeRestrict) := by
    have ec : TensorProduct.map (f.app (op V)).hom.rangeRestrict (g.app (op V)).hom.rangeRestrict ∘ₗ
        TensorProduct.map (A.map k.op).hom (B.map k.op).hom ∘ₗ TensorProduct.map A0.subtype B0.subtype =
        TensorProduct.map ((M.map k.op).hom.restrict (fun x hx => lI hx)) ((N.map k.op).hom.restrict (fun x hx => lJ hx)) ∘ₗ
        TensorProduct.map ((f.app (op U)).hom.restrict hA) ((g.app (op U)).hom.restrict hB) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, e1, e2, TensorProduct.map_comp]
    rw [LinearMap.mem_ker, hyV]
    exact (LinearMap.congr_fun ec y0).trans (by rw [LinearMap.comp_apply, hy0, map_zero])
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_ker_map _) (LinearMap.surjective_rangeRestrict _)
    (LinearMap.exact_subtype_ker_map _) (LinearMap.surjective_rangeRestrict _)] at hker
  have hle : LinearMap.range (LinearMap.lTensor (A.obj (op V)) (LinearMap.ker (g.app (op V)).hom.rangeRestrict).subtype) ⊔
      LinearMap.range (LinearMap.rTensor (B.obj (op V)) (LinearMap.ker (f.app (op V)).hom.rangeRestrict).subtype) ≤
      locZero2 A B V := by
    refine sup_le ?_ ?_
    · rintro _ ⟨u, rfl⟩
      induction u using TensorProduct.inductionOn with
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | tmul a b =>
        have hb : (g.app (op V)).hom b.1 = 0 := by
          have := b.2
          rw [LinearMap.mem_ker] at this
          exact congrArg Subtype.val this
        refine loc_mono (fun W k' h => ?_) (hgi V b.1 hb)
        change TensorProduct.map _ _ (a ⊗ₜ b.1) = 0
        rw [TensorProduct.map_tmul, h, TensorProduct.tmul_zero]
    · rintro _ ⟨u, rfl⟩
      induction u using TensorProduct.inductionOn with
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | tmul a b =>
        have ha : (f.app (op V)).hom a.1 = 0 := by
          have := a.2
          rw [LinearMap.mem_ker] at this
          exact congrArg Subtype.val this
        refine loc_mono (fun W k' h => ?_) (hfi V a.1 ha)
        change TensorProduct.map _ _ (a.1 ⊗ₜ b) = 0
        rw [TensorProduct.map_tmul, h, TensorProduct.zero_tmul]
  refine loc_mono (fun W k' h => ?_) (hle hker)
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, TensorProduct.map_comp,
    LinearMap.comp_apply]
  exact h

end GlobalTheory.EtC.FlatTens

namespace GlobalTheory.EtC.FlatTens
open TensorProduct

variable {R : Type} [CommRing R]

theorem tens_locIm {ι : Type} {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : ∀ i, A i ⟶ M i)
    (g : ∀ i, B i ⟶ N i)
    (hfs : ∀ i (U : Scheme.{0}) (y : (M i).obj (op U)), Loc U fun V k => ∃ x, ((f i).app (op V)).hom x = ((M i).map k.op).hom y)
    (hgs : ∀ i (U : Scheme.{0}) (y : (N i).obj (op U)), Loc U fun V k => ∃ x, ((g i).app (op V)).hom x = ((N i).map k.op).hom y)
    (U : Scheme.{0}) (x : (tensP M N).obj (op U)) : x ∈ locIm (tensMap f g) U := by
  classical
  suffices h : ∀ x' : ⨁ i, (M i).obj (op U) ⊗[ULift.{1} R] (N i).obj (op U), x' ∈ locIm (tensMap f g) U from h x
  intro x'
  induction x' using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add a b ha hb => exact add_mem ha hb
  | of i y =>
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a b =>
      refine loc_mono (fun V k h => ?_) (loc_and (hfs i U a) (hgs i U b))
      obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := h
      refine ⟨DirectSum.of (fun i => (A i).obj (op V) ⊗[ULift.{1} R] (B i).obj (op V)) i (a' ⊗ₜ b'), ?_⟩
      erw [tensMap_of, tensP_map_of, ha', hb']

theorem tens_locZero {ι : Type} {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : ∀ i, A i ⟶ M i)
    (g : ∀ i, B i ⟶ N i)
    (hfs : ∀ i (U : Scheme.{0}) (y : (M i).obj (op U)), Loc U fun V k => ∃ x, ((f i).app (op V)).hom x = ((M i).map k.op).hom y)
    (hgs : ∀ i (U : Scheme.{0}) (y : (N i).obj (op U)), Loc U fun V k => ∃ x, ((g i).app (op V)).hom x = ((N i).map k.op).hom y)
    (hfi : ∀ i (U : Scheme.{0}) (x : (A i).obj (op U)), ((f i).app (op U)).hom x = 0 → x ∈ locZero (A i) U)
    (hgi : ∀ i (U : Scheme.{0}) (x : (B i).obj (op U)), ((g i).app (op U)).hom x = 0 → x ∈ locZero (B i) U)
    (U : Scheme.{0}) (x : (tensP A B).obj (op U)) (hx : ((tensMap f g).app (op U)).hom x = 0) :
    x ∈ locZero (tensP A B) U := by
  classical
  let x' : ⨁ i, (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U) := x
  have hc : ∀ i, TensorProduct.map ((f i).app (op U)).hom ((g i).app (op U)).hom (x' i) = 0 := fun i =>
    congrArg (fun z : ⨁ i, (M i).obj (op U) ⊗[ULift.{1} R] (N i).obj (op U) => z i) hx
  have hof : ∀ i (y : (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U)), y ∈ locZero2 (A i) (B i) U →
      DirectSum.of (fun i => (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U)) i y ∈ locZero (tensP A B) U := by
    intro i y hy
    refine loc_mono (fun V k h => ?_) hy
    change DirectSum.lmap _ (DirectSum.of (fun i => (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U)) i y) = 0
    rw [DirectSum.lmap_of]
    exact (congrArg _ h).trans (map_zero _)
  have hx' : x = ∑ i ∈ x'.support, DirectSum.of _ i (x' i) := (DirectSum.sum_support_of x').symm
  rw [hx']
  exact Submodule.sum_mem _ fun i _ => hof i _ (tensor_locally_zero_of_exact (f i) (g i) (hfs i) (hgs i) (hfi i) (hgi i) U _ (hc i))

theorem flatS_tens : ∀ (R : Type) [CommRing R] {I J T : Cx R} (τ : Pair I J T), τ.IsTensor → (∀ t, FlatS (I.X t)) →
    (∀ t, FlatS (J.X t)) → ∀ w, FlatS (T.X w) := by
  intro R _ I J T τ hτ hI hJ w
  choose PI φI sI iI fI using hI
  choose PJ φJ sJ iJ fJ using hJ
  refine ⟨tensP (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => PI p.1.1) (fun p => PJ p.1.2),
    tensMap (fun p => φI p.1.1) (fun p => φJ p.1.2) ≫ liftN τ w, ?_, ?_, ?_⟩
  · intro U y
    refine loc_trans (loc_mono (fun V g h => ?_) (hτ.1 U w y))
    obtain ⟨x, hx⟩ := h
    refine loc_mono (fun W k h' => ?_) (tens_locIm (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => φI p.1.1)
      (fun p => φJ p.1.2) (fun p => sI p.1.1) (fun p => sJ p.1.2) V x)
    obtain ⟨z, hz⟩ := h'
    refine ⟨z, ?_⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hz]
    change τ.lift W w (Tens.res k w x) = _
    rw [lift_res, hx]
    simp [Sec.res]
  · intro U x hx
    refine loc_trans (loc_mono (fun V g h => ?_) (hτ.2 U w _ hx))
    have h' : ((tensMap (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => φI p.1.1) (fun p => φJ p.1.2)).app (op V)).hom
        (((tensP (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => PI p.1.1) (fun p => PJ p.1.2)).map g.op).hom x) = 0 := by
      rw [nat_apply]
      exact h
    refine loc_mono (fun W k h'' => ?_) (tens_locZero (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => φI p.1.1)
      (fun p => φJ p.1.2) (fun p => sI p.1.1) (fun p => sJ p.1.2) (fun p => iI p.1.1) (fun p => iJ p.1.2) V _ h')
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact h''
  · intro U hU
    haveI : ∀ p : {p : ℤ × ℤ // p.1 + p.2 = w}, Module.Flat (ULift.{1} R) ((PI p.1.1).obj (op U)) := fun p => fI _ U hU
    haveI : ∀ p : {p : ℤ × ℤ // p.1 + p.2 = w}, Module.Flat (ULift.{1} R) ((PJ p.1.2).obj (op U)) := fun p => fJ _ U hU
    haveI : ∀ p : {p : ℤ × ℤ // p.1 + p.2 = w},
        Module.Flat (ULift.{1} R) ((PI p.1.1).obj (op U) ⊗[ULift.{1} R] (PJ p.1.2).obj (op U)) := fun p => inferInstance
    exact Module.Flat.directSum

end GlobalTheory.EtC.FlatTens

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_of_flat_complexes : ∀ (R : Type) [CommRing R] {I J T : Cx R} (τ : Pair I J T), τ.IsTensor → (∀ t, FlatS (I.X t)) → (∀ t, FlatS (J.X t)) → ∀ w, FlatS (T.X w) := by
  first | (exact @GlobalTheory.EtC.FlatTens.flatS_tens) | (exact GlobalTheory.EtC.FlatTens.flatS_tens) | (intros; apply GlobalTheory.EtC.FlatTens.flatS_tens  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCup
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedCup

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem cpush_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (a : CohomologyClass K I n) : cpush K (𝟙 I) n a = a := by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

def semiPre {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K') :
    SemiMap T K' where
  app U s := (ρ.app U s).comp ((u.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := by
    change Sec.res g (ρ.app _ s (Sec.map (u.f s) a)) = ρ.app _ s (Sec.map (u.f s) (Sec.res g a))
    rw [ρ.nat, sec_map_res]
  comm U s t a := by
    change Sec.map (_ : _ ⟶ _) (ρ.app U s (Sec.map (u.f s) a)) = ρ.app U t (Sec.map (u.f t) (Sec.map (T.d s t) a))
    rw [ρ.comm, ← sec_map_comp, ← sec_map_comp, u.comm]

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (u : I ⟶ K)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x =
      Sec.map (u.f s) (ev (R := R) α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem semiPre_op {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K')
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) T n) :
    (semiPre u ρ).op.app E n x = ρ.op.app E n (cpush _ u n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n (zcomp α (Cocycle.ofHom u) (add_zero n))
  change _ = ρ.op.app E n (CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)))
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n _ β hβ]
  refine (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R (semiPre u ρ)).2 E n α β (fun p s h U y => ?_)
  rw [hβ p s h U y]
  change ρ.app U s (ev (R := S) (α.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y) = _
  rw [ev_comp_ofHom]
  rfl

theorem semiMap_cup : ∀ (S R : Type) [CommRing S] [CommRing R] {I J T : Cx S} {I' J' K' : Cx R} (τ : Pair I J T) (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (σ : SemiMap T K'), (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b)) → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains S).obj E) I n) (b : CohomologyClass ((chains S).obj E) J m), σ.op.app E k (τ.cup E hk a b) = ν.cup E hk (ρ₁.op.app E n a) (ρ₂.op.app E m b) := by
  intro S R _ _ I J T I' J' K' τ ν ρ₁ ρ₂ σ hσ E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW S τ hk).1 α β
  obtain ⟨α', hα'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).1 E m β
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).1 E k γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW S τ hk).2 α β γ hγ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).2 E k γ γ' hγ',
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).2 E n α α' hα', (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).2 E m β β' hβ']
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 α' β' γ' ?_).symm
  intro N w h U x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hγ' N w h U x, hγ N w h U x, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, hσ, ← hα', ← hβ', Units.smul_def]

theorem reduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j),
    red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  intro Q q _ hqQ E n m i j a b
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp hqQ)⟩
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod Q) (res _ (tw Q i)) (res _ (tw Q j))
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod Q) τ hτ).1 (twPair Q i j) (𝟙 _) (𝟙 _)
  have hcup : cup Q a b = cpush _ u _ (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod Q) τ (twPair Q i j) (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
    rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_semiMap_of_tensorPairing Q (ZMod q) τ hτ (twPair q i j) (redMap Q q i) (redMap Q q j)
  have h1 := semiMap_cup (ZMod Q) (ZMod q) τ (twPair q i j) (redMap Q q i) (redMap Q q j) σ hσ E rfl a b
  rw [hcup]
  change (redMap Q q (i + j)).op.app E (n + m) (cpush _ u _ _) = (twPair q i j).cup E rfl _ _
  rw [← semiPre_op]
  change _ = (twPair q i j).cup E rfl ((redMap Q q i).op.app E n a) ((redMap Q q j).op.app E m b)
  rw [← h1]
  have hres := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q i
  have hresj := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q j
  have htw := GlobalTheory.T.isTateTwistResolution_tensor_flat Q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) hres.1 hresj.1 hresj.2.1 τ hτ
  have hflat := GlobalTheory.T.flat_tensor_of_flat_complexes (ZMod Q) τ hτ hres.2.1 hresj.2.1
  refine GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution Q q hqQ (i + j) _ htw hflat _ _ ?_ E (n + m) _
  intro U ζ
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [hσ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ ξ hξ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ j U ζ ξ hξ, (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 U ξ]
  change (redMap Q q (i + j)).app U 0 (Sec.map (u.f 0) _) = _
  rw [hu]
  change (redMap Q q (i + j)).app U 0 ((twPair Q i j).mul U 0 0 0 _ (resGen i ζ) (resGen j ζ)) = _
  rw [(GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique Q i j).1 U ζ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ (i + j) U ζ ξ hξ]

end GlobalTheory.EtC.RedCup

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCupStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  exact @GlobalTheory.EtC.RedCup.reduction_cup
end

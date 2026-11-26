module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTest
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleExtendedPrincipalPolarisationDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatio
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqOneOfTranslDiffTrivialModel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqOneOfTranslDiffTrivialModel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.PrincipalModel
open GlobalTheory.UU GlobalTheory.AbLaw

theorem exists_common_overfield {k A B : Type} [Field k] [Field A] [Field B] (f : k →+* A) (g : k →+* B) :
    ∃ (L : Type) (_ : Field L) (a : A →+* L) (b : B →+* L), a.comp f = b.comp g := by
  let _ := f.toAlgebra
  let _ := g.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k A B)
  refine ⟨TensorProduct k A B ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg _ (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := k) (A := A) (B := B))

theorem exists_valuationSubring {W F Ω : Type} [CommRing W] [IsLocalRing W] [Field F] [Field Ω] (φ : W →+* F)
    (f : W →+* Ω) [IsLocalHom f] : ∃ (O : ValuationSubring F) (j : W →+* O) (L : Type) (_ : Field L) (a : Ω →+* L)
      (g : O →+* L), (algebraMap O F).comp j = φ ∧ IsLocalHom g ∧ a.comp f = g.comp j := by
  obtain ⟨O, h, hl⟩ := IsLocalRing.exists_factor_valuationRing φ
  let j : W →+* O := φ.codRestrict O.toSubring h
  have : IsLocalHom j := hl
  obtain ⟨L, _, a, b, e⟩ := exists_common_overfield (IsLocalRing.ResidueField.lift f) (IsLocalRing.ResidueField.map j)
  refine ⟨O, j, L, inferInstance, a, b.comp (IsLocalRing.residue O), rfl, inferInstance, ?_⟩
  rw [← IsLocalRing.ResidueField.lift_comp_residue f, ← RingHom.comp_assoc, e, RingHom.comp_assoc,
    IsLocalRing.ResidueField.map_comp_residue, RingHom.comp_assoc]

theorem exists_embedding (V K W : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W] (h : Function.Injective (algebraMap V W)) :
    ∃ φ : W →+* AlgebraicClosure K, Function.Injective φ ∧ φ.comp (algebraMap V W) =
      (algebraMap K (AlgebraicClosure K)).comp (algebraMap V K) := by
  have i : Function.Injective (algebraMap V (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq V K]
    exact (algebraMap K _).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 h
  have : FaithfulSMul V (AlgebraicClosure K) := (faithfulSMul_iff_algebraMap_injective _ _).2 i
  let φ : W →ₐ[V] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, ?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    change Ideal.comap (algebraMap V W) (RingHom.ker φ.toRingHom) = ⊥
    rw [RingHom.comap_ker, show φ.toRingHom.comp (algebraMap V W) = algebraMap V _ from φ.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).1 i
  · rw [← IsScalarTower.algebraMap_eq]; exact φ.comp_algebraMap

theorem triv_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T)
    (h : Triv (translDiff A L x)) : Triv (translDiff A L (g ≫ x)) := by
  obtain ⟨d, hd⟩ := h
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ d hd (g ▷ A).left⟩
  have h3 : (fun k : Fin 2 => (g ▷ A).left ≫ ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem cubWeil_generic (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : RigLB A} (c : CubicalStr A L) {O F k : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F] [Field k] (g : O →+* k) [IsLocalHom g]
    {p : Sp O ⟶ S} {n : ℕ} (hn : IsUnit (n : O)) (X : Over.mk p ⟶ A) (hX : X ^ n = 1)
    {pk : Sp k ⟶ S} (ρk : Over.mk pk ⟶ Over.mk p) (hk : ρk.left = spMap g)
    {pF : Sp F ⟶ S} (ρF : Over.mk pF ⟶ Over.mk p) (hF : ρF.left = spMap (algebraMap O F))
    (ht : Triv (translDiff A L.L (ρk ≫ X))) (y : Over.mk pF ⟶ A) (hy : y ^ n = 1) :
    CubWeil c n (ρF ≫ X) y 1 := by
  have := hA.proper
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have w : y.left ≫ A.hom = spMap (algebraMap O F) ≫ p := (Over.w y).trans ((Over.w ρF).symm.trans (by rw [hF]; rfl))
  obtain ⟨l, hl₁, hl₂⟩ := (hE { R := O, K := F, commSq := ⟨w⟩, .. }).exists_lift
  let Y : Over.mk p ⟶ A := Over.homMk l hl₂
  have hYy : ρF ≫ Y = y := Over.OverMorphism.ext ((congrArg (· ≫ l) hF).trans hl₁)
  have hY : Y ^ n = 1 := by
    refine over_points_ext_of_injective S A O F _ (IsFractionRing.injective O F) p _ _ ?_
    have e : ρF ≫ Y ^ n = ρF ≫ 1 := by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one]
    have e' : ρF.left ≫ (Y ^ n).left = ρF.left ≫ (1 : Over.mk p ⟶ A).left := congrArg (fun q => q.left) e
    rw [hF] at e'
    exact e'
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hX hY
  have h₁ := hζ.comp ρk
  have h₂ := KerPair.cubWeil_of_gen hG S A hA L c n _ _ _ h₁.1 h₁.2.1 ht
  have h₃ := h₁.unique h₂
  rw [hk] at h₃
  have h₄ : ζ = 1 := unit_eq_one_of_localHom g hn hζ.pow_eq_one h₃
  have h₅ := hζ.comp ρF
  rwa [h₄, map_one, hYy] at h₅

theorem nondeg_of_isGrpPullback {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {B : Over S} [GrpObj B] [IsCommMonObj B]
    {L' : LB A.left} {L : LB B.left} (hL' : L'.IsLB) (hL : L.IsLB) {f : S' ⟶ S} {φ : A.left ⟶ B.left}
    (hp : IsGrpPullback A B f φ) (hi : LBIso L' (L.pull φ)) (T : Over S') (n : ℕ)
    (H : ∀ u : T ⟶ A, u ^ n = 1 → (∀ z : T ⟶ A, z ^ n = 1 → WeilIs A L' n u z 1) → u = 1)
    (x : Over.mk (T.hom ≫ f) ⟶ B) (hx : x ^ n = 1)
    (h : ∀ y : Over.mk (T.hom ≫ f) ⟶ B, y ^ n = 1 → WeilIs B L n x y 1) : x = 1 := by
  let β := pushHom hp T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  let u : T ⟶ A := Over.homMk (hp.1.lift x.left T.hom (Over.w x)) (hp.1.lift_snd _ _ _)
  have hu : β u = x := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  have hun : u ^ n = 1 := inj (by rw [map_pow, hu, map_one]; exact hx)
  have : u = 1 := H u hun fun z hz =>
    (weilIs_grpPullback_of_comm _ _ B A f φ L L' hL hL' hp hi T n u z x (β z) 1
      (congrArg (fun q => q.left) hu.symm) rfl).2 (h _ (by rw [← map_pow, hz, map_one]))
  rw [← hu, this, map_one]

theorem eq_one_of_cubWeil (hL : Laws) {S S' : Scheme.{0}} (P : PolAV S') {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : RigLB B} (c : CubicalStr B L) {f : S' ⟶ S} {φ : P.A.left ⟶ B.left}
    (hp : IsGrpPullback P.A B f φ) (hi : LBIso P.L (L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F]
    (t : Sp F ⟶ S') {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk (t ≫ f) ⟶ B) (hx : x ^ n = 1)
    (h : ∀ y : Over.mk (t ≫ f) ⟶ B, y ^ n = 1 → CubWeil c n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hmul, tw, htw⟩ := hL.polBaseChange S' _ t P
  have hp' : IsGrpPullback P'.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  have := P.isAb.comm
  have H := nondeg_of_isGrpPullback P'.isLB P.isLB hp' (LBIso.symm ⟨tw, htw⟩) (baseOver _) n
    (hL.weilNondeg F P' n hn)
  have e : (baseOver (Sp F)).hom ≫ t = t := Category.id_comp t
  rw [e] at H
  exact nondeg_of_isGrpPullback P.isLB L.isLB hp hi (Over.mk t) n H x hx fun y hy =>
    (cubWeil_iff_weilIs hL.globalFns hB hx hy 1).1 (h y hy)

theorem torsion_eq_one_of_triv : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ n : ℕ, (n : Ω) ≠ 0 → ∀ x : Over.mk (spMap f) ⟶ B, x ^ n = 1 → GlobalTheory.AbLaw.Triv (translDiff B M.L.L x) → x = 1 := by
  intro hL _ V K _ _ _ _ _ _ P B _ _ M φ hB hp hi _ Ω _ _ f hf n hn x hx ht
  have := hB.smooth
  have := hB.proper
  have hnV : IsUnit (n : V) := isUnit_of_map_unit f _ (by rw [map_natCast]; exact hn.isUnit)
  obtain ⟨W, _, _, _, _, _, f', _, inj, _, _, hf', lifts⟩ := GlobalTheory.exists_finite_extension_torsion_lift hL.unramExt V B n
    hnV Ω f hf {x} (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hx)
  obtain ⟨X, hX, hXx⟩ := lifts x (Finset.mem_singleton_self x)
  obtain ⟨ψ, hψ, eψ⟩ := exists_embedding V K W inj
  obtain ⟨O, j, k, _, a, g, hj, _, e⟩ := exists_valuationSubring ψ f'
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C),
      spMap (v.comp u) = spMap v ≫ spMap u := fun u v => by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let TW : Over (Sp V) := Over.mk (spMap (algebraMap V W))
  let TO : Over (Sp V) := Over.mk (spMap j ≫ spMap (algebraMap V W))
  let σ : TO ⟶ TW := Over.homMk (spMap j) rfl
  let ρk : Over.mk (spMap a ≫ spMap f) ⟶ TO := Over.homMk (spMap g) (by
    show spMap g ≫ spMap j ≫ spMap (algebraMap V W) = spMap a ≫ spMap f
    rw [← sp, ← sp, ← sp, ← RingHom.comp_assoc, ← e, RingHom.comp_assoc, hf'])
  let ρF : Over.mk (spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap (algebraMap V K)) ⟶ TO :=
    Over.homMk (spMap (algebraMap O (AlgebraicClosure K))) (by
      show spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j ≫ spMap (algebraMap V W) =
        spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap (algebraMap V K)
      rw [← sp, ← sp, ← sp, ← RingHom.comp_assoc, hj, eψ])
  let τ : Over.mk (spMap a ≫ spMap f) ⟶ Over.mk (spMap f) := Over.homMk (spMap a) rfl
  have hτ : τ ≫ x = ρk ≫ σ ≫ X := Over.OverMorphism.ext (by
    show spMap a ≫ x.left = spMap g ≫ spMap j ≫ X.left
    rw [← hXx, ← Category.assoc, ← Category.assoc, ← sp, ← sp, e])
  have hσ : (σ ≫ X) ^ n = 1 := by rw [← MonObj.comp_pow, hX, MonObj.comp_one]
  have hnO : IsUnit (n : O) := by simpa using hnV.map (j.comp (algebraMap V W))
  have key : ρF ≫ σ ≫ X = 1 := eq_one_of_cubWeil hL P hB M.c hp hi _
    (by simpa using (hnO.map (algebraMap O (AlgebraicClosure K))).ne_zero) _
    (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one])
    (cubWeil_generic hL.globalFns hB M.c g hnO (σ ≫ X) hσ ρk rfl ρF rfl (hτ ▸ triv_comp x τ ht))
  have hX1 : X = 1 := by
    refine over_points_ext_of_injective _ B W _ ψ hψ _ _ _ ?_
    have e₁ : (ρF ≫ σ) ≫ X = (ρF ≫ σ) ≫ 1 := by rw [Category.assoc, key, MonObj.comp_one]
    have e₂ : (spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j) ≫ X.left =
        (spMap (algebraMap O (AlgebraicClosure K)) ≫ spMap j) ≫ (1 : TW ⟶ B).left := congrArg (fun q => q.left) e₁
    rw [← sp, hj] at e₂
    exact e₂
  let ρ : Over.mk (spMap f) ⟶ TW := Over.homMk (spMap f') (by
    show spMap f' ≫ spMap (algebraMap V W) = spMap f
    rw [← sp, hf'])
  have : x = ρ ≫ X := Over.OverMorphism.ext hXx.symm
  rw [this, hX1]
  exact MonObj.comp_one _

end GlobalTheory.PrincipalModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqOneOfTranslDiffTrivialModelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_eq_one_of_translDiff_trivial_model : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ n : ℕ, (n : Ω) ≠ 0 → ∀ x : Over.mk (spMap f) ⟶ B, x ^ n = 1 → GlobalTheory.AbLaw.Triv (translDiff B M.L.L x) → x = 1 := by
  first | exact @GlobalTheory.PrincipalModel.torsion_eq_one_of_triv | exact GlobalTheory.PrincipalModel.torsion_eq_one_of_triv | (intros; apply GlobalTheory.PrincipalModel.torsion_eq_one_of_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatio
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.SpecialAmple

theorem exists_sec_ne_zero {X X' : Scheme.{0}} (π : X' ⟶ X) [IsIso π] {M : LB X} {M' : LB X'} (hM : M.IsLB)
    (hM' : M'.IsLB) (h : LBIso M' (M.pull π)) (hs : ∃ s : LB.Sec M, ∃ j, s.f j ≠ 0) :
    ∃ s' : LB.Sec M', ∃ j, s'.f j ≠ 0 := by
  obtain ⟨s, j, hj⟩ := hs
  obtain ⟨w, hw⟩ := h
  obtain ⟨⟨s', hs', -⟩, -⟩ := SecPullIso.section_pull X X' π M M' w hM hM' hw s
  refine ⟨s', ?_⟩
  by_contra h
  push Not at h
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨k, hz⟩ := exists_chart hM' z
  have e := hs' z j k hx hz
  have e₀ : gs (𝟙 X') z (M'.U k) (s'.f k) = 0 :=
    (congrArg (gs (𝟙 X') z _) (h k)).trans (AmpleCrit.gs_zero' _ z _ hz)
  replace e := e.trans ((congrArg _ e₀).trans (mul_zero _))
  rw [gs_stalkMap π z _ hx] at e
  rw [AmpleCrit.gs_zero' (𝟙 X) (π z) _ hx]
  exact AmpleCrit.injective_stalkMap π z (e.trans (map_zero _).symm)

theorem exists_iso {X Y S T T' : Scheme.{0}} {φ : Y ⟶ X} {a : Y ⟶ T} {b : X ⟶ S} {f : T ⟶ S}
    (h : IsPullback φ a b f) (e : T' ⟶ T) [IsIso e] (g : T' ⟶ S) (he : e ≫ f = g) :
    ∃ u : pullback b g ⟶ Y, IsIso u ∧ u ≫ φ = pullback.fst b g := by
  subst he
  let u : pullback b (e ≫ f) ⟶ Y := h.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e)
    (by rw [Category.assoc]; exact pullback.condition)
  have hu : u ≫ φ = pullback.fst _ _ := h.lift_fst _ _ _
  have H : IsPullback u (pullback.snd b (e ≫ f)) a e :=
    IsPullback.of_right (by rw [hu]; exact IsPullback.of_hasPullback _ _) (h.lift_snd _ _ _) h
  exact ⟨u, H.isIso_fst_of_isIso, hu⟩

theorem exists_sec_pull {X Y Y' : Scheme.{0}} {N : LB X} (hN : N.IsLB) {a : Y ⟶ X} {b : Y' ⟶ X} (u : Y' ⟶ Y)
    [IsIso u] (hu : u ≫ a = b) (hs : ∃ s : LB.Sec (N.pull a), ∃ j, s.f j ≠ 0) :
    ∃ s : LB.Sec (N.pull b), ∃ j, s.f j ≠ 0 :=
  by
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  exact exists_sec_ne_zero u (pull_isLB hN a) (pull_isLB hN b)
    (LBIso.chartPull (chartPullSame N _ _ _ u fun _ => hu.symm) (Geo.Tor.chartPullPull _ u u rfl)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB hN a)⟩) hs

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) :
    LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') : IsIso (spMap e.toRingHom) :=
  inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))

theorem exists_sec_pow {K : Type} [Field K] (P : PolAV (Sp K)) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ s : LB.Sec (AbLaw.pw P.L d), ∃ j, s.f j ≠ 0 := by
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ P.A P.L P.isLB).1 P.ample
  have hy : eSec P.A (IsLocalRing.closedPoint K) ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨d, hd, a i, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem exists_prime (Ω : Type) [Field Ω] (m : ℕ) (hm : 0 < m) : ∃ n : ℕ, n.Prime ∧ (n : Ω) ≠ 0 ∧ ¬ n ∣ m := by
  obtain ⟨n, hn, hp⟩ := Nat.exists_infinite_primes (m + ringChar Ω + 1)
  refine ⟨n, hp, fun h => ?_, fun h => ?_⟩
  · rcases (Nat.dvd_prime hp).1 ((ringChar.spec Ω n).1 h) with e | e
    · exact CharP.ringChar_ne_one e
    · omega
  · have := Nat.le_of_dvd hm h
    omega

theorem relAmple_special_fibre : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple ((Over.pullback (spMap (IsLocalRing.residue V))).obj B) (M.L.L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue V)))) := by
  intro hL hL2 V K _ _ _ _ _ _ P B _ _ M φ hB hφ hiso hV
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  obtain ⟨d, hd, h₀⟩ := exists_sec_pow P
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw : ∀ {X : Scheme.{0}} {H : LB X}, H.IsLB → (t : ℤ) → (AbLaw.pw H t).IsLB := by
    intro X H hH t
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  have hN := isLB_pw M.L.isLB d

  have h₁ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull φ), ∃ j, s.f j ≠ 0 := by
    refine exists_sec_ne_zero (𝟙 _) (isLB_pw P.isLB d) (pull_isLB hN φ) ?_ h₀
    refine LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) ?_
    rw [AmpleCrit.pull_pw_eq]
    exact lbIso_pw hiso.symm d
  have h₂ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull (pullback.fst B.hom (jK V))), ∃ j, s.f j ≠ 0 := by
    let e : K ≃+* FractionRing V := (FractionRing.algEquiv V K).symm.toRingEquiv
    have := isIso_spMap e
    obtain ⟨u, _, hu⟩ := exists_iso hφ.1 (spMap e.toRingHom) (jK V) (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext v
      exact (FractionRing.algEquiv V K).symm.commutes v)
    exact exists_sec_pull hN u hu h₁

  have h₃ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V B _ hN h₂
  let r := spMap (IsLocalRing.residue V)
  have h₄ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull (pullback.fst B.hom r)), ∃ j, s.f j ≠ 0 := by
    let e : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) ≃+* IsLocalRing.ResidueField V :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    have := isIso_spMap e
    obtain ⟨u, _, hu⟩ := exists_iso
      (IsPullback.of_hasPullback B.hom (thick V (IsLocalRing.maximalIdeal V) 0)) (spMap e.toRingHom) r (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2)
    exact exists_sec_pull hN u hu h₃
  rw [AmpleCrit.pull_pw_eq] at h₄
  obtain ⟨s, hs⟩ := h₄

  let k := IsLocalRing.ResidueField V
  let B' : Over (Sp k) := (Over.pullback r).obj B
  have h : IsGrpPullback B' B r (pullback.fst B.hom r) := isGrpPullback_pullback B r
  have : IsCommMonObj B' := PolPull.isCommMonObj_of_isGrpPullback h
  have hB' : IsAbelianScheme B' := {
    comm := inferInstance
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hB.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hB.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hB.geomConnected }
  obtain ⟨hL', hr, ⟨c', -⟩, -⟩ := CubePf.cubePull _ _ B B' (cubeMapOf h) M.L M.c
  let Ω := AlgebraicClosure k
  obtain ⟨n, hn, hnΩ, hnd⟩ := exists_prime Ω (2 * d) (by omega)
  refine AmpleCrit.relAmple_of_effective (GlobalTheory.T.card_torsion_points_abelianVariety hL.globalFns hL.rigidity) k (Field.toIsField k) B' hB'
    ((cubeMapOf h).rigLB M.L hL' hr) c' d s hd hs Ω (spMap (algebraMap k Ω)) n hn hnΩ hnd fun x hxn htr => ?_
  let f : V →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue V)
  have hf : IsLocalHom f := RingHom.isLocalHom_comp _ _
  have key : ∀ p' : Sp Ω ⟶ Sp V, p' = spMap f →
      ∀ y : Over.mk p' ⟶ B, y ^ n = 1 → AbLaw.Triv (translDiff B M.L.L y) → y = 1 := by
    rintro _ rfl
    exact GlobalTheory.T.torsion_eq_one_of_translDiff_trivial_model hL hL2 V K P B M φ hB hφ hiso hV Ω f hf n hnΩ
  have e : pushHom h _ x = 1 := key _ (Spec.map_comp _ _).symm (pushHom h _ x)
    (by rw [← map_pow, hxn, map_one]) (AmpleCrit.triv_translDiff_push h M.L.isLB x htr)
  have e' := e.trans (map_one (pushHom h (Over.mk (spMap (algebraMap k Ω))))).symm
  exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))

end GlobalTheory.SpecialAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatioStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple ((Over.pullback (spMap (IsLocalRing.residue V))).obj B) (M.L.L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue V)))) := by
  first | exact @GlobalTheory.SpecialAmple.relAmple_special_fibre | exact GlobalTheory.SpecialAmple.relAmple_special_fibre | (intros; apply GlobalTheory.SpecialAmple.relAmple_special_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleExtendedPrincipalPolarisationDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ExtAmple

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem relAmple_pullback_of_fac {S S₀ T : Scheme.{0}} [IsAffine S₀] {B : Over S} {A : Over S₀} {L : LB B.left}
    {L₀ : LB A.left} (hL : L.IsLB) (hL₀ : L₀.IsLB) {g : S₀ ⟶ S} {φ : A.left ⟶ B.left}
    (h : IsPullback φ A.hom B.hom g) (e : LBIso L₀ (L.pull φ)) (hA : RelAmple A L₀) (y : T ⟶ S₀) :
    RelAmple ((Over.pullback (y ≫ g)).obj B) (L.pull (pullback.fst B.hom (y ≫ g))) := by
  let ψ : pullback B.hom (y ≫ g) ⟶ A.left :=
    h.lift (pullback.fst B.hom (y ≫ g)) (pullback.snd B.hom (y ≫ g) ≫ y) (by rw [Category.assoc]; exact pullback.condition)
  have hψ : ψ ≫ φ = pullback.fst B.hom (y ≫ g) := h.lift_fst _ _ _
  have H : IsPullback ψ (pullback.snd B.hom (y ≫ g)) A.hom y := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hψ]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨w, hw⟩ : LBIso (L.pull (pullback.fst B.hom (y ≫ g))) (L₀.pull ψ) :=
    LBIso.chartPull
      (chartPullSame L (fun _ : PUnit => pullback.fst B.hom (y ≫ g)) (fun _ => φ) (fun _ => 1) ψ fun _ => hψ.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L₀ _ _ rfl) (LBIso.symm e)
  exact relAmple_pull (A' := (Over.pullback (y ≫ g)).obj B) H hL₀ (pull_isLB hL _)
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA

theorem fac_or_fac (V K k : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field k] (f : V →+* k) :
    (∃ g : K →+* k, f = g.comp (algebraMap V K)) ∨
      ∃ g : IsLocalRing.ResidueField V →+* k, f = g.comp (IsLocalRing.residue V) := by
  by_cases hf : RingHom.ker f = ⊥
  · have hi : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).2 hf
    exact Or.inl ⟨IsFractionRing.lift hi, RingHom.ext fun x => (IsFractionRing.lift_algebraMap hi x).symm⟩
  · have hm : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hf
    have he := IsLocalRing.eq_maximalIdeal hm
    exact Or.inr ⟨Ideal.Quotient.lift _ f (fun a ha => by rw [← he] at ha; exact ha), RingHom.ext fun x => rfl⟩

theorem relAmple_extension : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  intro h₁ h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ e hc
  refine GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres h₁ h₂ V hc B hB M fun k _ x => ?_
  obtain ⟨f, rfl⟩ := Spec.map_surjective x
  rcases fac_or_fac V K k f.hom with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hx : Spec.map f = spMap g ≫ spMap (algebraMap V K) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac M.L.isLB P.isLB hφ.1 e P.ample _
  · have hx : Spec.map f = spMap g ≫ spMap (IsLocalRing.residue V) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac (A := (Over.pullback (spMap (IsLocalRing.residue V))).obj B) M.L.isLB
      (pull_isLB M.L.isLB _) (IsPullback.of_hasPullback _ _) (lbIso_self (pull_isLB M.L.isLB _))
      (GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation h₁ h₂ V K P B M φ hB hφ e hc) _

end GlobalTheory.ExtAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleExtendedPrincipalPolarisationDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_extended_principalPolarisation_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  first | exact @GlobalTheory.ExtAmple.relAmple_extension | exact GlobalTheory.ExtAmple.relAmple_extension | (intros; apply GlobalTheory.ExtAmple.relAmple_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PolExtendDVR

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB Y} {M : LB X} {φ : Y ⟶ X} (h : LBIso L (M.pull φ)) (g : Z ⟶ Y) :
    LBIso (L.pull g) (M.pull (g ≫ φ)) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L g g rfl)
    (chartPullSame M (fun _ : PUnit => g ≫ φ) (fun _ => φ) (fun _ => 1) g fun _ => rfl) h

theorem exists_baseChange (hB : PolBaseChangeSt) {V K V' K' : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    (a : V →+* V') (ha : Function.Injective a)
    (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left)
    (hφ : IsGrpPullback P.A B (spMap (algebraMap V K)) φ) (hL : LBIso P.L (M.L.L.pull φ)) :
    ∃ (P' : PolAV (Sp K')) (M' : GlobalTheory.UU.CP ((Over.pullback (spMap a)).obj B))
      (φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left),
      IsGrpPullback P'.A ((Over.pullback (spMap a)).obj B) (spMap (algebraMap V' K')) φ' ∧
        LBIso P'.L (M'.L.L.pull φ') ∧ LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := by
  have hi : Function.Injective ((algebraMap V' K').comp a) := (IsFractionRing.injective V' K').comp ha
  let b : K →+* K' := IsFractionRing.lift hi
  have hb : b.comp (algebraMap V K) = (algebraMap V' K').comp a :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hi x
  have hs : spMap b ≫ spMap (algebraMap V K) = spMap (algebraMap V' K') ≫ spMap a := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hB _ _ (spMap b) P
  have gp : IsGrpPullback P'.A P.A (spMap b) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  have hπ := isGrpPullback_pullback B (spMap a)
  have gc := (gp.comp hφ).congr hs rfl
  obtain ⟨M', w, hw⟩ := GlobalTheory.UU.exists_pull M (GlobalTheory.UU.toBase_mul_pullback B (spMap a))
  have hM : LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := ⟨w, hw.gen⟩
  let φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left :=
    pullback.lift (g ≫ φ) (P'.A.hom ≫ spMap (algebraMap V' K')) (gc.1.w.trans (Category.assoc _ _ _).symm)
  have e : φ' ≫ pullback.fst B.hom (spMap a) = g ≫ φ := pullback.lift_fst _ _ _
  refine ⟨P', M', φ', hπ.cancel (gc.congr rfl e.symm) (pullback.lift_snd _ _ _), ?_, hM⟩
  have i₁ : LBIso P'.L (M.L.L.pull (g ≫ φ)) :=
    LBIso.trans P'.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull M.L.isLB _) (LBIso.symm ⟨t, ht⟩) (lbIso_pull_comp hL g)
  have i₂ := lbIso_pull_comp hM φ'
  rw [e] at i₂
  exact LBIso.trans P'.isLB (LB.isLB_pull M.L.isLB _) (LB.isLB_pull M'.L.isLB _) i₁ i₂.symm

end GlobalTheory.PolExtendDVR

namespace GlobalTheory


open PolExtendDVR IsLocalRing in
theorem polarisation_extends_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L ∧ KTriv B M.L.L := by
  intro h h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ hL
  let V' := AdicCompletion (maximalIdeal V) V
  obtain ⟨P', M', φ', hφ', hL', hM⟩ := exists_baseChange (K' := FractionRing V') h.polBaseChange (algebraMap V V')
    (algebraMap_adicCompletion_injective_of_dvr V) P B M φ hφ hL
  have hπ := isGrpPullback_pullback B (spMap (algebraMap V V'))
  have hB' := (pol_pull _ _ B _ _ _ M.L.L M'.L.L M.L.isLB M'.L.isLB hB hπ hM).1
  have hA' := GlobalTheory.T.relAmple_extended_principalPolarisation_dvr h h₂ V' (FractionRing V') P' _ M' φ' hB' hφ' hL' inferInstance
  have : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hA : RelAmple B M.L.L :=
    AmpleDescent.relAmple_of_faithfullyFlat V V' B _ _ M.L.L M'.L.L hB hπ M.L.isLB M'.L.isLB hM hA'
  exact ⟨hA, KTrivSpread.kTriv_of_generic_fibre h V K P B M φ hB hφ hL hA⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReductionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_extends_over_dvr_goodReduction : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L ∧ KTriv B M.L.L := by
  first | exact @GlobalTheory.polarisation_extends_dvr | exact GlobalTheory.polarisation_extends_dvr | (intros; apply GlobalTheory.polarisation_extends_dvr <;> assumption)
end

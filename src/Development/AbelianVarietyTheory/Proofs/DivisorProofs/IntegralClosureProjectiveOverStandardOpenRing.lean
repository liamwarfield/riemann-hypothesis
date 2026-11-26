module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslates
public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRing
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory


set_option synthInstance.maxHeartbeats 200000 in
theorem integralClosure_projective_rA : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F),
    IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  intro k _ _ F K _ _ _ _ _ _ d x h i
  obtain ⟨hfin, -, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x h {i} (Finset.singleton_nonempty i)
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h.pd i
  haveI : IsRegularRing (rA k x {i}) := IsRegularRing.of_ringEquiv e.toRingEquiv
  haveI : IsNoetherianRing (rA k x {i}) := inferInstance
  haveI : IsDomain (rA k x {i}) := inferInstance
  haveI : IsIntegrallyClosed (rA k x {i}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {i}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI : IsRegularRing (rB k K x {i}) := GlobalTheory.isRegularRing_of_smooth k _
  haveI hB : IsRegularRing (integralClosure (rA k x {i}) K) := ‹IsRegularRing (rB k K x {i})›
  haveI : IsNoetherianRing (integralClosure (rA k x {i}) K) := inferInstance
  haveI : IsDomain (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Algebra.IsIntegral (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : FaithfulSMul (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun y : integralClosure (rA k x {i}) K => (y : K)) hab
    exact Subtype.ext ((algebraMap F K).injective this)
  haveI : Algebra.HasGoingDown (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Module.Flat (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    refine GlobalTheory.flat_of_isRegularRing_of_isRegularRing fun q hq => ?_
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under (rA k x {i})) q]
    · exact le_self_add
    all_goals first | assumption | infer_instance
  haveI : Module.FinitePresentation (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_projective_over_standardOpenRing : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  first | (exact @GlobalTheory.integralClosure_projective_rA) | (exact GlobalTheory.integralClosure_projective_rA) | (intros; apply GlobalTheory.integralClosure_projective_rA  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem traceZeroIndex_of_intIndex : IntIndex → TraceZeroIndex := by
  intro hI L _ _ ϖ σ q hU
  have hq := hI L ϖ σ q hU
  obtain ⟨hσσ, hv, hϖ, -, ⟨x, hx, hδ⟩, -, -⟩ := hU
  have hσO : ∀ y ∈ intL L, σ y ∈ intL L := fun y hy => by
    show Valued.v (σ y) ≤ 1
    rw [hv]; exact hy
  have hδ0 : σ x - x ≠ 0 := fun h => by rw [h, map_zero] at hδ; exact zero_ne_one hδ
  have hδ1 : x - σ x ≠ 0 := fun h => hδ0 (by linear_combination -h)
  have hδi : (σ x - x)⁻¹ ∈ intL L := by
    show Valued.v (σ x - x)⁻¹ ≤ 1
    rw [map_inv₀, hδ, inv_one]
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y = -y := fun y => by
    rw [hT, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, ← add_eq_zero_iff_eq_neg]
    rfl
  have hw : ∀ y ∈ intL L, σ y - y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (hσO y hy) hy, by rw [map_sub, hσσ]; ring⟩
  have hu : ∀ y ∈ intL L, σ x * y - x * σ y ∈ T := fun y hy =>
    (memT _).2 ⟨sub_mem (mul_mem (hσO x hx) hy) (mul_mem hx (hσO y hy)), by
      rw [map_sub, map_mul, map_mul, hσσ, hσσ]; ring⟩
  let f : T × T →+ (intL L).toAddSubgroup :=
    { toFun := fun p => ⟨(σ x - x)⁻¹ * (p.1.1 + x * p.2.1),
        (intL L).mul_mem hδi ((intL L).add_mem ((memT _).1 p.1.2).1 ((intL L).mul_mem hx ((memT _).1 p.2.2).1))⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp; ring) }
  have hf : ∀ p, (f p : L) = (σ x - x)⁻¹ * (p.1.1 + x * p.2.1) := fun _ => rfl
  have hsurj : Function.Surjective f := fun y =>
    ⟨(⟨_, hu y.1 y.2⟩, ⟨_, hw y.1 y.2⟩), Subtype.ext (by rw [hf]; field_simp; ring)⟩
  have hc : (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup).comap f =
      ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T).prod ((T.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf T) := by
    ext ⟨u, w⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map,
      hf, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨y, hy, e⟩
      have e1 : (σ x - x) * (ϖ * y) = u.1 + x * w.1 := by rw [e]; field_simp
      have e2 := congrArg σ e1
      rw [map_mul, map_sub, hσσ, map_mul, hϖ, map_add (f := _), map_mul, ((memT _).1 u.2).2, ((memT _).1 w.2).2] at e2
      have e3 : ϖ * (σ y - y) = w.1 := mul_left_cancel₀ hδ0 (by linear_combination -e1 - e2)
      exact ⟨⟨_, hu y hy, by linear_combination e1 - x * e3⟩, _, hw y hy, e3⟩
    · rintro ⟨⟨a, ha, e1⟩, b, hb, e2⟩
      refine ⟨_, (f (⟨a, ha⟩, ⟨b, hb⟩)).2, ?_⟩
      rw [hf, ← e1, ← e2]; ring
  have h2 := AddSubgroup.index_comap_of_surjective
    (((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf (intL L).toAddSubgroup) hsurj
  rw [hc, AddSubgroup.index_prod, ← pow_two] at h2
  exact Nat.pow_left_injective two_ne_zero (h2.trans hq)

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSqStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex := by
  first | exact @GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | exact GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | (intros; apply GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductions
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isMonHom_of_fst_mul_snd {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by
  have hm : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ g = (x ≫ g) * (y ≫ g) := fun T x y => by
    have := congrArg (lift x y ≫ ·) h
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using this
  refine ⟨?_, ?_⟩
  · have h1 := hm (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S) ⟶ A) ≫ g = 1 := left_eq_mul.1 h1
    simpa [Hom.one_def] using h2
  · have e : (fst A A * snd A A) = μ[A] := by simp [Hom.mul_def]
    rw [e] at h
    rw [h, Hom.mul_def]
    congr 1

theorem mul_comp_of_isGrpPullback {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by
  let x' : T ⟶ Y := Over.homMk (ha.1.lift x.left T.hom (Over.w x)) (ha.1.lift_snd _ _ _)
  let y' : T ⟶ Y := Over.homMk (ha.1.lift y.left T.hom (Over.w y)) (ha.1.lift_snd _ _ _)
  have hx : x.left = x'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have hy : y.left = y'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have h1 := ha.2 T x' y' x y hx hy
  have h2 := hb.2 T (x' ≫ f) (y' ≫ f) (x ≫ g) (y ≫ g)
    (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hg])
    (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hg])
  ext
  rw [h2, Over.comp_left, h1, ← MonObj.mul_comp, Over.comp_left, Category.assoc, Category.assoc, hg]

theorem grpHom_algebraise : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  intro H R _ _ I hI A B _ _ hA hB Y Z _ _ β δ a b ha hβ hb hδ f hf hc
  obtain ⟨g, hg, hu⟩ := H R I hI A B hA inferInstance inferInstance inferInstance Y β a
    (fun e => (ha e).1) hβ (fun e => (f e).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← Category.assoc, hc, Category.assoc, hδ])
  refine ⟨g, isMonHom_of_fst_mul_snd g ?_, hg, hu⟩
  haveI : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  refine H.hom_ext hI fun e => ?_
  haveI := hf e
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (pullback.snd (A ⊗ A).hom (thick R I e))
  let P : Over.mk (T.hom ≫ thick R I e) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst (A ⊗ A).hom (thick R I e)) pullback.condition
  have key := mul_comp_of_isGrpPullback (ha e) (hb e) (f e) g (hg e) T (P ≫ fst A A) (P ≫ snd A A)
  have key' : P ≫ (fst A A * snd A A) ≫ g = P ≫ ((fst A A ≫ g) * (snd A A ≫ g)) := by
    rw [← Category.assoc, MonObj.comp_mul, key, MonObj.comp_mul, Category.assoc, Category.assoc]
  exact congrArg (·.left) key'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductionsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpHom_algebraisation_of_reductions : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  first | exact @GlobalTheory.grpHom_algebraise | exact GlobalTheory.grpHom_algebraise | (intros; apply GlobalTheory.grpHom_algebraise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem blockDiagPart_mul {L : Type} [Field L] {n : ℕ} (β : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L)
    (hA : A.BlockTriangular β) (hB : B.BlockTriangular β) (hAB : A * B = 1) :
    (Matrix.of fun a b => if β a = β b then A a b else 0) *
      (Matrix.of fun a b => if β a = β b then B a b else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h : β i = β j
  · rw [← hAB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
    · rw [hA h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hB (h ▸ h1 : β j < β l)]; simp
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e]))]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [if_neg (hl ▸ h : ¬ β l = β j), mul_zero]
    · rw [if_neg hl, zero_mul]

theorem leviPart : LeviPart := by
  intro L _ _ σ n β hβ g hg
  have hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev := fun a b =>
    ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩
  have h0 : (mat g⁻¹).BlockTriangular β := by
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h1 := blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM
  have h2 : antiJ L n * (cT σ M * antiJ L n) =
      Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0 := by
    ext a b
    rw [antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]
    by_cases h : β a = β b
    · rw [if_pos h, if_pos ((hβ' _ _).1 h.symm)]
    · rw [if_neg h, if_neg (fun e => h ((hβ' _ _).2 e).symm), map_zero]
  have h3 : cT σ M * antiJ L n * M = antiJ L n := by
    rw [← h2] at h1
    calc cT σ M * antiJ L n * M
        = antiJ L n * (antiJ L n * (cT σ M * antiJ L n) * M) := by
          rw [← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n),
            GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = antiJ L n := by rw [h1, Matrix.mul_one]
  obtain ⟨m, hm⟩ := exists_mat M h3
  have hmL : m ∈ leviU σ β := fun i j h => by rw [hm, hM, Matrix.of_apply, if_neg h]
  refine ⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, if_pos h], fun i j h => ?_⟩
  rw [← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : β i = β l
  · rw [hm, hM, Matrix.of_apply]
    split_ifs with h4
    · rfl
    · rw [hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]
  · rw [(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitaryStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_block_triangular_levi_part_unitary : GlobalTheory.SatakeWeyl.LeviPart := by
  first | exact @GlobalTheory.SatakeWeyl.leviPart | exact GlobalTheory.SatakeWeyl.leviPart | (intros; apply GlobalTheory.SatakeWeyl.leviPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CyclotomicGlobalSections

theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A)) :
    ∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  have hqk : (q : IsLocalRing.ResidueField A) ≠ 0 := by
    have := hq.map (IsLocalRing.residue A)
    simpa using this.ne_zero
  have hsepk : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).Separable :=
    (Polynomial.separable_X_pow_sub_C 1 hqk one_ne_zero).of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ hdeg hsepk
  obtain ⟨b0, rfl⟩ := IsLocalRing.residue_surjective a0
  have hred : ∀ p : Polynomial A, IsLocalRing.residue A (p.eval b0) =
      (p.map (IsLocalRing.residue A)).eval (IsLocalRing.residue A b0) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have h1 : (Polynomial.cyclotomic q A).eval b0 ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hred, Polynomial.map_cyclotomic]
    all_goals exact ha0
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q A)).eval b0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hred, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]
    have := hsepk.aeval_derivative_ne_zero (x := IsLocalRing.residue A b0) (by simpa [Polynomial.aeval_def] using ha0)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q A)
    (Polynomial.cyclotomic.monic q A) b0 h1 h2
  refine ⟨a, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha

end GlobalTheory.EtC.CyclotomicGlobalSections


open GlobalTheory.EtC.ConnectedGlobalSections in
theorem GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  intro q _ A _ hA hq j
  obtain ⟨ζ0, hζ0⟩ := GlobalTheory.EtC.CyclotomicGlobalSections.exists_cyclotomic_root q A hA hq
  obtain ⟨hH, -⟩ := hA
  haveI := hH
  let e : Sec (tw q j) (Spec (CommRingCat.of A)) ≃+ Ht q (sp A) 0 j :=
    AddEquiv.ofBijective (AddMonoidHom.mk' (secClass (tw q j))
      (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q j) _).2.2.1)
      (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q j) _).2.1
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1 := fun x hx => by
    have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
    · exact Or.inr (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)).symm
    · exact Or.inl ((hu.mul_left_eq_zero).1 h0)
  let φ : ZMod q →+ Sec (tw q j) (Spec (CommRingCat.of A)) :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • twGen j ζ
      map_zero' := zero_smul _ _
      map_add' := fun c d => add_smul (ULift.up c : ULift.{1} (ZMod q)) (ULift.up d) (twGen j ζ) }
  have hφ : ∀ c : ZMod q, φ c = c.val • twGen j ζ := fun c => by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]; rfl
  have hbij : Function.Bijective φ := by
    constructor
    · intro c d h
      rw [hφ, hφ] at h
      exact scalar_eq ζ c d h
    · intro y
      obtain ⟨n, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidem) ζ y
      exact ⟨(n : ZMod q), by rw [hφ, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]⟩
  exact ⟨((AddEquiv.ofBijective φ hbij).trans e).symm⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquivStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (exact GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (intros; apply GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.SmallEtaleCech

instance : PreservesLimitsOfSize.{0, 0} (disc : PSh ⥤ Spc) :=
  inferInstanceAs (PreservesLimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))

instance : PreservesLimitsOfSize.{0, 0} sch := inferInstanceAs (PreservesLimitsOfSize.{0, 0} (yoneda ⋙ disc))

noncomputable def bcIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) :
    bc p ≅ Over.post sch ⋙ Over.pullback p ⋙ Over.forget E :=
  NatIso.ofComponents (fun U => pullbackSymmetry p (sch.map U.hom)) (fun {U V} g => by
    change pullback.map p (sch.map U.hom) p (sch.map V.hom) (𝟙 _) (sch.map g.left) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← sch.map_comp, Over.w g]) ≫ (pullbackSymmetry p (sch.map V.hom)).hom =
      (pullbackSymmetry p (sch.map U.hom)).hom ≫ pullback.lift (f := sch.map V.hom) (g := p)
        (pullback.fst (sch.map U.hom) p ≫ sch.map g.left) (pullback.snd (sch.map U.hom) p)
        (by rw [Category.assoc, ← sch.map_comp, Over.w g, pullback.condition])
    apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd])

theorem bc_preserves {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (J : Type) [SmallCategory J] [IsConnected J]
    [FinCategory J] : PreservesLimitsOfShape J (bc p) := by
  have : PreservesLimitsOfShape J (Over.post sch ⋙ Over.pullback p ⋙ Over.forget E : Over S ⥤ _) := inferInstance
  exact preservesLimitsOfShape_of_natIso (bcIso p).symm

theorem bc_isPullback {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {U V : Over S} (g : U ⟶ V) :
    IsPullback (pullback.snd p (sch.map U.hom)) ((bc p).map g) (sch.map g.left) (pullback.snd p (sch.map V.hom)) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := pullback.fst p (sch.map V.hom)) (h₂₂ := sch.map V.hom) (v₁₃ := p) ?_ ?_
    (IsPullback.of_hasPullback p (sch.map V.hom)))
  · have h1 : (bc p).map g ≫ pullback.fst p (sch.map V.hom) = pullback.fst p (sch.map U.hom) := by
      simp [bc, pullback.map, pullback.lift_fst]
    have h2 : sch.map g.left ≫ sch.map V.hom = sch.map U.hom := by rw [← sch.map_comp, Over.w g]
    have h3 := IsPullback.of_hasPullback p (sch.map U.hom)
    rw [h2]
    exact h1 ▸ h3
  · simp [bc, pullback.map, pullback.lift_snd]

theorem hyp_coAug : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  intro R _ S E p _ U V g hg k
  refine GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R _ _ (fun n => ?_) U V g ?_
  · have h1 := bc_preserves p (WidePullbackShape (Fin (n + 1)))
    have h2 : PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1)))
        ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k) := inferInstance
    have h3 := preservesLimitsOfShape_of_equiv (widePushoutShapeOpEquiv (Fin (n + 1))).symm
        ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k)
    exact preservesColimitsOfShape_op _ ((Scheme.Etale.forget S ⋙ bc p) ⋙ (evaluation _ PSh).obj k)
  · have he : Etale g.unop.left := by
      have h1 : Etale V.unop.hom := V.unop.prop
      have h2 : Etale U.unop.hom := U.unop.prop
      have h3 : Etale (g.unop.left ≫ U.unop.hom) := by
        rw [MorphismProperty.Over.w g.unop]; exact h1
      exact Etale.of_comp _ U.unop.hom
    exact isLocallySurjective_of_isPullback _ _ _ _
      ((bc_isPullback p ((Scheme.Etale.forget S).map g.unop)).map ((evaluation _ PSh).obj k))
      (yoneda_map_isLocallySurjective_of_etale_surjective _ _ g.unop.left he hg)

end GlobalTheory.EtC.SmallEtaleCech
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) [HasFiniteWidePushouts (S.Etale)ᵒᵖ] (U V : (S.Etale)ᵒᵖ) (g : U ⟶ V), Surjective g.unop.left → Hyp R ((Scheme.Etale.forget S ⋙ bc p).op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (exact GlobalTheory.EtC.SmallEtaleCech.hyp_coAug) | (intros; apply GlobalTheory.EtC.SmallEtaleCech.hyp_coAug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadic
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open WittVector

namespace GlobalTheory.PDivLat

section Vals

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_iterate_teichmuller (x : PreTilt O p) (n : ℕ) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] (teichmuller p x) =
      teichmuller p (x ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobenius_eq_map_frobenius, map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem ghost_teichmuller (n : ℕ) (x : PreTilt O p) :
    ghost p O n (teichmuller p x) = x.untilt ^ p ^ n := by
  rw [ghost, frobenius_iterate_teichmuller, fontaineTheta_teichmuller, map_pow]

theorem ghost_one (n : ℕ) : ghost p O n 1 = 1 := by
  rw [ghost, iterate_map_one, map_one]

theorem ghost_sub (n : ℕ) (a b : Ainf p O) : ghost p O n (a - b) = ghost p O n a - ghost p O n b := by
  rw [ghost, iterate_map_sub, map_sub]; rfl

theorem ghost_pow (n : ℕ) (a : Ainf p O) (k : ℕ) : ghost p O n (a ^ k) = ghost p O n a ^ k := by
  rw [ghost, iterate_map_pow, map_pow]; rfl

theorem ghost_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → Ainf p O) :
    ghost p O n (∑ i ∈ s, f i) = ∑ i ∈ s, ghost p O n (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ghost_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ghost_add, ih]

theorem frobenius_ofPadic (a : ℤ_[p]) : WittVector.frobenius (ofPadic p O a) = ofPadic p O a := by
  ext k
  rw [coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, map_coeff]
  rw [← map_pow, ZMod.pow_card]

end Vals

theorem ghost_values : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have h0 : PreTilt.untilt ε = 1 := hε.zeta_zero
  have h1 : PreTilt.untilt (root ε) ^ p = 1 := by
    have := zeta_succ_pow ε 0
    rw [hε.zeta_zero] at this
    exact this
  have hxi : ∀ n, ghost p O n (xi ε) = ∑ i ∈ Finset.range p, (PreTilt.untilt (root ε) ^ p ^ n) ^ i := by
    intro n
    rw [xi, ghost_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ghost_pow, ghost_teichmuller]
  refine ⟨fun a => rfl, fun n a => ?_, fun n => ?_, ?_, fun n => ?_, fun n a => ?_⟩
  · rw [ghost, Function.iterate_fixed (frobenius_ofPadic a)]
    rfl
  · rw [Sandwich.mu, ghost_sub, ghost_teichmuller, ghost_one, h0, one_pow, sub_self]
  · have hp1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
    rw [hxi, pow_zero, pow_one]
    exact hp1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  · rw [hxi, pow_succ', pow_mul, h1, one_pow]
    simp
  · rw [← ghost_frobenius, GlobalTheory.Dieudonne.frobenius_phiInv]

end GlobalTheory.PDivLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadicStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  first | exact @GlobalTheory.PDivLat.ghost_values | exact GlobalTheory.PDivLat.ghost_values | (intros; apply GlobalTheory.PDivLat.ghost_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.TranslFree

variable {R A B : Type} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Bialgebra R B]
  (f : A →ₐc[R] B)

theorem coassoc (a : A) :
    TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
      ((f : A →ₗ[R] B).lTensor A (comul a))) =
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A (comul a)) := by
  let F : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (B ⊗[R] B) :=
    (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B)).lTensor A
  have h1 : ∀ w : A ⊗[R] A,
      TensorProduct.assoc R A B B (((f : A →ₗ[R] B).lTensor A ∘ₗ comul).rTensor B
        ((f : A →ₗ[R] B).lTensor A w)) =
      F (TensorProduct.assoc R A A A ((comul (R := R)).rTensor A w)) := by
    intro w
    induction w with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply]
      generalize comul (R := R) a = w
      induction w with
      | add u v hu hv => simp only [map_add (f := _), add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : A ⊗[R] A,
      (comul (R := R) (A := B)).lTensor A ((f : A →ₗ[R] B).lTensor A w) =
      F ((comul (R := R)).lTensor A w) := by
    intro w
    induction w with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, F]
      congr 1
      exact (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) b).symm
  rw [h1, h2, Coalgebra.coassoc_apply]

theorem counit_law (a : A) :
    TensorProduct.rid R A ((counit (R := R) (A := B)).lTensor A
      ((f : A →ₗ[R] B).lTensor A (comul a))) = a := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, CoalgHomClass.counit_comp,
    Coalgebra.lTensor_counit_comul]
  simp

end GlobalTheory.TranslFree

theorem GlobalTheory.PDivGroup.transl_free :
    ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by
  intro p R _ G n
  have htransl : (G.transl n).toLinearMap =
      (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor (G.A (n + 1)) ∘ₗ comul := by
    apply LinearMap.ext
    intro a
    simpa only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] using G.transl_apply n a
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simpa only [htransl, transl_apply] using GlobalTheory.TranslFree.coassoc (G.resOne n) a
  · intro a
    simpa only [transl_apply] using GlobalTheory.TranslFree.counit_law (G.resOne n) a
  · intro z
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (G.A (n + 1))
      (g := (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) (G.resOne_surjective n) z
    obtain ⟨x, rfl⟩ := GlobalTheory.HopfQuot.shear_surjective (R := R) y
    refine ⟨x, ?_⟩
    induction x with
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
    | tmul u v =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, GlobalTheory.HopfQuot.shear_tmul, transl_apply]
      generalize comul (R := R) v = w
      induction w with
      | add s t hs ht => simp only [map_add (f := _), mul_add, smul_add, hs, ht]
      | tmul s t => simp [TensorProduct.smul_tmul']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounitalStatement
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transl_coaction_free_coassoc_counital : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by
  first | exact @GlobalTheory.PDivGroup.transl_free | exact GlobalTheory.PDivGroup.transl_free | (intros; apply GlobalTheory.PDivGroup.transl_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
open Formalism.UG GlobalTheory.SatakeWeyl

open Matrix

namespace GlobalTheory.SatakeWeyl.InclusionMultiplication

variable {L : Type} [Field L] {n r : ℕ}

def incl (L : Type) [Field L] (e : Fin r → Fin n) : Matrix (Fin n) (Fin r) L :=
  Matrix.of fun a i => if a = e i then 1 else 0

theorem incl_mul_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix (Fin r) p L)
    (i : Fin r) (j : p) : (incl L e * M) (e i) j = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem incl_mul_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a ≠ e i := fun h => ha ⟨i, h.symm⟩
  simp [incl, this]

theorem mul_inclT_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix p (Fin r) L)
    (i : p) (j : Fin r) : (M * (incl L e)ᵀ) i (e j) = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem mul_inclT_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix p (Fin r) L)
    (i : p) {a : Fin n} (ha : a ∉ Set.range e) : (M * (incl L e)ᵀ) i a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : a ≠ e j := fun h => ha ⟨j, h.symm⟩
  simp [incl, this]

theorem inclT_mul_incl {e : Fin r → Fin n} (he : Function.Injective e) : (incl L e)ᵀ * incl L e = 1 := by
  ext i j
  simp [Matrix.mul_apply, incl, Function.swap, he.eq_iff, Matrix.one_apply, eq_comm]

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if i.rev = j then 1 else 0 := by
  have : (i.val + j.val + 1 = n) ↔ i.rev = j := by
    have := i.2
    rw [Fin.ext_iff, Fin.val_rev]; omega
  simp only [antiJ, this]

theorem antiJ_transpose : (antiJ L n)ᵀ = antiJ L n := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ, add_comm i.val j.val]

theorem antiJ_mul_incl {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    antiJ L n * incl L e = incl L e * antiJ L r := by
  ext a i
  have h1 : (antiJ L n * incl L e) a i = incl L e a.rev i := by
    simp [Matrix.mul_apply, antiJ_apply]
  have h2 : (incl L e * antiJ L r) a i = incl L e a i.rev := by
    simp [Matrix.mul_apply, antiJ_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  simp [incl, hr, Fin.rev_eq_iff]

theorem inclT_mul_antiJ {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    (incl L e)ᵀ * antiJ L n = antiJ L r * (incl L e)ᵀ := by
  have := congrArg Matrix.transpose (antiJ_mul_incl (L := L) hr)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose, antiJ_transpose] at this

def ext1 (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) : Matrix (Fin n) (Fin n) L :=
  1 + incl L e * (M - 1) * (incl L e)ᵀ

theorem extendMatrixByIdentityAlongIndices_mul {e : Fin r → Fin n} (he : Function.Injective e) (M N : Matrix (Fin r) (Fin r) L) :
    ext1 e (M * N) = ext1 e M * ext1 e N := by
  have h : incl L e * (M - 1) * (incl L e)ᵀ * (incl L e * (N - 1) * (incl L e)ᵀ)
      = incl L e * ((M - 1) * (N - 1)) * (incl L e)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl L e)ᵀ, inclT_mul_incl he, Matrix.one_mul]
  have h2 : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold ext1
  rw [add_mul, mul_add, mul_add, h, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  abel

theorem conjTranspose_extendMatrixByIdentityAlongIndices (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT, ext1, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add (f := _),
    map_sum, map_mul, incl, Matrix.of_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite σ, map_one,
    map_zero, Finset.sum_mul]
  congr 1
  · simp only [eq_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [eq_comm (a := i) (b := j)]
    ring

theorem extendMatrixByIdentityAlongIndices_unitary [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {e : Fin r → Fin n} (he : Function.Injective e)
    (hr : ∀ i, e i.rev = (e i).rev) (M : Matrix (Fin r) (Fin r) L)
    (hM : cT σ M * antiJ L r * M = antiJ L r) :
    cT σ (ext1 e M) * antiJ L n * ext1 e M = antiJ L n := by
  have hJ : ∀ N : Matrix (Fin r) (Fin r) L, antiJ L n * ext1 e N
      = ext1 e (antiJ L r * N * antiJ L r) * antiJ L n := by
    intro N
    have h2 : antiJ L r * N * antiJ L r - 1 = antiJ L r * (N - 1) * antiJ L r := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.UnitarySwap.antiJ_mul_self]
    unfold ext1
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, antiJ_mul_incl hr]
    simp only [Matrix.mul_assoc]
    rw [inclT_mul_antiJ hr, ← Matrix.mul_assoc (antiJ L r) (antiJ L r), GlobalTheory.UnitarySwap.antiJ_mul_self,
      Matrix.one_mul]
  rw [conjTranspose_extendMatrixByIdentityAlongIndices, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, ← extendMatrixByIdentityAlongIndices_mul he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
    GlobalTheory.UnitarySwap.antiJ_mul_self]
  simp [ext1]

end GlobalTheory.SatakeWeyl.InclusionMultiplication


open GlobalTheory.SatakeWeyl.InclusionMultiplication in
theorem GlobalTheory.SatakeWeyl.embExists : GlobalTheory.SatakeWeyl.EmbExists := by
  intro L _ _ σ n r e he hr
  choose f hf using fun g : GU σ r => exists_mat (σ := σ) (ext1 e (mat g)) (extendMatrixByIdentityAlongIndices_unitary σ he hr _ g.2)
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, fun g => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · rw [mat_mul, hf, hf, hf, mat_mul, extendMatrixByIdentityAlongIndices_mul he]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply, mul_inclT_apply he, incl_mul_apply he]
    simp [Matrix.one_apply, he.eq_iff]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply]
    rcases hab with h | h
    · rw [Matrix.mul_assoc, incl_mul_apply_of_not _ h, add_zero]
    · rw [mul_inclT_apply_of_not _ _ h, add_zero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbeddingStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smaller_unitary_group_embedding : GlobalTheory.SatakeWeyl.EmbExists := by
  first | exact @GlobalTheory.SatakeWeyl.embExists | exact GlobalTheory.SatakeWeyl.embExists | (intros; apply GlobalTheory.SatakeWeyl.embExists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateQuotientRegular
open MvPolynomial TensorProduct

namespace GlobalTheory

theorem isRegularRing_quotient_etaleCoordinate : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale →
    ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  intro p _ A _ _ n t het j
  let B := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra B A := (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
  have : Algebra.Etale B A := het
  let I : Ideal B := Ideal.span (X '' ({j} : Set (Fin n)))
  have hQ : IsRegularRing (B ⧸ I) :=
    IsRegularRing.of_ringEquiv (quotientSpanXEquiv (ZMod p) ({j} : Set (Fin n))).symm.toRingEquiv
  have : IsRegularRing (TensorProduct B (B ⧸ I) A) := isRegularRing_of_etale (B ⧸ I) _
  have hI : I.map (algebraMap B A) = Ideal.span {t j} := by
    simp only [I, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    show MvPolynomial.aeval t (X j) = t j
    simp
  have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.trans
    (Algebra.TensorProduct.comm B A (B ⧸ I)).toRingEquiv
  rw [hI] at e
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumRankOneReflectionSymmetryOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumRankOneReflectionSymmetryOfSteps
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem rankOne_of_steps : Descent → CellInv → ChainSum → RankOne := by
  intro hD hI hC G A _ _ K N N' ι c Q d h t t' hbi hfin hle hι hsplit hK hnorm hc hQ hidx hex hconj hdc
  obtain ⟨-, e1⟩ := hD G A K N N' ι h t hfin hle hι hsplit hK hnorm
  obtain ⟨f2, e2⟩ := hD G A K N N' ι h t' hfin hle hι hsplit hK hnorm
  have hcomm : ∀ a, t' * ι a = ι ((c ^ d) a) * t' := fun a => by
    rw [← hconj a]; group
  have key := hC A (K.comap ι) c Q d (fun v => cellSum K N' h (t' * ι v)) hc hQ hidx hex
    (by
      intro v hv a
      have := hI G K N' h (t' * ι a) (ι ((c ^ d) v)) 1 hbi hv K.one_mem (by simp) (by simp)
      show cellSum K N' h (t' * ι (v * a)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, ← mul_assoc, hcomm v, mul_one, mul_assoc])
    (by
      intro u hu a
      have := hI G K N' h (t' * ι a) 1 (ι u) hbi K.one_mem hu (hnorm u)
        (fun w hw => by simpa using hnorm u⁻¹ w hw)
      show cellSum K N' h (t' * ι (a * u)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, one_mul, mul_assoc])
    f2
  rw [e1, e2, ← key]
  refine finsum_congr fun y => ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, n1, n2, e⟩ := hdc y.out
  have hcc : (c ^ d) ((c ^ (-d)) y.out) = y.out := by
    rw [← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply]
  rw [hcomm, map_inv, hcc, map_inv, e, hI G K N' h _ k₁ k₂ hbi hk₁ hk₂ n1 n2]

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumRankOneReflectionSymmetryOfStepsStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps : GlobalTheory.SatakeWeyl.Descent → GlobalTheory.SatakeWeyl.CellInv → GlobalTheory.SatakeWeyl.ChainSum → GlobalTheory.SatakeWeyl.RankOne := by
  first | exact @GlobalTheory.SatakeWeyl.rankOne_of_steps | exact GlobalTheory.SatakeWeyl.rankOne_of_steps | (intros; apply GlobalTheory.SatakeWeyl.rankOne_of_steps <;> assumption)
end
end

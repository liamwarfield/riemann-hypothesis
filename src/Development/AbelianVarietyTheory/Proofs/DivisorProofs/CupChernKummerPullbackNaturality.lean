module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSection
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeSequenceExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6nat_holds : GlobalTheory.EtC.DivisorNaturality := by
  intro q _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f n m i j a b
    exact GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b
  · intro E E' f h
    exact (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.1 f h
  · intro E E' f L h
    exact (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 f L h
  · intro Y X f u h
    exact (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 f u h

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_chern_kummer_pullback_naturality : GlobalTheory.EtC.DivisorNaturality := by
  first | (exact @GlobalTheory.EtC.a6nat_holds) | (exact GlobalTheory.EtC.a6nat_holds) | (intros; apply GlobalTheory.EtC.a6nat_holds  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_cohomology_vanishing_negative_degree_zero : A9 := by
  intro R _ F
  refine ⟨?_, ?_⟩
  · intro E n hn
    have hz : ∀ α : Cochain ((chains R).obj E) (res R F) n, α = 0 := by
      intro α
      apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α 0
      intro p s h U x
      have hs : s < 0 := by omega
      haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs)
      exact Subsingleton.elim _ _
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := a.mk_surjective
    obtain ⟨b, rfl⟩ := b.mk_surjective
    have : a = b := Cocycle.ext (by rw [hz a.1, hz b.1])
    rw [this]
  · let f : ∀ X : Scheme.{0}, Sec F X →+ H R (sch.obj X) F 0 := fun X =>
      AddMonoidHom.mk' (secClass F (X := X)) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.1
    refine ⟨fun X => AddEquiv.ofBijective (f X) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.1, ?_, ?_⟩
    · intro Y X g s
      exact (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.2.1 g s
    · intro X s
      obtain ⟨α, hα⟩ := (secClass F s).mk_surjective
      exact ⟨α, hα, ((GlobalTheory.T.degreeZeroSectionClass_properties R F X).1 s α).2 hα⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero : GlobalTheory.EtC.A9 := by
  first | exact @GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | exact GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero | (intros; apply GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorBoxEqCharSum
open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxCharComb

open GlobalTheory.LocMod.Inhab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_box_superset {K : Set (Matrix Y Y' k)} (hK : IsCompact K) :
    ∃ R : kˣ, ∀ x ∈ K, x ∈ box Y Y' R := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ (box Y Y' (1 : kˣ) : Set (Matrix Y Y' k))) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually
        ((isOpen_box (Y := Y) (Y' := Y') (1 : kˣ)).mem_nhds (box Y Y' 1).zero_mem)
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s⁻¹, fun x hx r q => ?_⟩
  have h1 : valuation k (((s : k) • x) r q) ≤ valuation k ((1 : kˣ) : k) :=
    hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) x hx r q
  have e : x r q = (s : k)⁻¹ * (((s : k) • x) r q) := by
    rw [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ s.ne_zero]
  rw [e, map_mul, Units.val_inv_eq_inv_val]
  exact mul_le_of_le_one_right' (by simpa only [Units.val_one, map_one] using h1)

end GlobalTheory.BoxCharComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficients
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart

open ValuativeRel

def coeffOnChart {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D)
    (Y : Matrix (R ⊕ T) D k) : Matrix T R k :=
  (Y.submatrix Sum.inl τ).det⁻¹ • (Y.toRows₂.submatrix id τ * (Y.submatrix Sum.inl τ).adjugate)

theorem coeffOnChart_stack {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
    [Fintype D] [DecidableEq D] (τ : R → D)
    (Y₁ : Matrix R D k) (C : Matrix T R k) (h : (Y₁.submatrix id τ).det ≠ 0) :
    coeffOnChart τ (stack Y₁ C) = C := by
  have e1 : (stack Y₁ C).submatrix Sum.inl τ = Y₁.submatrix id τ := by
    rw [submatrix_inl_eq, toRows₁_stack]
  have e2 : (stack Y₁ C).toRows₂.submatrix id τ = C * Y₁.submatrix id τ := by
    ext i j; simp [stack, Matrix.mul_apply]
  rw [coeffOnChart, e1, e2, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ h, one_smul]

theorem coeffOnChart_continuousOn {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [ContinuousInv₀ k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D) :
    ContinuousOn (coeffOnChart (T := T) (k := k) τ) {Y | (Y.submatrix Sum.inl τ).det ≠ 0} := by
  have hA : Continuous fun Y : Matrix (R ⊕ T) D k => Y.submatrix Sum.inl τ :=
    continuous_id.matrix_submatrix _ _
  have hB : Continuous fun Y : Matrix (R ⊕ T) D k => Y.toRows₂.submatrix id τ :=
    (continuous_id.matrix_submatrix Sum.inr id).matrix_submatrix _ _
  exact ContinuousOn.smul (f := fun Y : Matrix (R ⊕ T) D k => (Y.submatrix Sum.inl τ).det⁻¹)
    (hA.matrix_det.continuousOn.inv₀ fun Y hY => hY) (hB.matrix_mul hA.matrix_adjugate).continuousOn

theorem bounded_coeff_of_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) :
    ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) →
      ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 →
        C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  intro f hf hdet
  have hcl : IsClosed (Function.support f) := by
    have := (hf.1.isOpen_fiber 0).isClosed_compl
    simpa [Function.support, Set.compl_setOf] using this
  have hK : IsCompact (Function.support f) := by
    have h2 : HasCompactSupport f := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at h2
    exact h2
  have hcont : ContinuousOn (coeffOnChart (T := T) (k := k) τ) (Function.support f) :=
    (coeffOnChart_continuousOn τ).mono fun Y hY => hdet Y hY
  obtain ⟨a, ha⟩ := GlobalTheory.BoxCharComb.exists_box_superset (hK.image_of_continuousOn hcont)
  refine ⟨a, fun Y₁ C hY => ?_⟩
  have hd := hdet _ hY
  rw [submatrix_inl_eq, toRows₁_stack] at hd
  have := ha _ ⟨_, hY, coeffOnChart_stack τ Y₁ C hd⟩
  exact this

end GlobalTheory.RankChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficientsStatement
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_bounded_coefficients : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 → C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  first | exact @GlobalTheory.RankChart.bounded_coeff_of_SB | exact GlobalTheory.RankChart.bounded_coeff_of_SB | (intros; apply GlobalTheory.RankChart.bounded_coeff_of_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedExists

def constCx {R : Type} [CommRing R] (F : Shv R) : Cx R where
  X _ := F
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

theorem ext_map (Q q : ℕ) (hq : q ∣ Q) (F : Shv (ZMod Q)) (G : Shv (ZMod q))
    (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hf : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) :
    ∃ α : (extSh (ZMod.castHom hq (ZMod q))).obj F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U),
      Sec.map α (extSh.sec (ZMod.castHom hq (ZMod q)) F U a) = f U a := by
  let ρ : SemiMap (constCx F) (constCx G) :=
    { app := fun U _ => f U
      nat := fun g _ a => hf _ _ g a
      comm := fun U s t a => by
        show Sec.map (0 : G ⟶ G) (f U a) = f U (Sec.map (0 : F ⟶ F) a)
        simp [Sec.map]
        exact ((f U).map_zero).symm }
  exact ⟨FactorExt.term _ (FactorExt.intCast_surj Q) ρ 0,
    fun U a => FactorExt.term_sec _ (FactorExt.intCast_surj Q) ρ 0 U a⟩

def semiOfExt {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) : SemiMap I K where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom.comp ((extπ (ZMod.castHom hq (ZMod q)) I).app U s)
  nat g s a := by
    have h := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op))
      ((extπ (ZMod.castHom hq (ZMod q)) I).app _ s a)).symm
    refine h.trans ?_
    exact congrArg (fun x => ((m.f s).hom.app (op _)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).nat g s a)
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a))) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · exact congrArg (fun x => ((m.f t).hom.app (op U)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).comm U s t a)

theorem semiOfExt_app {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (semiOfExt hq m).app U s a = Sec.map (m.f s) (extSh.sec (ZMod.castHom hq (ZMod q)) (I.X s) U a) := rfl

def powPrim {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.EtC.PrimBasic.prim_basic Q A).2.2.2.2.2 q hq ζ
    rw [← h]
    exact ξ.2⟩

theorem powPrim_map {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (ζ : Prim Q A) : (powPrim hq ζ).map φ = powPrim hq (ζ.map φ) :=
  Subtype.ext (map_pow φ _ _)

theorem nsmul_mod_of {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) (n : ℕ) :
    n • x = (n % q) • x := by
  have hq : q • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (by simp)
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm q, mul_smul, hq, smul_zero, add_zero]

theorem twRed_sec : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ), ∃ f : ∀ U : Scheme.{0}, Sec (tw Q i) U →+ Sec (tw q i) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec (tw Q i) U), Sec.res g (f U a) = f V (Sec.res g a)) ∧
    ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → f U (twGen i ζ) = twGen i ξ := by
  intro Q q _ _ hq i
  let M : Shv (ZMod Q) := (GlobalTheory.EtC.restr (ZMod.castHom hq (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (powPrim hq ζ) : Sec (tw q i) U)
  have ts := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim Q Γ(U, ⊤)), Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have := ts.2.2.2.1 V U g (powPrim hq ζ)
    rw [powPrim_map] at this
    exact this
  have hcast : ∀ u : (ZMod Q)ˣ, ((ZMod.unitsMap hq u : (ZMod q)ˣ) : ZMod q).val = (u : ZMod Q).val % q := by
    intro u
    show (ZMod.castHom hq (ZMod q) (u : ZMod Q)).val = _
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a h
    have hq1 : (ζ.1 ^ (Q / q)) ^ q = 1 := (GlobalTheory.EtC.PrimBasic.prim_basic q _).1 (powPrim hq ζ)
    have hpw : (powPrim hq ξ).1 = (powPrim hq ζ).1 ^ ((ZMod.unitsMap hq a : (ZMod q)ˣ) : ZMod q).val := by
      rw [hcast]
      show ξ.1 ^ (Q / q) = (ζ.1 ^ (Q / q)) ^ ((a : ZMod Q).val % q)
      rw [h, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.mod_add_div (a : ZMod Q).val q]
      rw [pow_add, pow_mul, hq1, one_pow, mul_one]
    have h5 := ts.2.2.2.2.1 U (powPrim hq ζ) (powPrim hq ξ) (ZMod.unitsMap hq a) hpw
    show (twGen i (powPrim hq ξ) : Sec (tw q i) U) =
      ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • (twGen i (powPrim hq ζ) : Sec (tw q i) U)
    have hm : (((ZMod.unitsMap hq a) ^ i : (ZMod q)ˣ) : ZMod q).val % q = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val % q := by
      rw [show (ZMod.unitsMap hq a) ^ i = ZMod.unitsMap hq (a ^ i) from (map_zpow _ _ _).symm, hcast, Nat.mod_mod]
    rw [h5, nsmul_mod_of (q := q) (twGen i (powPrim hq ζ)), hm, ← nsmul_mod_of (q := q)]
  obtain ⟨β, hβ, -⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).2.2.2.2.2 M e he1 he2
  refine ⟨fun U => ⟨⟨fun a => ((β.hom.app (op U)).hom a : Sec (tw q i) U), (β.hom.app (op U)).hom.map_zero⟩,
    fun a b => (β.hom.app (op U)).hom.map_add a b⟩, ?_, ?_⟩
  · intro V U g a
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (β.hom.naturality g.op)) a).symm
  · intro U ζ ξ h
    have h1 := hβ U ζ
    have h2 : powPrim hq ζ = ξ := Subtype.ext h.symm
    exact h1.trans (congrArg (twGen i) h2)

theorem redMap_exists (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ) :
    ∃ ρ : SemiMap (res _ (tw Q i)) (res _ (tw q i)), ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
      ξ.1 = ζ.1 ^ (Q / q) → ρ.app U 0 (resGen i ζ) = resGen i ξ := by
  obtain ⟨f, hf, hfg⟩ := twRed_sec Q q hq i
  obtain ⟨α, hα⟩ := ext_map Q q hq (tw Q i) (tw q i) f hf
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  have hQ := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))
    (extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) (res _ (tw q i))
    (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).1
    ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i))
  refine ⟨semiOfExt hq m, fun U ζ ξ h => ?_⟩
  have hv : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 := by
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        m.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ m.f 0) hs').trans (Category.assoc _ _ _)
  have hw : ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        α ≫ resι _ (tw q i) := by
    rw [HomologicalComplex.comp_f, ← hι]
    change ((HomologicalComplex.single (Shv (ZMod q)) (ComplexShape.up ℤ) 0).map α).f 0 ≫ _ = _
    rw [HomologicalComplex.single_map_f_self]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    exact Category.assoc _ _ _
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 = α ≫ resι _ (tw q i) := by
    have e : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
        ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 := by rw [hm]
    rw [hv, hw] at e
    exact (cancel_epi _).1 e
  rw [semiOfExt_app]
  change Sec.map (m.f 0) (extSh.sec _ _ U (Sec.map (resι _ (tw Q i)) (twGen i ζ))) = Sec.map (resι _ (tw q i)) (twGen i ξ)
  rw [← extSh.sec_map, ← hfg U ζ ξ h, ← hα]
  have e2 := congrArg (fun k => Sec.map k (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) U (twGen i ζ))) key
  exact e2

theorem red_exists : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  intro Q q _ _ hq i U ζ ξ h
  exact pick_spec (redMap_exists Q q hq i) U ζ ξ h

end GlobalTheory.EtC.RedExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistReductionResolutionMap_generator : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  first | (exact @GlobalTheory.EtC.RedExists.red_exists) | (exact GlobalTheory.EtC.RedExists.red_exists) | (intros; apply GlobalTheory.EtC.RedExists.red_exists  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6add_holds : GlobalTheory.EtC.DivisorAdditivity := by
  intro q _
  exact ⟨fun L M N hE hN => (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.2 L M N hE hN,
    fun u v hq => (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 u v hq⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernClass_kummerClass_additive : GlobalTheory.EtC.DivisorAdditivity := by
  first | (exact @GlobalTheory.EtC.a6add_holds) | (exact GlobalTheory.EtC.a6add_holds) | (intros; apply GlobalTheory.EtC.a6add_holds  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
namespace GlobalTheory.IntFiniteTypeDim

theorem exists_natPrime_mem_of_isMaximal (A : Type) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : A) ∈ m := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  letI := Ideal.Quotient.field m
  have hfin : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  rcases CharP.char_is_prime_or_zero (A ⧸ m) p with h | h
  · refine ⟨p, h, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · subst h
    haveI : CharZero (A ⧸ m) := CharP.charP_to_charZero _
    exfalso
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ m)) :=
      RingHom.injective_int _
    exact Int.not_isField
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (A ⧸ m)))

theorem ringKrullDim_quotient_le_of_minimalPrimes {A : Type} [CommRing A] (I : Ideal A)
    (c : WithBot ℕ∞) (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (A ⧸ P) ≤ c) :
    ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := s.head.1.asIdeal) s.head.2
  refine le_trans ?_ (h P hP)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) P) :=
    ⟨s.length, fun i => ⟨(s i).1, hle.trans (show s.head.1 ≤ (s i).1 from s.head_le i)⟩,
      fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t

theorem ringKrullDim_eq_trdeg_add_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
      Function.Injective (algebraMap ℤ A) →
        ringKrullDim A = ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) := by
  intro A _ _ _ hinj
  haveI : CharZero A := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ℤ) (S := A))
  have hrhs : ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) =
      (d : WithBot ℕ∞) + 1 := by
    rw [hd, Cardinal.toENat_nat]; rfl
  rw [hrhs]
  apply le_antisymm
  · refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun m hm => ?_
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    refine (Ideal.height_le_ringKrullDim_quotient_add_one hlm).trans ?_
    gcongr
    refine ringKrullDim_quotient_le_of_minimalPrimes _ _ fun q hq => ?_
    haveI := hq.1.1
    exact (ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd).le
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {(l : A)}) (J := m)
      ((Ideal.span_singleton_le_iff_mem _).mpr hlm)
    haveI := hq.1.1
    rw [← ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd]
    have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      (r := (l : A)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hl.ne_zero))
      (Ideal.Quotient.eq_zero_iff_mem.mpr hlq)

end GlobalTheory.IntFiniteTypeDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmul
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.OmLoc

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem pow_smul_d_mem (B : Subalgebra k K) {f v : K} (hf : f ∈ B) (M : ℕ) (hw : v * f ^ M ∈ B) :
    (f ^ (M + M)) • ι1 (D k K v) ∈ omB k K B 1 := by
  have hD : ∀ u ∈ B, ι1 (D k K u) ∈ omB k K B 1 := by
    intro u hu
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, fun _ => u, fun _ => hu, ?_⟩
    rw [one_smul, ExteriorAlgebra.ιMulti_apply]
    simp
  have hc : ∀ c ∈ B, ∀ a ∈ omB k K B 1, c • a ∈ omB k K B 1 := fun c hc a ha =>
    ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B 1 1).2.1 a ha).2.2.2 c hc
  have key : (f ^ (M + M)) • ι1 (D k K v) =
      f ^ M • ι1 (D k K (v * f ^ M)) - (v * f ^ M) • ι1 (D k K (f ^ M)) := by
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_add, smul_smul, smul_smul, pow_add,
      mul_comm (f ^ M) v]
    abel
  rw [key]
  exact sub_mem (hc _ (pow_mem hf M) _ (hD _ hw)) (hc _ hw _ (hD _ (pow_mem hf M)))

end GlobalTheory.PD.OmLoc

namespace GlobalTheory

theorem omB_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K),
      y ∈ omB k K (rB k K x I) q ↔
        ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  intro k _ _ F K _ _ _ _ _ _ d x h I i hi q y
  set f := algebraMap F K (∏ j ∈ I, x j / x i) with hfdef
  obtain ⟨hmono1, -⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)
  obtain ⟨-, hloc⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi
  have hBB' : rB k K x {i} ≤ rB k K x I := hmono1 I (Finset.singleton_subset_iff.2 hi)
  have hfB : f ∈ rB k K x {i} := by
    have hz : (∏ j ∈ I, x j / x i) ∈ rA k x {i} :=
      Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
    show IsIntegral (rA k x {i}) f
    exact isIntegral_algebraMap (R := rA k x {i}) (A := K) (x := ⟨_, hz⟩)
  have hf0 : f ≠ 0 :=
    (map_ne_zero (algebraMap F K)).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.pd.ne j) (h.pd.ne i))
  have hfinv : f⁻¹ ∈ rB k K x I :=
    (hloc _).2 ⟨1, by rw [pow_one, inv_mul_cancel₀ hf0]; exact Subalgebra.one_mem _⟩
  have hsmul : ∀ (C : Subalgebra k K) (p : ℕ), ∀ c ∈ C, ∀ a ∈ omB k K C p, c • a ∈ omB k K C p :=
    fun C p c hc a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K C p p).2.1 a ha).2.2.2 c hc
  constructor
  · intro hy
    have hQc : ∀ (p : ℕ) (c : K) (z : DR k K), c ∈ rB k K x I →
        (∃ N : ℕ, f ^ N • z ∈ omB k K (rB k K x {i}) p) → ∃ N : ℕ, f ^ N • (c • z) ∈ omB k K (rB k K x {i}) p := by
      rintro p c z hc ⟨N, hN⟩
      obtain ⟨M, hM⟩ := (hloc c).1 hc
      refine ⟨M + N, ?_⟩
      have e : f ^ (M + N) • (c • z) = (c * f ^ M) • (f ^ N • z) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      rw [e]
      exact hsmul _ p _ hM _ hN
    have hQmul : ∀ (p p' : ℕ) (a b : DR k K), (∃ N : ℕ, f ^ N • a ∈ omB k K (rB k K x {i}) p) →
        (∃ N : ℕ, f ^ N • b ∈ omB k K (rB k K x {i}) p') →
        ∃ N : ℕ, f ^ N • (a * b) ∈ omB k K (rB k K x {i}) (p + p') := by
      rintro p p' a b ⟨N, hN⟩ ⟨N', hN'⟩
      refine ⟨N + N', ?_⟩
      have e : f ^ (N + N') • (a * b) = (f ^ N • a) * (f ^ N' • b) := by
        rw [pow_add, mul_smul, smul_mul_assoc, mul_smul_comm]
      rw [e]
      exact (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) p p').1 _ hN _ hN'
    have hQ1 : ∀ v ∈ rB k K x I, ∃ N : ℕ, f ^ N • ι1 (D k K v) ∈ omB k K (rB k K x {i}) 1 := by
      intro v hv
      obtain ⟨M, hM⟩ := (hloc v).1 hv
      exact ⟨M + M, GlobalTheory.PD.OmLoc.pow_smul_d_mem _ hfB M hM⟩
    have hQm : ∀ (n : ℕ) (v : Fin n → K), (∀ j, v j ∈ rB k K x I) →
        ∃ N : ℕ, f ^ N • ExteriorAlgebra.ιMulti K n (fun j => D k K (v j)) ∈ omB k K (rB k K x {i}) n := by
      intro n
      induction n with
      | zero =>
        intro v _
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul, ExteriorAlgebra.ιMulti_zero_apply]
        exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) 0 0).2.2.2 1).2 ⟨1, Subalgebra.one_mem _, (map_one _).symm⟩
      | succ n ih =>
        intro v hv
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        have := hQmul 1 n _ _ (hQ1 (v 0) (hv 0)) (ih (fun j => v j.succ) fun j => hv j.succ)
        rw [Nat.add_comm 1 n] at this
        exact this
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hz
      exact hQc q b _ hb (hQm q v hv)
    | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
    | add a c _ _ ha hc =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hc
      refine ⟨N₁ + N₂, ?_⟩
      rw [smul_add]
      apply add_mem
      · rw [pow_add, mul_comm, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₁
      · rw [pow_add, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₂
    | smul r a _ ha =>
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, by rw [smul_comm]; exact Submodule.smul_mem _ r hN⟩
  · rintro ⟨N, hN⟩
    have := hsmul _ q (f⁻¹ ^ N) (pow_mem hfinv N) _
      ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) q q).2.2.1 _ hBB' hN)
    rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_smul] at this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K), y ∈ omB k K (rB k K x I) q ↔ ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  first | (exact @GlobalTheory.omB_iff_pow_smul) | (exact GlobalTheory.omB_iff_pow_smul) | (intros; apply GlobalTheory.omB_iff_pow_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_isLocallySurjective : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q),
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from
      (Arrow.mk f).augmentedCechNerve.hom)) := by
  intro R _ P Q f hf
  exact GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R f (fun U y => ⟨Presheaf.imageSieve f y, hf.imageSieve_mem y, fun V g hg => hg⟩)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsomComp
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.EmbConj

open GlobalTheory.PadicComplexHost

variable {p : ℕ} [Fact p.Prime]

theorem injective_of_comp {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] (φ : Λ →+* PadicAlgCl p)
    (h : φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
  change Ideal.comap (algebraMap ℤ_[p] Λ) (RingHom.ker φ) = ⊥
  rw [RingHom.comap_ker, h, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), RingHom.coe_comp]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem exists_algEquiv {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (φ₀ φ₁ : Λ →+* PadicAlgCl p)
    (h₀ : φ₀.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p))
    (h₁ : φ₁.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, σ (φ₀ x) = φ₁ x := by
  have tf : ∀ φ : Λ →+* PadicAlgCl p, Function.Injective φ →
      letI := φ.toAlgebra
      Module.IsTorsionFree Λ (PadicAlgCl p) := fun φ hφ => by
    letI := φ.toAlgebra
    haveI : FaithfulSMul Λ (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
    infer_instance
  have alg : letI := φ₀.toAlgebra
      Algebra.IsAlgebraic Λ (PadicAlgCl p) := by
    letI := φ₀.toAlgebra
    haveI : IsScalarTower ℤ_[p] Λ (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq' h₀.symm
    haveI : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) := ⟨fun x =>
      (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] (PadicAlgCl p)).2
        (Algebra.IsAlgebraic.isAlgebraic x)⟩
    exact Algebra.IsAlgebraic.extendScalars (R := ℤ_[p]) (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨g, hg⟩ : ∃ g : PadicAlgCl p →+* PadicAlgCl p, ∀ x, g (φ₀ x) = φ₁ x := by
    let f := @IsAlgClosed.lift (PadicAlgCl p) _ _ Λ _ _ (PadicAlgCl p) _ _ φ₀.toAlgebra
      φ₁.toAlgebra (tf φ₀ (injective_of_comp φ₀ h₀)) (tf φ₁ (injective_of_comp φ₁ h₁)) alg
    exact ⟨@AlgHom.toRingHom _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f,
      fun x => @AlgHom.commutes _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f x⟩
  have hq : g.comp (algebraMap ℚ_[p] (PadicAlgCl p)) = algebraMap ℚ_[p] (PadicAlgCl p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    ext a
    exact (congrArg g (RingHom.congr_fun h₀ a).symm).trans
      ((hg _).trans (RingHom.congr_fun h₁ a))
  let g' : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p := { g with commutes' := RingHom.congr_fun hq }
  exact ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective g'), hg⟩

end GlobalTheory.EmbConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartHodgeMatrix
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isLocalizationAway_of_le {k L : Type} [Field k] [Field L] [Algebra k L] {A B : Subalgebra k L}
    [Algebra A B] (hab : ∀ a : A, ((algebraMap A B a : B) : L) = a) (s : A) (hs : (s : L) ≠ 0)
    (hsi : (s : L)⁻¹ ∈ B) (hy : ∀ y ∈ B, ∃ N : ℕ, y * (s : L) ^ N ∈ A) : IsLocalization.Away s B := by
  have hu : IsUnit (algebraMap A B s) :=
    isUnit_iff_exists_inv.mpr ⟨⟨(s : L)⁻¹, hsi⟩, Subtype.ext (by simp [hab, hs])⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa using hu.pow n
  · intro z
    obtain ⟨N, hN⟩ := hy z z.2
    exact ⟨(⟨_, hN⟩, ⟨s ^ N, N, rfl⟩), Subtype.ext (by simp [hab])⟩
  · intro a b h
    refine ⟨1, ?_⟩
    have := congrArg (fun z : B => (z : L)) h
    simp only [hab] at this
    simp [Subtype.ext this]

theorem smooth_of_le_away {k L : Type} [Field k] [Field L] [Algebra k L] {A B : Subalgebra k L} (hle : A ≤ B)
    (s : L) (hsA : s ∈ A) (hs : s ≠ 0) (hsi : s⁻¹ ∈ B) (hy : ∀ y ∈ B, ∃ N : ℕ, y * s ^ N ∈ A)
    [Algebra.Smooth k A] : Algebra.Smooth k B := by
  letI : Algebra A B := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨s, hsA⟩ : A) B := isLocalizationAway_of_le (fun _ => rfl) _ hs hsi hy
  haveI : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (⟨s, hsA⟩ : A)
  exact Algebra.Smooth.comp k A B

section Parts

variable {k : Type} [Field k] {F K : Type} [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] {d : ℕ} {x : Fin (d + 1) → F}

theorem prod_ratio_ne_zero (h : IsPd k x) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.ne j) (h.ne i)

theorem prod_ratio_mem (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩

theorem prod_ratio_inv_mem (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : (∏ j ∈ I, x j / x i)⁻¹ ∈ rA k x I := by
  rw [← Finset.prod_inv_distrib]
  exact Subalgebra.prod_mem _ fun j hj => by
    rw [inv_div]; exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩

theorem rA_singleton_le {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) : rA k x {i} ≤ rA k x I :=
  Algebra.adjoin_mono fun _ ⟨i', hi', j, hy⟩ => ⟨i', by rw [Finset.mem_singleton.1 hi']; exact hi, j, hy⟩

theorem rA_isIntegrallyClosed (h : IsPd k x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsIntegrallyClosed (rA k x I) := by
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h i
  haveI : IsIntegrallyClosed (rA k x {i}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  letI : Algebra (rA k x {i}) (rA k x I) := (Subalgebra.inclusion (rA_singleton_le hi)).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨_, prod_ratio_mem I i⟩ : rA k x {i}) (rA k x I) :=
    isLocalizationAway_of_le (fun _ => rfl) _ (prod_ratio_ne_zero h I i) (prod_ratio_inv_mem I i)
      fun y hy => (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x h I i hi y).1 hy
  exact isIntegrallyClosed_of_isLocalization (rA k x I) (Submonoid.powers (⟨_, prod_ratio_mem I i⟩ : rA k x {i}))
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 => prod_ratio_ne_zero h I i (congrArg Subtype.val h0))

theorem rA_finite (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    Module.Finite (rA k x I) (integralClosure (rA k x I) K) := by
  haveI := h.fin
  haveI := h.sep
  haveI : IsFractionRing (rA k x I) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).1
  haveI : IsNoetherianRing (rA k x I) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).2
  haveI := rA_isIntegrallyClosed h.pd hi
  set_option synthInstance.maxHeartbeats 200000 in
    exact IsIntegralClosure.finite (rA k x I) F K (integralClosure (rA k x I) K)

theorem rB_frac (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    IsFractionRing (rB k K x I) K := by
  haveI := h.fin
  haveI : IsFractionRing (rA k x I) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x h.pd I ⟨i, hi⟩).1
  exact integralClosure.isFractionRing_of_finite_extension F K

theorem rB_smooth [CharZero k] (h : IsFinCover k K x) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) :
    Algebra.Smooth k (rB k K x I) := by
  have hleB : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)).1 I (Finset.singleton_subset_iff.2 hi)
  have hloc := (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi).2
  have hsB : algebraMap F K (∏ j ∈ I, x j / x i) ∈ rB k K x {i} :=
    (integralClosure (rA k x {i}) K).algebraMap_mem ⟨_, prod_ratio_mem I i⟩
  have hsiB : (algebraMap F K (∏ j ∈ I, x j / x i))⁻¹ ∈ rB k K x I := by
    rw [← map_inv₀]; exact (integralClosure (rA k x I) K).algebraMap_mem ⟨_, prod_ratio_inv_mem I i⟩
  haveI := h.smooth i
  exact smooth_of_le_away hleB _ hsB ((map_ne_zero _).2 (prod_ratio_ne_zero h.pd I i)) hsiB fun y hy => (hloc y).1 hy

end Parts

theorem rB_finite_frac_smooth : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧
      IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  intro k _ _ F K _ _ _ _ _ _ d x h I hI
  obtain ⟨i, hi⟩ := hI
  exact ⟨rA_finite h hi, rB_frac h hi, rB_smooth h hi⟩

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6supp : DivisorSupportCondition := by
  intro q _ U V E f g hc n m i j a b ha hb
  exact GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover (ZMod q) (twPair q i j) ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)).2.1)
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q j)).2.1) f g hc rfl a b ha hb

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_vanishes_on_two_member_cover : GlobalTheory.EtC.DivisorSupportCondition := by
  first | (exact @GlobalTheory.EtC.a6supp) | (exact GlobalTheory.EtC.a6supp) | (intros; apply GlobalTheory.EtC.a6supp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExact
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.MVFree

theorem shortExact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ (w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0), (ShortComplex.mk _ _ w).ShortExact := by
  intro R _ A A' _ _ _ _ f hN w
  obtain ⟨h1, h2⟩ := hN
  obtain ⟨w', hex⟩ := GlobalTheory.T.etale_mayerVietoris_free_sequence_exact R A A' f h1 h2
  have hm := GlobalTheory.T.mono_free_etale_mayerVietoris_left_map R A A' f
  have he := GlobalTheory.T.etaleMayerVietoris_free_right_epi R A A' f h1 h2
  exact { exact := hex, mono_f := hm, epi_g := he }

end GlobalTheory.EtC.MVFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleSheaf_excision_shortExact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ (w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0), (ShortComplex.mk _ _ w).ShortExact := by
  first | (exact @GlobalTheory.EtC.MVFree.shortExact) | (exact GlobalTheory.EtC.MVFree.shortExact) | (intros; apply GlobalTheory.EtC.MVFree.shortExact <;> assumption)
end
end

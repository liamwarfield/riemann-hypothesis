module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHodgeCohomologyEquivCechDifferentials
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteCoverProjSpaceReducedFibreOriginStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartLiftOfFiniteCover
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceComplexPointsStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceLocalParametersStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFamilyStatement
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUniqueComplexPointLiftClopenCover
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgeTraceEqSumClopenDecomposition
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsTangentMatrixIffRestrictOpen

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceSectionsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

private theorem germ_ex {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (e : V = W) (hV : genericPoint X ∈ V)
    (hW : genericPoint X ∈ W) (y : X.functionField) :
    (∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hV).hom f = y) ↔
      ∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hW).hom f = y := by
  subst e; rfl

private theorem ring_single {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type}
    {U : ι → X.Opens} {B : Finset ι → Subalgebra ℂ X.functionField} (h : IsAffCover p U B) (i : ι)
    (hg : genericPoint X ∈ U i) (y : X.functionField) :
    y ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y :=
  (h.ring {i} ⟨i, by simp⟩ y).trans (germ_ex (Finset.inf_singleton ..) _ _ y)

private theorem clear_denom {Y : Scheme.{0}} [IsIntegral Y] (s' : Y ⟶ Sp ℂ) [Algebra ℂ Y.functionField] {A W : Y.Opens}
    (hA : IsAffineOpen A) (gA : genericPoint Y ∈ A) (gW : genericPoint Y ∈ W) (B : Subalgebra ℂ Y.functionField)
    (hB : ∀ y, y ∈ B ↔ ∃ f : Γ(Y, A), (Y.presheaf.germ A (genericPoint Y) gA).hom f = y) (e : B →ₐ[ℂ] ℂ)
    (y : CxPts s' (RingHom.id ℂ)) (hM : UpperTheory.A.Mt s' A gA B e y) (hyW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W)
    (f : Γ(Y, W)) :
    ∃ (b : Y.functionField) (hb : b ∈ B), e ⟨b, hb⟩ ≠ 0 ∧
      b * (Y.presheaf.germ W (genericPoint Y) gW).hom f ∈ B := by
  obtain ⟨hyA, hev⟩ := hM
  obtain ⟨h, hhW, hh⟩ := hA.exists_basicOpen_le (V := W) ⟨_, CxPts.mem_ptsIn.1 hyW⟩ (CxPts.mem_ptsIn.1 hyA)
  have hD : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen h) := CxPts.mem_ptsIn.2 hh
  have hne := (CxPts.mem_ptsIn_basicOpen hyA h).1 hD
  have gD : genericPoint Y ∈ Y.basicOpen h :=
    ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen h).isOpen).2 ⟨_, trivial, hh⟩
  have := hA.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((Y.presheaf.map (homOfLE hhW).op).hom f)
  have hb : (Y.presheaf.germ A (genericPoint Y) gA).hom (h ^ n) ∈ B := (hB _).2 ⟨_, rfl⟩
  refine ⟨_, hb, ?_, (hB _).2 ⟨a, ?_⟩⟩
  · rw [hev (h ^ n) hb, CxPts.ev_eq hyA, map_pow, ← CxPts.ev_eq hyA]
    exact pow_ne_zero n hne
  · have e1 := congrArg (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom ha
    have e2 : ∀ g : Γ(Y, A), (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom (algebraMap Γ(Y, A) Γ(Y, Y.basicOpen h) g)
        = (Y.presheaf.germ A (genericPoint Y) gA).hom g := fun g =>
      Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le h)) (genericPoint Y) gD g
    have e3 : (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom ((Y.presheaf.map (homOfLE hhW).op).hom f)
        = (Y.presheaf.germ W (genericPoint Y) gW).hom f :=
      Y.presheaf.germ_res_apply (homOfLE hhW) (genericPoint Y) gD f
    rw [map_mul, map_pow, e2, e2, e3] at e1
    rw [map_pow, mul_comm]
    exact e1.symm

theorem UpperTheory.etaleCorrespondence_sections_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (i : Fin (d + 1)) (e : rB ℂ Y.functionField x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : Y.functionField) (hb : b ∈ rB ℂ Y.functionField x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ Y.functionField x {i} := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU i e
  obtain ⟨-, hU1⟩ := UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU
  have hU2 := UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hP c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have gen : ∀ (c : Y ⟶ Z) [Etale c] (k : Fin (d + 1)), genericPoint Y ∈ c ⁻¹ᵁ U k := fun c _ k => by
    change c (genericPoint Y) ∈ U k
    rw [UpperTheory.A.generic_map c]
    simpa using hU.ne {k}
  have hA : IsAffineOpen (c1 ⁻¹ᵁ U i) := by simpa using hU1.affine {i} ⟨i, by simp⟩
  have hB := ring_single hU1 i (gen c1 i)
  obtain ⟨y, hy, -⟩ := (UpperTheory.complexPoints_bijective_algHom_affineOpen Y s' hL _ hA (gen c1 i) _ hB).1 e
  obtain ⟨j, hj⟩ := CxPts.exists_mem_ptsIn hU.cover (UpperTheory.A.zpt c2 h2 y)
  have hyW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U j) := by
    refine CxPts.mem_ptsIn.2 ?_
    exact CxPts.mem_ptsIn.1 hj
  refine ⟨j, fun v hv => ?_⟩
  obtain ⟨f, rfl⟩ := (ring_single hU2 j (gen c2 j) v).1 hv
  exact clear_denom s' hA (gen c1 i) (gen c2 j) _ hB e y hy hyW f
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ComplexPointEvalPullbackSection
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.complexPoint_eval_pullback_section :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (h : c ≫ s = s') (V : Z.Opens) (f : Γ(Z, V)) (y : CxPts s' (RingHom.id ℂ)), y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c ⁻¹ᵁ V) → CxPts.ev s' (RingHom.id ℂ) (c ⁻¹ᵁ V) ((c.app V).hom f) y = CxPts.ev s (RingHom.id ℂ) V f (UpperTheory.A.zpt c h y) := by
  intro Z Y s s' c h V f y _
  exact (GlobalTheory.Points.valR_comp y.1 c V f).symm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRegularParametersOfReducedQuotient
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.exists_regular_parameters_of_reduced_quotient :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover ℂ K x → IsReduced ((rB ℂ K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})))) → ∀ φ : rB ℂ K x {0} →ₐ[ℂ] ℂ, (∀ j : Fin d, φ ⟨_, tco_mem ℂ K x j⟩ = 0) → ∀ b : rB ℂ K x {0}, φ b = 0 → ∃ (c : rB ℂ K x {0}) (g : Fin d → rB ℂ K x {0}), φ c ≠ 0 ∧ c * b = ∑ l, g l * ⟨_, tco_mem ℂ K x l⟩ := by
  intro F K _ _ _ _ _ _ d x hc hred φ hφ b hb
  set I : Ideal (rB ℂ K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})) with hI
  have hφI : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    rw [hI, Ideal.mem_span_range_iff_exists_fun] at ha
    obtain ⟨g, rfl⟩ := ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hφ j, mul_zero]
  let ψ : (rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ I φ hφI
  have hψ : ∀ a, ψ (Ideal.Quotient.mk I a) = φ a := fun a => rfl
  let ι : ↥(rA ℂ x {0}) →+* ↥(rB ℂ K x {0}) :=
    (algebraMap (↥(rA ℂ x {0})) K).codRestrict (rB ℂ K x {0}) (fun r => isIntegral_algebraMap)
  have hι : ∀ r, (ι r : K) = algebraMap F K (r : F) := fun r => rfl
  have hbot : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
      Ideal.Quotient.mk I (ι ⟨y, hy⟩) = algebraMap ℂ _ c := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin ℂ {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i} := hy
    induction hy' using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i, hi, j, rfl⟩ := hz
      rw [Finset.mem_singleton] at hi
      subst hi
      induction j using Fin.cases with
      | zero =>
        by_cases h0 : x 0 = 0
        · refine ⟨0, ?_⟩
          have : ι ⟨x 0 / x 0, hy⟩ = 0 := Subtype.ext (by rw [hι]; simp [h0])
          rw [this, map_zero, map_zero]
        · refine ⟨1, ?_⟩
          have : ι ⟨x 0 / x 0, hy⟩ = 1 := Subtype.ext (by rw [hι]; simp [h0])
          rw [this, map_one, map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
        have : ι ⟨x j.succ / x 0, hy⟩ = ⟨_, tco_mem ℂ K x j⟩ := rfl
        rw [this]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap c =>
      refine ⟨c, ?_⟩
      have : ι ⟨algebraMap ℂ F c, hy⟩ = algebraMap ℂ _ c := by
        apply Subtype.ext
        rw [hι]
        exact (IsScalarTower.algebraMap_apply ℂ F K c).symm
      rw [this]
      exact (Ideal.Quotient.mkₐ ℂ I).commutes c
    | add y z hy1 hz1 ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy hy1
      obtain ⟨c2, h2⟩ := ihz hz1
      refine ⟨c1 + c2, ?_⟩
      have : ι ⟨y + z, hy⟩ = ι ⟨y, hy1⟩ + ι ⟨z, hz1⟩ := by
        rw [← map_add (f := _)]
        rfl
      rw [this, map_add (f := _), h1, h2, map_add (f := _)]
    | mul y z hy1 hz1 ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy hy1
      obtain ⟨c2, h2⟩ := ihz hz1
      refine ⟨c1 * c2, ?_⟩
      have : ι ⟨y * z, hy⟩ = ι ⟨y, hy1⟩ * ι ⟨z, hz1⟩ := by
        rw [← map_mul]
        rfl
      rw [this, map_mul, h1, h2, map_mul]
  let f : ↥(rA ℂ x {0}) →+* (rB ℂ K x {0} ⧸ I) := (Ideal.Quotient.mk I).comp ι
  let g : ↥(rA ℂ x {0}) →+* ℂ := ψ.toRingHom.comp f
  have hfg : (algebraMap ℂ (rB ℂ K x {0} ⧸ I)).comp g = f := by
    ext r
    obtain ⟨c, hc'⟩ := hbot r.1 r.2
    have hr : f r = algebraMap ℂ _ c := hc'
    show algebraMap ℂ _ (ψ (f r)) = f r
    rw [hr, ψ.commutes]
    rfl
  have hint : Algebra.IsIntegral ℂ (rB ℂ K x {0} ⧸ I) := by
    constructor
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hpm, hp⟩ := (a.2 : IsIntegral (↥(rA ℂ x {0})) (a : K))
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map, hfg]
    have hzero : p.eval₂ ι a = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ p ι (rB ℂ K x {0}).val.toRingHom a
      simpa using this.trans hp
    have := Polynomial.hom_eval₂ p ι (Ideal.Quotient.mk I) a
    rw [hzero, map_zero] at this
    exact this.symm
  have hft : Algebra.FiniteType ℂ (rB ℂ K x {0} ⧸ I) := by
    have := hc.3 0
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ I) (Ideal.Quotient.mkₐ_surjective ℂ I)
  have hfin : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := Algebra.IsIntegral.finite
  have hart : IsArtinianRing (rB ℂ K x {0} ⧸ I) := IsArtinianRing.of_finite ℂ _
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I b) (1 : rB ℂ K x {0} ⧸ I)
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨1 - b * y0, ?_⟩
  have hc1 : φ (1 - b * y0) ≠ 0 := by
    simp [map_sub, map_mul, hb]
  have hkill : Ideal.Quotient.mk I ((1 - b * y0) * b) = 0 := by
    have hy2 : Ideal.Quotient.mk I b ^ (n + 1) * Ideal.Quotient.mk I y0 = Ideal.Quotient.mk I b ^ n := by
      simpa [smul_eq_mul] using hy
    have h0 : Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n = 0 := by
      rw [map_sub, map_one, map_mul]
      linear_combination (-1 : rB ℂ K x {0} ⧸ I) * hy2
    apply IsReduced.eq_zero
    refine ⟨n + 1, ?_⟩
    rw [map_mul, mul_pow]
    calc Ideal.Quotient.mk I (1 - b * y0) ^ (n + 1) * Ideal.Quotient.mk I b ^ (n + 1)
        = Ideal.Quotient.mk I (1 - b * y0) ^ n * Ideal.Quotient.mk I b
          * (Ideal.Quotient.mk I (1 - b * y0) * Ideal.Quotient.mk I b ^ n) := by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_range_iff_exists_fun] at hkill
  obtain ⟨gg, hgg⟩ := hkill
  exact ⟨gg, hc1, hgg.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceDifferentialsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.etaleCorrespondence_differentials_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (l : Fin d) (hg : genericPoint Y ∈ c1 ⁻¹ᵁ U l.succ) (hg0 : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) (e : rB ℂ Y.functionField x {l.succ} →ₐ[ℂ] ℂ) (e0 : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ) (y : CxPts s' (RingHom.id ℂ)), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U l.succ) hg _ e y → UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) hg0 _ e0 y → e0 ⟨_, tco_mem ℂ Y.functionField x l⟩ ≠ 0 := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU l hg hg0 e e0 y hM hM0
  have mem : ∀ (I : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I →
      algebraMap F Y.functionField (x j / x i) ∈ rB ℂ Y.functionField x I := fun I i j hi =>
    (integralClosure (rA ℂ x I) Y.functionField).algebraMap_mem
      ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩
  obtain ⟨f0, hf0⟩ := (UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {0} ⟨0, by simp⟩ (c1 ⁻¹ᵁ U 0) (by simp) hg0 _).1
    (tco_mem ℂ Y.functionField x l)
  have hV : genericPoint Y ∈ c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ := ⟨hg0, hg⟩
  obtain ⟨fb, hfb⟩ := (UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {0, l.succ} ⟨0, by simp⟩
    (c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ) (by simp) hV _).1 (mem _ l.succ 0 (by simp))
  have hres : (Y.presheaf.germ _ (genericPoint Y) hV).hom (resG Y inf_le_left f0) =
      algebraMap F Y.functionField (x l.succ / x 0) := by
    rw [← hf0]
    exact Y.presheaf.germ_res_apply (homOfLE inf_le_left) (genericPoint Y) hV f0
  have hne := hx.pd.ne
  have hunit : resG Y inf_le_left f0 * fb = 1 := by
    apply germ_injective_of_isIntegral Y (genericPoint Y) hV
    rw [map_mul, map_one, hres, hfb, ← map_mul, div_mul_div_comm, mul_comm (x l.succ), div_self (mul_ne_zero (hne _) (hne _)), map_one]
  have hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ) :=
    CxPts.mem_ptsIn_inf.2 ⟨hM0.1, hM.1⟩
  have hval := hM0.2 f0 (hf0 ▸ tco_mem ℂ Y.functionField x l)
  have h3 : e0 ⟨_, tco_mem ℂ Y.functionField x l⟩ = CxPts.ev s' (RingHom.id ℂ) _ f0 y := by
    rw [← hval]; congr 2; exact hf0.symm
  rw [h3, ← CxPts.ev_res inf_le_left hy f0]
  exact CxPts.ev_ne_zero hy (IsUnit.of_mul_eq_one _ hunit)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFieldExtensionStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

private theorem red_of_fu {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra A B]
    [IsScalarTower ℂ A B] [Algebra.FormallyUnramified A B] (I : Ideal A) [IsReduced (A ⧸ I)]
    [Module.Finite ℂ (A ⧸ I)] [Module.Finite ℂ (B ⧸ I.map (algebraMap A B))] :
    IsReduced (B ⧸ I.map (algebraMap A B)) := by
  have h1 : Algebra.FormallyUnramified ℂ (A ⧸ I) := GlobalTheory.SepIdem.formallyUnramified_of_isReduced ℂ _
  have h2 : Algebra.FormallyUnramified A (B ⧸ I.map (algebraMap A B)) := by
    haveI : Algebra.FormallyUnramified B (B ⧸ I.map (algebraMap A B)) :=
      .of_surjective (Ideal.Quotient.mkₐ B _) Ideal.Quotient.mk_surjective
    exact .comp A B _
  have h3 : Algebra.FormallyUnramified (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    .of_restrictScalars A _ _
  haveI : IsScalarTower ℂ (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := .of_algebraMap_eq fun c => by
    have e : algebraMap ℂ (B ⧸ I.map (algebraMap A B)) c =
        algebraMap B (B ⧸ I.map (algebraMap A B)) (algebraMap A B (algebraMap ℂ A c)) := by
      rw [← IsScalarTower.algebraMap_apply ℂ A B, ← IsScalarTower.algebraMap_apply ℂ B _]
    rw [e, IsScalarTower.algebraMap_apply ℂ A (A ⧸ I)]
    rfl
  have h4 : Algebra.FormallyUnramified ℂ (B ⧸ I.map (algebraMap A B)) := .comp ℂ (A ⧸ I) _
  exact Algebra.FormallyUnramified.isReduced_of_field ℂ _

private theorem fin_of_const {R E Q : Type} [CommRing R] [CommRing E] [Algebra R E] [Module.Finite R E] [CommRing Q]
    [Algebra ℂ Q] (φ : R →+* Q) (π : E →+* Q) (hs : Function.Surjective π) (hπ : ∀ r e, π (r • e) = φ r * π e)
    (hc : ∀ r, ∃ c : ℂ, φ r = algebraMap ℂ Q c) : Module.Finite ℂ Q := by
  obtain ⟨n, s, hs'⟩ := Module.Finite.exists_fin (R := R) (M := E)
  have key : ∀ e, π e ∈ Submodule.span ℂ (Set.range (π ∘ s)) := by
    intro e
    have he : e ∈ Submodule.span R (Set.range s) := hs' ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ iha ihb => rw [map_add (f := _)]; exact Submodule.add_mem _ iha ihb
    | smul r y _ ih =>
      obtain ⟨c, hc'⟩ := hc r
      rw [hπ, hc', ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ih
  have htop : Submodule.span ℂ (Set.range (π ∘ s)) = ⊤ := by
    refine top_le_iff.1 fun a _ => ?_
    obtain ⟨b, rfl⟩ := hs a
    exact key b
  exact ⟨htop ▸ Submodule.fg_span (Set.finite_range _)⟩

private theorem rA_const {F Q : Type} [Field F] [Algebra ℂ F] [CommRing Q] [Algebra ℂ Q] {d : ℕ} (x : Fin (d + 1) → F)
    (h0 : x 0 ≠ 0) (ψ : rA ℂ x {0} →ₐ[ℂ] Q) (ht : ∀ (j : Fin d) (h : x j.succ / x 0 ∈ rA ℂ x {0}), ψ ⟨_, h⟩ = 0)
    (r : rA ℂ x {0}) : ∃ c : ℂ, ψ r = algebraMap ℂ Q c := by
  obtain ⟨r, hr⟩ := r
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    induction j using Fin.cases with
    | zero =>
      refine ⟨1, ?_⟩
      rw [map_one, ← map_one ψ]
      congr 1
      exact Subtype.ext (div_self h0)
    | succ j => exact ⟨0, by rw [map_zero]; exact ht j _⟩
  | algebraMap c => exact ⟨c, ψ.commutes c⟩
  | add a b ha hb iha ihb =>
    obtain ⟨c₁, e₁⟩ := iha
    obtain ⟨c₂, e₂⟩ := ihb
    exact ⟨c₁ + c₂, by rw [map_add (f := _), ← e₁, ← e₂]; exact map_add ψ ⟨a, ha⟩ ⟨b, hb⟩⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨c₁, e₁⟩ := iha
    obtain ⟨c₂, e₂⟩ := ihb
    exact ⟨c₁ * c₂, by rw [map_mul, ← e₁, ← e₂]; exact map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem fin_quot {K F : Type} [Field K] [Field F] [Algebra ℂ K] [Algebra ℂ F] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (hx : IsFinCover ℂ K x) :
    Module.Finite ℂ ((rB ℂ K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})))) := by
  set J := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0})) with hJ
  let φ : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0} :=
    { toFun := fun a => ⟨algebraMap F K a, (integralClosure (rA ℂ x {0}) K).algebraMap_mem a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      commutes' := fun c => Subtype.ext (IsScalarTower.algebraMap_apply ℂ F K c).symm }
  let ψ : rA ℂ x {0} →ₐ[ℂ] (rB ℂ K x {0} ⧸ J) := (Ideal.Quotient.mkₐ ℂ J).comp φ
  have hψ := rA_const x (hx.pd.ne 0) ψ fun j h =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  let ι : integralClosure (rA ℂ x {0}) K →+* rB ℂ K x {0} :=
    { toFun := fun e => ⟨e.1, e.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI hfin : Module.Finite (rA ℂ x {0}) (integralClosure (rA ℂ x {0}) K) :=
    rA_finite hx (Finset.mem_singleton_self 0)
  refine fin_of_const (R := rA ℂ x {0}) (E := integralClosure (rA ℂ x {0}) K) ψ.toRingHom
    ((Ideal.Quotient.mk J).comp ι) ?_ ?_ hψ
  · intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨⟨b.1, b.2⟩, rfl⟩
  · intro r e
    have e0 : ι (r • e) = φ r * ι e := Subtype.ext (Algebra.smul_def r (e : K))
    change Ideal.Quotient.mk J (ι (r • e)) = Ideal.Quotient.mk J (φ r) * Ideal.Quotient.mk J (ι e)
    rw [e0, map_mul]

private noncomputable def upB (K L : Type) {F : Type} [Field K] [Field L] [Field F] [Algebra ℂ K] [Algebra ℂ L] [Algebra ℂ F]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower ℂ F K] [IsScalarTower ℂ F L] [IsScalarTower ℂ K L]
    [IsScalarTower F K L] {d : ℕ} (x : Fin (d + 1) → F) : rB ℂ K x {0} →ₐ[ℂ] rB ℂ L x {0} :=
  { toFun := fun b => ⟨algebraMap K L b, by
      haveI : IsScalarTower (rA ℂ x {0}) K L := .of_algebraMap_eq fun a => by
        change algebraMap F L a = algebraMap K L (algebraMap F K a)
        exact IsScalarTower.algebraMap_apply F K L _
      have hb : IsIntegral (rA ℂ x {0}) (b : K) := b.2
      exact hb.algebraMap⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b => Subtype.ext (map_add _ _ _)
    commutes' := fun c => Subtype.ext (IsScalarTower.algebraMap_apply ℂ K L c).symm }

private theorem map_upB_span_tco (K L : Type) {F : Type} [Field K] [Field L] [Field F] [Algebra ℂ K] [Algebra ℂ L] [Algebra ℂ F]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower ℂ F K] [IsScalarTower ℂ F L] [IsScalarTower ℂ K L]
    [IsScalarTower F K L] {d : ℕ} (x : Fin (d + 1) → F) :
    (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0}))).map (upB K L x).toRingHom =
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L x j⟩ : rB ℂ L x {0})) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact Subtype.ext (IsScalarTower.algebraMap_apply F K L _).symm


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem upB_fu {d : ℕ} {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] {c : Y ⟶ Z} (h : c ≫ s = s') [IsFinite c] [Etale c]
    [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s')
    [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField]
    (g : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g))
    {F : Type} [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField]
    [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField]
    (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hU : IsAffCover s U (rB ℂ Z.functionField x)) :
    (upB Z.functionField Y.functionField x).toRingHom.FormallyUnramified := by
  have hne : ({0} : Finset (Fin (d + 1))).Nonempty := ⟨0, by simp⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = ({0} : Finset (Fin (d + 1))).inf U := ⟨_, rfl⟩
  have hV : genericPoint Z ∈ V := hVdef ▸ hU.ne {0}
  have hV' : genericPoint Y ∈ c ⁻¹ᵁ V := by
    change c (genericPoint Y) ∈ V
    rw [UpperTheory.A.generic_map c]
    exact hV
  have hVa : IsAffineOpen V := hVdef ▸ hU.affine {0} hne
  have hVa' : IsAffineOpen (c ⁻¹ᵁ V) := hVa.preimage c
  have het : (c.app V).hom.Etale := by
    have := Etale.etale_appLE (f := c) hVa hVa' le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have hfu : (c.app V).hom.FormallyUnramified := het.formallyUnramified
  have memK : ∀ y, y ∈ rB ℂ Z.functionField x {0} ↔ ∃ f : Γ(Z, V), (Z.presheaf.germ V (genericPoint Z) hV).hom f = y := by
    subst hVdef
    exact hU.ring {0} hne
  have memL : ∀ y, y ∈ rB ℂ Y.functionField x {0} ↔ ∃ f : Γ(Y, c ⁻¹ᵁ V), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom f = y :=
    UpperTheory.A.mem_rB_pull h hK hL g hU {0} hne (c ⁻¹ᵁ V) (by rw [UpperTheory.A.preimage_inf, hVdef]) hV'
  let aK : Γ(Z, V) →+* rB ℂ Z.functionField x {0} :=
    (Z.presheaf.germ V (genericPoint Z) hV).hom.codRestrict _ fun f => (memK _).2 ⟨f, rfl⟩
  let aL : Γ(Y, c ⁻¹ᵁ V) →+* rB ℂ Y.functionField x {0} :=
    (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom.codRestrict _ fun f => (memL _).2 ⟨f, rfl⟩
  have bK : Function.Bijective aK := by
    refine ⟨fun a b e => germ_injective_of_isIntegral Z _ hV (congrArg Subtype.val e), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (memK y.1).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  have bL : Function.Bijective aL := by
    refine ⟨fun a b e => germ_injective_of_isIntegral Y _ hV' (congrArg Subtype.val e), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (memL y.1).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  let eK := RingEquiv.ofBijective aK bK
  let eL := RingEquiv.ofBijective aL bL
  have hcomm : (upB Z.functionField Y.functionField x).toRingHom = (eL.toRingHom.comp (c.app V).hom).comp eK.symm.toRingHom := by
    refine RingHom.ext fun y => ?_
    obtain ⟨f, rfl⟩ := eK.surjective y
    refine Subtype.ext ?_
    have e1 : eK.symm (eK f) = f := eK.symm_apply_apply f
    change algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom f) =
      (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom (eK.symm (eK f)))
    rw [e1, g V hV hV' f]
  rw [hcomm]
  exact RingHom.FormallyUnramified.respectsIso.2 _ _ (RingHom.FormallyUnramified.respectsIso.1 _ _ hfu)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem UpperTheory.etaleCorrespondence_fieldExtension_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → IsReduced ((rB ℂ Y.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Y.functionField x j⟩ : rB ℂ Y.functionField x {0})))) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU hred
  obtain ⟨hxL, -⟩ := UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU
  have hfu := upB_fu h1 hK hL g1 x U hU
  letI alg : Algebra (rB ℂ Z.functionField x {0}) (rB ℂ Y.functionField x {0}) :=
    (upB Z.functionField Y.functionField x).toRingHom.toAlgebra
  haveI : Algebra.FormallyUnramified (rB ℂ Z.functionField x {0}) (rB ℂ Y.functionField x {0}) := hfu
  haveI : IsScalarTower ℂ (rB ℂ Z.functionField x {0}) (rB ℂ Y.functionField x {0}) :=
    .of_algebraMap_eq fun c => ((upB Z.functionField Y.functionField x).commutes c).symm
  have hI := map_upB_span_tco Z.functionField Y.functionField x
  haveI := fin_quot x hx
  have hfinL := fin_quot x hxL
  rw [← hI] at hfinL ⊢
  exact red_of_fu _
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteDimensionalHodgeCohomologyOfSmoothProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

set_option maxSynthPendingDepth 1

noncomputable section

private theorem smulHom_eq {X : Scheme.{0}} (F : X.Modules) (r : Γ(X, ⊤)) :
    GlobalTheory.smulHom F r = GroundTheory.Arith.SchemeCoh.smulHom F r := by
  ext U x
  rfl

private def cohEquiv {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules)
    (n : ℕ) : coh F n ≃ₗ[R] Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb F) n :=
  { (coh.toH F n) with
    map_smul' := fun r x => by
      have h := coh.toH_map R (smulHom F (algebraMap R Γ(X, ⊤) r)) n x
      rw [← cohOn.smul_eq_map] at h
      refine h.trans ?_
      rw [smulHom_eq]
      rfl }

private theorem finiteType_sec {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) [LocallyOfFiniteType s]
    {U : Z.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℂ (CechDR.Sec s U) := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (CechDR.secMap s U).hom.FiniteType := by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ U le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp h (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  exact h2

private theorem isCoherent_Omega {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) [LocallyOfFiniteType s] (a : ℕ) :
    GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := by
  refine ⟨inferInstance, fun U hU => ?_⟩
  haveI := finiteType_sec s hU
  have h : Module.Finite (CechDR.Sec s U) (CechDR.OmU s U a) := inferInstance
  have h' : Module.Finite (CechDR.Sec s U) Γ(Omega s a, U) := Module.Finite.equiv (toOmEquiv s a hU)
  exact h'

theorem UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s → ∀ a b : ℕ, FiniteDimensional ℂ (hodgeH s a b) := by
  intro Z _ s d _ hp a b
  obtain ⟨N, i, hi, his⟩ := hp
  haveI : IsProper (PSpace.str ℂ N) :=
    inferInstanceAs (IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase ℂ N))
  haveI : IsProper s := by rw [← his]; infer_instance
  letI : Z.Over (Spec (.of ℂ)) := ⟨s⟩
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := inferInstanceAs (IsProper s)
  have hc : GroundTheory.Arith.SchemeCoh.IsCoherent (Omega s a) := isCoherent_Omega s a
  have h := @GroundTheory.Arith.SchemeCoh.finite_H_of_isProper ℂ _ _ Z _ _ (Omega s a) hc b
  letI := algΓ s
  have h' : Module.Finite ℂ (coh (Omega s a) b) := by
    haveI : Module.Finite ℂ (Sheaf.H.{0} (GroundTheory.Arith.SchemeCoh.modulesAb (Omega s a)) b) := h
    exact Module.Finite.equiv (cohEquiv ℂ (Omega s a) b).symm
  exact h'

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HolomorphicLefschetzFiniteEtaleIntegral
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1
open GlobalTheory.PD GlobalTheory.WH

namespace UpperTheory.A

private theorem ring_one {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (i : ι) (hg : genericPoint X ∈ U i)
    (y : X.functionField) : y ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y := by
  have key : ∀ (W : X.Opens) (_ : W = ({i} : Finset ι).inf U) (hg : genericPoint X ∈ W),
      y ∈ B {i} ↔ ∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hg).hom f = y := by
    intro W hW hg
    subst hW
    exact hU.ring {i} ⟨i, Finset.mem_singleton_self i⟩ y
  exact key _ (by simp) hg

private theorem affine_one {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (i : ι) : IsAffineOpen (U i) := by
  simpa using hU.affine {i} ⟨i, Finset.mem_singleton_self i⟩

private theorem generic_one {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
    {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (i : ι) : genericPoint X ∈ U i := by
  simpa using hU.ne {i}

private theorem conj_inv {d : ℕ} (A M P : Matrix (Fin d) (Fin d) ℂ) (hP : IsUnit P.det) (hM : M = P * A * P⁻¹) (a : ℕ) :
    (1 - M).det = (1 - A).det ∧
      (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)).coeff a =
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a := by
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hdet : P.det * P⁻¹.det = 1 := by rw [← Matrix.det_mul, hPi, Matrix.det_one]
  constructor
  · have e : 1 - M = P * (1 - A) * P⁻¹ := by
      rw [hM, Matrix.mul_sub, Matrix.sub_mul, mul_one, hPi]
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, mul_comm _ P.det, hdet, one_mul]
  · set Q := P.map (Polynomial.C : ℂ →+* Polynomial ℂ) with hQ
    set Q' := P⁻¹.map (Polynomial.C : ℂ →+* Polynomial ℂ) with hQ'
    have h1 : Q * Q' = 1 := by
      rw [hQ, hQ', ← Matrix.map_mul, hPi]; simp
    have hd : Q.det * Q'.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    have e : 1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C =
        Q * (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C) * Q' := by
      rw [hM, Matrix.map_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul, mul_one, h1,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, mul_comm _ Q.det, hd, one_mul]

private theorem rB_map {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L] [Algebra F K] [Algebra F L]
    [Algebra K L] [IsScalarTower ℂ F K] [IsScalarTower ℂ F L] [IsScalarTower ℂ K L] [IsScalarTower F K L] {d : ℕ}
    (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) {b : K} (hb : b ∈ rB ℂ K x I) : algebraMap K L b ∈ rB ℂ L x I := by
  have hb' : IsIntegral (rA ℂ x I) b := hb
  have h : IsIntegral (rA ℂ x I) (algebraMap K L b) := hb'.algebraMap
  exact h

end UpperTheory.A

theorem UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_integral :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
      ∀ (Y : Scheme.{0}) [IsIntegral Y] (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
      ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
      ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
      ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
          ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  classical
  intro Z _ s d _ hP Y _ s' c1 c2 h1 h2 _ _ hf2 he2 Fx hF A hA a
  haveI := hf2
  haveI := he2
  haveI : SmoothOfRelativeDimension d s' := by
    subst h1
    have h0 : SmoothOfRelativeDimension 0 c1 := (Etale.iff_smoothOfRelativeDimension_zero c1).1 inferInstance
    have h3 : SmoothOfRelativeDimension (0 + d) (c1 ≫ s) := smoothOfRelativeDimension_comp 0 d c1 s
    rwa [Nat.zero_add] at h3
  have hfin := fun b => UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj Z s d hP a b
  refine ⟨hfin, ?_⟩
  letI iK : Algebra ℂ Z.functionField := ffAlg s
  letI iL : Algebra ℂ Y.functionField := ffAlg s'
  obtain ⟨ψ, hψ⟩ := UpperTheory.A.exists_ffMap s s' c1 h1 rfl rfl
  obtain ⟨j2, g2⟩ := UpperTheory.A.exists_ffMap s s' c2 h2 rfl rfl
  letI : Algebra Z.functionField Y.functionField := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ Z.functionField Y.functionField := .of_algebraMap_eq fun c => (ψ.commutes c).symm
  have g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)),
      (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) =
        algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g) :=
    fun V hV hV' g => (hψ V hV hV' g).symm
  obtain ⟨F, x, U, hx, hU, hred, hS⟩ := GlobalTheory.T.exists_finiteCover_projSpace_reduced_fibre_origin Z s d rfl hP (Fx.image (UpperTheory.A.zpt c1 h1))
  letI : Algebra F Y.functionField := ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  haveI : @IsScalarTower F Z.functionField Y.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : @IsScalarTower ℂ F Y.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ Z.functionField Y.functionField c, IsScalarTower.algebraMap_apply ℂ F Z.functionField c]
    rfl
  obtain ⟨hxY, hUY⟩ := UpperTheory.A.isFinCover_pull (instK := iK) (instL := iL) (c := c1) (p := s) (p' := s') (F := F) (x := x) (U := U) h1 rfl rfl g1 hx hU
  have hredY := UpperTheory.etaleCorrespondence_fieldExtension_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU hred
  have hgen : ∀ i, genericPoint Y ∈ c1 ⁻¹ᵁ U i := fun i => UpperTheory.A.generic_one hUY i
  have pa := fun i => UpperTheory.complexPoints_bijective_algHom_affineOpen Y s' rfl (c1 ⁻¹ᵁ U i) (UpperTheory.A.affine_one hUY i) (hgen i) (rB ℂ Y.functionField x {i})
    (UpperTheory.A.ring_one hUY i (hgen i))
  have fixI := fun i => UpperTheory.etaleCorrespondence_complexPoints_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU i (hgen i)
  have hin : ∀ y ∈ Fx, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) := fun y hy =>
    CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 (hS _ (Finset.mem_image_of_mem _ hy)).1)
  have hz : ∀ y ∈ Fx, ∀ e : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ, UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ e y →
      ∀ j : Fin d, e ⟨_, tco_mem ℂ Y.functionField x j⟩ = 0 := by
    intro y hy e he j
    have hg0 := UpperTheory.A.generic_one hU 0
    obtain ⟨f, hf⟩ := (UpperTheory.A.ring_one hU 0 hg0 _).1 (tco_mem ℂ Z.functionField x j)
    have hev := (hS _ (Finset.mem_image_of_mem _ hy)).2 j hg0 f hf
    have hgerm : (Y.presheaf.germ (c1 ⁻¹ᵁ U 0) (genericPoint Y) (hgen 0)).hom ((c1.app (U 0)).hom f) =
        algebraMap F Y.functionField (x j.succ / x 0) := by
      rw [g1 _ hg0, hf]; rfl
    have hm : (Y.presheaf.germ (c1 ⁻¹ᵁ U 0) (genericPoint Y) (hgen 0)).hom ((c1.app (U 0)).hom f) ∈
        rB ℂ Y.functionField x {0} := hgerm ▸ tco_mem ℂ Y.functionField x j
    have h3 := he.2 _ hm
    rw [UpperTheory.complexPoint_eval_pullback_section Z Y s s' c1 h1 _ f y he.1] at h3
    rw [hev] at h3
    rw [← h3]
    exact congrArg e (Subtype.ext hgerm.symm)
  have hex : ∀ y : {y // y ∈ Fx}, ∃ e : fib ℂ Y.functionField x, UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ e.1 y.1 := by
    rintro ⟨y, hy⟩
    obtain ⟨e, he, -⟩ := (pa 0).2 y (hin y hy)
    exact ⟨⟨e, hz y hy e he⟩, he⟩
  choose ef hef using hex
  have hefu : ∀ (y : {y // y ∈ Fx}) (e : fib ℂ Y.functionField x), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ e.1 y.1 → e = ef y :=
    fun y e he => Subtype.ext (((pa 0).2 y.1 (hin y.1 y.2)).unique he (hef y))
  have hinj : Function.Injective ef := by
    intro y y' h
    have h' : UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) (hgen 0) _ (ef y).1 y'.1 := h ▸ hef y'
    exact Subtype.ext (((pa 0).1 (ef y).1).unique (hef y) h')
  let Fx' : Finset (fib ℂ Y.functionField x) := Finset.univ.image ef
  have hFx' : ∀ e : fib ℂ Y.functionField x, e ∈ Fx' ↔ IsFix (rB ℂ Y.functionField x {0}) e.1 j2 (rB ℂ Z.functionField x {0}) := by
    intro e
    constructor
    · intro he
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 he
      exact (fixI 0 _ y.1 (hef y)).2 ((hF y.1).1 y.2)
    · intro he
      obtain ⟨y, hy, -⟩ := (pa 0).1 e.1
      have hyF : y ∈ Fx := (hF y).2 ((fixI 0 _ y hy).1 he)
      exact Finset.mem_image.2 ⟨⟨y, hyF⟩, Finset.mem_univ _, (hefu ⟨y, hyF⟩ e hy).symm⟩
  have hmg := fun (e : fib ℂ Y.functionField x) =>
    UpperTheory.exists_regular_parameters_of_reduced_quotient F Y.functionField d x hxY hredY e.1 e.2

  have hrow : ∀ e : fib ℂ Y.functionField x, ∃ M : Matrix (Fin d) (Fin d) ℂ, e ∈ Fx' → ∀ m : Fin d,
      ∃ (c : Y.functionField) (hc : c ∈ rB ℂ Y.functionField x {0}) (g : Fin d → Y.functionField)
        (hg : ∀ l, g l ∈ rB ℂ Y.functionField x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
        c * j2 (algebraMap F Z.functionField (x m.succ / x 0)) = ∑ l, g l * algebraMap F Y.functionField (x l.succ / x 0) ∧
        ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * M m l := by
    intro e
    by_cases he : e ∈ Fx'
    · have hfix := (hFx' e).1 he
      have row : ∀ m : Fin d, ∃ r : Fin d → ℂ,
          ∃ (c : Y.functionField) (hc : c ∈ rB ℂ Y.functionField x {0}) (g : Fin d → Y.functionField)
            (hg : ∀ l, g l ∈ rB ℂ Y.functionField x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
            c * j2 (algebraMap F Z.functionField (x m.succ / x 0)) = ∑ l, g l * algebraMap F Y.functionField (x l.succ / x 0) ∧
            ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * r l := by
        intro m
        obtain ⟨b0, hb0, hbv, hne, hval⟩ := hfix _ (tco_mem ℂ Z.functionField x m)
          (UpperTheory.A.rB_map x {0} (tco_mem ℂ Z.functionField x m))
        have h0 : e.1 ⟨_, UpperTheory.A.rB_map x {0} (tco_mem ℂ Z.functionField x m)⟩ = 0 := by
          exact (congrArg e.1 (Subtype.ext (IsScalarTower.algebraMap_apply F Z.functionField Y.functionField _).symm)).trans
            (e.2 m)
        rw [h0, mul_zero] at hval
        obtain ⟨c', g', hc', hcg⟩ := hmg e ⟨_, hbv⟩ hval
        have hcg' := congrArg Subtype.val hcg
        refine ⟨fun l => e.1 (g' l) / e.1 (c' * ⟨b0, hb0⟩), (c' : Y.functionField) * b0, (c' * ⟨b0, hb0⟩ : rB ℂ Y.functionField x {0}).2,
          fun l => (g' l : Y.functionField), fun l => (g' l).2, ?_, ?_, ?_⟩
        · change e.1 (c' * ⟨b0, hb0⟩) ≠ 0
          rw [map_mul]
          exact mul_ne_zero hc' hne
        · rw [mul_assoc]
          simpa using hcg'
        · intro l
          have hne' : e.1 (c' * ⟨b0, hb0⟩) ≠ 0 := by
            rw [map_mul]
            exact mul_ne_zero hc' hne
          change e.1 (g' l) = e.1 (c' * ⟨b0, hb0⟩) * (e.1 (g' l) / e.1 (c' * ⟨b0, hb0⟩))
          field_simp
      choose r hr using row
      exact ⟨Matrix.of r, fun _ m => hr m⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose A' hA' using hrow
  have hconj : ∀ y : {y // y ∈ Fx}, ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ A' (ef y) = P * A y.1 * P⁻¹ := fun y =>
    UpperTheory.etaleCorrespondence_local_parameters_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU hred y.1 ((hF y.1).1 y.2) (A y.1) (hA y.1 y.2).1
      (hgen 0) (ef y).1 (hef y) (ef y).2 (A' (ef y)) (hA' (ef y) (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hinv : ∀ y : {y // y ∈ Fx}, (1 - A' (ef y)).det = (1 - A y.1).det ∧
      (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A' (ef y)).map Polynomial.C)).coeff a =
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y.1).map Polynomial.C)).coeff a := fun y => by
    obtain ⟨P, hPu, hPe⟩ := hconj y
    exact UpperTheory.A.conj_inv (A y.1) (A' (ef y)) P hPu hPe a
  obtain ⟨E, nP, nT⟩ := GlobalTheory.T.exists_hodge_cohomology_equiv_cech_differentials
  have key := GlobalTheory.T.exists_chart_lift_of_finite_cover d a F Z.functionField Y.functionField x j2 hx hxY
    (UpperTheory.etaleCorrespondence_sections_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU) hredY
    (by
      intro i hi e hfix
      obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.2 hi
      obtain ⟨y, hy, -⟩ := (pa l.succ).1 e
      have hyF : y ∈ Fx := (hF y).2 ((fixI l.succ e y hy).1 hfix)
      exact UpperTheory.etaleCorrespondence_differentials_statement d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU l (hgen _) (hgen 0) e (ef ⟨y, hyF⟩).1 y hy
        (hef ⟨y, hyF⟩) ((ef ⟨y, hyF⟩).2 l))
    (by
      intro e hfix
      obtain ⟨y, hy, -⟩ := (pa 0).1 e
      exact hz y ((hF y).2 ((fixI 0 e y hy).1 hfix)) e hy)
    Fx' hFx'
    (by
      intro e _ b hb1 hb hb0
      let ι : rB ℂ Z.functionField x {0} →ₐ[ℂ] rB ℂ Y.functionField x {0} :=
        ((IsScalarTower.toAlgHom ℂ Z.functionField Y.functionField).comp (rB ℂ Z.functionField x {0}).val).codRestrict _
          fun v => UpperTheory.A.rB_map x {0} v.2
      obtain ⟨c, g, hc, hcg⟩ := UpperTheory.exists_regular_parameters_of_reduced_quotient F Z.functionField d x hx hred (e.1.comp ι)
        (fun j => (congrArg e.1 (Subtype.ext
          (IsScalarTower.algebraMap_apply F Z.functionField Y.functionField _).symm)).trans (e.2 j)) ⟨b, hb⟩ hb0
      refine ⟨c, (ι c).2, c.2, hc, fun l => g l, fun l => (g l).2, ?_⟩
      simpa using congrArg Subtype.val hcg)
    A' hA'
    (by
      intro e he
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 he
      rw [(hinv y).1]
      exact (hA y.1 y.2).2)
    (fun p => (E d Z s _ U (rB ℂ Z.functionField x) rfl hU a p).conj (hodgeTrace h1 a p ∘ₗ hodgePull h2 a p))
    (fun p b hb => UpperTheory.etaleCorrespondence_family_statement E nP nT d Z Y s s' hP c1 c2 h1 h2 rfl rfl g1 j2 g2 F x U hx hU hUY a p b hb)
    (fun p => haveI := hfin p; Module.Finite.equiv (E d Z s _ U (rB ℂ Z.functionField x) rfl hU a p))
  calc _ = _ := Finset.sum_congr rfl fun p _ => by
          haveI := hfin p
          rw [← LinearMap.trace_conj' (hodgeTrace h1 a p ∘ₗ hodgePull h2 a p) (E d Z s _ U (rB ℂ Z.functionField x) rfl hU a p)]
    _ = _ := key
    _ = _ := by
      rw [Finset.sum_image fun y _ y' _ h => hinj h, ← Finset.sum_coe_sort Fx]
      exact Finset.sum_congr rfl fun y _ => by rw [(hinv y).1, (hinv y).2]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothOfRelativeDimensionCompEtale
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.smoothOfRelativeDimension_comp_etale :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → ∀ (d : ℕ) [SmoothOfRelativeDimension d s], Etale c → SmoothOfRelativeDimension d s' := by
  intro Z Y s s' c h d _ hc
  subst h
  have h0 : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 hc
  have h1 : SmoothOfRelativeDimension (0 + d) (c ≫ s) := smoothOfRelativeDimension_comp 0 d c s
  rwa [Nat.zero_add] at h1
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

private theorem isAffine_of_iso {Z Z' : Scheme.{0}} (e : Z' ⟶ Z) [IsIso e] {U : Z.Opens}
    (h : IsAffineOpen (e ⁻¹ᵁ U)) : IsAffineOpen U := by
  have h' := h.preimage (inv e)
  have e' : (inv e) ⁻¹ᵁ (e ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id, Scheme.Hom.id_preimage]
  rwa [e'] at h'

private theorem isTan_of_iso {Z Z' Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (e : Z' ⟶ Z) [IsIso e]
    (d : ℕ) (c1 c2 : Y ⟶ Z') (a1 a2 : Y ⟶ Z) (e1 : c1 ≫ e = a1) (e2 : c2 ≫ e = a2)
    (h1 : c1 ≫ e ≫ s = s') (h2 : c2 ≫ e ≫ s = s') (g1 : a1 ≫ s = s') (g2 : a2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ)
    (hT : IsTan (s := e ≫ s) d c1 c2 h1 h2 y A) : IsTan (s := s) d a1 a2 g1 g2 y A := by
  subst e1 e2
  obtain ⟨U', V, hV1, hV2, t, hy, hU', hV, φ, p1, p2, p3, p4⟩ := hT
  obtain ⟨U, rfl⟩ : ∃ U : Z.Opens, U' = e ⁻¹ᵁ U := ⟨e ''ᵁ U', (e.preimage_image_eq U').symm⟩
  have hs : ∀ x : Sec (e ≫ s) (e ⁻¹ᵁ U), ∃ x' : Sec s U, appSec s (e ≫ s) e U x' = x :=
    fun x => (ConcreteCategory.bijective_of_isIso (e.app U)).2 x
  choose r hr using hs
  have hc : ∀ (c : Y ⟶ Z') (x : Sec (e ≫ s) (e ⁻¹ᵁ U)),
      appSec s s' (c ≫ e) U (r x) = appSec (e ≫ s) s' c (e ⁻¹ᵁ U) x := by
    intro c x
    conv_rhs => rw [← hr x]
    simp only [appSec, Scheme.Hom.comp_app]
    rfl
  refine ⟨U, V, hV1, hV2, fun l => r (t l), hy, isAffine_of_iso e hU', hV, φ, p1, fun l => ?_, fun j => ?_, p4⟩
  · rw [hc]; exact p2 l
  · rw [hc]; exact p3 j

theorem UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_correspondence :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
      ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
      ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
      ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
      ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
          ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  intro Z _ s d _ hP Y s' c1 c2 h1 h2 _ _ hf2 he2 F hF A hA a
  classical
  haveI := hf2
  haveI := he2
  haveI cZ : CompactSpace Z := UpperTheory.Cb.compactSpace_of_projective_and_of_finite.1 Z s hP
  haveI cY : CompactSpace Y := UpperTheory.Cb.compactSpace_of_projective_and_of_finite.2 Y Z c1 inferInstance cZ
  haveI sm : SmoothOfRelativeDimension d s' := UpperTheory.Cb.smoothOfRelativeDimension_comp_etale Z Y s s' c1 h1 d inferInstance
  obtain ⟨J, _, W, hdis, hsup, hint⟩ := UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth Y s' d
  have hcov : ∀ y : Y, ∃ i, y ∈ W i := fun y => by
    have : y ∈ iSup W := by rw [hsup]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hne : ∀ {i j : J} {y : Y}, y ∈ W i → y ∈ W j → i = j := by
    intro i j y hi hj
    by_contra hij
    have : y ∈ W i ⊓ W j := ⟨hi, hj⟩
    rw [hdis i j hij] at this
    exact this
  have hcl : ∀ m, IsClosed (W m : Set Y) := by
    intro m
    have e : ((W m : Set Y))ᶜ = ⋃ i ∈ {i | i ≠ m}, (W i : Set Y) := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      constructor
      · intro hy
        obtain ⟨i, hi⟩ := hcov y
        exact ⟨i, fun e => hy (e ▸ hi), hi⟩
      · rintro ⟨i, him, hi⟩ hy
        exact him (hne hi hy)
    rw [← isOpen_compl_iff, e]
    exact isOpen_biUnion fun i _ => (W i).isOpen
  haveI instI : ∀ m, IsClosedImmersion (W m).ι := fun m =>
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl m)
  haveI instF1 : ∀ m, IsFinite ((W m).ι ≫ c1) := fun m => inferInstance
  haveI instF2 : ∀ m, IsFinite ((W m).ι ≫ c2) := fun m => inferInstance
  haveI instE1 : ∀ m, Etale ((W m).ι ≫ c1) := fun m => inferInstance
  haveI instE2 : ∀ m, Etale ((W m).ι ≫ c2) := fun m => inferInstance
  have hm1 : ∀ m, ((W m).ι ≫ c1) ≫ s = (W m).ι ≫ s' := fun m => by rw [Category.assoc, h1]
  have hm2 : ∀ m, ((W m).ι ≫ c2) ≫ s = (W m).ι ≫ s' := fun m => by rw [Category.assoc, h2]
  let φ : ∀ m, CxPts ((W m).ι ≫ s') (RingHom.id ℂ) → CxPts s' (RingHom.id ℂ) := fun m y' =>
    ⟨y'.1 ≫ (W m).ι, by simpa [Category.assoc] using y'.2⟩
  have φinj : ∀ m, Function.Injective (φ m) := by
    intro m y y' e
    have e' : y.1 ≫ (W m).ι = y'.1 ≫ (W m).ι := congrArg Subtype.val e
    exact Subtype.ext ((cancel_mono _).1 e')
  let Fm : ∀ m, Finset (CxPts ((W m).ι ≫ s') (RingHom.id ℂ)) := fun m =>
    F.preimage (φ m) (φinj m).injOn
  have hFm : ∀ m y', y' ∈ Fm m ↔ y'.1 ≫ (W m).ι ≫ c1 = y'.1 ≫ (W m).ι ≫ c2 := by
    intro m y'
    rw [Finset.mem_preimage, hF]
    simp only [φ, Category.assoc]
  have hAm : ∀ m, ∀ y' ∈ Fm m, GlobalTheory.W1.IsTan d ((W m).ι ≫ c1) ((W m).ι ≫ c2) (hm1 m) (hm2 m) y' (A (φ m y')) ∧
      (1 - A (φ m y')).det ≠ 0 := by
    intro m y' hy'
    obtain ⟨hT, hD⟩ := hA (φ m y') (Finset.mem_preimage.1 hy')
    refine ⟨?_, hD⟩
    haveI : IsIso (⊤ : Z.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e1 : (((W m).ι ≫ c1) ≫ inv (⊤ : Z.Opens).ι) ≫ (⊤ : Z.Opens).ι = (W m).ι ≫ c1 := by simp
    have e2 : (((W m).ι ≫ c2) ≫ inv (⊤ : Z.Opens).ι) ≫ (⊤ : Z.Opens).ι = (W m).ι ≫ c2 := by simp
    have hT' := (UpperTheory.Cb.isTangentMatrix_iff_restrict_open Z Y s s' d c1 c2 h1 h2 ⊤ (W m) _ _ e1 e2 (φ m y') y' rfl (A (φ m y'))).1 hT
    exact isTan_of_iso (⊤ : Z.Opens).ι d _ _ _ _ e1 e2 _ _ _ _ y' _ hT'
  let g : CxPts s' (RingHom.id ℂ) → ℂ := fun y =>
    (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det
  have key : ∀ m, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
      ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace (hm1 m) a b ∘ₗ hodgePull (hm2 m) a b) =
        ∑ y ∈ Fm m, g (φ m y) := fun m => by
    haveI := hint m
    exact UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_integral Z s d hP (W m).toScheme ((W m).ι ≫ s') ((W m).ι ≫ c1) ((W m).ι ≫ c2) (hm1 m) (hm2 m)
      inferInstance inferInstance (Fm m) (hFm m) (fun y' => A (φ m y')) (hAm m) a
  have hFD : ∀ b, FiniteDimensional ℂ (hodgeH s a b) := by
    rcases isEmpty_or_nonempty J with hJ | ⟨⟨m⟩⟩
    · exact fun b => UpperTheory.finiteDimensional_hodgeCohomology_of_smooth_proj Z s d hP a b
    · exact (key m).1
  refine ⟨hFD, ?_⟩
  have hu : ∀ b, hodgeTrace h1 a b ∘ₗ hodgePull h2 a b =
      ∑ m, hodgeTrace (hm1 m) a b ∘ₗ hodgePull (hm2 m) a b := by
    intro b
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, UpperTheory.Cb.hodgeTrace_eq_sum_clopen_decomposition Z Y s s' c1 h1 J W hdis hsup instF1 instE1 a b (hodgePull h2 a b x),
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.comp_apply, hodgePull_comp h2 rfl (hm2 m) a b x]
  have hsum : ∑ m, ∑ y ∈ Fm m, g (φ m y) = ∑ y ∈ F, g y := by
    have hP9 : ∀ y : CxPts s' (RingHom.id ℂ), ∃ m, ∃ y', φ m y' = y := fun y => by
      obtain ⟨m, ⟨y', hy', -⟩, -⟩ := UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover Y s' J W hdis hsup y
      exact ⟨m, y', Subtype.ext hy'⟩
    have hU9 : ∀ {m m' y' y''}, φ m y' = φ m' y'' → m = m' := by
      intro m m' y' y'' e
      obtain ⟨m0, -, hu0⟩ := UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover Y s' J W hdis hsup (φ m y')
      have a1 := hu0 m ⟨y', rfl, fun z hz => φinj m (Subtype.ext hz)⟩
      have a2 := hu0 m' ⟨y'', (congrArg Subtype.val e).symm, fun z hz => φinj m' (Subtype.ext (hz.trans (congrArg Subtype.val e)))⟩
      exact a1.trans a2.symm
    choose μ y0 hy0 using hP9
    rw [← Finset.sum_fiberwise F μ g]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_nbij (φ m) ?_ (φinj m).injOn ?_ (fun _ _ => rfl)
    · intro y' hy'
      refine Finset.mem_filter.2 ⟨Finset.mem_preimage.1 hy', ?_⟩
      exact hU9 (hy0 (φ m y'))
    · intro y hy
      obtain ⟨hyF, rfl⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
      exact ⟨y0 y, Finset.mem_coe.2 (Finset.mem_preimage.2 (by rw [hy0]; exact hyF)), hy0 y⟩
  change _ = ∑ y ∈ F, g y
  rw [← hsum, ← Finset.sum_congr rfl (fun m _ => (key m).2), Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu b, map_sum, Finset.mul_sum]

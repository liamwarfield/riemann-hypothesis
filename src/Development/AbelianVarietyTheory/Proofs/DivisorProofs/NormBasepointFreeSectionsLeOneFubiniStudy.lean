module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueVectorFieldOfGlobalOneFormValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChartStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudy
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudy
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem canNorms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  intro k _ X _ p D _ P e x hx n u hn hu
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : 2 * n ≠ 0 := by omega
  have hup := GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u (e : ℤ) 0
  have hnn : ∀ (Q : Pair p) σ (y : CxPts p σ) f, 0 ≤ Q.nu e 0 σ y f := fun Q σ y f => by
    rw [← norm_val]; exact norm_nonneg _
  have hS : ∀ σ (y : CxPts p σ), 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y
    obtain ⟨l, hl⟩ := hx.cover (under y)
    have h := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2
    exact lt_of_lt_of_le (pow_pos h _) (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l))
  have key : ∀ σ (y : CxPts p σ) f, (upperParabolic P u).nu e 0 σ y f ^ (2 * n) =
      P.nu e 0 σ y f ^ (2 * n) / ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y f
    rw [(hup.2.2 σ y f).2, mul_pow, ← Real.exp_nat_mul, hu σ y]
    have : ((2 * n : ℕ) : ℝ) * (-(((e : ℤ) : ℝ) * (((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)))) / 2)
        = -Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)) := by
      push_cast; field_simp
    rw [this, Real.exp_neg, Real.exp_log (hS σ y), div_eq_mul_inv]
  refine ⟨fun l σ y => ?_, fun σ y => ?_, ⟨hx.pos, fun l => hup.1 ▸ hx.mem l, fun z => ?_⟩, ⟨?_, fun l => ?_, fun z => ?_⟩, ?_⟩
  · rw [← pow_le_pow_iff_left₀ (hnn _ σ y _) zero_le_one hn0, one_pow, key, div_le_one (hS σ y)]
    exact Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l)
  · obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => P.nu e 0 σ y (x l)) Finset.univ_nonempty
    refine ⟨l, ?_⟩
    rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (hnn _ σ y _) hn0, key, ← Real.exp_nat_mul]
    have e1 : ((2 * n : ℕ) : ℝ) * -(Real.log (D + 1) / (2 * n)) = -Real.log (D + 1) := by
      push_cast; field_simp
    have hD : (0 : ℝ) < D + 1 := by positivity
    rw [e1, Real.exp_neg, Real.exp_log hD, inv_eq_one_div, div_le_div_iff₀ hD (hS σ y), one_mul]
    calc ∑ i, P.nu e 0 σ y (x i) ^ (2 * n) ≤ ∑ _i : Fin (D + 1), P.nu e 0 σ y (x l) ^ (2 * n) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hnn P σ y _) (hl i (Finset.mem_univ i)) _
      _ = P.nu e 0 σ y (x l) ^ (2 * n) * (D + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  · obtain ⟨l, hl⟩ := hx.cover z
    exact ⟨l, (hup.2.1 (x l)).symm ▸ hl⟩
  · exact Nat.mul_pos hx.pos hn
  · have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).1
    convert h using 2 <;> push_cast <;> ring
  · obtain ⟨l, hl⟩ := hx.cover z
    refine ⟨l, ?_⟩
    have h := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.1 n hn
    have e2 : ((e * n : ℕ) : ℤ) = (n : ℤ) * (e : ℤ) := by push_cast; ring
    have e3 : (0 : ℤ) = (n : ℤ) * 0 := by ring
    show z ∈ NV P ((e * n : ℕ) : ℤ) 0 (x l ^ n)
    rw [e2, e3, h]; exact hl
  · intro σ y
    have hp : ∀ l, P.nu ((e * n : ℕ) : ℤ) 0 σ y (x l ^ n) = P.nu e 0 σ y (x l) ^ n := fun l => by
      have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).2 σ y
      convert h using 2 <;> push_cast <;> ring
    rw [hu σ y]
    simp only [hp, ← pow_mul]
    push_cast
    ring_nf

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  first | exact @GlobalTheory.HSAmp.canNorms | exact GlobalTheory.HSAmp.canNorms | (intros; apply GlobalTheory.HSAmp.canNorms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentGradedFamilyNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentGradedFamilyNonzero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.DescGraded

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _

theorem theta_c₀ (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    have e1 : spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) = spMap (Desc.cst (σ.C x).G.hom) ≫ spMap (σ.ρ x) := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc, (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem c₀_mem_W (σ : Setup) (x : Sp σ.R) (r : σ.R) : σ.c₀ r ∈ σ.W x := fun z _ => by
  have := RingHom.congr_fun (theta_c₀ σ x) r
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact regAt_cst _ _ _

theorem W_mul (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a * b ∈ σ.W x := fun z hz => by
  rw [map_mul]; exact (ha z hz).mul (hb z hz)

theorem W_add (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a + b ∈ σ.W x := fun z hz => by
  rw [map_add (f := _)]; exact (ha z hz).add (hb z hz)

theorem sec_mul_left {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) {a b : X.functionField}
    (ha : ∀ x, RegAt x a) (hb : b ∈ Sec D k) : a * b ∈ Sec D k := fun x => by
  obtain ⟨g, hg, h⟩ := hb x
  exact ⟨g, hg, _root_.mul_assoc a b g ▸ (ha x).mul h⟩

theorem finite_height_one {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).preimage
    (f := fun p : PrimeSpectrum R => p.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro p ⟨hp, hfp⟩
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hfp) ?_
  rw [hp]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf)

theorem c₀_f_ne_zero (σ : Setup) : σ.c₀ σ.f ≠ 0 := by
  have e : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    have e2 : spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) =
        spMap (Desc.cst σ.A.hom) ≫ Desc.awayMap σ.f := by
      rw [← Spec.map_comp]; rfl
    have e : spMap σ.c₀ = spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) := by
      rw [e2, Setup.c₀, spMap_cst, spMap_cst, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e, RingHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit σ.f).map _).ne_zero

theorem gradedFam_and_ne_zero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  intro σ
  refine ⟨⟨⟨fun x => ?_, fun x => ?_⟩, fun k => ⟨fun x => ?_, fun x => ?_⟩,
    fun k a ha b hb => ⟨fun x => (ha.1 x).add (hb.1 x), fun x => W_add σ x (ha.2 x) (hb.2 x)⟩,
    fun k r a ha => ⟨sec_mul_left _ _ (fun x => regAt_cst _ x r) ha.1, fun x => W_mul σ x (c₀_mem_W σ x r) (ha.2 x)⟩,
    fun k l a ha b hb => ⟨fun x => ?_, fun x => W_mul σ x (ha.2 x) (hb.2 x)⟩⟩, ?_⟩
  · rw [zero_nsmul]
    exact ⟨1, CartierDiv.isEqn_zero x, by simpa using (unitAt_one x).regAt⟩
  · simpa using c₀_mem_W σ x 1
  · exact (CartierDiv.vanishesAt_zero _ x).regularAt
  · simpa using c₀_mem_W σ x 0
  · rw [add_nsmul]
    exact (ha.1 x).mul (hb.1 x)
  · obtain ⟨k, hk, u, hu, U, -, hU, hx⟩ := σ.amp (genericPoint _)
    have hu0 : u ≠ 0 := by
      have : genericPoint σ.A.left ∈ locus σ.D k u := hU ▸ hx
      exact CartierDiv.GeneratesAt.ne_zero this
    choose m hm using fun x => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ x u
    obtain ⟨M, hM⟩ := ((finite_height_one σ.hf).image m).bddAbove
    refine ⟨k, hk, σ.c₀ σ.f ^ M * u, ⟨?_, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ _).2 fun p hp hfp => ?_⟩,
      mul_ne_zero (pow_ne_zero _ (c₀_f_ne_zero σ)) hu0⟩
    · rw [← map_pow]
      exact sec_mul_left _ _ (fun x => regAt_cst _ x _) hu
    · have hle : m p ≤ M := hM ⟨p, ⟨hp, hfp⟩, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [pow_add, _root_.mul_assoc, ← map_pow]
      exact W_mul σ p (c₀_mem_W σ p _) (hm p)

end GlobalTheory.DescGraded
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentGradedFamilyNonzeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDescent_gradedFamily_nonzero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  first | exact @GlobalTheory.DescGraded.gradedFam_and_ne_zero | exact GlobalTheory.DescGraded.gradedFam_and_ne_zero | (intros; apply GlobalTheory.DescGraded.gradedFam_and_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.LiftWitness

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem spMap_id (L : Type) [CommRing L] : spMap (RingHom.id L) = 𝟙 _ := by
  simp [spMap]

theorem laurentProd_bijective (B C : Type) [CommRing B] [CommRing C] : Function.Bijective
    ((laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.coeff_injective
    ext n
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h1
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h2
  · rintro ⟨f, g⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk rfl f.coeff g.coeff), ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor <;> (apply AddMonoidAlgebra.coeff_injective; ext n; simp [laurentMap_coeff])


open GlobalTheory.EtC.GmPhiNat in
theorem eq_zero_of_pull_laurent_fst_snd (q : ℕ) (B C : Type) [CommRing B] [CommRing C] (n i : ℤ)
    (z : Ht q (sp (LaurentPolynomial (B × C))) n i)
    (h1 : pull _ (spMap (laurentMap (RingHom.fst B C))) _ n z = 0)
    (h2 : pull _ (spMap (laurentMap (RingHom.snd B C))) _ n z = 0) : z = 0 := by
  let e := (laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))
  let E := RingEquiv.ofBijective e (laurentProd_bijective B C)
  have hinv : E.symm.toRingHom.comp e = RingHom.id _ :=
    RingHom.ext fun x => E.symm_apply_apply x
  have hw : pull _ (spMap e) _ n z = 0 := by
    apply (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q (LaurentPolynomial B) (LaurentPolynomial C) n i).1
    simp only [← pull_spMap_comp, map_zero, e, RingHom.fst_comp_prod, RingHom.snd_comp_prod]
    exact Prod.ext h1 h2
  have := pull_spMap_comp q e E.symm.toRingHom n i z
  rw [hinv, spMap_id, pull_id, hw, map_zero] at this
  exact this

theorem surj_prod (q : ℕ) [NeZero q] (B C : Type) [CommRing B] [CommRing C] (hq : IsUnit (q : B × C)) (i : ℤ)
    (hB : Function.Surjective (gmPhi q B i)) (hC : Function.Surjective (gmPhi q C i)) :
    Function.Surjective (gmPhi q (B × C) i) := by
  intro y
  obtain ⟨b, hb⟩ := hB (pull _ (spMap (laurentMap (RingHom.fst B C))) _ 1 y)
  obtain ⟨c, hc⟩ := hC (pull _ (spMap (laurentMap (RingHom.snd B C))) _ 1 y)
  obtain ⟨a, ha⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q B C 0 (i - 1)).2 (b, c)
  simp only [Prod.mk.injEq] at ha
  refine ⟨a, (sub_eq_zero.mp ?_).symm⟩
  apply eq_zero_of_pull_laurent_fst_snd q B C 1 i
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.1, hb, sub_self]
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.2, hc, sub_self]

theorem exists_factor (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (p : Ideal A) [p.IsPrime] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  let D := A ⧸ p
  let Ω := AlgebraicClosure (FractionRing D)
  let T := integralClosure D Ω
  letI : Algebra A T := ((algebraMap D T).comp (Ideal.Quotient.mk p)).toAlgebra
  have hint : Algebra.IsIntegral A T := by
    have h1 : (Ideal.Quotient.mk p).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : (algebraMap D T).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := D) x
    exact ⟨fun x => RingHom.IsIntegral.trans _ _ h1 h2 x⟩
  have hloc : IsLocalRing T := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A T
  have hqT : IsUnit (q : T) := by simpa using hq.map (algebraMap A T)
  refine ⟨T, inferInstance, inferInstance, hint, fun a ha => ?_,
    (GlobalTheory.T.units_cohomology_bijective q T (GlobalTheory.aic_integralClosure_algebraicClosure D) hqT i).2⟩
  have hinjΩ : Function.Injective (algebraMap D Ω) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) Ω]
    exact (algebraMap (FractionRing D) Ω).injective.comp (IsFractionRing.injective D (FractionRing D))
  have hinj : Function.Injective (algebraMap D T) := by
    intro x y h
    exact hinjΩ (congrArg Subtype.val h)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact ha

theorem exists_witness (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (S : Finset (Ideal A)) (hS : ∀ p ∈ S, p.IsPrime) (hne : S.Nonempty) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → ∀ p ∈ S, a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton p =>
    have := hS p (Finset.mem_singleton_self p)
    obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_factor q A hq i p
    exact ⟨B, inferInstance, inferInstance, hint, fun a ha r hr => by
      rw [Finset.mem_singleton] at hr; subst hr; exact hker a ha, hsurj⟩
  | cons p S hp hSne ih =>
    have := hS p (Finset.mem_cons_self p S)
    obtain ⟨B, _, _, hintB, hkerB, hsurjB⟩ := ih fun r hr => hS r (Finset.mem_cons_of_mem hr)
    obtain ⟨C, _, _, hintC, hkerC, hsurjC⟩ := exists_factor q A hq i p
    have hqBC : IsUnit (q : B × C) := by simpa using hq.map (algebraMap A (B × C))
    refine ⟨B × C, inferInstance, inferInstance, inferInstance, fun a ha r hr => ?_,
      surj_prod q B C hqBC i hsurjB hsurjC⟩
    rw [Prod.algebraMap_apply, Prod.mk_eq_zero] at ha
    rcases Finset.mem_cons.1 hr with rfl | hr
    · exact hkerC a ha.2
    · exact hkerB a ha.1 r hr

theorem lift_witness : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
      ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  intro q _ A _ _ hSH hq i x
  obtain ⟨hH, -⟩ := hSH
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
    exact ⟨p, hfin.mem_toFinset.2 hp⟩
  obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_witness q A hq i hfin.toFinset
    (fun p hp => (hfin.mem_toFinset.1 hp).1.1) hne
  obtain ⟨a', ha'⟩ := hsurj (pull _ (spMap (laurentMap (algebraMap A B))) _ 1 x)
  refine ⟨B, inferInstance, inferInstance, hint, fun a ha => ?_, a', ha'.symm⟩
  rw [RingHom.mem_ker] at ha
  have : a ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 fun p hp => hker a ha p (hfin.mem_toFinset.2 hp)
  exact this
end GlobalTheory.EtC.LiftWitness
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegralStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_from_integral : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧ ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  first | (exact @GlobalTheory.EtC.LiftWitness.lift_witness) | (exact GlobalTheory.EtC.LiftWitness.lift_witness) | (intros; apply GlobalTheory.EtC.LiftWitness.lift_witness  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangular
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem det_upU {K : Type} [Field K] {s : ℕ} (y : Low s → K) : (upU y).det = 1 := by
  have hb : (upU y).BlockTriangular id := fun a b (hab : b < a) => by
    simp only [upU, Matrix.of_apply, dif_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => by simp [upU]

theorem pts_of {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hR : Refines E E' φ f) {A : Mat m X.Fn}
    {u : Cell m → Y.Fn} (hg : InCell E E' φ f A u (genericPoint Y.X)) {K : Type} [Field K] (x : Sp K ⟶ X.X)
    (hA : A ∈ E.S (x (IsLocalRing.closedPoint K))) (y₀ : Cell m → K)
    (hbears : ∀ p : Sp K ⟶ Y.X, A ∈ E.S (f (p (IsLocalRing.closedPoint K))) →
      (Bears E' φ A (upM y₀) p ↔ ∃ u' : Cell m → Y.Fn, upM u' * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧
        ∀ j, (ratOf Y).val p (u' j) = y₀ j))
    (huniq : ∀ (s : ℕ) (y y' : Low s → Y.Fn) (b : Matrix (Fin s) (Fin s) Y.Fn), (∀ i j, i < j → b i j = 0) →
      upU y = b * upU y' → y = y') :
    ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧
      ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  have hPar : Par 0 ⊤ (upM y₀) := fun τ =>
    ⟨fun _ _ => trivial, by simp [upM, det_upU], trivial, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨p, ⟨hpf, hpB⟩, huq⟩ := hR.lifts K x A hA (upM y₀) hPar
  have hfz : f (p (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
    rw [← hpf]; rfl
  have hA' : A ∈ E.S (f (p (IsLocalRing.closedPoint K))) := hfz ▸ hA
  obtain ⟨u', hu'S, hu'v⟩ := (hbears p hA').1 hpB
  have huu : u' = u := by
    have h1 := Fr.mem_genericPoint hu'S
    have hdA : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
      have := Mat.det_map A φ.toRingHom τ
      rw [show A.map φ.toRingHom = A.map φ from rfl] at this
      rw [this]; exact (map_ne_zero _).2 (Fr.det_ne hg.1 τ)
    have hdu : ∀ τ, (upM u τ).det ≠ 0 := fun τ => by simp [upM, det_upU]
    have hP := (Fr.mem_iff hg.2).1 h1
    rw [Mat.mul_inv_rev, ← mul_assoc, mul_assoc (upM u'), Mat.mul_inv hdA, mul_one] at hP
    have he : upM u' = (upM u' * (upM u)⁻¹) * upM u := by rw [mul_assoc, Mat.inv_mul hdu, mul_one]
    funext ⟨τ, s⟩
    have := huniq (m τ) (fun s => u' ⟨τ, s⟩) (fun s => u ⟨τ, s⟩) ((upM u' * (upM u)⁻¹) τ)
      (fun i j hij => (hP τ).2.2.2 i j i.2 hij) (congrFun he τ)
    exact congrFun this s
  subst huu
  refine ⟨p, ⟨hpf, ⟨hA', hu'S⟩, hu'v⟩, fun p' ⟨hp'f, ⟨h1, h2⟩, hv⟩ => huq p' ⟨hp'f, (hbears p' h1).2 ⟨u', h2, hv⟩⟩⟩

theorem cell_points_existsUnique : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hR A u hg K _ x hA y₀
  exact pts_of hR hg x hA y₀ (fun p hp => GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A K p hp y₀)
    (fun s y y' b hb h => upU_unique_of_lower Y.Fn s y y' b hb h)

end GlobalTheory.FlagCell2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangularStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cell_points_existsUnique_unitriangular : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  first | exact @GlobalTheory.FlagCell2.cell_points_existsUnique | exact GlobalTheory.FlagCell2.cell_points_existsUnique | (intros; apply GlobalTheory.FlagCell2.cell_points_existsUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProd
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pt_bsL_fb {n d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) : pt ε (bsL ε w) (fb ε w) = w := by
  ext a
  obtain ⟨x, rfl⟩ := ε.symm.surjective a
  rcases x with b | j <;> simp [pt, bsL_apply, fb]

theorem cellMap_image_eq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε
  have hO := GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u
  have hP := GlobalTheory.T.flag_cell_points_existsUnique_unitriangular F X Y ι m E E' φ f hR A u hgen
  have hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j,
      ratVal (u j) y = (ratOf Y).val y.1 (u j) :=
    fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))
  refine ⟨?_, ?_, ?_⟩
  · let W : Y.X.Opens := ⟨{y | InCell E E' φ f A u y}, hO.1⟩
    have e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source := by
      ext y
      simp only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]
      rfl
    rw [e]
    exact (isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))
  · intro y hy y' hy' h
    have h1 := congrArg (bsL ε) h
    have h2 := congrArg (fb ε) h
    simp only [cellMap, bsL_pt, fb_pt] at h1 h2
    have hx : ptMap σ f hf y = ptMap σ f hf y' := c.e.injOn hy.2 hy'.2 h1
    have hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ)) := hy.1.1
    apply Subtype.ext
    exact (hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique
      ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩
      ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩
  · intro S hS hA
    ext w
    constructor
    · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
      exact ⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩
    · rintro ⟨x, hxS, hxw⟩
      obtain ⟨p, ⟨hpf, hpc, hpv⟩, -⟩ := hP ℂ x.1 (hA x hxS) (fb ε w)
      have hps : p ≫ Y.str = spMap σ := by rw [← hf, ← Category.assoc, hpf, x.2]
      let y : CxPts Y.str σ := ⟨p, hps⟩
      have hyx : ptMap σ f hf y = x := Subtype.ext hpf
      refine ⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩
      have hv : (fun j => ratVal (u j) y) = fb ε w := funext fun j => (hval y hpc j).trans (hpv j)
      simp only [cellMap, hyx, hxw, hv]
      exact pt_bsL_fb ε w

end GlobalTheory.FlagCell2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProdStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_coords_bijective_onto_chart_prod : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  first | exact @GlobalTheory.FlagCell2.cellMap_image_eq | exact GlobalTheory.FlagCell2.cellMap_image_eq | (intros; apply GlobalTheory.FlagCell2.cellMap_image_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianSche
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueVectorFieldOfGlobalOneFormValuesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : AffOp A.left) (l : GlobForm A.hom →ₗ[R] Sec A.hom U.unop.1), ∃! δ : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] Sec A.hom U.unop.1, ∀ w : GlobForm A.hom, δ (w.1 U) = l w := by
  first | exact @GlobalTheory.ParPt.exists_unique_of_globForm | exact GlobalTheory.ParPt.exists_unique_of_globForm | (intros; apply GlobalTheory.ParPt.exists_unique_of_globForm <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalForms
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
namespace GlobalTheory.ParForm

theorem isBaseChange_of_dual {R B M N : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite B N] [Module.Projective B N] (f : M →ₗ[R] N)
    (h : ∀ l : M →ₗ[R] B, ∃! δ : N →ₗ[B] B, ∀ w, δ (f w) = l w) : IsBaseChange B f := by
  let F : B ⊗[R] M →ₗ[B] N := f.liftBaseChange B
  have hF : ∀ w, F (1 ⊗ₜ w) = f w := fun w ↦ by simp [F]
  have hd : Function.Bijective F.dualMap := by
    rw [Function.bijective_iff_existsUnique]
    intro φ
    obtain ⟨δ, h1, h2⟩ := h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))
    refine ⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩
    · refine (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)
      simpa [hF] using h1 w
    · rw [← hF]
      exact LinearMap.congr_fun e (1 ⊗ₜ w)
  have hdd : Function.Bijective F.dualMap.dualMap :=
    (LinearEquiv.ofBijective _ hd).dualMap.bijective
  have hb : Function.Bijective F := by
    have e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M)) :=
      funext fun x ↦ rfl
    rw [← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]
    exact hdd.comp (Module.bijective_dual_eval B _)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF

theorem smooth_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

theorem par : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  intro H H' R _ A _ g hA hg U
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := smooth_sec A.hom hs U.unop
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := H' R A g hA hg
  exact isBaseChange_of_dual _ (GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values H H' R A g hA hg U)

end GlobalTheory.ParForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalFormsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_differentials_from_globalForms : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  first | exact @GlobalTheory.ParForm.par | exact GlobalTheory.ParForm.par | (intros; apply GlobalTheory.ParForm.par <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheria
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheria
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

open Opposite TopologicalSpace

theorem const_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → Const A.hom := by
  intro R _ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  have hbij := ((GlobalTheory.ProperFunctions.functions_of_isProper).2.2 R A.left A.hom).1
  intro g hg
  have hc : ∀ (U V : A.left.affineOpens) (h : V.1 ≤ U.1),
      A.left.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, -⟩ := A.left.sheaf.existsUnique_gluing' (fun U : A.left.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top A.left).ge (fun U ↦ g (op U)) (by
      intro U V
      refine A.left.sheaf.eq_of_locally_eq' (fun W : {W : A.left.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens A.left} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(A.left, a)),
            A.left.presheaf.map f'.op (A.left.presheaf.map f.op x) = A.left.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))
  obtain ⟨r, hr⟩ := hbij.2 t
  refine ⟨r, fun U ↦ ?_⟩
  rw [← ht U.unop, ← hr]
  rfl

end GlobalTheory.LiftSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheriaStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → Const A.hom := by
  first | exact @GlobalTheory.LiftSys.const_of_isAbelianScheme | exact GlobalTheory.LiftSys.const_of_isAbelianScheme | (intros; apply GlobalTheory.LiftSys.const_of_isAbelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianSche
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem good_of_isAbelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Good A.hom := by
  intro HC HH R _ _ A _ g hA hg
  have hs : Smooth A.hom := hA.smooth
  have hp : IsProper A.hom := hA.proper
  have hsep : IsSeparated A.hom := inferInstance
  have hqc : QuasiCompact A.hom := inferInstance
  have bij := HC.bijective_cechDeRhamComparison_degreeOne A.hom hs hsep hqc
  obtain ⟨-, -, ⟨-, hproj, -⟩, -, ⟨hcl, hinj, -⟩, -⟩ := HH R A g hA hg
  have key : ∀ f : Form A.hom, cmp1 A.hom (Form.cl A.hom f) = clForm A.hom (cmpForm A.hom f) :=
    comparison_formClass A.hom
  refine ⟨GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian R A hA, GlobalTheory.T.abelianScheme_differentials_from_globalForms HC HH R A g hA hg, hproj, fun w ↦ ?_, fun f ↦ ?_⟩
  · have hw : w ∈ ClosedForm A.hom := hcl ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := bij.2 (clForm A.hom ⟨w, hw⟩)
    have h1 : clForm A.hom ⟨w, hw⟩ ∈ CechHodgeFiltration A.hom := (cechHodgeFiltration_eq_range A.hom).symm ▸ ⟨_, rfl⟩
    have h2 : c ∈ F1 A.hom := by
      change toH1O A.hom c = 0
      apply cmpO_injective R A.left A.hom
      rw [← structureSheaf_comparison_comm, hc, map_zero]
      exact h1
    rw [hodgeFiltration_eq_range] at h2
    obtain ⟨f, rfl⟩ := h2
    refine ⟨f, ?_⟩
    have := hinj ((key f).symm.trans hc)
    exact congrArg Subtype.val this
  · constructor
    · intro h
      apply hinj
      rw [← key, h, map_zero, map_zero]
    · intro h
      apply bij.1
      rw [key, h, map_zero, map_zero]

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianScheStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Good A.hom := by
  first | exact @GlobalTheory.LiftSys.good_of_isAbelianScheme | exact GlobalTheory.LiftSys.good_of_isAbelianScheme | (intros; apply GlobalTheory.LiftSys.good_of_isAbelianScheme <;> assumption)
end
end

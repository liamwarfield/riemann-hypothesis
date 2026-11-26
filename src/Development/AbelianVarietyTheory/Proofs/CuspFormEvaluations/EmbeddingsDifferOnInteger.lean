module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartFree

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped ComplexConjugate
open Matrix

theorem embeddings_differ_on_integer {E : Type} [Field E] [NumberField E] (τ τ' : E →+* ℂ) (h : τ ≠ τ') :
    ∃ a : 𝓞 E, τ (a : E) ≠ τ' (a : E) := by
  by_contra hall
  push Not at hall
  apply h
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  simp only [map_div₀]
  rw [show (algebraMap (𝓞 E) E a) = (a : E) from rfl, show (algebraMap (𝓞 E) E b) = (b : E) from rfl,
    hall a, hall b]

theorem balanced_pairs_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ} (A : 𝓞 E → Matrix (Fin d) (Fin d) S)
    (uvec : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin d), ∑ j, A a i j * uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * uvec ℓ i)
    (M : Fin d → Fin d → S) (hbal : ∀ a, (A a).transpose * Matrix.of M = Matrix.of M * A (H.bar a))
    (ℓ ℓ' : Lt1 Dw) (hne : ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j ≠ 0) :
    ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  by_contra hc
  have hσ : ℓ.1 ≠ ComplexEmbedding.conjugate ℓ'.1 := by
    intro h
    apply hc
    rw [h]
    show ℓ'.1 = star (star ℓ'.1)
    rw [star_star]
  obtain ⟨a, ha⟩ := embeddings_differ_on_integer _ _ hσ
  have hmv : ∀ (b : 𝓞 E) (ℓ₀ : Lt1 Dw), A b *ᵥ uvec ℓ₀ = algebraMap c.F S (embK c ℓ₀.1 b) • uvec ℓ₀ := by
    intro b ℓ₀
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact heig b ℓ₀ i
  set B := uvec ℓ ⬝ᵥ (Matrix.of M *ᵥ uvec ℓ') with hB
  have hBe : B = ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j := by
    rw [hB]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h1 := congrArg (fun N : Matrix (Fin d) (Fin d) S => uvec ℓ ⬝ᵥ (N *ᵥ uvec ℓ')) (hbal a)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hmv,
    hmv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← hB] at h1
  have key : (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) * B = 0 := by
    rw [sub_mul, h1, sub_self]
  have hu : IsUnit (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) := by
    rw [← map_sub]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    apply ha
    have h2 := congrArg (fun x : c.F => (x : ℂ)) (sub_eq_zero.1 h0)
    simp only [embK_coe] at h2
    rw [h2, H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  exact hne (hBe ▸ (hu.mul_right_eq_zero).1 key)

theorem twist_on_eigenDirections (hFix : FrTruncFixSt) (hLE : LinEigSt) : FrTruncFixBSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
  obtain ⟨e', hfr, hrig, cc, hT, h0, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hs S y C
  exact ⟨e', hfr, hrig, cc, hT, h0, hsym, fun m ℓ ℓ' hne => balanced_pairs_conjugate c (fun a => dLin (C.B.A.act a)) C.uvec
    (fun a ℓ i => hLE E H Dw l Xo c S y C a ℓ i) (cc m) (hbal m) ℓ ℓ' hne, hu⟩

theorem eigenDirections : LinEigSt := GlobalTheory.EigDir.linEig_holds

theorem chartIndep_of_globalFns (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  have hAct := expActOf_of eigenDirections
  chartIndep2_verb
    (chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) (killAddVal_of fun _ _ _ _ H => psiCover_holds H))
    (twist_on_eigenDirections (frTruncFix_of frRatio_holds) eigenDirections) germFix_holds (harmInv_of hAct)

theorem chartIndep : ChartIndepSt2 :=
  chartIndep_of_globalFns GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.ChartFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldBC.exists_emb_ext {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (hle : c.F ≤ c'.F) (σ : c.F →+* ℂ) :
    ∃ σ' : c'.F →+* ℂ, σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle) = σ := by
  letI : Algebra c.F c'.F := (_root_.Formalism.L2.Pj.incF c c' hle).toAlgebra
  letI : Algebra c.F ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic ℚ c'.F := Algebra.IsAlgebraic.of_finite ℚ c'.F
  haveI : Algebra.IsAlgebraic c.F c'.F := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let τ : c'.F →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨τ.toRingHom, ?_⟩
  ext x
  exact τ.commutes x

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldBC.rulBC_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)
    (hle : c.F ≤ c'.F) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ)
    (n : ℕ), ∀ f ∈ _root_.Formalism.L2.Pj.sec Xo c a n,
    (∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f) ∧
    (_root_.GlobalTheory.FieldBC.rulBC hle f ∈ _root_.Formalism.L2.Pj.cusp Xo c' (_root_.Formalism.L2.Pj.unfBC hle U) a n ↔ f ∈ _root_.Formalism.L2.Pj.cusp Xo c U a n) := by
  intro E _ _ _ H Dw l Xo c c' hle r U a n f hf
  obtain ⟨hsec, hval⟩ := (_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf
  have hread : ∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f := by
    intro σ'
    have hbc : _root_.Formalism.L2.Pj.IsBC hle (_root_.GlobalTheory.FieldBC.rulBC hle f) ![1] ![f] := by
      unfold _root_.Formalism.L2.Pj.IsBC
      intro S _ _ _ h y
      simp [hval S h y]
    rw [_root_.Formalism.L2.Pj.rdU_unfBC hle U σ' hbc, Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero, map_one]
    exact one_smul ℂ _
  refine ⟨hread, ?_⟩
  rw [_root_.Formalism.L2.Pj.mem_cusp, _root_.Formalism.L2.Pj.mem_cusp]
  constructor
  · rintro ⟨-, hcusp⟩
    refine ⟨hf, fun σ hσ => ?_⟩
    obtain ⟨σ', rfl⟩ := _root_.GlobalTheory.FieldBC.exists_emb_ext hle σ
    have hmem := hcusp σ' (_root_.Formalism.L2.Pj.goodEmb_ext hle hσ rfl)
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC] at hmem
    exact hmem
  · rintro ⟨-, hcusp⟩
    refine ⟨hsec, fun σ' hσ' => ?_⟩
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC]
    exact hcusp _ (by unfold _root_.Formalism.L2.Pj.GoodEmb at hσ' ⊢; exact hσ')

end GlobalTheory.FieldBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom
noncomputable section

namespace GlobalTheory.FiniteOrderRule

open Formalism.L2.Pj

theorem eq_zero_of_forall_algHom {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R]
    [Algebra.FiniteType K R] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (x : R)
    (h : ∀ φ : R →ₐ[K] Ω, φ x = 0) : x = 0 := by
  have hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hb : (⊥ : Ideal R).jacobson = ⊥ := hJ.out (Ideal.isRadical_bot)
  rw [← Ideal.mem_bot, ← hb, Ideal.jacobson, Ideal.mem_sInf]
  rintro J ⟨-, hM⟩
  letI := Ideal.Quotient.field J
  haveI : Module.Finite K (R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ J)
  let ψ : (R ⧸ J) →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h0 := h (ψ.comp (Ideal.Quotient.mkₐ K J))
  have h1 : Ideal.Quotient.mk J x = 0 := by
    apply ψ.toRingHom.injective
    rw [map_zero]
    exact h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem pow_eq_one_of_complex {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (σ : K →+* ℂ) (f : Rules pts) (hf : IsNatural pts mapR f) (k : ℕ)
    (h : ∀ y : pts (CAt σ), evalAt pts mapR f y ^ k = 1) (p : TRing K) (y : pts p.R) : f p y ^ k = 1 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  rw [← sub_eq_zero]
  letI : Algebra K ℂ := σ.toAlgebra
  refine eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ ?_
  intro φ
  let φ' : p.R →ₐ[K] CAt σ := φ
  obtain ⟨z, hz⟩ := hB p.R (CAt σ) φ' y
  have hT : FromTest pts mapR z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evalAt at h0
  rw [dite_eq_left hT, ← hW f hf (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  show φ' _ = 0
  rw [map_sub, map_pow, h0, map_one, sub_self]

theorem evalAt_pow_eq_one {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (f : Rules pts) (k : ℕ) (h : ∀ (p : TRing K) (y : pts p.R), f p y ^ k = 1)
    {S : Type} [CommRing S] [Algebra K S] (y : pts S) (hT : FromTest pts mapR y) :
    evalAt pts mapR f y ^ k = 1 := by
  unfold evalAt
  rw [dite_eq_left hT, ← map_pow, h, map_one]

end GlobalTheory.FiniteOrderRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.FiniteOrderRule.unitC_of_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → UnitC d := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet hC A y
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hk : Nat.card Cls ≠ 0 := Nat.card_pos.ne'
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    d.c₂.F.val.toRingHom d.cδ hC.1.1 (Nat.card Cls) (fun z => by
      have h2 := hC.2 z
      unfold evR at h2
      rw [h2, if_neg Bool.false_ne_true, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one,
        Units.val_one, map_one])
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ (Nat.card Cls) h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hk

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def rulEv (U : Unf Xo c σ r)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) :
    Rul Xo c →+* ((Σ k : U.Comp, (U.X k).dom) → ℂ) where
  toFun f y := rdU U f y.1 y.2.1
  map_zero' := by funext y; rw [map_zero]; rfl
  map_add' f g := by funext y; rw [map_add (f := _)]; rfl
  map_mul' f g := by funext y; rw [rdU_mul]; rfl
  map_one' := by
    funext y
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom U 1 y.1 y.2]
    have e : evR Xo c 1 (U.un y.1 y.2) = 1 := evalAt_one _ _ _ (hT y.1 y.2)
    rw [e]
    rfl

end Ev

def sumParts (R M : Type) [CommRing R] [AddCommMonoid M] :
    AddMonoidAlgebra R M →+* R :=
  (AddMonoidAlgebra.lift R R M 1).toRingHom

theorem sumParts_single (R M : Type) [CommRing R] [AddCommMonoid M] (m : M) (f : R) :
    sumParts R M (AddMonoidAlgebra.single m f) = f := by
  simp [sumParts]

theorem sumParts_smul (K R M : Type) [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (a : K)
    (x : AddMonoidAlgebra R M) : sumParts R M (a • x) = a • sumParts R M x := by
  rw [← algebraMap_smul R a x, ← algebraMap_smul R a (sumParts R M x)]
  exact map_smul (AddMonoidAlgebra.lift R R M 1) _ _

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_isRdgU : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  intro D T h j hj n
  have hT := h.unTest j hj T.σ₀ T.good_σ₀
  have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
  let ev : AddMonoidAlgebra (T.R j) (Deg D j) →+* (DomPt T j → ℂ) :=
    (rulEv (T.U j T.σ₀) hT).comp (sumParts (T.R j) (Deg D j))
  have hev : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (y : DomPt T j),
      ev (incG deg (cutR T.C j) u F) y = rdR h j F y.1 y.2.1 := by
    intro u F y
    show rulEv (T.U j T.σ₀) hT (sumParts (T.R j) (Deg D j) (AddMonoidAlgebra.single (deg u) F.1)) y = _
    rw [sumParts_single]
    rfl
  have hsm : ∀ (a : T.Q.c.F) (F : AddMonoidAlgebra (T.R j) (Deg D j)), ev (a • F) = T.σ₀ a • ev F := by
    intro a F
    funext y
    show rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) (a • F)) y.1 y.2.1 =
      T.σ₀ a • rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) F) y.1 y.2.1
    rw [sumParts_smul, map_smulₛₗ]
    rfl
  have hind : ∀ (u : WeightFamilies.Wt D j) (m : ℕ) (F : Fin m → cutR T.C j u),
      LinearIndependent T.Q.c.F F → LinearIndependent ℂ fun i => ev (incG deg (cutR T.C j) u (F i)) := by
    intro u m F hF
    have hb := hF.map' (cutR T.C j u).subtype (Submodule.ker_subtype _)
    have hs : ∀ i, (F i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := fun i =>
      cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA u) u.n (cutR_le T.C j u (F i).2)
    have hli : LinearIndependent ℂ (fun i => rdU (T.U j T.σ₀) (F i).1) :=
      (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ T.σ₀ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
        ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) (wtA u) u.n).1 m (fun i => (F i).1) hs hb
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg
    refine hli g ?_
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
    · have h1 := congrFun hg ⟨k, ⟨x, hx⟩⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun z => g i * z) (hev u (F i) ⟨k, ⟨x, hx⟩⟩).symm
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : rdU (T.U j T.σ₀) (F i).1 k x = 0 := dif_neg hx
      rw [this, mul_zero]
  exact ⟨⟨DomPt T j, T.σ₀, ev, hsm, hind⟩, Equiv.refl _, fun _ => rfl, hev⟩

end GlobalTheory.Shares
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingFormsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_embedding_reading_forms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  first | exact @GlobalTheory.Shares.exists_isRdgU | exact GlobalTheory.Shares.exists_isRdgU | (intros; apply GlobalTheory.Shares.exists_isRdgU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRdOfInBasis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem addL_zero_wt (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  simp [addL, wadd, wsmul]

theorem rk_Mlat_eq_finrank (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (h : LatAt B j ka) :
    X.rk ka (B.Mlat j ka) = Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
  letI : Submodule.IsFullLattice B.KO (B.Mlat j ka) := h
  unfold PJ.rk
  rw [Submodule.IsFullLattice.span_eq_top]

private lemma s_mem_sp_univ (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) : R.s w t i ∈ R.sp wL Set.univ := by
  unfold Rdg.s Rdg.sp
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨w k, Set.mem_univ _, rfl⟩

theorem Rdg.s_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) : R.s w t i ^ m * v ∈ R.sp (addL u wL (n + m)) Set.univ := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>

    rw [pow_succ', mul_assoc, ← Nat.add_assoc, ← wadd_addL]
    exact hmul _ _ _ (s_mem_sp_univ R w t i) _ ih

theorem Rdg.prod_pow_mul_mem (R : Rdg X) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
    (hmul : ∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j))) (u : WeightFamilies.Wt D j) (n : ℕ) {v : R.Y → ℂ}
    (hv : v ∈ R.sp (addL u wL n) Set.univ) :
    (∏ i ∈ s, R.s w t i.succ ^ α i) * v ∈ R.sp (addL u wL (n + ∑ i ∈ s, α i)) Set.univ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have h := R.s_pow_mul_mem w t hmul a.succ u (n + ∑ i ∈ s, α i) (α a) ih
    have e : n + (α a + ∑ i ∈ s, α i) = n + ∑ i ∈ s, α i + α a := by ring
    rw [e]
    exact h

theorem shareRd_of_inBasis : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → WeightFamilies.dimY D j < T → 0 < WeightFamilies.dimY D j → LatAt B j ka → (∃ la, InBasis G la) → ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka hDT _ hlat hex
  obtain ⟨la, hla⟩ := hex

  have hI := (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T Mg δ xs hgen hfac hka la).1 hla
  obtain ⟨-, -, -, -, -, hmul, -, hfin⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hθ : ∀ i, R.ev (X.inc wF (G.th' i)) ∈ R.sp wF Set.univ := fun i =>
    Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩

  have hLI := (hfac.indep G.del (fun i => R.ev (X.inc wF (G.th' i))) hθ hI.1).1

  have hmem : ∀ p, R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p ∈
      R.sp ka Set.univ := by
    rintro ⟨⟨α, hα⟩, i⟩
    have h0 : R.ev (X.inc wF (G.th' i)) ∈ R.sp (addL wF wL 0) Set.univ := by
      rw [addL_zero_wt]
      exact hθ i
    have h1 := R.s_pow_mul_mem G.w t hmul 0 wF 0 (T - ∑ k, α k) h0
    have h2 := R.prod_pow_mul_mem G.w t hmul α Finset.univ wF (0 + (T - ∑ k, α k)) h1
    have hle : ∑ k, α k ≤ T := by
      unfold a0 at hα
      omega
    have e : 0 + (T - ∑ k, α k) + ∑ k ∈ Finset.univ, α k = T := by omega
    rw [e, hka] at h2
    show R.mon G.w t α * R.s G.w t 0 ^ (T - ∑ k, α k) * R.ev (X.inc wF (G.th' i)) ∈ R.sp ka Set.univ
    rw [mul_assoc]
    exact h2

  obtain ⟨hfd, hfr⟩ := hfin ka ⊤
  rw [Submodule.top_coe] at hfd hfr
  have hcard : Nat.card ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del) ≤
      Module.finrank B.KO (⊤ : Submodule B.KO (B.Cusp j ka)) := by
    rw [← hfr]
    haveI : FiniteDimensional ℂ (R.sp ka Set.univ) := hfd
    have hLI' : LinearIndependent ℂ (fun p =>
        (⟨R.lead G.w t T (a0 D j T) (fun i => R.ev (X.inc wF (G.th' i))) p, hmem p⟩ :
          R.sp ka Set.univ)) :=
      LinearIndependent.of_comp (R.sp ka Set.univ).subtype hLI
    haveI := hLI'.finite
    haveI := Fintype.ofFinite ({α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin G.del)
    rw [Nat.card_eq_fintype_card]
    exact hLI'.fintype_card_le_finrank
  have hcnt : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} =
      (T - 1).choose (WeightFamilies.dimY D j) :=
    GlobalTheory.card_exponents_sum_lt_sub _ _ hDT
  rw [Nat.card_prod, Nat.card_fin, hcnt] at hcard
  unfold ShareRd
  rw [rk_Mlat_eq_finrank X ka hlat]
  exact_mod_cast hcard

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InContainMROfAnFacts
noncomputable section

namespace GlobalTheory.Shares.Contain

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem addL_zero (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  unfold addL wadd wsmul
  cases u
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; simp
  · funext τ i; simp
  · simp

def secP (X : PJ D B P j) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (i : Fin (WeightFamilies.dimY D j + 1)) :
    MvPolynomial (Idx D j N) X.Forms :=
  ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))

section Weights

variable {X : PJ D B P j} {N : ℕ} {wL : WeightFamilies.Wt D j} {w : Fin N → B.Cusp j wL}

theorem ofWt_pow_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) : OfWt X (addL u wL (n + m)) (secP X w i ^ m * p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact hm _ _ _ _ (hs i) ih

theorem ofWt_prod_mul (hs : ∀ i, OfWt X wL (secP X w i))
    (hm : ∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q))
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (u : WeightFamilies.Wt D j) (n : ℕ) {p : MvPolynomial (Idx D j N) X.Forms}
    (hp : OfWt X (addL u wL n) p) (s : Finset (Fin (WeightFamilies.dimY D j))) :
    OfWt X (addL u wL (n + ∑ i ∈ s, α i)) ((∏ i ∈ s, secP X w i.succ ^ α i) * p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, add_comm (α a), ← add_assoc]
    exact ofWt_pow_mul hs hm _ u _ _ ih

end Weights

theorem inContainMR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → addL wF wL T = ka → WeightFamilies.dimY D j ≤ T → ∀ S : Scal B, Submodule.span B.KO ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ → ∀ la, InBasis G la → InContainMR G la S CR T c := by
  intro D B P j X ka wL wF G R t T CR c δ xs hgen hA hka hDT S hTh la hB
  obtain ⟨hsec, hC, hCw, hmul, -, -, hsp, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  obtain ⟨hli, hdel⟩ := (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D B P j X ka wL wF G R t T _ δ xs hgen hA hka la).1 hB
  have hs1 : ∀ i, toRp X la G.N (secP X G.w i) = sec X la G.w i := fun i => (hsec i).1
  have hs2 : ∀ i, R.toFn t (secP X G.w i) = R.s G.w t i := fun i => (hsec i).2.1
  have hs3 : ∀ i, OfWt X wL (secP X G.w i) := fun i => (hsec i).2.2
  have hspan : Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hdel])
  have hcon := hA.contain G.del (fun i => R.ev (X.inc wF (G.th' i)))
    (fun i => Submodule.subset_span ⟨G.th' i, Set.mem_univ _, rfl⟩) hspan

  set Gen : Set (Rp X la G.N) := ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       zAll G la S T) with hGen
  let Sp : Set (MvPolynomial (Idx D j G.N) X.Forms) := {p | OfWt X ka p ∧ toRp X la G.N p ∈ Gen}
  have hle : Submodule.span ℂ (Set.range (R.lead G.w t T (a0 D j T) fun i => R.ev (X.inc wF (G.th' i)))) ⊔
      R.deep G.w t (X.wF0 wL wF) (a0 D j T) ≤ Submodule.span ℂ (R.toFn t '' Sp) := by
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨⟨⟨al, hal⟩, i⟩, rfl⟩
      refine ⟨(∏ k, secP X G.w k.succ ^ al k) * (secP X G.w 0 ^ (T - ∑ k, al k) *
        MvPolynomial.C (X.inc wF (G.th' i))), ⟨?_, Or.inl ⟨al, i, hal, ?_⟩⟩, ?_⟩
      · have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (G.th' i)) : MvPolynomial (Idx D j G.N) X.Forms) := by
          rw [addL_zero]; exact hCw _ _
        have h1 := ofWt_prod_mul hs3 hmul al wF _ (ofWt_pow_mul hs3 hmul 0 wF 0 (T - ∑ k, al k) h0) Finset.univ
        have he : 0 + (T - ∑ k, al k) + ∑ k, al k = T := by
          unfold a0 at hal; omega
        rwa [he, hka] at h1
      · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow, mul_assoc]
      · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.lead, Rdg.mon, mul_assoc]
    · rintro _ ⟨al, f, hal, hf, rfl⟩
      have hf' : f ∈ R.sp (X.wF0 wL wF)
          ((X.Thc S.s0 (X.wF0 wL wF) : Submodule (𝓞 B.KO) _) : Set (B.Cusp j (X.wF0 wL wF))) := by
        rw [← hsp, hTh]; exact hf
      clear hf
      unfold Rdg.sp at hf'
      induction hf' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨θ, hθ, rfl⟩ := hx
        refine Submodule.subset_span ⟨(∏ k, secP X G.w k.succ ^ al k) * MvPolynomial.C (X.inc _ θ),
          ⟨?_, Or.inr ⟨al, θ, hal, hθ, ?_⟩⟩, ?_⟩
        · have h0 : OfWt X (addL wF wL (WeightFamilies.dimY D j))
              (MvPolynomial.C (X.inc _ θ) : MvPolynomial (Idx D j G.N) X.Forms) := hCw _ θ
          have h1 := ofWt_prod_mul hs3 hmul al wF _ h0 Finset.univ
          have he : WeightFamilies.dimY D j + ∑ k, al k = T := by
            unfold a0 at hal; omega
          rwa [he, hka] at h1
        · simp only [map_mul, map_prod, map_pow, hs1, (hC _).1, Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow]
        · simp only [map_mul, map_prod, map_pow, hs2, (hC _).2, Rdg.mon]
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have hmem : R.ev (X.inc ka F) ∈ Submodule.span ℂ (R.toFn t '' Sp) :=
    hle (hcon (Submodule.subset_span ⟨F, hF, rfl⟩))
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.1 hmem
  choose p hp hpg using fun i => (g i).2
  have htr := (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la G.N t hgen ka (Fin n) p (fun i => (hp i).1)).2.1
    (MvPolynomial.C (X.inc ka F)) (hCw _ _)
  rw [(hC _).1, (hC _).2] at htr
  have h2 : R.ev (X.inc ka F) ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)) := by
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hpg i⟩)
  refine Submodule.span_mono ?_ (htr.2 h2)
  rintro _ ⟨i, rfl⟩
  exact (hp i).2

end GlobalTheory.Shares.Contain
end
end

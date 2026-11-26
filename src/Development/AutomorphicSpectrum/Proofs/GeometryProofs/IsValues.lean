module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def IsValues (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
    (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (MV : LieModel P.tK.G (𝟙 (Sp L)) V)
    {m : ℕ} (s : Fin m → 𝔐.Li) (sL : Fin m → V) : Prop :=
  ∀ k, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
    𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (s k) v ∧ (MV.pt (sL k)).left ≫ P.m.φ = v.left

def primeOf {L : Type} [Field L] [NumberField L] (v : FinitePlace L) : PrimeSpectrum (𝓞 L) :=
  ⟨v.maximalIdeal.asIdeal, v.maximalIdeal.isPrime⟩

end Defs

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open Polynomial NumberField

theorem iSupIndep_eigSp {Ω E F I : Type} [Field Ω] [CharZero Ω] [AddCommGroup E] [Module Ω E] [Field F] [NumberField F]
    (ρ : 𝓞 F →+* Module.End Ω E) (σ : I → (𝓞 F →+* Ω)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp ρ (σ s) := by
  obtain ⟨θ, -, -, -, -, hgen⟩ := Cusp.exists_integral_generator F
  have hagree : ∀ (τ : 𝓞 F →+* Ω) (P : ℤ[X]), τ (aeval θ P) = aeval (τ θ) P := fun τ P =>
    (aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  refine ((Module.End.eigenspaces_iSupIndep (ρ θ)).comp hinj).mono fun s x hx => ?_
  have hx' := (Submodule.mem_iInf _).1 hx θ
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx'
  exact Module.End.mem_eigenspace_iff.2 hx'

theorem isInternal_eigSp : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  intro Ω _ _ E _ _ F _ _ ρ I _ _ σ hσ hcard
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_eigSp ρ σ hσ)
    (Cusp.iSup_eigSp_eq_top ρ σ hσ hcard)

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_decomposition_internal : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | exact GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.isInternal_eigSp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjective
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MorphismEqOfGenericPointEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem morphism_eq_of_generic_point_eq : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g := by
  intro R _ Z W _ s Ω _ ξ f g hs hξ h
  have := projProper _ _ _ hs
  have : W.IsSeparated := ⟨by
    rw [← terminal.comp_from s]
    infer_instance⟩
  have : IsDominant ξ := ⟨fun q => closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self _)) (specializes_iff_mem_closure.1 (hξ q))⟩
  exact ext_of_isDominant ξ h

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem maps_eq_of_eq_at_generic : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g :=
  @PositivityTheory.UnitarySelfGeneration.morphism_eq_of_generic_point_eq

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_eq_generic_projective : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic | exact GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEmbLabel
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEqNegOfSquare
theorem UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq :
    ∀ {d : ℕ},
    (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith [mul_comm z.im z.re]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso
      rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (h : z ^ 2 = -(d : ℂ)) : starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq hd h

theorem exists_emb_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l) (κ : c.F →+* ℂ) (lab : CMType H ⊕ CMType H), ∃ s : E →+* ℂ, κ.comp (labelEmb c lab) = s.comp (algebraMap (𝓞 E) E) ∧ ∀ ρ : c.F, (ρ : ℂ) = H.rt0 → s (H.rt : E) = Sum.elim (fun _ => κ ρ) (fun _ => -κ ρ) lab := by
  intro E _ _ _ H l c κ lab
  rcases lab with τ | τ
  · refine ⟨κ.comp (τ.1.codRestrict c.F (c.conj τ.1)), rfl, fun ρ hρ => ?_⟩
    show κ _ = κ ρ
    congr 1
    apply Subtype.ext
    exact τ.2.trans hρ.symm
  · refine ⟨κ.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (IsCMField.complexConj E : E →+* E)), ?_, fun ρ hρ => ?_⟩
    · refine RingHom.ext fun a => ?_
      show κ _ = κ _
      congr 1
      apply Subtype.ext
      show τ.1 ((H.bar a : 𝓞 E) : E) = τ.1 (IsCMField.complexConj E (a : E))
      rw [H.bar_eq]
    · show κ _ = -κ ρ
      rw [← map_neg]
      congr 1
      apply Subtype.ext
      show τ.1 (IsCMField.complexConj E (H.rt : E)) = -(ρ : ℂ)
      rw [IsCMField.complexEmbedding_complexConj, τ.2, hρ]
      exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [CharZero Ω] in
theorem segre_update_ratio [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (hc b)]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem adjoin_segre_eq (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) =
      blockFnField y := by
  classical
  rw [← CoordArithOfFnField.ratioField_eq y (E c₀) hc]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, rfl⟩
  · rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨E.symm (Function.update (E c₀) k i), ?_⟩
    simpa using segre_update_ratio y (E c₀) hc k i

theorem trdeg_blockFnField {y : (Σ k, ι k) → Ω} {e : ℕ} (hA : IsArithVar (mCoordIdeal y) (e + 1))
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Algebra.trdeg ℚ (blockFnField y) = e := by
  obtain ⟨_, _, _, hdim⟩ := hA
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = e := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h1, ← trdeg_add_eq ℤ ℚ (A := blockFnField y), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_away_of_trdeg (S : Set Ω) (hS : S.Finite) {e : ℕ}
    (h : Algebra.trdeg ℚ (IntermediateField.adjoin ℚ S) = e) :
    ∃ s : Algebra.adjoin ℚ S, s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  have hfin : Algebra.FiniteType ℚ (Algebra.adjoin ℚ S) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
  have h2 : Algebra.trdeg ℚ (Algebra.adjoin ℚ S) = e := by
    rw [← h]
    exact (GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := ℚ) (A := Algebra.adjoin ℚ S)
      (IntermediateField.adjoin ℚ S)).symm
  exact GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℚ _ h2)

theorem exists_away_standardSmooth (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  refine exists_away_of_trdeg _ (Set.finite_range _) ?_
  rw [adjoin_segre_eq y E c₀ hc]
  exact trdeg_blockFnField hA (E c₀) hc

end GlobalTheory.CompanionTheory.Ar.SegreChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalizationStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_smooth_localization : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0), ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | exact GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem aeval_const_mul {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℤ R] {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (κ : R) (a : σ → R) :
    aeval (fun j => κ * a j) G = κ ^ n * aeval a G := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = n := by
    have h := hG (mem_support_iff.1 hm)
    have e : Finsupp.weight (1 : σ → ℕ) m = ∑ i, m i := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [← e]
    exact h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_homog {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (c₀ : σ) (h1 : r c₀ = 1)
    (t : Algebra.adjoin ℚ (Set.range r)) :
    ∃ (m : ℤ) (n : ℕ) (G : MvPolynomial σ ℤ), m ≠ 0 ∧ G.IsHomogeneous n ∧
      aeval r G = (m : Ω) * (t : Ω) := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, 1, X j, one_ne_zero, isHomogeneous_X _ _, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [map_intCast, eq_intCast, eq_ratCast, Int.cast_natCast]
    rw [Rat.cast_def]
    field_simp
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add (f := _), map_mul, map_pow, aeval_X, h1, one_pow, mul_one, eq_intCast, map_intCast, e₁, e₂]
      push_cast
      ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, G₁ * G₂, mul_ne_zero hm₁ hm₂, hG₁.mul hG₂, ?_⟩
    simp only [map_mul, e₁, e₂]
    push_cast
    ring

theorem smooth_away_mul {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by
  let S := Localization.Away s
  let T := Localization.Away (algebraMap B S u)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (algebraMap B S u)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans e 0 ℚ S T
  rw [zero_add] at h
  haveI : IsLocalization.Away (s * u) T := IsLocalization.Away.mul' S T s u
  let f : T ≃ₐ[B] Localization.Away (s * u) :=
    IsLocalization.algEquiv (Submonoid.powers (s * u)) T (Localization.Away (s * u))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv e (f.restrictScalars ℚ)

theorem eval_map_int {σ : Type} (w : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))

theorem blockRatio_eq (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (p : Σ k, ι k) [DecidableEq K] :
    y p / y ⟨p.1, E c₀ p.1⟩ =
      (∏ k, y ⟨k, E (E.symm (Function.update (E c₀) p.1 p.2)) k⟩) / ∏ k, y ⟨k, E c₀ k⟩ := by
  obtain ⟨k₀, i⟩ := p
  simp only [Equiv.apply_symm_apply]
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  rw [div_eq_div_iff (hc k₀) h0,
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, E c₀ k⟩) (Finset.mem_univ k₀),
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, Function.update (E c₀) k₀ i k⟩) (Finset.mem_univ k₀)]
  have e : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, Function.update (E c₀) k₀ i k⟩ =
      ∏ k ∈ Finset.univ.erase k₀, y ⟨k, E c₀ k⟩ :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e, Function.update_self]
  ring

theorem aeval_blockRatio_mem [CharZero Ω] (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (β : MRing ι) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ∈
      Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) := by
  classical
  induction β using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem _ n
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    refine mul_mem hp (Algebra.subset_adjoin ⟨E.symm (Function.update (E c₀) i.1 i.2), ?_⟩)
    exact (blockRatio_eq y E c₀ hc i).symm

theorem aeval_eq_prod_mul (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b) :
    aeval y β = (∏ k, y ⟨k, E c₀ k⟩ ^ b k) *
      aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := by
  have h := GlobalTheory.CompanionTheory.Ar.aeval_blockScale hb (fun k => y ⟨k, E c₀ k⟩) (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩)
  have e : (fun p : Σ k, ι k => y ⟨p.1, E c₀ p.1⟩ * (y p / y ⟨p.1, E c₀ p.1⟩)) = y :=
    funext fun p => mul_div_cancel₀ _ (hc p.1)
  rwa [e] at h

theorem mConeMap_segre (j : Fin (N + 1)) :
    mConeMap y (∏ k, (X ⟨k, E j k⟩ : MRing ι)) =
      (∏ k, (X k : MvPolynomial K Ω)) * C (∏ k, y ⟨k, E j k⟩) := by
  simp only [map_prod, mConeMap, aeval_X, Finset.prod_mul_distrib]
  rw [mul_comm]

theorem vanish_of_value (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b)
    {n : ℕ} {m : ℤ} {G : MvPolynomial (Fin (N + 1)) ℤ} (hG : G.IsHomogeneous n)
    (hval : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G =
      (m : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hβ : evC z β = 0) :
    (∏ k, z ⟨k, E c₀ k⟩) = 0 ∨ aeval (fun j => ∏ k, z ⟨k, E j k⟩) G = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hx : aeval (fun j => ∏ k, y ⟨k, E j k⟩) G * ∏ k, y ⟨k, E c₀ k⟩ ^ b k =
      (m : Ω) * aeval y β * (∏ k, y ⟨k, E c₀ k⟩) ^ n := by
    have e : (fun j => ∏ k, y ⟨k, E j k⟩) = fun j => (∏ k, y ⟨k, E c₀ k⟩) *
        ((∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :=
      funext fun j => (mul_div_cancel₀ _ h0).symm
    rw [e, aeval_const_mul hG, hval, aeval_eq_prod_mul y E c₀ hc hb]
    ring
  let P₁ : MRing ι := aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G * ∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k
  let P₂ : MRing ι := C m * β * (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι)) ^ n
  have hmem : P₁ - P₂ ∈ mCoordIdeal y := by
    refine RingHom.mem_ker.2 ?_
    have hG' : mConeMap y (aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G) =
        (∏ k, (X k : MvPolynomial K Ω)) ^ n * C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) := by
      rw [comp_aeval_apply]
      simp only [mConeMap_segre]
      rw [aeval_const_mul hG]
      congr 1
      exact (comp_aeval_apply _ (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) G).symm
    have hX : mConeMap y (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k) =
        (∏ k, (X k : MvPolynomial K Ω) ^ b k) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k) := by
      simp only [map_prod, map_pow, mConeMap, aeval_X, mul_pow, Finset.prod_mul_distrib]
      rw [mul_comm]
    have hC : mConeMap y (C m) = C (m : Ω) := by
      simp [mConeMap]
    have hS := mConeMap_segre y E c₀
    simp only [P₁, P₂, map_sub, map_mul, map_pow, hG', hX, hC, hS,
      GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog y hb]
    rw [sub_eq_zero]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hx
    simp only [map_mul, map_pow] at this
    calc _ = (∏ k, (X k : MvPolynomial K Ω)) ^ n * (∏ k, (X k : MvPolynomial K Ω) ^ b k) *
          (C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k)) := by ring
      _ = _ := by rw [this]; ring
  have hzero := hz.2 _ hmem
  have hev : aeval z (P₁ - P₂) = 0 := by rw [← eval_map_int]; exact hzero
  have hβ' : aeval z β = 0 := by rw [← eval_map_int]; exact hβ
  have hP : aeval (fun j => ∏ k, z ⟨k, E j k⟩) G * ∏ k, z ⟨k, E c₀ k⟩ ^ b k = 0 := by
    simp only [P₁, P₂, map_sub, map_mul, map_pow, map_prod, aeval_X, hβ', comp_aeval_apply] at hev
    simpa using hev
  rcases mul_eq_zero.1 hP with h | h
  · exact Or.inr h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine Or.inl (Finset.prod_eq_zero_iff.2 ⟨k, Finset.mem_univ _, ?_⟩)
    by_contra h'
    exact pow_ne_zero _ h' hk

end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm


open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes in
theorem GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  intro Ω _ _ K _ ι _ y e β b hb hβ N E c₀ hc s hs _
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have h1 : (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) c₀ = 1 := div_self h0
  obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := SegreForm.exists_homog _ c₀ h1 s
  obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := SegreForm.exists_homog _ c₀ h1
    ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩
  have hbt : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ≠ 0 := by
    intro h
    apply hβ
    rw [form_mem_mCoordIdeal_iff y hb, SegreForm.aeval_eq_prod_mul y E c₀ hc hb, h, mul_zero]
  have hm₁' : (m₁ : Ω) ≠ 0 := by exact_mod_cast hm₁
  have hm₂' : (m₂ : Ω) ≠ 0 := by exact_mod_cast hm₂
  have hs' : (s : Ω) ≠ 0 := fun h => hs (Subtype.ext h)
  refine ⟨n₁ + n₂, X c₀ * G₁ * G₂,
    s * (((m₁ * m₂ : ℤ) : Algebra.adjoin ℚ _) * ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩),
    ?_, ?_, ?_, ?_, SegreForm.smooth_away_mul s _ e, ?_⟩
  · have := ((isHomogeneous_X ℤ c₀).mul hG₁).mul hG₂
    convert this using 1
    ring
  · rw [mul_assoc]
    exact dvd_mul_right _ _
  · have e₂' : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G₂ =
        (m₂ : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := e₂
    rw [map_mul, map_mul, aeval_X, e₁, e₂', div_self h0]
    push_cast
    ring
  · intro h
    have h' := congrArg (Subtype.val) h
    have h'' : (s : Ω) * (((m₁ : Ω) * m₂) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β) = 0 := by
      simpa using h'
    exact mul_ne_zero hs' (mul_ne_zero (mul_ne_zero hm₁' hm₂') hbt) h''
  · intro z hz hzβ
    rw [SegreForm.eval_map_int, map_mul, map_mul, aeval_X]
    rcases SegreForm.vanish_of_value y E c₀ hc hb hG₂ e₂ hz hzβ with h | h
    · simp only [h, zero_mul]
    · simp only [h, mul_zero]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzeroStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_smooth_chart_of_nonzero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | exact GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.Rt0NeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem rt0_conj_neg_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have hsq := H.sqrt_neg_disc_sq
  have hd : (H.d : ℝ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have him := congrArg Complex.im hsq
  have hre := congrArg Complex.re hsq
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.natCast_im,
    Complex.natCast_re] at him hre
  have h0 : H.rt0.re = 0 := by
    by_contra h
    have hi : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by nlinarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [hi] at hre
    have : (0 : ℝ) < H.d := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hd)
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem rt0_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have hsq := H.sqrt_neg_disc_sq
  rw [h] at hsq
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  simp at hsq
  exact H.d_prime.ne_zero hsq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

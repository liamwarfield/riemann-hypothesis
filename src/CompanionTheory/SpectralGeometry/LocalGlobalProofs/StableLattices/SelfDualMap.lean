module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdAny

theorem selfDual_map {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ+ W) (μ : Measure V)
    (χ : V → V → ℂ) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  obtain ⟨hH, hinv⟩ := h
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨e.isAddHaarMeasure_map μ, ?_⟩
  intro Φ hc hs hint z
  let H : V → ℂ := fun y => ∫ x, Φ (e x) * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map e) = H (e.symm y) := fun y => by
    rw [hemb.integral_map]
    simp [H]
  simp only [h1] at hint ⊢
  have hint2 : Integrable H μ := by
    have h2 := (hemb.integrable_map_iff).1 hint
    simpa [Function.comp_def] using h2
  have h3 := hinv (Φ ∘ e) (hc.comp e.continuous) (hs.comp_homeomorph e.toHomeomorph) hint2 (e.symm z)
  rw [hemb.integral_map]
  simp only [ContinuousAddEquiv.symm_apply_apply]
  refine h3.trans ?_
  simp

section Unit

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def evalE : (Unit → R) ≃ₜ+ R where
  toFun x := x ()
  invFun s := fun _ => s
  left_inv x := rfl
  right_inv s := rfl
  map_add' x y := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

variable [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

theorem iff_of_unit (ψR : R → ℂ) (lam : Measure R) [SigmaFinite lam] (c : ℝ≥0)
    (B : Matrix Unit Unit R) (hB : B = 1)
    (h : ∀ μ : Measure (Unit → R), SelfDual μ (fun x y => ψR (x ⬝ᵥ (B *ᵥ y))) ↔
      μ = c • Measure.pi fun _ => lam) (ν : Measure R) :
    SelfDual ν (fun s t => ψR (s * t)) ↔ ν = c • lam := by
  subst hB
  have hχ : (fun x y : Unit → R => ψR (x ⬝ᵥ ((1 : Matrix Unit Unit R) *ᵥ y))) =
      fun x y => ψR (evalE x * evalE y) := by
    funext x y
    simp [evalE, dotProduct]
  rw [hχ] at h
  have hm : Measurable (evalE : (Unit → R) ≃ₜ+ R) := evalE.continuous.measurable
  have hms : Measurable (evalE.symm : R ≃ₜ+ (Unit → R)) := evalE.symm.continuous.measurable
  have hp : (Measure.pi fun _ : Unit => lam).map evalE = lam :=
    (measurePreserving_funUnique lam Unit).map_eq
  have hmm : ∀ μ : Measure R, (μ.map evalE.symm).map evalE = μ := fun μ => by
    rw [Measure.map_map hm hms]
    convert Measure.map_id
    ext x
    simp
  constructor
  · intro hν
    have h1 := selfDual_map evalE.symm ν _ hν
    have h2 := (h _).1 h1
    have h3 := congrArg (Measure.map evalE) h2
    rw [hmm, Measure.map_smul, hp] at h3 <;> try exact hm.aemeasurable
    exact h3
  · rintro rfl
    have h1 := selfDual_map evalE _ _ ((h _).2 rfl)
    rw [Measure.map_smul, hp] at h1 <;> try exact hm.aemeasurable
    simpa using h1

end Unit

theorem selfDual_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (Ainf F), SelfDual ν (fun s t => psiInf F ψ (s * t)) ↔ ν = cinf • laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (Fv F v), SelfDual ν (fun s t => psiV F ψ v (s * t)) ↔ ν = c v • lam v := by
  intro F E _ _ _ _ _ σ hCM laminf lam hinf hlam ψ hψ
  obtain ⟨cinf, c, hU, h1, h2⟩ := GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_coord F hCM.1 laminf lam hinf hlam ψ hψ
    Unit 1 (Matrix.isSymm_one) (by simp)
  refine ⟨cinf, c, hU, fun ν => ?_, fun v ν => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := isLocR_Ainf F hCM.1
    haveI := a1; haveI := a2; haveI := a3; haveI := a4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI := hinf.1
    exact iff_of_unit (psiInf F ψ) laminf cinf _ (Matrix.map_one _ (map_zero _) (map_one _)) h1 ν
  · obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := a1; haveI := a2; haveI := a3; haveI := a4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    exact iff_of_unit (psiV F ψ v) (lam v) (c v) _ (Matrix.map_one _ (map_zero _) (map_one _)) (h2 v) ν

end GlobalTheory.CompanionTheory.SW.SdAny
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem card_lev_lt_succ {n : ℕ} (lev : Fin n → ℕ) (k : ℕ) :
    (univ.filter fun a => lev a < k + 1).card =
      (univ.filter fun a => lev a < k).card + (univ.filter fun a => lev a = k).card := by
  have hd : Disjoint (univ.filter fun a => lev a < k) (univ.filter fun a => lev a = k) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    omega
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_union]
  omega

theorem sum_sz_castLE {n M : ℕ} (lev : Fin n → ℕ) : ∀ (k : ℕ) (hk : k ≤ M),
    ∑ b : Fin k, sz lev M (Fin.castLE hk b) = (univ.filter fun a => lev a < k).card := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [Fin.sum_univ_castSucc, card_lev_lt_succ, ← ih (by omega)]
    rfl

theorem lt_card_iff {n : ℕ} {lev : Fin n → ℕ} (hm : Monotone lev) (k : ℕ) (a : Fin n) :
    (a : ℕ) < (univ.filter fun b => lev b < k).card ↔ lev a < k := by
  constructor
  · intro h
    by_contra hn
    have hs : (univ.filter fun b => lev b < k) ⊆ Finset.Iio a := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact Finset.mem_Iio.2 (hm.reflect_lt (by omega))
    have := Finset.card_le_card hs
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hs : Finset.Iic a ⊆ (univ.filter fun b => lev b < k) := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (hm (Finset.mem_Iic.1 hb)) h
    have := Finset.card_le_card hs
    rw [Fin.card_Iic] at this
    omega

theorem lev_stdBlocks {n M : ℕ} (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (i : Fin M) (p : Fin (sz lev M i)) : lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ) := by
  have hv := stdBlocks_val (sz lev M) h i p
  rw [sum_sz_castLE lev (i : ℕ) i.2.le] at hv
  have hp : (p : ℕ) < (univ.filter fun a => lev a = (i : ℕ)).card := p.2
  have h1 := lt_card_iff hm (i : ℕ) (stdBlocks (sz lev M) h ⟨i, p⟩)
  have h2 := lt_card_iff hm ((i : ℕ) + 1) (stdBlocks (sz lev M) h ⟨i, p⟩)
  rw [card_lev_lt_succ] at h2
  have h3 := h2.1 (by omega)
  have h4 : ¬ lev (stdBlocks (sz lev M) h ⟨i, p⟩) < (i : ℕ) := fun hl => by
    have := h1.2 hl
    omega
  omega

theorem stdBlocks_clusters : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  intro n M lev h hm _
  refine ⟨lev_stdBlocks lev h hm, fun f i => ?_⟩
  refine Finset.sum_bij (fun p _ => stdBlocks (sz lev M) h ⟨i, p⟩) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact lev_stdBlocks lev h hm i p
  · intro p _ q _ hpq
    have := (stdBlocks (sz lev M) h).injective hpq
    simpa using this
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨⟨j, q⟩, rfl⟩ := (stdBlocks (sz lev M) h).surjective a
    have hj : j = i := Fin.ext ((lev_stdBlocks lev h hm j q).symm.trans ha)
    subst hj
    exact ⟨q, mem_univ _, rfl⟩
  · intro p _
    rfl

end GlobalTheory.CompanionTheory.RgCOBlock
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSumStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_blocks_level_sum : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters | exact GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEq
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEq
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.SumSz

theorem sum_sz_eq_card : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  intro n M lev h
  have key := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin M)))
    (f := fun a => (⟨lev a, h a⟩ : Fin M)) (fun a _ => Finset.mem_coe.2 (mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at key
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  unfold sz
  congr 1

end GlobalTheory.CompanionTheory.RgCOBlock.SumSz
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEqStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_of_level_sizes_eq : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card | exact GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.SumSz.sum_sz_eq_card <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ConjQdet
namespace GlobalTheory.CompanionTheory.RgConjQdet

open Finset

theorem conj_single_apply {n : ℕ} (U Ui : Matrix (Fin n) (Fin n) ℂ) (p q a b : Fin n) :
    (U * Matrix.single p q 1 * Ui : Matrix (Fin n) (Fin n) ℂ) a b = U a p * Ui q b := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem conjQdet : CompanionTheory.RgExh.Dec.J.ConjQdet := by
  intro n X U Ui hUUi hUiU u
  have hE : ∀ (x : ℂ) (p q : Fin n),
      Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) x p q =
        ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d := by
    intro x p q
    have hd : ∑ c, ∑ d, (U c p * Ui q d) • (if c = d then algebraMap ℂ (Module.End ℂ X.V) x else 0)
        = if p = q then algebraMap ℂ (Module.End ℂ X.V) x else 0 := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_smul]
      have hc : ∑ c, U c p * Ui q c = (Ui * U) q p := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      rw [hc, hUiU, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq
        simp
      · rw [if_neg (Ne.symm hpq), if_neg hpq, zero_smul]
    simp only [Formalism.REAL.Tm, ReciprocityTheory.ChartRestriction.DS.actM, conj_single_apply, Matrix.transpose_apply,
      Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    rw [hd]
  have hT : Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) =
      fun x p q => ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d :=
    funext fun x => funext fun p => funext fun q => hE x p q
  rw [PI.UnitaryGroupMassFormula.DSIC.qdet_eq_qF (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)), hT,
    PI.UnitaryGroupMassFormula.DSIC.qF_row, PI.UnitaryGroupMassFormula.DSIC.qF_col X.E X.gl, smul_smul, Matrix.det_transpose,
    Matrix.det_transpose, ← Matrix.det_mul, hUUi, Matrix.det_one, one_smul]

end GlobalTheory.CompanionTheory.RgConjQdet
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotient
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotient
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.QuotAction

theorem descends (C : Type) [AddCommGroup C] [Module ℂ C] (L : Type) (l : L → Module.End ℂ C)
    (Z B : Submodule ℂ C) (hZ : ∀ k, ∀ z ∈ Z, l k z ∈ Z) (hB : ∀ k, ∀ z ∈ B, l k z ∈ B) :
    ∃ ρ : FreeAlgebra ℂ L →ₐ[ℂ] Module.End ℂ (Z ⧸ B.comap Z.subtype),
      ∀ (y : FreeAlgebra ℂ L) (z : Z), ∃ hz : FreeAlgebra.lift ℂ l y (z : C) ∈ Z,
        ρ y (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ⟨FreeAlgebra.lift ℂ l y (z : C), hz⟩ := by
  let lZ : L → Module.End ℂ Z := fun k => (l k).restrict (hZ k)
  have hBl : ∀ k, B.comap Z.subtype ≤ (B.comap Z.subtype).comap (lZ k) := by
    intro k z hz
    show Z.subtype (lZ k z) ∈ B
    exact hB k z hz
  let lQ : L → Module.End ℂ (Z ⧸ B.comap Z.subtype) :=
    fun k => (B.comap Z.subtype).mapQ (B.comap Z.subtype) (lZ k) (hBl k)
  have hP : ∀ (y : FreeAlgebra ℂ L) (z : Z),
      FreeAlgebra.lift ℂ l y (z : C) = ((FreeAlgebra.lift ℂ lZ y z : Z) : C) := by
    intro y
    induction y using FreeAlgebra.induction
    · intro z; simp
    · intro z; rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]; rfl
    · rename_i a b ha hb
      intro z; simp only [map_mul, Module.End.mul_apply, hb, ha]
    · rename_i a b ha hb
      intro z; simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb]
  have hQ : ∀ (y : FreeAlgebra ℂ L) (z : Z),
      FreeAlgebra.lift ℂ lQ y (Submodule.Quotient.mk z) = Submodule.Quotient.mk (FreeAlgebra.lift ℂ lZ y z) := by
    intro y
    induction y using FreeAlgebra.induction
    · intro z; simp
    · intro z; rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]; rfl
    · rename_i a b ha hb
      intro z; simp only [map_mul, Module.End.mul_apply, hb, ha]
    · rename_i a b ha hb
      intro z; simp only [map_add (f := _), LinearMap.add_apply, Submodule.Quotient.mk_add, ha, hb]
  refine ⟨FreeAlgebra.lift ℂ lQ, fun y z => ⟨by rw [hP y z]; exact (FreeAlgebra.lift ℂ lZ y z).2, ?_⟩⟩
  rw [hQ y z]
  congr 1
  exact Subtype.ext (hP y z).symm

end GlobalTheory.CompanionTheory.RgCOBlock.QuotAction
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotientStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_algebra_action_on_subquotient : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (L : Type) (l : L → Module.End ℂ C)
    (Z B : Submodule ℂ C), (∀ k, ∀ z ∈ Z, l k z ∈ Z) → (∀ k, ∀ z ∈ B, l k z ∈ B) →
    ∃ ρ : FreeAlgebra ℂ L →ₐ[ℂ] Module.End ℂ (Z ⧸ B.comap Z.subtype),
      ∀ (y : FreeAlgebra ℂ L) (z : Z), ∃ hz : FreeAlgebra.lift ℂ l y (z : C) ∈ Z,
        ρ y (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨FreeAlgebra.lift ℂ l y (z : C), hz⟩ := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends | exact GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp

open Finset
open CompanionTheory.D.LK (Pos Cn ann cre lift sg)
open CompanionTheory.RgExh.U

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_ann_ne (i k : Pos n) (x : Cn n V) (A : Finset (Pos n))
    (h : (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  change (if k ∈ A then sg k A • (if i ∈ A.erase k then 0 else
    sg i (A.erase k) • x (insert i (A.erase k))) else 0) ≠ 0 at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · rw [if_pos hk, if_pos hi, smul_zero] at h
      exact absurd rfl h
    · refine ⟨hk, hi, fun hx => ?_⟩
      rw [if_pos hk, if_neg hi, hx, smul_zero, smul_zero] at h
      exact h rfl
  · rw [if_neg hk] at h
    exact absurd rfl h

theorem lF_ne (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n))
    (h : lF E p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ i k : Pos n, adC p q i k ≠ 0 ∧ (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hall⟩ := hcon
  apply h
  change ((lift n (E p q) + adL p q : Module.End ℂ (Cn n V)) x) A = 0
  rw [LinearMap.add_apply, Pi.add_apply, CompanionTheory.D.LK.lift_apply, h0, map_zero, zero_add]
  unfold adL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply]
  by_cases hc : adC p q i k = 0
  · rw [hc, zero_smul]
  · rw [hall i k hc, smul_zero]

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  unfold adC at h
  unfold inU at hi ⊢
  by_cases h1 : q = (i : Fin n × Fin n).1 ∧ (k : Fin n × Fin n) = (p, (i : Fin n × Fin n).2)
  · rw [h1.2]
    show lev p < lev (i : Fin n × Fin n).2
    rw [hpq, h1.1]
    exact hi
  · by_cases h2 : (i : Fin n × Fin n).2 = p ∧ (k : Fin n × Fin n) = ((i : Fin n × Fin n).1, q)
    · rw [h2.2]
      show lev (i : Fin n × Fin n).1 < lev q
      rw [← hpq, ← h2.1]
      exact hi
    · rw [if_neg h1, if_neg h2, sub_zero] at h
      exact absurd rfl h

theorem lF_suppIn_deg (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (_hlev : Monotone lev) (x : Cn n V)
    (hx : SuppIn (inU lev) x) (p q : Fin n) (hpq : lev p = lev q) :
    SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  unfold SuppIn at hx ⊢
  unfold Deg
  constructor
  · intro A hA l hl
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hx A h0 l hl
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hsupp := hx _ hx'
      by_cases hlk : l = k
      · subst hlk
        exact inU_of_adC hpq hc (hsupp i (Finset.mem_insert_self _ _))
      · exact hsupp l (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hlk, hl⟩))
  · intro j hj A hA
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hj A h0
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hcard := hj _ hx'
      rw [Finset.card_insert_of_notMem hi, Finset.card_erase_of_mem hk] at hcard
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨k, hk⟩
      omega

end GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegreeStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_preserves_support_degree : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q, lev p = lev q → SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | exact GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.lF_suppIn_deg <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem ev_fa {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    ev E (fa n Y) = qdet E (Y + ((n : ℂ) - 1) / 2) := by
  unfold fa
  rw [map_qdet]
  congr 1
  funext p q
  simp [ev]

theorem evL_fb {n M : ℕ} (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n)
    (hlev : ∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ))
    {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    evL lev E (fb d h Y) = (List.ofFn fun i : Fin M =>
      qdet (fun p q : Fin (d i) => E (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩))
        (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2)).prod := by
  unfold fb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  rw [Function.comp_apply, map_qdet, shift, add_sub_assoc]
  congr 1
  funext p q
  simp [evL, hlev]

theorem span_apply_sum {n : ℕ} (lev : Fin n → ℕ) (hm : Monotone lev) {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (r : Fin n → Fin n → Prop) (hr : ∀ p q, r p q → lev p < lev q)
    {y : Module.End ℂ V}
    (hy : y ∈ Submodule.span ℂ {y : Module.End ℂ V | ∃ (p q : Fin n) (w : Module.End ℂ V), r p q ∧ y = E p q * w})
    (x : V) : ∃ w : Pos n → V, y x = ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, hpq, rfl⟩ := hy
    have hl := hr p q hpq
    have hlt : p < q := by
      by_contra hc
      exact absurd (hm (not_lt.mp hc)) (not_le.mpr hl)
    classical
    refine ⟨Pi.single (⟨(p, q), hlt⟩ : Pos n) (w x), ?_⟩
    rw [Finset.sum_eq_single (⟨(p, q), hlt⟩ : Pos n)]
    · simp [inU, hl]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [LinearMap.add_apply, hu, hv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  | smul c a _ ha =>
    obtain ⟨u, hu⟩ := ha
    refine ⟨c • u, ?_⟩
    rw [LinearMap.smul_apply, hu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

theorem co_hyp : ∀ (n M : ℕ) (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ), Monotone lev →
    (∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (ev E (fa n Y))) ∧
      ∀ x : V, ∃ w : Pos n → V, ev E (fa n Y) x - evL lev E (fb d h Y) x =
        ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  intro n M lev d h Y hm hlev V _ _ E hE
  rw [ev_fa, evL_fb lev d h hlev]
  refine ⟨fun i _ => (Formalism.REAL.qDetCentral (Module.End ℂ V) n E hE _ i.1.1 i.1.2).symm, fun x => ?_⟩
  have hlevb : ∀ p : Fin n, lev p = ((blk (stdBlocks d h) p : Fin M) : ℕ) := by
    intro p
    have := hlev ((stdBlocks d h).symm p).1 ((stdBlocks d h).symm p).2
    simpa [blk] using this
  have hc := GlobalTheory.CapHC.qdet_blocks_congr (Module.End ℂ V) d h E hE Y
  obtain ⟨w, hw⟩ := span_apply_sum lev hm E (fun p q => blk (stdBlocks d h) p < blk (stdBlocks d h) q)
    (fun p q hpq => by rw [hlevb p, hlevb q]; exact hpq) hc x
  exact ⟨w, by rw [← hw, LinearMap.sub_apply]⟩

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifferenceStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_action_commutes_levi_difference : ∀ (n M : ℕ) (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ), Monotone lev →
    (∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (ev E (fa n Y))) ∧
      ∀ x : V, ∃ w : Pos n → V, ev E (fa n Y) x - evL lev E (fb d h Y) x =
        ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.co_hyp | exact GlobalTheory.CompanionTheory.RgCOBlock.co_hyp | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.co_hyp <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansion
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansion
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GroundTheory.BlockD.FourierDecayAlt.GaugeExists (qdetPoly tmPoly evU evU_apply evU_qdetPoly natDegree_qdetPoly_le
  coeff_qdetPoly_top prod_linear sum_fin_cast)

section Poly

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem poly_eq_zero_of_evU (Q : A[X]) (h : ∀ u : ℂ, evU u Q = 0) : Q = 0 := by
  ext j
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  let R : ℂ[X] := ∑ k ∈ range (Q.natDegree + 1), monomial k (φ (Q.coeff k))
  have hR : R = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 := congrArg φ (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [evU_apply, eval₂_eq_sum_range, map_sum, map_zero] at h1
    rw [eval_zero, ← h1]
    simp only [R, eval_finsetSum, eval_monomial, RingHom.id_apply, ← map_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have h2 := congrArg (fun p => p.coeff j) hR
  simp only [R, finsetSum_coeff, coeff_monomial, Finsupp.single_apply, coeff_zero, Finset.sum_ite_eq', mem_range] at h2
  split_ifs at h2 with hj
  · exact h2
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem commute_coeff_of_evU (P : A[X]) (a : A) (h : ∀ u : ℂ, Commute (evU u P) a) (j : ℕ) :
    Commute (P.coeff j) a := by
  have hC : ∀ u : ℂ, evU u (C a) = a := fun u => by simp [evU_apply]
  have hQ : P * C a - C a * P = 0 := poly_eq_zero_of_evU _ fun u => by
    rw [map_sub, map_mul, map_mul, hC, sub_eq_zero]
    exact h u
  have h2 := congrArg (fun p => p.coeff j) hQ
  simp only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero] at h2
  exact sub_eq_zero.1 h2

theorem coeff_qdetPoly_mem {n : ℕ} (E : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (hS : ∀ p q, E p q ∈ S) (j : ℕ) : (qdetPoly E).coeff j ∈ S := by
  let f : S →+* A := S.val.toRingHom
  have hC : ∀ a ∈ S, C a ∈ liftsRing f := fun a ha => by
    rw [← lifts_iff_liftsRing]
    exact C_mem_lifts f ⟨a, ha⟩
  have hX : (X : A[X]) ∈ liftsRing f := by
    rw [← lifts_iff_liftsRing]
    exact X_mem_lifts f
  have hT : ∀ (k : ℕ) (a b : Fin n), tmPoly E k a b ∈ liftsRing f := fun k a b => by
    unfold tmPoly
    refine add_mem ?_ (hC _ (hS a b))
    split_ifs
    · exact sub_mem hX (hC _ (S.algebraMap_mem _))
    · exact zero_mem _
  have hP : qdetPoly E ∈ liftsRing f := by
    unfold qdetPoly
    refine sum_mem fun σ _ => mul_mem (hC _ (intCast_mem S _)) ?_
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hT _ _ _
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at hP
  obtain ⟨y, hy⟩ := hP j
  rw [← hy]
  exact y.2

end Poly

theorem capelli_coef_commute : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (M : ℕ) (d : Fin M → ℕ) (X : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W), (∀ i, GlRel (X i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (X i p q) (X j r v)) → ∃ c : Fin M → ℕ → Module.End ℂ W, (∀ i, c i (d i) = 1) ∧ (∀ i (u : ℂ), qdet (X i) u = ∑ j ∈ Finset.range (d i + 1), u ^ j • c i j) ∧ (∀ i, 1 ≤ d i → c i (d i - 1) = ∑ p, X i p p - (((d i : ℂ) * ((d i : ℂ) - 1) / 2)) • (1 : Module.End ℂ W)) ∧ ∀ i j a b, Commute (c i a) (c j b) := by
  intro W _ _ M d X hgl hcomm
  have hL : ∀ i a p q, Commute ((qdetPoly (X i)).coeff a) (X i p q) := fun i a p q =>
    commute_coeff_of_evU _ _ (fun u => by
      rw [evU_qdetPoly]
      exact Formalism.REAL.qDetCentral _ _ (X i) (hgl i) u p q) a
  have hL2 : ∀ i j a r v, Commute ((qdetPoly (X i)).coeff a) (X j r v) := by
    intro i j a r v
    by_cases hij : i = j
    · subst hij
      exact hL i a r v
    · have hm := coeff_qdetPoly_mem (X i) (Subalgebra.centralizer ℂ {X j r v}) (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hcomm i j hij p q r v).symm.eq) a
      rw [Subalgebra.mem_centralizer_iff] at hm
      exact (hm _ rfl).symm
  refine ⟨fun i j => (qdetPoly (X i)).coeff j, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨-, htop, -⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i) = 1
    rw [coeff_qdetPoly_top _ _ (by omega), htop]
  · intro i u
    rw [← evU_qdetPoly (X i) u, evU_apply,
      eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le (X i)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, ← map_pow]
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm
  · intro i hi
    obtain ⟨-, -, hsub⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i - 1) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_qdetPoly_top _ _ (by omega), hsub (d i - 1) (by omega), Finset.sum_sub_distrib,
      ← map_sum, sum_fin_cast, Algebra.algebraMap_eq_smul_one]
  · intro i j a b
    have hm := coeff_qdetPoly_mem (X j) (Subalgebra.centralizer ℂ {(qdetPoly (X i)).coeff a})
      (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hL2 i j a p q).eq) b
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm _ rfl

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansionStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_coefficients_expansion : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (M : ℕ) (d : Fin M → ℕ) (X : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W), (∀ i, GlRel (X i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (X i p q) (X j r v)) → ∃ c : Fin M → ℕ → Module.End ℂ W, (∀ i, c i (d i) = 1) ∧ (∀ i (u : ℂ), qdet (X i) u = ∑ j ∈ Finset.range (d i + 1), u ^ j • c i j) ∧ (∀ i, 1 ≤ d i → c i (d i - 1) = ∑ p, X i p p - (((d i : ℂ) * ((d i : ℂ) - 1) / 2)) • (1 : Module.End ℂ W)) ∧ ∀ i j a b, Commute (c i a) (c j b) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute | exact GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LabelTracking
open Finset

namespace GlobalTheory.CompanionTheory.Labels

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec.J

variable {n : ℕ}

theorem tie_step {χ₀ χ : Fin n → ℂ} {t : Fin n}
    (hT : ∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) (hg : ∀ r, χ r ≠ χ t + 1) :
    ∀ r s, r ≠ s → (χ + Pi.single t 1 : Fin n → ℂ) r = (χ + Pi.single t 1 : Fin n → ℂ) s →
      (χ + Pi.single t 1 : Fin n → ℂ) r = χ₀ r ∧ (χ + Pi.single t 1 : Fin n → ℂ) s = χ₀ s := by
  intro r s hrs h
  by_cases hr : r = t
  · subst hr
    have hs : s ≠ r := hrs.symm
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hs, add_zero] at h
    exact absurd h.symm (hg s)
  by_cases hs : s = t
  · subst hs
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hr, add_zero] at h
    exact absurd h (hg r)
  simp only [Pi.add_apply, Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hs, add_zero] at h ⊢
  exact hT r s hrs h

theorem apply_swap_of_eq (χ : Fin n → ℂ) {r s : Fin n} (h : χ r = χ s) (i : Fin n) :
    χ i = χ (Equiv.swap r s i) := by
  by_cases h1 : i = r
  · subst h1; simp [h]
  by_cases h2 : i = s
  · subst h2; simp [h]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem sum_filter_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) (a : Fin 3) :
    ∑ i ∈ univ.filter (fun i => (L ∘ Equiv.swap r s) i = a), χ i = ∑ i ∈ univ.filter (fun i => L i = a), χ i :=
  Finset.sum_equiv (Equiv.swap r s) (by simp) fun i _ => apply_swap_of_eq χ h i

theorem deg_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) :
    deg χ (L ∘ Equiv.swap r s) = deg χ L := by
  simp only [deg, sum_filter_swap χ L h]

theorem isLabel_swap {j : ℕ} {L : Fin n → Fin 3} (h : IsLabel j L) (r s : Fin n) :
    IsLabel j (L ∘ Equiv.swap r s) := by
  intro a
  rw [← h a]
  exact Finset.card_equiv (Equiv.swap r s) (by simp)

theorem moved_labels (χ₀ : Fin n → ℂ) (j : ℕ) : ∀ (ss : List (Fin n)) (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)),
    GoodPath χ ss → (∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) →
    (∀ L ∈ Λ, IsLabel j L ∧ (deg χ₀ L).re < 0) →
    ∀ L ∈ moveIter χ Λ ss, IsLabel j L ∧ (deg χ₀ L).re < 0 := by
  intro ss
  induction ss with
  | nil =>
    intro χ Λ _ _ hΛ L hL
    exact hΛ L hL
  | cons t ss ih =>
    intro χ Λ hg hT hΛ L hL
    refine ih (χ + Pi.single t 1) (move χ Λ t) hg.2 (tie_step hT hg.1) ?_ L hL
    rintro _ ⟨L₀, hL₀, r, hr, rfl⟩
    obtain ⟨hl, hd⟩ := hΛ L₀ hL₀
    refine ⟨isLabel_swap hl r t, ?_⟩
    by_cases hrt : r = t
    · subst hrt
      simpa using hd
    · obtain ⟨h1, h2⟩ := hT r t hrt hr
      rw [deg_swap χ₀ L₀ (h1.symm.trans (hr.trans h2))]
      exact hd

theorem labelTrack : LabelTrack := by
  intro n χ ss B j hg hf L hL
  obtain ⟨hl, hd⟩ := moved_labels χ j ss χ _ hg (fun _ _ _ _ => ⟨rfl, rfl⟩) (fun _ h => h) L hL
  refine hf (univ.filter fun s => L s = 2) (univ.filter fun s => L s = 0) ?_ ?_ hd
  · refine Finset.disjoint_filter.2 fun x _ h1 h2 => ?_
    rw [h1] at h2
    exact absurd h2 (by decide)
  · rw [hl 2, hl 0]
    simp [dims]

end GlobalTheory.CompanionTheory.Labels
end

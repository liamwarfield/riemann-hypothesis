module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjPowOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteFiniteCount
open NumberField MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount

open Formalism.MainNotions.S GlobalTheory.Count

def DefiniteHyp (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ) : Prop :=
  IsDSData B d ∧ SigIs B p 0 ∧ 1 ≤ p ∧ 1 ≤ B.g ∧ B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E

theorem DefiniteHyp.rank_eq {B : RowsAut} {d : InfinitePlace B.I.F → ℝ} {p : ℕ}
    (h : DefiniteHyp B d p) : B.I.n = p := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  obtain ⟨hp, hq⟩ := h.2.1 v
  unfold AutInst.pAt at hp
  unfold AutInst.qAt at hq
  have hall : ∀ a, B.I.ε v a = true := by
    intro a
    by_contra ha
    have hm : a ∈ (Finset.univ.filter fun a => B.I.ε v a = false) := by
      simpa using ha
    rw [Finset.card_eq_zero.mp hq] at hm
    simp at hm
  rw [← hp, Finset.filter_true_of_mem fun a _ => hall a]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanProperties
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Count.CartanSize

open GlobalTheory.Count.Cartan

theorem cartan_size : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  intro n ε
  have hU : ∀ g : UJ ε, Formalism.REAL.inUJ ε (uMat g) := fun g => g.2
  have hnn : ∀ g : Matrix (Fin n) (Fin n) ℂ, 0 ≤ dHS g := fun g => Real.sqrt_nonneg _
  obtain ⟨-, hB, -, hC, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro g
    refine ⟨hnn _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.Dec.dOp_fin_zero]
      exact hnn _
    · obtain ⟨h0, -, -, h2, -⟩ := hB g g (by omega)
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
  · intro g
    exact ⟨uMat g * NormedSpace.exp (-Formalism.REAL.polarLog (uMat g)), Formalism.REAL.mul_exp_neg_polarLog_mem_compact (hU g),
      Formalism.REAL.polarLog (uMat g), Formalism.REAL.polarLog_mem_hermitian_part (hU g), Formalism.REAL.polar_decomposition_eq,
      GlobalTheory.Count.Cartan.dHS_eq_log (hU g)⟩
  · intro hr g
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dHS]
    · obtain ⟨-, -, -, -, h3⟩ := hB g g (by omega)
      simp only [hr, Nat.cast_zero, mul_zero, Real.sqrt_zero, zero_mul] at h3
      exact le_antisymm h3 (hnn _)

end GlobalTheory.Count.CartanSize
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanPropertiesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  first | exact @GlobalTheory.Count.CartanSize.cartan_size | exact GlobalTheory.Count.CartanSize.cartan_size | (intros; apply GlobalTheory.Count.CartanSize.cartan_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrankStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E → (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  first | exact @GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | exact GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | (intros; apply GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentIsometryDefiniteEqOne
open Matrix Finset Real

namespace GlobalTheory


open scoped ComplexOrder in
theorem unipotent_isometry_definite_eq_one :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), c ≠ 0 → Aᴴ * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * A = c • 1 → (A - 1) ^ m = 0 → A = 1 := by
  intro n m A c hc hA hm

  have hU : Aᴴ * A = 1 := by
    have h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_right_injective _ hc h1
  have hU' : A * Aᴴ = 1 := mul_eq_one_comm.mp hU

  have hcomm : Commute (A - 1)ᴴ (A - 1) := by
    show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU',
      one_mul, mul_one]
    abel
  have hN : (A - 1) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]

  have hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0 := by
    rw [hcomm.mul_pow, hN, mul_zero]
  have key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro hk
      apply ih
      have h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_pow, hBh, ← pow_add,
          show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTerm
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem GFset_eq_one_of_place (I : AutInst) (γ : I.GA) (hγ : γ ∈ I.GFset) (v : InfinitePlace I.F)
    (h : uMat (γ.1 v) = 1) : γ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hγ
  have hdet : ∀ w, IsUnit (I.P w).det := fun w => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit w)
  set M : Matrix (Fin I.n) (Fin I.n) I.E := (g : Matrix (Fin I.n) (Fin I.n) I.E) with hM
  have e1 : (I.P v)⁻¹ * M.map (I.φ v) * I.P v = 1 := (hinf v).symm.trans h
  have e2 : M.map (I.φ v) * I.P v = I.P v := by
    have := congrArg (I.P v * ·) e1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hdet v)] using this
  have e3 : M.map (I.φ v) = 1 := by
    have := congrArg (· * (I.P v)⁻¹) e2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v)] using this
  have hg : M = 1 := by
    apply Matrix.map_injective (I.φ v).injective
    dsimp only
    rw [e3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext (funext fun w => ?_) ?_
  · have hw : uMat (γ.1 w) = 1 := by
      rw [hinf w, hg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (hdet w)]
    exact Subtype.ext (Units.ext (by simpa using hw))
  · have hf : I.fmat γ.2 = 1 := by
      rw [hfin, hg, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (Units.ext (by simpa using hf))

theorem one_mem_GFset_def (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))]
    rfl
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem definite_count_of_finite : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) →
      (B.D : ℝ) = mainTerm B d := by
  intro B d p hH hfin
  have hn : B.I.n = p := hH.rank_eq
  obtain ⟨hDS, hSig, hp, -, hprime, hgt, hsplit⟩ := hH
  have hn1 : 1 ≤ B.I.n := hn ▸ hp

  have hq : ∀ v, (univ.filter fun a => B.I.ε v a = false).card = 0 := fun v => (hSig v).2
  have hrk : ∀ v, rkR (B.I.ε v) = 0 := fun v => by
    unfold rkR
    rw [hq v]
    exact Nat.min_zero _
  have hpos : ∀ v a, B.I.ε v a = true := fun v a => by
    by_contra hne
    have ha : a ∈ univ.filter fun a => B.I.ε v a = false := by simpa using hne
    rw [Finset.card_eq_zero.mp (hq v)] at ha
    exact Finset.notMem_empty a ha
  have hJ : ∀ v, Formalism.REAL.Jm (B.I.ε v) = 1 := fun v => by
    unfold Formalism.REAL.Jm
    simp [hpos v]
  have hunit : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), (uMat g)ᴴ * uMat g = 1 := fun v g => by
    have h0 : (uMat g)ᴴ * Formalism.REAL.Jm (B.I.ε v) * uMat g = Formalism.REAL.Jm (B.I.ε v) := g.2
    rwa [hJ v, Matrix.mul_one] at h0
  have hdHS : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), dHS (uMat g) = 0 := fun v g =>
    (GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties B.I.n (B.I.ε v)).2.2.2 (hrk v) g

  have hrad := GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank B.I.E B.g₀ hprime hsplit
  have hNU := (GlobalTheory.NearElement.near_unipotent B d (1 / 10 ^ 5) (by norm_num) le_rfl hn1 hgt hrad _ _
    rfl rfl).1
  have hkey : ∀ x γ : B.I.GA, γ ∈ B.I.GFset → phe B d (x⁻¹ * γ * x) ≠ 0 → γ = 1 := by
    intro x γ hγ hne
    have hep : (0 : ℝ) ≤ 1 / 10 ^ 5 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) := by positivity
    obtain ⟨-, hu, -⟩ := hNU x γ ⟨hγ, hne, fun v => by rw [hdHS]; exact hep⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    apply GFset_eq_one_of_place B.I γ hγ v
    apply GlobalTheory.unipotent_isometry_definite_eq_one B.I.n B.I.n _ 1 one_ne_zero _ (hu v)
    simpa using hunit v (γ.1 v)

  have hker : ∀ x, kern B.I (phe B d) x x = phe B d 1 := by
    intro x
    unfold kern
    rw [tsum_eq_single (⟨1, one_mem_GFset_def B.I⟩ : B.I.GFset)]
    · simp
    · intro γ hγ
      by_contra hne
      exact hγ (Subtype.ext (hkey x γ.1 γ.2 hne))
  have hph1 : ph B d 1 = ((∏ v, d v : ℝ) : ℂ) := by
    unfold ph
    have hc : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1 := by
      intro v
      have hs : B.σ v (uMat ((1 : B.I.Ginf) v)) = 1 := by
        rw [show uMat ((1 : B.I.Ginf) v) = 1 from rfl]
        exact (hDS v).2.1.2.2.1.1.1
      rw [hs, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, (hDS v).2.2.1.1]
      simp
    rw [Finset.prod_congr rfl (fun v _ => hc v)]
    simp

  have hloc : LocDec B 0 := by
    intro v g
    have hd : decE (rkR (B.I.ε v)) 0 (dOp (uMat g)) = 1 := by simp [decE]
    rw [hd]
    calc ‖⟪B.w v, B.σ v (uMat g) (B.w v)⟫_ℂ‖ ≤ ‖B.w v‖ * ‖B.σ v (uMat g) (B.w v)‖ :=
          norm_inner_le_norm _ _
      _ = 1 := by rw [(hDS v).2.1.2.2.1.2.1 _ g.2 _, (hDS v).2.2.1.1]; norm_num
  have hbig : HBig B 32 0 := by
    intro v
    rw [hrk v]
    simp
  obtain ⟨hcont, hbd, hmaj⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d 0 hDS hloc
  have hm := hmaj 0 le_rfl (fun v => Or.inl (hrk v))
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  have hint : Integrable (ph B d) (muInf B.I) :=
    hm.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  obtain ⟨T, hT⟩ := (GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hDS hint).2.2.1
  obtain ⟨-, -, -, -, -, -, -, hD, -⟩ := GlobalTheory.T.kernelB' B d 0 hDS hn1 hloc hbig hfin T hT
  simp_rw [hker] at hD
  rw [setIntegral_const] at hD
  have hphe : phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 := by
    show ph B d (1 : B.I.GA).1 * B.e (1 : B.I.GA).2 = _
    rw [Prod.fst_one, Prod.snd_one, hph1]
  rw [hphe] at hD
  have he1 := (GlobalTheory.rowsAut_idem_elementary B).1
  have hre := congrArg Complex.re hD
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, he1,
    mul_zero, sub_zero, zero_mul, Complex.natCast_re] at hre
  unfold mainTerm AutInst.Dstar AutInst.vol
  rw [← hre, measureReal_def]
  ring

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTermStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → (B.D : ℝ) = mainTerm B d := by
  first | exact @GlobalTheory.Dec.definite_count_of_finite | exact GlobalTheory.Dec.definite_count_of_finite | (intros; apply GlobalTheory.Dec.definite_count_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearAbsMeasurableAndSplit
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.NearMeas

theorem tsum_sub_eq {G : Type} (S T : Set G) (h : S ⊆ T) (f : G → ℝ≥0∞) :
    ∑' γ : S, f γ.1 = ∑' γ : T, S.indicator f γ.1 := by
  rw [tsum_subtype S f, tsum_subtype T (S.indicator f), Set.indicator_indicator,
    Set.inter_eq_right.mpr h]

private theorem continuous_ph' (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (ph B d) := by
  show Continuous fun g : B.I.Ginf =>
    ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)
  refine continuous_const.mul (continuous_star.comp (continuous_finsetProd _ fun v _ => ?_))
  obtain ⟨-, ⟨-, -, ⟨-, -, hcont⟩, -⟩, -⟩ := h v
  have hmat : Continuous fun g : B.I.Ginf => uMat (g v) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
  have hc : Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) :=
    (hcont (B.w v)).comp_continuous hmat fun g => (g v).2
  exact continuous_const.inner hc

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (phe B d) := by
  obtain ⟨hlc, -⟩ := B.e_adm
  show Continuous fun x : B.I.GA => ph B d x.1 * B.e x.2
  exact ((continuous_ph' B d h).comp continuous_fst).mul (hlc.continuous.comp continuous_snd)

private theorem continuous_conj_by_inv (B : RowsAut) (γ : B.I.GA) :
    Continuous fun x : B.I.GA => x⁻¹ * γ * x :=
  (continuous_inv.mul continuous_const).mul continuous_id

private theorem measurable_indicator_nearNe_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d)
    (γ : B.I.GA) :
    Measurable fun x : B.I.GA =>
      {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
        (fun x => ‖phe B d (x⁻¹ * γ * x)‖ₑ) x := by
  have hc : Continuous fun x : B.I.GA => phe B d (x⁻¹ * γ * x) :=
    (continuous_phe B d h).comp (continuous_conj_by_inv B γ)
  have hd : ∀ v, Continuous fun x : B.I.GA => dHS (uMat ((x⁻¹ * γ * x).1 v)) := fun v =>
    (GlobalTheory.Count.CartanSize.cartan_size _ (B.I.ε v)).1.comp
      ((continuous_apply v).comp (continuous_fst.comp (continuous_conj_by_inv B γ)))
  have hcl : IsClosed {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le (hd v) continuous_const
  have hne : MeasurableSet {x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} :=
    hc.measurable (measurableSet_singleton 0).compl
  have hset : MeasurableSet {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} := by
    have heq : {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} =
        ({x : B.I.GA | γ ∈ B.I.GFset} ∩ ({x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} ∩
          {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B})) ∩ {x : B.I.GA | γ ≠ 1} := by
      ext x
      rfl
    rw [heq]
    exact ((MeasurableSet.const _).inter (hne.inter hcl.measurableSet)).inter (MeasurableSet.const _)
  exact Measurable.indicator hc.enorm.measurable hset

theorem nearAbs_measurable_and_split : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) ∧ ∀ x : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * x)‖) → ENNReal.ofReal ‖kern B.I (phe B d) x x - phe B d 1‖ ≤ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
  intro B d h
  classical
  refine ⟨?_, ?_⟩
  · have hcount : Countable B.I.GFset := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    have heq : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d = fun x => ∑' γ : B.I.GFset,
        {x : B.I.GA | γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
          (fun x => ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ) x := by
      funext x
      exact tsum_sub_eq (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x) B.I.GFset (fun γ hγ => hγ.1.1)
        (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)
    rw [heq]
    exact Measurable.tsum fun γ => measurable_indicator_nearNe_phe B d h γ.1
  · intro x hsum
    have hone : (1 : B.I.GA) ∈ B.I.GFset := (GlobalTheory.RatDiscrete.ratSub B.I).one_mem
    let o : B.I.GFset := ⟨1, hone⟩
    have hs : Summable fun γ : B.I.GFset => phe B d (x⁻¹ * γ.1 * x) := hsum.of_norm
    have hk : kern B.I (phe B d) x x = ∑' γ : B.I.GFset, phe B d (x⁻¹ * γ.1 * x) := rfl
    have h1 : phe B d 1 = phe B d (x⁻¹ * o.1 * x) := by simp [o]
    rw [hk, h1, hs.tsum_eq_add_tsum_ite o, add_sub_cancel_left]
    have hgn : Summable fun γ : B.I.GFset =>
        ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ := by
      refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun γ => ?_
      by_cases hγ : γ = o <;> simp [hγ]
    have hsub1 : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ B.I.GFset := fun γ hγ => hγ.1.1
    have hsub2 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x ⊆ B.I.GFset := fun γ hγ => hγ.1
    calc ENNReal.ofReal ‖∑' γ : B.I.GFset, if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖
        ≤ ENNReal.ofReal (∑' γ : B.I.GFset,
            ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hgn)
      _ = ∑' γ : B.I.GFset, ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hgn]
          simp only [ofReal_norm]
      _ ≤ ∑' γ : B.I.GFset,
            ((GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x).indicator (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1 +
              (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x).indicator
                (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1) := by
          refine ENNReal.tsum_le_tsum fun γ => ?_
          by_cases hγ : γ = o
          · simp [hγ]
          have hγ1 : γ.1 ≠ 1 := fun h' => hγ (Subtype.ext h')
          rw [if_neg hγ]
          by_cases hn : IsNear B d (epN B) x γ.1
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x := ⟨hn, hγ1⟩
            rw [Set.indicator_of_mem hm]
            exact le_self_add
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x := ⟨γ.2, hn⟩
            rw [Set.indicator_of_mem hm]
            exact le_add_self
      _ = GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
          rw [ENNReal.tsum_add]
          exact congrArg₂ (· + ·)
            (tsum_sub_eq _ _ hsub1 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm
            (tsum_sub_eq _ _ hsub2 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm

end GlobalTheory.NearMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSubLeExpNegSixteenthMul
open Matrix Finset Real

namespace GlobalTheory

theorem abs_sub_le_exp_neg_sixteenth_mul :
    ∀ (D Ds n f : ℝ), 0 ≤ D → 0 ≤ Ds → Real.exp 15 ≤ n → 1 ≤ f → |D - Ds| ≤ (2 * Real.exp (-(1 / 4) * n * f * Real.log n) + Real.exp (-n ^ 2 * f)) * Ds + Real.exp (-n ^ 2 * f) * D → |D - Ds| ≤ Real.exp (-(1 / 16) * n * f * Real.log n) * Ds := by
  intro D Ds n f hD hDs hn hf h
  have hn16 : (16:ℝ) ≤ n := by
    have := Real.add_one_le_exp (15:ℝ); linarith
  have hn0 : 0 < n := by linarith
  have hL : 15 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 15) hn
    rwa [Real.log_exp] at this
  have hLn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hnf : 16 ≤ n * f := by nlinarith
  have ha : 240 ≤ n * f * Real.log n := by nlinarith
  have hnn : n * f * Real.log n ≤ n ^ 2 * f := by
    have := mul_le_mul_of_nonneg_left hLn (by linarith : (0:ℝ) ≤ n * f)
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8); linarith
  have hT8 : Real.exp (-(1 / 16) * n * f * Real.log n - Real.log 8) =
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have e1 : Real.exp (-(1 / 4) * n * f * Real.log n) ≤
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have e2 : Real.exp (-n ^ 2 * f) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have hT1 : Real.exp (-(1 / 16) * n * f * Real.log n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; nlinarith
  have hδ0 : 0 ≤ Real.exp (-n ^ 2 * f) := (Real.exp_pos _).le
  have hδ : Real.exp (-n ^ 2 * f) ≤ 1 / 2 := by linarith
  have hX : 0 ≤ |D - Ds| := abs_nonneg _
  have hD' : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have p1 := mul_le_mul_of_nonneg_left hD' hδ0
  have p2 := mul_le_mul_of_nonneg_right hδ hX
  have p3 := mul_le_mul_of_nonneg_right e1 hDs
  have p4 := mul_le_mul_of_nonneg_right e2 hDs
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsIntegralSubConstMulLeOfSplit
open MeasureTheory

namespace GlobalTheory

theorem abs_integral_sub_const_mul_le_of_split :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (M : Set X) (K : X → ℝ) (nr fr : X → ENNReal) (c a b e : ℝ), MeasurableSet M → Integrable K μ → (∀ x, 0 ≤ K x) → Measurable nr → 0 ≤ c → 0 ≤ a → 0 ≤ b → 0 ≤ e → (∀ x ∈ M, ENNReal.ofReal |K x - c| ≤ nr x + fr x) → ∫⁻ x in M, nr x ∂μ ≤ ENNReal.ofReal a → ∫⁻ x in M, fr x ∂μ ≤ ENNReal.ofReal b → ∫⁻ x in Mᶜ, ENNReal.ofReal (K x) ∂μ ≤ ENNReal.ofReal e → |∫ x, K x ∂μ - c * (μ Set.univ).toReal| ≤ a + b + c * (μ Mᶜ).toReal + e := by
  intro X _ μ _ M K nr fr c a b e hM hK hK0 hnr hc ha hb he hpt hna hfb hce
  have hsplit : ∫ x, K x ∂μ = ∫ x in M, K x ∂μ + ∫ x in Mᶜ, K x ∂μ :=
    (integral_add_compl hM hK).symm
  have hmeas : (μ Set.univ).toReal = (μ M).toReal + (μ Mᶜ).toReal := by
    rw [← measure_add_measure_compl hM,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hintM : ∫ x in M, (K x - c) ∂μ = ∫ x in M, K x ∂μ - c * (μ M).toReal := by
    rw [integral_sub hK.integrableOn (integrable_const c), setIntegral_const, smul_eq_mul,
      measureReal_def, mul_comm]

  have h1 : |∫ x in M, (K x - c) ∂μ| ≤ a + b := by
    have hle : ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ENNReal.ofReal (a + b) := by
      calc ∫⁻ x in M, ENNReal.ofReal ‖K x - c‖ ∂μ ≤ ∫⁻ x in M, (nr x + fr x) ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hM] with x hx
            simpa [Real.norm_eq_abs] using hpt x hx
        _ = ∫⁻ x in M, nr x ∂μ + ∫⁻ x in M, fr x ∂μ := lintegral_add_left hnr _
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add hna hfb
        _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
    have hn := norm_integral_le_lintegral_norm (μ := μ.restrict M) (fun x => K x - c)
    rw [Real.norm_eq_abs] at hn
    exact hn.trans (ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hb) hle)

  have h2 : ∫ x in Mᶜ, K x ∂μ ≤ e := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hK0)
      hK.integrableOn.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal he hce
  have h3 : 0 ≤ ∫ x in Mᶜ, K x ∂μ := integral_nonneg fun x => hK0 x
  have h4 : 0 ≤ c * (μ Mᶜ).toReal := mul_nonneg hc ENNReal.toReal_nonneg
  have key : ∫ x, K x ∂μ - c * (μ Set.univ).toReal =
      ∫ x in M, (K x - c) ∂μ + (∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal) := by
    rw [hsplit, hmeas, hintM]; ring
  rw [key]
  calc _ ≤ |∫ x in M, (K x - c) ∂μ| + |∫ x in Mᶜ, K x ∂μ - c * (μ Mᶜ).toReal| := abs_add_le _ _
    _ ≤ (a + b) + (c * (μ Mᶜ).toReal + e) := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ = a + b + c * (μ Mᶜ).toReal + e := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBounds
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountSum

theorem countHyp_mono {B : RowsAut} {Cg : ℝ} {n₀ n₁ : ℕ} {d : InfinitePlace B.I.F → ℝ} {p q : ℕ} {b : ℝ}
    (h : CountHyp B Cg n₀ d p q b) (hn : n₁ ≤ n₀) : CountHyp B Cg n₁ d p q b :=
  ⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩

theorem countingTheorem_of_finite_of_bounds :
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound →
    GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hfinC hflag hpt hnear hfar hrare hdeep Cg
  by_cases hC : 0 ≤ Cg
  swap
  · exact ⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩
  obtain ⟨n₁, hn₁⟩ := hnear Cg hC
  obtain ⟨n₂, hn₂⟩ := hfar Cg hC
  obtain ⟨n₃, hn₃⟩ := hrare
  obtain ⟨n₄, hn₄⟩ := hdeep Cg hC
  refine ⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩
  have hfin := hfinC B Cg _ d p q b (by omega) H
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H
  have H1 := countHyp_mono H (n₁ := n₁) (by omega)
  have H2 := countHyp_mono H (n₁ := n₂) (by omega)
  have H4 := countHyp_mono H (n₁ := n₄) (by omega)
  obtain ⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩ := H
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e := GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin
    rw [← e, sub_self, abs_zero]
    positivity
  have hn1 : 1 ≤ B.I.n := by omega
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  obtain ⟨-, -, hphe1, him, hre, -, hloc⟩ := hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)
  obtain ⟨-, hv0, hvT, -⟩ := hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc
  have hI : Integrable (ph B d) (muInf B.I) := by
    have h0 := hint 0 le_rfl (fun v => Or.inr (by
      have h1 := h32 v
      rw [hrk v] at h1 ⊢
      have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
      have hqn : (q : ℝ) < B.I.n := by exact_mod_cast (by omega : q < B.I.n)
      have hn0 : (0 : ℝ) < B.I.n := by exact_mod_cast hn1
      have := mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)
      nlinarith))
    simp only [zero_mul, Real.exp_zero, mul_one] at h0
    exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hDS hI
  obtain ⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩ := GlobalTheory.T.kernelB' B d h hDS hn1 hloc h32 hfin T hT
  obtain ⟨hsum, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hDS hn1 hloc h32
  obtain ⟨hmeas, hsplit⟩ := GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS
  have hcl : Continuous (least B.I) := (GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1
  set μ := (B.I.muA B.μf).restrict B.fund with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩
  have hM : MeasurableSet {x | tauStar B q b ≤ least B.I x} :=
    (isClosed_le continuous_const hcl).measurableSet
  have hvol : 0 < B.I.vol B.μf B.fund := ENNReal.toReal_pos hv0.ne' hvT.ne
  have hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd.le hre
  have hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund := by
    unfold mainTerm AutInst.Dstar; ring
  have hm0 : 0 ≤ mainTerm B d := hmain ▸ mul_nonneg hc0 hvol.le
  have e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x} :=
    Set.inter_comm _ _
  have e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]
  have key := GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x}
    (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d)
    ((∏ v, d v) * (B.e 1).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d)
    (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)
    ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) hM hKi.re
    (fun x => by
      simp only [hexp, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)
    (fun x _ => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hphe1, Complex.re_ofReal_mul])
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)
    (by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)
  have hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ) := by
    have := integral_re hKi
    rw [hD] at this
    simpa using this
  have hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund := by
    rw [hμ, Measure.restrict_apply_univ]; rfl
  have hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund := by
    have h1 := hn₃ B p q hsig (by omega) hq2 hrd hlf
    unfold prob at h1
    rw [div_le_iff₀ hvol] at h1
    refine le_trans ?_ h1
    rw [hμ, Measure.restrict_apply hM.compl]
    refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne
      (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))
    have hx' : ¬ tauStar B q b ≤ least B.I x := hx
    exact lt_trans (not_le.1 hx') (hts hq).1
  rw [hKD, hU, ← hmain] at key
  have hP' := mul_le_mul_of_nonneg_left hP hc0
  have hne : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 (by omega)
  have fin := GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne
    (by exact_mod_cast hf1) (by
      refine key.trans ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
      simp only [neg_mul]
      rw [hmain] at *
      nlinarith [hP'])
  simpa only [neg_mul] using fin

end GlobalTheory.CountSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBoundsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds : (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) → GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds | exact GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds | (intros; apply GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds <;> assumption)
end

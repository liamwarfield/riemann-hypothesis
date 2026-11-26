module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf.MajMeas

variable {D : D7}

theorem norm_compAt_le_realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m)
    (j : Fin n) : ‖compAt θ τ x i j‖ ≤ realSize θ x := by
  unfold realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ', ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖ :=
        Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} :
    Continuous (realSize θ : Mx D m n → ℝ) := by
  unfold realSize
  refine continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_norm.comp ((GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j))

theorem finPart_eq_zero_iff {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (a : AE D) : finPart D a = 0 ↔ a = σ (fun τ => θ τ (infPart D a)) := by
  constructor
  · intro ha
    refine sub_eq_zero.1 (h.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, h.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, h.comp, sub_self]
  · intro ha
    rw [ha]
    exact h.fin _

theorem isClosed_finZero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (m n : ℕ) : IsClosed {z : Mx D m n | z.map (finPart D) = 0} := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have e : {z : Mx D m n | z.map (finPart D) = 0} =
      ⋂ i, ⋂ j, {z : Mx D m n | z i j = σ (fun τ => θ τ (infPart D (z i j)))} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hz i j
      have hz' := congrFun (congrFun hz i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at hz'
      exact (finPart_eq_zero_iff h _).1 hz'
    · intro hz
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact (finPart_eq_zero_iff h _).2 (hz i j)
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (continuous_id.matrix_elem i j) ?_
  exact h.cont.comp (continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp h.inf τ).comp (continuous_id.matrix_elem i j))

theorem setOf_inBox {m n : ℕ} (K : Set (Mx D m n)) :
    {x | InBox K x} = K + {z : Mx D m n | z.map (finPart D) = 0} := by
  ext x
  constructor
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, x - k, hx, add_sub_cancel k x⟩
  · rintro ⟨k, hk, z, hz, rfl⟩
    exact ⟨k, hk, by rwa [add_sub_cancel_left]⟩

theorem isClosed_inBox {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) : IsClosed {x | InBox K x} := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  rw [setOf_inBox]
  exact (isClosed_finZero h m n).add_left_of_isCompact hK

theorem isCompact_box {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (R : ℝ) :
    IsCompact {x | InBox K x ∧ realSize θ x ≤ R} := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  let B : Set (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let g : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) → Mx D m n := fun p =>
    p.1 + Matrix.of fun i j => σ (fun τ => p.2 τ i j - θ τ (infPart D (p.1 i j)))
  have hg : Continuous g := by
    refine continuous_fst.add (continuous_matrix fun i j => h.cont.comp (continuous_pi fun τ => ?_))
    have c1 : Continuous fun p : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) => p.2 τ i j := by fun_prop
    have c2 : Continuous fun p : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) => θ τ (infPart D (p.1 i j)) :=
      (GlobalTheory.FockCompare.continuous_comp h.inf τ).comp (continuous_fst.matrix_elem i j)
    exact c1.sub c2
  refine ((hK.prod hB).image hg).of_isClosed_subset
    ((isClosed_inBox h K hK).inter (isClosed_le (continuous_realSize h.inf) continuous_const)) ?_
  rintro x ⟨⟨k, hk, hx⟩, hR⟩
  refine ⟨(k, fun τ i j => θ τ (infPart D (x i j))), ⟨hk, fun τ _ i _ j _ => ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_compAt_le_realSize θ x τ i j).trans hR
  · ext i j
    have h0 := congrFun (congrFun hx i) j
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply] at h0
    have e := (finPart_eq_zero_iff h _).1 h0
    simp only [(infPart D).map_sub, (θ _).map_sub] at e
    show k i j + σ (fun τ => θ τ (infPart D (x i j)) - θ τ (infPart D (k i j))) = x i j
    rw [← e, add_sub_cancel]

theorem measurable_maj {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (N : ℕ) : Measurable (maj θ K N) := by
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  unfold maj
  exact Measurable.ite (isClosed_inBox h K hK).measurableSet
    ((continuous_const.add (continuous_realSize h.inf)).pow N).measurable.inv measurable_const

theorem exists_leftInv {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E)
    (hx : LinearIndependent D.host.E x.transpose) : ∃ y : Matrix (Fin n) (Fin m) D.host.E, y * x = 1 := by
  have hinj : Function.Injective x.mulVecLin := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective x.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  rwa [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {m n k : ℕ} (A : Mx D m n) (B : Mx D n k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem realSize_mul_le (θ : InfFam D) {m n k : ℕ} (Y : Mx D m n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : Mx D n k, realSize θ (Y * a) ≤ c * realSize θ a := by
  refine ⟨∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖, by positivity, fun a => ?_⟩
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

theorem maj_rat_le (θ : InfFam D) (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E)
    (hx : LinearIndependent D.host.E x.transpose) (K : Set (Mx D m k)) (hK : IsCompact K) :
    ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k,
      maj θ K N ((rat x : Mx D m n) * u) ≤ C * maj θ K' N u := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  obtain ⟨y, hy⟩ := exists_leftInv x hx
  have hyx : (rat y : Mx D n m) * rat x = 1 := by
    unfold rat
    rw [← Matrix.map_mul, hy, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c, hc0, hc⟩ := realSize_mul_le θ (k := k) (rat y : Mx D n m)
  refine ⟨(fun a => (rat y : Mx D n m) * a) '' K, hK.image (continuous_const.matrix_mul continuous_id),
    fun N => ⟨(1 + c) ^ N, fun u => ?_⟩⟩
  by_cases hb : InBox K ((rat x : Mx D m n) * u)
  · obtain ⟨k0, hk0, hkx⟩ := hb
    have hb' : InBox ((fun a => (rat y : Mx D n m) * a) '' K) u := by
      refine ⟨rat y * k0, ⟨k0, hk0, rfl⟩, ?_⟩
      have e : u - rat y * k0 = rat y * (rat x * u - k0) := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
      rw [e, Matrix.map_mul, hkx, Matrix.mul_zero]
    simp only [maj, if_pos (show InBox K ((rat x : Mx D m n) * u) from ⟨k0, hk0, hkx⟩), if_pos hb']
    have hs := hc ((rat x : Mx D m n) * u)
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul] at hs
    have h0 := realSize_nonneg θ ((rat x : Mx D m n) * u)
    have h0' := realSize_nonneg θ u
    have hle : 1 + realSize θ u ≤ (1 + c) * (1 + realSize θ ((rat x : Mx D m n) * u)) := by nlinarith
    have hA : 0 < (1 + realSize θ ((rat x : Mx D m n) * u)) ^ N := by positivity
    have hB : 0 < (1 + realSize θ u) ^ N := by positivity
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  · have e : maj θ K N ((rat x : Mx D m n) * u) = 0 := by simp only [maj, if_neg hb]
    rw [e]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N u)

end GlobalTheory.Unf.MajMeas


open GlobalTheory.Unf.MajMeas in
theorem GlobalTheory.Unf.maj_measurable_rat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  intro D θ hθ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact ⟨fun m n K hK => ⟨isClosed_inBox hσ K hK, continuous_realSize hθ, fun N => measurable_maj hσ K hK N,
    fun R => isCompact_box hσ K hK R⟩, fun m n k x hx K hK => maj_rat_le θ m n k x hx K hK⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  first | exact @GlobalTheory.Unf.maj_measurable_rat | exact GlobalTheory.Unf.maj_measurable_rat | (intros; apply GlobalTheory.Unf.maj_measurable_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

theorem mul_mul_mul_of_gram {a b c e n : Type*} [Fintype b] [Fintype c] [Fintype e] {R : Type*} [Semiring R]
    {A : Matrix a b R} {G : Matrix b c R} {M : Matrix c e R} {C : Matrix a e R} (h : A * G * M = C)
    (N : Matrix e n R) : A * (G * (M * N)) = C * N := by
  rw [← h]; simp only [Matrix.mul_assoc]

def selFirst (D : D7) (σ : ℕ) : Matrix (Fin σ) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun i j => if j = i.castSucc then 1 else 0

def lastE (D : D7) (σ : ℕ) : Fin (σ + 1) → D.host.E := Pi.single (Fin.last σ) 1

def besselRationalBasePointMatrix (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem ell_succ_eq : ell D (σ + 1) = fun i => incA D (lastE D σ i) := by
  funext i
  by_cases h : i = Fin.last σ
  · subst h
    show (if (Fin.last σ).1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ (Fin.last σ))
    rw [if_pos (by rw [Fin.val_last]), lastE, Pi.single_eq_same, map_one]
  · have h' : ¬ (i.1 + 1 = σ + 1) := fun h' => h (Fin.ext (by rw [Fin.val_last]; omega))
    show (if i.1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ i)
    rw [if_neg h', lastE, Pi.single_eq_of_ne h, map_zero]

theorem zl_eq_rat (B : BesLev D σ) : zl B = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zl, zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_x0Rat (B : BesLev D σ) : rat (besselRationalBasePointMatrix B) = x0 B := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_x0Rat (B : BesLev D σ) :
    (besselRationalBasePointMatrix B)ᴴ * B.V.gram * besselRationalBasePointMatrix B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [besselRationalBasePointMatrix, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_x0Rat (B : BesLev D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (besselRationalBasePointMatrix B) : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B) := by
  rw [zl_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_x0Rat B), gram_rat B.L rfl]

theorem linearIndependent_x0Rat (B : BesLev D σ) : LinearIndependent D.host.E (besselRationalBasePointMatrix B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : besselRationalBasePointMatrix B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * besselRationalBasePointMatrix B = selFirst D σ := by
    rw [besselRationalBasePointMatrix, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_x0Rat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem exists_rationalOrbit_point_eq_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B :=
  fun _ _ B => ⟨besselRationalBasePointMatrix B, ⟨linearIndependent_x0Rat B, gramSkew_x0Rat B⟩, rat_x0Rat B⟩

end GlobalTheory.Unf.FB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_orb_rat_eq_x0 : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B := by
  exact GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.PairKer

variable {D : D7}

noncomputable def mulRight (S : HSp D) (m : ℕ) (γ : GA D S) : Mx D m S.rank ≃+ Mx D m S.rank where
  toFun w := w * mt S γ
  invFun w := w * mt S γ⁻¹
  left_inv w := by simp only [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  right_inv w := by simp only [Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem om_emb {ψ : AddChar (AF D.host.F) ℂ} {S T A L : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χ χ' om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (o : OrthDec T A L) {γ : GA D A}
    (hγ : γ ∈ GQ A) (h₀ : GA D S) (h₁ : GA D A) (w : WO S L) :
    om (h₀, o.emb (γ * h₁, 1)) f (o.jB * w) = om (h₀, o.emb (h₁, 1)) f (o.jB * w) := by
  have hg : o.emb (γ, 1) ∈ GQ T := o.emb_mem_GQ hγ (GQ L).one_mem
  have a1 : o.emb (γ, 1) * o.emb (h₁, 1) = o.emb (γ * h₁, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have a2 : (o.emb (γ, 1))⁻¹ = o.emb (γ⁻¹, 1) := by
    rw [← map_inv]; exact congrArg _ (Prod.ext rfl inv_one)
  have a3 : mt T (o.emb (γ⁻¹, 1)) * (o.jB * w) = o.jB * w := by
    rw [cancel₂ (o.emb_jB _ _), mt_one, Matrix.mul_one]
  have key : ∀ (δ : GA D T) (x : WO S T), δ ∈ GQ T → mt T δ⁻¹ * x = x → ∀ k, om (h₀, δ * k) f x = om (h₀, k) f x := by
    intro δ x hδ hx k
    have e := GlobalTheory.WeilRat.om_rat_actO D ψ h.std S T _ _ _ h 1 (GQ S).one_mem δ hδ
      _ (h.om_pres (h₀, k) f hf) (mt T δ⁻¹ * x)
    have hact : actO S T 1 δ (mt T δ⁻¹ * x) = x := by
      simp only [actO, inv_one, mt_one, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
    rw [hact, hx] at e
    rw [show (h₀, δ * k) = (1, δ) * (h₀, k) by simp, map_mul, mul_apply_eq_comp]
    exact e
  rw [← a1]
  exact key _ _ hg (by rw [a2]; exact a3) _

theorem pairKer_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → Continuous (Function.uncurry (pairKer s vL Y Ξ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, pairKer s vL Y Ξ (γ * h₀) h₁ = pairKer s vL Y Ξ h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, pairKer s vL Y Ξ h₀ (γ * h₁) = pairKer s vL Y Ξ h₀ h₁ := by
  intro D ψ σ J B s vL Y Ξ hY hΞ
  have hn : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
    have h1 : ‖ψ x‖ = 1 := s.weil₀.std.1.2.1 x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  set K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.A → ℂ := fun w p =>
    s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB * w) * star (Y p.1 w) with hK
  have hP : ∀ h₀ h₁, pairKer s vL Y Ξ h₀ h₁ = ∫ w in vL.𝓕, K w (h₀, h₁) ∂vL.μ := fun h₀ h₁ => by
    simp only [pairKer, contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ _ _ _ s.weil₀ Ξ hΞ
    have h2 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        (((q.2.1, B.o.emb (q.2.2, 1)), B.o.jB * q.1) : (GA D J.W₀ × GA D B.V₀) × WO J.W₀ B.V₀) :=
      ((continuous_fst.comp continuous_snd).prodMk (B.o.continuous_emb.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_const))).prodMk
        (continuous_const.matrix_mul continuous_fst)
    have h3 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        ((q.2.1, q.1) : GA D J.W₀ × WO J.W₀ B.L) := (continuous_fst.comp continuous_snd).prodMk continuous_fst
    exact (h1.comp h2).mul (hY.cont.comp h3).star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ x p, K (γ + x) p = K x p := by
    rintro _ ⟨γ, rfl⟩ x p
    have e1 := (s.weil₀.om_pres (p.1, B.o.emb (p.2, 1)) Ξ hΞ).quasi (B.o.iB * γ) (B.o.jB * x)
    have e2 := hY.quasi p.1 γ x
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB * rat γ) (B.o.jB * x) = symplOH J.W₀ B.L (rat γ) x := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB * (rat γ + x)) * star (Y p.1 (rat γ + x)) =
      s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB * x) * star (Y p.1 x)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB * rat γ) (B.o.jB * x)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, hcont, -, hinv⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  refine ⟨?_, fun γ hγ h₀ h₁ => ?_, fun γ hγ h₀ h₁ => ?_⟩
  · have : Function.uncurry (pairKer s vL Y Ξ) = fun p => ∫ w in vL.𝓕, K w p ∂vL.μ := funext fun p => hP p.1 p.2
    rw [this]; exact hcont
  · rw [hP, hP, ← hinv (mulRight J.W₀ _ γ) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) ?_ (h₀, h₁)]
    · congr 1; funext w
      have e := GlobalTheory.WeilRat.om_rat_actO D ψ s.weil₀.std J.W₀ B.V₀ _ _ _ s.weil₀
        γ hγ 1 (GQ B.V₀).one_mem _ (s.weil₀.om_pres (h₀, B.o.emb (h₁, 1)) Ξ hΞ)
        (B.o.jB * (w * mt J.W₀ γ))
      have hact : actO J.W₀ B.V₀ γ 1 (B.o.jB * (w * mt J.W₀ γ)) = B.o.jB * w := by
        simp only [actO, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
      rw [hact, ← mul_apply_eq_comp, ← map_mul, Prod.mk_mul_mk, one_mul] at e
      change s.om₀ (γ * h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB * w) * star (Y (γ * h₀) w) =
        s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB * (w * mt J.W₀ γ)) * star (Y h₀ (w * mt J.W₀ γ))
      rw [e, hY.left γ hγ]
    · intro x
      refine ⟨fun h => ?_, fun h => ratMx_mul h ((mem_GQ_iff _ _).1 hγ)⟩
      rw [← (mulRight J.W₀ _ γ).symm_apply_apply x]
      exact ratMx_mul h ((mem_GQ_iff _ _).1 (inv_mem hγ))
  · rw [hP, hP]
    congr 1; funext w
    have e := om_emb s.weil₀ hΞ B.o hγ h₀ h₁ w
    change s.om₀ (h₀, B.o.emb (γ * h₁, 1)) Ξ (B.o.jB * w) * star (Y h₀ w) =
      s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB * w) * star (Y h₀ w)
    rw [e]

end GlobalTheory.PairKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → Continuous (Function.uncurry (pairKer s vL Y Ξ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, pairKer s vL Y Ξ (γ * h₀) h₁ = pairKer s vL Y Ξ h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, pairKer s vL Y Ξ h₀ (γ * h₁) = pairKer s vL Y Ξ h₀ h₁ := by
  first | exact @GlobalTheory.PairKer.pairKer_law | exact GlobalTheory.PairKer.pairKer_law | (intros; apply GlobalTheory.PairKer.pairKer_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPadicCoordinatesOfDegreeOneSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPadicCoordinatesOfDegreeOneSplitPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitQT

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

def intEquiv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F ≃+* 𝒪[Fv F v] where
  toFun x := ⟨x.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v x.1).2 x.2⟩
  invFun y := ⟨y.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v y.1).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem exists_coord_padic : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  intro D T _ w e hw hs hT hT2
  obtain ⟨_, _, v, ε, hε, he⟩ := id hs
  have hsa : SplitAt D v e := GlobalTheory.FinPl.SplitPoint.splitAt_of hs hε he
  have hch : Chart e v (comp hsa) := chart_comp hsa
  have hTw : ((T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have := Ideal.absNorm_mem w.asIdeal
    rwa [hT] at this
  have hTw2 : ((T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := fun h =>
    hT2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  obtain ⟨⟨p, hp, hirr⟩, hcard⟩ := GlobalTheory.SplitUnif.unif_chart e w v (comp hsa) hw hch _ hTw hTw2
  have hpT : p = (T : Ov D v) := by
    apply Subtype.ext
    rw [show ((p : Fv D.host.F v)) = algebraMap (Ov D v) (Fv D.host.F v) p from rfl, hp]
    simp
  subst hpT
  haveI : CharZero (Fv D.host.F v) :=
    charZero_of_injective_ringHom (algebraMap D.host.F (v.adicCompletion D.host.F)).injective
  have hc1 : Nat.card (IsLocalRing.ResidueField 𝒪[Fv D.host.F v]) = T := by
    rw [← hT, ← hcard]
    exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (intEquiv D.host.F v)).toEquiv).symm
  have hc2 : Irreducible (T : 𝒪[Fv D.host.F v]) := by
    rw [← map_natCast (intEquiv D.host.F v) T]
    exact (MulEquiv.irreducible_iff (intEquiv D.host.F v).toMulEquiv).2 hirr
  obtain ⟨φ, hφ, hφ', hφO⟩ := GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer (Fv D.host.F v) T hc1 hc2
  obtain ⟨sp, hse, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε hs hε he
  refine ⟨v, φ.symm.toRingHom.comp sp.pr, sp.sec.comp φ.toRingHom.toAddMonoidHom, ⟨ε, hε, he⟩,
    fun a => ?_, fun x => ?_, hφ'.comp sp.cont_pr, sp.cont_sec.comp hφ, fun a => ?_⟩
  · change φ.symm (sp.pr (sp.sec (φ a))) = a
    rw [sp.pr_sec, RingEquiv.symm_apply_apply]
  · change sp.sec (φ (φ.symm (sp.pr x))) = e * x
    rw [RingEquiv.apply_symm_apply, sp.sec_pr, hse]
  · exact (hφO a).symm.trans (sp.int_iff (φ a))

end GlobalTheory.FinPl.SplitQT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPadicCoordinatesOfDegreeOneSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicCoordinates_of_degreeOne_splitPlace : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  first | exact @GlobalTheory.FinPl.SplitQT.exists_coord_padic | exact GlobalTheory.FinPl.SplitQT.exists_coord_padic | (intros; apply GlobalTheory.FinPl.SplitQT.exists_coord_padic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

namespace GlobalTheory.InhPt

open GlobalTheory.MixPer

theorem exists_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ := by
  intro D k _ _ _ _ p ψ hψ
  have hn : ∀ x : AF D.host.F, ‖ψ x‖ = 1 := hψ.1.2.1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  let χ : AddChar k Circle :=
    { toFun := fun a => ⟨psiE ψ (p.sec a), by simpa [Submonoid.unitSphere, psiE] using hn _⟩
      map_zero_eq_one' := by ext; simp [psiE]
      map_add_eq_mul' := by intro a b; ext; simp [psiE, map_add (f := _), AddChar.map_add_eq_mul]; rfl }
  exact ⟨χ, fun a => rfl, Continuous.subtype_mk hc _⟩

theorem exists_splitPt_frame_char : ∀ (D : D7), (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ), T.Prime → Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ p : SplitPt D k, p.e = e) ∧ ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), (∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ ∧ χ ≠ 1 ∧ (p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1) := by
  intro D
  refine ⟨?_, ?_⟩
  · intro k _ _ _ _ _ _ T hT hcard hirr w e hw he hN hsq
    haveI := Fact.mk hT
    obtain ⟨φ, hφ, hφs, hφO⟩ := GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer k T hcard hirr
    obtain ⟨v, pr, sec, hab, h1, h2, hpr, hsec, hint⟩ := GlobalTheory.T.exists_padicCoordinates_of_degreeOne_splitPlace D T w e hw he hN hsq
    refine ⟨⟨v, e, he, hab, φ.toRingHom.comp pr, sec.comp φ.symm.toRingHom.toAddMonoidHom, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · intro a; simp [h1]
    · intro x; simp [h2]
    · exact hφ.comp hpr
    · exact hsec.comp hφs
    · intro a
      have := hφO (φ.symm a)
      simp only [RingEquiv.apply_symm_apply] at this
      simp [this, hint]
  · intro k _ _ _ _ p
    refine ⟨?_, ?_⟩
    · intro S n _ _ b b' h1 h2
      obtain ⟨gl, hs, hm⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k p S n b b' h1 h2
      exact ⟨⟨b, b', h1, h2, gl, hs, hm⟩, rfl⟩
    · intro ψ hψ
      obtain ⟨χ, hχ, hc⟩ := exists_char D k p ψ hψ
      obtain ⟨a, ha⟩ := GlobalTheory.T.exists_adelicTraceCharacter_splitSection_ne_one D k p ψ hψ
      refine ⟨χ, hχ, hc, ?_, fun hu => GlobalTheory.T.splitPlaceCharacter_conductor_integers D k p ψ χ hψ hχ hu⟩
      intro h1
      apply ha
      rw [← hχ a, h1]
      simp

end GlobalTheory.InhPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPoint_frame_character : ∀ (D : D7), (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ), T.Prime → Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ p : SplitPt D k, p.e = e) ∧ ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), (∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ ∧ χ ≠ 1 ∧ (p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1) := by
  first | exact @GlobalTheory.InhPt.exists_splitPt_frame_char | exact GlobalTheory.InhPt.exists_splitPt_frame_char | (intros; apply GlobalTheory.InhPt.exists_splitPt_frame_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamBij

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' ha hb := ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ h := ⟨fun γ hγ g => by simp [h.1 γ hγ g], h.2.const_smul c⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem formAt_eq (β : Frame p S n) (P : Pair k n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) :
    formAt β P (φ P) = φ := by
  funext P₁
  have h := Classical.epsilon_spec (p := fun g : GL n k => g • P = P₁) (MulAction.exists_smul_eq (GL n k) P P₁)
  show β.rep _ (φ P) = φ P₁
  rw [← hφ, h]

theorem sum_single_sum (β : Frame p S n) {ι : Type} (s : Finset ι) (g : ι → GL n k) (a : ι → ℂ)
    (φ₀ : GA D S → ℂ) :
    (∑ i ∈ s, Finsupp.single (g i) (a i)).sum (fun h b => b • β.rep h φ₀) = ∑ i ∈ s, a i • β.rep (g i) φ₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finsupp.sum_add_index' (h := fun h b => b • β.rep h φ₀) (fun h => zero_smul ℂ (β.rep h φ₀)) (fun h _ _ => add_smul _ _ (β.rep h φ₀)), Finsupp.sum_single_index (h := fun h b => b • β.rep h φ₀) (zero_smul ℂ _), ih]

section Ops

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (β : Frame p S n)

theorem isRam_diaFFStar (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (dia ε (FFStar q χ φ)) := by
  refine ⟨dia_mem_EqForm ε (FFStar_mem_EqForm q χ hφ.1), hO.dia_mem_ram ε _ (hO.FFStar_mem_ram _ hφ.2.1),
    fun P' => ?_⟩
  rw [dia_apply, FFStar_apply]
  exact (contAutSub S).sum_mem fun P₁ _ => (contAutSub S).smul_mem _ (hφ.2.2 P₁)

theorem isRam_FFdia (hO : OperatorIdentities k n (GA D S → ℂ) q χ) (c : ℂ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (c • FF q χ (dia ε⁻¹ φ)) := by
  refine ⟨(EqForm β.rep).smul_mem c (FF_mem_EqForm q χ (dia_mem_EqForm _ hφ.1)),
    (Mram k n _).smul_mem c (hO.FF_mem_ram _ (hO.dia_mem_ram _ _ hφ.2.1)), fun P' => ?_⟩
  rw [Pi.smul_apply, FF_apply]
  refine (contAutSub S).smul_mem c ((contAutSub S).sum_mem fun Q _ => (contAutSub S).smul_mem _ ?_)
  rw [dia_apply]
  exact hφ.2.2 _

theorem diaFFStar_inv (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) :
    dia ε (FFStar q χ (((resCard k : ℂ) ^ Fintype.card n)⁻¹ • FF q χ (dia ε⁻¹ φ))) = φ := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  rw [map_smul, map_smul, hO.FFStar_FF_ram _ (hO.dia_mem_ram _ _ h), map_smul, smul_smul, inv_mul_cancel₀ hqr,
    one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem diaFFStar_inj (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ φ' : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) (h' : φ' ∈ Mram k n (GA D S → ℂ))
    (he : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ')) : φ = φ' := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  have h2 : FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ))) = FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ'))) := by rw [he]
  have hd : ∀ X : Form k n (GA D S → ℂ), dia ε⁻¹ (dia ε X) = X := fun X => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hd, hd, hO.FF_FFStar_ram _ h, hO.FF_FFStar_ram _ h'] at h2
  exact smul_right_injective _ hqr h2

end Ops

theorem ramBijective_at (q : Unif k) (χ₀ : AddChar k Circle) (hχ : HasConductor χ₀ 1) (ε : 𝓀[k]ˣ)
    (β : Frame p S n) (P : Pair k n) :
    Set.BijOn (sOp β P q (resChar χ₀ hχ q) ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q (resChar χ₀ hχ q) φ)) ∧
        sOp β P q (resChar χ₀ hχ q) ε (φ P) = dia ε (FFStar q (resChar χ₀ hχ q) φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q (resChar χ₀ hχ q) ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q (resChar χ₀ hχ q) ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀) := by
  set χ := resChar χ₀ hχ q with hχdef
  have hO : OperatorIdentities k n (GA D S → ℂ) q χ :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ₀ hχ n).1 (GA D S → ℂ)).2
  set r : ℂ := ((resCard k : ℂ) ^ Fintype.card n)⁻¹ with hr

  have hval : ∀ φ, IsRam β φ → sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P := fun φ hφ => by
    show dia ε (FFStar q χ (formAt β P (φ P))) P = _
    rw [formAt_eq β P hφ.1]

  have hinv : ∀ φ, IsRam β φ → sOp β P q χ ε ((r • FF q χ (dia ε⁻¹ φ)) P) = φ P := fun φ hφ => by
    rw [hval _ (isRam_FFdia q χ ε β hO r hφ), diaFFStar_inv q χ ε hO hφ.2.1]
  let gch : Pair k n → GL n k := fun P₁ => Classical.epsilon fun g : GL n k => g • P = P₁
  refine ⟨⟨?_, ?_, ?_⟩, fun φ hφ => ⟨isRam_diaFFStar q χ ε β hO hφ, hval φ hφ⟩,
    ∑ P₁ ∈ withKer (ε • P).lat, Finsupp.single (gch P₁) (χ (-cross q P₁ (ε • P))),
    ∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q)), fun φ₀ => ?_, fun φ₀ hφ₀ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, isRam_diaFFStar q χ ε β hO hφ, (hval φ hφ).symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ he
    rw [hval φ hφ, hval φ' hφ'] at he
    have hX := isRam_diaFFStar q χ ε β hO hφ
    have hX' := isRam_diaFFStar q χ ε β hO hφ'
    have he' : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ') := by
      rw [← formAt_eq β P hX.1, ← formAt_eq β P hX'.1, he]
    rw [diaFFStar_inj q χ ε hO hφ.2.1 hφ'.2.1 he']
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨_, isRam_FFdia q χ ε β hO r hφ, rfl⟩, hinv φ hφ⟩
  · rw [sum_single_sum]
    rfl
  · obtain ⟨φ, hφ, rfl⟩ := hφ₀
    have hc : (∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q))).sum
        (fun g a => a • β.rep g (φ P)) = (r • FF q χ (dia ε⁻¹ φ)) P := by
      rw [sum_single_sum, Pi.smul_apply, FF_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [smul_smul, dia_apply]
      conv_rhs => rw [← formAt_eq β P hφ.1]
      rfl
    rw [hc]
    exact ⟨hinv φ hφ, _, isRam_FFdia q χ ε β hO r hφ, rfl⟩

end GlobalTheory.FinPl.RamBij

namespace GlobalTheory.FinPl

theorem ramBijective_holds : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  intro D k _ _ _ _ p n _ _ q χ₀ hχ χ hχeq ε S β P
  subst hχeq
  exact RamBij.ramBijective_at q χ₀ hχ ε β P

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombinStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  first | exact @GlobalTheory.FinPl.ramBijective_holds | exact GlobalTheory.FinPl.ramBijective_holds | (intros; apply GlobalTheory.FinPl.ramBijective_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelic
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SkewVol

variable (D : D7) (ρ : ℕ)

def skewPart (x : Mx D ρ ρ) : Mx D ρ ρ := half D • (x - adj x)

variable {D ρ}

theorem skewPart_mem (x : Mx D ρ ρ) : skewPart D ρ x ∈ skewA D ρ := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {c : Mx D ρ ρ} (hc : c ∈ skewA D ρ) : skewPart D ρ c = c := by
  rw [skewPart, (mem_skewA).1 hc, sub_neg_eq_add, smul_add, half_smul_add]

theorem skewPart_add (x y : Mx D ρ ρ) : skewPart D ρ (x + y) = skewPart D ρ x + skewPart D ρ y := by
  rw [skewPart, skewPart, skewPart, adj_add, add_sub_add_comm, smul_add]

theorem skewPart_rat {x : Mx D ρ ρ} (hx : x ∈ ratMx D ρ ρ) : skewPart D ρ x ∈ ratMx D ρ ρ := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ - γᴴ), ?_⟩
  rw [rat_smul, rat_sub, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPart D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  show Continuous fun x => half D • (x - adj x) from (continuous_id.sub continuous_adj).const_smul (half D)

theorem isClosed_skewA : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) :=
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.2.1
  isClosed_eq continuous_adj continuous_neg

theorem isCoLat_skew :
    GlobalTheory.CuspGeneric.IsCoLat ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D ρ ρ
  refine ⟨?_, ?_⟩
  · let φ : (ratMx D ρ ρ).addSubgroupOf (skewA D ρ) → ratMx D ρ ρ := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D ρ ρ → skewA D ρ := fun x => ⟨skewPart D ρ x, skewPart_mem x⟩
    have hP : Continuous P := continuous_skewPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_addSubgroupOf.2 (skewPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change skewPart D ρ (γ + x.1) = skewPart D ρ γ + x.1
    rw [skewPart_add, skewPart_of_mem x.2]

theorem exists_haar_covol_one : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  intro D ρ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (skewA D ρ) := (isClosed_skewA (D := D) (ρ := ρ)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (skewA D ρ) _ isCoLat_skew
  exact ⟨μ, 𝓕, hμ, inferInstance, hF, h1⟩

end GlobalTheory.SkewVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_covolume_one_skewHermitian_adelic : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  first | exact @GlobalTheory.SkewVol.exists_haar_covol_one | exact GlobalTheory.SkewVol.exists_haar_covol_one | (intros; apply GlobalTheory.SkewVol.exists_haar_covol_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

def splitLoc (D : D7) : Set (AE D)ˣ :=
  {x | ∃ e, IsSplitIdem D e ∧ (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1}

def modSet (D : D7) (N : ℕ) : Set (AE D)ˣ :=
  {x | infPart D (x : AE D) = 1 ∧
    (∃ r ∈ intAE D, finPart D (x : AE D) - 1 = (N : Af D.host.F ⊗[D.host.F] D.host.E) * r) ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D}

def grpH (D : D7) (N : ℕ) : Subgroup (AE D)ˣ :=
  Subgroup.closure (Set.range (Units.map (incA D).toMonoidHom) ∪ splitLoc D ∪ modSet D N)

end GlobalTheory.HeckeSplitAll
end
end

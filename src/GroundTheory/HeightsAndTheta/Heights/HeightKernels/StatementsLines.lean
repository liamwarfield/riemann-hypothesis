module

public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder

noncomputable section

def stdLattice (K : Type*) [Field K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.span (𝓞 K) (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K))

def stdSumBasis (K : Type*) [Field K] (m k : ℕ) : Module.Basis (Fin m ⊕ Fin k) K (Fin (m + k) → K) :=
  (Pi.basisFun K (Fin (m + k))).reindex finSumFinEquiv.symm

def LinesLatticeBasis.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι],
    Fintype.card ι = Module.finrank ℚ V → ∀ M : Submodule ℤ V, Submodule.IsFullLattice ℚ M →
      ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b)

def LinesGenIndexDet.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    [DecidableEq ι] (bA bB : Module.Basis ι ℚ V) (A B : AddSubgroup V),
    A = AddSubgroup.closure (Set.range bA) → B = AddSubgroup.closure (Set.range bB) →
      genIndex A B = |((bA.det bB : ℚ) : ℝ)|

def LinesIsLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (M : Submodule (𝓞 K) (ι → K)),
    (M.restrictScalars ℤ).FG → Submodule.span K (M : Set (ι → K)) = ⊤ →
      Submodule.IsFullLattice ℚ (M.restrictScalars ℤ)

def LinesGenIndexTrans.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (A B C : Submodule ℤ V),
    Submodule.IsFullLattice ℚ A → Submodule.IsFullLattice ℚ B → Submodule.IsFullLattice ℚ C →
      0 < genIndex A.toAddSubgroup B.toAddSubgroup ∧
        genIndex A.toAddSubgroup B.toAddSubgroup * genIndex B.toAddSubgroup C.toAddSubgroup =
          genIndex A.toAddSubgroup C.toAddSubgroup

def LinesIdealLatticeFG.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K),
    (∀ x, a x ≠ 0) →
      (idealLattice a).FG ∧ Submodule.span K (idealLattice a : Set (Fin n → K)) = ⊤

theorem stdSumBasis_inl (K : Type*) [Field K] (m k : ℕ) (i : Fin m) :
    stdSumBasis K m k (Sum.inl i) = Pi.single (Fin.castAdd k i) 1 := by
  simp [stdSumBasis]

theorem stdSumBasis_inr (K : Type*) [Field K] (m k : ℕ) (j : Fin k) :
    stdSumBasis K m k (Sum.inr j) = Pi.single (Fin.natAdd m j) 1 := by
  simp [stdSumBasis]

theorem stdSumBasis_elim (K : Type*) [Field K] (m k : ℕ) :
    Sum.elim (fun i => stdSumBasis K m k (Sum.inl i)) (fun j => stdSumBasis K m k (Sum.inr j)) =
      ⇑(stdSumBasis K m k) := by
  funext x; cases x <;> rfl

theorem stdLattice_isLattice_example :
    Submodule.IsFullLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) := by
  have : Submodule.IsLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) :=
    Submodule.IsLattice.of_fg ℚ ((Submodule.fg_span (Set.finite_range _)).restrictScalars)
  refine { span_eq_top := ?_ }
  change Submodule.span ℚ (stdLattice ℚ 1 : Set (Fin 1 → ℚ)) = ⊤
  rw [stdLattice, Submodule.span_span_of_tower (𝓞 ℚ)]
  have h : ⇑(Pi.basisFun ℚ (Fin 1)) = fun j => Pi.single j 1 :=
    funext (Pi.basisFun_apply ℚ (Fin 1))
  rw [← h, Module.Basis.span_eq]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudySmooth

theorem contDiffAt_blockNorm {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))
  have hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    intro h0
    exact hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)
  exact (contDiffAt_norm ℂ hne).comp z hL.contDiffAt

end FubiniStudySmooth

theorem FsLineSmooth.proof : FsLineSmooth.Statement := by
  intro K _ ι _
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _
  refine contDiffOn_prod fun k _ => ?_
  intro z hz
  simp only [Pi.one_apply, zpow_one]
  exact (FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDensityIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartDensityIntegrableAlt

theorem exists_conjTranspose_mul_self {e : ℕ} {N : Matrix (Fin e) (Fin e) ℂ} (hN : N.PosDef) :
    ∃ C : Matrix (Fin e) (Fin e) ℂ, N = Cᴴ * C ∧ C.det ≠ 0 := by
  obtain ⟨U, l, hl, hspec⟩ : ∃ (U : Matrix (Fin e) (Fin e) ℂ) (l : Fin e → ℝ), (∀ k, 0 ≤ l k) ∧
      N = U * diagonal (fun k => (l k : ℂ)) * star U := by
    refine ⟨(hN.1.eigenvectorUnitary : Matrix (Fin e) (Fin e) ℂ), hN.1.eigenvalues,
      fun k => (hN.eigenvalues_pos k).le, ?_⟩
    have h := hN.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set s : Fin e → ℂ := fun k => ((Real.sqrt (l k) : ℝ) : ℂ) with hs
  have hss : (fun i => star s i * s i) = fun k => (l k : ℂ) := by
    funext k
    simp only [hs, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hl k)]
  have hNC : N = (diagonal s * star U)ᴴ * (diagonal s * star U) := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (star s)), diagonal_mul_diagonal, hss, hspec,
      star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨diagonal s * star U, hNC, fun h => ?_⟩
  have hdet := (hN.det_pos).ne'
  rw [hNC, det_mul, h, mul_zero] at hdet
  exact hdet rfl

theorem chart_quad_eq {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hH : M.IsHermitian)
    {C : Matrix (Fin e) (Fin e) ℂ} (hNC : M.submatrix Fin.succ Fin.succ = Cᴴ * C) {d : Fin e → ℂ}
    (hd : Cᴴ *ᵥ d = fun i => M i.succ 0) (y : Fin e → ℂ) :
    star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (M 0 0 - star d ⬝ᵥ d) + star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) := by
  have h1 : star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) =
      star y ⬝ᵥ ((Cᴴ * C) *ᵥ y) + star y ⬝ᵥ (Cᴴ *ᵥ d) + star (Cᴴ *ᵥ d) ⬝ᵥ y + star d ⬝ᵥ d := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, dotProduct_mulVec (star d) C y]
    ring
  rw [h1, ← hNC, hd]
  have hw : ∀ j : Fin e, M 0 j.succ = star (M j.succ 0) := fun j => (hH.apply 0 j.succ).symm
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, star_one,
    one_mul, mul_one, submatrix_apply, hw, mul_add, Finset.sum_add_distrib]
  ring

theorem re_star_dotProduct_self {e : ℕ} (z : Fin e → ℂ) : (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hermChartPot_eq_gbPot_affine {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ∃ (c : Fin e → ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (κ : ℝ), P.det ≠ 0 ∧
      hermChartPot M = fun y => gbPot (c + P *ᵥ y) + κ := by
  obtain ⟨C, hNC, hC⟩ := exists_conjTranspose_mul_self (hM.submatrix (Fin.succ_injective e))
  have hCH : Cᴴ.det ≠ 0 := by rw [det_conjTranspose]; exact star_ne_zero.mpr hC
  set w : Fin e → ℂ := fun i => M i.succ 0 with hw
  set d : Fin e → ℂ := (Cᴴ)⁻¹ *ᵥ w with hd'
  have hd : Cᴴ *ᵥ d = w := by
    rw [hd', mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCH), one_mulVec]
  have hq := fun y => chart_quad_eq hM.1 hNC hd y
  set s : ℝ := (M 0 0 - star d ⬝ᵥ d).re with hs
  have hspos : 0 < s := by
    have hy0 : C *ᵥ (-(C⁻¹ *ᵥ d)) + d = 0 := by
      rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC), one_mulVec, neg_add_cancel]
    have hx : (Fin.cons 1 (-(C⁻¹ *ᵥ d)) : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
      have := congr_fun h 0
      simp at this
    have hpos := hM.re_dotProduct_pos hx
    rw [hq, hy0] at hpos
    simpa [hs] using hpos
  set r : ℝ := Real.sqrt s with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hspos
  refine ⟨((r⁻¹ : ℝ) : ℂ) • d, ((r⁻¹ : ℝ) : ℂ) • C, Real.log r, ?_, ?_⟩
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (inv_pos.mpr hrpos).ne')) hC
  · funext y
    have hX : 0 ≤ ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hcy : ((r⁻¹ : ℝ) : ℂ) • d + (((r⁻¹ : ℝ) : ℂ) • C) *ᵥ y = ((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d) := by
      rw [smul_mulVec, smul_add, add_comm]
    have hnorm : ∑ i, ‖(((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d)) i‖ ^ 2 = (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hrpos), mul_pow]
    have hsq : s = r ^ 2 := (Real.sq_sqrt hspos.le).symm
    have h1pos : 0 < 1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hsplit : s + ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 = r ^ 2 * (1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2) := by
      rw [hsq]; field_simp
    simp only [hermChartPot, gbPot]
    rw [hq, Complex.add_re, ← hs, re_star_dotProduct_self, hcy, hnorm, hsplit,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrpos.le,
      Real.log_mul hrpos.ne' (Real.sqrt_pos.mpr h1pos).ne']
    ring

theorem integrable_fsDens (D : ℕ) :
    Integrable (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
  have hcont : Continuous (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y => ?_
    have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
    positivity
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by
    simp only [Pi.zero_apply]; positivity)]
  have h := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero] at h
  rw [h]
  exact ENNReal.ofReal_lt_top

theorem integrable_comp_affine {D : ℕ} {f : (Fin D → ℂ) → ℝ} (hf : Integrable f) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : Integrable (fun y => f (c + P *ᵥ y)) := by
  set L := ChartMongeAmpereAffineInvariance.realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)))
    (by rw [ChartMongeAmpereAffineInvariance.det_realCLE]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe] at hmap
  have hg : Integrable (fun w => f (c + w)) (Measure.map L volume) := by
    rw [hmap]
    exact (hf.comp_add_left c).smul_measure ENNReal.ofReal_ne_top
  exact L.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hg

end ChartDensityIntegrableAlt


open ChartDensityIntegrableAlt in
theorem ChartDensityIntegrable.proof : ChartDensityIntegrable.Statement := by
  intro e M hM
  obtain ⟨c, P, κ, hP, hpot⟩ := hermChartPot_eq_gbPot_affine M hM
  have h : (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y) = fun y =>
      (Complex.normSq P.det * ((e.factorial : ℝ) / Real.pi ^ e)) *
        ((1 + ∑ i, ‖(c + P *ᵥ y) i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [hpot, ChartMongeAmpereAffineInvariance.maDensity_comp_affine gbPot c P hP κ y, maDensity_gbPot]
    ring
  rw [h]
  exact (integrable_comp_affine (integrable_fsDens e) c P hP).const_mul _

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def GrassGeomDegChart.Statement : Prop :=
  ∀ n : ℕ, ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
    geomDeg (grassIdeal 1 1 n) (fsMulti (plBlocks 1 1 n)) n = chartMass (Bᴴ * B)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianArithmeticVariety

theorem det_submatrix_sign {R : Type*} [CommRing R] {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (g h : Fin j → Fin N) (hg : Function.Injective g) (hh : Function.Injective h)
    (hr : Set.range h = Set.range g) :
    ∃ s : ℤˣ, (A.submatrix id h).det = ((s : ℤ) : R) * (A.submatrix id g).det := by
  let σ : Equiv.Perm (Fin j) :=
    (Equiv.ofInjective h hh).trans ((Equiv.subtypeEquivRight (fun x => by rw [hr])).trans (Equiv.ofInjective g hg).symm)
  have hσ : ∀ i, g (σ i) = h i := by
    intro i
    simp [σ, Equiv.apply_ofInjective_symm]
  refine ⟨Equiv.Perm.sign σ, ?_⟩
  have : A.submatrix id h = (A.submatrix id g).submatrix id σ := by
    ext r i; simp [hσ]
  rw [this, det_permute']

def col {j m : ℕ} (a : Fin j) (b : Fin m) (i : Fin j) : Fin (j + m) :=
  if i = a then Fin.natAdd j b else Fin.castAdd m i

theorem col_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (col a b) := by
  intro x y hxy
  simp only [col] at hxy
  split_ifs at hxy with h1 h2 h2
  · exact h1.trans h2.symm
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)

def idx {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨col a b, col_injective a b⟩, by simp⟩

theorem minor_idx {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by
  obtain ⟨s, hs⟩ := det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b)
    ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by
      rw [Finset.range_orderEmbOfFin]; simp [idx])
  refine ⟨s, ?_⟩
  have hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r i
    by_cases hi : i = a
    · simp [col, onePipe, hi]
    · simp [col, onePipe, hi]
  rw [colsOf, hs, hcol, ← cramer_apply, cramer_one]
  rfl

theorem colsOf_anchor {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by
  have he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) =
      Fin.castAdd m :=
    (Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm
  ext r i
  simp [colsOf, onePipe, he]

end GrassmannianArithmeticVariety


open GrassmannianArithmeticVariety in
theorem GrassArithVar.proof (h : CoordConeArithVar.Statement) : GrassArithVar.Statement := by
  intro f j m hf
  let e : Fin (f * j * m) ≃ Fin f × Fin j × Fin m :=
    finProdFinEquiv.symm.trans
      ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  let φ := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)
  let t : Fin (f * j * m) → GrassField f j m := fun i => φ (X (e i))
  have anchor : ∀ τ, grassCoord f j m ⟨τ, plAnchor j m⟩ = 1 := by
    intro τ
    have hp : grassPolyCoord f j m ⟨τ, plAnchor j m⟩ = 1 :=
      (congrArg Matrix.det (colsOf_anchor _)).trans det_one
    rw [grassCoord, hp, map_one]
  have hmem : ∀ q : MvPolynomial (Fin f × Fin j × Fin m) ℚ,
      algebraMap _ (GrassField f j m) q ∈ IntermediateField.adjoin ℚ (Set.range t) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨e.symm i, by simp [t, φ]⟩)
  refine h (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) (fun _ => plAnchor j m)
    (f * j * m) t ⟨⟨0, hf⟩⟩ (fun τ => by rw [anchor]; exact one_ne_zero) ?_ ?_ ?_
  · exact ((MvPolynomial.algebraicIndependent_X _ ℚ).map' (f := φ)
      (IsFractionRing.injective _ _)).comp e e.injective
  · intro i
    rcases hi : e i with ⟨τ, a, b⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤˣ, grassPolyCoord f j m ⟨τ, idx a b⟩ =
        ((s : ℤ) : MvPolynomial (Fin f × Fin j × Fin m) ℚ) * X (τ, a, b) :=
      minor_idx _ a b
    have hr : grassCoord f j m ⟨τ, idx a b⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (coneRatios (grassCoord f j m) fun _ => plAnchor j m) :=
      IntermediateField.subset_adjoin _ _ ⟨⟨τ, idx a b⟩, rfl⟩
    have hy : grassCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : GrassField f j m) * t i := by
      rw [grassCoord, hs, map_mul, map_intCast]
      simp [t, φ, hi]
    rw [anchor, div_one, hy] at hr
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hr
    · simpa using neg_mem hr
  · rintro r ⟨⟨τ, I⟩, rfl⟩
    have hr : grassCoord f j m ⟨τ, I⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (Set.range t) := by
      rw [anchor, div_one]; exact hmem _
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range t))
      (A := GrassField f j m) ⟨_, hr⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyInvariance

open ChartMongeAmpereAffineInvariance

def EnergyInvariantUnder {e : ℕ} (C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : Prop :=
  ∀ M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k

variable {e : ℕ}

theorem posDef_conj {M C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hC : C.det ≠ 0) :
    (Cᴴ * M * C).PosDef :=
  hM.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)))

theorem conj_mul (M A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    (A * B)ᴴ * M * (A * B) = Bᴴ * (Aᴴ * M * A) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem invariantUnder_mul {A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hA : EnergyInvariantUnder A)
    (hB : EnergyInvariantUnder B) (hAdet : A.det ≠ 0) : EnergyInvariantUnder (A * B) := by
  intro M N hM hN k
  rw [conj_mul, conj_mul, hB _ _ (posDef_conj hM hAdet) (posDef_conj hN hAdet), hA M N hM hN]

theorem invariantUnder_of_mul_right {C V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hCV : EnergyInvariantUnder (C * V)) (hV : EnergyInvariantUnder V) (hC : C.det ≠ 0) :
    EnergyInvariantUnder C := by
  intro M N hM hN k
  rw [← hV _ _ (posDef_conj hM hC) (posDef_conj hN hC), ← conj_mul, ← conj_mul, hCV M N hM hN]

theorem maDensity_comp_affine_family {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j => fun y => φ j (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity φ (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hH : ∀ j, cxHessian (fun y => φ j (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian (φ j) (c + P *ᵥ z) * P.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_affine (φ j) c P hP κ z
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun j => cxHessian (φ j) (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem invariantUnder_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (hdet : T.det ≠ 0) : EnergyInvariantUnder T := by
  intro M N hM hN k
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set P := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hPdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hP : P.det ≠ 0 := by
    rw [hPdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfM : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  have hfN : hermChartPot (Tᴴ * N * T) = fun y => hermChartPot N (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj N T hN hT ht)
  set Φ : Fin e → (Fin e → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  have hfam : (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) =
      fun j => fun y => Φ j (c + P *ᵥ y) + Real.log ‖T 0 0‖ := by
    funext j y
    by_cases h : (j : ℕ) < k <;> simp [hΦ, h, hfM, hfN]
  set f : (Fin e → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y, (hermChartPot (Tᴴ * M * T) y - hermChartPot (Tᴴ * N * T) y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) y =
      Complex.normSq P.det * f (c + P *ᵥ y) := fun y => by
    rw [hfam, maDensity_comp_affine_family Φ c P hP, hfM, hfN, hf]
    ring
  unfold chartMixedEnergy
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_affine f c P hP, ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hP).ne', one_mul]

theorem invariantUnder_of_row_one (hS : ChartEnergySwapInvariant.Statement)
    (C : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hC : C.det ≠ 0) (h1 : C 0 1 ≠ 0) :
    EnergyInvariantUnder C := by
  have h01 : (0 : Fin (e + 1 + 1)) ≠ 1 := by simp
  set S : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := swapFirstTwo e with hSdef
  have hSinv : EnergyInvariantUnder S := fun M N hM hN k => hS e M N hM hN k
  have hSdet : S.det ≠ 0 := by
    rw [hSdef, swapFirstTwo, det_permutation, Equiv.Perm.sign_swap h01]
    norm_num
  set T : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ).updateRow 1 (C 0) with hTdef
  have hT0 : ∀ j : Fin (e + 1), T 0 j.succ = 0 := fun j => by
    rw [hTdef, updateRow_ne h01, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hTdet : T.det = C 0 1 := by
    have hrow : ∑ m, C 0 m • (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) m = C 0 := by
      funext p
      simp [Finset.sum_apply, Matrix.one_apply]
    have h := det_updateRow_sum (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) 1 (C 0)
    rw [hrow] at h
    simpa using h
  have hTdet' : T.det ≠ 0 := by rw [hTdet]; exact h1
  have hST0 : ∀ m, C 0 m = (S * T) 0 m := fun m => by
    rw [hSdef, swapFirstTwo, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, Equiv.swap_apply_left, id, hTdef,
      updateRow_self]
  have hSTdet : (S * T).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hSdet hTdet'
  have hU : IsUnit (S * T).det := isUnit_iff_ne_zero.mpr hSTdet
  set A := C * (S * T)⁻¹ with hAdef
  have hCA : C = A * (S * T) := by rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]
  have hA0 : ∀ j : Fin (e + 1), A 0 j.succ = 0 := fun j => by
    rw [hAdef, Matrix.mul_apply]
    simp_rw [hST0]
    rw [← Matrix.mul_apply, mul_nonsing_inv _ hU, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hAdet : A.det ≠ 0 := fun h => hC (by rw [hCA, det_mul, h, zero_mul])
  have h := invariantUnder_mul (invariantUnder_of_row_zero A hA0 hAdet)
    (invariantUnder_mul hSinv (invariantUnder_of_row_zero T hT0 hTdet') hSdet) hAdet
  rwa [← hCA] at h

end ChartEnergyInvariance


open ChartEnergyInvariance in
theorem ChartEnergyLinearInvariant.proof (hS : ChartEnergySwapInvariant.Statement) :
    ChartEnergyLinearInvariant.Statement := by
  intro e M N C hM hN hC k
  by_cases hrow : ∀ j : Fin e, C 0 j.succ = 0
  · exact invariantUnder_of_row_zero C hrow hC M N hM hN k
  · push Not at hrow
    obtain ⟨j, hj⟩ := hrow
    cases e with
    | zero => exact j.elim0
    | succ e =>
      set V : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
        (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ).permMatrix ℂ with hVdef
      have hs0 : Equiv.swap (1 : Fin (e + 1 + 1)) j.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero j).symm
      have hV0 : ∀ m : Fin (e + 1), V 0 m.succ = 0 := fun m => by
        simp [hVdef, PEquiv.toMatrix_apply, hs0, (Fin.succ_ne_zero m).symm]
      have hVdet : V.det ≠ 0 := by
        rw [hVdef, det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ)) with h | h <;>
          simp [h]
      have hCV1 : (C * V) 0 1 ≠ 0 := by
        rw [hVdef, PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, Equiv.symm_swap, Equiv.swap_apply_left, id]
        exact hj
      have hCVdet : (C * V).det ≠ 0 := by
        rw [det_mul]
        exact mul_ne_zero hC hVdet
      exact invariantUnder_of_mul_right (invariantUnder_of_row_one hS (C * V) hCVdet hCV1)
        (invariantUnder_of_row_zero V hV0 hVdet) hC M N hM hN k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyDiagonal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDiagonalAlt

def diagEnergy {e : ℕ} (l : Fin (e + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (e + 1),
    chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k

theorem diag_posDef {e : ℕ} {l : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) :
    (Matrix.diagonal fun j => (l j : ℂ)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by simpa using hl j

theorem diag_congr {e : ℕ} (s d : Fin (e + 1) → ℝ) :
    (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (d j : ℂ)) *
        Matrix.diagonal (fun j => (s j : ℂ)) =
      Matrix.diagonal fun j => ((s j * d j * s j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem diagEnergy_mul (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {l l' : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) (hl' : ∀ j, 0 < l' j) :
    diagEnergy (l * l') = diagEnergy l + diagEnergy l' := by
  have hll' : ∀ j, 0 < (l * l') j := fun j => mul_pos (hl j) (hl' j)
  set s : Fin (e + 1) → ℝ := fun j => (Real.sqrt (l' j))⁻¹ with hs
  have hss : ∀ j, s j * s j * l' j = 1 := fun j => by
    simp only [hs]
    rw [← mul_inv, Real.mul_self_sqrt (hl' j).le, inv_mul_cancel₀ (hl' j).ne']
  have hsd : (Matrix.diagonal fun j => (s j : ℂ)).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have : (Real.sqrt (l' j)) ≠ 0 := (Real.sqrt_pos.mpr (hl' j)).ne'
    simpa [hs] using this
  have h1 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => ((l * l') j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = Matrix.diagonal fun j => (l j : ℂ) := by
    rw [diag_congr]
    congr 1
    funext j
    congr 1
    simp only [Pi.mul_apply]
    linear_combination (l j) * hss j
  have h2 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (l' j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = 1 := by
    rw [diag_congr, ← diagonal_one]
    congr 1
    funext j
    rw [show s j * l' j * s j = 1 by linarith [hss j]]
    simp
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => ((l * l') j : ℂ))
      (Matrix.diagonal fun j => (l' j : ℂ)) k = chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ _ (diag_posDef hll') (diag_posDef hl') hsd k, h1, h2]
  unfold diagEnergy
  rw [hC e _ (Matrix.diagonal fun j => (l' j : ℂ)) 1 (diag_posDef hll') (diag_posDef hl') PosDef.one,
    Finset.sum_congr rfl fun k _ => hterm k]

theorem diagEnergy_perm (hI : ChartEnergyLinearInvariant.Statement) {e : ℕ} {l : Fin (e + 1) → ℝ}
    (hl : ∀ j, 0 < l j) (σ : Equiv.Perm (Fin (e + 1))) : diagEnergy (l ∘ σ) = diagEnergy l := by
  set C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := σ.symm.toPEquiv.toMatrix with hCdef
  have hCH : Cᴴ = σ.toPEquiv.toMatrix := by
    ext i j
    rw [hCdef, conjTranspose_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.symm_apply_eq]
    by_cases h : σ i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hconj : ∀ A : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, Cᴴ * A * C = A.submatrix σ σ := by
    intro A
    rw [hCH, PEquiv.toMatrix_toPEquiv_mul, hCdef, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
    rfl
  have hCd : C.det ≠ 0 := by
    rw [hCdef, show (σ.symm.toPEquiv.toMatrix : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      Equiv.Perm.permMatrix ℂ σ.symm from rfl, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k =
      chartMixedEnergy (Matrix.diagonal fun j => ((l ∘ σ) j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ C (diag_posDef hl) PosDef.one hCd k, hconj, hconj, submatrix_diagonal_equiv,
      submatrix_one_equiv]
    rfl
  unfold diagEnergy
  exact (Finset.sum_congr rfl fun k _ => hterm k).symm

theorem cxHessian_add_const {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (κ : ℝ) :
    cxHessian (fun y => φ y + κ) = cxHessian φ := by
  have h : fderiv ℝ (fun y => φ y + κ) = fderiv ℝ φ := funext fun x => fderiv_add_const κ
  funext z
  unfold cxHessian
  simp only [h]
  rfl

theorem maDensity_congr {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (h : ∀ j, cxHessian (φ j) = cxHessian (ψ j))
    (z : Fin D → ℂ) : maDensity φ z = maDensity ψ z := by
  unfold maDensity
  simp only [h]

theorem hermChartPot_const {e : ℕ} {c : ℝ} (hc : 0 < c) (y : Fin e → ℂ) :
    hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) y =
      hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c := by
  set v : Fin (e + 1) → ℂ := Fin.cons 1 y with hv
  have hv0 : v ≠ 0 := fun h => by
    have := congr_fun h 0
    simp [hv] at this
  have hx : 0 < (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re :=
    PosDef.one.re_dotProduct_pos hv0
  have hq : (star v ⬝ᵥ ((Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) *ᵥ v)).re =
      c * (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re := by
    rw [← smul_one_eq_diagonal, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  unfold hermChartPot
  rw [← hv, hq, Real.sqrt_mul hc.le, Real.log_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hx).ne',
    Real.log_sqrt hc.le]
  ring

theorem diagEnergy_const {e : ℕ} {c : ℝ} (hc : 0 < c) :
    diagEnergy (fun _ : Fin (e + 1) => c) =
      (e + 1) * (1 / 2 * Real.log c) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have hpot : hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) =
      fun y => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c :=
    funext (hermChartPot_const hc)
  have hk : ∀ k, chartMixedEnergy (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) 1 k =
      1 / 2 * Real.log c * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
    intro k
    have hd : ∀ y, maDensity (fun j : Fin e => if (j : ℕ) < k then
        hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ))
        else hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y =
        maDensity (fun _ : Fin e => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y := by
      refine maDensity_congr _ _ fun j => ?_
      split_ifs
      · rw [hpot, cxHessian_add_const]
      · rfl
    unfold chartMixedEnergy chartMass
    simp_rw [hd]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [hpot]
    ring
  unfold diagEnergy
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem diagEnergy_one {e : ℕ} : diagEnergy (1 : Fin (e + 1) → ℝ) = 0 := by
  calc diagEnergy (1 : Fin (e + 1) → ℝ) = diagEnergy (fun _ : Fin (e + 1) => (1 : ℝ)) := rfl
    _ = 0 := by rw [diagEnergy_const one_pos, Real.log_one]; ring

theorem diagEnergy_prod (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Fin (e + 1) → ℝ) (hf : ∀ t j, 0 < f t j) :
    diagEnergy (∏ t ∈ s, f t) = ∑ t ∈ s, diagEnergy (f t) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact diagEnergy_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      diagEnergy_mul hI hC (hf a) (fun j => by rw [Finset.prod_apply]; exact Finset.prod_pos fun t _ => hf t j),
      ih]

end ChartEnergyDiagonalAlt


open ChartEnergyDiagonalAlt in
theorem ChartEnergyDiagonal.proof (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement) :
    ChartEnergyDiagonal.Statement := by
  intro e l hl
  change diagEnergy l = _
  set f : Fin (e + 1) → Fin (e + 1) → ℝ := fun t => l ∘ (Equiv.addRight t) with hf
  have hfpos : ∀ t j, 0 < f t j := fun t j => hl _
  have hprod : (∏ t, f t) = fun _ => ∏ j, l j := by
    funext i
    rw [Finset.prod_apply]
    exact Equiv.prod_comp (Equiv.addLeft i) l
  have key := diagEnergy_prod hI hC Finset.univ f hfpos
  rw [hprod, diagEnergy_const (Finset.prod_pos fun j _ => hl j),
    Finset.sum_congr rfl fun t _ => diagEnergy_perm hI hl (Equiv.addRight t), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.log_prod (fun j _ => (hl j).ne')] at key
  push_cast at key
  have he : (0 : ℝ) < e + 1 := by positivity
  have h2 : ((e : ℝ) + 1) * (diagEnergy l - 1 / 2 * (∑ j, Real.log (l j)) *
      chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) = 0 := by
    linear_combination -key
  have := (mul_eq_zero.mp h2).resolve_left he.ne'
  linarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassFibreDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

def GrassFibreDegree.Statement : Prop :=
  ∀ (n p : ℕ), p.Prime →
    vertR (grassIdeal 1 1 n) (fun _ : Fin n => fsMulti (plBlocks 1 1 n)) (C (p : ℤ)) = Real.log p

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassLinesProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GrassLinesProj.Statement : Prop :=
  ∀ (m : ℕ) (II : IntersectionSystem), IsIntersectionSystem II →
    II (Fin 1) (plBlocks 1 1 m) (grassIdeal 1 1 m) (1 * 1 * m + 1) (fun _ => fsMulti (plBlocks 1 1 m)) =
      II Unit (PBlk (m + 1)) ⊥ (m + 1) (fun _ => fsMulti (PBlk (m + 1)))

end

end GroundTheory.Heights₂.Heights
end

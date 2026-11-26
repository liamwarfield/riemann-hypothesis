module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.FreeQuotientRank
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfFinitelyGenerated
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ReductionTau
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.ReductionTauOf
set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem reductionTau_of (h3 : SubmoduleExists) (h6 : SizesLocallyComparable) (h7 : InfimumContinuousFamily)
    (h8 : MinkowskiSubmodule) (h9 : LatticeVectorsBoundedBelow) (h10 : HeightsPositive) : ReductionTau := by
  unfold Formalism.L2.SG.LitS.ReductionTau
  intro I hn
  refine ⟨?_, fun x => ?_⟩
  · exact h7 I.GA (Sub I) (fun x s => size I s) (fun x => h3 I hn x)
      (fun x s => Real.rpow_nonneg (h10 I x s).le _) (fun x r hr => h6 I x r hr)
  · obtain ⟨c, hc, hc8⟩ := h8 I
    obtain ⟨l, hl, hl9⟩ := h9 I x
    have hδ : ∀ s : Sub I x, Real.sqrt (l / c) ≤ size I s := by
      intro s
      obtain ⟨u, huB, hu0, hsum⟩ := hc8 x s
      have h1 := hl9 u (s.B_lat huB) hu0
      have hs0 : 0 ≤ size I s := Real.rpow_nonneg (h10 I x s).le _
      exact Real.sqrt_le_iff.2 ⟨hs0, (div_le_iff₀ hc).2 (by linarith)⟩
    haveI := h3 I hn x
    exact ⟨lt_min (by norm_num) (lt_of_lt_of_le (Real.sqrt_pos.2 (div_pos hl hc)) (le_ciInf hδ)),
      min_le_left _ _⟩

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.T8m
set_option autoImplicit false

noncomputable section

open MeasureTheory Metric

namespace Formalism.L2.SG.Pf.Tau

theorem t8m : MinkowskiFirstTheorem := by
  intro d hd
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; omega)
  set v1 : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hv1_def
  have hv1ne : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hv1pos : 0 < v1 :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hv1ne
  refine ⟨4 / v1 ^ ((2 : ℝ) / d), by positivity, ?_⟩
  intro L _ _
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℝ (Fin d)))
  set F := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L b) with hF_def
  have hcov : ZLattice.covolume L = volume.real F := ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hcov0 : 0 ≤ ZLattice.covolume L := by rw [hcov]; exact measureReal_nonneg
  have hFfin : volume F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  set r : ℝ := 2 * (ZLattice.covolume L / v1) ^ ((1 : ℝ) / d) with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ ZLattice.covolume L / v1 := by positivity
  have key : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ d = t := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, one_div_mul_cancel hdpos.ne', Real.rpow_one]
  have key2 : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ 2 = t ^ ((2 : ℝ) / d) := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  have hrd : r ^ d = 2 ^ d * (ZLattice.covolume L / v1) := by
    rw [hr_def, mul_pow, key _ hq0]
  have hvol : volume F * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))
      ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r) := by
    rw [Measure.addHaar_closedBall volume 0 hr0, hfr, hrd, ← ENNReal.ofReal_toReal hv1ne, ← hv1_def,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hFfin]
    have : (volume F).toReal = ZLattice.covolume L := by rw [hcov]; rfl
    have e : (2 : ℝ) ^ d * (ZLattice.covolume L / v1) * v1 = ZLattice.covolume L * 2 ^ d := by
      field_simp
    rw [this, e, ENNReal.ofReal_mul hcov0, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
  haveI hcL : Countable L := Countable.of_equiv _ b.repr.toEquiv.symm
  haveI : Countable L.toAddSubgroup := hcL
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) hF (fun y hy => by simpa using hy) (convex_closedBall _ _)
    (isCompact_closedBall _ _) hvol
  refine ⟨x, x.2, fun h => hx0 (Subtype.ext h), ?_⟩
  have hxr : ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ r := by simpa using hxs
  calc ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
    _ = 4 / v1 ^ ((2 : ℝ) / d) * ZLattice.covolume L ^ ((2 : ℝ) / d) := by
      rw [hr_def, mul_pow, key2 _ hq0, Real.div_rpow hcov0 hv1pos.le]
      ring
  exact le_rfl

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MinkowskiSubmoduleShortVector
set_option autoImplicit false

noncomputable section

open NumberField Matrix Module MeasureTheory
open scoped ComplexOrder Classical

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

def t8C (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * (Matrix.of fun i k => b k i).map (I.φ v)

theorem coord_linear_comb (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (a : Fin j → I.E) :
    coordV I x v (∑ k, a k • b k) = t8C I x v b *ᵥ fun k => I.φ v (a k) := by
  unfold coordV t8C
  have hw : (fun i => I.φ v ((∑ k, a k • b k) i)) =
      (Matrix.of fun i k => b k i).map (I.φ v) *ᵥ fun k => I.φ v (a k) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, map_sum, mul_comm]
  rw [hw, Matrix.mulVec_mulVec]

theorem gramV_eq_conjTranspose_t8C_mul_t8C (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (t8C I x v b)ᴴ * t8C I x v b := by
  have hc : ∀ a i, coordV I x v (b a) i = t8C I x v b i a := by
    intro a i
    first
      | rfl
      | (unfold coordV t8C; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply])
  unfold gramV
  ext a c
  simp only [hc, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem coord_matrix_mulVec_injective (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (hb : LinearIndependent I.E b) :
    Function.Injective (t8C I x v b).mulVec := by
  set A : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹ with hA
  set Bm : Matrix (Fin I.n) (Fin j) I.E := Matrix.of fun i a => b a i with hBm
  have hB : Function.Injective Bm.mulVec := by
    intro c c' h
    have hs : ∑ a, (c a - c' a) • b a = 0 := by
      ext i
      have := congrFun h i
      simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        Pi.zero_apply]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this
    funext a
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ hs a)
  have hAu : IsUnit A := (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  intro w w' h
  apply mulVec_injective_map (I.φ v) Bm hB
  apply Matrix.mulVec_injective_iff_isUnit.2 hAu
  simpa only [t8C, Matrix.mulVec_mulVec] using h

def linearCombinationOfRows {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) : (Fin j → E) →+ (Fin n → E) where
  toFun a := ∑ k, a k • b k
  map_zero' := by simp
  map_add' a a' := by simp [add_smul, Finset.sum_add_distrib]

theorem linearComb_apply {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (a : Fin j → E) :
    linearCombinationOfRows b a = ∑ k, a k • b k := rfl

theorem linear_comb_injective {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (hb : LinearIndependent E b) :
    Function.Injective (linearCombinationOfRows b) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  rw [linearComb_apply] at ha
  funext k
  exact Fintype.linearIndependent_iff.mp hb a ha k

theorem linearComb_single {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (k : Fin j) (c : E) :
    linearCombinationOfRows b (Pi.single k c) = c • b k := by
  rw [linearComb_apply]
  simp [Pi.single_apply, ite_smul]

theorem short_vector_sublattice (I : AutInst) (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) (x : I.GA) (s : Sub I x) (C : ℝ)
    (hC : ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j)))) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ u ∈ L, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ C * ZLattice.covolume L ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ))) :
    ∃ u ∈ s.B, u ≠ 0 ∧ ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2 ≤
      C * t8K I s.j ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ)) * size I s ^ 2 := by

  choose R hR hRdet using fun v => gram_factor_invertible (t8C I x v s.b) (coord_matrix_mulVec_injective I x v s.b s.b_ind)
  have hgram : ∀ v, (gramV I x v s.b).det.re = Complex.normSq (R v).det := by
    intro v
    rw [gramV_eq_conjTranspose_t8C_mul_t8C, hR v, Matrix.det_mul, Matrix.det_conjTranspose,
      ← Complex.ofReal_re (Complex.normSq (R v).det), Complex.normSq_eq_conj_mul_self]
    rfl

  set P : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) (Set.range s.b) with hP
  have hfin : Finite (s.B ⧸ P.comap s.B.subtype) := by
    obtain ⟨M, hMfg, hM⟩ := h1 I x
    refine h2 I.E I.n s.j M s.B s.b hMfg ?_ s.b_ind s.b_mem s.B_span
    intro u hu
    rw [← SetLike.mem_coe, hM]
    exact s.B_lat hu
  set N : ℕ := Nat.card (s.B ⧸ P.comap s.B.subtype) with hN
  have hN0 : 0 < N := Nat.card_pos

  set lin := linearCombinationOfRows s.b with hlin
  have hlinj : Function.Injective lin := linear_comb_injective s.b s.b_ind
  set Bp : AddSubgroup (Fin s.j → I.E) := s.B.toAddSubgroup.comap lin with hBp
  set Op : AddSubgroup (Fin s.j → I.E) := (t8O I s.j).toAddSubgroup with hOp
  have hgen : ∀ p : Σ _ : Fin s.j, Free.ChooseBasisIndex ℤ (𝓞 I.E),
      lin (Pi.single p.1 (integralBasis I.E p.2)) = (RingOfIntegers.basis I.E p.2) • s.b p.1 := by
    intro p
    rw [hlin, linearComb_single, integralBasis_apply, algebraMap_smul]
  have hOB : Op ≤ Bp := by
    intro y hy
    change lin y ∈ s.B
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      rw [hgen]
      exact s.B.smul_mem _ (s.b_mem p.1)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact s.B.add_mem hy hz
    | smul c y _ hy => rw [map_zsmul]; exact s.B.toAddSubgroup.zsmul_mem hy c
  have hmapO : Op.map lin = P.toAddSubgroup := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      change lin a ∈ P
      induction ha using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, rfl⟩ := hy
        rw [hgen]
        exact P.smul_mem _ (Submodule.subset_span ⟨p.1, rfl⟩)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact P.add_mem hy hz
      | smul c y _ hy => rw [map_zsmul]; exact P.toAddSubgroup.zsmul_mem hy c
    · intro hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 I.E)).1 (show y ∈ P from hy)
      refine ⟨fun k => (c k : I.E), mem_integral_vectors I s.j _ fun k => ⟨c k, rfl⟩, ?_⟩
      rw [hlin, linearComb_apply, ← hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact algebraMap_smul I.E (c k) (s.b k)
  have hmapB : Bp.map lin = s.B.toAddSubgroup := by
    refine AddSubgroup.map_comap_eq_self ?_
    intro u hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (s.B_span hu)
    exact ⟨c, hc⟩
  have hrel : Op.relIndex Bp = N := by
    rw [← AddSubgroup.relIndex_map_map_of_injective Op Bp hlinj, hmapO, hmapB, hN]
    rfl

  have hRdet' : ∀ v, (R v).det ≠ 0 := hRdet
  set Θ := t8Th R with hΘ
  have hΘinj : Function.Injective Θ := blockTransform_injective R hRdet'
  set L₁ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j))) :=
    Submodule.span ℤ (Set.range (blockBasis R hRdet')) with hL₁
  set L₂ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j))) :=
    (Bp.map Θ).toIntSubmodule with hL₂
  have hL₁' : L₁.toAddSubgroup = Op.map Θ := by
    rw [hL₁, ← map_integral_vectors_span R hRdet']
    rfl
  have hL₂' : L₂.toAddSubgroup = Bp.map Θ := AddSubgroup.toIntSubmodule_toAddSubgroup _
  have h12 : L₁ ≤ L₂ := by
    intro y hy
    have hy' : y ∈ L₁.toAddSubgroup := hy
    rw [hL₁'] at hy'
    show y ∈ L₂.toAddSubgroup
    rw [hL₂']
    exact AddSubgroup.map_mono hOB hy'
  have hrel2 : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup = N := by
    rw [hL₁', hL₂', AddSubgroup.relIndex_map_map_of_injective Op Bp hΘinj, hrel]

  have hNR : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hN0.ne')
  set β' := (blockBasis R hRdet').isUnitSMul (w := fun _ => ((N : ℝ))⁻¹) (fun _ => isUnit_iff_ne_zero.2 hNR)
    with hβ'
  have hsub : (L₂ : Set (EuclideanSpace ℝ (Fin (2 * I.f * s.j)))) ⊆ Submodule.span ℤ (Set.range β') := by
    intro w hw
    have hw' : w ∈ L₂.toAddSubgroup := hw
    rw [hL₂'] at hw'
    obtain ⟨a, ha, rfl⟩ := hw'
    have hNa : N • a ∈ Op := by
      rw [← hrel]
      exact AddSubgroup.nsmul_relIndex_mem Op ha
    have hNw : N • Θ a ∈ L₁ := by
      have : Θ (N • a) ∈ L₁.toAddSubgroup := by
        rw [hL₁']
        exact ⟨N • a, hNa, rfl⟩
      rwa [map_nsmul] at this
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hNw
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
    simp only [hβ', Basis.isUnitSMul_apply]
    have e : ∀ p, c p • ((N : ℝ)⁻¹ • blockBasis R hRdet' p) = (N : ℝ)⁻¹ • (c p • blockBasis R hRdet' p) :=
      fun p => smul_comm _ _ _
    simp only [e, ← Finset.smul_sum, hc]
    rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0.ne')]
  have : DiscreteTopology L₂ :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range β'))) hsub
  have : IsZLattice ℝ L₂ := ⟨by
    rw [eq_top_iff, ← (blockBasis R hRdet').span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    exact h12 (Submodule.subset_span ⟨p, rfl⟩)⟩

  have hcov := ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ h12
  rw [hrel2, covolume_blockBasis] at hcov
  have hht : ht I s = (∏ v, Complex.normSq (R v).det) / N := by
    rw [ht]
    simp only [hgram]
    rfl
  have hcov2 : ZLattice.covolume L₂ = t8K I s.j * ht I s := by
    have hpos := ZLattice.covolume_pos L₂ volume
    rw [hht]
    rw [div_eq_iff hpos.ne'] at hcov
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    field_simp
    linarith
  have hht0 : 0 ≤ ht I s := by
    rw [hht]
    exact div_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)

  obtain ⟨w, hw, hw0, hwb⟩ := hC L₂
  have hw' : w ∈ L₂.toAddSubgroup := hw
  rw [hL₂'] at hw'
  obtain ⟨a, ha, rfl⟩ := hw'
  refine ⟨lin a, ha, ?_, ?_⟩
  · intro h0
    apply hw0
    have : a = 0 := hlinj (by rw [h0, map_zero])
    rw [this, map_zero]
  · have hnorm : ‖Θ a‖ ^ 2 = ∑ v, ∑ i, ‖coordV I x v (lin a) i‖ ^ 2 := by
      rw [hΘ, blockTransform_norm_sq]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hlin, linearComb_apply, coord_linear_comb]
      exact (norm_sq_eq_of_gram_eq _ _ (hR v) _).symm
    rw [← hnorm]
    refine hwb.trans (le_of_eq ?_)
    rw [hcov2, Real.mul_rpow (integral_covolume_pos I s.j).le hht0, size, ← Real.rpow_mul_natCast hht0]
    have hf : (0 : ℝ) < I.f := by
      have : 0 < Fintype.card (InfinitePlace I.F) := Fintype.card_pos
      rw [card_infinite_places] at this
      exact_mod_cast this
    have hj : (0 : ℝ) < s.j := by exact_mod_cast s.j_pos
    have e : (1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)) * ((2 : ℕ) : ℝ) = (2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e]
    ring

theorem minkowski_submodule_short_vector (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) (h8m : MinkowskiFirstTheorem) : MinkowskiSubmodule := by
  intro I
  let cj : ℕ → ℝ := fun j =>
    if h : 1 ≤ 2 * I.f * j then (h8m _ h).choose * t8K I j ^ ((2 : ℝ) / ((2 * I.f * j : ℕ) : ℝ)) else 0
  have hcj : ∀ j, 0 ≤ cj j := by
    intro j
    simp only [cj]
    split_ifs with h
    · exact mul_nonneg (h8m _ h).choose_spec.1.le (Real.rpow_nonneg (integral_covolume_pos I j).le _)
    · exact le_rfl
  refine ⟨1 + ∑ j ∈ Finset.range (I.n + 1), cj j, by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range (I.n + 1)) => hcj j
    linarith, ?_⟩
  intro x s
  have hd : 1 ≤ 2 * I.f * s.j := by
    have : 0 < Fintype.card (InfinitePlace I.F) := Fintype.card_pos
    rw [card_infinite_places] at this
    have := s.j_pos
    have : 1 ≤ I.f * s.j := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [Nat.mul_assoc]
    omega
  obtain ⟨u, hu, hu0, hub⟩ := short_vector_sublattice I h1 h2 x s (h8m _ hd).choose (fun L _ _ => (h8m _ hd).choose_spec.2 L)
  refine ⟨u, hu, hu0, hub.trans ?_⟩
  have hjn : s.j ≤ I.n := by
    have := s.b_ind.fintype_card_le_finrank
    simpa using this
  have hle : cj s.j ≤ 1 + ∑ j ∈ Finset.range (I.n + 1), cj j := by
    have := Finset.single_le_sum (f := cj) (fun j _ => hcj j) (Finset.mem_range.2 (Nat.lt_succ_of_le hjn))
    linarith
  have hcs : cj s.j = (h8m _ hd).choose * t8K I s.j ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ)) := by
    simp only [cj, dif_pos hd]
  rw [← hcs]
  exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ReductionTheoryOfLattice
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ThirdEstimateOfFirstTwo
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem exists_ne_zero_mem_L (I : AutInst) (hn : 1 ≤ I.n) : ∃ l ∈ I.L, l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := I.L_span
  have h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact hcon
  rw [h0] at h
  haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact bot_ne_top h

theorem third_estimate_of_first_two (h0 : LatticeCommensurable) (h1 : LatticeFinitelyGenerated) : SubmoduleExists := by
  intro I hn x
  obtain ⟨m, hm1, _, hLm⟩ := h0 I x
  obtain ⟨M, _, hM⟩ := h1 I x
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_mem_L I hn
  have hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E)) := by
    rw [hM]
    exact hLm l hlL
  have hm0 : ((m : I.E) • l) ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0
  obtain ⟨t, htM, hspan, hli⟩ := exists_linearIndependent I.E (M : Set (Fin I.n → I.E))
  have htfin : t.Finite := hli.setFinite
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    have h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E)) := Submodule.subset_span hml
    rw [← hspan] at h2
    exact hm0 ((Submodule.mem_bot _).mp h2)
  haveI := htfin.fintype
  let e := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩
  · exact Fintype.card_pos_iff.mpr hne.to_subtype
  · exact hli.comp _ e.injective
  · exact hM.le
  · intro a
    exact htM (e a).2
  · intro v hv
    have hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact (e a).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hr, hspan]
    exact Submodule.subset_span hv

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.KsetInvMem
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem kset_inv_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hk

theorem t4 : LatticeRightInvariant := by
  intro I x y k hk
  ext u
  show (I.fmat (x * (y, k)).2⁻¹) *ᵥ _ ∈ I.Lf ↔ (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
  have hk' : ∀ w, w ∈ I.Lf ↔ I.fmat k⁻¹ *ᵥ w ∈ I.Lf := kset_inv_mem I hk
  have e : I.fmat (x * (y, k)).2⁻¹ = I.fmat k⁻¹ * I.fmat x.2⁻¹ := by
    simp only [AutInst.fmat, Prod.snd_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]
  exact (hk' _).symm

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.LatticeVectorsBoundedBelow
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem one_le_norm_embedding_alt (I : AutInst) (a : 𝓞 I.E) (ha : a ≠ 0) :
    ∃ v, 1 ≤ ‖I.φ v (a : I.E)‖ := by
  set β : I.E := (a : I.E) * star (a : I.E) with hβ
  have hfix : star β = β := by simp [hβ, mul_comm]
  obtain ⟨γ, hγ⟩ := (I.cm.fixed β).1 hfix
  have haI : IsIntegral ℤ (a : I.E) := a.2
  have hsI : IsIntegral ℤ (star (a : I.E)) := IsIntegral.map I.cm.sig haI
  have hβI : IsIntegral ℤ β := haI.mul hsI
  have hγI : IsIntegral ℤ γ := by
    rw [← isIntegral_algebraMap_iff (B := I.E), hγ]
    exact hβI
  have ha0 : (a : I.E) ≠ 0 := by simpa using ha
  have hβ0 : β ≠ 0 := mul_ne_zero ha0 (star_ne_zero.2 ha0)
  let g : 𝓞 I.F := ⟨γ, hγI⟩
  have hg0 : g ≠ 0 := by
    intro h
    apply hβ0
    rw [← hγ]
    have : γ = 0 := congrArg Subtype.val h
    simp [this]
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace I.F, 1 ≤ w (g : I.F) := by
    by_contra h
    push Not at h
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w₀) hg0 (fun z _ => h z)) (not_le.2 (h w₀))
  refine ⟨w, ?_⟩
  have e : w (g : I.F) = ‖I.φ w (a : I.E)‖ ^ 2 := by
    rw [← InfinitePlace.norm_embedding_eq, show (g : I.F) = γ from rfl, ← I.φ_over, hγ, hβ, map_mul,
      I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj, sq]
  rw [e] at hw
  by_contra h
  push Not at h
  nlinarith [norm_nonneg (I.φ w (a : I.E))]

theorem lattice_common_denominator (I : AutInst) : ∃ b : 𝓞 I.E, b ≠ 0 ∧
    ∀ y ∈ I.L, ∀ i, ∃ c : 𝓞 I.E, (c : I.E) = (b : I.E) * y i := by
  first | exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator .. | (apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator I

theorem invertible_matrix_lower_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : Fin n → ℂ) (i : Fin n), ‖w i‖ ^ 2 ≤ C * ∑ k, ‖(A *ᵥ w) k‖ ^ 2 := by
  obtain ⟨U, rfl⟩ := hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  refine ⟨∑ i, ∑ k, ‖B i k‖ ^ 2 + 1, by positivity, fun w i => ?_⟩
  set z := (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w
  have hw : w = B *ᵥ z := by
    simp only [z, B, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h1 : ‖w i‖ ≤ ∑ k, ‖B i k‖ * ‖z k‖ := by
    rw [hw]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 : ‖w i‖ ^ 2 ≤ (∑ k, ‖B i k‖ ^ 2) * ∑ k, ‖z k‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ k, ‖B i k‖ ^ 2 ≤ ∑ i, ∑ k, ‖B i k‖ ^ 2 + 1 := by
    have := Finset.single_le_sum (f := fun i => ∑ k, ‖B i k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))

theorem lattice_vectors_bounded_below (h0 : LatticeCommensurable) : LatticeVectorsBoundedBelow := by
  intro I x
  obtain ⟨m, hm1, hm, -⟩ := h0 I x
  obtain ⟨b, hb0, hb⟩ := lattice_common_denominator I
  have hC : ∀ v, ∃ C : ℝ, 0 < C ∧ ∀ (u : Fin I.n → I.E) (i : Fin I.n),
      ‖I.φ v (u i)‖ ^ 2 ≤ C * ∑ k, ‖coordV I x v u k‖ ^ 2 := fun v => by
    have hU : IsUnit (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) :=
      (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
    obtain ⟨C, hC, hCw⟩ := invertible_matrix_lower_bound _ hU
    exact ⟨C, hC, fun u i => hCw (fun i => I.φ v (u i)) i⟩
  choose C hCpos hCb using hC
  set K : ℝ := ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v :=
      Finset.sum_nonneg fun w _ => by have := hCpos w; positivity
    linarith
  refine ⟨1 / K, by positivity, ?_⟩
  intro u hu hu0
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨c, hc⟩ := hb _ (hm u hu) i
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0' : (b : I.E) ≠ 0 := by simpa using hb0
  have hc0 : c ≠ 0 := by
    intro h
    have : (c : I.E) = 0 := by simp [h]
    rw [hc, Pi.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero hb0' (mul_ne_zero hm0 hi) this
  obtain ⟨v, hv⟩ := one_le_norm_embedding_alt I c hc0
  have e : ‖I.φ v (c : I.E)‖ = ‖I.φ v (b : I.E)‖ * (m : ℝ) * ‖I.φ v (u i)‖ := by
    rw [hc, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_natCast, norm_mul, norm_mul,
      Complex.norm_natCast, mul_assoc]
  set S := ∑ w, ∑ k, ‖coordV I x w u k‖ ^ 2
  have hSv : ∑ k, ‖coordV I x v u k‖ ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun w => ∑ k, ‖coordV I x w u k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ v)
  have hS0 : 0 ≤ S := by positivity
  have h1 : 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := by
    have : 1 ≤ ‖I.φ v (c : I.E)‖ ^ 2 := by nlinarith
    rw [e] at this
    nlinarith
  have h2 : ‖I.φ v (u i)‖ ^ 2 ≤ C v * S := (hCb v u i).trans
    (mul_le_mul_of_nonneg_left hSv (hCpos v).le)
  have h3 : ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v ≤ K := by
    have := Finset.single_le_sum (f := fun w => ‖I.φ w (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C w)
      (fun w _ => by have := hCpos w; positivity) (Finset.mem_univ v)
    linarith
  have h4 : 1 ≤ K * S := by
    have hbm : 0 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 := by positivity
    calc 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := h1
      _ ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * (C v * S) := mul_le_mul_of_nonneg_left h2 hbm
      _ = (‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v) * S := by ring
      _ ≤ K * S := mul_le_mul_of_nonneg_right h3 hS0
  rw [div_le_iff₀ hK0]
  linarith

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Imports
set_option autoImplicit false

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

theorem t2 : ExistsBoundedBasis := by
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  classical
  have hBfg : B.FG := by
    haveI := isNoetherian_of_fg_of_noetherian M hM
    have h1 : (B.comap M.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hBM] at h2
  obtain ⟨s, hs⟩ := hBfg
  have hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g := fun g hg =>
    (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))
  choose! c hc using hcoef
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))
  have hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro g hg
    rw [← hc g hg, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hint : IsIntegral ℤ (y • c g a) :=
      hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)
    have e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a := by
      rw [← smul_assoc]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    rw [← hs]
    intro v hv
    refine Submodule.span_induction (fun g hg => hyg g hg) (by simp)
      (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw)
      (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv
  haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) :=
    Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
  show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0
  have hz := map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  rw [← hz, Submodule.Quotient.mk_eq_zero]
  exact hyB v v.2

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.LatticeFinitelyGeneratedOfCommensurable
set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem inclE_mem_intAf (I : AutInst) (c : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) ∈ IntAf I.F I.E := by
  apply Subring.subset_closure
  left
  exact ⟨⟨(c : I.E), c, rfl⟩, rfl⟩

def latSubmodule (I : AutInst) (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := latSet I x
  zero_mem' := by
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have : (fun i : Fin I.n => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
      funext i; simp
    rw [this, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  add_mem' := by
    intro u w hu hw
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((u + w) i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) +
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
      funext i; simp
    rw [h, Matrix.mulVec_add]
    exact I.Lf.add_mem hu hw
  smul_mem' := by
    intro c u hu
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((c • u) i)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) •
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) := by
      funext i
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul]
    have := I.Lf.smul_mem (⟨_, inclE_mem_intAf I c⟩ : IntAf I.F I.E) hu
    exact this

theorem coe_latSubmodule (I : AutInst) (x : I.GA) :
    ((latSubmodule I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = latSet I x := rfl

theorem lattice_finitelyGenerated_of_commensurable (h0 : LatticeCommensurable) : LatticeFinitelyGenerated := by
  intro I x
  obtain ⟨m, hm1, hA, -⟩ := h0 I x
  refine ⟨latSubmodule I x, ?_, coe_latSubmodule I x⟩
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    (((m : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
  have hle : latSubmodule I x ≤ I.L.map φ := by
    intro u hu
    refine ⟨(m : I.E) • u, hA u hu, ?_⟩
    simp [φ, smul_smul, inv_mul_cancel₀ hm0]
  have hfg : (I.L.map φ).FG := I.L_fg.map φ
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  have h1 := IsNoetherian.noetherian ((latSubmodule I x).comap (I.L.map φ).subtype)
  have h2 := h1.map (I.L.map φ).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2

end Formalism.L2.SG.Pf.Tau
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.T7
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace Formalism.L2.SG.Pf.Tau

theorem t7 : InfimumContinuousFamily := by
  intro X _ S g hne hpos hloc
  have hbdd : ∀ x, BddBelow (Set.range (g x)) := fun x => ⟨0, by rintro _ ⟨s, rfl⟩; exact hpos x s⟩
  have hinf_nonneg : ∀ x, 0 ≤ ⨅ s, g x s := fun x => by
    haveI := hne x
    exact le_ciInf fun s => hpos x s
  have key : ∀ x y (r : ℝ), 0 ≤ r → (∀ s, ∃ s', g y s' ≤ r * g x s) → (⨅ s, g y s) ≤ r * ⨅ s, g x s := by
    intro x y r hr h
    haveI := hne x
    rw [Real.mul_iInf_of_nonneg hr]
    exact le_ciInf fun s => by
      obtain ⟨s', hs'⟩ := h s
      exact (ciInf_le (hbdd y) s').trans hs'
  have hmin : ∀ a b r : ℝ, 1 ≤ r → 0 ≤ b → a ≤ r * b → min (1 / 2) a ≤ r * min (1 / 2) b := by
    intro a b r hr hb hab
    rcases le_total b (1 / 2) with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hab
    · rw [min_eq_left h]
      nlinarith [min_le_left (1 / 2 : ℝ) a]
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hr : (1 : ℝ) < 1 + ε := by linarith
  filter_upwards [hloc x (1 + ε) hr] with x' hx'
  have h1 := hmin _ _ _ hr.le (hinf_nonneg x) (key x x' _ (by linarith) hx'.1)
  have h2 := hmin _ _ _ hr.le (hinf_nonneg x') (key x' x _ (by linarith) hx'.2)
  have hm1 : min (1 / 2 : ℝ) (⨅ s, g x s) ≤ 1 / 2 := min_le_left _ _
  have hm2 : min (1 / 2 : ℝ) (⨅ s, g x' s) ≤ 1 / 2 := min_le_left _ _
  have hp1 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x s) := le_min (by norm_num) (hinf_nonneg x)
  have hp2 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x' s) := le_min (by norm_num) (hinf_nonneg x')
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end Formalism.L2.SG.Pf.Tau
end
end

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reduction_theory_of_lattice (h0 : LatticeCommensurable) (h8 : MinkowskiSubmodule) : ReductionTau :=
  reductionTau_of (third_estimate_of_first_two h0 (lattice_finitelyGenerated_of_commensurable h0)) (sizes_locally_comparable t4 t5) t7 h8 (lattice_vectors_bounded_below h0) (packet_conditions_closed (lattice_finitelyGenerated_of_commensurable h0) t2)

theorem reductionTau_of_minkowskiSubmodule (h8 : MinkowskiSubmodule) : ReductionTau :=
  reduction_theory_of_lattice t0 h8

end Formalism.L2.SG.Pf.Tau
end

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reductionTau : ReductionTau :=
  reductionTau_of_minkowskiSubmodule (minkowski_submodule_short_vector (lattice_finitelyGenerated_of_commensurable t0) t2 t8m)

end Formalism.L2.SG.Pf.Tau
end

set_option autoImplicit false

namespace Formalism.L2.SG.Pf

theorem reduction_theory : Formalism.L2.SG.LitS.ReductionTau :=
  Tau.reductionTau

end Formalism.L2.SG.Pf

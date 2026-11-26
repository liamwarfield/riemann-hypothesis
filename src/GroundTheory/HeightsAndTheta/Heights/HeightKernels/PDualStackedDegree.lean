module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace DualStackedDegreeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem isLattice (F : HermLattice K i) : Submodule.IsFullLattice ℚ (F.lattice.restrictScalars ℤ) :=
  LinesIsLattice.proof K (Fin i) F.lattice (F.fg.restrictScalars) F.span_eq

theorem degree_withStdMetric (F : HermLattice K i) :
    F.withStdMetric.degree = Real.log (genIndex F.lattice.toAddSubgroup
      (HermLattice.standard K i).lattice.toAddSubgroup) := by
  have hspan : Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K)) =
        Set.range (Pi.basisFun K (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]; exact (Pi.basisFun K (Fin i)).span_eq
  have hlat : F.withStdMetric.lattice = F.lattice := rfl
  have hstd : F.withStdMetric.metric = fun _ => 1 := rfl
  simp only [HermLattice.degree, subDegree, hlat, hstd, hspan, Submodule.restrictScalars_top, inf_top_eq,
    TopDualLatticeChange.gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero]
  rfl

theorem degree_sub (F F' : HermLattice K i) (h : F'.lattice ≤ F.lattice) :
    F.withStdMetric.degree - F'.withStdMetric.degree =
      Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup) := by
  have hT := LinesGenIndexTrans.proof LinesLatticeBasis.proof
    (LinesGenIndexDet.proof LinesLatticeBasis.proof)
  obtain ⟨hpos1, hmul⟩ := hT (Fin i → K) (F.lattice.restrictScalars ℤ) (F'.lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ) (isLattice F) (isLattice F') (isLattice _)
  obtain ⟨hpos2, -⟩ := hT (Fin i → K) (F'.lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ) (isLattice F') (isLattice _) (isLattice _)
  have e : ∀ L : Submodule (𝓞 K) (Fin i → K), (L.restrictScalars ℤ).toAddSubgroup = L.toAddSubgroup :=
    fun _ => rfl
  simp only [e] at hpos1 hmul hpos2
  rw [degree_withStdMetric, degree_withStdMetric, ← hmul, Real.log_mul hpos1.ne' hpos2.ne',
    add_sub_cancel_right, genIndex, (AddSubgroup.relIndex_eq_one (H := F.lattice.toAddSubgroup)
      (K := F'.lattice.toAddSubgroup)).mpr (fun _ hx => h hx), Nat.cast_one, div_one]

theorem relIndex_stacked {T : Type} [Fintype T] [DecidableEq T] {F F' : HermLattice K i}
    (h : F'.lattice ≤ F.lattice) (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ)
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) :
    ((dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup : ℝ) = ∏ t, |(a t : ℝ)| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ (DualTopStackedExistence.dualLattice_mono h) b b']
  have hv : (fun t => (⟨(b t : Fin i → K), DualTopStackedExistence.dualLattice_mono h (b t).2⟩ :
      dualLattice F')) = fun t => a t • b' t := by
    funext t; exact Subtype.ext (hab t)
  have hdet : b'.det (fun t => a t • b' t) = ∏ t, a t := by
    rw [Module.Basis.det_apply]
    have hm : b'.toMatrix (fun t => a t • b' t) = Matrix.diagonal a := by
      ext s t
      by_cases hst : s = t
      · subst hst; simp [Module.Basis.toMatrix_apply]
      · simp [Module.Basis.toMatrix_apply, hst]
    rw [hm, Matrix.det_diagonal]
  erw [hv, hdet]
  push_cast [Nat.cast_natAbs, Int.cast_abs, Int.cast_prod, Finset.abs_prod]
  rfl

end DualStackedDegreeAlt


open DualStackedDegreeAlt in
theorem DualStackedDegree.proof (hIdx : DualLatticeIndex.Statement) : DualStackedDegree.Statement := by
  intro K _ _ i F F' T _ _ b b' a h hab
  have ha : ∀ t, a t ≠ 0 := fun t ht => b.ne_zero t (Subtype.ext (by rw [hab t, ht, zero_smul]; rfl))
  rw [degree_sub F F' h, ← hIdx K i F F' h, relIndex_stacked h b b' a hab,
    Real.log_prod (fun t _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha t)))]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedDiag {T : Type} [DecidableEq T] (a : T → ℤ) : ∀ _ : Unit, T → T → ℤ :=
  fun _ t s => if t = s then a t else 0

abbrev stackedBlocks (T : Type) : Unit ⊕ Unit → Type := Sum.elim (dualBlocks T) (dualBlocks T)

def stackedGraph {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  graphIdeal (dualIdeal b') (linForm (stackedDiag a))

def graphFirst {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inl (), t⟩

def graphSecond {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inr (), t⟩

def degFirst : Unit ⊕ Unit → ℤ := pullDeg (Sum.inl : Unit → Unit ⊕ Unit) fun _ => 1

def degSecond : Unit ⊕ Unit → ℤ := pullDeg (Sum.inr : Unit → Unit ⊕ Unit) fun _ => 1

def DualStackedGraphImage.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    imageZ inrV (stackedGraph b' a) = dualIdeal b ∧
      ∀ (G : GenFibre inrV (stackedGraph b' a))
        (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit))),
        IsFieldIntersection J → J (fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

def DualStackedGraphHorizontal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (W : Ideal (MRing (stackedBlocks T))), IsHorizontal W →
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) ↔
        W ∈ divSupp (stackedGraph b' a) (C (a t) * graphFirst t)) ∧
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) →
        multAt (stackedGraph b' a ⊔ Ideal.span {graphSecond t}) W =
          multAt (stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t}) W)

def DualStackedGraphFibre.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (L : Fin (i - 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (stackedBlocks T)),
      (∀ j, (L j).a = degFirst ∨ (L j).a = degSecond) →
      ((∀ j, (L j).a = degSecond) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) =
          -∑ s, Real.log |(a s : ℝ)|) ∧
      ((∃ j, (L j).a = degFirst) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) = 0)

theorem degFirst_inr : degFirst (Sum.inr ()) = 0 := by
  rw [degFirst, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inl_ne_inr hu)]
  rfl

theorem degSecond_inr : degSecond (Sum.inr ()) = 1 := by
  rw [degSecond, pullDeg, Sum.inr_injective.extend_apply]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.POneBlockPointDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace OneBlockPointDeg

variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

theorem isMultiHomog_of_isHomogeneous (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f fun _ => n := by
  intro m hm k
  have h := hf (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k
    (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')] at h
  exact h

theorem aeval_homog (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by
  classical
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c := by
    funext ⟨k, i⟩; obtain rfl := hK k; rfl
  have h := Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)
  rwa [Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e] at h

theorem ringKrullDim_adjoin_eq_one {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by
  have hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ := by
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin]; exact Algebra.adjoin_le hs
  let _ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ' :=
    { ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }
  have hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w))
      ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) := ⟨fun b => by
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x}) := by
      rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact b.2
    refine (Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb
    rintro y (hy | hy)
    · exact ((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map
        (Algebra.adjoin Φ s).val).tower_top
    · rw [Set.mem_singleton_iff.mp hy]
      exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩
  have : IsArtinianRing (Algebra.adjoin Φ s) := IsArtinianRing.of_finite Φ _
  have : IsNoetherianRing (Algebra.adjoin Φ s) := IsNoetherianRing.of_finite Φ _
  rw [← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]
  change ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1
  rw [← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]
  rfl

end OneBlockPointDeg


open OneBlockPointDeg in
theorem OneBlockPointDeg.proof : OneBlockPointDeg.Statement := by
  classical
  intro Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr
  set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr
  set L := Algebra.adjoin Φ (Set.range r) with hL
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩
  have hrL : ∀ p, r p ∈ L := fun p => Algebra.subset_adjoin ⟨p, rfl⟩

  have hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n,
      homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') := by
    intro f hf n
    have hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L := fun g => by
      rw [hL, ← aeval_range]; exact AlgHom.mem_range_self _ g
    let P : Polynomial L := ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩
    have hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0 := by
      have h0 := RingHom.mem_ker.mp hf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent f, map_sum] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]
      rfl
    have hP0 := (transcendental_iff.mp htr) P hP
    rw [RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]
    by_cases hn : n < f.totalDegree + 1
    · have h1 := congrArg (fun q : Polynomial L => q.coeff n) hP0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finset.sum_ite_eq',
        Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1
      rw [show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]
      simp
    · rw [homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp
  have hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c := fun k => by
    rw [RingHom.mem_ker, aeval_X]; exact hz k

  have hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) := by
    refine ⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a}, fun g hg => hg.2,
      le_antisymm (fun f hf => ?_)
      (Ideal.span_le.mpr fun g hg => hg.1)⟩
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span
      ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩
  refine ⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩
  ·
    have hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩}) := by
      rintro _ ⟨p, rfl⟩
      rw [show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
        (Algebra.subset_adjoin (Or.inr rfl))
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv,
      aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]
    rfl
  ·
    have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
      rintro _ ⟨p, rfl⟩
      exact (IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val
    have e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r := by
      funext ⟨k, i⟩; obtain rfl := hK k; rfl
    rw [Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e,
      ← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ClosedPointAffineChart

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')


omit [Fintype T] in
theorem ratio_mem (t u : T) : y ⟨(), u⟩ / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩


omit [Fintype T] in
theorem mem_chart_of_mem_curveRing {b : K'} (hb : b ∈ curveRing y) (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    b ∈ chartRingZ y (fun _ => t) :=
  mem_curveRing.mp hb (fun _ => t) (fun _ => ht)


omit [Fintype T] in
theorem mem_curveRing_of_forall {b : K'}
    (h : ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t)) : b ∈ curveRing y := by
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := h (c ()) (hc ())
  rwa [← hc'] at h1


omit [Fintype T] in
theorem div_pow_mem_of_mem_chartLat {e : ℕ} {g : K'} (hg : g ∈ chartLat y 1 e) (t : T)
    (ht : y ⟨(), t⟩ ≠ 0) : g / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t) := by
  have h : g * ∏ k : Unit, y ⟨k, t⟩ ^ (-((e : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y (fun _ => t) :=
    hg (fun _ => t) (fun _ => ht)
  simpa [zpow_neg, zpow_natCast, div_eq_mul_inv] using h


omit [Fintype T] in
theorem exists_mul_inv_mem {m : Ideal (curveRing y)} [m.IsPrime] {e : ℕ} {g : K'} (hg0 : g ≠ 0)
    (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (y ⟨(), t⟩ ^ e / g) ∈ chartRingZ y (fun _ => t) := by
  by_contra hcon
  push Not at hcon
  let R : Subring K' := (chartRingZ y (fun _ => t)).toSubring
  have hBR : curveRing y ≤ R := fun b hb => mem_chart_of_mem_curveRing y hb t ht
  let S' : Submonoid R := m.primeCompl.map (Subring.inclusion hBR)
  let z : R := ⟨g / y ⟨(), t⟩ ^ e, div_pow_mem_of_mem_chartLat y hgL t ht⟩
  have hyt : y ⟨(), t⟩ ^ e ≠ 0 := pow_ne_zero _ ht
  have hdisj : Disjoint ((Ideal.span {z} : Ideal R) : Set R) (S' : Set R) := by
    rw [Set.disjoint_left]
    intro r hr hrS
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hrS
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : (w : K') * (g / y ⟨(), t⟩ ^ e) = (s : K') := congrArg Subtype.val hw
    apply hcon s hs
    rw [← h1, show (w : K') * (g / y ⟨(), t⟩ ^ e) * (y ⟨(), t⟩ ^ e / g) = (w : K') by field_simp]
    exact w.2
  obtain ⟨q, hq, hzq, hqS⟩ := Ideal.exists_le_prime_disjoint _ S' hdisj
  obtain ⟨W, hRW, hunit, hlt⟩ := ClosedPointUnitSection.exists_valuationSubring R q
  have hBW : ∀ b : curveRing y, (b : K') ∈ W := fun b => hRW (Subring.inclusion hBR b)
  have hBunit : ∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1 := by
    intro b hb
    apply hunit (Subring.inclusion hBR b)
    intro hbq
    exact Set.disjoint_left.mp hqS hbq (Submonoid.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hW W hBW hBunit t
  have h2 : W.valuation (z : K') < 1 := hlt z (hzq (Ideal.subset_span (Set.mem_singleton z)))
  have h3 : (z : K') * (y ⟨(), t⟩ ^ e / g) = 1 := by
    show g / y ⟨(), t⟩ ^ e * (y ⟨(), t⟩ ^ e / g) = 1
    field_simp
  have h4 := congrArg W.valuation h3
  rw [map_mul, map_one] at h4
  have h5 : W.valuation (y ⟨(), t⟩ ^ e / g) ≤ 1 := (W.valuation_le_one_iff _).mpr h1
  have h6 : W.valuation (z : K') * W.valuation (y ⟨(), t⟩ ^ e / g) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h5) h2
  exact ne_of_lt h6 h4

theorem exists_mul_div_mem_curveRing {m : Ideal (curveRing y)} (hm : m.IsMaximal) {e : ℕ} {g : K'}
    (hg0 : g ≠ 0) (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    {h : K'} (hh : ∀ t : T, y ⟨(), t⟩ ≠ 0 → h / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t)) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (h / g) ∈ curveRing y := by
  classical
  have := hm.isPrime
  have key : ∀ t : T, ∃ s : curveRing y, s ∉ m ∧
      (y ⟨(), t⟩ ≠ 0 → (s : K') * (h / g) ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, fun h1 => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (h' ht).elim⟩
    · obtain ⟨s, hs, hsm⟩ := exists_mul_inv_mem y hg0 hgL hW t ht
      refine ⟨s, hs, fun _ => ?_⟩
      have e1 : (s : K') * (h / g) = h / y ⟨(), t⟩ ^ e * ((s : K') * (y ⟨(), t⟩ ^ e / g)) := by
        field_simp
      rw [e1]
      exact mul_mem (hh t ht) hsm
  choose S hSm hS using key
  refine ⟨∏ t, S t, fun hmem => ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hSm t ht
  · apply mem_curveRing_of_forall
    intro t ht
    have e1 : ((∏ u, S u : curveRing y) : K') * (h / g) =
        (∏ u ∈ Finset.univ.erase t, (S u : K')) * ((S t : K') * (h / g)) := by
      push_cast
      rw [← Finset.mul_prod_erase Finset.univ (fun u => (S u : K')) (Finset.mem_univ t)]
      ring
    rw [e1]
    exact mul_mem (prod_mem fun u _ => mem_chart_of_mem_curveRing y (S u).2 t ht) (hS t ht)

end ClosedPointAffineChart

theorem ClosedPointChart.proof (hU : ClosedPointUnitSection.Statement) : ClosedPointChart.Statement := by
  intro T _ K' _ _ y hy m hm
  obtain ⟨e, g, he, hg0, hgL, hW⟩ := hU T K' y hy m hm
  have := hm.isPrime
  obtain ⟨W, hBW, hBunit, hBlt⟩ := ClosedPointUnitSection.exists_valuationSubring (curveRing y) m
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => W.valuation (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hratio : ∀ u, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ W := by
    intro u
    apply W.mem_of_valuation_le_one
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hyt))).mpr
      (ht u (Finset.mem_univ _))
  have hchartW : ∀ x ∈ chartRingZ y (fun _ => t), x ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
      exact hratio u
    | algebraMap r => rw [eq_intCast]; exact intCast_mem W r
    | add x z _ _ hx hz => exact add_mem hx hz
    | mul x z _ _ hx hz => exact mul_mem hx hz
  have hinv : y ⟨(), t⟩ ^ e / g ∈ W := hW W hBW hBunit t
  have hgt : g / y ⟨(), t⟩ ^ e ∈ W :=
    hchartW _ (ClosedPointAffineChart.div_pow_mem_of_mem_chartLat y hgL t hyt)
  have hval : W.valuation (y ⟨(), t⟩ ^ e / g) = 1 := by
    have h1 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) = 1 := by
      rw [← map_mul, show y ⟨(), t⟩ ^ e / g * (g / y ⟨(), t⟩ ^ e) = 1 by
        field_simp [pow_ne_zero e hyt]]
      exact map_one _
    have h2 := (W.valuation_le_one_iff _).mpr hinv
    have h3 := (W.valuation_le_one_iff _).mpr hgt
    by_contra hne
    have h4 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) (lt_of_le_of_ne h2 hne)
    exact ne_of_lt h4 h1
  have hmon : ∀ u t' : T, y ⟨(), t'⟩ ≠ 0 →
      y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e ∈ chartRingZ y (fun _ => t') := by
    intro u t' ht'
    have e1 : y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e =
        (y ⟨(), u⟩ / y ⟨(), t'⟩) * (y ⟨(), t⟩ / y ⟨(), t'⟩) ^ (e - 1) := by
      rw [div_pow, div_mul_div_comm, mul_pow_sub_one (by omega : e ≠ 0)]
    rw [e1]
    exact mul_mem (ClosedPointAffineChart.ratio_mem y t' u)
      (pow_mem (ClosedPointAffineChart.ratio_mem y t' t) _)
  have hpow : y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) = y ⟨(), t⟩ ^ e := mul_pow_sub_one (by omega) _
  obtain ⟨s0, hs0, hs0B⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon t)
  have ha0 : (⟨_, hs0B⟩ : curveRing y) ∉ m := by
    intro hmem
    have h1 := hBlt _ hmem
    change W.valuation ((s0 : K') * (y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) / g)) < 1 at h1
    rw [map_mul, hpow, hval, hBunit s0 hs0, one_mul] at h1
    exact lt_irrefl _ h1
  refine ⟨t, hyt, fun u => ?_⟩
  obtain ⟨su, hsu, hsuB⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon u)
  refine ⟨⟨_, hsuB⟩ * s0, su * ⟨_, hs0B⟩, fun hmem => ?_, ?_⟩
  · rcases hm.isPrime.mem_or_mem hmem with h | h
    · exact hsu h
    · exact ha0 h
  · push_cast
    field_simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

instance isPrime_map_C_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).2 inferInstance

abbrev nagataRing (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R))

def VertPointNagata.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : T → curveRing y)
          (hb : ∀ u, b u ∉ curvePtIdeal y W), (∀ u, (b u : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a u) →
          ∃ Φ : Localization.AtPrime W →+* nagataRing (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing (fun _ : Unit => T)) _) ∧
            ∀ f : MRing (fun _ : Unit => T), Φ (algebraMap _ _ f) =
              algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ _ : Unit, T) => Polynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p.2)
                  (⟨b p.2, hb p.2⟩ : (curvePtIdeal y W).primeCompl)) * Polynomial.X) f)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

namespace DualStdGenDeg

def fibreBlk₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) :=
  ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩

theorem eq_fibreBlk₀ (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) : k = fibreBlk₀ := by
  rcases k with ⟨⟨⟩ | ⟨⟩, h⟩
  · rfl
  · exact absurd ⟨(), rfl⟩ h

def fibreCoord {T : Type} {i : ℕ} (c : T) :
    ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k
  | ⟨Sum.inl (), _⟩ => c
  | ⟨Sum.inr (), h⟩ => absurd ⟨(), rfl⟩ h

theorem range_eq {T Φ' : Type} [Field Φ'] {i : ℕ} (x' : (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → Φ') (d : Φ') :
    (Set.range fun p : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
        fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k) => x' ⟨p.1.1, p.2⟩ / d) =
      Set.range fun t : T => x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) / d := by
  ext y
  constructor
  · rintro ⟨⟨⟨⟨⟩ | ⟨⟩, h⟩, t⟩, rfl⟩
    · exact ⟨t, rfl⟩
    · exact absurd ⟨(), rfl⟩ h
  · rintro ⟨t, rfl⟩
    exact ⟨⟨fibreBlk₀, t⟩, rfl⟩

end DualStdGenDeg


open DualStdGenDeg in
theorem DualStdGenDeg.proof (hPt : OneBlockPointDeg.Statement) (hRat : DualStdFibreRatios.Statement) :
    DualStdGenDeg.Statement := by
  intro K _ _ i T _ _ b G J hi hJ
  obtain ⟨c, hc, hrank, htr⟩ := hRat K i T b G hi
  have hfin : Module.Finite G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
      G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
        G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) :=
    Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)
  have key := hPt G.Φ G.Φ' (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr) fibreBlk₀ eq_fibreBlk₀
    (fun q => G.x' ⟨q.1.1, q.2⟩) (fibreCoord c) hc
  beta_reduce at key
  rw [range_eq G.x'] at key
  obtain ⟨hV, hch, hdeg⟩ := key hfin htr
  have hJ0 := hJ.1 (fibreIdeal Sum.inr G) Fin.elim0 (fibreCoord c) hV hch
  rw [hJ0]
  exact congrArg ((↑) : ℕ → ℤ) (hdeg.trans hrank)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

namespace VerticalPointInjective

theorem coord_ne_zero {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (t : T)
    (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ mCoordIdeal y) : y ⟨(), t⟩ ≠ 0 := by
  intro h0
  apply ht
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp {T : Type} [Fintype T] {K' : Type} [Field K']
    (y : (Σ _ : Unit, T) → K') (s : MRing (fun _ : Unit => T)) (hA : IsArithVar (mCoordIdeal y) 1)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1)) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ Unit (fun _ => T) (mCoordIdeal y) s (fun _ => 1) hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ Unit (fun _ => T) _ W hJ hW.1)

end VerticalPointInjective


open VerticalPointInjective in
theorem VertPointInj.proof (hCh : VertPointChart.Statement) : VertPointInj.Statement := by
  intro T _ K' _ _ y s hA hs hsP W hW W' hW' hWW'
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨t', ht'⟩ := hW'.2 ()
  have hyt : y ⟨(), t⟩ ≠ 0 :=
    VerticalPointInjective.coord_ne_zero y t fun h => ht (le_sup_left.trans hW.1.1.2 h)
  obtain ⟨hmax, hrat, hform⟩ := hCh T K' y s hA hs hsP W hW t ht
  obtain ⟨-, -, hform'⟩ := hCh T K' y s hA hs hsP W' hW' t' ht'
  obtain ⟨a', b', hb', hab'⟩ := hrat t'
  have hab'' : (b' : K') * y ⟨(), t'⟩ = a' * y ⟨(), t⟩ := by
    rw [← hab']; field_simp
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := VerticalPointInjective.isMultiHomogIdeal_of_mem_divSupp y s hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    have he' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun _ => e ()) := by
      have : e = fun _ => e () := funext fun u => by cases u; rfl
      rwa [this] at he
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' (e ()) g he').1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform (e ()) g he').2 ⟨a * a' ^ e (), b' ^ e () * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · exact hb' (hmax.isPrime.mem_of_pow_mem _ h)
      · exact hb h
    · push_cast
      calc (b' : K') ^ e () * b * aeval y g = a * ((b' : K') * y ⟨(), t'⟩) ^ e () := by
            rw [mul_assoc, habg]; ring
        _ = _ := by rw [hab'']; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertRIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

namespace VerticalIndex

variable {T : Type} [Fintype T] {K' : Type} [Field K']

theorem aeval_mem_sectionMod (y : (Σ _ : Unit, T) → K') {s : MRing (fun _ : Unit => T)}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1)) : aeval y s ∈ sectionMod y :=
  HilbertSamuel.NormCountBounded.secM_le_chartLat y 1 (Submodule.subset_span ⟨s, hs, rfl⟩)


omit [Fintype T] in
theorem span_toAddSubgroup (y : (Σ _ : Unit, T) → K') (x : K') :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩


omit [Fintype T] in
theorem genIndex_eq_card (y : (Σ _ : Unit, T) → K') {x : K'} (hx : x ∈ sectionMod y) :
    genIndex (chartLat y (fun _ => 1) 1) (curveMul y x) = Nat.card (sectionQuot y x) := by
  have hle : curveMul y x ≤ chartLat y (fun _ => 1) 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end VerticalIndex


open IndefiniteRowSideFullHecke.HeightsSet in
theorem VertRIndex.proof (hL : LogCardLength.Statement) (hF : SectionQuotFinite.Statement)
    (hV : VertPointLength.Statement) (hR : VertPointResidue.Statement) : VertRIndex.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  have := hF T K' y s hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV T K' y s hP hs hsP
  rw [VerticalIndex.genIndex_eq_card y (VerticalIndex.aeval_mem_sectionMod y hs),
    hL (curveRing y) (sectionQuot y (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s, (locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) : ℝ) *
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (CurveDivVertical.full Unit (fun _ => T) _ s _ hP hs hsP W hW), hmult W hW,
          ← hR T K' y s hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0},
          (locLen m (sectionQuot y (aeval y s)) : ℝ) * Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleSub
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSimpleSub.proof (hBasis : DualTopBasisChange.Statement)
    (hStep : DualTopSimpleStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSimpleSub.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hlt hcov
  have hle := hlt.le
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStep K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hlt hcov hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSubLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSubLattice.proof (hBasis : DualTopBasisChange.Statement)
    (hStacked : DualTopStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSubLattice.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hle
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStacked K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hle hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end

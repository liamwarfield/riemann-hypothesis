module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def sectionMod (y : (Σ k, ι k) → Ω) : Submodule (curveRing y) Ω where
  carrier := chartLat y (fun _ => 1) 1
  zero_mem' := (chartLat y (fun _ => 1) 1).zero_mem
  add_mem' := fun ha hb => (chartLat y (fun _ => 1) 1).add_mem ha hb
  smul_mem' := fun b m hm c hc => by
    have hb : (b : Ω) ∈ chartRingZ y c := mem_curveRing.mp b.2 c hc
    have hm' := hm c hc
    rw [Subring.smul_def, smul_eq_mul, mul_assoc]
    exact mul_mem hb hm'

abbrev sectionQuot (y : (Σ k, ι k) → Ω) (x : Ω) : Type _ :=
  ↥(sectionMod y) ⧸ (Submodule.span (curveRing y) {x}).comap (sectionMod y).subtype

def curvePtIdeal (y : (Σ k, ι k) → Ω) (W : Ideal (MRing ι)) : Ideal (curveRing y) :=
  Ideal.span {b | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ W ∧ h ∉ W ∧
    (b : Ω) * aeval y h = aeval y g}

end Objects

def SectionQuotFinite.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Finite (sectionQuot y (aeval y s))

def VertPointLength.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
          {m | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0} ∧
        ∀ W ∈ divSupp (mCoordIdeal y) s,
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (sectionQuot y (aeval y s))

def VertPointResidue.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        (geoNum 0 W Fin.elim0 : ℝ) * Real.log (charOf W) =
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField Matrix

noncomputable section

theorem single_mem_dualLattice_standard (K : Type) [Field K] [NumberField K] {i : ℕ} (j : Fin i) :
    (Pi.single j 1 : Fin i → K) ∈ dualLattice (HermLattice.standard K i) := by
  intro x hx
  rw [single_one_dotProduct]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    by_cases h : j = k
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul a y _ hy =>
    obtain ⟨c, hc⟩ := hy
    exact ⟨a * c, by simp [hc, Algebra.smul_def]⟩

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def dualStdCoordMat (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    ∀ _ : Unit, Fin i → T → ℤ :=
  fun _ j t => b.repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩ t


omit [DecidableEq T] in
theorem dualStdCoordMat_sum (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (j : Fin i) :
    ∑ t, dualStdCoordMat b () j t • (b t : Fin i → K) = Pi.single j 1 := by
  have h := congrArg (fun v : dualLattice (HermLattice.standard K i) => (v : Fin i → K))
    (b.sum_repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

def DualStdBasePtFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdImageBot.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) = ⊥

def DualStdGenDeg.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))))
    (J : IFamily G.Φ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))),
    1 ≤ i → IsFieldIntersection J →
    J (fibreIdeal Sum.inr G) 0 Fin.elim0 = (Module.finrank ℚ K : ℤ)

def DualStdMetricPull.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b),
      (dualLine (HermLattice.standard K i) b hb).h z =
        (fsMulti (PBlk i)).h (linApply (ι₂ := PBlk i) (dualStdCoordMat b) z)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopStacked
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace DualTopStackedExistence

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem dualLattice_mono {F F' : HermLattice K i} (h : F'.lattice ≤ F.lattice) :
    dualLattice F ≤ dualLattice F' :=
  fun _ hφ x hx => hφ x (h hx)

theorem card_eq_of_bijective {F : HermLattice K i} {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    Fintype.card T = Fintype.card ((K →+* ℂ) × Fin i) := by
  have h := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  exact h.symm

theorem exists_stacked {F F' : HermLattice K i} (h : F'.lattice ≤ F.lattice) {T T' : Type} [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T' ℤ (dualLattice F')) (hcard : Fintype.card T = Fintype.card T') :
    ∃ (b₁ : Module.Basis T' ℤ (dualLattice F)) (b₁' : Module.Basis T' ℤ (dualLattice F')) (a : T' → ℤ),
      ∀ t, (b₁ t : Fin i → K) = a t • (b₁' t : Fin i → K) := by
  let eN := Submodule.comapSubtypeEquivOfLe (dualLattice_mono h)
  have hrank : Module.finrank ℤ ((dualLattice F).comap (dualLattice F').subtype) =
      Module.finrank ℤ (dualLattice F') := by
    rw [eN.finrank_eq, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b', hcard]
  obtain ⟨b₁', a, ab, hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b' hrank
  refine ⟨ab.map eN, b₁', a, fun t => ?_⟩
  have h1 := congrArg (fun x : dualLattice F' => (x : Fin i → K)) (hab t)
  simp only [Module.Basis.map_apply]
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe]
  simpa using h1

end DualTopStackedExistence

def DualTopStacked.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (a : T → ℤ) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice ≤ F.lattice →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    II Unit (dualBlocks T) (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (∑ t, Real.log |(a t : ℝ)|) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleSub
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualTopSimpleSub.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F'.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

namespace DualTopSimpleSubExample

end DualTopSimpleSubExample


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySymmetry

theorem cxHessian_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by
  have h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z := by
    funext z
    exact fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
    rw [h1]
    exact fderiv_sub (hf' y) (hg' y)
  ext i j
  simp only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem mixedDisc_update_sub {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]

theorem maDensity_update_sub {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring

theorem update_comp_swap {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'

end ChartEnergySymmetry


open ChartEnergySymmetry in
theorem ChartEnergySymm.proof (hI : ChartIbpSymm.Statement) : ChartEnergySymm.Statement := by
  intro e A B C D T p hA hB hC hD hT
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := p.pos; omega⟩
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ
  set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def
  have hT' : ∀ i, (T' i).PosDef := fun i => hT _
  have hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) =
      Function.update (fun j => hermChartPot (T j)) p (hermChartPot X) := fun X => by
    funext j
    exact Function.apply_update (fun _ M => hermChartPot M) T p X j
  have hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y,
      maDensity (fun j => hermChartPot (Function.update T p X j)) y -
          maDensity (fun j => hermChartPot (Function.update T p Y j)) y =
        maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot Y y')
          fun i => hermChartPot (T' i)) y := by
    intro X Y hX hY y
    rw [hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX)
      (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]
  simp_rw [hdiff C D hC hD, hdiff A B hA hB]
  exact hI n A B C D T' hA hB hC hD hT'

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i), F'.lattice ≤ F.lattice →
    (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup =
      F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ClosedPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegStandard
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

theorem DualGeomDegStandard.proof (hD : DualGeomDegCharts.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualGeomDegStandard.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  have hterm : ∀ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) =
      chartMass (1 : Matrix (Fin (i - 1 + 1)) (Fin (i - 1 + 1)) ℂ) := fun σ =>
    hM _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
  rw [e1, hE, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Embeddings.card K ℂ, nsmul_eq_mul]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualMetricEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

namespace DualMetricEnergyAlt

theorem log_det_re_sub {m : Type} [Fintype m] [DecidableEq m] {H A : Matrix m m ℂ} (hH : H.PosDef)
    (hA : Function.Bijective A.mulVec) :
    Real.log (Aᴴ * H * A).det.re - Real.log (Aᴴ * A).det.re = Real.log H.det.re := by
  have hd : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hA.1)).ne_zero
  obtain ⟨hre, him⟩ := Complex.lt_def.mp hH.det_pos
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hHd : H.det = (H.det.re : ℂ) := Complex.ext (by simp) (by simp [← him])
  have hn : 0 < Complex.normSq A.det := Complex.normSq_pos.mpr hd
  have e1 : (Aᴴ * H * A).det.re = Complex.normSq A.det * H.det.re := by
    rw [det_mul, det_mul, det_conjTranspose, hHd, mul_right_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have e2 : (Aᴴ * A).det.re = Complex.normSq A.det := by
    rw [det_mul, det_conjTranspose, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [e1, e2, Real.log_mul hn.ne' hre.ne']
  ring

end DualMetricEnergyAlt

theorem DualMetricEnergy.proof (hD : DualEnergyCharts.Statement) (hC : ChartEnergy.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualMetricEnergy.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  rw [e1, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun k _ => hE k, Finset.sum_comm]
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hterm : ∀ σ : K →+* ℂ,
      ∑ k ∈ Finset.range (n + 1), chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k =
        1 / 2 * Real.log (F.metric σ).det.re *
          chartMass (1 : Matrix (Fin (n + 1 - 1 + 1)) (Fin (n + 1 - 1 + 1)) ℂ) := by
    intro σ
    have h := hC (n + 1 - 1) _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
      (Matrix.PosDef.conjTranspose_mul_self (A σ) (hA σ).1)
    have hl := DualMetricEnergyAlt.log_det_re_sub (m := Fin (n + 1)) (F.posDef σ) (hA σ)
    rw [hl] at h
    exact h
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_mul, ← Finset.mul_sum]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopLatticeChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace TopDualLatticeChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def supStandard (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice ⊔ (HermLattice.standard K i).lattice
  fg := F.fg.sup (HermLattice.standard K i).fg
  span_eq := eq_top_iff.mpr (F.span_eq ▸ Submodule.span_mono
    (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp


omit [NumberField K] in
theorem gramAt_one_single (σ : K →+* ℂ) :
    gramAt (1 : Matrix (Fin i) (Fin i) ℂ) σ (fun j : Fin i => (Pi.single j 1 : Fin i → K)) = 1 := by
  ext a c
  simp only [gramAt, embVec, Matrix.one_mulVec, dotProduct, Pi.star_apply, Pi.single_apply,
    apply_ite σ, map_one, map_zero, Matrix.one_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem standard_degree : (HermLattice.standard K i).degree = 0 := by
  have hinf : (HermLattice.standard K i).lattice ⊓
      (Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K))).restrictScalars (𝓞 K) =
      (HermLattice.standard K i).lattice :=
    inf_eq_left.mpr (Submodule.span_le_restrictScalars (𝓞 K) K _)
  simp only [HermLattice.degree, subDegree, hinf]
  have hstd : (HermLattice.standard K i).metric = fun _ => 1 := rfl
  simp only [hstd, gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero, genIndex]
  show Real.log (((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
    (HermLattice.standard K i).lattice.toAddSubgroup : ℝ) /
      ((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
        (HermLattice.standard K i).lattice.toAddSubgroup : ℝ)) = 0
  simp [AddSubgroup.relIndex_self]

end TopDualLatticeChange


open TopDualLatticeChange in
theorem DualTopLatticeChange.proof (hSub : DualTopSubLattice.Statement) :
    DualTopLatticeChange.Statement := by
  intro K _ _ i F T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨TG, hTG, hdTG, ⟨bG⟩⟩ := DualLatticeBasisExists.proof K i (supStandard F)
  have hbG := DualEmbBijective.proof K i (supStandard F) TG bG
  have h1 := hSub K i (supStandard F) F TG T bG hbG b hb II hi hII le_sup_left
  have h2 := hSub K i (supStandard F) (HermLattice.standard K i) TG T' bG hbG b' hb' II hi hII
    le_sup_right
  have hstd : (HermLattice.standard K i).withStdMetric.degree = 0 := standard_degree
  have hline : dualLine (HermLattice.standard K i).withStdMetric b' hb' =
      dualLine (HermLattice.standard K i) b' hb' := rfl
  rw [hline, hstd] at h2
  rw [h1, h2]
  ring

end

end GroundTheory.Heights₂.Heights
end

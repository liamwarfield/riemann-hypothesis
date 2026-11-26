module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory

theorem glueMeas_univ_ne_top_of_compact {M : Type} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type}
    (e : ι → OpenPartialHomeomorph M (V n)) (hcov : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (r : ι → V n → ℝ) (hr : ∀ i, ContinuousOn (r i) (e i).target)
    (hc : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) :
    GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  classical
  set μ := GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) with hμ
  have hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ENNReal.ofReal (r i (e i y)) =
        ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (r j (e j y)) := by
    intro i j y hi hj
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hc i j y hi hj]
  have hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ μ U < ∞ := by
    intro y
    obtain ⟨i, hi⟩ := hcov y
    have hT : (e i).target ∈ nhds ((e i) y) := (e i).open_target.mem_nhds ((e i).map_source hi)
    obtain ⟨δ, hδ, hδs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hT
    set U := (e i).source ∩ (e i) ⁻¹' Metric.ball ((e i) y) δ with hUdef
    have hUo : IsOpen U :=
      (e i).continuousOn.isOpen_inter_preimage (e i).open_source Metric.isOpen_ball
    have hUs : U ⊆ (e i).source := inter_subset_left
    have himg : (e i) '' U ⊆ Metric.closedBall ((e i) y) δ := by
      rintro _ ⟨z, hz, rfl⟩
      exact Metric.ball_subset_closedBall hz.2
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall ((e i) y) δ).exists_bound_of_continuousOn ((hr i).mono hδs)
    refine ⟨U, hUo, ⟨hi, Set.mem_preimage.mpr (Metric.mem_ball_self hδ)⟩, ?_⟩
    have hm := GlobalTheory.ChartGlue.measurableSet_image (e i) hUo.measurableSet hUs
    rw [hμ, GlobalTheory.ChartGlue.glueMeas_apply e _ hd hρ i hUo.measurableSet hUs,
      GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hUo.measurableSet hUs]
    calc ∫⁻ v in (e i) '' U, ENNReal.ofReal (r i ((e i) ((e i).symm v)))
        ≤ ∫⁻ _ in (e i) '' U, ENNReal.ofReal C := by
          refine setLIntegral_mono' hm fun v hv => ENNReal.ofReal_le_ofReal ?_
          rw [(e i).right_inv (hδs (himg hv))]
          have := hC v (himg hv)
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal C * volume ((e i) '' U) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * volume (Metric.closedBall ((e i) y) δ) := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  choose U hUo hyU hUf using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => mem_iUnion.2 ⟨y, hyU y⟩)
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ht) ?_)
  exact (measure_biUnion_finset_le t U).trans_lt (ENNReal.sum_lt_top.2 fun y _ => hUf y)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompactStatement
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type} (e : ι → OpenPartialHomeomorph M (V n)), (∀ y, ∃ i, y ∈ (e i).source) → (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → ∀ (r : ι → V n → ℝ), (∀ i, ContinuousOn (r i) (e i).target) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) → GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  first | exact @GlobalTheory.glueMeas_univ_ne_top_of_compact | exact GlobalTheory.glueMeas_univ_ne_top_of_compact | (intros; apply GlobalTheory.glueMeas_univ_ne_top_of_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullback
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CechBC

universe v u

theorem widePullback_isPullback {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (hP : IsPullback a f' f b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] :
    IsPullback
      (WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, hP.w, ← Category.assoc, WidePullback.π_arrow]))
      (WidePullback.base (fun _ : Fin (n + 1) => f')) (WidePullback.base (fun _ : Fin (n + 1) => f)) b := by
  refine IsPullback.of_isLimit' ⟨WidePullback.lift_base _ _ _ _⟩ (PullbackCone.IsLimit.mk _
    (fun s => WidePullback.lift s.snd
      (fun i => hP.lift (s.fst ≫ WidePullback.π _ i) s.snd
        (by rw [Category.assoc, WidePullback.π_arrow, s.condition]))
      (fun i => hP.lift_snd _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, IsPullback.lift_fst]
    · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, s.condition]
  · intro s
    exact WidePullback.lift_base _ _ _ _
  · intro s m h1 h2
    apply WidePullback.hom_ext
    · intro j
      apply hP.hom_ext
      · rw [WidePullback.lift_π, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, WidePullback.lift_π]
      · rw [WidePullback.lift_π, IsPullback.lift_snd, Category.assoc, WidePullback.π_arrow, h2]
    · rw [WidePullback.lift_base, h2]

theorem lift_comp_lift {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (w : a ≫ f = f' ≫ b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] {T : C}
    (g : T ⟶ X') (e : Fin (n + 1) → (T ⟶ Y')) (he : ∀ i, e i ≫ f' = g)
    (g₂ : T ⟶ X) (e₂ : Fin (n + 1) → (T ⟶ Y)) (he₂ : ∀ i, e₂ i ≫ f = g₂)
    (hg : g ≫ b = g₂) (hh : ∀ i, e i ≫ a = e₂ i) :
    WidePullback.lift g e he ≫
      WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, w, ← Category.assoc, WidePullback.π_arrow]) =
      WidePullback.lift g₂ e₂ he₂ := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, WidePullback.lift_π, hh]
  · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, WidePullback.lift_base, hg]

end GlobalTheory.CechBC


open GlobalTheory.CechBC in
theorem GlobalTheory.cech_baseChange : ∀ (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X), IsPullback a f' f b → ∃ m : cech f' ⟶ cech f, IsPullback m (GlobalTheory.EtC.cechAug f') (GlobalTheory.EtC.cechAug f) (sch.map b) ∧ ∀ (k : ℕ) (U : Scheme.{0}) (x : U ⟶ X') (y : Fin (k + 1) → (U ⟶ Y')) (h : ∀ i, y i ≫ f' = x), ∃ h', (m.app (op (SimplexCategory.mk (k)))).app (op U) (cechPt f' k x y h) = cechPt f k (x ≫ b) (fun i => y i ≫ a) h' := by
  intro Y X Y' X' a f' f b hP
  have hw : yoneda.map a ≫ yoneda.map f = yoneda.map f' ≫ yoneda.map b := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hP.w]
  have hY : IsPullback (yoneda.map a) (yoneda.map f') (yoneda.map f) (yoneda.map b) := hP.map yoneda
  refine ⟨Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw), ?_, ?_⟩
  · refine IsPullback.of_forall_isPullback_app (fun n => ?_)
    exact widePullback_isPullback hY n.unop.len
  · intro k U x y h
    have h' : ∀ i, (y i ≫ a) ≫ f = x ≫ b := fun i => by rw [Category.assoc, hP.w, ← Category.assoc, h i]
    refine ⟨h', ?_⟩
    have key : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫
        (Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw)).app (op (SimplexCategory.mk k)) =
        WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map (x ≫ b)) (fun i => yoneda.map (y i ≫ a))
        (fun i => by rw [← yoneda.map_comp, h' i]) := by
      exact lift_comp_lift hw k _ _ _ _ _ _ (yoneda.map_comp x b).symm (fun i => (yoneda.map_comp (y i) a).symm)
    unfold cechPt
    erw [← NatTrans.comp_app_apply]
    exact congrArg (fun φ : yoneda.obj U ⟶ (cech f).obj (op (SimplexCategory.mk k)) => φ.app (op U) (𝟙 U)) key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCechNerve_baseChange_isPullback : ∀ (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X), IsPullback a f' f b → ∃ m : cech f' ⟶ cech f, IsPullback m (GlobalTheory.EtC.cechAug f') (GlobalTheory.EtC.cechAug f) (sch.map b) ∧ ∀ (k : ℕ) (U : Scheme.{0}) (x : U ⟶ X') (y : Fin (k + 1) → (U ⟶ Y')) (h : ∀ i, y i ≫ f' = x), ∃ h', (m.app (op (SimplexCategory.mk (k)))).app (op U) (cechPt f' k x y h) = cechPt f k (x ≫ b) (fun i => y i ≫ a) h' := by
  first | (exact @GlobalTheory.cech_baseChange) | (exact GlobalTheory.cech_baseChange) | (intros; apply GlobalTheory.cech_baseChange  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormula
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

namespace GlobalTheory.GlueCover

open GlobalTheory.ChartGlue

variable {n : ℕ}

section Null

variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

end Null

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}


set_option autoImplicit false in
open MeasureTheory Set Topology in
open scoped ENNReal in
variable {n : ℕ} in
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A} in
omit [T2Space A] [T2Space B] in
theorem _root_.GlobalTheory.GlueCover.exists_sheet
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {z : B}
    (hch : ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {U : Set B} (hUo : IsOpen U) (hzU : z ∈ U) :
    ∃ M : Set B, M ⊆ U ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        _root_.GlobalTheory.ChartGlue.glueMeas e' ρ' (M ∩ m ⁻¹' Q) = _root_.GlobalTheory.ChartGlue.glueMeas e ρ Q := by
  obtain ⟨i, j, hzj, hzi, hcompat⟩ := hch
  have hMo : IsOpen (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) :=
    (hUo.inter (e' j).open_source).inter ((e i).open_source.preimage hm)
  refine ⟨U ∩ (e' j).source ∩ m ⁻¹' (e i).source, fun w hw => hw.1.1, hMo,
    ⟨⟨hzU, hzj⟩, hzi⟩, ?_, ?_⟩
  · have hm_eq : ∀ w ∈ U ∩ (e' j).source ∩ m ⁻¹' (e i).source,
        (e i).symm (e' j w) = m w := by
      intro w hw
      rw [(hcompat w hw.1.2 hw.2).1, (e i).left_inv hw.2]
    have himage : m '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) =
        (e i).symm '' (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) := by
      rw [Set.image_image]
      exact (Set.image_congr hm_eq).symm
    rw [himage]
    have hS : IsOpen (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) :=
      (e' j).isOpen_image_of_subset_source hMo (fun w hw => hw.1.2)
    refine (e i).symm.isOpen_image_of_subset_source hS ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [OpenPartialHomeomorph.symm_source, (hcompat w hw.1.2 hw.2).1]
    exact (e i).map_source hw.2
  · intro Q hQ hQM
    have hQi : Q ⊆ (e i).source := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQM hq
      exact hw.2
    have hPm : MeasurableSet (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) :=
      hMo.measurableSet.inter (hm.measurable hQ)
    have hPj : U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q ⊆ (e' j).source :=
      fun w hw => hw.1.1.2
    rw [_root_.GlobalTheory.ChartGlue.glueMeas_apply e' ρ' hd' hρ' j hPm hPj,
      _root_.GlobalTheory.ChartGlue.glueMeas_apply e ρ hd hρ i hQ hQi,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hPm hPj,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hQ hQi]
    have himg : e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) = e i '' Q := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨m w, hw.2, ((hcompat w hw.1.1.2 hw.1.2).1).symm⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQM hq
        exact ⟨w, ⟨hw, hq⟩, (hcompat w hw.1.2 hw.2).1⟩
    rw [himg]
    refine setLIntegral_congr_fun (_root_.GlobalTheory.ChartGlue.measurableSet_image _ hQ hQi) ?_
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hQM hq
    beta_reduce
    rw [(e i).left_inv hw.2, ← (hcompat w hw.1.2 hw.2).1, (e' j).left_inv hw.1.2]
    exact (hcompat w hw.1.2 hw.2).2

end Cover

end GlobalTheory.GlueCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT : ∀ (R : Subring ℂ) (N w : ℕ)
    (f : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = _root_.ReciprocityTheory.ChartRestriction.L1.DD τ ^ w * P.eval (_root_.ReciprocityTheory.ChartRestriction.L1.jT τ) := by
  intro R N w f hN hinv hq
  obtain ⟨a, ha, haR⟩ := hq
  have hmf : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (12 * w) f := _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N _ f a hN hinv ha
  have h1 : _root_.GlobalTheory.QFam.HasQ 1 f fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) := by
    rw [_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
    obtain ⟨g, hg⟩ := hmf
    have hgf : (⇑g : ℍ → ℂ) = f := funext hg
    have h := _root_.GlobalTheory.hasQExpansion_modularForm g
    rw [hgf] at h
    simpa using h
  have hN' := _root_.GlobalTheory.QFam.hasQ_mul_spread 1 N f _ one_pos hN h1
  rw [one_mul] at hN'
  have heq := _root_.GlobalTheory.QFam.HasQ.coeff_unique hN ha hN'
  have hcoeff : _root_.ReciprocityTheory.ChartRestriction.L1.CoeffIn R (UpperHalfPlane.qExpansion 1 f) := by
    intro m
    have h := haR (N * m)
    rw [heq] at h
    simpa [_root_.GlobalTheory.QFam.spread, Nat.mul_div_cancel_left _ hN] using h
  obtain ⟨P, hPR, -, hP⟩ := _root_.ReciprocityTheory.ChartRestriction.L1.qPrin R w f hmf hcoeff
  exact ⟨P, hPR, hP⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariantStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant : ∀ (R : Subring ℂ) (N w : ℕ) (f : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → QAll (· ∈ R) N f → ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = DD τ ^ w * P.eval (jT τ) := by
  first | exact @GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | exact GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | (intros; apply GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ofArrows_sigmaι_mem_etale {ι : Type} (V : ι → Scheme.{0}) :
    Presieve.ofArrows V (Sigma.ι V) ∈ Scheme.etalePrecoverage (∐ V) := by
  refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => inferInstance⟩
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover V).exists_eq x
  exact ⟨i, y, hy⟩

theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] :
    Subsingleton (Sec F Z) := by
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  have hmem : (⊥ : Sieve Z) ∈ Scheme.etaleTopology Z := Scheme.bot_mem_grothendieckTopology (P := @Etale) Z
  refine ⟨fun a b => (hF _ hmem).isSeparatedFor.ext fun _ _ hf => ?_⟩
  simp at hf

theorem sec_sigma_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  intro R _ F ι V
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  have h := hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck (ofArrows_sigmaι_mem_etale V))
  rw [Presieve.isSheafFor_arrows_iff] at h
  have hc : ∀ x : ∀ i, Sec F (V i), Presieve.Arrows.Compatible (F.obj ⋙ forget _) (Sigma.ι V) x := by
    intro x i j Z gi gj hij
    by_cases e : i = j
    · subst e
      obtain rfl := (cancel_mono (Sigma.ι V i)).1 hij
      rfl
    · have : IsEmpty Z := ⟨fun z => (isEmpty_pullback_sigmaι_of_ne V e).false ((pullback.lift gi gj hij).base z)⟩
      have := sec_subsingleton_of_isEmpty F Z
      exact Subsingleton.elim _ _
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · obtain ⟨t, -, ht⟩ := h (fun i => Sec.res (Sigma.ι V i) a) (hc _)
    exact (ht a fun i => rfl).trans (ht b fun i => (congrFun hab i).symm).symm
  · obtain ⟨t, ht, -⟩ := h x (hc x)
    exact ⟨t, funext ht⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_sigma_res_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  first | (exact @GlobalTheory.EtC.sec_sigma_bijective) | (exact GlobalTheory.EtC.sec_sigma_bijective) | (intros; apply GlobalTheory.EtC.sec_sigma_bijective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjection
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_sigmaDesc_of_isOpenImmersion {ι : Type} (V : Scheme.{0}) (Y : ι → Scheme.{0})
    (u : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (u i)] : Etale (Sigma.desc u) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

theorem etFF_preimage_of_etale_surjective (A B : CommRingCat.{0}) (k : Spec B ⟶ Spec A)
    [Etale k] [Surjective k] : EtFF (Spec.preimage k) := by
  rw [(GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.2.1 A B _), Spec.map_preimage]
  exact ⟨inferInstance, inferInstance⟩

theorem exists_etFF_of_isAffine (A : CommRingCat.{0}) (X V : Scheme.{0}) [IsAffine X]
    (h' : X ⟶ V) (f : V ⟶ Spec A) [Etale (h' ≫ f)] [Surjective (h' ≫ f)] :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  have he : Etale (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  have hs : Surjective (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  refine ⟨Γ(X, ⊤), Spec.preimage (X.isoSpec.inv ≫ h' ≫ f), X.isoSpec.inv ≫ h',
    etFF_preimage_of_etale_surjective _ _ _, ?_⟩
  rw [Spec.map_preimage, Category.assoc]

theorem exists_etFF_refine_of_etale_surjective :
    ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f →
      ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  intro A V f hf hs
  have hopen : ∀ x : V.affineCover.I₀, IsOpen (Set.range (V.affineCover.f x ≫ f)) := fun x =>
    (V.affineCover.f x ≫ f).isOpenMap.isOpen_range
  have hcov : Set.univ ⊆ ⋃ x : V.affineCover.I₀, Set.range (V.affineCover.f x ≫ f) := by
    intro y _
    obtain ⟨v, rfl⟩ := f.surjective y
    obtain ⟨x, hx⟩ := V.affineCover.covers v
    exact Set.mem_iUnion.mpr ⟨V.affineCover.idx v, ⟨_, by rw [Scheme.Hom.comp_apply, hx]⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  let Y : t → Scheme.{0} := fun i => V.affineCover.X i.1
  let u : ∀ i, Y i ⟶ V := fun i => V.affineCover.f i.1
  haveI : ∀ i, IsAffine (Y i) := fun i => inferInstanceAs (IsAffine (Spec _))
  haveI : ∀ i, IsOpenImmersion (u i) := fun i => inferInstanceAs (IsOpenImmersion (V.affineCover.f i.1))
  haveI : Etale (Sigma.desc u) := etale_sigmaDesc_of_isOpenImmersion V Y u
  have hcomp : Sigma.desc u ≫ f = Sigma.desc fun i => u i ≫ f := by
    ext i; simp
  haveI hsurj : Surjective (Sigma.desc u ≫ f) := by
    rw [hcomp]
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    refine Set.eq_univ_of_univ_subset (fun y hy => ?_)
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩
  exact exists_etFF_of_isAffine A (∐ Y) V (Sigma.desc u) f

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection : ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f → ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  first | (exact @GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective) | (exact GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective) | (intros; apply GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCElements

theorem chains_X_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) :=
  ((chainsN R).obj E).isZero_extend_X ComplexShape.embeddingDownNat n (fun i hi => by
    change -(i : ℤ) = n at hi; omega)

theorem res_X_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  intro R _ F
  have zero_iff : ∀ (E : Spc) (n : ℤ) (c : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk c = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), (show ((HC R F).obj (op E)).X n from c.1) = ((HC R F).obj (op E)).d (n - 1) n y := by
    intro E n c
    rw [CohomologyClass.mk_eq_zero_iff]
    constructor
    · rintro ⟨m, hm, β, hβ⟩
      obtain rfl : m = n - 1 := by omega
      exact ⟨β, hβ.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨n - 1, by omega, y, hy.symm⟩
  refine ⟨?_, fun E n z hz => CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz), ?_, ?_, ?_, ?_⟩
  · intro E n hn
    refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => ?_⟩
    change Cochain ((chains R).obj E.unop) (res R F) n at a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : 0 < p
    · exact (chains_X_isZero R E.unop p hp).eq_of_src _ _
    · exact (res_X_isZero R F q (by omega)).eq_of_tgt _ _
  · intro E n x
    obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c.1, c.2, rfl⟩
  · intro E n z hz z' hz'
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _ at hy
      rw [← hy]; abel
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _
      rw [hy]; abel
  · intro E n z hz
    exact zero_iff E n _
  · intro E E' f n z hz
    refine ⟨(zcomp (Cocycle.ofHom ((chains R).map f)) (Cocycle.mk z (n + 1) rfl hz) (zero_add n)).2, ?_⟩
    rfl

end GlobalTheory.EtC.HCElements
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  first | exact @GlobalTheory.EtC.HCElements.main | exact GlobalTheory.EtC.HCElements.main | (intros; apply GlobalTheory.EtC.HCElements.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.InjResCmp

variable {R : Type} [CommRing R]

theorem cpush_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpush_comp (K : Cx R) {I J L : Cx R} (f : I ⟶ J) (g : J ⟶ L) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpush_homotopy (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (h : Homotopy f g) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K f n x = cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨x.1.comp z (by omega), ?_⟩
  rw [δ_comp x.1 z (by omega) (n + 1) 0 n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.comp_add]

open DerivedCategory in
theorem exists_quasiIso (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C) [QuasiIso ε] [(res R M).IsKInjective] :
    ∃ u : C ⟶ res R M, QuasiIso u := by
  letI := HasDerivedCategory.standard (Shv R)
  have : QuasiIso (resAug M) := (inferInstance : QuasiIso (injectiveResolution M).ι')
  let e : Q.obj C ≅ Q.obj (res R M) := (asIso (Q.map ε)).symm ≪≫ asIso (Q.map (resAug M))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj C)
    (res R M)).surjective
    ((quotientCompQhIso (Shv R)).hom.app C ≫ e.hom ≫ (quotientCompQhIso (Shv R)).inv.app (res R M))
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ?_⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have h1 := quotientCompQhIso_hom_naturality u
  have h2 : Q.map u = (quotientCompQhIso (Shv R)).inv.app C ≫ Qh.map ((HomotopyCategory.quotient _ _).map u) ≫
      (quotientCompQhIso (Shv R)).hom.app (res R M) := by
    rw [h1]; simp
  rw [h2, hg]
  infer_instance

theorem hyper_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C),
    C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ),
    Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  intro R _ M C ε hC hI hε K n
  haveI := hC
  haveI : ∀ t, Injective (C.X t) := hI
  haveI := hε
  haveI : C.IsKInjective := isKInjective_of_injective C 0
  haveI : (res R M).IsKInjective := (inferInstance : (injectiveResolution M).cochainComplex.IsKInjective)
  obtain ⟨u, hu⟩ := exists_quasiIso M C ε
  obtain ⟨e, -⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 hu
  exact ⟨{ toFun := cpush K e.inv n
           invFun := cpush K e.hom n
           left_inv := fun x => by
             change cpush K e.hom n (cpush K e.inv n x) = x
             rw [← cpush_comp, cpush_homotopy K e.homotopyInvHomId, cpush_id]
           right_inv := fun y => by
             change cpush K e.inv n (cpush K e.hom n y) = y
             rw [← cpush_comp, cpush_homotopy K e.homotopyHomInvId, cpush_id]
           map_add' := map_add _ }⟩

end GlobalTheory.EtC.InjResCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolutionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHypercohomology_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C), C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ), Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  first | exact @GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | exact GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | (intros; apply GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GmSec

def gammaIso : yoneda.obj (Spec (CommRingCat.of (MvPolynomial Unit (ULift ℤ)))) ≅ Scheme.Γ ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((AffineSpace.toSpecMvPolyIntEquiv Unit (X := U.unop)).trans (Equiv.funUnique Unit _))) (by
      intro U V f
      ext g
      rfl)


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
theorem _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ forget CommRingCat) :=
  Presieve.isSheaf_iso _ _root_.GlobalTheory.EtC.GmSec.gammaIso
    (Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

abbrev uval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op V)) : Γ(V, ⊤)ˣ :=
  Additive.toMul (ULift.down (α := Additive Γ(V, ⊤)ˣ) t)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_uval_map_eq_units_map {U V : Scheme.{0}} (g : V ⟶ U)
    (t : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U)) :
    _root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
        forget (ModuleCat.{1} (ULift.{1} ℤ))).map g.op t) =
      Units.map (Scheme.Γ.map g.op).hom.toMonoidHom (_root_.GlobalTheory.EtC.GmSec.uval t) :=
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_eq_of_uval_eq {U : Scheme.{0}}
    (s s' : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U))
    (h : _root_.GlobalTheory.EtC.GmSec.uval s = _root_.GlobalTheory.EtC.GmSec.uval s') : s = s' := by
  cases s; cases s'; congr 1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private theorem isSheaf_etaleTopology_units :
    Presieve.IsSheaf Scheme.etaleTopology.{0}
      ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) := by
  intro U S hS x hx
  have hG := _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma S hS
  let a : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((_root_.GlobalTheory.EtC.GmSec.uval (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  let b : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => (((_root_.GlobalTheory.EtC.GmSec.uval (x f hf))⁻¹ : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have ha : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg (fun t => ((_root_.GlobalTheory.EtC.GmSec.uval t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
  have hb : b.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun t => (((_root_.GlobalTheory.EtC.GmSec.uval t)⁻¹ : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
    simp only [gmSec_uval_map_eq_units_map, ← map_inv] at this
    exact this
  have hA := hG.isAmalgamation ha
  have hB := hG.isAmalgamation hb
  set A := hG.amalgamate a ha
  set B := hG.amalgamate b hb
  have hAB : A * B = 1 := by
    refine hG.isSeparatedFor.ext fun V f hf => ?_
    change (Scheme.Γ.map f.op).hom (A * B) = (Scheme.Γ.map f.op).hom 1
    rw [map_mul, map_one]
    change (Scheme.Γ ⋙ forget CommRingCat).map f.op A *
      (Scheme.Γ ⋙ forget CommRingCat).map f.op B = 1
    rw [hA f hf, hB f hf]
    exact (_root_.GlobalTheory.EtC.GmSec.uval (x f hf)).mul_inv
  have hBA : B * A = 1 := by rw [mul_comm, hAB]
  let u : Γ(U, ⊤)ˣ := ⟨A, B, hAB, hBA⟩
  refine ⟨⟨Additive.ofMul u⟩, fun V f hf => gmSec_eq_of_uval_eq _ _ (Units.ext (hA f hf)),
    fun t ht => gmSec_eq_of_uval_eq _ _ (Units.ext ?_)⟩
  refine hG.isSeparatedFor.ext fun V f hf => ?_
  change ((_root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).map f.op t) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
    (Scheme.Γ ⋙ forget CommRingCat).map f.op A
  rw [ht f hf, hA f hf]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
theorem _root_.GlobalTheory.EtC.GmSec.gm_sec_bijective :
    ∀ U : Scheme.{0},
      Function.Bijective
        (_root_.GlobalTheory.EtC.ofRings.sec _root_.GlobalTheory.EtC.unitsF U) := by
  intro U
  have hP : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_etaleTopology_units)
  haveI := isIso_toSheafify Scheme.etaleTopology hP
  delta _root_.GlobalTheory.EtC.ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF)).app (op U))

end GlobalTheory.EtC.GmSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnitsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units :
    ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec unitsF U) := by
  have hGamma : Presheaf.IsSheaf Scheme.etaleTopology.{0} Scheme.Γ := by
    intro R
    have gammaIso : Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
      NatIso.ofComponents
        (fun U => (Equiv.trans (Quiver.Hom.opEquiv)
          (ΓSpec.adjunction.homEquiv U.unop (op R))).toIso)
        (by
          intro U V f
          ext g
          exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)
    exact Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (Presieve.isSheaf_iso _ gammaIso.symm
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
  have hUnits : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ unitsF) := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    let F := forget₂ CommRingCat.{0} CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat ⋙ uliftFunctor.{1, 0}
    have hF : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ F) :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ F hGamma
    exact hF
  intro U
  have := isIso_toSheafify Scheme.etaleTopology hUnits
  delta ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem exists_filtered_colimit_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  intro A O _ _ _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  have : Nonempty J := IsFiltered.nonempty
  refine ⟨J, inferInstance, inferInstance, Under.lift D t,
    { app j := Under.homMk (s.app j) (by simp [hst]) },
    ⟨Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs⟩, fun j => (hst j).1⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEtStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  first | (exact @GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt) | (exact GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt) | (intros; apply GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

instance : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance

theorem isPullback_sch_bc {S W : Scheme.{0}} (r : W ⟶ S) (U : Over S) :
    IsPullback (sch.map (pullback.snd U.hom r)) (sch.map (pullback.fst U.hom r)) (sch.map r) (sch.map U.hom) :=
  (IsPullback.of_hasPullback U.hom r).flip.map sch

theorem bc_sch_iso : ∀ (S W : Scheme.{0}) (r : W ⟶ S), ∃ e : (Over.pullback r ⋙ Over.forget W ⋙ sch) ≅ bc (sch.map r), ∀ U : Over S, e.hom.app U ≫ pullback.fst (sch.map r) (sch.map U.hom) = sch.map (pullback.snd U.hom r) ∧ e.hom.app U ≫ pullback.snd (sch.map r) (sch.map U.hom) = sch.map (pullback.fst U.hom r) := by
  intro S W r
  refine ⟨NatIso.ofComponents (fun U => (isPullback_sch_bc r U).isoPullback) ?_, fun U => ?_⟩
  · intro U V g
    have fV := (isPullback_sch_bc r V).isoPullback_hom_fst
    have sV := (isPullback_sch_bc r V).isoPullback_hom_snd
    have fU := (isPullback_sch_bc r U).isoPullback_hom_fst
    have sU := (isPullback_sch_bc r U).isoPullback_hom_snd
    apply pullback.hom_ext
    · simp only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, Category.comp_id]
      erw [fV, fU, ← Functor.map_comp, pullback.lift_snd]
    · simp only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_snd]
      erw [sV, reassoc_of% sU, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
  · exact ⟨IsPullback.isoPullback_hom_fst _, IsPullback.isoPullback_hom_snd _⟩

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem etale_mem_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔
    ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  intro U S
  constructor
  · intro hS u
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    obtain ⟨i, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 u
    exact ⟨𝒰.X i, 𝒰.f i, v, 𝒰.map_prop i, hv, hle _ _ (Presieve.ofArrows.mk i)⟩
  · intro h
    choose V j v hj hv hS using h
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V j (fun u => ⟨u, v u, hv u⟩) hj, ?_⟩
    intro W f hf
    obtain ⟨u⟩ := hf
    exact hS u

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPointsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_etale_covering_sieves_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔ ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  first | (exact @GlobalTheory.etale_mem_iff_points) | (exact GlobalTheory.etale_mem_iff_points) | (intros; apply GlobalTheory.etale_mem_iff_points  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.isIso_chains_map_of_isIso_free (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E')
    (h : ∀ n, IsIso ((free R).map (f.app n))) : IsIso ((chains R).map f) := by
  have hw : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact h n
  have : IsIso ((chainsN R).map f) := by
    unfold chainsN
    rw [Functor.comp_map]
    infer_instance
  unfold chains
  rw [Functor.comp_map]
  infer_instance

end GlobalTheory
end

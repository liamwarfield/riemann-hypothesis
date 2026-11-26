module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMixOfBaseInt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInfStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArFormExistsOfInt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arFormExists_of_int :
    (∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D →
      ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ) → GlobalTheory.Published.ArFormExists := by
  intro H k _ X _ p D hX ι _ L
  let t : X ⟶ Sp ℤ := specZIsTerminal.from X
  haveI : Module.Finite ℤ k := hX.finite
  have hL : ∀ i τ, (wZ (L i) t τ).IsCInf := fun i τ => GlobalTheory.T.wZ_isCInf' k X p t (L i) τ
  obtain ⟨Φ, hΦ⟩ := H X t D (GlobalTheory.CompanionTheory.Ar.BaseZ.isArithVar_int k X p t D hX) ι
    (fun i => GlobalTheory.CompanionTheory.Ar.BaseZ.toZ (L i) t (hL i))
  exact ⟨Φ, (GlobalTheory.T.toZ_isArFun_iff k X p t D hX ι L hL Φ).1 hΦ⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bridge
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricGlue
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricConj
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {σ σ' : k →+* ℂ}

noncomputable def conjPts (p : Y ⟶ Sp k) (h : σ = (starRingEnd ℂ).comp σ') : CxPts p σ' ≃ₜ CxPts p σ :=
  (Points.conjHomeomorph Y).subtype fun y => by
    have e : spMap σ = spMap (starRingEnd ℂ) ≫ spMap σ' := by
      rw [h, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    change y ≫ p = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ p = _
    rw [e, Category.assoc]
    exact (Points.conjHomeomorph (Sp k)).injective.eq_iff.symm

end GlobalTheory.AmbMetric
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricPart
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

section Calc

variable {P : Scheme.{0}} {q : P ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts q σ}

theorem cInfAt_mul {f g : CxPts q σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_one_sub {f : CxPts q σ → ℝ} (hf : CInfAt f y) : CInfAt (fun z => 1 - f z) y :=
  hf.comp₂ hf (G := fun x => 1 - x.1) (contDiff_const.sub contDiff_fst)

theorem cInfAt_prod {ι : Type} (s : Finset ι) {f : ι → CxPts q σ → ℝ} (hf : ∀ i ∈ s, CInfAt (f i) y) :
    CInfAt (fun z => ∏ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := q) 1 y
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact cInfAt_mul (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Calc

theorem exists_bump {P : Scheme.{0}} {q : P ⟶ Sp k} {N : ℕ} {σ : k →+* ℂ} (R : AnRead q σ N)
    [T2Space (CxPts q σ)] (y : CxPts q σ) (W : Set (CxPts q σ)) (hW : IsOpen W) (hy : y ∈ W) :
    ∃ β : CxPts q σ → ℝ, (∀ z, CInfAt β z) ∧ (∀ z, 0 ≤ β z ∧ β z ≤ 1) ∧ tsupport β ⊆ W ∧
      ∀ᶠ z in 𝓝 y, β z = 1 := by
  classical
  obtain ⟨c, hc⟩ := R.cover y
  set e := (R.chart c).e with he
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
  have hyT : e y ∈ e.target ∩ e.symm ⁻¹' W := ⟨e.map_source hc, by rw [mem_preimage, e.left_inv hc]; exact hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT (e y) hyT
  let β₀ : ContDiffBump (e y) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target ∩ e.symm ⁻¹' W :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e y) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e y) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun v hv => (hcb hv).1)
  have hCsub : C ⊆ e.source ∩ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e.map_target (hcb hv).1, (hcb hv).2⟩
  let β : CxPts q σ → ℝ := fun w => if w ∈ e.source then β₀ (e w) else 0
  have hsupp : Function.support β ⊆ C := by
    intro w hw
    simp only [Function.mem_support, β] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e y) (ε / 2) := by
        rw [← β₀.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport β ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨β, fun z => ?_, fun z => ?_, hts.trans fun w hw => (hCsub hw).2, ?_⟩
  · by_cases hz : z ∈ e.source
    · refine cInfAt_of_chart e.open_source (R.chart c) ?_ hz hz
      refine (β₀.contDiff.contDiffOn (s := e.target ∩ e.symm ⁻¹' e.source)).congr fun v hv => ?_
      have hv1 : e.symm v ∈ e.source := hv.2
      show (if e.symm v ∈ e.source then β₀ (e (e.symm v)) else 0) = β₀ v
      rw [if_pos hv1, e.right_inv hv.1]
    · have hzC : z ∉ C := fun h => hz (hCsub h).1
      refine (cInfAt_const (p := q) 0 z).congr ?_
      filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw
      by_contra h
      exact hw (hsupp h)
  · simp only [β]
    split_ifs
    · exact ⟨β₀.nonneg, β₀.le_one⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hc, Set.mem_preimage.mpr (Metric.mem_ball_self (by linarith))⟩] with w hw
    simp only [β, if_pos hw.1]
    exact β₀.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

theorem exists_partition {P : Scheme.{0}} {q : P ⟶ Sp k} {N : ℕ} {σ : k →+* ℂ} (R : AnRead q σ N)
    [CompactSpace (CxPts q σ)] [T2Space (CxPts q σ)] {J : Type} (V : J → Set (CxPts q σ)) (hV : ∀ j, IsOpen (V j))
    (hc : ∀ y, ∃ j, y ∈ V j) :
    ∃ (n : ℕ) (c : Fin n → J) (ρ : Fin n → CxPts q σ → ℝ), (∀ a y, CInfAt (ρ a) y) ∧ (∀ a y, 0 ≤ ρ a y) ∧
      (∀ a, tsupport (ρ a) ⊆ V (c a)) ∧ ∀ y, ∑ a, ρ a y = 1 := by
  classical
  choose j hj using hc
  choose β hβs hβb hβt hβ1 using fun y => exists_bump R y (V (j y)) (hV (j y)) (hj y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : CxPts q σ => interior {y | β x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hβ1 y)⟩)
  let pt : Fin t.card → CxPts q σ := fun a => (t.equivFin.symm a : CxPts q σ)
  let ψ : Fin t.card → CxPts q σ → ℝ := fun a => β (pt a)
  have hsum : ∀ x, ∑ a, ψ a x * ∏ b ∈ Finset.univ with b < a, (1 - ψ b x) = 1 - ∏ a, (1 - ψ a x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun a => j (pt a), fun a x => ψ a x * ∏ b ∈ Finset.univ with b < a, (1 - ψ b x),
    fun a y => ?_, fun a y => ?_, fun a => ?_, fun x => ?_⟩
  · exact cInfAt_mul (hβs _ y) (cInfAt_prod _ fun b _ => cInfAt_one_sub (hβs _ y))
  · exact mul_nonneg (hβb _ y).1 (Finset.prod_nonneg fun b _ => sub_nonneg.2 (hβb _ y).2)
  · exact (tsupport_mul_subset_left (f := ψ a)).trans (hβt (pt a))
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : pt (t.equivFin ⟨u, hu⟩) = u := by simp [pt]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | β u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory.AmbMetric
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricLoc
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

theorem exists_local_ext {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k} (i : X ⟶ P) [IsClosedImmersion i]
    (hi : i ≫ q = p) {σ : k →+* ℂ} (f : CxPts p σ → ℝ) (x₀ : CxPts p σ) (hf : CInfAt f x₀) :
    ∃ (V : Set (CxPts q σ)) (θ : CxPts q σ → ℝ), IsOpen V ∧ PtsOver.map i hi (spMap σ) x₀ ∈ V ∧
      (∀ y ∈ V, CInfAt θ y) ∧ ∀ x, PtsOver.map i hi (spMap σ) x ∈ V → θ (PtsOver.map i hi (spMap σ) x) = f x := by
  classical
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := hf
  have hu₀ : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ W := mem_ptsIn.1 h₁
  obtain ⟨U, hU, hiu, -⟩ := exists_isAffineOpen_mem_and_subset (X := P)
    (x := i (x₀.1 (IsLocalRing.closedPoint ℂ))) (U := ⊤) trivial
  have hU' : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  obtain ⟨h, hhV, hxh⟩ := hU'.exists_basicOpen_le (V := W ⊓ i ⁻¹ᵁ U)
    ⟨x₀.1 (IsLocalRing.closedPoint ℂ), ⟨hu₀, hiu⟩⟩ hiu
  obtain ⟨H, hH⟩ := i.app_surjective U hU h
  have hUa : IsAffineOpen (P.basicOpen H) := hU.basicOpen H
  have hpre : i ⁻¹ᵁ P.basicOpen H = X.basicOpen h := by
    rw [Scheme.preimage_basicOpen]
    exact congrArg X.basicOpen hH
  have hle : i ⁻¹ᵁ P.basicOpen H ≤ W := hpre.le.trans (hhV.trans inf_le_left)
  choose G hG using fun a => i.app_surjective (P.basicOpen H) hUa (resG X hle (g a))
  have hmem (x : CxPts p σ) : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (P.basicOpen H) ↔
      x ∈ ptsIn p σ (i ⁻¹ᵁ P.basicOpen H) := by
    rw [mem_ptsIn, mem_ptsIn]
    rfl
  have hev (x : CxPts p σ) (hx : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (P.basicOpen H)) (a : ι) :
      ev q σ (P.basicOpen H) (G a) (PtsOver.map i hi (spMap σ) x) = ev p σ W (g a) x := by
    rw [← ev_app i hi (P.basicOpen H) (G a) x]
    have e : (i.app (P.basicOpen H)) (G a) = resG X hle (g a) := hG a
    rw [e, ev_res hle ((hmem x).1 hx)]
  have hemb := PtsOver.isClosedEmbedding_map (C := ℂ) i hi (spMap σ)
  have hN : {x | f x = F fun a => ev p σ W (g a) x} ∈ 𝓝 x₀ := h₅
  rw [hemb.isInducing.nhds_eq_comap] at hN
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hN
  obtain ⟨V', hV't, hV'o, hx₀V'⟩ := mem_nhds_iff.1 ht
  have hcont : ContinuousOn (fun y (a : ι) => ev q σ (P.basicOpen H) (G a) y) (ptsIn q σ (P.basicOpen H)) :=
    continuousOn_pi.2 fun a => continuousOn_ev (G a)
  refine ⟨V' ∩ (ptsIn q σ (P.basicOpen H) ∩ (fun y (a : ι) => ev q σ (P.basicOpen H) (G a) y) ⁻¹' O),
    fun y => F fun a => ev q σ (P.basicOpen H) (G a) y,
    hV'o.inter (hcont.isOpen_inter_preimage (isOpen_ptsIn _) h₂), ?_, ?_, ?_⟩
  · have hx₀ : PtsOver.map i hi (spMap σ) x₀ ∈ ptsIn q σ (P.basicOpen H) := by
      rw [hmem, mem_ptsIn, hpre]
      exact hxh
    refine ⟨hx₀V', hx₀, ?_⟩
    simp only [Set.mem_preimage, hev x₀ hx₀]
    exact h₃
  · rintro y ⟨-, hy₁, hy₂⟩
    exact ⟨P.basicOpen H, ι, inferInstance, G, F, O, hy₁, h₂, hy₂, h₄, EventuallyEq.rfl⟩
  · rintro x ⟨hx₁, hx₂, -⟩
    have e : f x = F fun a => ev p σ W (g a) x := hts (hV't hx₁)
    rw [e]
    exact congrArg F (funext fun a => hev x hx₂ a)

end GlobalTheory.AmbMetric
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open scoped ContDiff

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

section Generic

variable {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_logSq_ev {W : Y.Opens} (u : Γ(Y, W)ˣ) (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => Real.log (‖ev p σ W u.val z‖ ^ 2)) y := by
  refine ⟨W, Unit, inferInstance, fun _ => u.val, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0}, hy,
    isOpen_ne_fun (continuous_apply ()) continuous_const, ev_ne_zero hy u.isUnit, ?_,
    Filter.EventuallyEq.rfl⟩
  refine ContDiffOn.log ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffOn ?_
  intro v hv
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

theorem cInfAt_sum {ι : Type} (s : Finset ι) {f : ι → CxPts p σ → ℝ} (hf : ∀ i ∈ s, CInfAt (f i) y) :
    CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (0 : ℝ) y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Generic

section Transport

variable {X : Scheme.{0}} {p : X ⟶ Sp k}

private theorem phi_sub_logSq_eq_of_mem_overlap (A : LB X) (hA : A.IsLB) (L : HermLB p) (w : A.Iso L.B)
    (hw : LB.Gen.IsGen w) (σ : k →+* ℂ) (a a' : L.B.ι) (b : A.ι) (y : CxPts p σ)
    (ha : y ∈ ptsIn p σ (L.B.U a)) (ha' : y ∈ ptsIn p σ (L.B.U a')) (hb : y ∈ ptsIn p σ (A.U b)) :
    (L.φ σ).φ a y - y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) =
      (L.φ σ).φ a' y - y.logSq (L.B.U a' ⊓ A.U b) (w.s (a', b)) := by
  have hV : y ∈ ptsIn p σ ((L.B.div A).U (a, b) ⊓ (L.B.div A).U (a', b)) := by
    simp only [LB.div, mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ha' hb ⊢
    tauto
  have hg := congrArg (y.logSq _) (hw (a, b) (a', b))
  rw [logSq_res _ hV, logSq_mul hV, logSq_res _ hV] at hg
  dsimp only [LB.div] at hg hV
  rw [logSq_mul hV, logSq_inv hV, logSq_res _ hV, logSq_res _ hV] at hg
  have hbb : y.logSq (A.U b ⊓ A.U b) (A.g b b) = 0 := by
    have h0 := congrArg (y.logSq _) (hA.g_self b)
    rw [logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at hb ⊢; tauto),
      logSq_one (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at hb ⊢; tauto)] at h0
    exact h0
  have ht := (L.φ σ).trans a a' y ha ha'
  have hl : Real.log (‖gv p σ L.B a a' y‖ ^ 2) = y.logSq (L.B.U a ⊓ L.B.U a') (L.B.g a a') := rfl
  rw [hl] at ht
  rw [hbb] at hg
  linarith

private theorem logSq_inf_eq_add_logSq_transition (A : LB X) (L : HermLB p) (w : A.Iso L.B)
    (hw : LB.Gen.IsGen w) (σ : k →+* ℂ) (a : L.B.ι) (b b' : A.ι) (y : CxPts p σ)
    (ha : y ∈ ptsIn p σ (L.B.U a)) (hb : y ∈ ptsIn p σ (A.U b)) (hb' : y ∈ ptsIn p σ (A.U b')) :
    y.logSq (L.B.U a ⊓ A.U b') (w.s (a, b')) =
      y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) + y.logSq (A.U b ⊓ A.U b') (A.g b b') := by
  have hV : y ∈ ptsIn p σ ((L.B.div A).U (a, b) ⊓ (L.B.div A).U (a, b')) := by
    simp only [LB.div, mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha hb hb' ⊢
    tauto
  have hg := congrArg (y.logSq _) (hw (a, b) (a, b'))
  rw [logSq_res _ hV, logSq_mul hV, logSq_res _ hV] at hg
  dsimp only [LB.div] at hg hV
  rw [logSq_mul hV, logSq_inv hV, logSq_res _ hV, logSq_res _ hV] at hg
  have haa : y.logSq (L.B.U a ⊓ L.B.U a) (L.B.g a a) = 0 := by
    have h0 := congrArg (y.logSq _) (L.isLB.g_self a)
    rw [logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ⊢; tauto),
      logSq_one (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at ha ⊢; tauto)] at h0
    exact h0
  rw [haa] at hg
  linarith

theorem exists_transport (A : LB X) (hA : A.IsLB) (L : HermLB p) (hL : LBIso A L.B) :
    ∃ (χ : ∀ σ : k →+* ℂ, Weight p σ A) (hc : ∀ σ, (χ σ).IsCInf) (hj : ∀ σ σ', (χ σ).IsConj (χ σ')),
      (⟨A, hA, χ, hc, hj⟩ : HermLB p).Isometric L := by
  obtain ⟨w, hw⟩ := hL
  have hcov : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ a, y ∈ ptsIn p σ (L.B.U a) := by
    intro σ y
    have h : ∀ x : X, ∃ a, x ∈ L.B.U a := by
      intro x
      have hx : x ∈ (⨆ i, L.B.U i) := by
        rw [L.isLB.cover]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    exact (h _).imp fun a ha => mem_ptsIn.mpr ha
  let F : ∀ σ : k →+* ℂ, A.ι → CxPts p σ → ℝ := fun σ b y =>
    (L.φ σ).φ (hcov σ y).choose y -
      y.logSq (L.B.U (hcov σ y).choose ⊓ A.U b) (w.s ((hcov σ y).choose, b))
  have hF : ∀ (σ : k →+* ℂ) (b : A.ι) (y : CxPts p σ) (a : L.B.ι), y ∈ ptsIn p σ (L.B.U a) →
      y ∈ ptsIn p σ (A.U b) → F σ b y = (L.φ σ).φ a y - y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b)) :=
    fun σ b y a ha hb => phi_sub_logSq_eq_of_mem_overlap A hA L w hw σ _ a b y (hcov σ y).choose_spec ha hb
  have htr : ∀ (σ : k →+* ℂ) (i j : A.ι), ∀ y ∈ ptsIn p σ (A.U i), y ∈ ptsIn p σ (A.U j) →
      F σ j y = F σ i y - Real.log (‖gv p σ A i j y‖ ^ 2) := by
    intro σ i j y hi hj
    obtain ⟨a, ha⟩ := hcov σ y
    rw [hF σ j y a ha hj, hF σ i y a ha hi]
    have h2 := logSq_inf_eq_add_logSq_transition A L w hw σ a i j y ha hi hj
    have hl : Real.log (‖gv p σ A i j y‖ ^ 2) = y.logSq (A.U i ⊓ A.U j) (A.g i j) := rfl
    rw [hl]
    linarith
  let χ : ∀ σ : k →+* ℂ, Weight p σ A := fun σ => ⟨hA, F σ, htr σ⟩
  have hc : ∀ σ, (χ σ).IsCInf := by
    intro σ b y hb
    obtain ⟨a, ha⟩ := hcov σ y
    have hS : ptsIn p σ (L.B.U a) ∩ ptsIn p σ (A.U b) ∈ 𝓝 y :=
      ((isOpen_ptsIn _).inter (isOpen_ptsIn _)).mem_nhds ⟨ha, hb⟩
    have h2 := cInfAt_logSq_ev (W := L.B.U a ⊓ A.U b) (w.s (a, b)) (mem_ptsIn_inf.mpr ⟨ha, hb⟩)
    have h1 : CInfAt (fun z => (L.φ σ).φ a z - z.logSq (L.B.U a ⊓ A.U b) (w.s (a, b))) y :=
      ((L.cInf σ a y ha).add h2.neg).congr (Filter.Eventually.of_forall fun z => sub_eq_add_neg _ _)
    exact h1.congr (Filter.mem_of_superset hS fun z hz => hF σ b z a hz.1 hz.2)
  have hj : ∀ σ σ', (χ σ).IsConj (χ σ') := by
    intro σ σ' b y y' hyy' hb
    obtain ⟨a, ha⟩ := hcov σ y
    have ha' := (mem_ptsIn_iff_of_conj hyy').mpr ha
    have hb' := (mem_ptsIn_iff_of_conj hyy').mpr hb
    show F σ' b y' = F σ b y
    rw [hF σ' b y' a ha' hb', hF σ b y a ha hb, L.conj σ σ' a y y' hyy' ha]
    congr 1
    unfold CxPts.logSq
    rw [ev_conj hyy' (mem_ptsIn_inf.mpr ⟨ha, hb⟩), Complex.norm_conj]
  refine ⟨χ, hc, hj, w, hw, ?_⟩
  intro σ a b y ha hb
  have h3 := hF σ b y a ha hb
  show (L.φ σ).φ a y = F σ b y + y.logSq (L.B.U a ⊓ A.U b) (w.s (a, b))
  linarith

end Transport

section Glue

variable {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k}

theorem mem_ptsIn_pull (i : X ⟶ P) (hi : i ≫ q = p) {σ : k →+* ℂ} (B : LB P) (c : B.ι) (x : CxPts p σ)
    (h : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c)) : x ∈ ptsIn p σ ((B.pull i).U fun _ => c) := by
  have h1 := (mem_ptsIn_preimage (m := PtsOver.map i hi (spMap σ)) (fun z => rfl)).mpr h
  rw [mem_ptsIn] at h1 ⊢
  simp only [LB.pull, LB.LinComb]
  rw [← SetLike.mem_coe]
  simpa [LB.wchart] using h1

theorem gv_pull (i : X ⟶ P) (hi : i ≫ q = p) {σ : k →+* ℂ} (B : LB P) (c c' : B.ι) (x : CxPts p σ)
    (h : x ∈ ptsIn p σ ((B.pull i).U fun _ => c)) (h' : x ∈ ptsIn p σ ((B.pull i).U fun _ => c')) :
    gv p σ (B.pull i) (fun _ => c) (fun _ => c') x = gv q σ B c c' (PtsOver.map i hi (spMap σ) x) :=
  (gv_linComb (m := fun _ => PtsOver.map i hi (spMap σ) x) (fun _ => rfl) h h').trans (by simp)

private theorem logSq_cocycle {Y : Scheme.{0}} {r : Y ⟶ Sp k} {σ : k →+* ℂ} (B : LB Y)
    (hB : B.IsLB) (c₁ c₂ c₃ : B.ι) (z : CxPts r σ) (h₁ : z ∈ ptsIn r σ (B.U c₁))
    (h₂ : z ∈ ptsIn r σ (B.U c₂)) (h₃ : z ∈ ptsIn r σ (B.U c₃)) :
    z.logSq (B.U c₁ ⊓ B.U c₂) (B.g c₁ c₂) + z.logSq (B.U c₂ ⊓ B.U c₃) (B.g c₂ c₃) =
      z.logSq (B.U c₁ ⊓ B.U c₃) (B.g c₁ c₃) := by
  have h0 := congrArg (z.logSq _) (hB.cocycle c₁ c₂ c₃)
  rw [logSq_mul (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto),
    logSq_res _ (by simp only [mem_ptsIn, TopologicalSpace.Opens.mem_inf] at h₁ h₂ h₃ ⊢; tauto)] at h0
  exact h0

theorem exists_weight_ext_sigma (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ q = p) {N : ℕ} (hP : IsArithVar q N)
    (hs : GenSmooth q N) (B : LB P) (hB : B.IsLB) (σ : k →+* ℂ) (χ : Weight p σ (B.pull i)) (hχ : χ.IsCInf) :
    ∃ ψ : Weight q σ B, ψ.IsCInf ∧ ∀ (c : B.ι) (x : CxPts p σ),
      PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c) → ψ.φ c (PtsOver.map i hi (spMap σ) x) = χ.φ (fun _ => c) x := by
  haveI : CompactSpace (CxPts q σ) := compactSpace σ hP.isProjOver
  haveI : T2Space (CxPts q σ) := t2Space_cxPts_of_isProjOver σ hP.isProjOver
  obtain ⟨R⟩ := hs σ
  set m := PtsOver.map i hi (spMap σ) with hm
  have hmc : IsClosed (range m) := (PtsOver.isClosedEmbedding_map i hi (spMap σ)).isClosed_range
  have hcov : ∀ y : CxPts q σ, ∃ c, y ∈ ptsIn q σ (B.U c) := by
    intro y
    have h : ∀ x : P, ∃ c, x ∈ B.U c := by
      intro x
      have hx : x ∈ (⨆ c, B.U c) := by
        rw [hB.cover]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    exact (h _).imp fun c hc => mem_ptsIn.mpr hc
  have loc : ∀ y : CxPts q σ, ∃ (c : B.ι) (V : Set (CxPts q σ)) (θ : CxPts q σ → ℝ),
      IsOpen V ∧ y ∈ V ∧ V ⊆ ptsIn q σ (B.U c) ∧ (∀ z ∈ V, CInfAt θ z) ∧
        ∀ x : CxPts p σ, m x ∈ V → θ (m x) = χ.φ (fun _ => c) x := by
    intro y
    obtain ⟨c, hc⟩ := hcov y
    by_cases hy : y ∈ range m
    · obtain ⟨x₀, rfl⟩ := hy
      have hx₀ := mem_ptsIn_pull i hi B c x₀ hc
      obtain ⟨V, θ, hV, hV₀, hθ, heq⟩ := exists_local_ext i hi (χ.φ fun _ => c) x₀ (hχ (fun _ => c) x₀ hx₀)
      exact ⟨c, V ∩ ptsIn q σ (B.U c), θ, hV.inter (isOpen_ptsIn _), ⟨hV₀, hc⟩, inter_subset_right,
        fun z hz => hθ z hz.1, fun x hx => heq x hx.1⟩
    · refine ⟨c, (range m)ᶜ ∩ ptsIn q σ (B.U c), fun _ => 0, hmc.isOpen_compl.inter (isOpen_ptsIn _),
        ⟨hy, hc⟩, inter_subset_right, fun z _ => cInfAt_const 0 z, ?_⟩
      intro x hx
      exact absurd (mem_range_self x) hx.1
  choose cc V θ hVo hyV hVsub hθ hθx using loc
  obtain ⟨n, a, ρ, hρs, hρ0, hρsupp, hρ1⟩ := exists_partition R V hVo (fun y => ⟨y, hyV y⟩)
  have hzero : ∀ t z, ρ t z ≠ 0 → z ∈ V (a t) := fun t z h0 =>
    hρsupp t (subset_tsupport _ (Function.mem_support.mpr h0))
  let Ψ : B.ι → CxPts q σ → ℝ := fun c z =>
    ∑ t : Fin n, ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c))
  have htr : ∀ (c c' : B.ι), ∀ z ∈ ptsIn q σ (B.U c), z ∈ ptsIn q σ (B.U c') →
      Ψ c' z = Ψ c z - Real.log (‖gv q σ B c c' z‖ ^ 2) := by
    intro c c' z hz hz'
    have key : ∀ t : Fin n, ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c') (B.g (cc (a t)) c')) =
        ρ t z * (θ (a t) z - z.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) -
          ρ t z * z.logSq (B.U c ⊓ B.U c') (B.g c c') := by
      intro t
      by_cases h0 : ρ t z = 0
      · simp [h0]
      have hzc := hVsub (a t) (hzero t z h0)
      have h3 := logSq_cocycle B hB (cc (a t)) c c' z hzc hz hz'
      rw [← h3]
      ring
    have hl : Real.log (‖gv q σ B c c' z‖ ^ 2) = z.logSq (B.U c ⊓ B.U c') (B.g c c') := rfl
    show ∑ t : Fin n, _ = ∑ t : Fin n, _ - _
    rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_sub_distrib, ← Finset.sum_mul, hρ1, one_mul, hl]
  refine ⟨⟨hB, Ψ, htr⟩, ?_, ?_⟩
  · intro c z hz
    show CInfAt (fun w => ∑ t : Fin n, ρ t w *
      (θ (a t) w - w.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c))) z
    apply cInfAt_sum
    intro t _
    by_cases hzV : z ∈ V (a t)
    · have hzc := hVsub (a t) hzV
      have h2 := cInfAt_logSq_ev (W := B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)
        (mem_ptsIn_inf.mpr ⟨hzc, hz⟩)
      have h1 : CInfAt (fun w => θ (a t) w - w.logSq (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) z :=
        ((hθ (a t) z hzV).add h2.neg).congr (Filter.Eventually.of_forall fun w => sub_eq_add_neg _ _)
      exact cInfAt_mul (hρs t z) h1
    · have hns : z ∉ tsupport (ρ t) := fun h => hzV (hρsupp t h)
      have hev := (notMem_tsupport_iff_eventuallyEq.mp hns)
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hev] with w hw
      simp only [Pi.zero_apply] at hw
      simp [hw]
  · intro c x hx
    show ∑ t : Fin n, ρ t (m x) * (θ (a t) (m x) -
      CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) = χ.φ (fun _ => c) x
    have key : ∀ t : Fin n, ρ t (m x) * (θ (a t) (m x) -
        CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c)) = ρ t (m x) * χ.φ (fun _ => c) x := by
      intro t
      by_cases h0 : ρ t (m x) = 0
      · simp [h0]
      have hzV := hzero t (m x) h0
      have hzc := hVsub (a t) hzV
      rw [hθx (a t) x hzV]
      have hxa := mem_ptsIn_pull i hi B (cc (a t)) x hzc
      have hxc := mem_ptsIn_pull i hi B c x hx
      have htrχ := χ.trans (fun _ => cc (a t)) (fun _ => c) x hxa hxc
      rw [gv_pull i hi B (cc (a t)) c x hxa hxc] at htrχ
      have hl : Real.log (‖gv q σ B (cc (a t)) c (PtsOver.map i hi (spMap σ) x)‖ ^ 2) =
          CxPts.logSq (m x) (B.U (cc (a t)) ⊓ B.U c) (B.g (cc (a t)) c) := rfl
      rw [hl] at htrχ
      rw [htrχ]
    rw [Finset.sum_congr rfl (fun t _ => key t), ← Finset.sum_mul, hρ1, one_mul]

end Glue

section Conj

variable {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k}

theorem cInfAt_conj {σ : k →+* ℂ} {f : CxPts q ((starRingEnd ℂ).comp σ) → ℝ} {y : CxPts q σ}
    (h : CInfAt f (conjPts q rfl y)) : CInfAt (fun z => f (conjPts q rfl z)) y := by
  obtain ⟨W, ι, hι, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hy' : y ∈ ptsIn q σ W := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mp hyW
  have evrel : ∀ z ∈ ptsIn q σ W, ∀ a, ev q ((starRingEnd ℂ).comp σ) W (g a) (conjPts q rfl z) =
      starRingEnd ℂ (ev q σ W (g a) z) := fun z hz a => ev_conj rfl hz (g a)
  have hc1 : ContDiff ℝ ∞ (fun z : ℂ => starRingEnd ℂ z) := by
    have h0 := Complex.conjCLE.contDiff (n := ∞)
    convert h0 using 1
    ext z
    rfl
  let c : (ι → ℂ) → (ι → ℂ) := fun v a => starRingEnd ℂ (v a)
  have hc : ContDiff ℝ ∞ c := contDiff_pi.mpr fun a => hc1.comp (contDiff_apply ℝ (fun _ => ℂ) a)
  refine ⟨W, ι, hι, g, fun v => F (c v), c ⁻¹' O, hy', hO.preimage hc.continuous, ?_,
    hF.comp hc.contDiffOn (mapsTo_preimage c O), ?_⟩
  · show (fun a => starRingEnd ℂ (ev q σ W (g a) y)) ∈ O
    have he : (fun a => starRingEnd ℂ (ev q σ W (g a) y)) =
        fun a => ev q ((starRingEnd ℂ).comp σ) W (g a) (conjPts q rfl y) :=
      funext fun a => (evrel y hy' a).symm
    rw [he]
    exact hmem
  · have h1 := hev.comp_tendsto ((conjPts q rfl).continuous.tendsto y)
    have h2 : ptsIn q σ W ∈ 𝓝 y := (isOpen_ptsIn W).mem_nhds hy'
    filter_upwards [h1, h2] with z hz hzW
    simp only [Function.comp] at hz
    rw [hz]
    show F _ = F _
    congr 1
    funext a
    exact evrel z hzW a

theorem exists_weight_ext (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ q = p) {N : ℕ} (hP : IsArithVar q N)
    (hs : GenSmooth q N) (B : LB P) (hB : B.IsLB) (χ : ∀ σ : k →+* ℂ, Weight p σ (B.pull i))
    (hχ : ∀ σ, (χ σ).IsCInf) (hχc : ∀ σ σ', (χ σ).IsConj (χ σ')) :
    ∃ ψ : ∀ σ : k →+* ℂ, Weight q σ B, (∀ σ, (ψ σ).IsCInf) ∧ (∀ σ σ', (ψ σ).IsConj (ψ σ')) ∧
      ∀ (σ : k →+* ℂ) (c : B.ι) (x : CxPts p σ), PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (B.U c) →
        (ψ σ).φ c (PtsOver.map i hi (spMap σ) x) = (χ σ).φ (fun _ => c) x := by
  choose ψ0 hψ0c hψ0e using fun σ => exists_weight_ext_sigma i hi hP hs B hB σ (χ σ) (hχ σ)
  have hcongr : ∀ (c : B.ι) (σ1 σ2 : k →+* ℂ), σ1 = σ2 → ∀ (z1 : CxPts q σ1) (z2 : CxPts q σ2),
      (z1 : Sp ℂ ⟶ P) = z2 → (ψ0 σ1).φ c z1 = (ψ0 σ2).φ c z2 := by
    intro c σ1 σ2 h z1 z2 hz
    subst h
    rw [Subtype.ext hz]
  have hLconj : ∀ (σ : k →+* ℂ) (c c' : B.ι) (y : CxPts q σ), y ∈ ptsIn q σ (B.U c ⊓ B.U c') →
      Real.log (‖gv q ((starRingEnd ℂ).comp σ) B c c' (conjPts q rfl y)‖ ^ 2) =
        Real.log (‖gv q σ B c c' y‖ ^ 2) := by
    intro σ c c' y hy
    unfold CxPts.gv
    rw [ev_conj rfl hy, Complex.norm_conj]
  let Ψ : ∀ σ : k →+* ℂ, B.ι → CxPts q σ → ℝ := fun σ c y =>
    ((ψ0 σ).φ c y + (ψ0 ((starRingEnd ℂ).comp σ)).φ c (conjPts q rfl y)) / 2
  have htr : ∀ (σ : k →+* ℂ) (c c' : B.ι), ∀ y ∈ ptsIn q σ (B.U c), y ∈ ptsIn q σ (B.U c') →
      Ψ σ c' y = Ψ σ c y - Real.log (‖gv q σ B c c' y‖ ^ 2) := by
    intro σ c c' y hc hc'
    have hc2 := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hc
    have hc2' := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hc'
    have e1 := (ψ0 σ).trans c c' y hc hc'
    have e2 := (ψ0 ((starRingEnd ℂ).comp σ)).trans c c' _ hc2 hc2'
    rw [hLconj σ c c' y (mem_ptsIn_inf.mpr ⟨hc, hc'⟩)] at e2
    show (_ + _) / 2 = (_ + _) / 2 - _
    rw [e1, e2]
    ring
  refine ⟨fun σ => ⟨hB, Ψ σ, htr σ⟩, ?_, ?_, ?_⟩
  · intro σ c y hy
    have hy2 := (mem_ptsIn_iff_of_conj (y := y) (y' := conjPts q rfl y) rfl).mpr hy
    have h1 := hψ0c σ c y hy
    have h2 := cInfAt_conj (f := (ψ0 ((starRingEnd ℂ).comp σ)).φ c) (hψ0c _ c _ hy2)
    exact h1.comp₂ h2 (G := fun v => (v.1 + v.2) / 2) (by fun_prop)
  · intro σ σ' c y y' hyy' hy
    have hσ := eq_conj_of_conj hyy'
    subst hσ
    have hy' : y' = conjPts q rfl y := Subtype.ext hyy'
    subst hy'
    show ((ψ0 _).φ c (conjPts q rfl y) + (ψ0 _).φ c (conjPts q rfl (conjPts q rfl y))) / 2 =
      ((ψ0 σ).φ c y + (ψ0 _).φ c (conjPts q rfl y)) / 2
    rw [hcongr c ((starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ)) σ (RingHom.ext fun x => by simp)
      (conjPts q rfl (conjPts q rfl y)) y ((conjHomeomorph P).left_inv _)]
    ring
  · intro σ c x hx
    have hxp := mem_ptsIn_pull i hi B c x hx
    have hmx : conjPts q rfl (PtsOver.map i hi (spMap σ) x) =
        PtsOver.map i hi (spMap ((starRingEnd ℂ).comp σ)) (conjPts p rfl x) := by
      apply Subtype.ext
      show spMap (starRingEnd ℂ) ≫ ((x : Sp ℂ ⟶ X) ≫ i) = (spMap (starRingEnd ℂ) ≫ (x : Sp ℂ ⟶ X)) ≫ i
      exact (Category.assoc _ _ _).symm
    have hx2 : PtsOver.map i hi (spMap ((starRingEnd ℂ).comp σ)) (conjPts p rfl x) ∈
        ptsIn q ((starRingEnd ℂ).comp σ) (B.U c) := by
      rw [← hmx]
      exact (mem_ptsIn_iff_of_conj rfl).mpr hx
    show ((ψ0 σ).φ c (PtsOver.map i hi (spMap σ) x) +
      (ψ0 _).φ c (conjPts q rfl (PtsOver.map i hi (spMap σ) x))) / 2 = (χ σ).φ (fun _ => c) x
    rw [hψ0e σ c x hx, hmx, hψ0e _ c (conjPts p rfl x) hx2, hχc σ _ (fun _ => c) x (conjPts p rfl x) rfl hxp]
    ring

end Conj

end GlobalTheory.AmbMetric
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Published.Amb

variable {k : Type} [CommRing k] {X : Scheme.{0}}

private theorem comb_isometric_of_isometric {p : X ⟶ Sp k} {ι : Type} [Fintype ι] {L L' : ι → HermLB p}
    (hL : ∀ j, (L j).Isometric (L' j)) (n : ι → ℤ) : (comb L n).Isometric (comb L' n) := by
  unfold comb
  induction (Finset.univ : Finset ι).toList with
  | nil => exact HermLB.Isometric.refl _
  | cons i l ih =>
    simp only [List.foldr_cons]
    refine HermLB.Isometric.tens ?_ ih
    unfold zp
    exact HermLB.Isometric.tens (HermLB.Isometric.pow (hL i) _) (HermLB.Isometric.dual (HermLB.Isometric.pow (hL i) _))

theorem mixOn_congr [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {ι : Type}
    [Fintype ι] {M M' : HermLB p} {L L' : ι → HermLB p} (hM : M.Isometric M') (hL : ∀ j, (L j).Isometric (L' j))
    (H : MixOn p D ι M L) : MixOn p D ι M' L' := by
  intro Φ hΦ n h hh r hr
  have hfam : ∀ o : Option ι, (o.elim M' L').Isometric (o.elim M L) := by
    intro o
    cases o with
    | none => exact HermLB.Isometric.symm hM
    | some j => exact HermLB.Isometric.symm (hL j)
  have hΦ' : IsArFun (fun o : Option ι => o.elim M L) D Φ :=
    ⟨fun n' => HermLB.Isometric.isSelfInter hX (comb_isometric_of_isometric hfam n') (hΦ.1 n'), hΦ.2⟩
  have hcomb : (comb L' n).Isometric (comb L n) := comb_isometric_of_isometric (fun j => HermLB.Isometric.symm (hL j)) n
  have hh' : (comb L n).IsArithHeight h := HermLB.Isometric.isArithHeight hX hcomb hh
  obtain ⟨r0, hr0, hdiv, hlog⟩ := HermLB.Isometric.exists_isRatSec (HermLB.Isometric.symm hM) hr
  obtain ⟨hint, heq⟩ := H Φ hΦ' n h hh' r0 hr0
  have hms : ∀ σ, MeasurableSet (offSupp p σ (M'.div hr)) := fun σ => (isOpen_offSupp _).measurableSet
  refine ⟨fun σ => ?_, ?_⟩
  · have hi := hint σ
    rw [HermLB.Isometric.chernIntegrableOn_eq (HermLB.Isometric.symm hcomb) σ D, hdiv] at hi
    exact hi.congr (hms σ) (hlog σ)
  · rw [heq, hdiv, sub_right_inj]
    simp only [HermLB.archInt]
    rw [hdiv]
    apply finsum_congr
    intro σ
    rw [HermLB.Isometric.chernInt_eq (HermLB.Isometric.symm hcomb) σ D]
    exact Weight.chernInt_congr (hms σ) (hlog σ)

theorem pull_congr {Y P : Scheme.{0}} {p : P ⟶ Sp k} {q : Y ⟶ Sp k} (M : HermLB p) {f g : Y ⟶ P} (e : f = g)
    (hf : f ≫ p = q) (hg : g ≫ p = q) : M.pull f hf = M.pull g hg := by
  subst e; rfl

theorem dim_closure_image {P : Scheme.{0}} (i : X ⟶ P) [IsClosedImmersion i] (x : X) :
    topologicalKrullDim (closure ({i x} : Set P)) = topologicalKrullDim (closure ({x} : Set X)) := by
  have hi : Topology.IsClosedEmbedding i := i.isClosedEmbedding
  have hE : Topology.IsEmbedding (fun z : closure ({x} : Set X) => i z.1) :=
    hi.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hset : closure ({i x} : Set P) = Set.range (fun z : closure ({x} : Set X) => i z.1) := by
    rw [← Set.image_singleton, hi.closure_image_eq]
    ext y
    simp
  rw [hset]
  exact (IsHomeomorph.topologicalKrullDim_eq _ hE.toHomeomorph.isHomeomorph).symm

end GlobalTheory.Published.Amb
end
end

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.ExistsMetricExtB
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.ArithmeticHeightTower.Read1

open GlobalTheory.Amb GlobalTheory.AmbMetric GlobalTheory.Published GlobalTheory.Published.Amb

theorem isArithVar_mpZ (m : ℕ) (n : Fin (m + 1) → ℕ) : IsArithVar (mpStr ℤ m n) (∑ a, n a) :=
  isArithVar_mp ℤ inferInstance m n

theorem isArithVar_qp (n' m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsArithVar (qpStr n' m n) (∑ a, (Fin.cons n' n : Fin (m + 2) → ℕ) a) := by
  have hA := isArithVar_mpZ m n
  have h1 : ringKrullDim ℤ = 1 := GlobalTheory.Amb.ringKrullDim_eq_one (Module.Finite.self ℤ)
  have hP := GlobalTheory.ProjModel.isArithVar_pspace ℤ h1 n'
  have hsum : ∑ a, (Fin.cons n' n : Fin (m + 2) → ℕ) a = n' + ∑ a, n a := Fin.sum_cons _ _
  rw [hsum]
  have hpc : GlobalTheory.Amb.PolyCovered (qpStr n' m n) (n' + ∑ a, n a) :=
    GlobalTheory.Amb.polyCovered_pullback (PSpace.str ℤ n') (mpStr ℤ m n) _ _ (GlobalTheory.Amb.polyCovered_pSpace n')
      (GlobalTheory.Amb.polyCovered_mp ℤ m n)
  have e : spMap (Int.castRingHom ℤ) = 𝟙 (Sp ℤ) := by simp
  have f1 : Flat (toSpecBase ℤ n') := by
    have := hP.flat
    rwa [e, Category.comp_id] at this
  have f2 : Flat (mpStr ℤ m n) := by
    have := hA.flat
    rwa [e, Category.comp_id] at this
  refine ⟨inferInstance, inferInstance, GlobalTheory.Amb.isIntegral_of_polyCovered _ _ hpc,
    GlobalTheory.ProjSpace.isProjOver_pullback hP.isProjOver hA.isProjOver, ?_,
    GlobalTheory.Amb.topologicalKrullDim_of_polyCovered h1 _ _ hpc⟩
  rw [e, Category.comp_id]
  infer_instance

theorem exists_lb_twB (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ) (hX : IsArithVar p D)
    (ι : Type) [Fintype ι] (B : ι → LB X) (hB : ∀ j, (B j).IsLB) :
    ∃ (m : ℕ) (n : Fin (m + 1) → ℕ) (i : X ⟶ MP ℤ m n) (_ : IsClosedImmersion i) (_ : i ≫ mpStr ℤ m n = p)
      (c : ι → Fin m) (t : ι → ℤ), ∀ j, LBIso ((twB m n (c j) (t j)).pull i) (B j) := by
  obtain ⟨N, e, he, hep⟩ := hX.isProjOver
  haveI := he
  choose tt r g hg hcls using fun (j : ι) => GlobalTheory.Amb.exists_twist_map e (B j) (hB j)
  set eq := Fintype.equivFin ι
  let n : Fin (Fintype.card ι + 1) → ℕ := Fin.cons N (fun k => r (eq.symm k))
  let a : (i : Fin (Fintype.card ι + 1)) → X ⟶ projectiveSpace ℤ (n i) :=
    Fin.cases (motive := fun i => X ⟶ projectiveSpace ℤ (n i)) e (fun k => g (eq.symm k))
  have ha : ∀ i, a i ≫ toSpecBase ℤ (n i) = p := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hep
    · exact (hg (eq.symm k)).trans hep
  let i := GroundTheory.Arith.SchemeCoh.ProjSpace.lift (Fintype.card ι) n p a ha
  have hi0 : i ≫ pr ℤ (Fintype.card ι) n 0 = e := GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ n p a ha 0
  haveI := GlobalTheory.Amb.isSeparated_pr_zero ℤ (Fintype.card ι) n
  haveI : IsClosedImmersion (i ≫ pr ℤ (Fintype.card ι) n 0) := by rw [hi0]; exact he
  have hci : IsClosedImmersion i := IsClosedImmersion.of_comp i (pr ℤ (Fintype.card ι) n 0)
  have key : ∀ k : Fin (Fintype.card ι),
      LBIso ((twB (Fintype.card ι) n k (-(tt (eq.symm k) : ℤ))).pull i) (B (eq.symm k)) := by
    intro k
    exact GlobalTheory.Amb.lbIso_pull_tw i (pr ℤ (Fintype.card ι) n k.succ) (pr ℤ (Fintype.card ι) n 0) (a k.succ) e
      (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ n p a ha k.succ) hi0 (tt (eq.symm k)) (B (eq.symm k)) (hB _)
      (hcls (eq.symm k))
  refine ⟨Fintype.card ι, n, i, hci, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ n p a ha, fun j => eq j,
    fun j => -(tt j : ℤ), fun j => ?_⟩
  have := key (eq j)
  rwa [Equiv.symm_apply_apply] at this

theorem isLB_twB (m : ℕ) (n : Fin (m + 1) → ℕ) (c : Fin m) (t : ℤ) : (twB m n c t).IsLB :=
  isLB_tw (LB.isLB_pull (O1_isLB ℤ _) _) (LB.isLB_pull (O1_isLB ℤ _) _) _

theorem exists_metric_ext_B (k : Type) [CommRing k] (P : Scheme.{0}) [IsIntegral P] (q : P ⟶ Sp k) (N : ℕ)
    (hP : IsArithVar q N) (hs : GenSmooth q N) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ P) [IsClosedImmersion i]
    (p : X ⟶ Sp k) (hi : i ≫ q = p) (B' : LB P) (hB' : B'.IsLB) (L : HermLB p) (hL : LBIso (B'.pull i) L.B) :
    ∃ M : HermLB q, M.B = B' ∧ (M.pull i hi).Isometric L := by
  obtain ⟨χ, hc, hj, hT⟩ := GlobalTheory.AmbMetric.exists_transport (B'.pull i)
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hB' i) L hL
  obtain ⟨ψ, hψc, hψj, hext⟩ := GlobalTheory.AmbMetric.exists_weight_ext i hi hP hs B' hB' χ hc hj
  refine ⟨⟨B', hB', ψ, hψc, hψj⟩, rfl, ?_⟩
  refine GlobalTheory.HermLB.Isometric.trans ?_ hT
  refine GlobalTheory.HermLB.isometric_of_eqOn (fun σ a y hy => ?_)
  change (χ σ).φ a y = ((ψ σ).pull i hi).φ a y
  change y ∈ ptsIn p σ ((B'.pull i).U a) at hy
  have hm : PtsOver.map i hi (spMap σ) y ∈ ptsIn q σ (B'.U (a PUnit.unit)) :=
    (GlobalTheory.Published.mem_ptsIn_pull (m := PtsOver.map i hi (spMap σ)) (fun z => rfl)).1 hy
  have e1 := GlobalTheory.Weight.pull_φ (ψ σ) i hi a y
  rw [hext σ (a PUnit.unit) y hm] at e1
  exact e1.symm

theorem isTwB_of_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (M : HermLB (mpStr ℤ m n)) (c : Fin m) (t : ℤ)
    (h : M.B = twB m n c t) : IsTwB M := by
  exact ⟨c, t, ⟨by rw [h]; exact GlobalTheory.lbIso_self (isLB_twB m n c t)⟩⟩

theorem exists_ambientZ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℤ} {D : ℕ}
    (hX : IsArithVar p D) {ι : Type} [Fintype ι] (L : ι → HermLB p) :
    ∃ (m : ℕ) (n : Fin (m + 1) → ℕ) (i : X ⟶ MP ℤ m n) (_ : IsClosedImmersion i) (hi : i ≫ mpStr ℤ m n = p)
      (M : ι → HermLB (mpStr ℤ m n)), (∀ j, IsTwB (M j)) ∧ ∀ j, ((M j).pull i hi).Isometric (L j) := by
  obtain ⟨m, n, i, hci, hi, c, t, hiso⟩ :=
    exists_lb_twB X p D hX ι (fun j => (L j).B) (fun j => (L j).isLB)
  haveI := hci
  haveI := GlobalTheory.Amb.isIntegral_mp ℤ m n
  choose M hMB hMI using fun (j : ι) => exists_metric_ext_B ℤ (MP ℤ m n) (mpStr ℤ m n) _ (isArithVar_mpZ m n)
    (GlobalTheory.Amb.genSmooth_mp ℤ m n) X i p hi (twB m n (c j) (t j)) (isLB_twB m n (c j) (t j)) (L j) (hiso j)
  exact ⟨m, n, i, hci, hi, M, fun j => isTwB_of_eq (M j) (c j) (t j) (hMB j), hMI⟩

theorem form (H : FormZ) : ArFormExists := by
  apply GlobalTheory.CompanionTheory.Ar.BaseZ.arFormExists_of_int
  intro X _ p D hX ι _ L
  obtain ⟨m, n, i, hci, hi, M, hM, hI⟩ := exists_ambientZ hX L
  haveI := hci
  subst hi
  obtain ⟨Φ, hΦ1, hΦ2⟩ := H m n X i D hX ι M hM
  refine ⟨Φ, fun c => ?_, hΦ2⟩
  exact (GlobalTheory.ArInt.isometric_comb_congr (fun j => hI j) c).isSelfInter hX (hΦ1 c)

theorem mix (H : MixZ) : ArMix := by
  apply GlobalTheory.CompanionTheory.Ar.BaseZ.arMix_of_base_int
  intro X _ _ p D hX ι _ M L Φ hΦ c h hh r hr
  obtain ⟨m, n, i, hci, hi, N, hN, hI⟩ := exists_ambientZ hX (fun o : Option ι => o.elim M L)
  haveI := hci
  subst hi
  have hmix := H m n X i D hX ι (N none) (fun j => N (some j)) (hN none) (fun j => hN (some j))
  have hmix' := GlobalTheory.Published.Amb.mixOn_congr hX (hI none) (fun j => hI (some j)) hmix
  exact hmix' Φ hΦ c h hh r hr

theorem proj (HH : HeightsZ) (HQ : HeightsQ) (HP : ProjQ) : HeightProjection := by
  apply GlobalTheory.CompanionTheory.Ar.BaseZ.heightProjection_of_int
  intro X Y _ p q D e hX hY π hπ hdim hdeg L h hh
  haveI := hX.isIntegral
  obtain ⟨m, n, i, hci, hi, M, hM, hI⟩ := exists_ambientZ hX (fun _ : Unit => L)
  haveI := hci
  obtain ⟨n', j0, hj0, hj0q⟩ := hY.isProjOver
  haveI := hj0
  have hπi : (π ≫ i) ≫ mpStr ℤ m n = q := by rw [Category.assoc, hi, hπ]
  have cond : j0 ≫ toSpecBase ℤ n' = (π ≫ i) ≫ mpStr ℤ m n := by
    rw [hπi]
    exact hj0q
  let j : Y ⟶ QP n' m n := pullback.lift j0 (π ≫ i) cond
  haveI : IsClosedImmersion j := GlobalTheory.Amb.isClosedImmersion_lift ℤ m n' n j0 (π ≫ i) cond
  have hjq : j ≫ qpStr n' m n = q := by
    simp only [j, qpStr, pullback.lift_fst_assoc]
    exact hj0q
  have hjs : j ≫ qpSnd n' m n = π ≫ i := pullback.lift_snd _ _ _
  have hAQ := isArithVar_qp n' m n
  have hAM := isArithVar_mpZ m n
  obtain ⟨hM0, hhM⟩ := HH m n (M ()) (hM ())
  obtain ⟨h', hh'⟩ := HQ n' m n (M ()) (hM ())
  have hXh : L.IsArithHeight (fun x => hM0 (i x)) := (hI ()).isArithHeight hX (hhM.restrict hAM i hi)
  have heq : h = fun x => hM0 (i x) := GlobalTheory.HermLB.IsArithHeight.unique hX hh hXh
  have hY1 := hh'.restrict hAQ j hjq
  have iso_of_refines {Z : Scheme.{0}} {r : Z ⟶ Sp ℤ} {A B : HermLB r} {v : A.B.ι → B.B.ι}
      (hv : Refines A B v 0) : A.Isometric B :=
    GlobalTheory.HermLB.isometric_of_chart v hv.le (fun x j j' hj hj' => hv.g Z (𝟙 Z) x j j' hj hj')
      (fun σ j y hy => ((hv.φ σ j y hy).trans (add_zero _)).symm)
  have hY2 := (iso_of_refines (GlobalTheory.HermLB.refines_pull_pull (M ()) (qpSnd n' m n) (qpSnd_str n' m n) j hjq
    (by rw [Category.assoc, qpSnd_str, hjq]))).isArithHeight hY hY1
  rw [GlobalTheory.Published.Amb.pull_congr (M ()) hjs _ hπi] at hY2
  have hY3 := (iso_of_refines (GlobalTheory.HermLB.refines_pull_comp (M ()) i hi π hπ hπi)).isArithHeight hY hY2
  have hY4 := ((hI ()).pull π hπ).isArithHeight hY hY3
  refine ⟨fun y => h' (j y), hY4, ?_⟩
  have hpt : qpSnd n' m n (j (genericPoint Y)) = i (π (genericPoint Y)) := by
    rw [← Scheme.Hom.comp_apply, hjs, Scheme.Hom.comp_apply]
  have hrd : Scheme.Hom.residueDegree (qpSnd n' m n) (j (genericPoint Y)) =
      Scheme.Hom.residueDegree π (genericPoint Y) := by
    have e1 := GlobalTheory.CurveDegreesCompare.residueDegree_comp j (qpSnd n' m n) (genericPoint Y)
    have e2 := GlobalTheory.CurveDegreesCompare.residueDegree_comp π i (genericPoint Y)
    rw [hjs, e2, GlobalTheory.Published.residueDegree_of_isClosedImmersion i,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion j] at e1
    simpa using e1.symm
  have hdimQ := hdim
  rw [← GlobalTheory.Published.Amb.dim_closure_image i, ← hpt] at hdimQ
  have hdegQ : Scheme.Hom.residueDegree (qpSnd n' m n) (j (genericPoint Y)) ≠ 0 := by
    rw [hrd]
    exact hdeg
  have hYj : IsArithVar (j ≫ qpStr n' m n) e := by
    rw [hjq]
    exact hY
  have key := HP n' m n Y j e hYj hdimQ hdegQ (M ()) (hM ()) hM0 h' hhM hh'
  show h' (j (genericPoint Y)) = _
  rw [key, hrd, hpt, heq]

end GlobalTheory.ArithmeticHeightTower.Read1
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.ArithmeticHeightTower.Read1

open GlobalTheory.Amb GlobalTheory.Published GlobalTheory.Published.Amb

theorem heights_of_form_mix (HF : FormZ) (HM : MixZ) : HeightsZ ∧ HeightsQ := by
  have H := GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive (form HF) (mix HM)
  refine ⟨fun m n M _ => ?_, fun n' m n M _ => ?_⟩
  · have := isIntegral_mp ℤ m n
    exact (H ℤ _ _ _ (isArithVar_mpZ m n)).1 M
  · have := (isArithVar_qp n' m n).isIntegral
    exact (H ℤ _ _ _ (isArithVar_qp n' m n)).1 _

theorem bridge3 (HF : FormZ) (HM : MixZ) (HP : ProjQ) : ArFormExists ∧ ArMix ∧ HeightProjection :=
  ⟨form HF, mix HM, proj (heights_of_form_mix HF HM).1 (heights_of_form_mix HF HM).2 HP⟩

end GlobalTheory.ArithmeticHeightTower.Read1

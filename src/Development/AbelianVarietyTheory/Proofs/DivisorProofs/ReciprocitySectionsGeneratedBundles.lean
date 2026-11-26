module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositive

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditive
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix.CycAdd

theorem isProjOver_clos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p) (z : X) :
    IsProjOver (closι z ≫ p) := by
  obtain ⟨N, i, hi, h⟩ := hp
  exact ⟨N, closι z ≫ i, inferInstance, by rw [Category.assoc, h]⟩

theorem int_congr {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L M : Fin D → MLine p σ} (h : ∀ ε, part L ε = part M ε) (f : CxPts p σ → ℝ) : Mix.int L f = Mix.int M f := by
  simp only [Mix.int, h]

theorem pull_update {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (i : Fin D) (A : MLine p σ) (z : X) :
    (fun j => (Function.update L i A j).pull (closι z) rfl) =
      Function.update (fun j => (L j).pull (closι z) rfl) i (A.pull (closι z) rfl) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

end GlobalTheory.Mix.CycAdd


open GlobalTheory.Mix.CycAdd in
theorem GlobalTheory.Mix.cycInt_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  intro k _ X p σ hp D L i A B f z hA hB
  have hq := isProjOver_clos hp z
  have hI := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl
  have hparts : ∀ ε, part (fun j => (Function.update L i (A.tens B) j).pull (closι z) rfl) ε =
      part (Function.update (fun j => (L j).pull (closι z) rfl) i
        ((A.pull (closι z) rfl).tens (B.pull (closι z) rfl))) ε := by
    intro ε
    refine GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k (clos z) (closι z ≫ p) σ hq D _ _ (fun j => ?_) ε
    by_cases hj : j = i
    · subst hj; simpa using hI.2.2.1 A B
    · simpa [Function.update_of_ne hj] using (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k (clos z) (clos z) (closι z ≫ p) (closι z ≫ p) σ (𝟙 _) (Category.id_comp _)).1 ((L j).pull (closι z) rfl)
  unfold CycIntg at hA hB
  unfold cycInt
  rw [int_congr hparts, pull_update, pull_update]
  rw [pull_update] at hA hB
  exact (GlobalTheory.T.mixedChernIntegral_additive_in_factor k (clos z) (closι z ≫ p) σ hq D _ i _ _ _ hA hB).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClosureIntegral_update_tensor_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  first | exact @GlobalTheory.Mix.cycInt_update_tens | exact GlobalTheory.Mix.cycInt_update_tens | (intros; apply GlobalTheory.Mix.cycInt_update_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosTwistMetrisedLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CInfAtSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BumpPts

theorem exists_finset_closure_eq_top {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(X, W), Subring.closure (Set.range (constFn p W) ∪ ↑s) = ⊤ := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  letI := (p.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Sp k, ⊤) Γ(X, W) := h
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := Γ(Sp k, ⊤)) (A := Γ(X, W))
  refine ⟨s, ?_⟩
  have e : Set.range (constFn p W) = Set.range (algebraMap Γ(Sp k, ⊤) Γ(X, W)) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b, ?_⟩
      have hb : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b) = b := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
      show (p.appLE ⊤ W (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b)) = _
      rw [hb]
      rfl
  rw [e, ← Algebra.adjoin_eq_ring_closure, hs]
  rfl

theorem exists_cInf_bump (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (hp : IsProjOver p) (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)) (hO : IsOpen O)
    (hy : y ∈ O) : ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧
      tsupport χ ⊆ O := by
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  haveI : T2Space (CxPts p σ) := t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top y.1)
  have hyW' : y ∈ ptsIn p σ W := hyW
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top p hW
  let φ : CxPts p σ → (s → ℂ) := fun z a => ev p σ W a.1 z

  obtain ⟨S, hS, hSO⟩ : ∃ S ∈ 𝓝 (φ y), ∀ z ∈ ptsIn p σ W, φ z ∈ S → z ∈ O := by
    let l := Filter.comap φ (𝓝 (φ y)) ⊓ 𝓟 (ptsIn p σ W)
    have hφl : Tendsto φ l (𝓝 (φ y)) := tendsto_comap.mono_left inf_le_left
    have ht : Tendsto (fun z => z) l (𝓝 y) := by
      refine (PtsOver.tendsto_iff_of_generators hW hyW hs).2 ⟨?_, fun f hf => ?_⟩
      · exact mem_inf_of_right (mem_principal_self _)
      · exact ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hφl
    have h : O ∈ l := ht (hO.mem_nhds hy)
    rw [mem_inf_principal] at h
    obtain ⟨S, hS, hSO⟩ := mem_comap.1 h
    exact ⟨S, hS, fun z hz hzS => hSO hzS hz⟩
  obtain ⟨F, hFS, hFc, hFd, hFr, hF1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hS
  let K : Set (CxPts p σ) := {z | z ∈ ptsIn p σ W ∧ φ z ∈ tsupport F}

  have hKc : IsCompact K := by
    refine isCompact_iff_ultrafilter_le_nhds.2 fun u hu => ?_
    have hKu : K ∈ u := le_principal_iff.1 hu
    have hWu : ∀ᶠ z in (u : Filter (CxPts p σ)), z ∈ ptsIn p σ W := mem_of_superset hKu fun z hz => hz.1
    obtain ⟨v, -, hv⟩ := hFc.ultrafilter_le_nhds (u.map φ)
      (le_principal_iff.2 (Ultrafilter.mem_map.2
        (mem_of_superset hKu fun z (hz : z ∈ K) => hz.2)))
    have hv' : Tendsto φ u (𝓝 v) := hv
    have hcst : ∀ a : k, ∀ z ∈ ptsIn p σ W, ev p σ W (constFn p W a) z = ev p σ W (constFn p W a) y :=
      fun a z hz => by
        show valR z.1 W _ = valR y.1 W _
        rw [valR_constFn p z.1 W hz, valR_constFn p y.1 W hyW, z.2, y.2]
    have hlim : ∀ f : Γ(X, W), ∃ c, Tendsto (fun z => ev p σ W f z) u (𝓝 c) := by
      intro f
      have hf : f ∈ Subring.closure (Set.range (constFn p W) ∪ ↑s) := hs ▸ Subring.mem_top f
      induction hf using Subring.closure_induction with
      | mem f hf =>
        rcases hf with ⟨a, rfl⟩ | hf
        · exact ⟨_, tendsto_const_nhds.congr' (hWu.mono fun z hz => (hcst a z hz).symm)⟩
        · exact ⟨v ⟨f, hf⟩, ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hv'⟩
      | zero =>
        exact ⟨0, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm)⟩
      | one =>
        exact ⟨1, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm)⟩
      | add f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c + d, (hc.add hd).congr fun z => (ev_add f g z).symm⟩
      | neg f _ hf =>
        obtain ⟨c, hc⟩ := hf
        exact ⟨-c, hc.neg.congr' (hWu.mono fun z hz => by
          show -ev p σ W f z = ev p σ W (-f) z
          rw [ev_eq hz, ev_eq hz, map_neg])⟩
      | mul f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c * d, (hc.mul hd).congr fun z => (ev_mul f g z).symm⟩
    choose c hc using hlim
    let ψ : Γ(X, W) →+* ℂ :=
      { toFun := c
        map_one' := tendsto_nhds_unique (hc 1)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm))
        map_mul' := fun f g => tendsto_nhds_unique (hc (f * g))
          (((hc f).mul (hc g)).congr fun z => (ev_mul f g z).symm)
        map_zero' := tendsto_nhds_unique (hc 0)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm))
        map_add' := fun f g => tendsto_nhds_unique (hc (f + g))
          (((hc f).add (hc g)).congr fun z => (ev_add f g z).symm) }
    have hψ : ∀ a, ψ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W a) = σ a := fun a => tendsto_nhds_unique (hc _)
      (tendsto_const_nhds.congr' (hWu.mono fun z hz => (ev_algX hz a).symm))
    let z' : CxPts p σ := ofHom hW ψ hψ
    have hz'W : z' ∈ ptsIn p σ W := ofHom_mem hW ψ hψ
    have hz'ev : ∀ f, ev p σ W f z' = c f := fun f => ev_ofHom hW ψ hψ f
    have ht : Tendsto (fun z => z) (u : Filter (CxPts p σ)) (𝓝 z') := by
      refine (PtsOver.tendsto_iff_of_generators hW hz'W hs).2 ⟨hWu, fun f _ => ?_⟩
      have := hc f
      rw [← hz'ev f] at this
      exact this
    have hφz' : φ z' = v := funext fun a =>
      (hz'ev a.1).trans (tendsto_nhds_unique (hc a.1) (((continuous_apply a).tendsto _).comp hv'))
    refine ⟨z', ⟨hz'W, ?_⟩, ht⟩
    rw [hφz']
    exact hFc.isClosed.mem_of_tendsto hv' (mem_of_superset hKu fun z hz => hz.2)
  have hKcl : IsClosed K := hKc.isClosed
  let χ : CxPts p σ → ℝ := (ptsIn p σ W).indicator fun z => F (φ z)
  have hsupp : Function.support χ ⊆ K := fun z hz => by
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hz
    exact ⟨hz.1, subset_tsupport _ hz.2⟩
  refine ⟨χ, fun z => ?_, fun z => Set.indicator_nonneg (fun w _ => (hFr ⟨_, rfl⟩).1) z, ?_, ?_⟩
  · by_cases hz : z ∈ ptsIn p σ W
    · refine ⟨W, s, inferInstance, fun a => a.1, F, Set.univ, hz, isOpen_univ, trivial,
        hFd.contDiffOn, ?_⟩
      filter_upwards [(isOpen_ptsIn W).mem_nhds hz] with w hw
      exact Set.indicator_of_mem hw _
    · have hzK : z ∉ K := fun h => hz h.1
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
      exact Function.notMem_support.1 fun h => hw (hsupp h)
  · show 0 < (ptsIn p σ W).indicator (fun z => F (φ z)) y
    rw [Set.indicator_of_mem hyW', hF1]
    exact one_pos
  · exact (closure_minimal hsupp hKcl).trans fun z hz => hSO z hz.1 (hFS hz.2)

end GlobalTheory.BumpPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_bump_complexPoints_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)), IsOpen O → y ∈ O → ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ O := by
  first | exact @GlobalTheory.BumpPts.exists_cInf_bump | exact GlobalTheory.BumpPts.exists_cInf_bump | (intros; apply GlobalTheory.BumpPts.exists_cInf_bump <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory.CInfGlue

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_inv {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h0 : f y ≠ 0) :
    CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun v hv => hv.2, h₅.mono fun z hz => by simp only [hz]⟩
  have := h₅.self_of_nhds
  simp only at this
  rw [Set.mem_preimage, ← this]
  exact h0

theorem cInfAt_mul {f g : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h' : CInfAt g y) :
    CInfAt (fun z => f z * g z) y :=
  h.comp₂ h' (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sum {κ : Type} (s : Finset κ) (f : κ → CxPts p σ → ℝ) {y : CxPts p σ}
    (h : ∀ j ∈ s, CInfAt (f j) y) : CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem cInfAt_cut {χ v : CxPts p σ → ℝ} {O : Set (CxPts p σ)} (hχ : ∀ z, CInfAt χ z)
    (hs : tsupport χ ⊆ O) (hv : ∀ z ∈ O, CInfAt v z) (z : CxPts p σ) :
    CInfAt (fun w => χ w * v w) z := by
  by_cases hz : z ∈ O
  · exact cInfAt_mul (hχ z) (hv z hz)
  · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hs h)
    refine (cInfAt_const 0 z).congr ?_
    filter_upwards [h0] with w hw
    simp [hw]

theorem glue : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (T : Type) (m : T → CxPts p σ) (u : T → ℝ), (∀ x : CxPts p σ, ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧ ∀ t, m t ∈ O → v (m t) = u t) → ∃ v : CxPts p σ → ℝ, (∀ z, CInfAt v z) ∧ ∀ t, v (m t) = u t := by
  intro k _ X p hp σ T m u h
  haveI : CompactSpace (CxPts p σ) := GlobalTheory.CxPts.compactSpace σ hp
  choose O v hO hx hv hu using h
  choose χ hχ hχ0 hχx hχs using fun x => GlobalTheory.T.exists_smooth_bump_complexPoints_projective k X p hp σ x (O x) (hO x) (hx x)
  have hc : ∀ x, Continuous (χ x) := fun x =>
    continuous_iff_continuousAt.2 fun z => (hχ x z).continuousAt
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => {z | 0 < χ x z})
    (fun x => isOpen_lt continuous_const (hc x))
    (fun z _ => Set.mem_iUnion.2 ⟨z, hχx z⟩)
  have hS : ∀ z, 0 < ∑ x ∈ s, χ x z := fun z => by
    obtain ⟨x, hxs, hz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact Finset.sum_pos' (fun j _ => hχ0 j z) ⟨x, hxs, hz⟩
  refine ⟨fun z => (∑ x ∈ s, χ x z * v x z) * (∑ x ∈ s, χ x z)⁻¹, fun z => ?_, fun t => ?_⟩
  · exact cInfAt_mul
      (cInfAt_sum s (fun x w => χ x w * v x w) fun x _ => cInfAt_cut (hχ x) (hχs x) (hv x) z)
      (cInfAt_inv (cInfAt_sum s χ fun x _ => hχ x z) (hS z).ne')
  · have e : ∀ x ∈ s, χ x (m t) * v x (m t) = χ x (m t) * u t := fun x _ => by
      by_cases h0 : χ x (m t) = 0
      · simp [h0]
      · rw [hu x t (hχs x (subset_tsupport _ h0))]
    simp only
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, mul_right_comm, mul_inv_cancel₀ (hS _).ne', one_mul]

end GlobalTheory.CInfGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsProjOver
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocExt

theorem isSeparated_of_isProjOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  infer_instance

end GlobalTheory.LocExt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ClosedExt

theorem locExt {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ)
    (hu : ∀ y, CInfAt u y) (x : CxPts p σ) :
    ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧
      ∀ y : CxPts q σ, ptMap π hπ σ y ∈ O → v (ptMap π hπ σ y) = u y := by
  have := GlobalTheory.LocExt.isSeparated_of_isProjOver hp
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, hπ]⟩
  have hemb : IsClosedEmbedding (ptMap π hπ σ) := by
    have : CompactSpace (CxPts q σ) := GlobalTheory.CxPts.compactSpace σ hq
    have hc : Continuous (ptMap π hπ σ) := continuous_of_comp (f := π) fun _ => rfl
    refine hc.isClosedEmbedding fun y y' h => Subtype.ext ?_
    exact (cancel_mono π).1 (congrArg Subtype.val h)
  by_cases hx : ∃ y : CxPts q σ, ptMap π hπ σ y = x
  · obtain ⟨y₀, rfl⟩ := hx
    obtain ⟨W, ι, _, g, F, O₀, h₁, h₂, h₃, h₄, h₅⟩ := hu y₀
    obtain ⟨t, ht, htW⟩ := (π.isClosedEmbedding.isInducing.isOpen_iff).1 W.2
    let W₁ : X.Opens := ⟨t, ht⟩
    have hW₁ : π ⁻¹ᵁ W₁ = W := Opens.ext htW
    have hz₀ : π (y₀.1 (IsLocalRing.closedPoint ℂ)) ∈ W₁ := by
      have := mem_ptsIn.1 h₁
      rw [← hW₁] at this
      exact this
    obtain ⟨W', hW'a, hzW', hW'le⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hz₀
    have hle : π ⁻¹ᵁ W' ≤ W := by
      rw [← hW₁]
      exact fun a ha => hW'le ha
    choose g' hg' using fun a => π.app_surjective W' hW'a (resG Y hle (g a))
    have hval (y : CxPts q σ) (hy : y ∈ ptsIn q σ (π ⁻¹ᵁ W')) (a : ι) :
        ev p σ W' (g' a) (ptMap π hπ σ y) = ev q σ W (g a) y := by
      rw [← ev_res hle hy, ← hg' a]
      exact valR_comp y.1 π W' (g' a)
    obtain ⟨s, hs, hsu⟩ := h₅.exists_mem
    obtain ⟨N, hNs, hN, hy₀N⟩ := mem_nhds_iff.1 hs
    obtain ⟨N', hN', hNN'⟩ := (hemb.isInducing.isOpen_iff).1 hN
    have hE : IsOpen (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀) :=
      (continuousOn_pi.2 fun a => continuousOn_ev (g' a)).isOpen_inter_preimage (isOpen_ptsIn W') h₂
    have hy₀W' : y₀ ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 hzW'
    refine ⟨N' ∩ (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀),
      fun z => F fun a => ev p σ W' (g' a) z, hN'.inter hE, ⟨?_, ?_, ?_⟩, fun z hz => ?_, fun y hy => ?_⟩
    · have : y₀ ∈ ptMap π hπ σ ⁻¹' N' := hNN'.symm ▸ hy₀N
      exact this
    · exact mem_ptsIn.2 hzW'
    · simp only [Set.mem_preimage, hval y₀ hy₀W']
      exact h₃
    · exact ⟨W', ι, inferInstance, g', F, O₀, hz.2.1, h₂, hz.2.2, h₄, EventuallyEq.rfl⟩
    · have hyN : y ∈ N := by
        have : y ∈ ptMap π hπ σ ⁻¹' N' := hy.1
        rwa [hNN'] at this
      have hyW' : y ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 (mem_ptsIn.1 hy.2.1)
      simp only [hval y hyW']
      exact (hsu (hNs hyN)).symm
  · exact ⟨(Set.range (ptMap π hπ σ))ᶜ, fun _ => 0, hemb.isClosed_range.isOpen_compl, hx,
      fun z _ => cInfAt_const 0 z, fun y hy => absurd (Set.mem_range_self y) hy⟩

theorem exists_extension : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ), (∀ y, CInfAt u y) → ∃ v : CxPts p σ → ℝ, (∀ y, CInfAt v y) ∧ ∀ y, v (ptMap π hπ σ y) = u y := by
  intro k _ X Y p q σ hp π _ hπ u hu
  exact GlobalTheory.CInfGlue.glue k X p hp σ (CxPts q σ) (ptMap π hπ σ) u (locExt hp π hπ u hu)

end GlobalTheory.ClosedExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosTwistMetrisedLineBundle
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem semiPosReg_of_eqOn_charts {E E' : LB X} (χ : Weight p σ E) {χ' : Weight p σ E'}
    (h : χ'.SemiPosReg D) (j : E.ι → E'.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (E'.U (j i)))
    (he : ∀ i y, y ∈ ptsIn p σ (E.U i) → χ.φ i y = χ'.φ (j i) y) : χ.SemiPosReg D := fun i c y hy ξ => by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (E.U i))
  have e : (fun v => (χ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => (χ'.φ (j i) (c.e.symm v) : ℂ) :=
    eventually_of_mem (ho.mem_nhds (mem_over c.e hy.1 hy.2)) fun v hv => by
      simp only [he i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact h (j i) c y ⟨hy.1, hj i y hy.2⟩ ξ

theorem exists_generating_secs_tens_lbPow {H L : LB X} (hH : H.IsLB) (hL : L.IsLB) {N : ℕ}
    {s : Fin (N + 1) → H.Sec} (hs : AbLaw.VeryAmpleBy p H s) :
    ∃ (m n : ℕ) (u : Fin n → (CechPic.tens L (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X p H _ s hH hs L hL
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t₀ ≤ m := ⟨t₀.toNat, by omega⟩
  obtain ⟨n, u, hu⟩ := ht m hm
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨m, _, v, hv⟩

theorem exists_semiPosReg_tens : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  rintro F _ X p σ ⟨N, ι, hι, hp⟩ D A
  let O : MLine (PSpace.str F N) σ := MLine.ofHerm (ProjSpace.hermitianTwistingSheaf F N) σ
  have hO : O.φ.SemiPosReg N := Weight.semiPosReg_fsBasis (ProjSpace.O1_isLB F N) _
    (ProjSpace.iSup_nonzeroLocus_coord F N) 1 (by simp)
  have hsm : SmoothOfRelativeDimension N (PSpace.str F N) := inferInstance
  let H : MLine p σ := O.pull ι hp
  have hH : H.φ.SemiPosReg D := GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ O.cInf hO
  have hpow (m : ℕ) : (H.φ.pow m).SemiPosReg D :=
    Weight.SemiPosReg.of_mul _ H.cInf hH ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
      (fun _ _ h => mem_pow_iff.1 h) fun j y => H.φ.zpow_φ (m : ℤ) j y
  have hva : ∃ s : Fin (N + 1) → H.B.Sec, AbLaw.VeryAmpleBy p H.B s := by
    dsimp [H, O, MLine.pull, MLine.ofHerm, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    subst hp
    exact ⟨_, ProjSpace.veryAmpleBy_secPull_coord ι⟩
  obtain ⟨s, hs⟩ := hva
  obtain ⟨m, hgen⟩ := exists_generating_secs_tens_lbPow H.φ.isLB A.φ.isLB hs
  obtain ⟨φ₁, hφ₁, hφ₁'⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ _ (A.φ.tens (H.φ.pow m)).isLB hgen
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function F X p σ _ φ₁ (A.φ.tens (H.φ.pow m)) hφ₁ (A.cInf.tens (H.cInf.zpow m))
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.ClosedExt.exists_extension F _ X (PSpace.str F N) p σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩ ι hp u hu
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn F σ N v hv
  have hwc : ((O.φ.pow m').addFn v).IsCInf := (O.cInf.zpow m').addFn hv
  have hw : (((O.φ.pow m').addFn v).pull ι hp).SemiPosReg D :=
    GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ hwc (hm' m' le_rfl)
  refine ⟨⟨_, (H.φ.pow m).tens (H.φ.pow m'), (H.cInf.zpow m).tens (H.cInf.zpow m')⟩,
    Weight.SemiPosReg.tens (H.cInf.zpow m) (H.cInf.zpow m') (hpow m) (hpow m'), ?_⟩
  refine semiPosReg_of_eqOn_charts (A.φ.tens ((H.φ.pow m).tens (H.φ.pow m')))
    (Weight.SemiPosReg.tens hφ₁ (hwc.pull ι hp) (hφ₁' D) hw)
    (fun i => ((i.1, i.2.1), i.2.2)) (fun i y hy => ?_) fun i y hy => ?_
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    refine mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨h₁, h₂⟩, ?_⟩
    have h₄ := mem_pow_iff.1 h₃
    exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun b => Set.mem_iInter.1 (mem_ptsIn.1 h₄) b)
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    have e₁ : A.φ.φ i.1 y + (H.φ.pow m).φ i.2.1 y = φ₁.φ (i.1, i.2.1) y + u y :=
      hu' (i.1, i.2.1) y (mem_ptsIn_inf.2 ⟨h₁, h₂⟩)
    have e₂ : (H.φ.pow m').φ i.2.2 y = (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) :=
      (H.φ.zpow_φ m' i.2.2 y).trans ((congrArg (_ * ·) (O.φ.pull_φ ι hp (i.2.2 PUnit.unit) y)).trans
        (O.φ.zpow_φ m' (i.2.2 PUnit.unit) _).symm)
    have e₃ : (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y =
        (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) + v (ptMap ι hp σ y) :=
      ((O.φ.pow m').addFn v).pull_φ ι hp i.2.2 y
    change A.φ.φ i.1 y + ((H.φ.pow m).φ i.2.1 y + (H.φ.pow m').φ i.2.2 y) =
      φ₁.φ (i.1, i.2.1) y + (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y
    rw [e₃, hv', e₂, ← add_assoc, e₁]
    ring

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosTwistMetrisedLineBundleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  first | exact @GlobalTheory.Mix.exists_semiPosReg_tens | exact GlobalTheory.Mix.exists_semiPosReg_tens | (intros; apply GlobalTheory.Mix.exists_semiPosReg_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundles
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.RecSec

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem finsum_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i (A.tens C)) (B.logSec b) z =
      ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i A) (B.logSec b) z +
        ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i C) (B.logSec b) z := by
  have : CompactSpace X := compactSpace_of_projOver hp
  have hfin := Δ.finite_support_mult
  have hsub (G : X → ℝ) : (Function.support fun z => (Δ.mult z : ℝ) * G z).Finite :=
    hfin.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h0; exact hz (by simp [h0])
  rw [← finsum_add_distrib (hsub _) (hsub _)]
  refine finsum_congr fun z => ?_
  by_cases h0 : Δ.mult z = 0
  · simp [h0]
  have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
  have hcl : topologicalKrullDim (closure ({z} : Set X)) = e :=
    (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hz1
  have h₁ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i A) z hcl).2.2.2 B b (hb z h0)
  have h₂ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i C) z hcl).2.2.2 B b (hb z h0)
  rw [GlobalTheory.T.pointClosureIntegral_update_tensor_additive F X p σ hp e L i A C (B.logSec b) z h₁ h₂, mul_add]

theorem side_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (N M : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    side N (Function.update L i (A.tens C)) (M.logSec s) (B.logSec b) Δ =
      side N (Function.update L i A) (M.logSec s) (B.logSec b) Δ +
        side N (Function.update L i C) (M.logSec s) (B.logSec b) Δ := by
  simp only [side, Fin.cons_update]
  have hA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ A) M s hs
  have hC := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ C) M s hs
  rw [(GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hp (e + 1) (Fin.cons N L) i.succ A C (M.logSec s) hA hC).2,
    finsum_update_tens P hp hdim Δ B b hb L i A C]
  ring

theorem reciprocity_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro P F _ X _ _ p σ e hp hdim L M N s hs t ht hcod hgM hgN
  classical
  let Df : (Fin e → MLine p σ) → ℝ := fun L =>
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) -
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)
  have hbt : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_left fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hbs : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_right fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hadd : ∀ (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ),
      Df (Function.update L i (A.tens C)) = Df (Function.update L i A) + Df (Function.update L i C) := by
    intro L i A C
    simp only [Df, side_update_tens P hp hdim N M s hs _ N t hbt L i A C,
      side_update_tens P hp hdim M N t ht _ M s hbs L i A C]
    ring
  have hpos : ∀ L : Fin e → MLine p σ, (∀ i, (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := fun L hL =>
    sub_eq_zero.2 (GlobalTheory.T.generatedBundles_reciprocity_semiPositive P F X p σ e hp hdim L M N s hs t ht hcod hL hgM hgN)
  have key : ∀ (S : Finset (Fin e)) (L : Fin e → MLine p σ),
      (∀ i, i ∉ S → (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun L hL => hpos L fun i => hL i (Finset.notMem_empty i)
    | insert a S ha ih =>
      intro L hL
      obtain ⟨Q, hQ, hAQ⟩ := GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle F X p σ hp (e + 1) (L a)
      have hgood : ∀ R : MLine p σ, R.φ.SemiPosReg (e + 1) → Df (Function.update L a R) = 0 := by
        intro R hR
        refine ih _ fun i hi => ?_
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hR
        · rw [Function.update_of_ne hia]
          exact hL i (by simp [hia, hi])
      have h := hadd L a (L a) Q
      rw [hgood _ hAQ, hgood _ hQ, Function.update_eq_self] at h
      linarith
  have := key Finset.univ L fun i hi => absurd (Finset.mem_univ i) hi
  exact sub_eq_zero.1 this

end GlobalTheory.RecSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundlesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_sections_generatedBundles : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.RecSec.reciprocity_sec | exact GlobalTheory.RecSec.reciprocity_sec | (intros; apply GlobalTheory.RecSec.reciprocity_sec <;> assumption)
end

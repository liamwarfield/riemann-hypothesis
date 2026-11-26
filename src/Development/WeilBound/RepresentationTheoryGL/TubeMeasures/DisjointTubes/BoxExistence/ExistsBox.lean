module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LowSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNormLtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes

namespace GlobalTheory.StdMassLower

section
variable {E : Type} [Field E] [NumberField E]

theorem eq_zero_of_norm_lt_one (z : 𝓞 E) (h : ∀ φ : E →+* ℂ, ‖φ (z : E)‖ < 1) : z = 0 := by
  classical
  by_contra hz
  have h0 : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.2 hz
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ z : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (z : E))
  rw [← Algebra.coe_norm_int, norm_prod] at h2
  have h3 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ < 1 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ ≤ ‖τ.toRatAlgHom (z : E)‖ := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ.toRatAlgHom)]
          exact mul_le_of_le_one_right (norm_nonneg _)
            (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun σ _ => (h σ.toRingHom).le)
      _ < 1 := h τ
  rw [← h2] at h3
  simp only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast] at h3
  linarith

theorem eq_of_mk_eq (x y : 𝓞 E) (hx : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ ≤ 1) (hy : ∀ φ : E →+* ℂ, ‖φ (y : E)‖ ≤ 1)
    (h : Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) x = Ideal.Quotient.mk _ y) : x = y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  have : z = 0 := eq_zero_of_norm_lt_one z fun φ => by
    have e : φ (x : E) - φ (y : E) = 3 * φ (z : E) := by
      have := congrArg (fun t : 𝓞 E => φ (algebraMap (𝓞 E) E t)) hz
      simpa only [map_sub, map_mul, map_ofNat] using this
    have e2 := norm_sub_le (φ (x : E)) (φ (y : E))
    rw [e, norm_mul] at e2
    have := hx φ
    have := hy φ
    simp only [Complex.norm_ofNat] at e2
    linarith
  rw [this, mul_zero] at hz
  exact sub_eq_zero.1 hz

theorem card_quot_three :
    Nat.card (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) = 3 ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : (3 : 𝓞 E) = algebraMap ℤ (𝓞 E) 3 := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp

theorem coord_of_mem {n : ℕ} {x : Fin n → E} (hx : x ∈ Formalism.MainNotions.StandardLattice.stdLat E n) (i : Fin n) :
    ∃ a : 𝓞 E, (a : E) = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [← ha, ← hb]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨r * a, by simp [← ha, Algebra.smul_def]⟩

theorem isLattice_std (n : ℕ) : Submodule.IsFullLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  have : Submodule.IsLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) :=
    Submodule.IsLattice.of_fg E (Submodule.fg_span (Set.finite_range _))
  refine { span_eq_top := ?_ }
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  exact Submodule.subset_span ⟨j, rfl⟩

variable [StarRing E]

omit [NumberField E] in
theorem re_form (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (τ : E →+* ℂ) : (τ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re = ∑ i, Complex.normSq (τ (x i)) := by
  change (τ (∑ i, star (x i) * x i)).re = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem trace_pos (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (Formalism.MainNotions.StandardLattice.stdForm E n x x) := by
  have h1 := congrArg Complex.re
    (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := Formalism.MainNotions.StandardLattice.stdForm E n x x))
  rw [Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine Finset.sum_pos (fun σ _ => ?_) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
    refine lt_of_lt_of_eq ?_ (re_form hφ x σ.toRingHom).symm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero σ.toRingHom).2 hi)
  rw [← h1] at h2
  simpa using h2

omit [NumberField E] in
theorem isSymm_std (n : ℕ) : (Formalism.MainNotions.StandardLattice.stdForm E n).IsSymm := by
  constructor
  intro x y
  change starRingEnd _ (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star]


omit [NumberField E] in
theorem norm_entry_le (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (Formalism.MainNotions.StandardLattice.stdForm E n)) (j i : Fin n)
    (τ : E →+* ℂ) : ‖τ (g (Pi.single j 1) i)‖ ≤ 1 := by
  have e : Formalism.MainNotions.StandardLattice.stdForm E n (g (Pi.single j 1)) (g (Pi.single j 1)) = 1 := by
    rw [hg]
    change ∑ i, star ((Pi.single j (1 : E) : Fin n → E) i) * (Pi.single j (1 : E) : Fin n → E) i = 1
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h1 := re_form hφ (g (Pi.single j 1)) τ
  rw [e, map_one, Complex.one_re] at h1
  have h2 := Finset.single_le_sum (f := fun i => Complex.normSq (τ (g (Pi.single j 1) i)))
    (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [← h1, Complex.normSq_eq_norm_sq] at h2
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 h2

theorem card_aut_std (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) (n : ℕ) :
    Finite (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ∧
    Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ≤
      3 ^ (Module.finrank ℚ E * n ^ 2) := by
  have hm : ∀ (g : Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) (j i : Fin n),
      ∃ a : 𝓞 E, (a : E) = g.1 (Pi.single j 1) i := fun g j i => by
    refine coord_of_mem ?_ i
    exact g.2.2.le ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  choose a ha using hm
  have hq := card_quot_three (E := E)
  haveI : Finite (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hq]; positivity)
  have hinj : Function.Injective fun g j i => Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) (a g j i) := by
    intro g g' h
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    funext i
    rw [Pi.basisFun_apply]
    change g.1 _ i = g'.1 _ i
    rw [← ha, ← ha, eq_of_mk_eq (a g j i) (a g' j i) (fun φ => ?_) (fun φ => ?_) (congrFun (congrFun h j) i)]
    · rw [ha]; exact norm_entry_le hφ g.2.1 j i φ
    · rw [ha]; exact norm_entry_le hφ g'.2.1 j i φ
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans_eq ?_⟩
  rw [Nat.card_fun, Nat.card_fun, hq, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← pow_mul, sq]

end

theorem card_aut_gmap {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (N : Submodule (𝓞 K) V) :
    Nat.card (Formalism.ThetaLiftIndependence.autL h N) = Nat.card (Formalism.ThetaLiftIndependence.autL h (Formalism.HermitianLatticesTheory.gmap g N)) := by
  have hmul : ∀ (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V),
      Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := fun a b M => by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have hone : ∀ M : Submodule (𝓞 K) V, Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := fun M => Submodule.map_id M
  refine Nat.card_congr
    { toFun := fun u => ⟨g * u.1 * g⁻¹, mul_mem (mul_mem hg u.2.1) (inv_mem hg), ?_⟩
      invFun := fun u => ⟨g⁻¹ * u.1 * g, mul_mem (mul_mem (inv_mem hg) u.2.1) hg, ?_⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  · rw [← hmul, inv_mul_cancel_right, hmul, u.2.2]
  · rw [hmul, hmul, u.2.2, ← hmul, inv_mul_cancel, hone]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E], (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ, ((3 : ℝ) ^ (Module.finrank ℚ E * n ^ 2))⁻¹ ≤ Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  intro E _ _ _ _ hst n
  have hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := fun φ a => by
    rw [hst, IsCMField.complexEmbedding_complexConj]
  obtain ⟨⟨s, hs⟩, hm, -⟩ := Formalism.HermitianLatticesTheory.final_massBasic E (Fin n → E) _ (isSymm_std n) (trace_pos hφ) _
    (isLattice_std n)
  obtain ⟨N, ⟨hN, g, hg, e⟩, -⟩ := hs.2 (Formalism.MainNotions.StandardLattice.stdLat E n)
    ⟨isLattice_std n, fun p _ => ⟨1, one_mem _, Submodule.map_id _⟩⟩
  obtain ⟨hf, hc⟩ := card_aut_std hφ n
  haveI : Nonempty (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) :=
    ⟨⟨1, one_mem _, Submodule.map_id _⟩⟩
  have hp : 0 < Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) := Nat.card_pos
  rw [hm s hs]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun M => ((Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) M) : ℝ))⁻¹) (fun _ _ => by positivity) hN)
  beta_reduce
  rw [card_aut_gmap _ hg N, e]
  exact inv_anti₀ (by exact_mod_cast hp) (by exact_mod_cast hc)

end GlobalTheory.StdMassLower
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.B

theorem exists_box {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, Group (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, IsTopologicalGroup (X i)] [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]
    (m : ∀ i, Measure (X i)) (hm : ∀ i, (m i).IsHaarMeasure) :
    ∃ B : Set (∀ i, X i), MeasurableSet B ∧ Measure.pi m B ≠ 0 ∧ Measure.pi m B ≠ ⊤ := by
  choose K hK hK1 using fun i => exists_compact_mem_nhds (1 : X i)
  haveI := hm
  refine ⟨Set.univ.pi K, MeasurableSet.univ_pi fun i => (hK i).measurableSet, ?_, ?_⟩
  · rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (MeasureTheory.Measure.measure_pos_of_mem_nhds (μ := m i) (hK1 i)).ne'
  · rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top fun i _ => (hK i).measure_lt_top.ne

theorem exp_le (f r : ℕ) (dd : ℝ) (hf : 1 ≤ f) (hr : 2 ≤ r) (hd : 1 ≤ dd) :
    Real.exp (-(3 * ((f : ℝ) * (r : ℝ) ^ 2 * (Real.log ((f : ℝ) * r + 3) + 1) + Real.log dd))) ≤
      (((r : ℝ) ^ (r ^ 2))⁻¹) ^ f * ((3 : ℝ) ^ (2 * f * r ^ 2))⁻¹ := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hpos : 0 < (((r : ℝ) ^ (r ^ 2))⁻¹) ^ f * ((3 : ℝ) ^ (2 * f * r ^ 2))⁻¹ := by positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv, Real.log_pow, Real.log_inv,
    Real.log_pow]
  push_cast
  have hf0 : (0 : ℝ) ≤ f := by positivity
  have hfr : (0 : ℝ) ≤ (f : ℝ) * (r : ℝ) ^ 2 := by positivity
  have h1 : Real.log r ≤ Real.log ((f : ℝ) * r + 3) := by
    apply Real.log_le_log hr0
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    nlinarith
  have h3 : Real.log 3 ≤ Real.log ((f : ℝ) * r + 3) := by
    apply Real.log_le_log (by norm_num)
    have : (0 : ℝ) ≤ (f : ℝ) * r := by positivity
    linarith
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hd0 : 0 ≤ Real.log dd := Real.log_nonneg hd
  have e1 : (f : ℝ) * ((r : ℝ) ^ 2 * Real.log r) ≤ (f : ℝ) * (r : ℝ) ^ 2 * Real.log ((f : ℝ) * r + 3) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hfr
  have e2 : 2 * (f : ℝ) * (r : ℝ) ^ 2 * Real.log 3 ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2 * Real.log ((f : ℝ) * r + 3)) := by
    have := mul_le_mul_of_nonneg_left h3 hfr
    linarith
  nlinarith

end MainStatements.Tam.B

namespace MainStatements.Tam

theorem low : VolSt → StabSt → NumSt → LowSt := by
  intro hv hs hn
  refine ⟨3, by norm_num, ?_⟩
  intro D Tu Cl t0 hC i P μ 𝓕 hF
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hV : (Wc D i).SigOK := D.sp.W_sig _
  have hsig := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.CovTop.VolUp.exists_realPart_hom D (Wc D i) θ A hV hθ hA
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨B, hBm, hB0, hBt⟩ := MainStatements.Tam.B.exists_box m (fun ρ => (hm ρ).1)
  have hKo : IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P} :=
    GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _
  have heq := GlobalTheory.CovTop.VolPush.meas_translate_eq D (Wc D i) θ A m rp _ μ hV hθ hA hm hrpc hrp hKo hF.1 1 (one_mem _) B hBm
  have hsub : {h | finE (Wc D i) (1⁻¹ * h) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P ∧ rp h ∈ B} ⊆
      {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} := by
    intro h hh
    refine ⟨hs.2 D Tu Cl t0 hC i P h ?_, hh.2⟩
    simpa using hh.1
  have hle : Measure.pi m B ≤ μ {h | h ∈ Stab (Wc D i) ∧ rp h ∈ B} := heq ▸ measure_mono hsub
  have hvol := hv D (Wc D i) _ _ hV hsig μ 𝓕 hF.2 θ A m rp hθ hA hm hrpc hrp B hBm
  set X : ℝ := ReciprocityTheory.ChartRestriction.DS.volU (Wc D i).rank ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D (Wc D i).rank with hX
  have hXle : ENNReal.ofReal X ≤ μ 𝓕 := by
    have h1 : ENNReal.ofReal X * Measure.pi m B ≤ μ 𝓕 * Measure.pi m B := by
      rw [hvol, mul_comm]
      gcongr
    first
      | exact (ENNReal.mul_le_mul_right hB0 hBt).1 h1
      | exact (ENNReal.mul_le_mul_iff_left hB0 hBt).1 h1
      | exact (ENNReal.mul_le_mul_iff_right hB0 hBt).1 h1
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [show Module.finrank ℚ D.host.E = 4 * D.R.ord from D.host.finrank_cmField]
    unfold Ranks.f Ranks.n; ring
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hmass : ((3 : ℝ) ^ (2 * D.R.f * D.R.r ^ 2))⁻¹ ≤ Formalism.MainNotions.StandardLattice.massI D D.R.r := by
    have := GlobalTheory.StdMassLower.main D.host.E (fun _ => rfl) D.R.r
    rw [hfin] at this
    exact this
  obtain ⟨hn1, -⟩ := hn D.R.r hr
  have hlow : (((D.R.r : ℝ) ^ (D.R.r ^ 2))⁻¹) ^ D.R.f * ((3 : ℝ) ^ (2 * D.R.f * D.R.r ^ 2))⁻¹ ≤ X := by
    rw [hX, hrk]
    have hr0 : (0 : ℝ) < ((D.R.r : ℝ) ^ (D.R.r ^ 2))⁻¹ := by
      have : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
      positivity
    have hv0 : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r := hr0.le.trans hn1
    exact mul_le_mul (pow_le_pow_left₀ hr0.le hn1 _) hmass (by positivity) (pow_nonneg hv0 _)
  have hd : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hexp := MainStatements.Tam.B.exp_le D.R.f D.R.r _ hf hr hd
  calc ENNReal.ofReal (Real.exp (-(3 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) +
        Real.log |(discr D.host.E : ℝ)|))))
      ≤ ENNReal.ofReal X := ENNReal.ofReal_le_ofReal (hexp.trans hlow)
    _ ≤ μ 𝓕 := hXle

end MainStatements.Tam

end

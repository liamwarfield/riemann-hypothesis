module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.PointwiseNormConstantSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_basis_mem : (∀ (r : ℕ) (X : Data E r) (W : Submodule E (Fin r → E)), ∃ w : Fin (Module.finrank E W) → Fin r → E, LinearIndependent E w ∧ (∀ a, w a ∈ X.Λ) ∧ Submodule.span E (Set.range w) = W) := by
  intro r X W
  choose n hn hmem using (GlobalTheory.LatDen.latDen r X).1
  set b := Module.finBasis E W
  set v : Fin (Module.finrank E W) → Fin r → E := fun i => (b i : Fin r → E) with hv
  have hvli : LinearIndependent E v := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hne : ∀ i, (n (v i) : E) ≠ 0 := fun i => Nat.cast_ne_zero.2 (hn (v i)).ne'
  set c : Fin (Module.finrank E W) → Eˣ := fun i => Units.mk0 _ (hne i)
  have hli : LinearIndependent E (fun i => (n (v i) : E) • v i) := hvli.units_smul c
  refine ⟨fun i => (n (v i) : E) • v i, hli, fun a => hmem (v a), ?_⟩
  have hle : Submodule.span E (Set.range fun i => (n (v i) : E) • v i) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact W.smul_mem _ (b i).2
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LatBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumLowerOfLineHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumLowerOfLineHeights
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LineHeight

theorem gramDet_column {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (((A * (Matrix.of fun k (_ : Unit) => u k))ᴴ * (A * (Matrix.of fun k (_ : Unit) => u k))).det.re)
      = ∑ a, ‖(A.mulVec u) a‖ ^ 2 := by
  rw [Matrix.det_unique, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (A * Matrix.of fun k (_ : Unit) => u k) a default = A.mulVec u a := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.conjTranspose_apply, h, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_min_le_of_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (m : ℝ) (hm : m ≤ ∏ i, f i) : ∃ i, min 1 m ≤ f i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i0⟩ := ‹Nonempty ι›
  by_cases hm0 : m ≤ 0
  · exact absurd ((min_le_right _ _).trans (hm0.trans (hf i0))) (not_le.mpr (hcon i0))
  · have h1 : ∀ i, f i ≤ 1 := fun i => ((hcon i).trans_le (min_le_left _ _)).le
    have hp : ∏ i, f i ≤ f i0 := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)]
      exact mul_le_of_le_one_right (hf i0) (Finset.prod_le_one₀ (fun i _ => hf i) fun i _ => h1 i)
    have h2 : f i0 < m := (hcon i0).trans_le (min_le_right _ _)
    linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nonempty_cmType {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.mp (mt (X.cmType τ).2 h)⟩⟩

theorem c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ :=
  mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero τ.1).mpr X.ξ0_ne))

theorem exists_la1_lower_bound_of_line_heights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  intro r X d hd hr m hm
  have := nonempty_cmType X
  obtain ⟨τ0, -, hτ0⟩ := (Finset.univ : Finset X.Ψ).exists_min_image X.c Finset.univ_nonempty
  have hmin : 0 < min 1 m := lt_min one_pos hm
  have hδ : 0 < X.c τ0 * min 1 m := mul_pos (c_pos X τ0) hmin
  refine ⟨Real.sqrt (X.c τ0 * min 1 m), Real.sqrt_pos.2 hδ, fun x hx hW => ?_⟩
  obtain ⟨hdet, hmaj⟩ := GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx
  have key : ∀ v ∈ X.Λ, v ≠ 0 →
      X.c τ0 * min 1 m ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have hli : LinearIndependent E (fun _ : Unit => v) := linearIndependent_unique_iff.mpr hv0
    have hfin : Module.finrank E (Submodule.span E (Set.range fun _ : Unit => v)) = 1 := by
      rw [Set.range_const]
      exact finrank_span_singleton hv0
    have hg : ∀ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))).det.re =
          X.maj x τ (Data.emb τ.1 v) :=
      fun τ => (gramDet_column _ _).trans (hmaj τ _).symm
    have hmaj0 : ∀ τ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ => by
      rw [hmaj]
      positivity
    have hidx := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli fun _ => hv
    have h1 := hW _ hfin
    rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
    simp only [hg] at h1
    have h2 : m ≤ ∏ τ, X.maj x τ (Data.emb τ.1 v) :=
      h1.trans (div_le_self (Finset.prod_nonneg fun τ _ => hmaj0 τ)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx))
    obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hmaj0 m h2
    calc X.c τ0 * min 1 m ≤ X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hτ0 τ (Finset.mem_univ _)) hτ hmin.le (c_pos X τ).le
      _ ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
            (fun τ _ => mul_nonneg (c_pos X τ).le (hmaj0 τ)) (Finset.mem_univ τ)
  have hne : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ :=
      Submodule.span_eq_bot.mpr fun v hv => hcon v hv
    rw [X.Λ_span] at hbot
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact top_ne_bot hbot
  obtain ⟨v0, hv0, hv00⟩ := hne
  unfold Data.la1
  refine Real.sqrt_le_sqrt ?_
  unfold Data.firstMinimumSq
  refine le_csInf ⟨_, v0, hv0, hv00, rfl⟩ ?_
  rintro t ⟨v, hv, hv0', rfl⟩
  exact key v hv hv0'

end GlobalTheory.LineHeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumLowerOfLineHeightsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.firstMinimum_lower_of_lineHeights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  first | exact @GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights | exact GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights | (intros; apply GlobalTheory.LineHeight.exists_la1_lower_bound_of_line_heights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumMultiLtSucc
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.JetsPure

open Filter Asymptotics

theorem _root_.GlobalTheory.JetsPure.monomial_isBigO {n D : ℕ} (σ : Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hσ : ∀ k, DifferentiableAt ℂ (σ k) 0) (h0 : ∀ k, σ k 0 = 0) (α : Fin D → ℕ) :
    (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (∑ q, α q) := by
  have h1 : ∀ q, σ q =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ‖z‖ := by
    intro q
    have h := (hσ q).hasFDerivAt.isBigO_sub.norm_right
    simpa only [h0 q, sub_zero] using h
  have h2 : (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ q, ‖z‖ ^ α q :=
    IsBigO.finsetProd fun q _ => (h1 q).pow (α q)
  simpa only [Finset.prod_pow_eq_pow_sum] using h2

theorem _root_.GlobalTheory.JetsPure.main : ∀ (J I : Type) [Fintype I] (D T a : ℕ),
    a ≤ T + 1 → ∀ (n : J → ℕ) (e : ∀ p, Fin (n p) ≃ Fin D)
    (f w0 : ∀ p, _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ) (s : ∀ p, Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ)
    (t : ∀ p, I → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ),
    (∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), DifferentiableAt ℂ (f p) z ∧
      DifferentiableAt ℂ (w0 p) z ∧
      (∀ k, DifferentiableAt ℂ (s p k) z) ∧ ∀ k, DifferentiableAt ℂ (t p k) z) →
    (∀ p, w0 p 0 ≠ 0 ∧ (∀ k, s p k 0 = 0) ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) 0).det
        ≠ 0) →
    (∀ v : J → ℂ, ∃ u : I → ℂ, ∀ p, ∑ k, u k * t p k 0 = v p) →
    ∃ cc : (Fin D → ℕ) → I → ℂ, ∀ p, (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
      cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) =O[𝓝 0]
        fun z => ‖z‖ ^ a := by
  intro J I _ D T a haT n e f w0 s t hdiff hnz hsurj
  induction a with
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have hf : ContinuousAt (f p) 0 := (hdiff p).self_of_nhds.1.continuousAt
    simpa using hf.tendsto.isBigO_one ℝ
  | succ a ih =>
    obtain ⟨cc, hcc⟩ := ih (by omega)
    have haT' : a ≤ T := by omega
    have hw0c : ∀ p, ContinuousAt (w0 p) 0 := fun p =>
      (hdiff p).self_of_nhds.2.1.continuousAt
    have hev : ∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), (DifferentiableAt ℂ (f p) z ∧
        DifferentiableAt ℂ (w0 p) z ∧ (∀ k, DifferentiableAt ℂ (s p k) z) ∧
        ∀ k, DifferentiableAt ℂ (t p k) z) ∧ w0 p z ≠ 0 :=
      fun p => (hdiff p).and ((hw0c p).eventually_ne (hnz p).1)
    have htaylor : ∀ p, ∃ b : (Fin (n p) → ℕ) → ℂ, (fun z => (f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
        cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) -
        ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a, b β * ∏ k, (s p (e p k) z / w0 p z) ^ β k)
          =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro p
      obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.mp (hev p)
      have hζ : DifferentiableOn ℂ
          (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        apply differentiableAt_euclidean.mpr
        intro k
        obtain ⟨⟨-, hw, hs, -⟩, hw0⟩ := hU z hz
        have hsk := hs (e p k)
        fun_prop (disch := assumption)
      have hg : DifferentiableOn ℂ (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        obtain ⟨⟨hf, hw, hs, ht⟩, -⟩ := hU z hz
        fun_prop
      obtain ⟨b, hb⟩ := _root_.ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates (a := a) _
        (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U 0 hUo h0U
        hg hζ (by simp [(hnz p).2.1]; rfl) (hnz p).2.2 (by simpa only [sub_zero] using hcc p)
      exact ⟨b, by simpa only [WithLp.ofLp_toLp, sub_zero] using hb⟩
    choose b hb using htaylor
    choose u hu using fun α : Fin D → ℕ => hsurj fun p => b p (α ∘ e p) / w0 p 0 ^ T
    refine ⟨fun α => if ∑ q, α q < a then cc α else u α, fun p => ?_⟩
    have hsplit : _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1) = _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a ∪ Finset.Nat.antidiagonalTuple D a := by
      ext α
      simp only [Finset.mem_union, _root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff, Finset.Nat.mem_antidiagonalTuple]
      omega
    have hdisj : Disjoint (_root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a) (Finset.Nat.antidiagonalTuple D a) := by
      rw [Finset.disjoint_left]
      intro α h1 h2
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff] at h1
      rw [Finset.Nat.mem_antidiagonalTuple] at h2
      omega
    have hreidx : ∀ z, ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a,
        b p β * ∏ k, (s p (e p k) z / w0 p z) ^ β k =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q := by
      intro z
      symm
      refine Finset.sum_nbij' (fun α => α ∘ e p) (fun β => β ∘ (e p).symm) ?_ ?_ ?_ ?_ ?_
      · intro α hα
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
        rw [← hα]
        exact Equiv.sum_comp (e p) α
      · intro β hβ
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
        rw [← hβ]
        exact Equiv.sum_comp (e p).symm β
      · intro α _
        ext q
        simp
      · intro β _
        ext k
        simp
      · intro α _
        simp only [Function.comp_apply]
        rw [Equiv.prod_comp (e p) (fun q => (s p q z / w0 p z) ^ α q)]
    have hsum_split : ∀ z, ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1), ∑ k,
        (if ∑ q, α q < a then cc α else u α) k * (∏ q, s p q z ^ α q) *
          w0 p z ^ (T - ∑ q, α q) * t p k z =
        ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z +
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ k,
          u α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z := by
      intro z
      rw [hsplit, Finset.sum_union hdisj]
      congr 1
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_pos (_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff.mp hα)]
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_neg (by rw [Finset.Nat.mem_antidiagonalTuple.mp hα]; exact lt_irrefl a)]
    have hR : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, (fun z => ∑ k, u α k *
        (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z -
        b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro α hα
      have hsum : ∑ q, α q = a := Finset.Nat.mem_antidiagonalTuple.mp hα
      obtain ⟨-, hw, hs, ht⟩ := (hdiff p).self_of_nhds
      have hH0 : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = b p (α ∘ e p) := by
        have hw : w0 p 0 ^ T ≠ 0 := pow_ne_zero _ (hnz p).1
        have h : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = w0 p 0 ^ T * ∑ k, u α k * t p k 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h, hu α p]
        field_simp
      have hHd : DifferentiableAt ℂ (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z)) 0 := by
        fun_prop
      have hHO : (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z) -
          ∑ k, u α k * (w0 p 0 ^ T * t p k 0)) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p) => ‖z‖ := by
        simpa only [sub_zero] using hHd.hasFDerivAt.isBigO_sub.norm_right
      have hmono := _root_.GlobalTheory.JetsPure.monomial_isBigO (fun q z => s p q z / w0 p z)
        (fun q => by
          have hsq := hs q
          have hw00 := (hnz p).1
          fun_prop (disch := assumption)) (fun q => by simp [(hnz p).2.1]) α
      rw [hsum] at hmono
      refine (hmono.mul hHO).congr' ?_ (Eventually.of_forall fun z => by ring)
      filter_upwards [(hw0c p).eventually_ne (hnz p).1] with z hz
      rw [hH0]
      have hP : ∏ q, s p q z ^ α q = (∏ q, (s p q z / w0 p z) ^ α q) * w0 p z ^ a := by
        rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hz)]
      have hW : w0 p z ^ a * w0 p z ^ (T - a) = w0 p z ^ T := by
        rw [← pow_add, Nat.add_sub_cancel' haT']
      rw [hsum, hP, mul_sub, Finset.mul_sum, ← hW]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    refine ((hb p).sub (IsBigO.sum hR)).congr' (Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    clear hdiff hnz hsurj ih hcc hev hsplit hdisj hR hw0c hb hu
    beta_reduce
    rw [hsum_split z, hreidx z, Finset.sum_apply, Finset.sum_sub_distrib]
    ring

end GlobalTheory.JetsPure
end

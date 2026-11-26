module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanValueBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidef
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RefLowerOfFibreInput
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnit
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.FlatLine

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]

theorem aeval_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (MvPolynomial.comp_aeval_apply (R := ℤ) z σ.toIntAlgHom f).symm

theorem ptsOver_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) : (fun p => σ (z p)) ∈ ptsOver 𝕜 P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_embed, hz.2 f hf, map_zero]

theorem hasVal_embed {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜)
    {z : (Σ k, ι k) → L} {val : L} (h : HasVal y a u z val) : HasVal y a u (fun p => σ (z p)) (σ val) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_embed]
    exact (map_ne_zero σ).2 hfz
  · rw [aeval_embed, aeval_embed, hgz, map_mul]

theorem isSmoothHerm_powH {A : HermLine ι} (hA : IsSmoothHerm A) (k : ℕ) : IsSmoothHerm (powH A k) :=
  ContDiffOn.pow hA k

theorem ptHt_pow (A : HermLine ι) (k : ℕ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) :
    ptHt (fun b => (((k : ℤ) * A.a b : ℤ) : ℝ)) (fun z => (k : ℝ) * Real.log (A.h z)) L w = k * lineHt A L w := by
  have e : ∀ v : FinitePlace L, ∑ b, (((k : ℤ) * A.a b : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) =
      (k : ℝ) • ∑ b, (A.a b : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  simp only [ptHt, lineHt, e]
  rw [← smul_finsum, ← Finset.mul_sum, smul_eq_mul]
  ring

theorem exists_arch_bound {y : (Σ k, ι k) → Ω} {d : ℕ} (hAr : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) (hB : Birational y)
    {A : HermLine ι} {k : ℕ} {u : Ω} {c : ℝ} (hS : IsSmoothHerm A)
    (hV : VertBound y (fun b => k * A.a b) u c) :
    ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, val ≠ 0 → HasVal y (fun b => k * A.a b) u z val →
      |(k : ℝ) * Real.log (A.h z) - Real.log ‖val‖| ≤ C := by
  obtain ⟨hu, q, m, hq, hm, -, h1, h2⟩ := hV
  have hP := isSmoothHerm_powH hS k
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hAr hB (powH A k) q m u hP hq hm h1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hAr hB (powH A k).inv q m u⁻¹ (isSmoothHerm_inv hP) hq hm h2
  refine ⟨max C₁ C₂, fun z hz val hv hval => ?_⟩
  have hp : 0 < A.h z := A.pos z hz.1
  have hn : 0 < ‖val‖ := norm_pos_iff.2 hv
  have b₁ : ‖val‖ ≤ Real.exp C₁ * A.h z ^ k := hC₁ z hz val hval
  have b₂ : ‖val⁻¹‖ ≤ Real.exp C₂ * (A.h z ^ k)⁻¹ := hC₂ z hz val⁻¹ (hasVal_inv hu hz hv hval)
  have l₁ : Real.log ‖val‖ ≤ C₁ + k * Real.log (A.h z) := by
    have := Real.log_le_log hn b₁
    rwa [Real.log_mul (Real.exp_pos _).ne' (pow_pos hp k).ne', Real.log_exp, Real.log_pow] at this
  have l₂ : -Real.log ‖val‖ ≤ C₂ - k * Real.log (A.h z) := by
    have := Real.log_le_log (norm_pos_iff.2 (inv_ne_zero hv)) b₂
    rwa [norm_inv, Real.log_inv, Real.log_mul (Real.exp_pos _).ne' (inv_pos.2 (pow_pos hp k)).ne', Real.log_exp,
      Real.log_inv, Real.log_pow, ← sub_eq_add_neg] at this
  rw [abs_le]
  constructor
  · have := le_max_left C₁ C₂
    linarith
  · have := le_max_right C₁ C₂
    linarith

end GlobalTheory.CompanionTheory.Ar.Ht.FlatLine


open GlobalTheory.CompanionTheory.Ar.Ht.FlatLine in
theorem GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  intro K _ ι _ Ω _ y d hAr hB A k u c hS hk hG hV
  obtain ⟨C, hC⟩ := exists_arch_bound hAr hB hS hV
  refine ⟨(c + C) / k, fun L _ _ w hw => ?_⟩
  obtain ⟨val, hv, hval⟩ := hG L w hw
  have hU := GlobalTheory.T.vertical_bound_height_compare K ι Ω y d hAr hB (fun b => k * A.a b) u c hV
    (fun z => (k : ℝ) * Real.log (A.h z)) L w hw val hv hval
  rw [ptHt_pow] at hU
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  set S := ∑ σ : L →+* ℂ, ((k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖) with hSdef
  have hSb : |S| ≤ (Module.finrank ℚ L : ℝ) * C := by
    calc |S| ≤ ∑ σ : L →+* ℂ, |(k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : L →+* ℂ, C := Finset.sum_le_sum fun σ _ =>
          hC _ (ptsOver_embed σ hw) _ ((map_ne_zero σ).2 hv) (hasVal_embed σ hval)
      _ = (Module.finrank ℚ L : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]
  have hm : |(Module.finrank ℚ L : ℝ)⁻¹ * S| ≤ C := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul_le_iff₀ hd]
    exact hSb
  have hT : |(k : ℝ) * lineHt A L w| ≤ c + C := by
    have := abs_sub_abs_le_abs_sub ((k : ℝ) * lineHt A L w) ((Module.finrank ℚ L : ℝ)⁻¹ * S)
    linarith
  rw [le_div_iff₀ hk']
  rwa [abs_mul, abs_of_pos hk', mul_comm] at hT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnitStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_height_bounded_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBounds
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBounds
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_sup_support {ι : Type} [Fintype ι] (x : ι → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := _root_.GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.log_sup_support (ι := ι) x hx

lemma log_support {x : L} (hx : x ≠ 0) : (Function.support fun v : FinitePlace L => Real.log (v x)).Finite := by
  refine (FinitePlace.hasFiniteMulSupport hx).subset fun v hv => ?_
  intro h
  apply hv
  simp only [h, Real.log_one]

lemma product_formula {x : L} (hx : x ≠ 0) :
    (∑ᶠ v : FinitePlace L, Real.log (v x)) + ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = 0 := by
  classical
  have h := prod_abs_eq_one hx
  rw [InfinitePlace.prod_eq_abs_norm] at h
  rw [ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq x hx]
  have hf : (Function.mulSupport fun v : FinitePlace L => v x).Finite := FinitePlace.hasFiniteMulSupport hx
  have hpos : ∀ v : FinitePlace L, v x ≠ 0 := fun v => by
    simpa using hx
  have e : (∑ᶠ v : FinitePlace L, Real.log (v x)) = Real.log (∏ᶠ v : FinitePlace L, v x) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset) _ (by simp),
      finsum_eq_sum_of_support_subset (s := hf.toFinset) _ ?_, Real.log_prod fun v _ => hpos v]
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hv
    simp only [h1, Real.log_one]
  have hP : (∏ᶠ v : FinitePlace L, v x) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have hN : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hx)
  rw [e, Real.log_abs]
  have h2 : |((Algebra.norm ℚ x : ℚ) : ℝ)| * ∏ᶠ v : FinitePlace L, v x = 1 := by
    rw [← h]
    push_cast
    rfl
  have h3 := congrArg Real.log h2
  rw [Real.log_mul (abs_ne_zero.2 hN) hP, Real.log_abs, Real.log_one] at h3
  linarith

lemma finsum_le_of_le {α : Type} {f g : α → ℝ} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (h : ∀ a, f a ≤ g a) : ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset ∪ hg.toFinset) f (by simp [Set.subset_def]),
    finsum_eq_sum_of_support_subset (s := hf.toFinset ∪ hg.toFinset) g (by simp [Set.subset_def])]
  exact Finset.sum_le_sum fun a _ => h a

lemma avg_abs_le (S : (L →+* ℂ) → ℝ) {C : ℝ} (h : ∀ σ, |S σ| ≤ C) :
    |(Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ| ≤ C := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∑ _σ : L →+* ℂ, C = Module.finrank ℚ L * C := by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul_le_iff₀ hd, ← hc]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => h σ)

end Places

section Blocks

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def bnorm (z : (Σ k, ι k) → ℂ) (k : K) : ℝ :=
  Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)

lemma norm_le_bnorm (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) : ‖z ⟨k, i⟩‖ ≤ bnorm z k := by
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

lemma bnorm_pos {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < bnorm z k := by
  obtain ⟨i, hi⟩ := h
  exact (norm_pos_iff.2 hi).trans_le (norm_le_bnorm z k i)

lemma bnorm_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (k : K) :
    bnorm (fun p => c p.1 * z p) k = ‖c k‖ * bnorm z k := by
  unfold bnorm
  simp only [norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

lemma continuous_bnorm (k : K) : Continuous fun z : (Σ k, ι k) → ℂ => bnorm z k :=
  Real.continuous_sqrt.comp (by fun_prop)

lemma contDiffOn_bnorm (k : K) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bnorm z k) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2 :=
    ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k)).norm_sq ℝ
  refine h1.contDiffOn.sqrt fun z hz => ?_
  have := bnorm_pos (hz k)
  unfold bnorm at this
  exact fun h0 => by simp [h0] at this

lemma exists_bound (B : HermLine ι) (hB : IsSmoothHerm B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      |Real.log (B.h z) - ∑ k, (B.a k : ℝ) * Real.log (bnorm z k)| ≤ C := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, bnorm z k = 1} with hS
  have hcl : IsClosed S := by
    simp only [hS, Set.setOf_forall]
    exact isClosed_iInter fun k => isClosed_eq (continuous_bnorm k) continuous_const
  have hsub : S ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    exact (norm_le_bnorm z k i).trans (hz k).le
  have hcpt : IsCompact S := (isCompact_closedBall 0 1).of_isClosed_subset hcl hsub
  have hmc : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    by_contra hn
    push_neg at hn
    have := hz k
    simp [bnorm, hn] at this
  have hcont : ContinuousOn (fun z => Real.log (B.h z)) S :=
    (ContDiffOn.continuousOn hB |>.mono fun z hz => hmc z hz).log fun z hz => (B.pos z (hmc z hz)).ne'
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hb : ∀ k, 0 < bnorm z k := fun k => bnorm_pos (hz k)
  set c : K → ℂ := fun k => (((bnorm z k)⁻¹ : ℝ) : ℂ) with hc
  have hcn : ∀ k, ‖c k‖ = (bnorm z k)⁻¹ := fun k => by
    simp only [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hb k))]
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    rw [← norm_pos_iff, hcn]
    exact inv_pos.2 (hb k)
  have hz' : (fun p => c p.1 * z p) ∈ S := fun k => by
    rw [bnorm_smul, hcn, inv_mul_cancel₀ (hb k).ne']
  have h1 := hC _ hz'
  rw [B.smul c z hc0, Real.norm_eq_abs] at h1
  have hprod : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc0 k))
  have hzpos := B.pos z hz
  rw [Real.log_mul hprod hzpos.ne',
    Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc0 k))] at h1
  have h2 : ∑ k, Real.log (‖c k‖ ^ B.a k) = -∑ k, (B.a k : ℝ) * Real.log (bnorm z k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_zpow, hcn, Real.log_inv]
    ring
  rw [h2] at h1
  rw [show Real.log (B.h z) - ∑ k, (B.a k : ℝ) * Real.log (bnorm z k) =
    -∑ k, (B.a k : ℝ) * Real.log (bnorm z k) + Real.log (B.h z) by ring]
  exact h1.trans (le_max_left _ _)

def twistLine (A : HermLine ι) (m : ℕ) : HermLine ι where
  a := fun k => (m : ℤ) * A.a k - 1
  h z := A.h z ^ m / ∏ k, bnorm z k
  pos z hz := div_pos (pow_pos (A.pos z hz) m) (Finset.prod_pos fun k _ => bnorm_pos (hz k))
  smul c z hc := by
    have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
    have h1 : ∀ k, ‖c k‖ ^ ((m : ℤ) * A.a k - 1) = (‖c k‖ ^ A.a k) ^ m / ‖c k‖ := fun k => by
      rw [zpow_sub₀ (hn k), zpow_one, mul_comm (m : ℤ), zpow_mul, zpow_natCast]
    simp only [h1, A.smul c z hc, bnorm_smul, Finset.prod_mul_distrib, Finset.prod_div_distrib, mul_pow,
      Finset.prod_pow]
    rw [mul_div_mul_comm]

lemma twistLine_smooth {A : HermLine ι} (hA : IsSmoothHerm A) (m : ℕ) : IsSmoothHerm (twistLine A m) := by
  refine ContDiffOn.div (ContDiffOn.pow hA m) (contDiffOn_prod fun k _ => contDiffOn_bnorm k) fun z hz => ?_
  exact (Finset.prod_pos fun k _ => bnorm_pos (hz k)).ne'

end Blocks

section Heights

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockHt (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) (k : K) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩))) + ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k))

def sumHt (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  ∑ k, blockHt L w k

variable {L : Type} [Field L] [NumberField L]

lemma blockHt_nonneg (w : (Σ k, ι k) → L) (k : K) (h : ∃ i, w ⟨k, i⟩ ≠ 0) : 0 ≤ blockHt L w k := by
  obtain ⟨i₀, hi₀⟩ := h
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) ?_
  rw [← product_formula hi₀]
  refine add_le_add ?_ (Finset.sum_le_sum fun σ _ => ?_)
  · refine finsum_le_of_le (log_support hi₀) (log_sup_support (fun i => w ⟨k, i⟩) ⟨i₀, hi₀⟩) fun v => ?_
    have hp : 0 < v (w ⟨k, i₀⟩) := by
      have : v (w ⟨k, i₀⟩) ≠ 0 := by simpa using hi₀
      exact lt_of_le_of_ne (apply_nonneg v _) this.symm
    exact Real.log_le_log hp (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove i₀)
  · exact Real.log_le_log (norm_pos_iff.2 ((map_ne_zero σ).2 hi₀))
      (norm_le_bnorm (fun p => σ (w p)) k i₀)

lemma sumHt_nonneg (w : (Σ k, ι k) → L) (h : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 ≤ sumHt L w :=
  Finset.sum_nonneg fun k _ => blockHt_nonneg w k (h k)

lemma ptHt_eq (a : K → ℝ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    ptHt a φ L w = ∑ k, a k * blockHt L w k + (Module.finrank ℚ L : ℝ)⁻¹ *
      ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - ∑ k, a k * Real.log (bnorm (fun p => σ (w p)) k)) := by
  have e : (∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      ∑ k, a k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_finsum]
    · intro k _
      exact (log_sup_support (fun i => w ⟨k, i⟩) (hw k)).subset fun v hv => right_ne_zero_of_mul hv
  have e2 : ∑ σ : L →+* ℂ, ∑ k, a k * Real.log (bnorm (fun p => σ (w p)) k) =
      ∑ k, a k * ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  have e3 : ∑ k, a k * blockHt L w k = (Module.finrank ℚ L : ℝ)⁻¹ *
      (∑ k, a k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) +
        ∑ k, a k * ∑ σ : L →+* ℂ, Real.log (bnorm (fun p => σ (w p)) k)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold blockHt
    ring
  unfold ptHt
  rw [e, Finset.sum_sub_distrib, e2, e3]
  ring

lemma lineHt_twist (A : HermLine ι) (m : ℕ) (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt (twistLine A m) L w = m * lineHt A L w - sumHt L w := by
  unfold lineHt
  rw [ptHt_eq _ _ w hw, ptHt_eq _ _ w hw]
  have h1 : ∀ σ : L →+* ℂ, Real.log ((twistLine A m).h fun p => σ (w p)) -
      ∑ k, (((twistLine A m).a k : ℤ) : ℝ) * Real.log (bnorm (fun p => σ (w p)) k) =
      m * (Real.log (A.h fun p => σ (w p)) - ∑ k, (A.a k : ℝ) * Real.log (bnorm (fun p => σ (w p)) k)) := by
    intro σ
    have hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero σ).2 hi⟩
    have hb : ∀ k, bnorm (fun p => σ (w p)) k ≠ 0 := fun k => (bnorm_pos (hz k)).ne'
    have e : (twistLine A m).h (fun p => σ (w p)) =
        (A.h fun p => σ (w p)) ^ m / ∏ k, bnorm (fun p => σ (w p)) k := rfl
    rw [e, Real.log_div (pow_ne_zero _ (A.pos _ hz).ne') (Finset.prod_ne_zero_iff.2 fun k _ => hb k),
      Real.log_pow, Real.log_prod fun k _ => hb k]
    simp only [twistLine]
    push_cast
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, mul_assoc]
    ring
  simp only [h1, ← Finset.mul_sum]
  have h2 : ∑ k, (((twistLine A m).a k : ℤ) : ℝ) * blockHt L w k =
      m * ∑ k, (A.a k : ℝ) * blockHt L w k - sumHt L w := by
    simp only [twistLine, sumHt]
    push_cast
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [h2]
  ring

lemma abs_lineHt_le (B : HermLine ι) (hB : IsSmoothHerm B) :
    ∃ n C : ℝ, 0 ≤ n ∧ 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L),
      (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → |lineHt B L w| ≤ n * sumHt L w + C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound B hB
  refine ⟨∑ k, |(B.a k : ℝ)|, C, Finset.sum_nonneg fun _ _ => abs_nonneg _, hC0, fun L _ _ w hw => ?_⟩
  have hh : ∀ k, 0 ≤ blockHt L w k := fun k => blockHt_nonneg w k (hw k)
  unfold lineHt
  rw [ptHt_eq _ _ w hw]
  refine (abs_add_le _ _).trans (add_le_add ?_ (avg_abs_le _ fun σ => hC _ fun k => ?_))
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold sumHt
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_of_nonneg (hh k)]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun k => |(B.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)) (hh k)
  · obtain ⟨i, hi⟩ := hw k
    exact ⟨i, (map_ne_zero σ).2 hi⟩

end Heights

section Sections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

lemma aeval_emb {L : Type} [Field L] (σ : L →+* ℂ) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm

lemma ptsOver_emb {L : Type} [Field L] (σ : L →+* ℂ) {P : Ideal (MRing ι)} {z : (Σ k, ι k) → L}
    (hz : z ∈ ptsOver L P) : (fun p => σ (z p)) ∈ ptsOver ℂ P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_emb, hz.2 f hf, map_zero]

lemma hasVal_emb {L : Type} [Field L] (σ : L →+* ℂ) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω}
    {z : (Σ k, ι k) → L} {w : L} (h : HasVal y a u z w) : HasVal y a u (fun p => σ (z p)) (σ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_emb]
    exact (map_ne_zero σ).2 h0
  · rw [aeval_emb, aeval_emb, h1, map_mul]

lemma lineHt_lower {y : (Σ k, ι k) → Ω} {d : ℕ} (hv : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) (hb : Birational y)
    (M : HermLine ι) (hM : IsSmoothHerm M) (u : Ω) (hu : u ∈ chartLatNm y M.a 1) :
    ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 →
      HasVal y M.a u w val → -C ≤ lineHt M L w := by
  have hu' : ((1 : ℕ) : Ω) * u ^ 1 ∈ chartLatNm y M.a 1 := by simpa using hu
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hv hb M 1 1 u hM one_pos one_pos hu'
  refine ⟨C, fun L _ _ w hw val hval hw' => ?_⟩
  have h1 := GlobalTheory.T.height_lower_bound_chart_norm K ι Ω y d hv hb M.a u 1 1 one_pos one_pos hu' (fun z => Real.log (M.h z)) L w hw val hval hw'
  simp only [Nat.cast_one, Real.log_one, div_one, sub_zero] at h1
  refine le_trans ?_ h1
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∑ _σ : L →+* ℂ, (-C) = Module.finrank ℚ L * (-C) := by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  rw [le_inv_mul_iff₀ hd, ← hc]
  refine Finset.sum_le_sum fun σ _ => ?_
  have hz := ptsOver_emb σ hw
  have h2 := hC _ hz (σ val) (hasVal_emb σ hw')
  have hvp : 0 < ‖σ val‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hval)
  have hpos := M.pos (fun p => σ (w p)) hz.1
  have h3 := Real.log_le_log hvp h2
  rw [Real.log_mul (Real.exp_pos C).ne' hpos.ne', Real.log_exp] at h3
  linarith

lemma sumHt_le {y : (Σ k, ι k) → Ω} {d : ℕ} (hv : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) (hb : Birational y)
    (A : HermLine ι) (hA : IsSmoothHerm A) (ha : AmpleQ y A.a) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y),
      sumHt L w ≤ m * lineHt A L w + C := by
  obtain ⟨m, l, s, hs, hcov⟩ := ha
  have hM := twistLine_smooth hA m
  choose C hC using fun i => lineHt_lower hv hb (twistLine A m) hM (s i) (hs i)
  refine ⟨m, ∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun L _ _ w hw => ?_⟩
  obtain ⟨i, val, hval, hw'⟩ := hcov L w hw
  have h1 := hC i L w hw val hval hw'
  rw [lineHt_twist A m w hw.1] at h1
  have h2 : C i ≤ ∑ i, |C i| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  linarith

end Sections

theorem height_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → ∀ A : HermLine ι, IsSmoothHerm A → AmpleQ y A.a → (∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), -C ≤ lineHt A L w) ∧ ∀ B : HermLine ι, IsSmoothHerm B → ∃ n C : ℝ, 0 ≤ n ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt B L w| ≤ n * lineHt A L w + C := by
  intro K _ ι _ Ω _ y d hv hb A hA ha
  obtain ⟨m, C, hC0, hC⟩ := sumHt_le hv hb A hA ha
  obtain ⟨nA, CA, hnA, hCA, hAle⟩ := abs_lineHt_le A hA
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hsum : ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), sumHt L w ≤ C := by
      intro L _ _ w hw
      simpa using hC L w hw
    refine ⟨⟨nA * C + CA, fun L _ _ w hw => ?_⟩, fun B hB => ?_⟩
    · have h1 := hAle L w hw.1
      have h2 := mul_le_mul_of_nonneg_left (hsum L w hw) hnA
      linarith [neg_abs_le (lineHt A L w)]
    · obtain ⟨n, CB, hn, hCB, hBle⟩ := abs_lineHt_le B hB
      refine ⟨0, n * C + CB, le_rfl, fun L _ _ w hw => ?_⟩
      have h1 := hBle L w hw.1
      have h2 := mul_le_mul_of_nonneg_left (hsum L w hw) hn
      linarith
  · have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    refine ⟨⟨C / m, fun L _ _ w hw => ?_⟩, fun B hB => ?_⟩
    · have h1 := hC L w hw
      have h2 := sumHt_nonneg w hw.1
      rw [neg_le_iff_add_nonneg, ← mul_le_mul_iff_right₀ hmr]
      have h3 : (m : ℝ) * (lineHt A L w + C / m) = m * lineHt A L w + C := by
        field_simp
      rw [mul_zero, h3]
      linarith
    · obtain ⟨n, CB, hn, hCB, hBle⟩ := abs_lineHt_le B hB
      refine ⟨n * m, n * C + CB, mul_nonneg hn hmr.le, fun L _ _ w hw => ?_⟩
      have h1 := hBle L w hw.1
      have h2 := mul_le_mul_of_nonneg_left (hC L w hw) hn
      nlinarith [h1, h2]

end GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBoundsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_height_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d → Birational y → ∀ A : HermLine ι, IsSmoothHerm A → AmpleQ y A.a → (∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), -C ≤ lineHt A L w) ∧ ∀ B : HermLine ι, IsSmoothHerm B → ∃ n C : ℝ, 0 ≤ n ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt B L w| ≤ n * lineHt A L w + C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | exact GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RefLowerOfFibreInput
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.RefLow

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem lineHt_eq (A : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt A L w = (Module.finrank ℚ L : ℝ)⁻¹ *
      (∑ k, (A.a k : ℝ) * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) +
        ∑ σ : L →+* ℂ, Real.log (A.h fun p => σ (w p))) := by
  unfold lineHt ptHt
  rw [finsum_sum_mul (fun k => (A.a k : ℝ)) (fun k (v : FinitePlace L) => Real.log (⨆ i, v (w ⟨k, i⟩)))]
  intro k
  refine support_log_iSup_place_finite (y := fun i => w ⟨k, i⟩) ?_
  obtain ⟨i, hi⟩ := hw k
  exact Function.ne_iff.mpr ⟨i, hi⟩

theorem lineHt_combLine_one {J : Type} [Fintype J] (l : J → HermLine ι) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt (combLine l fun _ => 1) L w = ∑ j, lineHt (l j) L w := by
  simp only [lineHt_eq _ L w hw]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    simp [combLine, Finset.sum_apply]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero σ).mpr hi⟩
    have : (combLine l fun _ => 1).h (fun p => σ (w p)) = ∏ j, (l j).h fun p => σ (w p) := by
      simp [combLine]
    rw [this, Real.log_prod fun j _ => ((l j).pos _ hz).ne']

theorem isSmoothHerm_combLine_one {J : Type} [Fintype J] (l : J → HermLine ι) (hl : ∀ j, IsSmoothHerm (l j)) :
    IsSmoothHerm (combLine l fun _ => 1) := by
  have : (combLine l fun _ => 1).h = fun z => ∏ j, (l j).h z := by
    funext z
    simp [combLine]
  unfold IsSmoothHerm
  rw [this]
  exact contDiffOn_prod fun j _ => hl j

end Lines

section Flags

variable {K : Type} [Field K] [NumberField K]

theorem sum_succ_sub_castSucc {r : ℕ} (g : Fin (r + 1) → ℝ) :
    ∑ i : Fin r, (g i.succ - g i.castSucc) = g (Fin.last r) - g 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih fun i => g i.castSucc
    simp only [Fin.succ_castSucc, h, Fin.succ_last, Fin.castSucc_zero]
    ring

theorem normDegree_rank_zero (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier) (h : E.rank F = 0) :
    E.normDegree F = 0 := by
  have hb : F = ⊥ := Submodule.finrank_eq_zero.1 h
  rw [hb, HermitianBundle.normDegree, HermitianBundle.degree_bot, zero_div]

theorem normDegree_top {E : HermitianBundle.{0} K} {r : ℕ} (A : SatFlag E r) :
    E.normDegree A.top = ∑ i, A.grDeg i := by
  have h0 : E.normDegree (A.F 0) = 0 := normDegree_rank_zero E _ (by simpa using A.rank 0)
  have := sum_succ_sub_castSucc fun i => E.normDegree (A.F i)
  simp only [SatFlag.grDeg, SatFlag.top]
  rw [this, h0, sub_zero]

end Flags

section Core

variable {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {Ψ : Type} [Fintype Ψ] {a b : ℕ}

theorem abs_sum_fin_le {n : ℕ} (g : Fin n → ℝ) (C : ℝ) (h : ∀ i, |g i| ≤ C) : |∑ i, g i| ≤ n * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)
  simp

theorem flatDeg_sub_le (A : FlagPair E Ψ a b) (h : Ψ × Fin (a + b) → ℝ) (C : ℝ)
    (hW : ∀ τ (i : Fin a), |h (τ, Fin.castAdd b i) - (A.W τ).grDeg i| ≤ C)
    (hS : ∀ τ (i : Fin b), |h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev| ≤ C) (τ : Ψ) :
    |A.flatDeg τ - ∑ l, h (τ, l)| ≤ ((a : ℝ) + b) * C := by
  have e : A.flatDeg τ - ∑ l, h (τ, l) =
      -(∑ i, (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i)) -
        ∑ i, (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev) := by
    have hr : ∑ i : Fin b, (A.S τ).grDeg i.rev = ∑ i, (A.S τ).grDeg i :=
      Equiv.sum_comp Fin.revPerm fun i => (A.S τ).grDeg i
    rw [FlagPair.flatDeg, normDegree_top, normDegree_top, Fin.sum_univ_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hr]
    ring
  have h1 := abs_le.1 (abs_sum_fin_le _ C (hW τ))
  have h2 := abs_le.1 (abs_sum_fin_le _ C (hS τ))
  rw [e, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem lamDeg_le (A : FlagPair E Ψ a b) (h : Ψ × Fin (a + b) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ τ (i : Fin a), |h (τ, Fin.castAdd b i) - (A.W τ).grDeg i| ≤ C)
    (hS : ∀ τ (i : Fin b), |h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev| ≤ C)
    (mu : Ψ → Fin (a + b) → ℝ) (hmu : ∀ τ i, |mu τ i| ≤ 2) :
    A.lamDeg mu ≤ -(∑ τ, ∑ l, mu τ l * h (τ, l)) + Fintype.card Ψ * (((a : ℝ) + b) * (2 * C)) := by
  have key : ∀ τ, -(∑ i : Fin a, mu τ (Fin.castAdd b i) * (A.W τ).grDeg i) +
      ∑ i : Fin b, mu τ (Fin.natAdd a i) * (A.S τ).grDeg i.rev ≤
      -(∑ l, mu τ l * h (τ, l)) + ((a : ℝ) + b) * (2 * C) := by
    intro τ
    have e : -(∑ i : Fin a, mu τ (Fin.castAdd b i) * (A.W τ).grDeg i) +
        ∑ i : Fin b, mu τ (Fin.natAdd a i) * (A.S τ).grDeg i.rev + ∑ l, mu τ l * h (τ, l) =
        ∑ i : Fin a, mu τ (Fin.castAdd b i) * (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i) +
        ∑ i : Fin b, mu τ (Fin.natAdd a i) * (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev) := by
      rw [Fin.sum_univ_add]
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have h1 := abs_sum_fin_le (fun i : Fin a =>
      mu τ (Fin.castAdd b i) * (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i)) (2 * C) fun i => by
        rw [abs_mul]
        exact mul_le_mul (hmu _ _) (hW τ i) (abs_nonneg _) (by norm_num)
    have h2 := abs_sum_fin_le (fun i : Fin b =>
      mu τ (Fin.natAdd a i) * (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev)) (2 * C) fun i => by
        rw [abs_mul]
        exact mul_le_mul (hmu _ _) (hS τ i) (abs_nonneg _) (by norm_num)
    have h1' := (abs_le.1 h1).2
    have h2' := (abs_le.1 h2).2
    nlinarith
  unfold FlagPair.lamDeg
  refine (Finset.sum_le_sum fun τ _ => key τ).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp

theorem flat_and_deg (A : FlagPair E Ψ a b) (hO : A.IsOrthFull) (h : Ψ × Fin (a + b) → ℝ) (C B Cs : ℝ)
    (hW : ∀ τ (i : Fin a), |h (τ, Fin.castAdd b i) - (A.W τ).grDeg i| ≤ C)
    (hS : ∀ τ (i : Fin b), |h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev| ≤ C)
    (hB : ∀ r, |h r| ≤ B) (hs : ∀ τ, |∑ l, h (τ, l)| ≤ Cs) :
    (∀ τ, |A.flatDeg τ| ≤ Cs + ((a : ℝ) + b) * C) ∧
      -E.normDegree ⊤ ≤ Fintype.card Ψ * (Cs + ((a : ℝ) + b) * C) + 2 * (Fintype.card Ψ * ((a : ℝ) * (B + C))) := by
  have hf : ∀ τ, |A.flatDeg τ| ≤ Cs + ((a : ℝ) + b) * C := by
    intro τ
    have h1 := abs_le.1 (flatDeg_sub_le A h C hW hS τ)
    have h2 := abs_le.1 (hs τ)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨hf, ?_⟩
  have hw : ∀ τ, -E.normDegree (A.W τ).top ≤ (a : ℝ) * (B + C) := by
    intro τ
    rw [normDegree_top, ← Finset.sum_neg_distrib]
    refine (Finset.sum_le_sum (g := fun _ => B + C) fun i _ => ?_).trans
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
    have h1 := abs_le.1 (hW τ i)
    have h2 := abs_le.1 (hB (τ, Fin.castAdd b i))
    linarith [h1.1, h1.2, h2.1, h2.2]
  have h0 := (GlobalTheory.T.orthogonal_flag_degree_comparison K E Ψ a b A hO).1
  have h1 : ∑ τ, A.flatDeg τ ≤ Fintype.card Ψ * (Cs + ((a : ℝ) + b) * C) := by
    refine (Finset.sum_le_sum (g := fun _ => Cs + ((a : ℝ) + b) * C) fun τ _ => (le_abs_self _).trans (hf τ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ τ, -E.normDegree (A.W τ).top ≤ Fintype.card Ψ * ((a : ℝ) * (B + C)) := by
    refine (Finset.sum_le_sum (g := fun _ => (a : ℝ) * (B + C)) fun τ _ => hw τ).trans ?_
    simp
  linarith

end Core

section Root

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem rootHt_zero_one (R : RootModel Ψ N) (L : Type) [Field L] [NumberField L] (w : (Σ k, R.ι k) → L) :
    rootHt R 1 0 1 L w = lineHt R.A L w / R.kA := by
  simp [rootHt, Fintype.sum_option, RootModel.coef, RootModel.line]
  ring

theorem rootHt_mu_zero (R : RootModel Ψ N) (mu : Wt Ψ N) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) :
    rootHt R 1 mu 0 L w = -∑ τ, ∑ l, mu τ l * lineHt (R.x 1 (τ, l)) L w := by
  simp [rootHt, Fintype.sum_option, RootModel.coef, RootModel.line, Fintype.sum_prod_type]

theorem abs_entry_le (mu : Wt Ψ N) (τ : Ψ) (i : Fin N) : |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  have h2 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  rw [Real.norm_eq_abs] at h2
  exact h2.trans h1

end Root

theorem refLower_of_fibre (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (R : RootModel Ψ (j + 1 + (k + 1)))
    (hA : AmpleQ R.y R.A.a) (hFl : FlatUnit R) (hFi : FibreInput R) : RefLower R := by
  classical
  obtain ⟨C, hC0, hI⟩ := hFi
  obtain ⟨⟨K₀, hK₀⟩, hB⟩ := GlobalTheory.T.ample_height_bounds R.K R.ι R.Ω R.y _ R.arith R.birational R.A R.A_smooth hA
  choose n c hn hbd using fun r => hB (R.x 1 r) (R.x_smooth 1 r)
  have hflat : ∀ τ, ∃ c' : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal R.y),
      |∑ l, lineHt (R.x 1 (τ, l)) L w| ≤ c' := by
    intro τ
    obtain ⟨kk, u, c0, hk, hu, hv⟩ := hFl τ
    have ha : (combLine (fun l => R.x 1 (τ, l)) fun _ => 1).a = fun b => ∑ i, R.xdeg (τ, i) b := by
      funext b
      simp [combLine, Finset.sum_apply, R.x_deg]
    obtain ⟨c', hc'⟩ := GlobalTheory.T.line_height_bounded_unit R.K R.ι R.Ω R.y _ R.arith R.birational
      (combLine (fun l => R.x 1 (τ, l)) fun _ => 1) kk u c0
      (isSmoothHerm_combLine_one _ fun l => R.x_smooth 1 _) hk (by rw [ha]; exact hu) (by rw [ha]; exact hv)
    refine ⟨c', fun L _ _ w hw => ?_⟩
    rw [← lineHt_combLine_one _ L w hw.1]
    exact hc' L w hw
  choose cf hcf using hflat
  obtain ⟨K1, hK1⟩ : ∃ v, v = |K₀| := ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := hK1 ▸ abs_nonneg _
  obtain ⟨nn, hnn⟩ : ∃ v, v = ∑ r, n r := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ v, v = ∑ r, |c r| := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ v, v = ∑ τ, |cf τ| := ⟨_, rfl⟩
  have hnn0 : 0 ≤ nn := hnn ▸ Finset.sum_nonneg fun r _ => hn r
  have hcc0 : 0 ≤ cc := hcc ▸ Finset.sum_nonneg fun r _ => abs_nonneg _
  have hCs0 : 0 ≤ Cs := hCs ▸ Finset.sum_nonneg fun r _ => abs_nonneg _
  obtain ⟨f, hf⟩ : ∃ v : ℝ, v = Fintype.card Ψ := ⟨_, rfl⟩
  have hf0 : 0 ≤ f := hf ▸ Nat.cast_nonneg _
  obtain ⟨a, ha⟩ : ∃ v : ℝ, v = ((j + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ v : ℝ, v = ((k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ Nat.cast_nonneg _
  have hb0 : 0 ≤ b := hb ▸ Nat.cast_nonneg _
  obtain ⟨kA, hkA⟩ : ∃ v : ℝ, v = R.kA := ⟨_, rfl⟩
  have hkA1 : 1 ≤ kA := by rw [hkA]; exact_mod_cast R.kA_pos
  obtain ⟨Cf, hCf⟩ : ∃ v, v = Cs + (a + b) * C := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  obtain ⟨n1, hn1⟩ : ∃ v, v = 2 * (f * (a * (nn * kA))) := ⟨_, rfl⟩
  have hn10 : 0 ≤ n1 := by rw [hn1]; positivity
  obtain ⟨C', hC'⟩ : ∃ v, v = f * Cf + 2 * (f * (a * (nn * K1 + cc + C))) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  obtain ⟨Cm, hCm⟩ : ∃ v, v = C + C' := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  obtain ⟨C₁, h11, hKC, hlog⟩ := GlobalTheory.CompanionTheory.LogLin.exists_log_affine_le Cm n1 K1 hCm0 hn10 hK10
  obtain ⟨Q, hQ⟩ : ∃ v, v = 4 * f * (a + b) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ v, v = 2 * f * Cf + 2 * f * (a + b) * C := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hQC : 0 ≤ Q * C₁ := mul_nonneg hQ0 (by linarith)
  obtain ⟨D, hD⟩ : ∃ v, v = 1 + C₁ + Q * C₁ + T := ⟨_, rfl⟩
  refine ⟨D, by linarith, fun L _ _ w hw => ?_⟩

  have hhA : -K1 ≤ lineHt R.A L w := by
    have h1 := hK₀ L w hw
    have h2 : K₀ ≤ K1 := hK1 ▸ le_abs_self _
    linarith
  obtain ⟨x, hx⟩ : ∃ v, v = rootHt R 1 0 1 L w := ⟨_, rfl⟩
  have hxA : lineHt R.A L w = kA * x := by
    rw [hx, rootHt_zero_one, ← hkA]
    field_simp
  have hxK : -K1 ≤ x := by
    rw [hxA] at hhA
    nlinarith
  have hxC : -C₁ ≤ x := by linarith
  rw [← hx]
  refine ⟨by linarith, fun mu hd hmu => ?_⟩
  obtain ⟨L', iF, iN, φ, E, A, hO, hW, hS, hSl⟩ := hI L w hw
  have hbnd : ∀ r, |lineHt (R.x 1 r) L w| ≤ nn * (kA * x + K1) + cc := by
    intro r
    have h1 := hbd r L w hw
    have h2 : n r ≤ nn := hnn ▸ Finset.single_le_sum (f := n) (fun r _ => hn r) (Finset.mem_univ r)
    have h3 : |c r| ≤ cc :=
      hcc ▸ Finset.single_le_sum (f := fun r => |c r|) (fun r _ => abs_nonneg _) (Finset.mem_univ r)
    have h4 : 0 ≤ kA * x + K1 := by rw [← hxA]; linarith
    have h5 : n r * (kA * x + K1) ≤ nn * (kA * x + K1) := mul_le_mul_of_nonneg_right h2 h4
    have h6 := mul_nonneg (hn r) hK10
    have h7 := le_abs_self (c r)
    rw [hxA] at h1
    nlinarith
  have hsum : ∀ τ, |∑ l, lineHt (R.x 1 (τ, l)) L w| ≤ Cs := by
    intro τ
    refine (hcf τ L w hw).trans ((le_abs_self _).trans ?_)
    exact hCs ▸ Finset.single_le_sum (f := fun τ => |cf τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  obtain ⟨hfl, hdeg⟩ := flat_and_deg A hO (fun r => lineHt (R.x 1 r) L w) C _ Cs hW hS hbnd hsum
  simp only [← ha, ← hb, ← hf, ← hCf] at hfl hdeg
  have hy : -E.normDegree ⊤ ≤ n1 * x + Cm := by
    have e : f * Cf + 2 * (f * (a * (nn * (kA * x + K1) + cc + C))) = n1 * x + C' := by
      rw [hn1, hC']
      ring
    rw [hCm]
    linarith
  obtain ⟨y, hyy⟩ : ∃ v, v = max (-E.normDegree ⊤) 0 := ⟨_, rfl⟩
  have hp : 0 ≤ y := hyy ▸ le_max_right _ _
  obtain ⟨m, hm⟩ : ∃ v, v = C * Real.log (2 + C + y) + C := ⟨_, rfl⟩
  have hl1 : 0 ≤ Real.log (2 + C + y) := Real.log_nonneg (by linarith)
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hCCm : C ≤ Cm := by linarith
  have hl2 : Real.log (2 + C + y) ≤ Real.log (2 + Cm + y) := Real.log_le_log (by linarith) (by linarith)
  have hmC : m ≤ C₁ * Real.log (2 + C₁ + x) := by
    refine le_trans ?_ (hlog x _ hxK hy)
    rw [← hyy, hm]
    have := mul_le_mul hCCm hl2 hl1 hCm0
    linarith
  have hsl : E.slopeMax ≤ (m : EReal) := by
    rw [hm, hyy]
    exact hSl
  have hent : ∀ τ i, |mu τ i| ≤ 2 := fun τ i => (abs_entry_le mu τ i).trans hmu
  have hlow := GlobalTheory.T.weighted_flag_degree_lower_bound L' E Ψ j k A mu 2 m Cf (fun τ a b hab => hd τ a b hab) hent hm0 hsl hfl
  have hup := lamDeg_le A (fun r => lineHt (R.x 1 r) L w) C hC0 hW hS mu hent
  simp only [← ha, ← hb, ← hf] at hup
  have hab : (j : ℝ) + 1 + ((k : ℝ) + 1) = a + b := by
    rw [ha, hb]
    push_cast
    ring
  rw [hab, ← hf] at hlow
  rw [rootHt_mu_zero]
  have hl3 : 0 ≤ Real.log (2 + C₁ + x) := Real.log_nonneg (by linarith)
  have hl4 : Real.log (2 + C₁ + x) ≤ Real.log (2 + D + x) :=
    Real.log_le_log (by linarith) (by linarith)
  have hDl : Q * C₁ * Real.log (2 + C₁ + x) ≤ D * Real.log (2 + D + x) :=
    mul_le_mul (by linarith) hl4 hl3 (by linarith)
  have hQm : Q * m ≤ Q * (C₁ * Real.log (2 + C₁ + x)) := mul_le_mul_of_nonneg_left hmC hQ0
  have e1 : f * (2 * 2 * (a + b) * m + 2 * Cf) = Q * m + 2 * f * Cf := by
    rw [hQ]
    ring
  have e2 : f * ((a + b) * (2 * C)) = 2 * f * (a + b) * C := by ring
  have e3 : Q * (C₁ * Real.log (2 + C₁ + x)) = Q * C₁ * Real.log (2 + C₁ + x) := by ring
  rw [e1] at hlow
  rw [e2] at hup
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.RefLow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RefLowerOfFibreInputStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ref_lower_of_fibre_input : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (R : RootModel Ψ (j + 1 + (k + 1))), AmpleQ R.y R.A.a → FlatUnit R → FibreInput R → RefLower R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre | exact GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfFibreInput
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.TopLower

theorem i5_of_hasRef_of_fibreInput : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (T : RootTower Ψ (j + 1 + (k + 1)))
    (II : IntersectionSystem) (R : T.Comp → RootModel Ψ (j + 1 + (k + 1))), IsIntersectionSystem II → HasRef T R →
    (∀ c, AmpleQ (R c).y (R c).A.a ∧ FlatUnit (R c) ∧ FibreInput (R c)) → T.I5 II := by
  intro Ψ _ _ j k T II R hII hR h
  exact GlobalTheory.T.tower_i5_of_reference Ψ _ T II R hII hR fun c =>
    GlobalTheory.T.ref_lower_of_fibre_input Ψ j k (R c) (h c).1 (h c).2.1 (h c).2.2

end GlobalTheory.CompanionTheory.Ar.Ht.TopLower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfFibreInputStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_i5_of_fibre_input : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (T : RootTower Ψ (j + 1 + (k + 1))) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ (j + 1 + (k + 1))), IsIntersectionSystem II → HasRef T R → (∀ c, AmpleQ (R c).y (R c).A.a ∧ FlatUnit (R c) ∧ FibreInput (R c)) → T.I5 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput | exact GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput <;> assumption)
end

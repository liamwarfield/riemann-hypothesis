module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContinuousOnIteratedFDerivTranslate

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IntegrableIteratedFDerivTranslate
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedFDerivMulConstOf
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rising_product_ne_zero (a : ℤ) (m : ℕ) (h : ∀ i : ℕ, i < m → (i : ℤ) + a ≠ 0) :
    ∏ i ∈ Finset.range m, ((a : ℂ) + (i : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply h i (Finset.mem_range.1 hi)
  have : (((i : ℤ) + a : ℤ) : ℂ) = 0 := by push_cast; linear_combination h0
  exact_mod_cast this

theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  simp only [herm, Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp <;> ring

theorem inG_nU_herm (x : Fin n → Fin n → ℝ) : InG (nU (herm x)) := by
  have hH := herm_isHermitian x
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hH]

theorem fubini_step (p q : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    (hψ : IsSingTest ψ) :
    ∫ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ ∂μ =
      ∫ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hU0 : ∀ g : M2 n, InG g → g ∈ {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := fun g hg =>
    ⟨(gset_sub_dom hg).2.1, (gset_sub_dom hg).2.2.1⟩
  have hf0c : ContinuousOn (f0 (n := n) p q) {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
    (contDiffOn_scalar_section p q).continuousOn
  have hf0ne : ∀ k, f0 p q (ι k) ≠ 0 := fun k h => by
    have := scalar_section_mul_conjugate_section ((hK (ι k)).2 ⟨k, rfl⟩) p q; rw [h, zero_mul] at this; exact zero_ne_one this
  have hc : Continuous fun k => (f0 p q (ι k))⁻¹ :=
    (hf0c.comp_continuous hι (fun k => hU0 _ (hιG k))).inv₀ hf0ne
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set F : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => f0 p q (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 *
    (f0 p q (ι z.1))⁻¹ with hFdef
  have hFc : Continuous F :=
    ((hf0c.comp_continuous hmap (fun z => hU0 _ (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hc.comp continuous_fst)
  have hFs : HasCompactSupport F := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport F) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFdef, h0]
  have hFi : Integrable F (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ = ∫ x, F (k, x) := by
    intro k; rw [← integral_mul_const]
  have e2 : ∀ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x = ∫ k, F (k, x) ∂μ := by
    intro x; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFdef, mul_assoc]; ring
  simp_rw [e1, e2]
  exact integral_integral_swap (f := fun k x => F (k, x)) hFi

theorem embOn_add (s : Finset (Fin n)) (T T' : Matrix s s ℂ) : embOn s (T + T') = embOn s T + embOn s T' := by
  ext a b; simp only [embOn, Matrix.add_apply]; split_ifs <;> simp

theorem embOn_smul (s : Finset (Fin n)) (c : ℂ) (T : Matrix s s ℂ) : embOn s (c • T) = c • embOn s T := by
  ext a b; simp only [embOn, Matrix.smul_apply]; split_ifs <;> simp

theorem WD_add (Q Q' R R' : Matrix (Fin n) (Fin n) ℂ) : WD (Q + Q') (R + R') = WD Q R + WD Q' R' := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (Q + Q') (R + R') 0 = fromBlocks 0 Q R 0 + fromBlocks 0 Q' R' 0 := by
    rw [Matrix.fromBlocks_add, add_zero]
  simp only [WD, this, Matrix.mul_add, Matrix.add_mul]

theorem WD_smul (c : ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ) : WD (c • Q) (c • R) = c • WD Q R := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) (c • R) 0 = c • fromBlocks 0 Q R 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero]
  simp only [WD, this, Matrix.mul_smul, Matrix.smul_mul]

theorem WD_split (Q R : Matrix (Fin n) (Fin n) ℂ) : WD Q R = WD Q 0 + WD 0 R := by
  rw [← WD_add]; simp

def LQ (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD (embOn s T) 0
      map_add' := fun T T' => by
        have h := WD_add (embOn s T) (embOn s T') (0 : Matrix (Fin n) (Fin n) ℂ) 0
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (embOn s T) (0 : Matrix (Fin n) (Fin n) ℂ)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

def LR (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD 0 (embOn s T)
      map_add' := fun T T' => by
        have h := WD_add (0 : Matrix (Fin n) (Fin n) ℂ) 0 (embOn s T) (embOn s T')
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (0 : Matrix (Fin n) (Fin n) ℂ) (embOn s T)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

theorem LQ_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LQ s x T = x * WD (embOn s T) 0 := rfl

theorem LR_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LR s x T = x * WD 0 (embOn s T) := rfl

theorem mul_mX (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) : x * mX 1 Q R 1 = x + x * WD Q 0 + x * WD 0 R := by
  rw [mX_eq, Matrix.mul_add, Matrix.mul_one, WD_split, Matrix.mul_add, add_assoc]

theorem fin_append_mul {a b : ℕ} (M : M2 n) (u : Fin a → M2 n) (v : Fin b → M2 n) :
    (fun i => M * Fin.append u v i) = Fin.append (fun i => M * u i) (fun i => M * v i) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem contDiff_mulLeft (M : M2 n) : ContDiff ℂ ∞ (fun x : M2 n => M * x) :=
  (LinearMap.mulLeft ℂ M).toContinuousLinearMap.contDiff

theorem contDiff_nU_sandwich (a b : M2 n) : ContDiff ℂ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun H => a * fromBlocks 0 H 0 0 * b
      map_add' := fun H H' => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (H + H') 0 0 : M2 n) = fromBlocks 0 H 0 0 + fromBlocks 0 H' 0 0 := by
          rw [Matrix.fromBlocks_add]; simp
        rw [this, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c H => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • H) 0 0 : M2 n) = c • fromBlocks 0 H 0 0 := by
          rw [Matrix.fromBlocks_smul]; simp
        simp only [RingHom.id_apply]
        rw [this, Matrix.mul_smul, Matrix.smul_mul] }
  have h : (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) = fun H => a * b + L.toContinuousLinearMap H := by
    funext H
    have : nU H = 1 + (fromBlocks 0 H 0 0 : M2 n) := by
      rw [nU, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [h]
  exact contDiff_const.add L.toContinuousLinearMap.contDiff

theorem iteratedFDeriv_mul_const_of (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (c : ℂ)
    (x : M2 n) (hx : x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F y * c) x v = iteratedFDeriv ℂ N F x v * c := by
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left ((ContinuousLinearMap.mul ℂ ℂ).flip c) hFx
    (i := N) (by exact_mod_cast le_top)
  have e : (fun y => F y * c) = (ContinuousLinearMap.mul ℂ ℂ).flip c ∘ F := by funext y; rfl
  rw [e, h]; rfl

theorem integrable_of_continuous_K {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] {f : Kg → ℂ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _))

theorem detD_detD_mul_const {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) (c : ℂ) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S) * c)) =
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) * c := by
  rw [detD_detD_comp (fun y => F y * c) U hU (hF.mul contDiffOn_const) x₀ hx LA LB,
    detD_detD_comp F U hU hF x₀ hx LA LB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [iteratedFDeriv_mul_const_of F U hU hF c x₀ hx]; ring

end PositivityTheory.Rg.Sw.LVs
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem integrable_iteratedFDeriv_translate (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c)
    (N : ℕ) (x : M2 n) (hx : ∀ k, ι k * x ∈ U) (w : Fin N → M2 n) :
    Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x w) μ := by
  have h := continuousOn_iteratedFDeriv_translate F U hU hF Kg ι hι c hc N
  have hg : Continuous (fun k : Kg => (k, x)) := continuous_id.prodMk continuous_const
  have hm : ∀ k, (k, x) ∈ (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U} : Set (Kg × M2 n)) :=
    fun k => ⟨Set.mem_univ _, hx⟩
  have h2 : Continuous (fun k : Kg => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x) :=
    h.comp_continuous hg hm
  exact integrable_of_continuous_K μ ((continuous_eval_const w).comp h2)

theorem spherical_detD (hHI : HolInt) (F : M2 n → ℂ) (hF : ContDiffOn ℂ ∞ F (Dom n))
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hLA : ∀ M x T, LA (M * x) T = M * LA x T) (hLB : ∀ M x S, LB (M * x) S = M * LB x S)
    (g : M2 n) (hg : ∀ k, ι k * g ∈ Dom n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ := by
  classical
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => F (ι k * x) * c k) Ω := fun k =>
    (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := hHI n Kg μ Ω (fun k x => F (ι k * x) * c k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate F (Dom n) isOpen_dom hF Kg ι hι c hc N) hsm
  have hgΩ : g ∈ Ω := hg
  have hAv : ContDiffOn ℂ ∞ (fun x => ∫ k, F (ι k * x) * c k ∂μ) Ω := hH.1
  have key : ∀ (N : ℕ) (v : Fin N → M2 n), iteratedFDeriv ℂ N (fun x => ∫ k, F (ι k * x) * c k ∂μ) g v =
      ∫ k, iteratedFDeriv ℂ N (fun x => F (ι k * x) * c k) g v ∂μ := fun N v => hH.2 N g v hgΩ
  have e0 : (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ))
      = fun T => detD (fun S => (fun x => ∫ k, F (ι k * x) * c k ∂μ) (g + LA g T + LB g S)) := rfl
  have hFc : ∀ k, ContDiffOn ℂ ∞ (fun y => F y * c k) (Dom n) := fun k => hF.mul contDiffOn_const
  have hk : ∀ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
      F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    rw [← detD_detD_mul_const F (Dom n) isOpen_dom hF (ι k * g) (hg k) (LA (ι k * g)) (LB (ι k * g)) (c k),
      detD_detD_comp (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k * g) (hg k) _ _]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    rw [iteratedFDeriv_left_mul (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k) g (hg k), fin_append_mul]
    simp only [hLA, hLB]
  have hint : ∀ (σ : Equiv.Perm ιA) (τ : Equiv.Perm ιB), Integrable (fun k =>
      iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1)))) μ :=
    fun σ τ => integrable_iteratedFDeriv_translate F (Dom n) isOpen_dom hF μ ι hι c hc _ g hg _
  rw [e0, detD_detD_comp _ Ω hΩo hAv g hgΩ (LA g) (LB g), integral_congr_ae (Filter.Eventually.of_forall hk)]
  simp only [key]
  symm
  rw [MeasureTheory.integral_finsetSum _ (fun σ _ => MeasureTheory.integrable_finsetSum _ (fun τ _ => (hint σ τ).const_mul _))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun τ _ => (hint σ τ).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul]

theorem transpose_detD (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (WA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (WB : Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hW : ∀ (T T' : Matrix ιA ιA ℂ) (S S' : Matrix ιB ιB ℂ), (WA T + WB S) * (WA T' + WB S') = 0) :
    ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k) ∂μ =
      (-1) ^ (Fintype.card ιA + Fintype.card ιB) * ∫ k, F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ =>
        detD (fun S : Matrix ιB ιB ℂ => F2 (ι k + ι k * WA T + ι k * WB S))) ∂μ := by
  classical
  have hιK : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hιDom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom (hιK k).1
  set N := Fintype.card ιA + Fintype.card ιB with hN
  let W : Equiv.Perm ιA → Equiv.Perm ιB → Fin N → M2 n := fun σ τ =>
    Fin.append (fun i => WA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
      (fun i => WB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))
  have hWW : ∀ σ τ a b, W σ τ a * W σ τ b = 0 := by
    intro σ τ a b
    have hAA : ∀ T T' : Matrix ιA ιA ℂ, WA T * WA T' = 0 := fun T T' => by
      simpa only [map_zero, add_zero] using hW T T' 0 0
    have hAB : ∀ (T : Matrix ιA ιA ℂ) (S' : Matrix ιB ιB ℂ), WA T * WB S' = 0 := fun T S' => by
      simpa only [map_zero, add_zero, zero_add] using hW T 0 0 S'
    have hBA : ∀ (S : Matrix ιB ιB ℂ) (T' : Matrix ιA ιA ℂ), WB S * WA T' = 0 := fun S T' => by
      simpa only [map_zero, add_zero, zero_add] using hW 0 T' S 0
    have hBB : ∀ S S' : Matrix ιB ιB ℂ, WB S * WB S' = 0 := fun S S' => by
      simpa only [map_zero, zero_add] using hW 0 0 S S'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;>
      simp only [W, Fin.append_left, Fin.append_right]
    · exact hAA _ _
    · exact hAB _ _
    · exact hBA _ _
    · exact hBB _ _
  have expand : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k,
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (ι k + ι k * WA T + ι k * WB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i) := by
    intro F hF k
    have e := detD_detD_comp F (Dom n) isOpen_dom hF (ι k) (hιDom k)
      ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WA) ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WB)
    refine e.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_)
    congr 2
    rw [fin_append_mul]
    rfl
  have hcontD : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ σ τ,
      Continuous (fun k => iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i)) := by
    intro F hF σ τ
    have h1 : ContinuousOn (iteratedFDeriv ℂ N F) (Dom n) :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) isOpen_dom.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen N isOpen_dom hx).symm)
    have h2 : Continuous (fun k => iteratedFDeriv ℂ N F (ι k)) := h1.comp_continuous hι hιDom
    have h3 : Continuous (fun k => (fun i => ι k * W σ τ i : Fin N → M2 n)) :=
      continuous_pi fun i => hι.mul continuous_const
    exact h2.eval h3
  have hc1 : Continuous fun k => F1 (ι k) := hF1.continuousOn.comp_continuous hι hιDom
  have hc2 : Continuous fun k => F2 (ι k) := hF2.continuousOn.comp_continuous hι hιDom
  have hint1 : ∀ σ τ, Integrable (fun k => iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) μ :=
    fun σ τ => integrable_of_continuous_K μ ((hcontD F1 hF1 σ τ).mul hc2)
  have hint2 : ∀ σ τ, Integrable (fun k => F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) μ :=
    fun σ τ => integrable_of_continuous_K μ (hc1.mul (hcontD F2 hF2 σ τ))
  have eL : (fun k => detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k)) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) := by
    funext k; rw [expand F1 hF1 k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have eR : (fun k => F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F2 (ι k + ι k * WA T + ι k * WB S)))) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) := by
    funext k; rw [expand F2 hF2 k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [eL, eR, MeasureTheory.integral_finsetSum _ (fun σ _ => MeasureTheory.integrable_finsetSum _ (fun τ _ => (hint1 σ τ).const_mul _)),
    MeasureTheory.integral_finsetSum _ (fun σ _ => MeasureTheory.integrable_finsetSum _ (fun τ _ => (hint2 σ τ).const_mul _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun τ _ => (hint1 σ τ).const_mul _),
    MeasureTheory.integral_finsetSum _ (fun τ _ => (hint2 σ τ).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_const_mul,
    transpose hI F1 F2 χ1 χ2 hF1 hF2 h1 h2 h12 Kg μ ι hι hK N (W σ τ) (hWW σ τ)]
  ring

end PositivityTheory.Rg.Sw.LVs
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_one {n : ℕ} : InG (1 : M2 n) := by simp [InG]

private theorem exists_split_avoiding_of_goodSig (n p q : ℕ) (h : GoodSig n p q) :
    ∃ j ≤ n, (∀ i < j, i ≠ q) ∧ (∀ i < n - j, i ≠ p) ∧ (∀ i < j, i + p ≠ n) ∧ (∀ i < n - j, i + q ≠ n) := by
  unfold GoodSig at h
  rcases h with h | h | h | h
  · exact ⟨min q n, min_le_right _ _, by omega, by omega, by omega, by omega⟩
  · exact ⟨n - min p n, Nat.sub_le _ _, by omega, by omega, by omega, by omega⟩
  · exact ⟨0, Nat.zero_le _, by omega, by omega, by omega, by omega⟩
  · exact ⟨n, le_refl _, by omega, by omega, by omega, by omega⟩

private theorem integral_minorOn_wM_ne_zero {n : ℕ} (j : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    ∫ k, minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ * (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k))) ∂μ ≠ 0 := by
  have hKk : ∀ k, InK (ι k) := fun k => (hK _).2 ⟨k, rfl⟩
  have hU : ∀ k, wM (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro k
    have h1 := first_cayley_block_unitary (hKk k)
    have h2 := second_cayley_block_unitary (hKk k)
    have hu1 : u1 (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 h1
    have hu2 : u2 (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 h2
    have hi : (u2 (ι k))⁻¹ = star (u2 (ι k)) := Matrix.inv_eq_right_inv h2
    unfold wM
    rw [hi]
    exact mul_mem (Unitary.star_mem hu2) hu1
  set g : Kg → ℝ := fun k => Complex.normSq (minorOn (blkA j) (wM (ι k))) * Complex.normSq (minorOn (blkB j) (wM (ι k))) with hg
  have hpt : ∀ k, minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ * (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k))) = ((g k : ℝ) : ℂ) := by
    intro k
    rw [minorOn_inv_of_unitary (hU k), minorOn_inv_of_unitary (hU k)]
    simp only [hg, Complex.ofReal_mul, ← Complex.mul_conj, Complex.star_def]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
  have hw1 : wM (1 : M2 n) = 1 := by
    have h1 : (1 : M2 n) = Matrix.fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
    unfold wM u1 u2
    rw [h1, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
    simp
  have hm1 : ∀ s : Finset (Fin n), minorOn s (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro s
    unfold minorOn
    rw [Matrix.submatrix_one _ Subtype.val_injective]
    simp
  have hcw : Continuous fun k => wM (ι k) :=
    continuousOn_wM.comp_continuous hι (fun k => det_second_cayley_block_ne_zero (hKk k).1)
  have hgc : Continuous g := by
    rw [hg]
    exact ((Complex.continuous_normSq.comp ((continuous_minorOn _).comp hcw))).mul
      (Complex.continuous_normSq.comp ((continuous_minorOn _).comp hcw))
  have hpos : 0 < ∫ k, g k ∂μ := by
    refine hgc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (HasCompactSupport.of_compactSpace _) (fun k => ?_) ?_
    · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · simp [hg, map_one, hw1, hm1]
  exact_mod_cast hpos.ne'

theorem lv_of (hC : Cayley) (hU : UAct) (hDj : DjSec) (hDp : DpDual) (hHI : HolInt) (hHZ : HolZero)
    (hSD : SingToDiff) (hTC : TopComp) (hII : InfInv) : LV := by
  intro n p q hsig Kg _ _ _ _ _ _ μ _ ι hι hK
  by_contra hne
  push_neg at hne
  obtain ⟨j, hjn, hj1, hj2, hj3, hj4⟩ := exists_split_avoiding_of_goodSig n p q hsig
  have hC : ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · have := rising_product_ne_zero (-(q:ℤ)) j (fun i hi => by have := hj1 i hi; omega)
      push_cast at this ⊢
      exact this
    · have := rising_product_ne_zero (-(p:ℤ)) (n - j) (fun i hi => by have := hj2 i hi; omega)
      push_cast at this ⊢
      exact this
  have hC' : ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · have := rising_product_ne_zero ((p:ℤ) - n) j (fun i hi => by have := hj3 i hi; omega)
      push_cast at this ⊢
      exact this
    · have := rising_product_ne_zero ((q:ℤ) - n) (n - j) (fun i hi => by have := hj4 i hi; omega)
      push_cast at this ⊢
      exact this
  have hKk : ∀ k, InK (ι k) := fun k => (hK _).2 ⟨k, rfl⟩
  have hGk : ∀ k, InG (ι k) := fun k => (hKk k).1
  have hfv : ∀ k, (f0 (p:ℤ) (q:ℤ) (ι k))⁻¹ = fV (p:ℤ) (q:ℤ) (ι k) := fun k =>
    (eq_inv_of_mul_eq_one_right (scalar_section_mul_conjugate_section (hKk k) _ _)).symm
  set Ω : Set (M2 n) := {x : M2 n | ∀ k, ι k * x ∈ Dom n} with hΩdef
  have hΩ : IsOpen Ω := isOpen_domK Kg ι hι
  have hGΩ : ∀ g : M2 n, InG g → g ∈ Ω := fun g hg k => gset_sub_dom (inG_mul (hGk k) hg)
  have hf0 : ContDiffOn ℂ ∞ (f0 (p:ℤ) (q:ℤ)) (Dom n) :=
    (contDiffOn_scalar_section (n := n) _ _).mono (fun x hx => dom_sub x hx)
  have hcV : Continuous fun k => fV (p:ℤ) (q:ℤ) (ι k) :=
    cont_on_K _ (contDiffOn_fV _ _) Kg ι hι (fun k => gset_sub_dom (hGk k))
  have hk_cd : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k : Kg,
      ContDiffOn ℂ ∞ (fun y => F (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) Ω := by
    intro F hF k
    exact (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun y (hy : y ∈ Ω) => hy k)).mul contDiffOn_const
  set Φ : M2 n → ℂ := fun y => ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ with hΦdef
  have hΦ : ContDiffOn ℂ ∞ Φ Ω :=
    (hHI n Kg μ Ω (fun k y => f0 (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) hΩ
      (cont_translate' _ _ isOpen_dom hf0 Kg ι hι _ hcV) (hk_cd _ hf0)).1
  have hD1 : ∀ a b : M2 n, InG a → InG b → detD (fun H : Matrix (Fin n) (Fin n) ℂ => Φ (a * nU H * b)) = 0 := by
    intro a b ha hb
    have hS : IsOpen ((fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) ⁻¹' Ω) :=
      hΩ.preimage (contDiff_nU_sandwich a b).continuous
    have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) ⁻¹' Ω := by
      have hn0 : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
        unfold nU
        exact Matrix.fromBlocks_one
      show a * nU 0 * b ∈ Ω
      rw [hn0, mul_one]
      exact hGΩ _ (inG_mul ha hb)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS 0 h0
    refine hSD n _ r hr (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
    intro ψ hψ
    have h := hne ψ a b hψ ha hb
    rw [fubini_step (p:ℤ) (q:ℤ) Kg μ ι hι hK a b ha hb ψ hψ] at h
    simp only [hfv] at h
    exact h
  have hTop := hTC n j Φ Ω hΩ (fun g hg => hGΩ g hg) hΦ (by
      intro x P S _ _ hP hS
      show ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * (x * mX (1 + P) 0 0 (1 + S))) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ
        = ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * x) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ
      congr 1
      funext k
      rw [← mul_assoc, scalar_section_compact_block_invariant hU j _ _ _ P S hP hS]) hD1
  have hLQ : ∀ (M x : M2 n) (T : Matrix (blkA j) (blkA j) ℂ), LQ (blkA j) (M * x) T = M * LQ (blkA j) x T := by
    intro M x T
    rw [LQ_apply, LQ_apply, mul_assoc]
  have hLR : ∀ (M x : M2 n) (S : Matrix (blkB j) (blkB j) ℂ), LR (blkB j) (M * x) S = M * LR (blkB j) x S := by
    intro M x S
    rw [LR_apply, LR_apply, mul_assoc]
  have hm : ∀ (y : M2 n) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      y * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 = y + LQ (blkA j) y T + LR (blkB j) y S := by
    intro y T S
    rw [mX_eq, WD_split, LQ_apply, LR_apply, mul_add, mul_add, mul_one, add_assoc]
  have key : ∀ y ∈ Dom n, (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      f0 (p:ℤ) (q:ℤ) (y + LQ (blkA j) y T + LR (blkB j) y S)) =
      ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) * hF j p q y := by
    intro y hy
    have h := hDj n j p q y hjn (dom_sub y hy).1 (dom_sub y hy).2
    simp only [hm] at h
    rw [h]
    unfold hF
    ring
  set Ψ : M2 n → ℂ := fun y => ∫ k, hF j (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ with hΨdef
  have hΨ0 : ∀ g ∈ GSet n, Ψ g = 0 := by
    intro g hg
    have h := hTop g hg
    simp only [hm] at h
    rw [show (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
        Φ (g + LQ (blkA j) g T + LR (blkB j) g S)) = _ from
      spherical_detD hHI (f0 (p:ℤ) (q:ℤ)) hf0 μ ι hι _ hcV (LQ (blkA j)) (LR (blkB j)) hLQ hLR g
        (fun k => hGΩ g hg k)] at h
    have hc : (∫ k, (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
        f0 (p:ℤ) (q:ℤ) (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S)) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ) =
        ∫ k, ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) *
          (hF j p q (ι k * g) * fV (p:ℤ) (q:ℤ) (ι k)) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [key _ (hGΩ g hg k)]
      ring
    rw [hc, integral_const_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hC
  have hΨc : ContDiffOn ℂ ∞ Ψ Ω :=
    (hHI n Kg μ Ω (fun k y => hF j (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) hΩ
      (cont_translate' _ _ isOpen_dom (contDiffOn_hF j _ _) Kg ι hι _ hcV) (hk_cd _ (contDiffOn_hF j _ _))).1
  have hΨd : ∀ N : ℕ, iteratedFDeriv ℂ N Ψ 1 = 0 := fun N =>
    hHZ n Ω Ψ hΩ (fun g hg => hGΩ g hg) hΨc hΨ0 N 1 inG_one
  have hLR' : ∀ (M x : M2 n) (T : Matrix (blkA j) (blkA j) ℂ), LR (blkA j) (M * x) T = M * LR (blkA j) x T := by
    intro M x T
    rw [LR_apply, LR_apply, mul_assoc]
  have hLQ' : ∀ (M x : M2 n) (S : Matrix (blkB j) (blkB j) ℂ), LQ (blkB j) (M * x) S = M * LQ (blkB j) x S := by
    intro M x S
    rw [LQ_apply, LQ_apply, mul_assoc]
  have hsph := spherical_detD hHI (hF j (p:ℤ) (q:ℤ)) (contDiffOn_hF j _ _) μ ι hι _ hcV
    (LR (blkA j)) (LQ (blkB j)) hLR' hLQ' 1 (fun k => hGΩ 1 inG_one k)
  have hzero : (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      Ψ (1 + LR (blkA j) 1 T + LQ (blkB j) 1 S)) = 0 := by
    rw [detD_detD_comp Ψ Ω hΩ hΨc 1 (hGΩ 1 inG_one) (LR (blkA j) 1) (LQ (blkB j) 1)]
    simp [hΨd]
  rw [show (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      Ψ (1 + LR (blkA j) 1 T + LQ (blkB j) 1 S)) = _ from hsph] at hzero
  have htr := transpose_detD hII (hF j (p:ℤ) (q:ℤ)) (fV (p:ℤ) (q:ℤ)) (c1 (p:ℤ) (q:ℤ)) (c2 (p:ℤ) (q:ℤ))
    (contDiffOn_hF j _ _) (contDiffOn_fV _ _) (fun P x hP hx => hF_law j _ _ hP hx)
    (fun P x hP hx => fV_law _ _ hP hx) (fun P hP => modulus_characters_product _ _ hP) Kg μ ι hι hK
    (LR (blkA j) 1) (LQ (blkB j) 1) (by
      intro T T' S S'
      simp only [LR_apply, LQ_apply, one_mul]
      rw [add_comm (WD 0 _), add_comm (WD 0 _), ← WD_add, ← WD_add, add_zero, zero_add, add_zero, zero_add]
      exact WD_mul_WD_B_A j T S T' S')
  have e1 : ∀ (k : Kg) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      ι k * 1 + LR (blkA j) (ι k * 1) T + LQ (blkB j) (ι k * 1) S = ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S := by
    intro k T S
    simp only [LR_apply, LQ_apply, mul_one, one_mul]
  simp only [e1] at hzero
  rw [htr] at hzero
  have e2 : ∀ (y : M2 n) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      y + y * LR (blkA j) 1 T + y * LQ (blkB j) 1 S = y * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1 := by
    intro y T S
    rw [mX_eq, WD_split, LR_apply, LQ_apply, one_mul, one_mul, mul_add, mul_add, mul_one, add_assoc, add_comm (y * WD 0 _)]
  simp only [e2] at hzero
  have hc : (∫ k, hF j (p:ℤ) (q:ℤ) (ι k) * (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      fV (p:ℤ) (q:ℤ) (ι k * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) ∂μ) =
      ∫ k, ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) *
        (minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ *
          (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k)))) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [hDp n j p q (ι k) hjn (hGk k)]
    have h1 := scalar_section_mul_conjugate_section (hKk k) (p:ℤ) (q:ℤ)
    unfold hF
    linear_combination ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) *
        (minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ *
          (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k)))) * h1
  rw [hc, integral_const_mul] at hzero
  exact integral_minorOn_wM_ne_zero j Kg μ ι hι hK
    ((mul_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left (pow_ne_zero _ (by norm_num)))).resolve_left hC')

end PositivityTheory.Rg.Sw.LVs

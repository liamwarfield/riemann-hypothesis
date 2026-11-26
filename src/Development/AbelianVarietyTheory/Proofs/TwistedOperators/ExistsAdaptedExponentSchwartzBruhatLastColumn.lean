module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.AdaptedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_pow_le {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le

theorem eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by
  have key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹ := by
    intro s
    filter_upwards [eventually_pow_le h s⁻¹] with e he x hx
    have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
    have he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := by
      rw [pos_iff_ne_zero]; simp
    simp only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢
    exact hx.trans ((le_inv_comm₀ he0 hs).1 he)
  refine hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹)
    (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ht.mono fun e he => hst.trans he
  · intro s t hs ht
    filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2
  · intro x _
    by_cases hx : x = 0
    · subst hx
      exact ⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩
    · exact ⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds
        ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩

variable {n n' : Type}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem withCol_add (x₀ : Matrix n n' k) (y z : n → k) :
    withCol x₀ (y + z) = withCol x₀ y + withCol (0 : Matrix n n' k) z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [withCol]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_withCol_zero :
    Continuous fun z : n → k => withCol (0 : Matrix n n' k) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose s hs using fun i => exists_cball_subset (ht i)
  filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz
  exact hsub fun i _ => hs i (le_trans (hz i) (he i))

theorem eventually_adapted [Fintype n] [Fintype n'] {ϖ : kˣ} (h : IsUnif ϖ)
    {Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ (x₀ : Matrix n n' k) (y : n → k),
      (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧
        ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) ''
        tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹ := fun r =>
    eventually_subset_cball h (hc.image (by fun_prop))
  have h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [withCol]
  have h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k) :=
    (hΛ.preimage continuous_withCol_zero).mem_nhds (by
      simp only [Set.mem_preimage, h0]; exact Λ.zero_mem)
  filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y
  refine ⟨fun hne r => ?_, fun z hz => ?_⟩
  · exact he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩
  · rw [withCol_add]
    exact hinv _ _ (he2 z hz)

theorem exists_adapted_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  intro k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h
  exact ((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2
    fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists

end GlobalTheory.AdaptedExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumnStatement
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  first | exact @GlobalTheory.AdaptedExp.exists_adapted_exponent | exact GlobalTheory.AdaptedExp.exists_adapted_exponent | (intros; apply GlobalTheory.AdaptedExp.exists_adapted_exponent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistSupportPeriodicLevels
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.Proof.TwistSupportPeriodicLevels

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_latOf_eq {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by
  have h1 := latOf_le_iff.mp h.le
  have h2 := latOf_le_iff.mp h.ge
  simp only [inv_one, one_mul, mul_one] at h1 h2
  exact mem_KO.mpr ⟨h1, h2⟩

variable {r s s' : Type} [Fintype r] [DecidableEq r]

theorem intM_of_parPhi_ne_zero (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  rw [← Matrix.fromBlocks_toBlocks x, intM_fromBlocks]
  refine ⟨?_, h12, h21.intM, h22⟩
  rw [← e]
  exact intM_of_mem_KO hg

private theorem parPhi_add_eq_of_maxM {δ : kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) (hx : parPhi δ x ≠ 0) : parPhi δ (x + y) = parPhi δ x := by

  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  have hyb : MaxM (Matrix.fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ y.toBlocks₂₂) := by
    rwa [Matrix.fromBlocks_toBlocks]
  obtain ⟨hy11, hy12, hy21, hy22⟩ := maxM_fromBlocks.mp hyb
  have a11 : (x + y).toBlocks₁₁ = x.toBlocks₁₁ + y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
  have a12 : (x + y).toBlocks₁₂ = x.toBlocks₁₂ + y.toBlocks₁₂ := Matrix.ext fun _ _ => rfl
  have a21 : (x + y).toBlocks₂₁ = x.toBlocks₂₁ + y.toBlocks₂₁ := Matrix.ext fun _ _ => rfl
  have a22 : (x + y).toBlocks₂₂ = x.toBlocks₂₂ + y.toBlocks₂₂ := Matrix.ext fun _ _ => rfl
  have hM : MaxM ((x + y).toBlocks₁₁ - g.val) := by
    rw [a11, ← e]
    simpa using hy11
  obtain ⟨u, hu, hgu⟩ := exists_mul_KOne hg hM
  have k21 : MaxM (x + y).toBlocks₂₁ := by rw [a21]; exact h21.add hy21
  have k12 : IntM (x + y).toBlocks₁₂ := by rw [a12]; exact h12.add hy12.intM
  have k22 : IntM (x + y).toBlocks₂₂ := by rw [a22]; exact h22.add hy22.intM
  rw [parPhi_of_mem δ (mul_mem hg (KOne_le_KO hu)) hgu k21 k12 k22, parPhi_of_mem δ hg e h21 h12 h22]
  simp only [map_mul, tame_det_of_mem_KOne hδ hu, mul_one]

open Classical in
theorem parPhi_add {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (x : Matrix (r ⊕ s) (r ⊕ s') k) {y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) : parPhi δ (x + y) = parPhi δ x := by
  by_cases hx : parPhi δ x = 0
  · by_contra hne
    have hxy : parPhi δ (x + y) ≠ 0 := fun h0 => hne (h0.trans hx.symm)
    have back := parPhi_add_eq_of_maxM hδ hy.neg hxy
    rw [add_neg_cancel_right] at back
    exact hxy (back.symm.trans hx)
  · exact parPhi_add_eq_of_maxM hδ hy hx

variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem intM_of_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by
  have hM : IntM ((F.bas⁻¹).val * x * F'.bas.val) := fun a b => by
    have := h (F.ord.symm a) (F'.ord.symm b)
    simp only [LatFrame.coords, Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    exact this
  have hx : F.bas.val * ((F.bas⁻¹).val * x * F'.bas.val) * (F'.bas⁻¹).val = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [← hx]
  exact ((intM_of_mem_KO hF).mul hM).mul (mem_KO.mp hF').2

theorem maxM_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {y : Matrix Y Y' k} (h : MaxM y) : MaxM (F.coords F' y) := by
  have hM : MaxM ((F.bas⁻¹).val * y * F'.bas.val) :=
    ((mem_KO.mp hF).2.mul_maxM h).mul_intM (intM_of_mem_KO hF')
  show MaxM (((F.bas⁻¹).val * y * F'.bas.val).submatrix F.ord F'.ord)
  exact fun i j => hM (F.ord i) (F'.ord j)

theorem coords_add (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x y : Matrix Y Y' k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp

theorem stabLat_le_KO {g : GL Y k} (hg : g ∈ KO k Y) : stabLat g ≤ KO k Y := by
  intro a ha
  have hc := mem_stabLat.mp ha
  have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hg hc) (inv_mem hg)

private theorem transport_parPhi_add_eq_of_maxM [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'] {δ : kˣ →* ℂˣ}
    (hδ : IsTame δ) {F : LatFrame k (r ⊕ s) Y} {F' : LatFrame k (r ⊕ s') Y'} (hF : F.bas ∈ KO k Y)
    (hF' : F'.bas ∈ KO k Y') (x : Matrix Y Y' k) {y : Matrix Y Y' k} (hy : MaxM y) :
    F.transport F' (parPhi δ) (x + y) = F.transport F' (parPhi δ) x := by
  show parPhi δ (F.coords F' (x + y)) = parPhi δ (F.coords F' x)
  rw [coords_add]
  exact parPhi_add hδ _ (maxM_coords hF hF' hy)

end

theorem ofTwist_support_periodic_levels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by
  intro k _ _ _ _ s r t Z _ _ _ _ _ _ X _ _ δ hδ μ₀ F Ftop hF
  have hK : ∀ j c h, (F j c h).bas ∈ KO k (X j ⊕ Fin c) := fun j c h => mem_KO_of_latOf_eq (hF j c h)
  refine ⟨fun j c h x hx => ?_, fun j c h x y hy => ?_, fun j c h => ?_⟩
  · exact intM_of_coords (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) (intM_of_parPhi_ne_zero δ hx)
  · exact transport_parPhi_add_eq_of_maxM hδ (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) x hy
  · exact ((TypeDatum.map_conj (parahoric r (Fin j × t) δ hδ) (F j c h)).2.2).trans (stabLat_le_KO (hK j c h))

end GlobalTheory.Proof.TwistSupportPeriodicLevels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFn
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetQuotInt

theorem _root_.GlobalTheory.CosetQuotInt.isQuotInt_cosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J)
    (h : GL (n ⊕ Fin c) k)
    (m : Measure (GL n k)) (v : ℝ) (hv : v ≠ 0)
    (hvol : ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g,
      (∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
      (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
        (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
          (u₀ * _root_.GlobalTheory.RootEx.embX c g₀))
          ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m
          = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * v : ℝ) : ℂ))
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ)
    (hf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn J h f) :
    _root_.GlobalTheory.RootEx.IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  classical
  haveI : BorelSpace (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).1
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).2.2.1
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO at hJ
  obtain ⟨hJo, hJc⟩ := hJ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn at hf
  obtain ⟨hleft, hright, hsupp⟩ := hf
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv
  have hembP : ∀ g : GL n k,
      _root_.GlobalTheory.RootEx.embX c g ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro g
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_left ⟨g, rfl⟩
  have hNP : ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c 1,
      u ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro u hu
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_right hu
  obtain ⟨F, hFdef⟩ : ∃ F : GL (n ⊕ Fin c) k → ℂ,
      ∀ x, F x = if h⁻¹ * x ∈ J then f h / (v : ℂ) else 0 := ⟨_, fun _ => rfl⟩
  unfold _root_.GlobalTheory.RootEx.IsQuotInt
  refine ⟨F, ?_, fun x => ?_, ?_⟩
  · have hSB := _root_.GlobalTheory.QuotInt.sb_of_quot J hJo hJc
      {(h : GL (n ⊕ Fin c) k ⧸ J)}
      (fun q => if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0)
      (fun q hq => by
        simp only [Finset.mem_singleton] at hq
        simp [hq])
    have hFq : F = fun y : GL (n ⊕ Fin c) k => (fun q : GL (n ⊕ Fin c) k ⧸ J =>
        if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0) (y : GL (n ⊕ Fin c) k ⧸ J) := by
      funext y
      rw [hFdef]
      dsimp only
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, if_pos (QuotientGroup.eq.2 hy).symm]
      · rw [if_neg hy, if_neg (fun (he : (y : GL (n ⊕ Fin c) k ⧸ J) = h) =>
          hy (QuotientGroup.eq.1 he.symm))]
    rw [hFq]
    exact hSB
  · by_cases hx : DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J h =
        DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J x
    · obtain ⟨p, hp, j, hj, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hx
      obtain ⟨x₀, u', hu', rfl⟩ := _root_.GlobalTheory.RootEx.VolN.exists_of_mem_R hp
      obtain ⟨u₀, hu₀, hpeq⟩ : ∃ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1,
          _root_.GlobalTheory.RootEx.embX c x₀ * u' = u₀ * _root_.GlobalTheory.RootEx.embX c x₀ :=
        ⟨_, _root_.GlobalTheory.RootEx.Radical.conj_mem x₀ hu', by group⟩
      rw [hpeq, hright _ j hj, hleft u₀ hu₀ x₀ h]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
          f h / (v : ℂ) * (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) := by
        intro g u
        have hyP : _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀) ∈ _root_.GlobalTheory.RootEx.R k n c 1 :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hembP g) (hNP _ u.2))
            (Subgroup.mul_mem _ (hNP _ hu₀) (hembP x₀))
        have hiff : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) ∈ J ↔
            h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J := by
          have heq : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
              h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h * j := by group
          rw [heq, J.mul_mem_cancel_right hj]
        rw [hFdef]
        by_cases hin : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J
        · rw [if_pos (hiff.2 hin), Set.indicator_of_mem
            (show _ ∈ _root_.GlobalTheory.StepData.Cgrp J h from
              _root_.GlobalTheory.StepData.mem_Cgrp.2 ⟨hyP, hin⟩), mul_one]
        · rw [if_neg (fun h' => hin (hiff.1 h')), Set.indicator_of_notMem
            (show _ ∉ _root_.GlobalTheory.StepData.Cgrp J h from
              fun h' => hin (_root_.GlobalTheory.StepData.mem_Cgrp.1 h').2), mul_zero]
      simp_rw [hpt, integral_const_mul]
      rw [hvol u₀ hu₀ x₀]
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR
      rw [Complex.ofReal_mul, div_mul_eq_mul_div, eq_div_iff hv']
      ring
    · have hfx : f x = 0 := hsupp x (fun he => hx he.symm)
      rw [hfx]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        rw [hFdef, if_neg]
        intro hmem
        apply hx
        refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(_root_.GlobalTheory.RootEx.embX c g *
          (u : GL (n ⊕ Fin c) k))⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ (hembP g)
            (hNP _ u.2)), h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x),
          hmem, by group⟩
      simp_rw [hpt, integral_zero]
  · have hFind : F = ((fun y => h⁻¹ * y) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))).indicator
        (fun _ => f h / (v : ℂ)) := by
      funext y
      rw [hFdef]
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
      · rw [if_neg hy,
          Set.indicator_of_notMem (show y ∉ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
    rw [hFind, integral_indicator_const _
      (hJo.measurableSet.preimage (measurable_const_mul h⁻¹)), measureReal_def,
      measure_preimage_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CosetQuotInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFnStatement
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuotInt_cosetFn_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) (v : ℝ), v ≠ 0 → (∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * v : ℝ) : ℂ)) → ∀ (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), IsCosetFn J h f → IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  first | exact @GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | exact GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | (intros; apply GlobalTheory.CosetQuotInt.isQuotInt_cosetFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicator
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.StepAvg

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

private lemma measurableSet_Cgrp_of_isCO {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k) :
    MeasurableSet (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
  have hJ' : IsOpen (J : Set (GL (n ⊕ Fin c) k)) ∧ IsCompact (J : Set (GL (n ⊕ Fin c) k)) := hJ
  have hset : (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      (_root_.GlobalTheory.RootEx.R k n c 1 : Set (GL (n ⊕ Fin c) k)) ∩
        (fun x => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k)) := by
    ext x
    exact _root_.GlobalTheory.StepData.mem_Cgrp
  have hopen : IsOpen ((fun x : GL (n ⊕ Fin c) k => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))) :=
    hJ'.1.preimage (by fun_prop)
  rw [hset]
  exact (_root_.GlobalTheory.RootEx.VolN.isClosed_R 1).measurableSet.inter hopen.measurableSet

private lemma integral_indicator_embed_mul_unipotent_lemma (ν : Measure k) [ν.IsAddHaarMeasure]
    {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k)
    (x : GL n k) :
    ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k))
        ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
      (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)).indicator
        (fun _ => (((_root_.GlobalTheory.RootEx.volN ν n c 1)
          ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal
            : ℂ)) x := by
  haveI := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN (c := c) (n := n) ν 1
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  by_cases hx : x ∈ _root_.GlobalTheory.StepData.prX C
  · obtain ⟨u₁, hu₁N, hu₁C⟩ := _root_.GlobalTheory.StepData.mem_prX.mp hx
    let w : _root_.GlobalTheory.RootEx.N k n c 1 :=
      ⟨E x⁻¹ * u₁⁻¹ * (E x⁻¹)⁻¹, _root_.GlobalTheory.RootEx.Radical.conj_mem x⁻¹
        (Subgroup.inv_mem _ hu₁N)⟩
    have key : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E x * (u : GL (n ⊕ Fin c) k)) =
          ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) (w * u) := by
      intro u
      have hwu : ((w * u : _root_.GlobalTheory.RootEx.N k n c 1) : GL (n ⊕ Fin c) k) =
          (u₁ * E x)⁻¹ * (E x * u) := by
        simp only [w, Subgroup.coe_mul, map_inv, inv_inv, _root_.mul_inv_rev, mul_assoc]
      have hiff : E x * (u : GL (n ⊕ Fin c) k) ∈ C ↔
          w * u ∈ C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) := by
        rw [Subgroup.mem_subgroupOf, hwu, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hu₁C)]
      by_cases hu : E x * (u : GL (n ⊕ Fin c) k) ∈ C
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show w * u ∈ _ from hiff.mp hu)]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show w * u ∉ ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))) from fun h' => hu (hiff.mpr h'))]
    have hmeas : MeasurableSet ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))) :=
      measurable_subtype_coe (measurableSet_Cgrp_of_isCO hJ h)
    simp_rw [key]
    rw [integral_mul_left_eq_self (fun u => ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) u) w,
      integral_indicator_const _ hmeas, Set.indicator_of_mem hx, measureReal_def, Complex.real_smul,
      mul_one]
  · rw [Set.indicator_of_notMem hx]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    refine Set.indicator_of_notMem (fun hu => hx ?_) _
    refine _root_.GlobalTheory.StepData.mem_prX.mpr ⟨E x * u * (E x)⁻¹,
      _root_.GlobalTheory.RootEx.Radical.conj_mem x u.2, ?_⟩
    convert hu using 1
    simp [E]

theorem _root_.GlobalTheory.StepAvg.integral_translate_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J → ∀ (h : GL (n ⊕ Fin c) k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : _root_.GlobalTheory.RootEx.N k n c 1, (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * _root_.GlobalTheory.RootEx.embX c g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * ((_root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal * (m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h))).toReal) : ℝ) : ℂ) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c hc J hJ h hpr m _ u₀ hu₀ g₀
  haveI := _root_.GlobalTheory.RootEx.VolN.isMulRightInvariant_volN (c := c) (n := n) ν 1
  haveI := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar (k := k) m
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set V : ℂ := (((_root_.GlobalTheory.RootEx.volN ν n c 1)
    (C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal : ℂ)
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
      (_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← _root_.GlobalTheory.SplitWeil.nabs_mul, ← map_mul, inv_mul_cancel, map_one,
      _root_.GlobalTheory.SplitWeil.nabs_one]
  have hpos := _root_.GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g₀)
  have ha0 : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^
      (-((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ))) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ := by
    rw [hinv, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv,
      show ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) = (((c : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
    rfl
  have inner : ∀ g : GL n k,
      ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
          (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
            (E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ •
          (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) (g * g₀) := by
    intro g
    have e1 : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀) =
          E (g * g₀) * (E g₀⁻¹ * ((u * ⟨u₀, hu₀⟩ : _root_.GlobalTheory.RootEx.N k n c 1) :
            GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹) := by
      intro u
      simp only [map_mul, map_inv, inv_inv, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
    simp_rw [e1]
    rw [integral_mul_right_eq_self (fun u : _root_.GlobalTheory.RootEx.N k n c 1 =>
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (E (g * g₀) * (E g₀⁻¹ * (u : GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹))) ⟨u₀, hu₀⟩,
      _root_.GlobalTheory.RootEx.VolN.integral_conj_volN ν le_rfl hc g₀⁻¹
        (fun y => (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E (g * g₀) * y)),
      integral_indicator_embed_mul_unipotent_lemma ν hJ h (g * g₀), ha0]
    all_goals simp only [C, V]
  have hpr' : IsOpen (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) ∧
      IsCompact (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr
  have hborel := (_root_.GlobalTheory.SplitWeil.volGL_haar k n ν).1
  have hmeas : MeasurableSet (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr'.1.measurableSet

  simp_rw [inner]
  rw [integral_smul, integral_mul_right_eq_self (fun g : GL n k =>
      (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) g) g₀,
    integral_indicator_const _ hmeas, measureReal_def]
  simp only [V, Complex.real_smul]
  push_cast
  ring
end

end GlobalTheory.StepAvg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicatorStatement
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_indicator_Cgrp_translate_eq_deltaR_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k), IsCO (prX (Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * ((volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1))).toReal * (m (prX (Cgrp J h))).toReal) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.StepAvg.integral_translate_indicator | exact GlobalTheory.StepAvg.integral_translate_indicator | (intros; apply GlobalTheory.StepAvg.integral_translate_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemNormalizerOfTri
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal

noncomputable section
namespace GlobalTheory.RootEx.ConjVol

section Abstract
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cj (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) : U ≃ₜ* U where
  toMulEquiv := U.normalizerMonoidHom g
  continuous_toFun := Continuous.subtype_mk
    (f := fun u : U => (g : G) * u * (g : G)⁻¹) (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk
    (f := fun u : U => ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G) * u *
      ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G)⁻¹) (by fun_prop) _

theorem cj_coe (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) (u : U) :
    (cj U g u : G) = g * u * (g : G)⁻¹ := rfl

variable (U : Subgroup G) [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U]

def md : Subgroup.normalizer (U : Set G) →* ℝ≥0 where
  toFun g := mulEquivHaarChar (cj U g)
  map_one' := by
    have : cj U 1 = ContinuousMulEquiv.refl U := by ext u; simp [cj_coe]
    simp only [this, mulEquivHaarChar_refl]
  map_mul' a b := by
    have : cj U (a * b) = (cj U b).trans (cj U a) := by ext u; simp [cj_coe, mul_assoc]
    simp only [this, mulEquivHaarChar_trans, mul_comm]

theorem md_ne_zero (g : Subgroup.normalizer (U : Set G)) : md U g ≠ 0 := (mulEquivHaarChar_pos _).ne'

theorem md_conj (x g : Subgroup.normalizer (U : Set G)) : md U (x * g * x⁻¹) = md U g := by
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem integral_conj_of_md (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular]
    (g : Subgroup.normalizer (U : Set G)) (hg : md U g = 1) (f : G → ℂ) :
    ∫ u : U, f (g * (u : G) * (g : G)⁻¹) ∂μ = ∫ u : U, f u ∂μ := by
  have h := mulEquivHaarChar_smul_map μ (cj U g)
  rw [show mulEquivHaarChar (cj U g) = 1 from hg, one_smul] at h
  have h3 := integral_map_equiv (μ := μ) (cj U g).toHomeomorph.toMeasurableEquiv (fun u : U => f u)
  rw [show ⇑(cj U g).toHomeomorph.toMeasurableEquiv = ⇑(cj U g) from rfl, h] at h3
  exact h3.symm

end Abstract

section Alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem conj_mem_of_tri {p : ℕ} {g u : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) (hu : u ∈ N k n c p) : g * u * g⁻¹ ∈ N k n c p := by
  rw [Model.mem_N_iff] at hu ⊢
  intro r s hrs
  have e : (g * u * g⁻¹).val = 1 + g.val * (u.val - 1) * (g⁻¹).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, add_eq_left, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lev p s < lev p t
  · rw [hg' ht, mul_zero]
  rw [Matrix.mul_apply]
  refine mul_eq_zero_of_left (Finset.sum_eq_zero fun v _ => ?_) _
  by_cases hv : lev p v < lev p r
  · rw [hg hv, zero_mul]
  rw [Matrix.sub_apply, hu v t (by omega), sub_self, mul_zero]

theorem mem_normalizer_of_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) :
    g ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun u => ⟨conj_mem_of_tri hg hg', fun h => ?_⟩
  have := conj_mem_of_tri hg' (by rwa [inv_inv]) h
  simpa [mul_assoc] using this

theorem embX_tri (p : ℕ) (x : GL n k) : (embX c x).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · simp [VolN.val_embX]
  · simp [VolN.val_embX]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [VolN.val_embX, this]

theorem colE_tri (p : ℕ) (β : n → k) : (colE c p β).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · have : s.val + 1 ≠ p := by simp [lev] at h; omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [colE, upU, this]

theorem embX_mem (p : ℕ) (x : GL n k) :
    embX c x ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (embX_tri p x) (by rw [← map_inv]; exact embX_tri p _)

theorem colE_mem (p : ℕ) (β : n → k) :
    colE c p β ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (colE_tri p β) (by
    rw [inv_eq_of_mul_eq_one_right (QuotStep.colE_neg p β)]; exact colE_tri p _)

theorem colE_add (p : ℕ) (u w : n → k) : colE c p (u + w) = colE c p u * colE c p w := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = p <;> simp [h, add_comm]

end Alg

section Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_ne_zero_one [ValuativeRel.IsNontrivial k] : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
  obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
  obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
  exact ⟨a, by rintro rfl; simp at h0, by rintro rfl; simp at h1⟩

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem integral_conj_colE' (p : ℕ) (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (colE c p β * (u : GL (n ⊕ Fin c) k) * (colE c p β)⁻¹) ∂(volN ν n c p) =
      ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (N k n c p) := (VolN.isClosed_N p).locallyCompactSpace
  haveI := VolN.isHaarMeasure_volN (n := n) (c := c) ν p
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  let E : (n → k) → Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := fun b => ⟨_, colE_mem p b⟩
  have hs : ∀ a : k, a ≠ 0 → md (N k n c p) (E (a • β)) = md (N k n c p) (E β) := fun a ha => by
    let x : GL n k := Matrix.GeneralLinearGroup.scalar n (Units.mk0 a ha)
    rw [← md_conj (N k n c p) ⟨_, embX_mem p x⟩ (E β)]
    congr 1
    apply Subtype.ext
    refine Eq.trans ?_ (QuotStep.conj_colE p x β).symm
    change colE c p (a • β) = _
    congr 1
    funext i
    simp [x, Matrix.mulVec_diagonal]
  obtain ⟨a, h0, h1⟩ := exists_ne_zero_one (k := k)
  have e : E β = E (a • β) * E ((1 - a) • β) := by
    apply Subtype.ext
    change colE c p β = colE c p (a • β) * colE c p ((1 - a) • β)
    rw [← colE_add, ← add_smul, add_sub_cancel, one_smul]
  have h := congrArg (md (N k n c p)) e
  rw [map_mul, hs a h0, hs _ (sub_ne_zero.2 h1.symm)] at h
  exact integral_conj_of_md (N k n c p) _ (E β)
    (mul_left_cancel₀ (md_ne_zero _ (E β)) (h.symm.trans (mul_one _).symm)) f

end Meas

theorem integral_conj_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c (ρ + 1), f (colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹) ∂(volN ν n c (ρ + 1)) = ∫ u : N k n c (ρ + 1), f u ∂(volN ν n c (ρ + 1)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ ρ _ _ ν _ β f => integral_conj_colE' ν (ρ + 1) β f

end GlobalTheory.RootEx.ConjVol
end
end

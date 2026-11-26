module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFhyp
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HyperbolicTermsContribution

open UpperTheory.Esk

theorem vecMul_ne {F : Type} [Field F] (s : Fin 2 → F) (hs : s ≠ 0) (δ : GL (Fin 2) F) : s ᵥ* δ.val ≠ 0 := by
  intro h
  apply hs
  have h2 := congrArg (fun v => v ᵥ* (δ⁻¹ : GL (Fin 2) F).val) h
  simpa [Matrix.vecMul_vecMul] using h2

theorem isEll_conj {F : Type} [Field F]
    (hfix : ∀ (s : Fin 2 → F) (γ δ : GL (Fin 2) F), Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔
      ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val)) (g γ : PG F) :
    IsEll (g * γ * g⁻¹) ↔ IsEll γ := by
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective γ
  have h1 : ∀ s : Fin 2 → F, Fix s (γ : PG F) ↔ ∃ c : F, s ᵥ* γ.val = c • s := by
    intro s
    have := hfix s γ 1
    simpa using this
  constructor
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (h1 s).1 hf
    have hs' : s ᵥ* (δ⁻¹ : GL (Fin 2) F).val ≠ 0 := vecMul_ne s hs _
    apply h _ hs'
    rw [hfix]
    refine ⟨c, ?_⟩
    have e : (s ᵥ* (δ⁻¹ : GL (Fin 2) F).val) ᵥ* δ.val = s := by
      rw [Matrix.vecMul_vecMul]; simp
    rw [e, hc]
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (hfix s γ δ).1 hf
    exact h _ (vecMul_ne s hs δ) ((h1 _).2 ⟨c, hc⟩)

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

open scoped Classical in
open Classical in
def uT (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) : ℂ :=
  if IsEll γ then 0 else (D.LamF T γ).indicator (D.kk k a γ) y

theorem enorm_uT_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖uT D k a T γ y‖ₑ ≤ ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ := by
  unfold uT
  split_ifs <;> simp

theorem enorm_ind_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ ≤ ‖D.kk k a γ y‖ₑ := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

open scoped Classical in
open Classical in
theorem fhyp (hC4 : C4) (hE0a : E0a) (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hE2 : E2) (hE3 : E3) (hEcut : Ecut)
    (hFsum : Fsum) (hF5 : F5) (hF6 : F6) (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a)
    (b : D.Y → ℝ) (hb : IsCut (PG F) b)
    (hint : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY) :
    ∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY = 0 := by
  have hax := hyp.ax
  obtain ⟨hcnt, hsf, hpres, -, -, -, -, -⟩ := hE0a F I Gf D hax
  obtain ⟨-, hkkc, hkkm, -, -, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨-, -, -, -, -, -, -, hLamF, hev, -, hfix⟩ := hE0d F I Gf D hax
  obtain ⟨-, hE2'⟩ := hE2 F I Gf ι D k a hyp
  have hb3 := hE3 F I Gf D hax b hb
  obtain ⟨-, hcut⟩ := hEcut F I Gf D hax
  obtain ⟨C, hC⟩ := hF5 F I Gf ι D k a hyp
  have hF6' := hF6 F I Gf ι D k a hyp
  have : Countable (PG F) := hcnt
  have : Countable D.Cj := hcnt
  have : Countable D.Om := hax.cO

  have hbI : Integrable b D.μY := by
    refine ⟨hb.meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hb3
    refine lintegral_congr fun y => ?_
    exact Real.enorm_eq_ofReal (hb.nonneg y)

  have hum : ∀ T γ, Measurable (uT D k a T γ) := by
    intro T γ
    by_cases h : IsEll γ
    · unfold uT; simp only [h, if_true]; exact measurable_const
    · unfold uT; simp only [h, if_false]; exact (hkkm γ).indicator (hLamF T γ).1

  have hsumle : ∀ T : ℝ, 1 < T → ∀ y, y ∉ D.abelian₂ T → ∑' γ, ‖uT D k a T γ y‖ₑ ≤ C := by
    intro T hT y hy
    exact le_trans (ENNReal.tsum_le_tsum fun γ => enorm_uT_le D k a T γ y) ((hC T hT y).2 hy)
  have hon : ∀ T : ℝ, 1 < T → ∀ y, y ∈ D.abelian₂ T → ∀ γ, uT D k a T γ y = if IsEll γ then 0 else D.kk k a γ y := by
    intro T hT y hy γ
    unfold uT
    split_ifs
    · rfl
    · exact Set.indicator_of_mem ((hC T hT y).1 hy γ) _

  have hinv : ∀ T (g γ : PG F) (y : D.Y), uT D k a T (g * γ * g⁻¹) (g • y) = uT D k a T γ y := by
    intro T g γ y
    unfold uT
    rw [isEll_conj hfix g γ]
    split_ifs
    · rfl
    · rw [Set.indicator_apply, Set.indicator_apply, hkkc]
      simp only [(hLamF T γ).2 g y]

  have step1 : ∀ T : ℝ, 1 < T → Integrable (fun y => b y • ∑' γ, uT D k a T γ y) D.μY ∧
      ∫ y, b y • ∑' γ, uT D k a T γ y ∂D.μY = 0 := by
    intro T hT
    obtain ⟨CT, hCT⟩ := hE2' T
    have hfin : ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY < ⊤ := by
      have hle : ∀ y, ∑' γ, ‖uT D k a T γ y‖ₑ ≤ (CT : ℝ≥0∞) + C := by
        intro y
        by_cases hy : y ∈ D.abelian₂ T
        · refine le_trans ?_ le_self_add
          refine le_trans (ENNReal.tsum_le_tsum fun γ => ?_) (hCT y hy)
          exact (enorm_uT_le D k a T γ y).trans (enorm_ind_le D k a T γ y)
        · exact (hsumle T hT y hy).trans le_add_self
      calc ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY
          ≤ ∫⁻ y, ENNReal.ofReal (b y) * ((CT : ℝ≥0∞) + C) ∂D.μY :=
            lintegral_mono fun y => by gcongr; exact hle y
        _ = (∫⁻ y, ENNReal.ofReal (b y) ∂D.μY) * ((CT : ℝ≥0∞) + C) :=
            lintegral_mul_const' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top hb3 (by simp)
    obtain ⟨hb', hFs⟩ := hFsum F I Gf D hax b hb
    obtain ⟨hm', hi', hiY, heq⟩ := hFs (uT D k a T) (hum T) hfin
    refine ⟨hiY, ?_⟩
    rw [heq]

    let R : Set (D.Cj × D.Om) := Set.range (fun q : MulAction.orbitRel.Quotient (PG F) (D.Cj × D.Om) => q.out)
    have hR : ∀ ω : D.Cj × D.Om, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit (PG F) ω := by
      intro ω
      refine ⟨(Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · exact (MulAction.orbitRel_apply).1 (Quotient.mk_out ω)
      · rintro r ⟨⟨q, rfl⟩, hq⟩
        have e1 : q = Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω := by
          rw [← Quotient.out_eq q]
          exact Quotient.sound ((MulAction.orbitRel_apply).2 hq)
        rw [e1]
    have hβ : ∀ r : D.Cj × D.Om, ∃ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) r) β := by
      intro r
      refine hcut r.2 _ ?_
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      have := congrArg Prod.snd hg
      simpa using this
    choose β hβ using hβ
    have hinv' : ∀ (g : PG F) (p : (D.Cj × D.Om) × D.Xs),
        uT D k a T (D.el (g • p).1.1) ((g • p).1.2, (g • p).2) = uT D k a T (D.el p.1.1) (p.1.2, p.2) := by
      intro g p
      have e : ((g • p).1.2, (g • p).2) = g • ((p.1.2, p.2) : D.Y) := rfl
      rw [e, show D.el (g • p).1.1 = g * D.el p.1.1 * g⁻¹ from D.smulC g p.1.1, hinv]
    obtain ⟨hI, hS⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres _ hb' _ hm' hinv' hi' R hR β (fun r _ => hβ r)
    have hz : ∀ r : R, ∫ x, β r x • uT D k a T (D.el r.1.1) (r.1.2, x) = 0 := by
      intro r
      by_cases he : IsEll (D.el r.1.1)
      · simp [uT, he]
      · have hI' := hI r.1 r.2
        simp only [uT, he, if_false] at hI' ⊢
        exact hF6' T hT (D.el r.1.1) r.1.2 he (β r.1) (hβ r.1) hI'
    have hS' := hS
    simp only [hz] at hS'
    exact (hS'.unique hasSum_zero)

  have hT2 : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) + 2 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  have hlim : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop
      (𝓝 (∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖b y • ∑' γ : PG F, (if IsEll γ then 0 else D.kk k a γ y)‖ + b y * C)
      (fun n => (step1 _ (hT2 n)).1.aestronglyMeasurable) (hint.norm.add (hbI.mul_const _)) ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hb.nonneg y), ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hb.nonneg y)
      by_cases hy : y ∈ D.abelian₂ ((n : ℝ) + 2)
      · rw [tsum_congr (hon _ hT y hy)]
        exact le_add_of_nonneg_right C.2
      · have h1 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ₑ ≤ C :=
          enorm_tsum_le_tsum_enorm.trans (hsumle _ hT y hy)
        have h2 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ ≤ C := by
          have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
          simpa using this
        exact h2.trans (le_add_of_nonneg_left (norm_nonneg _))
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨T₀, hT₀⟩ := hev y
      obtain ⟨N, hN⟩ := exists_nat_ge T₀
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      have hy : y ∈ D.abelian₂ ((n : ℝ) + 2) := hT₀ _ (by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      dsimp only
      rw [tsum_congr (hon _ hT y hy)]
  have h0 : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact ((step1 _ (hT2 n)).2).symm
  exact tendsto_nhds_unique hlim h0

end UpperTheory.Esk.HyperbolicTermsContribution

theorem UpperTheory.Esk.pf_Fhyp : UpperTheory.Esk.C4 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.E2 → UpperTheory.Esk.E3 → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fsum → UpperTheory.Esk.F5 → UpperTheory.Esk.F6 → UpperTheory.Esk.Fhyp := by
  intro hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 F I Gf ι _ _ _ _ D k a hyp b hb hint
  exact UpperTheory.Esk.HyperbolicTermsContribution.fhyp hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 D k a hyp b hb hint
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFell
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticFixedPointTerms

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I]

theorem fix_iff (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (s : Fin 2 → F) (γ δ : GL (Fin 2) F) :
    Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔ ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val) :=
  (hE F I Gf D hD).2.2.2.2.2.2.2.2.2.2 s γ δ

theorem fix_mk (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (s : Fin 2 → F) (γ : GL (Fin 2) F) :
    Fix s (γ : PG F) ↔ ∃ c : F, s ᵥ* γ.val = c • s := by
  have h := fix_iff D hD hE s γ 1
  simpa using h

theorem isEll_conj (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (γ δ : GL (Fin 2) F) :
    IsEll ((δ : PG F) * (γ : PG F) * (δ : PG F)⁻¹) ↔ IsEll (γ : PG F) := by
  simp only [IsEll, fix_iff D hD hE, fix_mk D hD hE]
  constructor
  · intro h t ht hc
    refine h (t ᵥ* (δ⁻¹).val) ?_ ?_
    · intro h0
      apply ht
      have := congrArg (· ᵥ* δ.val) h0
      simpa [Matrix.vecMul_vecMul] using this
    · simpa [Matrix.vecMul_vecMul] using hc
  · intro h s hs hc
    refine h (s ᵥ* δ.val) ?_ hc
    intro h0
    apply hs
    have := congrArg (· ᵥ* (δ⁻¹).val) h0
    simpa [Matrix.vecMul_vecMul] using this

theorem isEll_conj' (D : Dat F I Gf) (hD : D.Ax) (hE : E0d) (δ γ : PG F) :
    IsEll (δ * γ * δ⁻¹) ↔ IsEll γ := by
  have h := isEll_conj D hD hE γ.out δ.out
  have e1 : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have e2 : ((δ.out : GL (Fin 2) F) : PG F) = δ := Quotient.out_eq δ
  rwa [e1, e2] at h

theorem isEll_of_totEll (D : Dat F I Gf) [Nonempty I] (γ : PG F) (h : D.TotEll γ.out) : IsEll γ := by
  intro s hs ⟨c, hc⟩
  set M : Matrix (Fin 2) (Fin 2) F := γ.out.val with hM
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e0 e1
  have q0 : (c ^ 2 - M.trace * c + M.det) * s 0 = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    linear_combination (M 1 1 - c) * e0 - M 1 0 * e1
  have q1 : (c ^ 2 - M.trace * c + M.det) * s 1 = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    linear_combination (-M 0 1) * e0 + (M 0 0 - c) * e1
  have hq : c ^ 2 - M.trace * c + M.det = 0 := by
    by_contra hne
    apply hs
    funext i
    fin_cases i
    · simpa [hne] using q0
    · simpa [hne] using q1
  have key : (2 * c - M.trace) ^ 2 = M.trace ^ 2 - 4 * M.det := by linear_combination 4 * hq
  obtain ⟨v⟩ := ‹Nonempty I›
  have hv := h v
  have k2 := congrArg (D.σ v) key
  simp only [map_pow, map_sub, map_mul, map_ofNat] at k2
  rw [← hM] at hv
  nlinarith [sq_nonneg (2 * D.σ v c - D.σ v M.trace)]

theorem supp (D : Dat F I Gf) {ι : Type} [Fintype ι] (a : ι → Gf) (γ : PG F) (ω : D.Om)
    (h : D.Te a γ.out (D.rep ω) ≠ 0) : ∃ i, γ • ω = ((D.rep ω * a i : Gf) : Gf ⧸ D.H) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨i, ?_⟩
  have hm : (D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * D.rep ω * a i ∈ D.H := by
    by_contra hn
    exact hi (by simp [Dat.ee, hn])
  have e1 : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have e2 : (show D.Om from ((D.rep ω : Gf) : Gf ⧸ D.H)) = ω := Quotient.out_eq ω
  have h2 : γ • ω = ((D.j γ.out * D.rep ω : Gf) : Gf ⧸ D.H) := by
    have h3 := D.mk_smulO γ.out (D.rep ω)
    rw [e1, e2] at h3
    exact h3
  rw [h2]
  refine QuotientGroup.eq.2 ?_
  simpa [_root_.mul_inv_rev, mul_assoc] using hm

end UpperTheory.Esk.EllipticFixedPointTerms

namespace UpperTheory.Esk

open EllipticFixedPointTerms

theorem pf_Fell : UpperTheory.Esk.C4 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.E3 → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fsum → UpperTheory.Esk.F2 → UpperTheory.Esk.F3 → UpperTheory.Esk.F4 → UpperTheory.Esk.Fell := by
  intro hC4 hE0a hE0c hE0d hE1 hE3 hEcut hFsum hF2 hF3 hF4
  intro F I Gf _ _ _ D hD ι _ a
  classical
  haveI : Nonempty I := by have := hD.two; infer_instance

  obtain ⟨f, hf1, hf2⟩ : ∃ f : D.Cj × D.Om → D.Cj × D.Om, (∀ p, f p ∈ MulAction.orbit (PG F) p) ∧
      (∀ p q, q ∈ MulAction.orbit (PG F) p → f q = f p) :=
    ⟨fun p => Quotient.out (Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) p),
      fun p => MulAction.orbitRel_apply.1 (Quotient.mk_out p),
      fun p q h => congrArg Quotient.out (Quotient.sound (MulAction.orbitRel_apply.2 h))⟩
  have hff : ∀ p, f (f p) = f p := fun p => hf2 p (f p) (hf1 p)
  have hR : ∀ ω, ∃! r, r ∈ Set.range f ∧ r ∈ MulAction.orbit (PG F) ω := by
    intro ω
    refine ⟨f ω, ⟨⟨ω, rfl⟩, hf1 ω⟩, ?_⟩
    rintro r ⟨⟨p, rfl⟩, hr⟩
    rw [← hf2 ω (f p) hr, hff]
  choose Sa hSa using fun i => hF4 F I Gf D hD (a i)
  let Sset : Set (D.Cj × D.Om) := {p | p ∈ Set.range f ∧ D.TotEll (D.el p.1).out ∧
    D.Te a (D.el p.1).out (D.rep p.2) ≠ 0 ∧ Finite (MulAction.stabilizer (PG F) p)}
  have hSfin : Sset.Finite := by
    refine (Set.finite_iUnion fun i => (hSa i).1.image f).subset ?_
    rintro p ⟨⟨q, rfl⟩, htot, hte, -⟩
    obtain ⟨i, hi⟩ := supp D a (D.el (f q).1) (f q).2 hte
    obtain ⟨δ, hδ⟩ := (hSa i).2 (D.el (f q).1) (f q).2 htot hi
    refine Set.mem_iUnion.2 ⟨i, δ • f q, hδ, ?_⟩
    rw [hf2 (f q) (δ • f q) (MulAction.mem_orbit _ δ), hff]
  refine ⟨hSfin.toFinset, fun p hp => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hp
    exact ⟨hp.2.1, hp.2.2.2⟩
  intro k hk b hb
  have hc := hE0c F I Gf ι D k a hk
  let u : PG F → D.Y → ℂ := fun γ y => if IsEll γ then D.kk k a γ y else 0
  have hu_meas : ∀ γ, Measurable (u γ) := by
    intro γ
    by_cases h : IsEll γ
    · simp only [u, h, if_true]; exact hc.2.2.1 γ
    · simp only [u, h, if_false]; exact measurable_const
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hk c₀ hc₀
  have hbd : ∀ y, ∑' γ, ‖u γ y‖ₑ ≤ (C : ℝ≥0∞) := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmink y.2 (D.rep y.1)
    calc ∑' γ, ‖u γ y‖ₑ ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ :=
          ENNReal.summable.tsum_le_tsum (fun γ => by
            by_cases h : IsEll γ
            · have hm : γ ∈ {γ : PG F | ¬ Fix s γ} := h s hs
              simp only [u, h, if_true, Set.indicator_of_mem hm, le_refl]
            · simp [u, h]) ENNReal.summable
      _ = ∑' γ : {γ : PG F | ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
      _ ≤ C := hC y s hs hsy
  have hfin : ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY < ⊤ := by
    calc ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY ≤ ∫⁻ y, ENNReal.ofReal (b y) * (C : ℝ≥0∞) ∂D.μY :=
          lintegral_mono fun y => by gcongr; exact hbd y
      _ = (∫⁻ y, ENNReal.ofReal (b y) ∂D.μY) * C := lintegral_mul_const' _ _ ENNReal.coe_ne_top
      _ < ⊤ := ENNReal.mul_lt_top (hE3 F I Gf D hD b hb) ENNReal.coe_lt_top
  obtain ⟨hb', hFs⟩ := hFsum F I Gf D hD b hb
  obtain ⟨hmeas', hint', hintY, heq⟩ := hFs u hu_meas hfin
  refine ⟨hintY, heq.trans ?_⟩
  obtain ⟨hcount, hsig, hpres, -⟩ := hE0a F I Gf D hD
  haveI : Countable (PG F) := hcount
  haveI : Countable D.Cj := hcount
  haveI : Countable D.Om := hD.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : DiscreteMeasurableSpace (D.Cj × D.Om) := ⟨fun s => s.to_countable.measurableSet⟩
  have stab_le : ∀ p : D.Cj × D.Om, MulAction.stabilizer (PG F) p ≤ MulAction.stabilizer (PG F) p.2 := by
    intro p g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    exact congrArg Prod.snd hg
  choose β hβ using fun p : D.Cj × D.Om => (hEcut F I Gf D hD).2 p.2 (MulAction.stabilizer (PG F) p) (stab_le p)
  have hinv : ∀ (g : PG F) (y : (D.Cj × D.Om) × D.Xs),
      u (D.el (g • y).1.1) ((g • y).1.2, (g • y).2) = u (D.el y.1.1) (y.1.2, y.2) := by
    rintro g ⟨⟨γ, ω⟩, z⟩
    show u (g * D.el γ * g⁻¹) (g • ((ω, z) : D.Y)) = u (D.el γ) (ω, z)
    simp only [u, isEll_conj' D hD hE0d, hc.2.1]
  obtain ⟨hintR, hsum⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres (fun p => b (p.1.2, p.2)) hb'
    (fun p => u (D.el p.1.1) (p.1.2, p.2)) hmeas' hinv hint' (Set.range f) hR β (fun r _ => hβ r)
  let g' : D.Cj × D.Om → ℂ := fun r => ∫ x, β r x • u (D.el r.1) (r.2, x)
  let h' : D.Cj × D.Om → ℂ := fun p => (Nat.card (MulAction.stabilizer (PG F) p) : ℂ)⁻¹ *
    (D.Te a ((D.el p.1).out) (D.rep p.2) * D.orb k ((D.el p.1).out))
  have hind : (Set.range f).indicator g' = Sset.indicator h' := by
    funext p
    by_cases hpR : p ∈ Set.range f
    · rw [Set.indicator_of_mem hpR]
      obtain ⟨γ, ω⟩ := p
      have hI := hintR (γ, ω) hpR
      by_cases hS : (γ, ω) ∈ Sset
      · rw [Set.indicator_of_mem hS]
        obtain ⟨-, htot, hte, -⟩ := hS
        have hell := isEll_of_totEll D (D.el γ) htot
        have := (hF3 F I Gf ι D k a hk (D.el γ) ω htot hte).2 (β (γ, ω)) (hβ (γ, ω))
        simp only [g', u, hell, if_true]
        exact this
      · rw [Set.indicator_of_notMem hS]
        simp only [g', u]
        by_cases hell : IsEll (D.el γ)
        · simp only [hell, if_true]
          by_cases htot : D.TotEll (D.el γ).out
          · by_cases hte : D.Te a (D.el γ).out (D.rep ω) = 0
            · simp [Dat.kk, Dat.kt, hte]
            · exfalso
              exact hS ⟨hpR, htot, hte, (hF3 F I Gf ι D k a hk (D.el γ) ω htot hte).1⟩
          · refine hF2 F I Gf ι D k a hk (D.el γ) ω htot (β (γ, ω)) (hβ (γ, ω)) ?_
            have hI' := hI
            simp only [u, hell, if_true] at hI'
            exact hI'
        · simp [hell]
    · rw [Set.indicator_of_notMem hpR, Set.indicator_of_notMem (by exact fun h => hpR h.1)]
  have h1 : HasSum ((Set.range f).indicator g') (∫ y, (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2)) y •
      (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) y ∂(Measure.count.prod volume)) :=
    (hasSum_subtype_iff_indicator (f := g')).1 hsum
  rw [hind] at h1
  have h2 : HasSum (Sset.indicator h') (∑ p ∈ hSfin.toFinset, Sset.indicator h' p) :=
    hasSum_sum_of_ne_finset_zero fun p hp => Set.indicator_of_notMem (by simpa using hp) _
  have h3 : ∑ p ∈ hSfin.toFinset, Sset.indicator h' p = geo D k a hSfin.toFinset := by
    unfold geo
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Set.indicator_of_mem (by simpa using hp)]
  rw [← h3]
  exact h1.unique h2
end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelSeriesConvergesProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I]

theorem ht_e (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap; split_ifs <;> positivity

theorem Kap_nonneg (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem N_pos (z : X I) : 0 < ∏ v, |(z v).1.im| :=
  Finset.prod_pos fun v _ => abs_pos.2 (z v).2

theorem fix_of (γ : PG F) (h : γ.out 1 0 = 0) : Fix ![0, 1] γ := by
  refine ⟨γ.out 1 1, ?_⟩
  ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h]

theorem e_ne : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1

theorem kap_split (k : I → ℕ) (z w : X I) :
    Kap k z w = (Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) *
      ((∏ v, |(w v).1.im|) / ∏ v, |(z v).1.im|) ^ ((1 : ℝ) / 2) := by
  rw [← Finset.prod_div_distrib, ← Real.finsetProd_rpow _ _ (fun v _ => by positivity), mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
  intro v _
  have h1 := abs_pos.2 (z v).2
  have h2 := abs_pos.2 (w v).2
  rw [← Real.mul_rpow (by positivity) (by positivity),
    show |(z v).1.im| / |(w v).1.im| * (|(w v).1.im| / |(z v).1.im|) = 1 by field_simp, Real.one_rpow]

theorem ratio (hE0d : E0d) {ι : Type} [Fintype ι] (D : Dat F I Gf) (hax : D.Ax) (a : ι → Gf) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (y : D.Y) (γ : PG F) (i : ι), ¬ Fix ![0, 1] γ →
      γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H) →
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 ≤ C' * ∏ v, |(y.2 v).1.im| := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := hE0d F I Gf D hax
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  choose Cm hCm using fun i => hax.mul (a i)⁻¹
  refine ⟨∑ i, max (Cm i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun y γ i hγ hi => ?_⟩
  have hγ' : γ.out 1 0 ≠ 0 := fun h => hγ (fix_of γ h)
  have hy : D.HtY ![0, 1] y = (∏ v, |(y.2 v).1.im|) * D.hf ![0, 1] (D.rep y.1) := ht_e D y.2 (D.rep y.1)
  have hgy : D.HtY ![0, 1] (γ • y) =
      (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1 * a i) := by
    have : γ • y = (((D.rep y.1 * a i : Gf) : Gf ⧸ D.H), γ • y.2) := Prod.ext hi rfl
    rw [this]; exact (h1 _ he _ _).trans (ht_e D _ _)
  have hprod : D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y ≤ 1 := by
    have := h2 _ he γ.out y
    rw [QuotientGroup.out_eq'] at this
    rw [this, mul_comm]
    apply h5
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hγ'
  have hx : 0 < D.hf ![0, 1] (D.rep y.1) := hax.pos _ he _
  have hxa : 0 < D.hf ![0, 1] (D.rep y.1 * a i) := hax.pos _ he _
  have hmul : D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.hf ![0, 1] (D.rep y.1 * a i) := by
    simpa using hCm i _ he (D.rep y.1 * a i)
  have hCm0 : 0 ≤ Cm i := by nlinarith
  have hNg : 0 ≤ ∏ v, |((γ • y.2 : D.Xs) v).1.im| := Finset.prod_nonneg fun v _ => abs_nonneg _
  have hN := (N_pos y.2).le
  have hHt : 0 ≤ D.HtY ![0, 1] y := (h4 _ he y).le
  have hHg : 0 ≤ D.HtY ![0, 1] (γ • y) := (h4 _ he _).le
  have hCi : Cm i ≤ ∑ j, max (Cm j) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (Cm j) 0) (fun j _ => le_max_right (Cm j) 0) (Finset.mem_univ i))
  have e1 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.HtY ![0, 1] y ^ 2 =
      ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| := by
    rw [sq, hy]; ring
  have e2 : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.HtY ![0, 1] (γ • y) := by
    rw [hgy]; nlinarith [mul_le_mul_of_nonneg_left hmul hNg]
  rw [e1]
  calc ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im|
      ≤ (Cm i * D.HtY ![0, 1] (γ • y)) * D.HtY ![0, 1] y * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 hHt) hN
    _ = Cm i * (D.HtY ![0, 1] (γ • y) * D.HtY ![0, 1] y) * ∏ v, |(y.2 v).1.im| := by ring
    _ ≤ Cm i * 1 * ∏ v, |(y.2 v).1.im| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCm0) hN
    _ ≤ (∑ j, max (Cm j) 0) * ∏ v, |(y.2 v).1.im| := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hCi hN

theorem main (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hPack : Pack) (hMult : Mult) (hKI : KapInt)
    {ι : Type} [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ≥0, ∀ y : D.Y, c₀ ≤ D.HtY ![0, 1] y →
      ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤ C := by
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  obtain ⟨-, -, -, ⟨CE, hCE⟩, hTe, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨C', hC'0, hC'⟩ := ratio hE0d D hyp.ax a
  obtain ⟨Cp, hCp⟩ := hPack F I Gf D hyp.ax
  obtain ⟨CM, hCM⟩ := hMult F I Gf D hyp.ax (1 / 16) c₀ (by norm_num) hc₀
  obtain ⟨CK, A, hK⟩ := hKI I k hyp.four
  have hm : ∀ v, Measurable fun w : D.Xs => (w v).1.im := fun v =>
    Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v))
  refine ⟨(Fintype.card ι : ℝ≥0) * Cp * A * CK *
    Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)), fun y hy => ?_⟩
  have hHt : 0 < D.HtY ![0, 1] y := hc₀.trans_le hy
  set Ht := D.HtY ![0, 1] y with hHtdef
  set h : D.Xs → ℝ≥0∞ := fun w => ENNReal.ofReal (Kap k y.2 w * ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2))
    with hhdef
  set K : ℝ := max CE 0 * Real.sqrt C' / Ht with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤
      ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := by
    rintro ⟨γ, hγ⟩
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have : D.kk k a γ y = 0 := by simp [Dat.kk, Dat.kt, h0]
      simp [this]
    obtain ⟨i, hi⟩ := hTe γ y.1 h0
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ) (fun _ _ => bot_le) (Finset.mem_univ i))
    simp only [Set.indicator_of_mem (show γ ∈ {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)]
    rw [hhdef, ← ofReal_norm, ← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have hr := hC' y γ i hγ hi
    have hN := N_pos y.2
    have hsq : ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) ≤ Real.sqrt C' / Ht := by
      rw [← Real.sqrt_eq_rpow]
      have : (∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im| ≤ C' / Ht ^ 2 := by
        rw [div_le_div_iff₀ hN (by positivity)]; linarith
      calc Real.sqrt ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ≤ Real.sqrt (C' / Ht ^ 2) :=
            Real.sqrt_le_sqrt this
        _ = Real.sqrt C' / Ht := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hHt.le]
    have hX : 0 ≤ Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Kap_nonneg _ _ _) (Finset.prod_nonneg fun v _ => by positivity)
    calc ‖D.kk k a γ y‖ ≤ CE * Kap k y.2 (γ • y.2 : D.Xs) := hCE γ y
      _ ≤ max CE 0 * Kap k y.2 (γ • y.2 : D.Xs) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Kap_nonneg _ _ _)
      _ = max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            ((∏ v, |((γ • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2)) := by
          congr 1; exact kap_split k y.2 _
      _ ≤ max CE 0 * ((Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
            (Real.sqrt C' / Ht)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hX) (le_max_right _ _)
      _ = K * (Kap k y.2 (γ • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) := by
          rw [hKdef]; ring

  have hmeas : Measurable h :=
    ((hK y.2).1.mul (Finset.measurable_prod _ fun v _ =>
      (measurable_const.div (hm v).abs).pow_const _)).ennreal_ofReal
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' → h w ≤ A * h w' := by
    intro w w' hn
    have := ENNReal.ofReal_le_ofReal ((hK y.2).2.2.2 w w' hn).2
    rwa [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this
  obtain ⟨hfin, hcard⟩ := hCM y ![0, 1] he hy
  have hcard' : ((({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (max CM 0 * (1 + Ht)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hint : ∫⁻ w, h w ≤ CK := (hK y.2).2.2.1
  have hcos : ∀ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ ≤
      ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    calc ∑' γ : {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}, h (γ.1 • y.2)
        ≤ Cp * A * ({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℝ≥0∞) * ∫⁻ w, h w :=
          hCp y _ h A hmeas hA hfin
      _ ≤ Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK := by gcongr
  have hfinal : ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht)) ≤
      ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
    rw [← ENNReal.ofReal_mul hK0]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 + Ht) / Ht ≤ 1 + 1 / c₀ := by
      have := one_div_le_one_div_of_le hc₀ hy
      rw [add_div, div_self hHt.ne']; linarith
    have h2 : 0 ≤ max CE 0 * Real.sqrt C' * max CM 0 := by positivity
    calc K * (max CM 0 * (1 + Ht)) = max CE 0 * Real.sqrt C' * max CM 0 * ((1 + Ht) / Ht) := by
          rw [hKdef]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  calc ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ
      ≤ ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ.1 := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' γ : PG F, ∑ i, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ :=
        (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
    _ = ∑ i, ∑' γ : PG F, ({γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}).indicator
        (fun γ' => ENNReal.ofReal K * h (γ' • y.2)) γ := Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ i : ι, ENNReal.ofReal K * (Cp * A * ENNReal.ofReal (max CM 0 * (1 + Ht)) * CK) :=
        Finset.sum_le_sum fun i _ => hcos i
    _ = (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * (ENNReal.ofReal K * ENNReal.ofReal (max CM 0 * (1 + Ht))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * ENNReal.ofReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) := by
        gcongr
    _ = (((Fintype.card ι : ℝ≥0) * Cp * A * CK *
          Real.toNNReal (max CE 0 * Real.sqrt C' * max CM 0 * (1 + 1 / c₀)) : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal]; push_cast; ring

end UpperTheory.Esk.KernelSeriesConvergence

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_series_converges_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.E1 := by
  intro _ hE0c hE0d hPack hMult hKI F I Gf ι _ _ _ _ D k a hyp c₀ hc₀
  obtain ⟨C, hC⟩ := KernelSeriesConvergence.main hE0c hE0d hPack hMult hKI D k a hyp c₀ hc₀
  refine ⟨C, fun y s hs hy => ?_⟩
  obtain ⟨-, h2, -, -, -, -, -, -, -, h10, h11⟩ := hE0d F I Gf D hyp.ax
  obtain ⟨-, h2c, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨δ, hδ⟩ := h10 s hs
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := KernelSeriesConvergence.e_ne
  have hy' : c₀ ≤ D.HtY ![0, 1] ((δ : PG F) • y) := by rw [h2 _ he δ y, hδ]; exact hy
  have hfix : ∀ γ : PG F, ¬ Fix s γ ↔ ¬ Fix ![0, 1] (MulAut.conj (δ : PG F) γ) := by
    intro γ
    have := h11 ![0, 1] γ.out δ
    rw [QuotientGroup.out_eq', hδ] at this
    exact not_congr this.symm
  let e : {γ : PG F // ¬ Fix s γ} ≃ {γ : PG F // ¬ Fix ![0, 1] γ} :=
    (MulAut.conj (δ : PG F)).toEquiv.subtypeEquiv hfix
  calc ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ
      = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a (e γ).1 ((δ : PG F) • y)‖ₑ := by
        congr 1; funext γ
        rw [show (e γ).1 = (δ : PG F) * γ.1 * (δ : PG F)⁻¹ from rfl, h2c]
    _ = ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ :=
        e.tsum_eq (fun γ => ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ)
    _ ≤ C := hC _ hy'
end
end

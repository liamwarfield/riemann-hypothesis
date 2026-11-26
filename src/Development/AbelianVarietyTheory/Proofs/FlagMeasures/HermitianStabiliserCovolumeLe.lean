module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalSetMeasureCommensurableIndexRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalSetMeasureCommensurableIndexRatio
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CovolIdx

theorem tsum_cosets {G : Type} [Group G] (C H : Subgroup G) (hC : C ≤ H) (f : G → ℝ≥0∞) :
    ∑' h : H, f h = ∑' q : H ⧸ C.subgroupOf H, ∑' c : C, f ((q.out : H) * (c : G)) := by
  rw [← ENNReal.tsum_prod]
  let e : (H ⧸ C.subgroupOf H) × C → H := fun p => p.1.out * ⟨p.2, hC p.2.2⟩
  have hmk : ∀ p, (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = p.1 := by
    intro p
    have : (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = QuotientGroup.mk p.1.out := by
      symm
      rw [QuotientGroup.eq]
      simp [e, Subgroup.mem_subgroupOf]
    rw [this, QuotientGroup.out_eq']
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q, c⟩ ⟨q', c'⟩ h
      have h1 : q = q' := by
        have := hmk (q, c)
        rw [h, hmk] at this
        exact this.symm
      subst h1
      have h2 := mul_left_cancel h
      have h3 : c = c' := Subtype.ext (congrArg Subtype.val h2 :)
      rw [h3]
    · intro h
      have hm : ((QuotientGroup.mk h : H ⧸ C.subgroupOf H).out)⁻¹ * h ∈ C.subgroupOf H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      refine ⟨(QuotientGroup.mk h, ⟨_, Subgroup.mem_subgroupOf.1 hm⟩), ?_⟩
      apply Subtype.ext
      simp [e]
  exact ((Equiv.ofBijective e he).tsum_eq (fun h : H => f h)).symm

theorem measure_eq_tsum_inter {G α : Type} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (R : Set α) (A : Subgroup G) [Countable A] (Ω S : Set α)
    (hm : ∀ s : G, Measurable fun x : α => s • x) (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) :
    μ S = ∑' a : A, μ ((fun x => (a : G) • x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((hm a hΩ).inter hS).nullMeasurableSet

theorem measure_eq_invVol_mul : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  intro G α _ _ _ μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB
  have hpre : ∀ s ∈ A ⊔ B, ∀ S, MeasurableSet S → μ ((fun x => s • x) ⁻¹' S) = μ S := by
    intro s hs S hS
    rw [← Measure.map_apply (hm s) hS, (hinv s hs).2]
  let F : G → G → ℝ≥0∞ := fun a b => μ ((fun x => a • x) ⁻¹' Ω ∩ (fun x => b • x) ⁻¹' K)
  have hF : ∀ a b c : G, c ∈ A ⊓ B → F (a * c) b = F a (b * c⁻¹) := by
    intro a b c hc
    refine Eq.trans ?_ (hpre c (Subgroup.mem_sup_left hc.1) _ ((hm a hΩ).inter (hm (b * c⁻¹) hK)))
    simp only [F]
    congr 1
    ext x
    simp [mul_smul]
  have h1 : ∀ b ∈ B, μ K = ∑' a : A, F a b := by
    intro b hb
    rw [← hpre b (Subgroup.mem_sup_right hb) K hK]
    exact measure_eq_tsum_inter μ R A Ω _ hm hR hΩ (hm b hK) fA
  have h2 : ∀ a ∈ A, μ Ω = ∑' b : B, F a b := by
    intro a ha
    rw [← hpre a (Subgroup.mem_sup_left ha) Ω hΩ,
      measure_eq_tsum_inter μ R B K _ hm hR hK (hm a hΩ) fB]
    simp only [F, Set.inter_comm]
  have key : ∑' _q : B ⧸ (A ⊓ B).subgroupOf B, μ K = ∑' _p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω := by
    have e1 : ∀ q : B ⧸ (A ⊓ B).subgroupOf B, μ K =
        ∑' p : A ⧸ (A ⊓ B).subgroupOf A, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro q
      rw [h1 _ q.out.2, tsum_cosets (A ⊓ B) A inf_le_left (fun a => F a (q.out : B))]
      refine tsum_congr fun p => ?_
      rw [← (Equiv.inv (A ⊓ B : Subgroup G)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [hF _ _ _ (Subtype.property _)]
      simp
    have e2 : ∀ p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω =
        ∑' q : B ⧸ (A ⊓ B).subgroupOf B, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro p
      rw [h2 _ p.out.2, tsum_cosets (A ⊓ B) B inf_le_right (fun b => F (p.out : A) b)]
    rw [tsum_congr e1, tsum_congr e2, ENNReal.tsum_comm]
  rw [Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_left, ENNReal.tsum_const, ENNReal.tsum_const] at key
  have fq : Finite (B ⧸ A.subgroupOf B) := Subgroup.fintypeOfIndexNeZero hAB |>.finite
  have fp : Finite (A ⧸ B.subgroupOf A) := Subgroup.fintypeOfIndexNeZero hBA |>.finite
  have key' : (A.relIndex B : ℝ≥0∞) * μ K = (B.relIndex A : ℝ≥0∞) * μ Ω := by
    simpa [ENat.card_eq_coe_natCard, Subgroup.relIndex, Subgroup.index] using key
  have hv : ENNReal.ofReal (GlobalTheory.HL.invVol A B) = (A.relIndex B : ℝ≥0∞)⁻¹ * (B.relIndex A : ℝ≥0∞) := by
    unfold GlobalTheory.HL.invVol
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hAB), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [hv, mul_assoc, ← key', ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hAB) (ENNReal.natCast_ne_top _), one_mul]

end GlobalTheory.CovolIdx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalSetMeasureCommensurableIndexRatioStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_set_measure_commensurable_index_ratio : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  first | exact @GlobalTheory.CovolIdx.measure_eq_invVol_mul | exact GlobalTheory.CovolIdx.measure_eq_invVol_mul | (intros; apply GlobalTheory.CovolIdx.measure_eq_invVol_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.Cov

theorem covol_of_act {G α : Type} [Group G] [MeasurableSpace α] (act : G → α → α) (h1 : ∀ x, act 1 x = x)
    (h2 : ∀ s t x, act (s * t) x = act s (act t x)) (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α)
    (hm : ∀ s, Measurable (act s)) (cA : Countable A) (cB : Countable B) (hR : μ Rᶜ = 0)
    (hinv : ∀ s ∈ A ⊔ B, (∀ x ∈ R, act s x ∈ R) ∧ μ.map (act s) = μ) (hAB : A.relIndex B ≠ 0) (hBA : B.relIndex A ≠ 0)
    (hΩ : MeasurableSet Ω) (hK : MeasurableSet K) (fA : ∀ x ∈ R, ∃! s, s ∈ A ∧ act s x ∈ Ω)
    (fB : ∀ x ∈ R, ∃! s, s ∈ B ∧ act s x ∈ K) : μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  letI : MulAction G α := { smul := act, one_smul := h1, mul_smul := h2 }
  exact GlobalTheory.T.fundamental_set_measure_commensurable_index_ratio G α μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB

theorem continuous_lmulM {k r : ℕ} (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem rset_mul {k r : ℕ} {γ : Mat k r} (hu : IsUnit γ.det) {a b : Mat k r} (ha : a ∈ Rset k r γ) (hb : b ∈ Rset k r γ) :
    a * b ∈ Rset k r γ := by
  refine ⟨WeylGroupFacts.mem_n_mul ha.1 hb.1, ?_⟩
  have e : γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := by
    have : (γ * a * γ⁻¹) * (γ * b * γ⁻¹) = γ * a * (γ⁻¹ * γ) * b * γ⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, nonsing_inv_mul _ hu, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact WeylGroupFacts.mem_n_mul ha.2 hb.2

theorem countable_aut (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Countable (V ≃ₗ[K] V) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable V := (Module.finBasis K V).equivFun.injective.countable
  let b := Module.finBasis K V
  refine Function.Injective.countable (f := fun s : V ≃ₗ[K] V => fun i => s (b i)) fun s t e => ?_
  exact LinearEquiv.toLinearMap_injective (b.ext fun i => congrFun e i)

theorem cov_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g hP hd hF hN hv gg Λ Kf hgg hT hKf
  obtain ⟨hex, hsep, hsub, -⟩ := RealMat.real_points K V H hK r N k ι σ β Φ z z' g hP hd hF
  have hι : Nonempty ι := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    exact ⟨(hP.2 w).choose⟩
  obtain ⟨v0⟩ := id hι
  choose m hm using fun s => (hex s).exists
  have hmu : ∀ (s : V ≃ₗ[K] V) (y : ι → Mt k r), (∀ v x, Matrix.of (y v) *ᵥ Φ v x = Φ v (s x)) → y = m s :=
    fun s y hy => (hex s).unique hy (hm s)
  have hH : ∀ v, IsHaarOn (Rset k r (g v)) (lebR0 k r N.j β) := fun v => by
    obtain ⟨-, hz, hz', hT0, ⟨c, hc⟩, -⟩ := hF v
    exact (GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r N.j N.j_le (z v) (z' v) (g v) β c hz hz' hT0 hc).1
  haveI : SigmaFinite (lebR0 k r N.j β) := (hH v0).1
  have hu : ∀ v, IsUnit (g v).det := fun v => RealMat.isUnit_det (hF v).2.2.2.2.1.choose_spec.1
  have hone : m 1 = fun _ => Matrix.of.symm (1 : Mat k r) :=
    (hmu 1 _ fun v x => by simp only [Equiv.apply_symm_apply, Matrix.one_mulVec]; rfl).symm
  have hmul : ∀ s t, m (s * t) = fun v => Matrix.of.symm (Matrix.of (m s v) * Matrix.of (m t v)) := fun s t =>
    (hmu (s * t) _ fun v x => by
      simp only [Equiv.apply_symm_apply]
      rw [← mulVec_mulVec, hm, hm]; rfl).symm
  have h1 : ∀ x : ι → Mt k r, mulP (m 1) x = x := fun x => by
    rw [hone]; funext v
    show (1 : Mat k r) * Matrix.of (x v) = x v
    rw [Matrix.one_mul]; rfl
  have h2 : ∀ s t (x : ι → Mt k r), mulP (m (s * t)) x = mulP (m s) (mulP (m t) x) := fun s t x => by
    rw [hmul]; funext v
    show (Matrix.of (m s v) * Matrix.of (m t v)) * Matrix.of (x v) = Matrix.of (m s v) * (Matrix.of (m t v) * Matrix.of (x v))
    rw [Matrix.mul_assoc]
  have hmeas : ∀ s, Measurable (mulP (k := k) (r := r) (m s)) := fun s =>
    Measurable.of_eval fun v => (continuous_lmulM _).measurable.comp (measurable_pi_apply v)
  have hmR : ∀ s ∈ N.R, m s ∈ RP k r g := fun s hs => hsub ⟨s, hs, hm s⟩
  have hnull : Measure.pi (fun _ : ι => lebR0 k r N.j β) (RP k r g)ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v, Function.eval v ⁻¹' {x : Mt k r | Matrix.of x ∉ Rset k r (g v)}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ (hH v).2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    exact Set.mem_iUnion.2 ⟨v, hv'⟩
  have hpres : ∀ s ∈ N.R, (Measure.pi fun _ : ι => lebR0 k r N.j β).map (mulP (m s)) =
      Measure.pi fun _ : ι => lebR0 k r N.j β := fun s hs => by
    have e : ∀ v, (lebR0 k r N.j β).map (lmulM (Matrix.of (m s v))) = lebR0 k r N.j β :=
      fun v => (hH v).2.2.2 _ (hmR s hs v)
    haveI : ∀ v, SigmaFinite ((lebR0 k r N.j β).map (lmulM (Matrix.of (m s v)))) := fun v => by rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => lebR0 k r N.j β)
      (f := fun v => lmulM (Matrix.of (m s v))) fun v => (continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  have conv : ∀ (Γ : Subgroup (V ≃ₗ[K] V)) (Ω : Set (ι → Mt k r)), IsFund (realPts Φ (Γ : Set (V ≃ₗ[K] V))) (RP k r g) Ω →
      ∀ x ∈ RP k r g, ∃! s, s ∈ Γ ∧ mulP (m s) x ∈ Ω := by
    intro Γ Ω h x hx
    obtain ⟨m0, ⟨⟨s, hs, hsm⟩, hΩ⟩, hun⟩ := h.2 x hx
    have e : m0 = m s := hmu s m0 hsm
    refine ⟨s, ⟨hs, e ▸ hΩ⟩, fun t ht => ?_⟩
    have e2 : m t = m0 := hun _ ⟨⟨t, ht.1, hm t⟩, ht.2⟩
    exact hsep t s hι fun v x => by rw [← hm t v x, ← hm s v x, e2, e]
  obtain ⟨hLU, -, hz1, -, hRefLat, -⟩ := GlobalTheory.DegCnt.InnerLat.main K V H hK r N gg Λ hgg hT
  have hzL : N.F.z ∈ latL N.F N.F' Λ := by
    have := (hz1 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    simpa using this
  have hΛdata := ((GlobalTheory.HermLat.isUnimod_iff H Λ).1 hT.1.1).1
  have hΛ : Submodule.IsFullLattice K Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg K hΛdata.1, span_eq_top := hΛdata.2 }
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    refine { toIsLattice := hRefLat, span_eq_top := ?_ }
    obtain ⟨-, -, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hP : N.Pi ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
      rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
      exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
        fun _ hx => Submodule.mem_sup_left hx)
    have hW : N.Wt ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
      intro x hx
      have hxW : x ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hx
      obtain ⟨c, hc, hcx⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛdata.2 x
      rw [← Submodule.smul_mem_iff _ hc]
      apply Submodule.subset_span
      apply Submodule.mem_sup_right
      refine ⟨⟨?_, Submodule.mem_sup_left hcx⟩, N.Wn.smul_mem c hxW⟩
      rw [hUp]
      exact Submodule.mem_sup_left (N.Wn.smul_mem c hxW)
    apply eq_top_iff.mpr
    rw [← hC.sup_eq_top]
    exact sup_le hW hP
  obtain ⟨Ω, hΩ, -, hΩle⟩ := GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds K V H hK r N k ι σ β Φ z z' g hP hd hF hN hv (latL N.F N.F' Λ) hLU hzL
  have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
  have hc1 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hRefFull hΛ).1
  have hc2 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hΛ hRefFull).1
  haveI := countable_aut K V
  have key := covol_of_act (fun s x => mulP (m s) x) h1 h2 (Measure.pi fun _ : ι => lebR0 k r N.j β) (RP k r g)
    (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) Ω Kf hmeas inferInstance inferInstance hnull
    (fun s hs => by
      have hsR : s ∈ N.R := (sup_le inf_le_left inf_le_left : _ ≤ N.R) hs
      exact ⟨fun x hx v => rset_mul (hu v) (hmR s hsR v) (hx v), hpres s hsR⟩)
    hc1 hc2 hΩ.1 hKf.1 (conv _ _ hΩ) (conv _ _ hKf)
  have hom : 0 ≤ N.om Λ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [key, ENNReal.ofReal_mul hom]
  exact mul_le_mul_right hΩle _

end GlobalTheory.DegVol.Cov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLeStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_stabiliser_covolume_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  first | exact @GlobalTheory.DegVol.Cov.cov_le | exact GlobalTheory.DegVol.Cov.cov_le | (intros; apply GlobalTheory.DegVol.Cov.cov_le <;> assumption)
end

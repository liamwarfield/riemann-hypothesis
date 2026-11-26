module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
public import CompanionTheory.AutomorphicTheory.ThetaDilations.OrbitAdelic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFinite
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFinite
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FinQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨-, htc, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  have hcx : w.IsComplex := htc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.mpr hcx
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  have := hτ w.embedding x
  rw [hc x] at this
  simpa using this.symm

theorem fixed_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ t : F, e = algebraMap F E t := by
  obtain ⟨x, hx⟩ := exists_moved σ h
  have hd : x - σ x ≠ 0 := fun h0 => hx (sub_eq_zero.mp h0).symm
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgHom.commutes, map_one, map_zero] at h2
    have h3 : t • (x - σ x) = 0 := by
      simp only [Algebra.smul_def] at hst ⊢
      linear_combination hst - h2
    have ht : t = 0 := (smul_eq_zero.mp h3).resolve_right hd
    subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])
  have hmem : e ∈ Submodule.span F ({(1 : E), x} : Set E) := by
    have : e ∈ Submodule.span F (Set.range ![(1 : E), x]) := by rw [hspan]; trivial
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using this
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  have h2 : a • (1 : E) + b • σ x = e := by
    have := congrArg σ hab
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgHom.commutes, map_one, he] at this
    simpa only [Algebra.smul_def] using this
  have h3 : b • (x - σ x) = 0 := by
    simp only [Algebra.smul_def] at hab h2 ⊢
    linear_combination hab - h2
  have hb : b = 0 := (smul_eq_zero.mp h3).resolve_right hd
  subst hb
  refine ⟨a, ?_⟩
  rw [← hab, Algebra.algebraMap_eq_smul_one]
  simp

theorem hE_self_fixed (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma σ h (x j)
  have h2 : σ (J j i) = J i j := hJ.1 i j
  have h3 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, h2, h3]
  ring

end Field

theorem gram_rational_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X : Fin 1 → Fin M → E, ∃ t : F, gramE σ J X = fun _ _ => algebraMap F E t) ∧
    (∀ (n : ℕ) (X : Fin n → Fin M → E),
      gramR (AF F) σ J (ratTup (AF F) X) = (gramE σ J X).map (inclR (AF F))) ∧
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      {t : F | ∃ Y ∈ Ω, gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)}.Finite := by
  intro F E _ _ _ _ _ σ hcm M J hJ
  refine ⟨?_, ?_, ?_⟩
  · intro X
    obtain ⟨t, ht⟩ := fixed_mem σ hcm _ (hE_self_fixed σ hcm J hJ (X 0))
    refine ⟨t, ?_⟩
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact ht
  · intro n X
    ext a b
    have hs : ∀ e : E, sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := fun e => by
      simp [sigR, inclR]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramR, hR, hform, ratTup, JR, Matrix.map_apply, gramE, hE, map_sum, map_mul, hs]
    rfl
  · intro Ω hΩ
    obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
    let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
      fun Y _ _ => gramR (AF F) σ J Y 0 0
    have hφ : Continuous φ :=
      continuous_pi fun _ => continuous_pi fun _ => hcont.matrix_elem 0 0
    have hfin := (GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hcm 1 1).2.1 _ (hΩ.image hφ)
    let ι : F → Fin 1 → Fin 1 → E := fun t _ _ => algebraMap F E t
    refine Set.Finite.of_injOn (f := ι) ?_ ?_ hfin
    · rintro t ⟨Y, hY, hYt⟩
      refine ⟨Y, hY, ?_⟩
      funext a b
      exact congrFun (congrFun hYt 0) 0
    · intro s _ t _ hst
      exact (algebraMap F E).injective (congrFun (congrFun hst 0) 0)

end GlobalTheory.CompanionTheory.SW.FinQ
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_gram_adelic_compact_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ X : Fin 1 → Fin M → E, ∃ t : F, gramE σ J X = fun _ _ => algebraMap F E t) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramR (AF F) σ J (ratTup (AF F) X) = (gramE σ J X).map (inclR (AF F))) ∧ ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → {t : F | ∃ Y ∈ Ω, gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinQ.gram_rational_finite | exact GlobalTheory.CompanionTheory.SW.FinQ.gram_rational_finite | (intros; apply GlobalTheory.CompanionTheory.SW.FinQ.gram_rational_finite <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierCoefficientGrowthBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierCoefficientGrowthBound
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem norm_fstar_le_den : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ C : ℝ, ∀ b : F, ‖fstar ψ (hf F) (Bf B) (muF B lf) φ (algebraMap F (A F) b)‖ ≤ C * ((den b : ℝ) ^ M)⁻¹ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.fstar_decay

end GlobalTheory.CompanionTheory.SW.Core
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierCoefficientGrowthBoundStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coefficient_growth_bound : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ C : ℝ, ∀ b : F, ‖fstar ψ (hf F) (Bf B) (muF B lf) φ (algebraMap F (A F) b)‖ ≤ C * ((den b : ℝ) ^ M)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.norm_fstar_le_den | exact GlobalTheory.CompanionTheory.SW.Core.norm_fstar_le_den | (intros; apply GlobalTheory.CompanionTheory.SW.Core.norm_fstar_le_den <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBounded
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBounded
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatCount

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def ratHom (M : ℕ) : (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun := ratTup (AF F)
  map_zero' := by
    funext a i
    simp [ratTup]
  map_add' X Y := by
    funext a i
    simp [ratTup]

lemma box_mono {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

lemma sizeInf_nonneg {d : ℕ} (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma repr_projInf_ratTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf (ratTup (AF F) X) a i) k =
      algebraMap F (Ainf F) (b.repr (X a i) k) := by
  have : projInf (ratTup (AF F) X) a i = (1 : Ainf F) ⊗ₜ[F] X a i := by
    simp [projInf, ratTup, inclR]
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

lemma sizeTup_ratTup_pos {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (hX : X ≠ 0) : 0 < sizeTup b (projInf (ratTup (AF F) X)) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨k, hk⟩ : ∃ k, b.repr (X a i) k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi (b.repr.map_eq_zero_iff.mp (Finsupp.ext h))
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  set Y := projInf (ratTup (AF F) X : Fin n → Fin M → AF F ⊗[F] E) with hY
  have h1 : 0 < ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ := by
    rw [hY, repr_projInf_ratTup, norm_pos_iff]
    change algebraMap F v.Completion (b.repr (X a i) k) ≠ 0
    exact (map_ne_zero _).mpr hk
  have h2 : ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ ≤ sizeInf b (Y a i) :=
    (Finset.single_le_sum
      (f := fun v => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum
      (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have h3 : sizeInf b (Y a i) ≤ sizeTup b Y :=
    (Finset.single_le_sum (f := fun i => sizeInf b (Y a i))
      (fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (Y a i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ a))
  linarith

end SlopeTestRemainingChoices

lemma exists_pos_lt {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ S, r < f x :=
  _root_.Bl.FirstLemmaK.goal1 hS f hf

theorem count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M Ω hΩ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨hcpt, hexh, hflow⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ b 1 M
  obtain ⟨-, hfin, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hCM 1 M
  obtain ⟨N, r, hN, hr, hsub⟩ := hexh Ω hΩ

  obtain ⟨r₀, h0, h1, hsmall⟩ := exists_pos_lt
    (((hfin _ (hcpt N 1 hN)).subset (Set.inter_subset_left
      (t := {X : Fin 1 → Fin M → E | X ≠ 0}))))
    (fun X => sizeTup b (projInf (ratTup (AF F) X)))
    (fun X hX => sizeTup_ratTup_pos b X hX.2)
  have hnone : ∀ X : Fin 1 → Fin M → E, X ≠ 0 → ratTup (AF F) X ∉ box b N r₀ := by
    intro X hX hmem
    have := hsmall X ⟨box_mono b N h1 hmem, hX⟩
    exact absurd hmem.2 (not_le.mpr this)
  have hscale : ∀ (x : ℝ) (Y : Fin 1 → Fin M → AF F ⊗[F] E),
      ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ Ω →
        Y ∈ box b N (Real.exp x * r) := by
    intro x Y hY
    refine (hflow τ hτ N (Real.exp x * r) (-x) Y).mp ?_
    have : Real.exp (-x) * (Real.exp x * r) = r := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact hsub hY
  refine ⟨Real.log (r₀ / r), (5 * r / r₀) ^ (2 * Module.finrank ℚ F * M), fun x => ?_⟩
  split_ifs with hx
  ·
    have hlt : Real.exp x * r < r₀ := by
      have := (Real.lt_log_iff_exp_lt (div_pos h0 hr)).mp hx
      exact (lt_div_iff₀ hr).mp this
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun X => Set.indicator_of_notMem ?_ _)
    intro hmem
    exact hnone X.1 X.2 (box_mono b N hlt.le (hscale x _ hmem))
  · have hge : r₀ ≤ Real.exp x * r := by
      have := (Real.log_le_iff_le_exp (div_pos h0 hr)).mp (not_lt.mp hx)
      exact (div_le_iff₀ hr).mp this
    set e := ratHom (F := F) (E := E) M with he
    have hone : ∑' l : Fin 1 → Fin M → E,
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ 1 := by
      rw [tsum_eq_single 0]
      · exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => by simp)
      · intro X hX
        exact Set.indicator_of_notMem (hnone X hX) _
    have hpack := GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hCM _ b M (Fin 1 → Fin M → E) e N r₀ (Real.exp x * r) h0 hge
    calc ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞)))
            (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1)
        ≤ ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0},
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e X.1) := by
          refine ENNReal.tsum_le_tsum fun X => ?_
          by_cases hm : ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
              ratTup (AF F) X.1 ∈ Ω
          · have hm' : e X.1 ∈ box b N (Real.exp x * r) := hscale x _ hm
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
          · rw [Set.indicator_of_notMem hm]
            exact bot_le
      _ ≤ ∑' l : Fin 1 → Fin M → E,
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun l => (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l))
      _ ≤ ENNReal.ofReal ((5 * (Real.exp x * r) / r₀) ^ (2 * Module.finrank ℚ F * M)) * 1 :=
          hpack.trans (mul_le_mul_right hone _)
      _ = ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M) *
            Real.exp (2 * Module.finrank ℚ F * M * x)) := by
          rw [mul_one]
          congr 1
          have : (2 * (Module.finrank ℚ F : ℝ) * M * x) =
              ((2 * Module.finrank ℚ F * M : ℕ) : ℝ) * x := by push_cast; ring
          rw [this, Real.exp_nat_mul, ← mul_pow]
          congr 1
          ring

end GlobalTheory.CompanionTheory.SW.LatCount
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBoundedStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flow_lattice_count_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatCount.count_le | exact GlobalTheory.CompanionTheory.SW.LatCount.count_le | (intros; apply GlobalTheory.CompanionTheory.SW.LatCount.count_le <;> assumption)
end
end

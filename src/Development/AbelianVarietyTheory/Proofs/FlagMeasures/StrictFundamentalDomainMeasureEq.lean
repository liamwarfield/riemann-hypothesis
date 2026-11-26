module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEq
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem strictFD_measure_eq_tsum {G X : Type} [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hmeas : ∀ g, Measurable (ρ g)) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = ∑' g, μ (D ∩ NN ∩ (ρ g)⁻¹' D') := by
  have h1 : μ D = μ (D ∩ NN) := by
    rw [← measure_inter_add_diff D hNN]
    have : μ (D \ NN) = 0 := measure_mono_null (fun x hx => hx.2) hnull
    rw [this, add_zero]
  rw [h1]
  have hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D' := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxD, hxN⟩
      obtain ⟨g, hg, -⟩ := hu' x hxN
      exact ⟨g, ⟨hxD, hxN⟩, hg⟩
    · rintro ⟨g, ⟨hxD, hxN⟩, -⟩
      exact ⟨hxD, hxN⟩
  conv_lhs => rw [hU]
  apply measure_iUnion
  · intro g h hgh
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩
    exact hgh ((hu' x hxN).unique hg hh)
  · intro g
    exact (hD.inter hNN).inter (hmeas g hD')

theorem strictFD_measure_eq {G X : Type} [Group G] [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hone : ∀ x, ρ 1 x = x) (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (hinv : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN) (hmp : ∀ g, MeasurePreserving (ρ g) μ μ)
    (hu : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = μ D' := by
  have hmeas : ∀ g, Measurable (ρ g) := fun g => (hmp g).measurable
  rw [strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu',
    strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply]
  have hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D) :=
    (hD'.inter hNN).inter (hmeas g⁻¹ hD)
  rw [← (hmp g).measure_preimage hS.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  have hx : ρ g⁻¹ (ρ g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  rw [hx]
  constructor
  · rintro ⟨⟨hxD, hxN⟩, hgx⟩
    exact ⟨⟨hgx, hinv g x hxN⟩, hxD⟩
  · rintro ⟨⟨hgx, hgxN⟩, hxD⟩
    refine ⟨⟨hxD, ?_⟩, hgx⟩
    have := hinv g⁻¹ _ hgxN
    rwa [hx] at this

end GlobalTheory.SnMass.VolN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEqStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictFundamentalDomain_measure_eq : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.SnMass.VolN.strictFD_measure_eq | exact GlobalTheory.SnMass.VolN.strictFD_measure_eq | (intros; apply GlobalTheory.SnMass.VolN.strictFD_measure_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowDivLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowDivLattice
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem hasDom_ideLat_dInv_div : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hu t t' c hc
  have hE : IsTotallyComplex E := hσ.2.1
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have hdF : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hd : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (FrameDual.natAbs_discr_sq (F := F) (E := E) hσ.2.2.1)
    rw [Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs] at h1
    rw [sq_abs]
    have h2 : ((|discr E| : ℤ) : ℝ) = ((|discr F| ^ 2 : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2, sq_abs]
  set I := dInv E t * (dInv E t')⁻¹ with hIdef
  have hNI : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (|(discr E : ℝ)|⁻¹ ^ t) * (|(discr E : ℝ)|⁻¹ ^ t')⁻¹ := by
    rw [hIdef, map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FrameDual.absNorm_dInv, FrameDual.absNorm_dInv]
  have hI : I ≠ 0 := by
    intro h0
    have h1 : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = 0 := by rw [h0, map_zero, Rat.cast_zero]
    rw [hNI] at h1
    have : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 hdE
    simp_all
  obtain ⟨L₀, hL₀, hcov⟩ := HomCovolume.exists_idealLat E hE I hI
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    LinearMap.pi fun w => (Algebra.lmul ℝ ℂ ((c : ℂ))⁻¹).comp (LinearMap.proj w)
  have hf : ∀ z w, f z w = ((c : ℂ))⁻¹ * z w := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2 :=
    Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 hc0) _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HomCovolume.HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ (ideLat I c : Set (InfinitePlace E → ℂ)) := by
    intro z
    change f z ∈ L₀ ↔ ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · rw [← h w, hf, mul_inv_cancel_left₀ hc0]
    · rw [hf, h w, inv_mul_cancel_left₀ hc0]
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu'⟩ := existsUnique_add_mem_latticeDomain L a
    refine ⟨z, ⟨(hL z).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hl'⟩
    exact congrArg Subtype.val (hu' ⟨l, (hL l).2 hl⟩ hl')
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    have hn : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hDpos : 0 < |(discr F : ℝ)| := abs_pos.2 hdF
    have hr : |(discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) =
        |(discr F : ℝ)| ^ (1 + 2 * t') / |(discr F : ℝ)| ^ (2 * t) := by
      rw [show (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = ((1 + 2 * t' : ℕ) : ℝ) - ((2 * t : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_sub hDpos, Real.rpow_natCast, Real.rpow_natCast]
    rw [hNI, HomCovolume.vInv_pow E hE, hn, hd, Real.sqrt_sq hDpos.le, hr, Finset.prod_const, Finset.card_univ,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    generalize |(discr F : ℝ)| = D at hDpos
    generalize Fintype.card (InfinitePlace E) = n
    rw [inv_pow, inv_pow, inv_inv, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_one, div_eq_mul_inv]
    ring

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowDivLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_div_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div | exact GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div | (intros; apply GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomain
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem existsUnique_layered_fundamentalDomain :
    ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  intro G X B _ _ V _ ρ NN o deg c L D ho h1 hmul hst hL0 hD hco htr hL hon hinj x hx
  classical
  haveI := Fintype.ofFinite B
  have hgx : ∀ (g : G) (y : X), y ∈ NN → ρ g y ∈ NN := fun g y hy => hst g y hy

  have step : ∀ (d : ℕ) (T : Finset B), (∀ β ∈ T, deg β = d) →
      (∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β) →
      ∃ g : G, ∀ β, (deg β < d ∨ β ∈ T) → c β (ρ g x) ∈ D β := by
    intro d T
    induction T using Finset.induction_on with
    | empty =>
      intro _ ⟨g, hg⟩
      refine ⟨g, fun β hβ => ?_⟩
      rcases hβ with hβ | hβ
      · exact hg β hβ
      · simp at hβ
    | insert b T hb ih =>
      intro hT h0
      obtain ⟨g, hg⟩ := ih (fun β hβ => hT β (Finset.mem_insert_of_mem hβ)) h0
      have hbd : deg b = d := hT b (Finset.mem_insert_self b T)
      obtain ⟨l, ⟨hlL, hlD⟩, -⟩ := hD b (c b (ρ g x))
      obtain ⟨h, hhl, hh0⟩ := hon b l hlL
      have hlow : ∀ β, deg β < d → c β (ρ h o) = 0 := fun β hβ =>
        hh0 β (fun e => by subst e; omega) (by omega)
      have htrans := htr d h hlow (ρ g x) (hgx g x hx)
      refine ⟨h * g, fun β hβ => ?_⟩
      rw [hmul]
      by_cases hβb : β = b
      · subst hβb
        rw [htrans β (by omega), hhl]
        exact hlD
      · have hle : deg β ≤ d := by
          rcases hβ with hβ | hβ
          · omega
          · exact (hT β hβ).le
        have hold : deg β < d ∨ β ∈ T := by
          rcases hβ with hβ | hβ
          · exact Or.inl hβ
          · exact Or.inr ((Finset.mem_insert.mp hβ).resolve_left hβb)
        rw [htrans β hle, hh0 β hβb (by omega), add_zero]
        exact hg β hold
  have exD : ∀ d : ℕ, ∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β := by
    intro d
    induction d with
    | zero => exact ⟨1, fun β hβ => absurd hβ (Nat.not_lt_zero _)⟩
    | succ d ih =>
      obtain ⟨g, hg⟩ := step d (Finset.univ.filter (fun β => deg β = d))
        (fun β hβ => (Finset.mem_filter.mp hβ).2) ih
      refine ⟨g, fun β hβ => hg β ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨M, hM⟩ := (Set.finite_range deg).bddAbove
  obtain ⟨g₀, hg₀⟩ := exD (M + 1)
  refine ⟨g₀, fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)), ?_⟩

  intro g₂ hg₂
  have hg₁ : ∀ β, c β (ρ g₀ x) ∈ D β := fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩))
  have hy : ρ g₀ x ∈ NN := hgx g₀ x hx
  have hδy : ρ (g₂ * g₀⁻¹) (ρ g₀ x) = ρ g₂ x := by
    rw [← hmul, inv_mul_cancel_right]
  have vanish : ∀ d : ℕ, ∀ β, deg β < d → c β (ρ (g₂ * g₀⁻¹) o) = 0 := by
    intro d
    induction d with
    | zero => exact fun β hβ => absurd hβ (Nat.not_lt_zero _)
    | succ d ih =>
      intro β hβ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact ih β h
      · have hin : c β (ρ (g₂ * g₀⁻¹) o) ∈ L β := hL _ β (fun β' hβ' => ih β' (by omega))
        have hadd := htr d (g₂ * g₀⁻¹) ih (ρ g₀ x) hy β h.le
        rw [hδy] at hadd
        have hmem : c β (ρ g₀ x) + c β (ρ (g₂ * g₀⁻¹) o) ∈ D β := hadd ▸ hg₂ β
        have hzero : c β (ρ g₀ x) + 0 ∈ D β := by simpa using hg₁ β
        exact (hD β (c β (ρ g₀ x))).unique ⟨hin, hmem⟩ ⟨hL0 β, hzero⟩
  have hone : g₂ * g₀⁻¹ = 1 :=
    hinj _ (fun β => vanish (M + 1) β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)))
  exact mul_inv_eq_one.mp hone

end GlobalTheory.SnMass.VolN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomainStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_layered_strictFundamentalDomain : ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  first | exact @GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | exact GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | (intros; apply GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangular
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.DepOne

theorem Hpk_mulVec_e {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    unfold Hpk
    rw [if_pos (by omega), one_mul]
  · intro l _ hl
    have hl' : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext h)
    have := a.isLt
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp

theorem Hpk_e_es {k r : ℕ} (a b : Fin r) :
    Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold Hpk
  by_cases hab : a = b
  · subst hab
    rw [if_pos (by omega), if_pos rfl]
  · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hab]

theorem es_es {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r)
    (b : Fin r) : ∀ (n : ℕ) (a : Fin r), a.val = n → a ≤ b →
      x (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a han hab
  have hU : xᴴ * Hpk k r * x = Hpk k r := hx.1
  have h := congrFun (congrFun hU (eI k r a)) (esI k r b)
  rw [Matrix.mul_assoc, Hpk_e_es] at h
  have hs : (xᴴ * (Hpk k r * x)) (eI k r a) (esI k r b) =
      ∑ i, star (x i (eI k r a)) * (Hpk k r *ᵥ fun l => x l (esI k r b)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [hs, Finset.sum_eq_single (eI k r a)] at h
  · rw [Hpk_mulVec_e, hx.2.1 a (eI k r a) le_rfl, if_pos rfl, star_one, one_mul] at h
    exact h
  · intro i _ hi
    by_cases hia : a.val ≤ i.val
    · rw [hx.2.1 a i hia, if_neg hi, star_zero, zero_mul]
    · have ha := a.isLt
      obtain ⟨c, rfl⟩ : ∃ c : Fin r, i = eI k r c := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      have hca : c.val < a.val := by simpa [eI] using not_le.1 hia
      rw [Hpk_mulVec_e]
      have hcb : c ≤ b := le_trans (le_of_lt (show c < a from hca)) hab
      rw [ih c.val (han ▸ hca) c rfl hcb, if_neg (fun h => by
        subst h; exact absurd hab (not_le.2 hca)), mul_zero]
  · simp

theorem dep_one : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    x ∈ Nset k r → Dep k r 1 (x - 1) := by
  intro k r x hx i j hij
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  have hi := i.isLt
  have hj := j.isLt
  simp only [pos] at hij
  by_cases hjr : j.val < r
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have e : j = eI k r ⟨j.val, hjr⟩ := Fin.ext rfl
    have := hx.2.1 ⟨j.val, hjr⟩ i hji
    rw [← e] at this
    exact this
  by_cases hjm : j.val ≤ r + k
  · have hri : r ≤ i.val := by split_ifs at hij <;> omega
    exact hx.2.2 i j (by omega) hjm hri
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have hb : 2 * r + k - j.val < r := by omega
    have hc : 2 * r + k - i.val < r := by omega
    have ej : j = esI k r ⟨2 * r + k - j.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    have ei : i = esI k r ⟨2 * r + k - i.val, hc⟩ := Fin.ext (by simp [esI]; omega)
    have key := es_es hx ⟨2 * r + k - j.val, hb⟩ _ ⟨2 * r + k - i.val, hc⟩ rfl
      (by rw [Fin.mk_le_mk]; omega)
    rw [← ei, ← ej] at key
    rw [key]
    by_cases hij' : i = j
    · subst hij'; simp
    · rw [if_neg hij', if_neg]
      intro h
      apply hij'
      rw [ei, ej, h]

end GlobalTheory.SnMass.VolN.DepOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangularStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_block_upper_unitriangular : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), x ∈ Nset k r → Dep k r 1 (x - 1) := by
  first | exact @GlobalTheory.SnMass.VolN.DepOne.dep_one | exact GlobalTheory.SnMass.VolN.DepOne.dep_one | (intros; apply GlobalTheory.SnMass.VolN.DepOne.dep_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProduct
open MeasureTheory

namespace GlobalTheory.NMKProd

theorem lintegral_nmk {H : Type} [Mul H] [MeasurableSpace H] [MeasurableMul₂ H]
    (a b k : Measure H) [SFinite a] [SFinite b] [SFinite k] (d : H → ENNReal) (hd : Measurable d)
    (φ : H → ENNReal) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(((a.prod (b.prod k)).withDensity fun x => d x.2.1).map
        fun x : H × H × H => x.1 * x.2.1 * x.2.2) =
      ∫⁻ u, ∫⁻ m, d m * ∫⁻ z, φ (u * m * z) ∂k ∂b ∂a := by
  have hmul : Measurable (fun x : H × H × H => x.1 * x.2.1 * x.2.2) :=
    (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd
  have hD : Measurable (fun x : H × H × H => d x.2.1) := hd.comp measurable_snd.fst
  have hφm : Measurable (fun x : H × H × H => φ (x.1 * x.2.1 * x.2.2)) := hφ.comp hmul
  rw [lintegral_map hφ hmul, lintegral_withDensity_eq_lintegral_mul _ hD hφm,
    lintegral_prod _ (hD.mul hφm).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hin : Measurable (fun y : H × H => d y.1 * φ (u * y.1 * y.2)) :=
    (hd.comp measurable_fst).mul (hφ.comp ((measurable_const.mul measurable_fst).mul measurable_snd))
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hin.aemeasurable]
  refine lintegral_congr fun m => ?_
  have hz : Measurable (fun z : H => φ (u * m * z)) := hφ.comp (measurable_id.const_mul (u * m))
  exact lintegral_const_mul (d m) hz

private lemma indicator_pi_univ_eq_prod {ι : Type} [Fintype ι] {G : ι → Type} (s : ∀ i, Set (G i))
    (x : ∀ i, G i) :
    (Set.univ.pi s).indicator (1 : (∀ i, G i) → ENNReal) x =
      ∏ i, (s i).indicator (1 : G i → ENNReal) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    rw [Set.mem_univ_pi] at hx
    simp [Set.indicator_of_mem (hx _)]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem prod_formula : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  intro ι _ G _ _ _ μ μN μM μK _ _ _ _ C c δ hC0 hCt hδ hrel φ hφ
  have hD : Measurable (fun m : ∀ i, G i => ∏ i, δ i (m i)) :=
    Finset.measurable_prod _ (fun i _ => (hδ i).comp (measurable_pi_apply i))
  have key := fun (ψ : (∀ i, G i) → ENNReal) (hψ : Measurable ψ) =>
    lintegral_nmk (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
      (fun m : ∀ i, G i => ∏ i, δ i (m i)) hD ψ hψ
  set R0 := (((Measure.pi μN).prod ((Measure.pi μM).prod (Measure.pi μK))).withDensity
      fun x => ∏ i, δ i (x.2.1 i)).map
    (fun x : (∀ i, G i) × (∀ i, G i) × (∀ i, G i) => x.1 * x.2.1 * x.2.2) with hR0
  have hC0' : (∏ i, C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hC0 i
  have hCt' : (∏ i, C i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hCt i
  have hpi : Measure.pi μ = (∏ i, C i)⁻¹ • ((∏ i, c i) • R0) := by
    refine Measure.pi_eq fun s hs => ?_
    have hX : ∀ i, C i * μ i (s i) = c i * ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      intro i
      have h := hrel i ((s i).indicator 1) (measurable_one.indicator (hs i))
      rwa [lintegral_indicator_one (hs i)] at h
    have hbox : R0 (Set.univ.pi s) = ∏ i, ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      rw [← lintegral_indicator_one (MeasurableSet.univ_pi hs),
        key _ (measurable_one.indicator (MeasurableSet.univ_pi hs))]
      have hK : ∀ u m : ∀ i, G i, ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) =
          ∏ i, ∫⁻ k, (s i).indicator 1 (u i * m i * k) ∂(μK i) := by
        intro u m
        simp_rw [indicator_pi_univ_eq_prod]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i k => (s i).indicator 1 (u i * m i * k))
          (fun i => (measurable_one.indicator (hs i)).comp (measurable_const.mul measurable_id))
      have hA : ∀ i (u' : G i), Measurable (fun m' : G i =>
          δ i m' * ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i)) := by
        intro i u'
        refine (hδ i).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun y : G i × G i => (s i).indicator 1 (u' * y.1 * y.2))
          ((measurable_one.indicator (hs i)).comp ((measurable_const.mul measurable_fst).mul measurable_snd))
      have hB : ∀ i, Measurable (fun u' : G i => ∫⁻ m', δ i m' *
          ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i) ∂(μM i)) := by
        intro i
        refine Measurable.lintegral_prod_right' (f := fun y : G i × G i =>
          δ i y.2 * ∫⁻ k, (s i).indicator 1 (y.1 * y.2 * k) ∂(μK i)) ?_
        refine ((hδ i).comp measurable_snd).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun z : (G i × G i) × G i =>
            (s i).indicator 1 (z.1.1 * z.1.2 * z.2))
          ((measurable_one.indicator (hs i)).comp
            ((measurable_fst.fst.mul measurable_fst.snd).mul measurable_snd))
      have hM : ∀ u : ∀ i, G i, ∫⁻ m, (∏ i, δ i (m i)) *
          ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) =
          ∏ i, ∫⁻ m', δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i) ∂(μM i) := by
        intro u
        simp_rw [hK u, ← Finset.prod_mul_distrib]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod
          (fun i m' => δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i)) (fun i => hA i (u i))
      simp_rw [hM]
      exact GlobalTheory.SnMass.Push.lintegral_fintype_prod _ hB
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [hbox, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => (hX i).symm,
      Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel hC0' hCt', one_mul]
  rw [hpi, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hC0' hCt', one_mul, hR0]
  exact congrArg ((∏ i, c i) * ·) (key φ hφ)

end GlobalTheory.NMKProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProductStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaNMKIntegration_pi_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  first | exact @GlobalTheory.NMKProd.prod_formula | exact GlobalTheory.NMKProd.prod_formula | (intros; apply GlobalTheory.NMKProd.prod_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLattice
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.IntU

theorem hpk_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mulVec_esI (k r : ℕ) (a : Fin r) (z : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ z) (esI k r a) = z (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row]

theorem coord_eI {E : Type} [Field E] {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x y : Fin (2 * r + k + 1) → E) (a : Fin r) (s : ℝ) (hs : s ≠ 0)
    (hy : B *ᵥ (fun i => τ (y i)) = (s : ℂ)⁻¹ • bvec (esI k r a)) :
    (B *ᵥ fun i => τ (x i)) (eI k r a) = (s : ℂ) * τ (form σ J x y) := by
  have key : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) := by
    rw [← hB]
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have lhs : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (s : ℂ)⁻¹ * (B *ᵥ fun i => τ (x i)) (eI k r a) := by
    rw [hy, star_smul, bvec, ← hpk_mulVec_esI k r a (B *ᵥ fun i => τ (x i))]
    simp [Pi.star_def, dotProduct, Pi.single_apply, -Matrix.mulVec_mulVec]
  have rhs : star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) = τ (form σ J x y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, map_sum, map_mul, hτ, RingHom.map_mulVec]
    rfl
  rw [lhs, rhs] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end GlobalTheory.SnMass.VolN.IntU

namespace GlobalTheory.SnMass.VolN.IntU

theorem form_smul_smul {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (c c' : E) (x y : Fin n → E) : form σ J (c • x) (c' • y) = c * σ c' * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_of_pair {E : Type} [Field E] [NumberField E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0) (hst : FrameDual.Stab σ 𝔞⁻¹) (u : E)
    (hu : ∀ c ∈ 𝔟, ∀ c' ∈ 𝔞⁻¹, c * σ c' * u ∈ (algebraMap (𝓞 E) E).range) : u ∈ 𝔞 * 𝔟⁻¹ := by
  have hI : 𝔟 * 𝔞⁻¹ ≠ 0 := mul_ne_zero h𝔟 (inv_ne_zero h𝔞)
  have e : 𝔞 * 𝔟⁻¹ = (𝔟 * 𝔞⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [e, FractionalIdeal.mem_inv_iff hI]
  intro y hy
  refine FractionalIdeal.mul_induction_on hy (fun c hc d hd => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · have := hu c hc (σ d) (hst d hd)
    rw [hσ] at this
    obtain ⟨t, ht⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨t, by rw [ht]; ring⟩
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule h₁ h₂

end GlobalTheory.SnMass.VolN.IntU


open GlobalTheory.SnMass.VolN.IntU in
theorem GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ p
  obtain ⟨hCM, -, hND, hSD, -, -, hTup, hMod, hs, hAd⟩ := hV
  obtain ⟨⟨a, b⟩, hab⟩ := p
  dsimp only
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    show σ (σ x) = x
    exact (Classical.arbitrary (InfinitePlace E)).embedding.injective (by rw [hconj, hconj, star_star])
  set eb : Fin (2 * r + k + 1) → E := fun i => P i b.castSucc with heb
  set fa : Fin (2 * r + k + 1) → E := fun i => f i a with hfa
  refine ⟨form (σ : E →+* E) J (γ *ᵥ eb) fa, ?_, fun w => ?_⟩
  · refine mem_of_pair (σ : E →+* E) hσ _ _ (FrameDual.dInv_ne_zero _) (FrameDual.dInv_ne_zero _)
      ((FrameDual.stab_dInv hσ _).inv hσ (FrameDual.dInv_ne_zero _)) _ ?_
    intro c hc c' hc'
    have h1 : c • eb ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.castAdd r b.castSucc, c, by rw [FrameDual.frameDualTupleIdeals_castAdd]; exact hc, by
        funext i; simp [heb, sideM]⟩)
    have h2 : c' • fa ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.natAdd (r + 1) a, c', by rw [FrameDual.frameDualTupleIdeals_natAdd]; exact hc', by
        funext i; simp [hfa, sideM]⟩)
    have h3 : γ *ᵥ (c • eb) ∈ Λ := by
      rw [← hγ.2]; exact ⟨_, h1, rfl⟩
    have h4 := (hSD.2 _).1 h3 _ h2
    rwa [Matrix.mulVec_smul, form_smul_smul] at h4
  · set τ := w.embedding with hτ
    have hB := hMod w
    have hdet : IsUnit (A w).det := by
      refine Ne.isUnit fun h0 => hND.2 ?_
      have := congrArg Matrix.det hB
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact (map_eq_zero τ).1 this.symm
    have hsb : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have hbv : bvec (eI k r b) = (s b : ℂ)⁻¹ • (A w *ᵥ fun i => τ (eb i)) := by
      rw [(hAd w b).1, smul_smul, inv_mul_cancel₀ hsb, one_smul]
    have hmap : (γ.map τ *ᵥ fun i => τ (eb i)) = fun i => τ ((γ *ᵥ eb) i) := by
      funext i; exact (RingHom.map_mulVec τ γ eb i).symm
    have hent : gM A γ w (eI k r a) (eI k r b) =
        (s b : ℂ)⁻¹ * (A w *ᵥ fun i => τ ((γ *ᵥ eb) i)) (eI k r a) := by
      have e1 : gM A γ w (eI k r a) (eI k r b) = (gM A γ w *ᵥ bvec (eI k r b)) (eI k r a) := by
        simp [bvec]
      rw [e1, hbv, Matrix.mulVec_smul, gM, Matrix.mulVec_mulVec, Matrix.mul_assoc (A w * γ.map τ),
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap]
      rfl
    show gM A γ w (eI k r a) (eI k r b) = _
    rw [hent, coord_eI (σ : E →+* E) τ (hconj τ) J (A w) hB (γ *ᵥ eb) fa a (s a) (hs a).ne' (hAd w a).2]
    push_cast
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  first | exact @GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat | exact GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat | (intros; apply GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLattice
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

section Corner

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem form_smul_smul' (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : E) (u v : Fin n → E) :
    form σ J (y • u) (x • v) = σ x * y * form σ J u v := by
  simp only [form, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_mem_dInv_mul (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) (i j : ℕ) (u v : Fin n → E)
    (hu : ∀ y ∈ (dInv E j)⁻¹, y • u ∈ Λ) (hv : ∀ x ∈ (dInv E i)⁻¹, x • v ∈ Λ) :
    form σ J u v ∈ dInv E i * dInv E j := by
  have h0 : dInv E i * dInv E j ≠ 0 :=
    mul_ne_zero (FrameDual.dInv_ne_zero i) (FrameDual.dInv_ne_zero j)
  rw [← inv_inv (dInv E i * dInv E j), FractionalIdeal.mem_inv_iff (inv_ne_zero h0)]
  intro z hz
  rw [mul_inv] at hz
  refine FractionalIdeal.mul_induction_on hz (fun x hx y hy => ?_) (fun a b ha hb => ?_)
  · have hsx : σ x ∈ (dInv E i)⁻¹ :=
      FrameDual.Stab.inv hσ (FrameDual.stab_dInv hσ i) (FrameDual.dInv_ne_zero i) x hx
    have h1 := (hΛ.2 (y • u)).1 (hu y hy) ((σ x) • v) (hv _ hsx)
    rw [form_smul_smul', hσ] at h1
    obtain ⟨d, hd⟩ := h1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩
    rw [hd]; ring
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule ha hb

end Corner

theorem Hpk_esI_apply (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  exact @_root_.GlobalTheory.SnMass.VolN.IntU.hpk_row k r a j

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem Hpk_mulVec_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_esI_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem map_mulVec_comp {E : Type} [Field E] (φ : E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (v : Fin n → E) : (γ.map φ) *ᵥ (fun i => φ (v i)) = fun i => φ ((γ *ᵥ v) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem corner_entry {E : Type} [Field E] (σ : E →+* E) (φ : E →+* ℂ) (hφ : ∀ x, φ (σ x) = star (φ x))
    {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hJ : J.det ≠ 0)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : Mᴴ * Hpk k r * M = J.map φ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (a b : Fin r) (fa fb : Fin (2 * r + k + 1) → E)
    (sa sb : ℝ) (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (ha : M *ᵥ (fun i => φ (fa i)) = ((sa : ℂ)⁻¹) • bvec (esI k r a))
    (hb : M *ᵥ (fun i => φ (fb i)) = ((sb : ℂ)⁻¹) • bvec (esI k r b)) :
    (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = ((sa * sb : ℝ) : ℂ) * φ (form σ J (γ *ᵥ fb) fa) := by
  have hsa' : (sa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsa
  have hsb' : (sb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsb
  have hdet : (J.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hJ
  have hU : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h => hdet ?_
    rw [← hM, Matrix.det_mul, h, mul_zero]
  have hinv : M⁻¹ *ᵥ bvec (esI k r b) = (sb : ℂ) • fun i => φ (fb i) := by
    have e1 : M⁻¹ *ᵥ (M *ᵥ (fun i => φ (fb i))) = fun i => φ (fb i) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    rw [hb, Matrix.mulVec_smul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hsb', one_smul]
  have hreal : star (M *ᵥ (fun i => φ (fa i))) = M *ᵥ (fun i => φ (fa i)) := by
    rw [ha]; funext j
    simp only [Pi.star_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbv : bvec (esI k r a) = (sa : ℂ) • (M *ᵥ (fun i => φ (fa i))) := by
    rw [ha, smul_smul, mul_inv_cancel₀ hsa', one_smul]
  set X : Fin (2 * r + k + 1) → ℂ := fun i => φ ((γ *ᵥ fb) i) with hX
  have h1 : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = (sb : ℂ) * (M *ᵥ X) (eI k r a) := by
    have : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) =
        ((M * γ.map φ * M⁻¹) *ᵥ bvec (esI k r b)) (eI k r a) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul,
      map_mulVec_comp, Matrix.mulVec_smul]
    rfl
  have h2 : (M *ᵥ X) (eI k r a) = (sa : ℂ) * (star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X)) := by
    rw [← Hpk_mulVec_esI k r a (M *ᵥ X)]
    have e2 : (Hpk k r *ᵥ (M *ᵥ X)) (esI k r a) = bvec (esI k r a) ⬝ᵥ (Hpk k r *ᵥ (M *ᵥ X)) := by
      simp [bvec]
    rw [e2, hbv, smul_dotProduct, smul_eq_mul, ← hreal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have h3 : star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X) = φ (form σ J (γ *ᵥ fb) fa) := by
    rw [hX, map_mulVec_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [form, dotProduct, map_sum, map_mul, hφ]
  rw [h1, h2, h3]
  push_cast; ring

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem corner_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD γ hγ p
  obtain ⟨hCM, -, hJ, hΛ, -, -, hlat, hA, hs, had⟩ := hD
  obtain ⟨-, -, -, hcc⟩ := hCM
  obtain ⟨-, hγΛ⟩ := hγ
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    change τ (σ (σ x)) = τ x
    rw [hcc, hcc, star_star]
  have hcol : ∀ (b : Fin r) (y : E), y ∈ (dInv E (r - (b : ℕ)))⁻¹ → y • (fun i => f i b) ∈ Λ := by
    intro b y hy
    refine hlat (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, y, ?_, ?_⟩)
    · simpa [id1] using hy
    · funext i; simp [sideM]
  have hmap : ∀ v ∈ Λ, γ *ᵥ v ∈ Λ := by
    intro v hv
    have : γ *ᵥ v ∈ latMap γ Λ := ⟨v, hv, rfl⟩
    rwa [hγΛ] at this
  have hc : form (σ : E →+* E) J (γ *ᵥ fun i => f i p.1.2) (fun i => f i p.1.1) ∈
      dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val) := by
    refine form_mem_dInv_mul (σ : E →+* E) hσ J Λ hΛ _ _ _ _ (fun y hy => ?_) (fun x hx => hcol _ x hx)
    rw [← Matrix.mulVec_smul]
    exact hmap _ (hcol _ y hy)
  refine ⟨_, hc, fun w => ?_⟩
  have hJ0 : J.det ≠ 0 := hJ.2
  have hφ : ∀ x, w.embedding ((σ : E →+* E) x) = star (w.embedding x) := fun x => hcc _ x
  have := corner_entry (σ : E →+* E) w.embedding hφ J hJ0 (A w) (hA w) γ p.1.1 p.1.2
    (fun i => f i p.1.1) (fun i => f i p.1.2) (s p.1.1) (s p.1.2) (hs _).ne' (hs _).ne'
    (had w p.1.1).2 (had w p.1.2).2
  simp only [gM]
  rw [this]

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  first | exact @GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat | exact GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat | (intros; apply GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat <;> assumption)
end
end

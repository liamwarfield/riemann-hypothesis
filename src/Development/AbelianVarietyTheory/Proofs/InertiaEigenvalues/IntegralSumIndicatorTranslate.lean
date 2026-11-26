module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealInducedCharacters.Induced
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CosetIntegral

theorem integral_sum_indicator_translate {G ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulRightInvariant] (H : Set G) (hH : IsOpen H) (hm : m H = 1) (T : Finset ι)
    (r : ι → G) (c : ι → ℂ) :
    ∫ x, ∑ q ∈ T, ((fun y => y * (r q)⁻¹) ⁻¹' H).indicator (fun _ => c q) x ∂m
      = ∑ q ∈ T, c q := by
  have hmeas : ∀ q, MeasurableSet ((fun y => y * (r q)⁻¹) ⁻¹' H) := fun q =>
    (hH.preimage (continuous_mul_const _)).measurableSet
  have hmq : ∀ q, m ((fun y => y * (r q)⁻¹) ⁻¹' H) = 1 := fun q => by
    rw [measure_preimage_mul_right, hm]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), measureReal_def, hmq q]
    simp
  · intro q _
    exact (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hmq q]; simp))

theorem integral_eq_of_coset_support
    (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R]
    [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] [Group S]
    [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S]
    (i : S →* R) (hi : Topology.IsClosedEmbedding i) (μ : Measure R) (ν : Measure S)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (R₀ : Subgroup R) (hR₀o : IsOpen (R₀ : Set R)) (_hR₀c : IsCompact (R₀ : Set R))
    (hμ : μ R₀ = 1) (hν : ν (i ⁻¹' R₀) = 1) (h : R → ℂ)
    (hinv : ∀ k ∈ R₀, ∀ g, h (k * g) = h g)
    (hsupp : ∀ g, h g ≠ 0 → ∃ k ∈ R₀, ∃ s, g = k * i s)
    (hcs : HasCompactSupport (fun s => h (i s))) :
    ∫ g, h g ∂μ = ∫ s, h (i s) ∂ν := by
  classical
  let S₀ : Subgroup S := R₀.comap i
  have hS₀o : IsOpen (i ⁻¹' (R₀ : Set R)) := hR₀o.preimage hi.continuous
  have hconst : ∀ g r, g * (i r)⁻¹ ∈ R₀ → h (i r) = h g := by
    intro g r hg
    have := hinv _ hg (i r)
    simpa using this.symm
  let U : S → Set S := fun s => (fun x => x * s⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))
  have hUo : ∀ s, IsOpen (U s) := fun s => hS₀o.preimage (continuous_mul_const _)
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover U hUo
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [U, R₀.one_mem]⟩)
  let mk : S → Quotient (QuotientGroup.rightRel S₀) := fun s => Quotient.mk _ s
  let T := t.image mk
  have hrel : ∀ a b : S, mk a = mk b ↔ i b * (i a)⁻¹ ∈ R₀ := fun a b => by
    simp only [mk, Quotient.eq, QuotientGroup.rightRel_apply, S₀, Subgroup.mem_comap,
      map_mul, map_inv]
  have hout : ∀ q, mk q.out = q := fun q => Quotient.out_eq q
  have hsuppT : ∀ x, h (i x) ≠ 0 → mk x ∈ T := by
    intro x hx
    have hx' : x ∈ tsupport (fun s => h (i s)) := subset_tsupport _ hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx')
    refine Finset.mem_image.2 ⟨s, hs, (hrel s x).2 ?_⟩
    simpa [U] using hxs
  have hrep : ∀ x, h (i (mk x).out) = h (i x) := by
    intro x
    apply hconst
    exact (hrel _ x).1 (hout _)

  have hR : (fun g => h g) = fun g => ∑ q ∈ T,
      ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R)).indicator (fun _ => h (i q.out)) g := by
    funext g
    by_cases hg : h g = 0
    · rw [hg]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hm : g ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))
      · rw [Set.indicator_of_mem hm, hconst g _ hm, hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨k, hk, s, rfl⟩ := hsupp g hg
      have hs : h (i s) ≠ 0 := by rwa [hinv k hk] at hg
      have hmem : ∀ q, (k * i s ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))) ↔ mk s = q := by
        intro q
        have e : mk s = q ↔ i s * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out s, hout q, eq_comm]
        rw [e]
        simp only [Set.mem_preimage, SetLike.mem_coe, mul_assoc]
        exact Subgroup.mul_mem_cancel_left R₀ hk
      simp only [Set.indicator, hmem, Finset.sum_ite_eq, if_pos (hsuppT s hs), hrep, hinv k hk]
  have hS : (fun x => h (i x)) = fun x => ∑ q ∈ T,
      ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))).indicator (fun _ => h (i q.out)) x := by
    funext x
    have hmem : ∀ q, x ∈ ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))) ↔ mk x = q := by
      intro q
      have e : mk x = q ↔ i x * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out x, hout q, eq_comm]
      rw [e]
      simp
    simp only [Set.indicator, hmem, Finset.sum_ite_eq]
    split_ifs with hx
    · rw [hrep]
    · by_contra hne
      exact hx (hsuppT x hne)
  rw [hR, hS, integral_sum_indicator_translate μ _ hR₀o hμ,
    integral_sum_indicator_translate ν _ hS₀o hν]

end GlobalTheory.CosetIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacter
open GlobalTheory.Published

noncomputable section

namespace GlobalTheory.InertiaEigenvalues

open BrauerSchur

theorem exists_transversal_index {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ t : Fin H.index → G, (∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) ∧ ∀ x, ∃ i, (t i)⁻¹ * x ∈ H := by
  classical
  let e : G ⧸ H ≃ Fin H.index := Finite.equivFin (G ⧸ H)
  refine ⟨fun i => (e.symm i).out, fun i j => ?_, fun x => ⟨e (x : G ⧸ H), ?_⟩⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq', e.symm.injective.eq_iff]
  · rw [← QuotientGroup.eq]
    simp only [Equiv.symm_apply_apply, QuotientGroup.out_eq']

theorem inducedRep_cyclic_trace (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ) :
    ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ),
      (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧
      ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = GlobalTheory.Published.indFun H (fun x => (χ x : ℂ)) g := by
  classical
  obtain ⟨t, ht, hc⟩ := exists_transversal_index H
  obtain ⟨i0, hi0⟩ := hc 1
  rw [mul_one] at hi0
  have hti0 : t i0 ∈ H := by simpa using H.inv_mem hi0
  have memiff : ∀ (k i : Fin H.index) (a : G), (t i)⁻¹ * a ∈ H → ((t k)⁻¹ * a * t i0 ∈ H ↔ k = i) := by
    intro k i a ha
    rw [← ht k i]
    constructor
    · intro hm
      have e : (t k)⁻¹ * t i = ((t k)⁻¹ * a * t i0) * (t i0)⁻¹ * ((t i)⁻¹ * a)⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm (H.inv_mem hti0)) (H.inv_mem ha)
    · intro hm
      have e : (t k)⁻¹ * a * t i0 = ((t k)⁻¹ * t i) * ((t i)⁻¹ * a) * t i0 := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm ha) hti0
  refine ⟨indRep H χ t ht hc, Pi.single i0 1, ?_, ?_, ?_⟩
  · intro σ
    ext k
    show Matrix.toLin' (indMat H χ t (σ : G)) (Pi.single i0 1) k = _
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
    have hσ : (t i0)⁻¹ * (σ : G) ∈ H := H.mul_mem hi0 σ.2
    by_cases hk : k = i0
    · subst hk
      rw [Pi.single_eq_same, mul_one, dot_conj H χ hti0 (σ : G)]
      unfold dot
      rw [dite_eq_left σ.2]
    · rw [Pi.single_eq_of_ne hk, mul_zero]
      unfold dot
      rw [dite_eq_right]
      rw [memiff k i0 _ hσ]
      exact hk
  · rw [eq_top_iff]
    have hsingle : ∀ i, Pi.single i (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun g => indRep H χ t ht hc g (Pi.single i0 1)) := by
      intro i
      have hti : (t i)⁻¹ * t i ∈ H := by simpa using H.one_mem
      have hval : indRep H χ t ht hc (t i) (Pi.single i0 1) = dot H χ (t i0) • Pi.single i (1 : ℂ) := by
        ext k
        show Matrix.toLin' (indMat H χ t (t i)) (Pi.single i0 1) k = _
        rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
        simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same, mul_one, inv_mul_cancel, one_mul]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
          unfold dot
          rw [dite_eq_right]
          rw [memiff k i _ hti]
          exact hk
      have hne : dot H χ (t i0) ≠ 0 := by
        unfold dot
        rw [dite_eq_left hti0]
        exact Units.ne_zero _
      have : Pi.single i (1 : ℂ) = (dot H χ (t i0))⁻¹ • indRep H χ t ht hc (t i) (Pi.single i0 1) := by
        rw [hval, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t i, rfl⟩)
    intro x _
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply, eq_comm]
    rw [e]; exact hsingle i
  · intro g
    rw [indRep_trace, ← indFun_eq_sum H χ t ht hc g]
    rfl

end GlobalTheory.InertiaEigenvalues

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacterStatement
open GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_representation_character : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ), (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧ ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = indFun H (fun x => (χ x : ℂ)) g := by
  first | exact @GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | exact GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | (intros; apply GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDcOfCover
noncomputable section

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

def dcSetoid (Γ K : Subgroup G) : Setoid G := GlobalTheory.DoubleCosetSetoid.doubleCosetSetoid Γ K

abbrev DC (Γ K : Subgroup G) : Type _ := Quotient (dcSetoid Γ K)

def stabCard (Γ K : Subgroup G) (t : G) : ℕ := Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}

def mass (Γ K : Subgroup G) : ℚ := ∑ᶠ c : DC Γ K, ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹

theorem finite_dc_of_le {Γ W K : Subgroup G} (hWK : W ≤ K) [Finite (DC Γ W)] : Finite (DC Γ K) := by
  let f : DC Γ W → DC Γ K := Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)
  refine Finite.of_surjective f ?_
  rintro ⟨x⟩
  exact ⟨Quotient.mk'' x, rfl⟩

theorem finite_dc_of_cover {Γ K : Subgroup G} (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ κ ∈ K, g = γ * t * κ) :
    Finite (DC Γ K) := by
  obtain ⟨T, hT⟩ := hT
  refine Finite.of_surjective (fun t : T => (Quotient.mk'' (t : G) : DC Γ K)) ?_
  rintro ⟨g⟩
  obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hT g
  refine ⟨⟨t, ht⟩, Quotient.sound' ⟨γ, hγ, κ, hκ, e⟩⟩

theorem stabCard_pos {Γ K : Subgroup G} (t : G) (h : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    0 < stabCard Γ K t := by
  haveI := h
  haveI : Nonempty {γ : Γ // t⁻¹ * (γ : G) * t ∈ K} := ⟨⟨1, by simp [K.one_mem]⟩⟩
  exact Nat.card_pos

theorem mass_pos {Γ K : Subgroup G} [Finite (DC Γ K)]
    (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) : 0 < mass Γ K := by
  haveI := Fintype.ofFinite (DC Γ K)
  rw [mass, finsum_eq_sum_of_fintype]
  have hne : (Finset.univ : Finset (DC Γ K)).Nonempty := ⟨Quotient.mk'' 1, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun c _ => ?_) hne
  have := stabCard_pos c.out (hfin c.out)
  positivity

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

theorem stabCard_eq {Γ K : Subgroup G} {t t' : G} (hr : (dcSetoid Γ K) t t') :
    stabCard Γ K t' = stabCard Γ K t := by
  obtain ⟨γ, hγ, κ, hκ, rfl⟩ := hr
  unfold stabCard
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨γ⁻¹ * (x.1 : G) * γ, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) x.1.2) hγ⟩, ?_⟩
      invFun := fun x => ⟨⟨γ * (x.1 : G) * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ x.1.2) (Γ.inv_mem hγ)⟩, ?_⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc] }
  · have := K.mul_mem (K.mul_mem hκ x.2) (K.inv_mem hκ)
    convert this using 1
    simp [mul_assoc]
  · have := K.mul_mem (K.mul_mem (K.inv_mem hκ) x.2) hκ
    convert this using 1
    simp [mul_assoc]

theorem stabCard_out (Γ K : Subgroup G) (x : G) :
    stabCard Γ K (Quotient.mk (dcSetoid Γ K) x).out = stabCard Γ K x :=
  (stabCard_eq (Quotient.mk_out (s := dcSetoid Γ K) x)).symm

theorem stabCard_conj (Γ K : Subgroup G) (h g : G) :
    stabCard Γ (K.map (MulAut.conj h).toMonoidHom) g = stabCard Γ K (g * h) := by
  unfold stabCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

def dcConj (Γ K : Subgroup G) (h : G) : DC Γ (K.map (MulAut.conj h).toMonoidHom) ≃ DC Γ K :=
  Quotient.congr (Equiv.mulRight h) (by
    intro a b
    constructor
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      rw [Subgroup.mem_map_equiv] at hκ
      refine ⟨γ, hγ, _, hκ, ?_⟩
      simp [e, MulAut.conj_symm_apply, mul_assoc]
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      refine ⟨γ, hγ, h * κ * h⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_map_equiv]
        simpa [MulAut.conj_symm_apply, mul_assoc] using hκ
      · have e' : b = γ * a * h * κ * h⁻¹ := by
          have := congrArg (· * h⁻¹) e
          simpa [mul_assoc] using this
        rw [e']
        simp [mul_assoc])

theorem mass_conj (Γ K : Subgroup G) (h : G) :
    mass Γ (K.map (MulAut.conj h).toMonoidHom) = mass Γ K := by
  unfold mass
  rw [← finsum_comp_equiv (dcConj Γ K h)]
  refine finsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h x =>
    have e1 : dcConj Γ K h (Quotient.mk _ x) = Quotient.mk (dcSetoid Γ K) (x * h) := rfl
    rw [e1, stabCard_out, stabCard_out, stabCard_conj]

end GlobalTheory.UnimodMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower
open GlobalTheory.PMonE Finset

namespace GlobalTheory.PMonE

theorem gsum_sub_of_charP {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] {m : Type*} [Fintype m]
    (e D : ℕ) (M : ℕ → Matrix m m F) (x y : m → F) :
    gsum (p ^ e) D M (x - y) = gsum (p ^ e) D M x - gsum (p ^ e) D M y := by
  unfold gsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simpa [pow_mul] using (sub_pow_char_pow (R := F) (p := p) (x i) (y i) (e * n))

theorem norm_gsum_le_of_small {F : Type*} [NormedField F] [IsUltrametricDist F] {m : Type*} [Fintype m]
    (q D : ℕ) (hq : 0 < q) (M : ℕ → Matrix m m F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ n, n ≤ D → ∀ i j, ‖M n i j‖ ≤ δ) (z : m → F) (hz : ‖z‖ ≤ 1) :
    ‖gsum q D M z‖ ≤ δ * ‖z‖ := by
  have h0 : 0 ≤ δ * ‖z‖ := mul_nonneg hδ (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  unfold gsum
  rw [Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun n hn => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun j _ => ?_
  rw [norm_mul, norm_pow]
  have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  refine mul_le_mul (hM n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) i j) ?_ (by positivity) hδ
  exact (pow_le_of_le_one (norm_nonneg _) (hj.trans hz) (pow_pos hq n).ne').trans hj

theorem gsum_eq_add_gsum_update {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
    (q D : ℕ) (U : ℕ → Matrix m m F) (y : m → F) :
    gsum q D U y = y + gsum q D (fun n => if n = 0 then U 0 - 1 else U n) y := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [Matrix.sub_mulVec]
  abel

theorem existsUnique_integral_gsum_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ) (_he : 0 < e)
    (U : ℕ → Matrix m m F) (h0 : ∀ i j, ‖(U 0 - 1) i j‖ < 1) (h1 : ∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1)
    (b : m → F) (hb : Integral b) : ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  set V : ℕ → Matrix m m F := fun n => if n = 0 then U 0 - 1 else U n with hV
  have hVs : ∀ n i j, ‖V n i j‖ < 1 := by
    intro n i j
    by_cases hn : n = 0
    · simpa [hV, hn] using h0 i j
    · simpa [hV, hn] using h1 n (Nat.one_le_iff_ne_zero.mpr hn) i j
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : NNReal, δ < 1 ∧ ∀ n, n ≤ D → ∀ i j, ‖V n i j‖ ≤ δ := by
    refine ⟨((range (D + 1)) ×ˢ (univ : Finset (m × m))).sup fun t => ‖V t.1 t.2.1 t.2.2‖₊, ?_, ?_⟩
    · rw [Finset.sup_lt_iff (by simp)]
      intro t _
      exact_mod_cast hVs t.1 t.2.1 t.2.2
    · intro n hn i j
      have := Finset.le_sup (f := fun t : ℕ × m × m => ‖V t.1 t.2.1 t.2.2‖₊)
        (s := (range (D + 1)) ×ˢ (univ : Finset (m × m))) (b := (n, i, j))
        (by simp [Nat.lt_succ_iff, hn])
      exact_mod_cast this
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hint : ∀ y : m → F, Integral y ↔ ‖y‖ ≤ 1 := fun y => (pi_norm_le_iff_of_nonneg zero_le_one).symm
  have hbound := norm_gsum_le_of_small (p ^ e) D hq V δ δ.2 hδ
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hsub : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ 1 := by
    intro x y hx hy
    rw [← hint] at *
    intro i
    rw [Pi.sub_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) ?_)
    rw [norm_neg]; exact hy i
  let T : (m → F) → (m → F) := fun y => b - gsum (p ^ e) D V y
  let S : Set (m → F) := Metric.closedBall 0 1
  have hS : ∀ y, y ∈ S ↔ ‖y‖ ≤ 1 := fun y => mem_closedBall_zero_iff
  have hT : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖T x - T y‖ ≤ δ * ‖x - y‖ := by
    intro x y hx hy
    have : T x - T y = - gsum (p ^ e) D V (x - y) := by
      rw [gsum_sub_of_charP]; simp only [T]; abel
    rw [this, norm_neg]
    exact hbound _ (hsub x y hx hy)
  have hmaps : Set.MapsTo T S S := by
    intro y hy
    rw [hS] at hy ⊢
    refine hsub _ _ ((hint b).mp hb) ((hbound y hy).trans ?_)
    exact mul_le_one₀ hδ1'.le (norm_nonneg _) hy
  have hc : ContractingWith δ (hmaps.restrict T S S) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hT x y ((hS _).mp x.2) ((hS _).mp y.2)
  have hfix : ∀ y, gsum (p ^ e) D U y = b ↔ T y = y := by
    intro y
    rw [gsum_eq_add_gsum_update]
    simp only [T]
    constructor
    · intro h; rw [← h]; simp [hV]
    · intro h; rw [sub_eq_iff_eq_add] at h; exact h.symm
  obtain ⟨y, hyS, hy, -⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps
    (x := 0) ((hS 0).mpr (by simp)) (edist_ne_top _ _)
  refine ⟨y, ⟨(hint y).mpr ((hS y).mp hyS), (hfix y).mpr hy⟩, ?_⟩
  rintro x ⟨hx, hx'⟩
  have h := hT x y ((hint x).mp hx) ((hS y).mp hyS)
  rw [(hfix x).mp hx', show T y = y from hy] at h
  have hn := norm_nonneg (x - y)
  have : ‖x - y‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → ∀ U : ℕ → Matrix m m F, (∀ i j, ‖(U 0 - 1) i j‖ < 1) → (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) → ∀ b : m → F, Integral b → ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  first | exact @GlobalTheory.PMonE.existsUnique_integral_gsum_eq | exact GlobalTheory.PMonE.existsUnique_integral_gsum_eq | (intros; apply GlobalTheory.PMonE.existsUnique_integral_gsum_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpace
open scoped ComplexConjugate

namespace GlobalTheory

lemma sesq_rules_of_combination {X : Type} (C : Submodule ℂ (X → ℂ)) (F : (X → ℂ) → (X → ℂ) → ℂ)
    (hl : ∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → F (a • f + f') g = star a * F f g + F f' g)
    (hr : ∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → F f (a • g + g') = a * F f g + F f g') :
    (∀ f f' g, f ∈ C → f' ∈ C → g ∈ C → F (f + f') g = F f g + F f' g) ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F (a • f) g = star a * F f g) ∧
    (∀ f g g', f ∈ C → g ∈ C → g' ∈ C → F f (g + g') = F f g + F f g') ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F f (a • g) = a * F f g) := by
  have l0 : ∀ g, g ∈ C → F 0 g = 0 := by
    intro g hg
    have := hl 1 0 0 g C.zero_mem C.zero_mem hg
    simp only [one_smul, add_zero, star_one, one_mul] at this
    linear_combination -this
  have r0 : ∀ f, f ∈ C → F f 0 = 0 := by
    intro f hf
    have := hr 1 f 0 0 hf C.zero_mem C.zero_mem
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f f' g hf hf' hg
    simpa using hl 1 f f' g hf hf' hg
  · intro a f g hf hg
    have := hl a f 0 g hf C.zero_mem hg
    rwa [add_zero, l0 g hg, add_zero] at this
  · intro f g g' hf hg hg'
    simpa using hr 1 f g g' hf hg hg'
  · intro a f g hf hg
    have := hr a f g 0 hf hg C.zero_mem
    rwa [add_zero, r0 f hf, add_zero] at this

theorem riesz_and_eigenvector_of_sesq_on_fun_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  intro X C hfin ip Φ hl hr hs hp Φl Φr
  haveI := hfin
  obtain ⟨ipa, ips, ipa', ips'⟩ := sesq_rules_of_combination C ip hl hr
  obtain ⟨Φa, Φs, Φa', Φs'⟩ := sesq_rules_of_combination C Φ Φl Φr
  let B : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun x y => ip (y : X → ℂ) x)
    (fun m₁ m₂ n => by simp only [Submodule.coe_add]; exact ipa' _ _ _ n.2 m₁.2 m₂.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]; exact ips' c _ _ n.2 m.2)
    (fun m n₁ n₂ => by simp only [Submodule.coe_add]; exact ipa _ _ _ n₁.2 n₂.2 m.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, smul_eq_mul, starRingEnd_apply]; exact ips c _ _ n.2 m.2)
  have Bsym : ∀ x y, B x y = conj (B y x) := by
    intro x y
    simp only [B, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply]
    exact hs _ _ x.2 y.2
  have Bpos : ∀ x, x ≠ 0 → 0 < (B x x).re := by
    intro x hx
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    exact hp _ x.2 (by rwa [ne_eq, Submodule.coe_eq_zero])
  let ipA : ℂ →ₗ[ℂ] ℂ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun a b => conj b * a) (by intros; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)
  have riesz : ∀ L : C →ₗ[ℂ] ℂ, ∃ x : C, ∀ y : C, ip (x : X → ℂ) y = L y := by
    intro L
    obtain ⟨x, hx, -⟩ := hermitian_adjoint_exists_unique ℂ C ipA B Bsym Bpos L 1
    exact ⟨x, fun y => by have := hx y; simpa [B, ipA] using this⟩
  refine ⟨?_, ?_⟩
  · intro f hf
    let L : C →ₗ[ℂ] ℂ :=
      { toFun := fun g => Φ f g
        map_add' := fun g g' => Φa' _ _ _ hf g.2 g'.2
        map_smul' := fun c g => Φs' c _ _ hf g.2 }
    obtain ⟨x, hx⟩ := riesz L
    exact ⟨x, x.2, fun g hg => hx ⟨g, hg⟩⟩
  · intro hC
    let large₂ : C → (C →ₗ[ℂ] ℂ) := fun g =>
      { toFun := fun f => star (Φ f g)
        map_add' := fun f f' => by
          simp only [Submodule.coe_add]; rw [Φa _ _ _ f.2 f'.2 g.2, star_add]
        map_smul' := fun c f => by
          simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
          rw [Φs c _ _ f.2 g.2, star_mul, star_star, mul_comm] }
    have hex : ∀ g : C, ∃ x : C, ∀ f : C, ip (f : X → ℂ) x = Φ f g := by
      intro g
      obtain ⟨x, hx⟩ := riesz (large₂ g)
      refine ⟨x, fun f => ?_⟩
      rw [hs _ _ x.2 f.2, hx f]
      simp [large₂]
    choose R hR using hex
    have inj : ∀ x y : C, (∀ f : C, ip (f : X → ℂ) x = ip f y) → x = y := by
      intro x y h
      by_contra hne
      have hd : ((x - y : C) : X → ℂ) = (-1 : ℂ) • (y : X → ℂ) + x := by
        rw [Submodule.coe_sub]; ext t; simp; ring
      have h1 := hr (-1) ((x - y : C) : X → ℂ) y x (x - y).2 y.2 x.2
      rw [← hd, h (x - y)] at h1
      have h2 := hp _ (x - y).2 (by rwa [ne_eq, Submodule.coe_eq_zero, sub_eq_zero])
      have h3 : ip ((x - y : C) : X → ℂ) ((x - y : C) : X → ℂ) = 0 := by rw [h1]; ring
      rw [h3] at h2
      simp at h2
    let Rl : Module.End ℂ C :=
      { toFun := R
        map_add' := fun g g' => inj _ _ (fun f => by
          rw [hR, Submodule.coe_add, Submodule.coe_add, ipa' _ _ _ f.2 (R g).2 (R g').2, hR, hR,
            Φa' _ _ _ f.2 g.2 g'.2])
        map_smul' := fun c g => inj _ _ (fun f => by
          rw [hR, Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul, ips' c _ _ f.2 (R g).2, hR,
            Φs' c _ _ f.2 g.2]) }
    haveI : Nontrivial C := Submodule.nontrivial_iff_ne_bot.mpr hC
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Rl
    obtain ⟨e, he⟩ := hc.exists_hasEigenvector
    refine ⟨c, e, e.2, by rw [ne_eq, Submodule.coe_eq_zero]; exact he.2, fun f hf => ?_⟩
    rw [← hR e ⟨f, hf⟩]
    show ip f ((Rl e : C) : X → ℂ) = _
    rw [he.apply_eq_smul, Submodule.coe_smul, ips' c _ _ hf e.2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpaceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  first | exact @GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | exact GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | (intros; apply GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAlgebraMapInjectiveOfCharZero
open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr

theorem padicInt_algebraMap_injective_of_charZero {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff hx0 : ℤ_[l])) :=
    (PadicInt.unitCoeff hx0).isUnit.map _
  have hp : (l : O) ^ x.valuation = 0 := (mul_eq_zero.1 hx).resolve_left hu.ne_zero
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) (pow_eq_zero_iff'.1 hp).1

theorem exists_eq_X_pow_mul_of_ne_zero {O : Type} [CommRing O] {a : O⟦X⟧} (ha : a ≠ 0) :
    ∃ (m : ℕ) (w : O⟦X⟧), a = X ^ m * w ∧ constantCoeff w ≠ 0 := by
  refine ⟨a.order.toNat, a.divXPowOrder, X_pow_order_mul_divXPowOrder.symm, ?_⟩
  rw [constantCoeff_divXPowOrder]
  exact coeff_order ha

theorem X_pow_card_dvd_of_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (a : O⟦X⟧)
    (h0 : constantCoeff a = 0) (ha : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a) :
    (X : O⟦X⟧) ^ Nat.card Δ ∣ a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact dvd_zero _
  obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero ha0
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [pow_zero, one_mul] at h0
      exact absurd h0 hw
    · exact h
  have hpow : ∀ δ ∈ Δ, (δ : ℤ_[l]) ^ m = 1 := by
    intro δ hδ
    obtain ⟨v, hv, hv0⟩ := exists_act_X (O := O) (δ : ℤ_[l])
    have e := ha δ hδ
    rw [map_mul, map_pow, hv, mul_pow, mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero m X_ne_zero) e
    have e'' := congrArg constantCoeff e'
    rw [map_mul, map_pow, hv0, constantCoeff_act] at e''
    have h1 : (algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m = 1 := by
      have h2 : ((algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m - 1) * constantCoeff w = 0 := by
        rw [sub_mul, one_mul, e'', sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hw)
    apply padicInt_algebraMap_injective_of_charZero O
    rw [map_pow, h1, map_one]
  have hexp : Monoid.exponent Δ ∣ m := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    apply Subtype.ext
    apply Units.ext
    simp [hpow g g.2]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact (pow_dvd_pow X (Nat.le_of_dvd hm hexp)).trans (dvd_mul_right _ _)

theorem X_pow_dvd_mk_sub_sum {O : Type} [CommRing O] (c : ℕ → O) (N : ℕ) :
    (X : O⟦X⟧) ^ N ∣ PowerSeries.mk c - ∑ k ∈ Finset.range N, C (c k) * X ^ k := by
  rw [X_pow_dvd_iff]
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, hm]

theorem injective_and_range_eq_invariants {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : Associated (j X) (X ^ Nat.card Δ))
    (hinv : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (j X) = j X) :
    Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a := by
  have hd : 0 < Nat.card Δ := Nat.card_pos
  obtain ⟨u, hu⟩ := hj
  have hjX0 : j X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact pow_ne_zero _ X_ne_zero hu.symm
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have e : j X = X ^ Nat.card Δ * ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact (dvd_pow_self (X : O⟦X⟧) hd.ne').mul_right _
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero hb0
    rw [map_mul, map_pow] at hb
    rcases mul_eq_zero.1 hb with h | h
    · exact pow_ne_zero m hjX0 h
    · apply hw
      rw [← constantCoeff_algHom j hXj w, h, map_zero]
  have hact : ∀ δ ∈ Δ, (act O (δ : ℤ_[l])).comp j = j := fun δ hδ =>
    algHom_ext_X _ _ (by rw [AlgHom.comp_apply, hinv δ hδ]; exact hXj)
      (by rw [AlgHom.comp_apply, hinv δ hδ])
  have hstep : ∀ q : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q) →
      ∃ q' : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q' = q') ∧
        q = C (constantCoeff q) + j X * q' := by
    intro q hq
    have h0 : constantCoeff (q - C (constantCoeff q)) = 0 := by simp
    have hi : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (q - C (constantCoeff q)) = q - C (constantCoeff q) := by
      intro δ hδ
      rw [map_sub, hq δ hδ, act_C]
    obtain ⟨r, hr⟩ := X_pow_card_dvd_of_invariant Δ _ h0 hi
    have hq' : q - C (constantCoeff q) = j X * (↑u * r) := by rw [hr, ← mul_assoc, hu]
    refine ⟨↑u * r, fun δ hδ => ?_, by rw [← hq']; ring⟩
    apply mul_left_cancel₀ hjX0
    rw [← hq', ← hinv δ hδ, ← map_mul, ← hq', hi δ hδ]
  choose f hf1 hf2 using hstep
  refine ⟨hinj, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ δ hδ
    exact DFunLike.congr_fun (hact δ hδ) b
  · intro ha
    let S := {q : O⟦X⟧ // ∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q}
    let nxt : S → S := fun q => ⟨f q.1 q.2, hf1 q.1 q.2⟩
    let sq : ℕ → S := fun n => nxt^[n] ⟨a, ha⟩
    let c : ℕ → O := fun k => constantCoeff (sq k).1
    have hexp : ∀ N, a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := by
      intro N
      induction N with
      | zero => simp [sq]
      | succ N ih =>
        have e1 : (sq (N + 1)).1 = f (sq N).1 (sq N).2 := by
          simp only [sq, Function.iterate_succ_apply']
          rfl
        have e2 : (sq N).1 = C (c N) + j X * (sq (N + 1)).1 := by
          rw [e1]
          exact hf2 _ _
        calc a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := ih
          _ = ∑ k ∈ Finset.range N, C (c k) * j X ^ k +
              j X ^ N * (C (c N) + j X * (sq (N + 1)).1) := by rw [← e2]
          _ = _ := by rw [Finset.sum_range_succ]; ring
    have hjsum : ∀ N, j (∑ k ∈ Finset.range N, C (c k) * X ^ k) =
        ∑ k ∈ Finset.range N, C (c k) * j X ^ k := by
      intro N
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, algHom_C]
    have hdvd : ∀ N, (X : O⟦X⟧) ^ N ∣ j (PowerSeries.mk c) - a := by
      intro N
      obtain ⟨r, hr⟩ := X_pow_dvd_mk_sub_sum c N
      have e3 : PowerSeries.mk c = ∑ k ∈ Finset.range N, C (c k) * X ^ k + X ^ N * r := by
        rw [← hr]
        ring
      have e4 : j (PowerSeries.mk c) - a = j X ^ N * (j r - (sq N).1) := by
        conv_lhs => rw [e3, map_add (f := _), map_mul, map_pow, hjsum, hexp N]
        ring
      rw [e4]
      exact (pow_dvd_pow_of_dvd hXj N).trans (dvd_mul_right _ _)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    have h' := (X_pow_dvd_iff.1 (hdvd (n + 1))) n (Nat.lt_succ_self n)
    rw [map_sub, sub_eq_zero] at h'
    exact h'

end GlobalTheory.CycFr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulPowOfMaximalIdealEqSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqPowMulUnit
namespace GlobalTheory.PowMulUnit

theorem exists_eq_pow_mul_unit {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hπ : IsLocalRing.maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ (0 : S)) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hex : ∃ n : ℕ, ¬ (π ^ n ∣ x) := by
    by_contra h0
    have h : ∀ n : ℕ, π ^ n ∣ x := fun n => not_not.mp (not_exists.mp h0 n)
    apply hx
    have hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal S ^ n := by
      refine Ideal.mem_iInf.mpr fun n => ?_
      rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [hK] at hmem
    exact hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec hex
    rw [h0, pow_zero] at h1
    exact h1 (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hdk : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_not.mp this
  obtain ⟨u, rfl⟩ := hdk
  refine ⟨k, u, ?_, rfl⟩
  by_contra hu
  have hum : u ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal u).mpr hu
  rw [hπ, Ideal.mem_span_singleton] at hum
  obtain ⟨w, rfl⟩ := hum
  apply Nat.find_spec hex
  rw [hk, pow_succ]
  exact ⟨w, by ring⟩

end GlobalTheory.PowMulUnit
end

open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem unit_mul_pow_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ 0) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  first
  | exact @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | (apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit ..)

theorem dvr_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) (hreg : ∀ a : S, π * a = 0 → a = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  have hpow : ∀ (k : ℕ) (a : S), π ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a h; simpa using h
    | succ k ih => intro a h; exact ih a (hreg _ (by rw [← h, pow_succ]; ring))
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨a, u, hu, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.1
    obtain ⟨b, v, hv, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.2
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy, pow_add]; ring
    exact (hu.mul hv).ne_zero (hpow _ _ this)
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hpr : (maximalIdeal S).IsPrincipal := ⟨⟨π, hm⟩⟩
  have hdvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 1 5).2 hpr
  exact ⟨inferInstance, hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩

end GlobalTheory.Pat
end

module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosets
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartLe
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartLe
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SplitCpt

theorem cptPart_le_self' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, -⟩
  exact ht

theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (x c : G) :
    c ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * c * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

theorem split_cpt : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  intro H _ _ _ _ σ K d d' _hσc hσ hKo hKc hσK hG y
  set T := twCent (swTw σ) (d, d') with hT
  set Cn := twCent (MonoidHom.id H) (d * σ d') with hCn
  have hKKc : IsCompact (((K.prod K).map (MulAut.conj y).toMonoidHom : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    exact (hKc.prod hKc).image (by
      show Continuous fun z : H × H => y * z * y⁻¹
      fun_prop)
  have hKKcl := hKKc.isClosed
  refine ⟨?_, ?_⟩
  · intro t ht
    apply Subgroup.subset_closure
    refine ⟨ht.1, hKKc.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun z hz => (Subgroup.zpowers_le.2 ht.2) hz) hKKcl
  · have hmapC : (cptPart T).map (MonoidHom.fst H H) ≤ cptPart Cn := by
      rw [Subgroup.map_le_iff_le_comap, cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      apply Subgroup.subset_closure
      refine ⟨((mem_twCent_swTw σ hσ d d' t).1 htT).1, ?_⟩
      have hC := htc.image continuous_fst
      refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    set x₃ : H := σ (d'⁻¹ * y.2) with hx₃
    set B : Subgroup H := (Cn ⊓ K.map (MulAut.conj y.1).toMonoidHom) ⊓ (Cn ⊓ K.map (MulAut.conj x₃).toMonoidHom) with hB
    have hB0 : B.relIndex (cptPart Cn) ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero (hG.2 y.1).2 (hG.2 x₃).2
    have hB1 : B.relIndex ((cptPart T).map (MonoidHom.fst H H)) ≠ 0 :=
      mt (Subgroup.relIndex_eq_zero_of_le_right hmapC) hB0
    have hB2 : (B.comap (MonoidHom.fst H H)).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.relIndex_comap]
    have hB3 : (B.comap (MonoidHom.fst H H) ⊓ cptPart T).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.inf_relIndex_right]
    have hle : B.comap (MonoidHom.fst H H) ⊓ cptPart T ≤
        T ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom := by
      rintro c ⟨hcB, hcC⟩
      have hcT : c ∈ T := cptPart_le_self' T hcC
      refine ⟨hcT, ?_⟩
      have h2 := ((mem_twCent_swTw σ hσ d d' c).1 hcT).2
      have hm1 : y.1⁻¹ * c.1 * y.1 ∈ K := (mem_map_conj K _ _).1 hcB.1.2
      have hm3 : x₃⁻¹ * c.1 * x₃ ∈ K := (mem_map_conj K _ _).1 hcB.2.2
      refine (mem_map_conj _ _ _).2 (Subgroup.mem_prod.2 ⟨hm1, ?_⟩)
      have hs := hσK _ hm3
      have e : (y⁻¹ * c * y).2 = σ (x₃⁻¹ * c.1 * x₃) := by
        simp only [Prod.snd_mul, Prod.snd_inv, h2, hx₃, map_mul, map_inv, hσ]
        group
      show (y⁻¹ * c * y).2 ∈ K
      rw [e]
      exact hs
    exact fun h0 => hB3 (Subgroup.relIndex_eq_zero_of_le_left hle h0)

end GlobalTheory.CompanionTheory.SplitCpt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartLeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_twist_compact_part_le : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SplitCpt.split_cpt | exact GlobalTheory.CompanionTheory.SplitCpt.split_cpt | (intros; apply GlobalTheory.CompanionTheory.SplitCpt.split_cpt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquiv
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.TransportLoc

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_iff (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d x : G) :
    x ∈ twCent θ d ↔ e x ∈ twCent θ' (e d) := by
  show x * d = d * θ x ↔ e x * e d = e d * θ' (e x)
  rw [← h, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem map_twConj (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d y : G) :
    e (y⁻¹ * d * θ y) = (e y)⁻¹ * e d * θ' (e y) := by
  simp only [map_mul, map_inv, h]

theorem twConj_mul (θ : G →* G) (d t w : G) (ht : t ∈ twCent θ d) :
    (t * w)⁻¹ * d * θ (t * w) = w⁻¹ * d * θ w := by
  have ht' : t * d = d * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc w⁻¹ * t⁻¹ * d * (θ t * θ w) = w⁻¹ * t⁻¹ * (d * θ t) * θ w := by group
    _ = w⁻¹ * d * θ w := by rw [← ht']; group

theorem finite_support (e : G ≃* G') (θ : G →* G) (θ' : G' →* G')
    (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ)
    (hθ : ∀ x, e (θ x) = θ' (e x)) (hK : ∀ x, x ∈ K ↔ e x ∈ K') (hf : ∀ x, f x = f' (e x))
    (hfin : {q : DoubleCoset.Quotient (twCent θ' (e d) : Set G') (K' : Set G') |
      ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * e d * θ' (Quotient.out q * k)) ≠ 0}.Finite) :
    {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
      ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite := by
  refine Set.Finite.of_injOn
    (f := fun q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) =>
      DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) ?_ ?_ hfin
  · rintro q ⟨k, hk, hne⟩
    obtain ⟨t, ht₀, k₁, hk₁, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e d)) K' (e (Quotient.out q))
    refine ⟨k₁⁻¹ * e k, K'.mul_mem (K'.inv_mem hk₁) ((hK k).1 hk), ?_⟩
    have hmul : Quotient.out (DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) *
        (k₁⁻¹ * e k) = t * e (Quotient.out q * k) := by
      rw [hout, map_mul]; group
    simp only []
    rw [hmul, twConj_mul θ' (e d) t _ ht₀, ← map_twConj e θ θ' hθ, ← hf]
    exact hne
  · intro q₁ _ q₂ _ heq
    obtain ⟨t', ht', k', hk', hy⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 heq
    have h₂ : Quotient.out q₂ = e.symm t' * Quotient.out q₁ * e.symm k' := by
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact hy
    have ht : e.symm t' ∈ twCent θ d := by
      rw [mem_twCent_iff e θ θ' hθ, e.apply_symm_apply]; exact ht'
    have hk : e.symm k' ∈ K := by
      rw [hK, e.apply_symm_apply]; exact hk'
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨_, ht, _, hk, h₂⟩

theorem index_ne_zero (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K')
    (u : K → ℂ) (u' : K' → ℂ) (hu : ∀ k : K, u k = u' ⟨e k, (hK k).1 k.2⟩)
    (h : (rStab u').index ≠ 0) : (rStab u).index ≠ 0 := by
  let φ : K →* K' :=
    { toFun := fun k => ⟨e k, (hK k).1 k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := fun k' =>
    ⟨⟨e.symm k', by rw [hK, e.apply_symm_apply]; exact k'.2⟩, by ext; simp [φ]⟩
  have hu' : ∀ k : K, u k = u' (φ k) := hu
  have hstab : rStab u = (rStab u').comap φ := by
    ext k
    constructor
    · intro hk x'
      obtain ⟨x, rfl⟩ := hφ x'
      show u' (φ x * φ k) = u' (φ x)
      rw [← map_mul, ← hu', ← hu']
      exact hk x
    · intro hk x
      show u (x * k) = u x
      rw [hu', hu', map_mul]
      exact hk (φ x)
  rw [hstab, Subgroup.index_comap_of_surjective _ hφ]
  exact h

theorem mem_conj_iff (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K') (y x : G) :
    x ∈ K.map (MulAut.conj y).toMonoidHom ↔ e x ∈ K'.map (MulAut.conj (e y)).toMonoidHom := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, (hK k).1 hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k', hk', h⟩
    refine ⟨e.symm k', by rw [SetLike.mem_coe, hK, e.apply_symm_apply]; exact hk', ?_⟩
    apply e.injective
    rw [← h]
    simp [MulAut.conj_apply]

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_iff (e : G ≃ₜ* G') (t : G) :
    IsCompact (closure (Subgroup.zpowers t : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
  have h : (Subgroup.zpowers (e t) : Set G') = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom t
    exact (congrArg (fun S : Subgroup G' => (S : Set G')) this).symm
  rw [h, ← e.toHomeomorph.image_closure, e.toHomeomorph.isCompact_image]

theorem map_cptPart (e : G ≃ₜ* G') (T : Subgroup G) (T' : Subgroup G') (hT : ∀ x, x ∈ T ↔ e x ∈ T') :
    (cptPart T).map e.toMulEquiv.toMonoidHom = cptPart T' := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext t'
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨(hT t).1 ht, (isCompact_closure_zpowers_iff e t).1 hc⟩
  · rintro ⟨ht', hc⟩
    refine ⟨e.symm t', ⟨?_, ?_⟩, e.apply_symm_apply t'⟩
    · rw [hT]; simpa using ht'
    · rw [isCompact_closure_zpowers_iff e]; simpa using hc

theorem locConds_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hθm : ∀ x, e.toMulEquiv (θ x) = θ' (e.toMulEquiv x) := hθ
  have hKm : ∀ x, x ∈ K ↔ e.toMulEquiv x ∈ K' := hK
  have hfm : ∀ x, f x = f' (e.toMulEquiv x) := hf
  have hT : ∀ x, x ∈ twCent θ d ↔ e.toMulEquiv x ∈ twCent θ' (e.toMulEquiv d) :=
    mem_twCent_iff e.toMulEquiv θ θ' hθm d
  refine ⟨?_, ?_, finite_support e.toMulEquiv θ θ' K K' d f f' hθm hKm hfm h₃, ?_⟩
  · intro x hx y hy
    apply e.toMulEquiv.injective
    rw [map_mul, map_mul]
    exact h₁ _ ((hT x).1 hx) _ ((hT y).1 hy)
  · intro y
    refine index_ne_zero e.toMulEquiv K K' hKm _ _ ?_ (h₂ (e y))
    intro k
    have := map_twConj e.toMulEquiv θ θ' hθm d (y * k)
    rw [hfm, this, map_mul]
    rfl
  · intro y
    obtain ⟨ha, hb⟩ := h₄ (e y)
    have hB := map_cptPart e (twCent θ d) (twCent θ' (e d)) hT
    have hA : twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom =
        (twCent θ' (e d) ⊓ K'.map (MulAut.conj (e y)).toMonoidHom).comap e.toMulEquiv.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_inf]
      exact and_congr (hT x) (mem_conj_iff e.toMulEquiv K K' hKm y x)
    constructor
    · rw [hA]
      intro x hx
      have hx' := ha hx
      rw [← hB] at hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      rwa [← e.toMulEquiv.injective hzx]
    · rw [hA, Subgroup.relIndex_comap, hB]
      exact hb

end GlobalTheory.CompanionTheory.TransportLoc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquivStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_conditions_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  first | exact @GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv | exact GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv | (intros; apply GlobalTheory.CompanionTheory.TransportLoc.locConds_of_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyOfSectionPlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyOfSectionPlaces
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSec

private theorem exists_heightOneSpectrum_under_maximalRealSubfield {E : Type} [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (Ideal.comap_bot_le_of_injective _ hinj)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  exact ⟨⟨Q, hQp, hQne⟩, HeightOneSpectrum.ext hQ⟩

theorem eventually_cofinite_of_section :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  intro E _ _ _ S hS P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  refine (hP.image fun w : {w : Pl E // w ∈ S} => w.1.under (𝓞 (maximalRealSubfield E))).subset ?_
  intro v hv
  obtain ⟨w₀, hw₀⟩ := exists_heightOneSpectrum_under_maximalRealSubfield v
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w₀
  exact ⟨⟨u, huS⟩, show ¬P (u.under _) by rw [hu, hw₀]; exact hv, hu.trans hw₀⟩

end GlobalTheory.CompanionTheory.LocHypSec
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyOfSectionPlacesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_of_section_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  first | exact @GlobalTheory.CompanionTheory.LocHypSec.eventually_cofinite_of_section | exact GlobalTheory.CompanionTheory.LocHypSec.eventually_cofinite_of_section | (intros; apply GlobalTheory.CompanionTheory.LocHypSec.eventually_cofinite_of_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionMeetsAbovePlace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionMeetsAbovePlace
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypAbove

theorem exists_above_mem_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)),
    IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  intro E _ _ _ S hS v
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [(show Ideal.under (𝓞 (maximalRealSubfield E)) (⊥ : Ideal (𝓞 E)) = ⊥ from
      Ideal.comap_bot_of_injective _ hinj)] at hQv
    exact v.ne_bot hQv.symm
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS (⟨Q, hQ, hQ0⟩ : Pl E)
  exact ⟨⟨u, huw.trans (HeightOneSpectrum.ext hQv)⟩, hu⟩

end GlobalTheory.CompanionTheory.LocHypAbove
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionMeetsAbovePlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_meets_above_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | exact GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | (intros; apply GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem eventually_val_le_one (E : Type) [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 E) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun w hw => ?_
  have hw' : ¬ Valued.v ((x : E) : w.adicCompletion E) ≤ 1 := hw
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', not_le] at hw'
  exact hw'

theorem ratW_mem_KGL_eventually (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hall : ∀ M : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j : Fin n,
      Valued.v (algebraMap E (w.adicCompletion E) ((M : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 := by
    intro M
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_val_le_one E _
  filter_upwards [hall δ, hall δ⁻¹] with w h1 h2
  rw [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  refine ⟨fun i j => h1 i j, fun i j => ?_⟩
  have key : (ratW n w δ)⁻¹ = ratW n w δ⁻¹ := (map_inv (ratW n w) δ).symm
  rw [key]
  exact h2 i j

end GlobalTheory.CompanionTheory.LocalHypotheses
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAllStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_element_integral_almost_all : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | exact GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitConditionsOfEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitConditionsOfEquiv
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitTransport

theorem unitConds_of_homeo : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  unfold GlobalTheory.CompanionTheory.LocalHypotheses.UnitConds at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, (hK d).2 h2, ?_, ?_⟩
  · funext x
    rw [hf x, h1]
    simp only [Set.indicator_apply, SetLike.mem_coe, hK x, Pi.one_apply]
  · unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    rw [SetLike.mem_coe, hK t]
    have hte : e t ∈ GlobalTheory.BCT.twCent θ' (e d) := by
      have htd : t * d = d * θ t := ht
      show e t * e d = e d * θ' (e t)
      rw [← hθ, ← map_mul e, ← map_mul e, htd]
    have hcl : closure (Subgroup.zpowers (e t) : Set G') =
        e '' closure (Subgroup.zpowers t : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        refine map_mem_closure e.symm.continuous hy ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [map_zpow, e.symm_apply_apply]⟩
      · rintro y ⟨x, hx, rfl⟩
        refine map_mem_closure e.continuous hx ?_
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow e t k).symm⟩
    have hce : IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
      rw [hcl]
      exact hc.image e.continuous
    unfold GlobalTheory.BCT.cptPart at h3
    exact h3 (Subgroup.subset_closure (And.intro hte hce))
  · intro y hy
    have hy' : (e y)⁻¹ * e d * θ' (e y) ∈ K' := by
      rw [← hθ, ← map_inv e, ← map_mul e, ← map_mul e]
      exact (hK _).1 hy
    obtain ⟨t', ht', k', hk', hyt⟩ := h4 (e y) hy'
    refine ⟨e.symm t', ?_, e.symm k', ?_, ?_⟩
    · show e.symm t' * d = d * θ (e.symm t')
      apply e.injective
      rw [map_mul, map_mul, hθ, e.apply_symm_apply]
      exact ht'
    · rw [hK, e.apply_symm_apply]
      exact hk'
    · apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hyt

end GlobalTheory.CompanionTheory.UnitTransport
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitConditionsOfEquivStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_conditions_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := by
  first | exact @GlobalTheory.CompanionTheory.UnitTransport.unitConds_of_homeo | exact GlobalTheory.CompanionTheory.UnitTransport.unitConds_of_homeo | (intros; apply GlobalTheory.CompanionTheory.UnitTransport.unitConds_of_homeo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfElliptic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfElliptic
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SepLocEl

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w) (x : E) :
    GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (GlobalTheory.SplitPts.conjE (E := E) k)) →
      GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [GlobalTheory.BCT.cj, dite_eq_left hex]
    exact hex.choose_spec.2 x
  have hinv : conjSrc (GlobalTheory.SplitPts.conjE (E := E))
      (conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w) = w := by
    apply (eq_conjSrc (fun x => ?_)).symm
    rw [← conjPl_conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w
      (GlobalTheory.SplitPts.conjE (E := E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)
  have hsrc : conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w = w := by
    by_contra hne
    apply hw
    refine ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2 ?_⟩
    right
    have h := conjPl_conjSrc (GlobalTheory.SplitPts.conjE (E := E))
      (conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w)
    rwa [hinv] at h
  exact key _ hsrc _
    (conjLoc_spec (GlobalTheory.SplitPts.conjE (E := E)) _).1 (conjLoc_spec (GlobalTheory.SplitPts.conjE (E := E)) _).2.1

theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases h : IsSplitAt w
  · simp only [nrmL, locEl, if_pos h]
  · simp only [nrmL, locEl, if_neg h]
    rw [map_mul]
    congr 1
    exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (GlobalTheory.BCT.cj w)
      (fun x => (cj_algebraMap h x).symm) δ).symm

theorem separable_charpoly_nrmL_locEl : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  intro _ E _ _ _ n w δ hδ
  rw [nrmL_locEl]
  have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val =
      (δ * thE E n δ).val.map (algebraMap E (w.adicCompletion E)) := rfl
  rw [e, Matrix.charpoly_map]
  exact Polynomial.Separable.map hδ.2.2.1

end GlobalTheory.CompanionTheory.SepLocEl

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfEllipticStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_charpoly_separable_of_elliptic : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
  (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  first | exact @GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | exact GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | (intros; apply GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypProof

theorem transport_loc : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := @GlobalTheory.T.local_conditions_of_equiv

theorem transport_unit : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → UnitConds θ' K' (e d) f' → UnitConds θ K d f := @GlobalTheory.T.unit_conditions_of_equiv

theorem split_index : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := @GlobalTheory.T.stabilizer_index_ne_zero

theorem split_fin : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := @GlobalTheory.T.finite_twisted_double_cosets

theorem split_cpt : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := @GlobalTheory.T.swap_twist_compact_part_le

theorem split_unit : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := @GlobalTheory.T.swap_twist_compact_part_in_prod

theorem inert_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := @GlobalTheory.T.nonsplit_place_pair_equiv

theorem split_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)), (∀ y, (e y).1 = evw w y) ∧
    (∀ y, e (thv a b v y) = swTw (sgP a b w.1) (e y)) ∧ (∀ y, y ∈ Kv a b v ↔ e y ∈ (K2 a b w.1).prod (K2 a b w.1)) ∧
    ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), e (pv a b v (ratF E a δ₁, ratF E b δ₂)) =
      ((ratW a w.1 δ₁, ratW b w.1 δ₂),
        (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
         ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂))) := @GlobalTheory.T.aux_statement_22

theorem sg_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
  Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧ ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := @GlobalTheory.T.pair_involution_continuous

theorem rat_mem : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := @GlobalTheory.T.rational_element_integral_almost_all

theorem cofinite_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := @GlobalTheory.T.eventually_of_section_places

theorem exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := @GlobalTheory.T.section_meets_above_place

theorem sep_locEl : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
  (nrmL n w (locEl n w δ)).val.charpoly.Separable := @GlobalTheory.T.norm_charpoly_separable_of_elliptic

theorem norm_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
  ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := @GlobalTheory.T.split_place_local_element

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fv_eq {S : Set (Pl E)} (hS : IsSection S) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (v : PlF E) (w : Above v)
    (hw : w.1 ∈ S) (y : Yv a b v) :
    fv S φ₁ φ₂ v y = φ₁ w.1 (evw w y) * if IsSplitAt w.1 then φ₂ w.1 (evw w (thv a b v y)) else 1 := by
  unfold fv
  rw [finprod_eq_single _ w, finprod_eq_if, if_pos hw]
  intro u hu
  have hn : u.1 ∉ S := by
    intro h
    apply hu
    apply Subtype.ext
    obtain ⟨z, -, hz⟩ := hS w.1
    have e : u.1.under (𝓞 (maximalRealSubfield E)) = w.1.under (𝓞 (maximalRealSubfield E)) := u.2.trans w.2.symm
    exact (hz _ ⟨h, e⟩).trans (hz _ ⟨hw, rfl⟩).symm
  rw [finprod_eq_if, if_neg hn]

theorem evw_pv_rat (v : PlF E) (w : Above v) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evw w (pv a b v (ratF E a δ₁, ratF E b δ₂)) = (ratW a w.1 δ₁, ratW b w.1 δ₂) := by
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_)) <;> rfl

theorem test_facts {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ K' : ∀ w : Pl E, Subgroup (GLw a w × GLw b w), (∀ w, IsOpen (K' w : Set (GLw a w × GLw b w))) ∧ (∀ w, K' w ≤ K2 a b w) ∧
      (∀ w, IsHecke (K' w) (φ w)) ∧ ∀ᶠ w in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ?_, fun w => ?_, h₃.1, h₃.2⟩
  · rw [Subgroup.coe_prod]
    exact ((h₁.1 w).1).prod ((h₂.1 w).1)
  · exact Subgroup.prod_mono (h₁.1 w).2.1 (h₂.1 w).2.1

theorem locConds_inert (hC : CjEx) (hU : Unr E) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (he₁ : polE δ₁ ∈ Ell E a) (he₂ : polE δ₂ ∈ Ell E b) (v : PlF E) (w : Above v) (hw : w.1 ∈ S) (hns : ¬ IsSplitAt w.1) :
    LocConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK⟩ := inert_iso hC E a b v w hns
  refine transport_loc e _ ((thL a w.1).prodMap (thL b w.1)) _ (K2 a b w.1) _ _ (φ₁ w.1) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_neg hns, mul_one, he]
  obtain ⟨K', hKo, hKle, hH, -⟩ := test_facts h₁
  have hloc : e (pv a b v (ratF E a δ₁, ratF E b δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) := by
    rw [he, evw_pv_rat]
    simp only [locEl, if_neg hns, ratW]
  rw [hloc]
  have s₁ := sep_locEl hC E a w.1 δ₁ he₁
  have s₂ := sep_locEl hC E b w.1 δ₂ he₂
  have hG := GlobalTheory.T.local_good_reduction E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂
  have hL := GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂
  obtain ⟨-, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w.1
  refine ⟨hG.1, fun y => split_index _ _ (K' w.1) _ (φ₁ w.1) (GlobalTheory.CompanionTheory.TwistOrbit.continuous_thPair hU a b w.1) hKc (hKo _)
    (hH w.1).2 y, ?_, hG.2⟩
  refine (hL.1 _ (hH w.1).1).subset ?_
  rintro q ⟨k, hk, hq⟩
  exact ⟨k, hk, subset_tsupport _ hq⟩

theorem split_all {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K K₁ K₂ : Subgroup H)
    (d d' : H) (f₁ f₂ : H → ℂ) (hσc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) (hσK : ∀ k ∈ K, σ k ∈ K)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) (hKo₁ : IsOpen (K₁ : Set H)) (hKo₂ : IsOpen (K₂ : Set H))
    (hH₁ : IsHecke K₁ f₁) (hH₂ : IsHecke K₂ f₂) (hG : PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d'))
    (hL : ∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) :
    LocConds (swTw σ) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) := by
  have hcomm : ∀ x ∈ twCent (swTw σ) (d, d'), ∀ y ∈ twCent (swTw σ) (d, d'), x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₁, e₁⟩ := (mem_twCent_swTw σ hσ d d' x).1 hx
    obtain ⟨y₁, e₂⟩ := (mem_twCent_swTw σ hσ d d' y).1 hy
    have c := hG.1 _ x₁ _ y₁
    refine Prod.ext c ?_
    show x.2 * y.2 = y.2 * x.2
    rw [e₁, e₂]
    have c' : σ x.1 * σ y.1 = σ y.1 * σ x.1 := by rw [← map_mul, c, map_mul]
    calc d' * σ x.1 * d'⁻¹ * (d' * σ y.1 * d'⁻¹) = d' * (σ x.1 * σ y.1) * d'⁻¹ := by group
      _ = d' * (σ y.1 * σ x.1) * d'⁻¹ := by rw [c']
      _ = _ := by group
  have hσc' : Continuous (swTw σ) := (hσc.comp continuous_snd).prodMk (hσc.comp continuous_fst)
  refine ⟨hcomm, ?_, ?_, split_cpt σ _ d d' hσc hσ hKo hKc hσK hG⟩
  · have hc2 : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
      rw [Subgroup.coe_prod]; exact hKc.prod hKc
    have ho2 : IsOpen ((K₁.prod (K₂.comap σ) : Subgroup (H × H)) : Set (H × H)) := by
      rw [Subgroup.coe_prod]; exact hKo₁.prod (hKo₂.preimage hσc)
    refine split_index (swTw σ) (K.prod K) (K₁.prod (K₂.comap σ)) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) hσc' hc2 ho2 ?_
    rintro ⟨k₁, k₂⟩ ⟨hk₁, hk₂⟩ ⟨x₁, x₂⟩
    have hk₂' : σ k₂ ∈ K₂ := hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(hH₁.2 k₁ hk₁ x₁).1, map_mul, (hH₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(hH₁.2 k₁ hk₁ x₁).2, map_mul, (hH₂.2 _ hk₂' _).2]
  · refine split_fin σ K d d' (fun y => f₁ y.1 * f₂ (σ y.2)) (tsupport f₁) (σ '' tsupport f₂) hσc hσ hKo hKc hσK hH₁.1 (hH₂.1.image hσc) ?_ hL
    intro y hy
    have h1 : f₁ y.1 ≠ 0 := left_ne_zero_of_mul hy
    have h2 : f₂ (σ y.2) ≠ 0 := right_ne_zero_of_mul hy
    exact ⟨subset_tsupport _ h1, σ y.2, subset_tsupport _ h2, hσ _⟩

theorem locConds_split (hC : CjEx) (hU : Unr E) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (he₁ : polE δ₁ ∈ Ell E a) (he₂ : polE δ₂ ∈ Ell E b) (v : PlF E) (w : Above v) (hw : w.1 ∈ S) (hs : IsSplitAt w.1) :
    LocConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK, hr⟩ := split_iso hC E a b v w hs
  obtain ⟨hσc, hσ, hσK⟩ := sg_facts E a b w.1
  refine transport_loc e _ (swTw (sgP a b w.1)) _ ((K2 a b w.1).prod (K2 a b w.1)) _ _
    (fun y => φ₁ w.1 y.1 * φ₂ w.1 (sgP a b w.1 y.2)) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_pos hs, ← he, ← he, hθ]
    rfl
  obtain ⟨K₁, hKo₁, -, hH₁, -⟩ := test_facts h₁
  obtain ⟨K₂, hKo₂, -, hH₂, -⟩ := test_facts h₂
  obtain ⟨hKo, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w.1
  rw [hr]
  have hN : (ratW a w.1 δ₁, ratW b w.1 δ₂) * sgP a b w.1 (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
    ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) :=
    Prod.ext (norm_split E a w.1 δ₁ hs) (norm_split E b w.1 δ₂ hs)
  have s₁ := sep_locEl hC E a w.1 δ₁ he₁
  have s₂ := sep_locEl hC E b w.1 δ₂ he₂
  have hG := GlobalTheory.T.local_good_reduction E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂
  have hL := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w.1 (locEl a w.1 δ₁, locEl b w.1 δ₂) s₁ s₂).1
  have hid : (thL a w.1).prodMap (thL b w.1) = MonoidHom.id _ := by
    have e₁ : thL a w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    have e₂ : thL b w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [e₁, e₂]
    rfl
  rw [hid, ← hN] at hG hL
  exact split_all _ _ (K₁ w.1) (K₂ w.1) _ _ _ _ hσc hσ hσK hKo hKc (hKo₁ _) (hKo₂ _) (hH₁ _) (hH₂ _) hG hL

theorem unitConds_inert (hC : CjEx) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (v : PlF E) (w : Above v)
    (hw : w.1 ∈ S) (hns : ¬ IsSplitAt w.1) (hφ : φ₁ w.1 = (K2 a b w.1 : Set (GLw a w.1 × GLw b w.1)).indicator 1)
    (hy : (locEl a w.1 δ₁, locEl b w.1 δ₂) ∈ K2 (E := E) a b w.1 ∧
      (∀ g : GLw a w.1 × GLw b w.1, g⁻¹ * (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) g ∈ K2 (E := E) a b w.1 →
        ∃ t ∈ twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂), t⁻¹ * g ∈ K2 (E := E) a b w.1) ∧
      cptPart (twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂)) ≤ K2 (E := E) a b w.1) :
    UnitConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK⟩ := inert_iso hC E a b v w hns
  refine transport_unit e _ ((thL a w.1).prodMap (thL b w.1)) _ (K2 a b w.1) _ _ (φ₁ w.1) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_neg hns, mul_one, he]
  have hloc : e (pv a b v (ratF E a δ₁, ratF E b δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) := by
    rw [he, evw_pv_rat]
    simp only [locEl, if_neg hns, ratW]
  rw [hloc]
  refine ⟨hφ, hy.1, hy.2.2, fun g hg => ?_⟩
  obtain ⟨t, ht, hk⟩ := hy.2.1 g hg
  exact ⟨t, ht, t⁻¹ * g, hk, by group⟩

theorem split_ind {H : Type} [Group H] (σ : H →* H) (K : Subgroup H) (hσ : ∀ g, σ (σ g) = g) (hσK : ∀ k ∈ K, σ k ∈ K)
    (f₁ f₂ : H → ℂ) (h₁ : f₁ = (K : Set H).indicator 1) (h₂ : f₂ = (K : Set H).indicator 1) :
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) = ((K.prod K : Subgroup (H × H)) : Set (H × H)).indicator 1 := by
  subst h₁ h₂
  funext y
  have e : σ y.2 ∈ K ↔ y.2 ∈ K := ⟨fun h => hσ y.2 ▸ hσK _ h, hσK _⟩
  by_cases c₁ : y.1 ∈ K <;> by_cases c₂ : y.2 ∈ K <;>
    simp [Set.indicator, Subgroup.mem_prod, c₁, c₂, e]

theorem unitConds_split (hC : CjEx) {S : Set (Pl E)} (hS : IsSection S)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (v : PlF E) (w : Above v)
    (hw : w.1 ∈ S) (hs : IsSplitAt w.1) (hφ₁ : φ₁ w.1 = (K2 a b w.1 : Set (GLw a w.1 × GLw b w.1)).indicator 1)
    (hφ₂ : φ₂ w.1 = (K2 a b w.1 : Set (GLw a w.1 × GLw b w.1)).indicator 1)
    (hd : (ratW a w.1 δ₁, ratW b w.1 δ₂) ∈ K2 (E := E) a b w.1)
    (hd' : (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
      ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)) ∈ K2 (E := E) a b w.1)
    (hy : (∀ g : GLw a w.1 × GLw b w.1, g⁻¹ * (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) g ∈ K2 (E := E) a b w.1 →
        ∃ t ∈ twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂), t⁻¹ * g ∈ K2 (E := E) a b w.1) ∧
      cptPart (twCent ((thL a w.1).prodMap (thL b w.1)) (locEl a w.1 δ₁, locEl b w.1 δ₂)) ≤ K2 (E := E) a b w.1) :
    UnitConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
  obtain ⟨e, he, hθ, hK, hr⟩ := split_iso hC E a b v w hs
  obtain ⟨hσc, hσ, hσK⟩ := sg_facts E a b w.1
  refine transport_unit e _ (swTw (sgP a b w.1)) _ ((K2 a b w.1).prod (K2 a b w.1)) _ _
    (fun y => φ₁ w.1 y.1 * φ₂ w.1 (sgP a b w.1 y.2)) hθ hK (fun x => ?_) ?_
  · rw [fv_eq hS φ₁ φ₂ v w hw, if_pos hs, ← he, ← he, hθ]
    rfl
  rw [hr]
  have hN : (ratW a w.1 δ₁, ratW b w.1 δ₂) * sgP a b w.1 (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
    ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)) = (locEl a w.1 δ₁, locEl b w.1 δ₂) :=
    Prod.ext (norm_split E a w.1 δ₁ hs) (norm_split E b w.1 δ₂ hs)
  have hid : (thL a w.1).prodMap (thL b w.1) = MonoidHom.id _ := by
    have e₁ : thL a w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    have e₂ : thL b w.1 = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [e₁, e₂]
    rfl
  rw [hid, ← hN] at hy
  obtain ⟨hc, hp⟩ := split_unit (sgP a b w.1) (K2 a b w.1) _ _ hσc hσ hσK hd hd' hy.2 hy.1
  exact ⟨split_ind _ _ hσ hσK _ _ hφ₁ hφ₂, ⟨hd, hd'⟩, hc, hp⟩

theorem locHyp : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  intro hC E _ _ _ hU a b S hS φ₁ φ₂ h₁ h₂ δ₁ δ₂ he₁ he₂
  have hloc : ∀ v : PlF E, LocConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
    intro v
    obtain ⟨w, hw⟩ := exists_above E S hS v
    by_cases hs : IsSplitAt w.1
    · exact locConds_split hC hU hS h₁ h₂ δ₁ δ₂ he₁ he₂ v w hw hs
    · exact locConds_inert hC hU hS h₁ δ₁ δ₂ he₁ he₂ v w hw hs
  have hunit : ∀ᶠ v : PlF E in cofinite,
      UnitConds (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) := by
    refine cofinite_sec E S hS _ ?_
    have hinj : Tendsto (Subtype.val : {w : Pl E // w ∈ S} → Pl E) cofinite cofinite :=
      Function.Injective.tendsto_cofinite Subtype.val_injective
    obtain ⟨-, -, -, -, t₁⟩ := test_facts h₁
    obtain ⟨-, -, -, -, t₂⟩ := test_facts h₂
    have c₁ := rat_mem E a δ₁
    have c₂ := rat_mem E b δ₂
    have c₃ := rat_mem E a (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁)
    have c₄ := rat_mem E b (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂)
    filter_upwards [hinj.eventually t₁, hinj.eventually t₂, hinj.eventually c₁, hinj.eventually c₂, hinj.eventually c₃,
      hinj.eventually c₄, GlobalTheory.T.unit_almost_everywhere_facts E hU a b S hS δ₁ δ₂ he₁ he₂] with w r₁ r₂ m₁ m₂ m₃ m₄ hy
    have hy' := hy _ rfl
    by_cases hs : IsSplitAt w.1
    · exact unitConds_split hC hS δ₁ δ₂ _ ⟨w.1, rfl⟩ w.2 hs r₁ r₂ ⟨m₁, m₂⟩ ⟨m₃, m₄⟩ hy'.2
    · exact unitConds_inert hC hS δ₁ δ₂ _ ⟨w.1, rfl⟩ w.2 hs r₁ hy'
  exact ⟨fun v => (hloc v).1, fun v y => (hloc v).2.1 y, fun v => (hloc v).2.2.1, fun v y => (hloc v).2.2.2 y, hunit⟩

end GlobalTheory.CompanionTheory.LocHypProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHoldStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hypotheses_hold : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  first | exact @GlobalTheory.CompanionTheory.LocHypProof.locHyp | exact GlobalTheory.CompanionTheory.LocHypProof.locHyp | (intros; apply GlobalTheory.CompanionTheory.LocHypProof.locHyp <;> assumption)
end

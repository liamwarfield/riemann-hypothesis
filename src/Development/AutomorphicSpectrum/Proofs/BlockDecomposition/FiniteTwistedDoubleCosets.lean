module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbedding

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosets
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosets
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSplit

theorem finite_of_subset_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩


open scoped Pointwise in
theorem finite_doubleCosets_split : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := by
  intro H _ _ _ σ K d d' f C₁ C₂ hσc hσ hKo hKc _ hC₁ hC₂ hf hfin
  open scoped Pointwise in
  have hC : IsCompact (C₁ * σ '' C₂) := hC₁.mul (hC₂.image hσc)
  have hSf := hfin _ hC
  set S := {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C₁ * σ '' C₂} with hS
  have hR : IsCompact ((fun q => Quotient.out q) '' S : Set H) := (hSf.image _).isCompact
  set A : Set H := ((fun q => Quotient.out q) '' S : Set H) * (K : Set H) with hAdef
  have hA : IsCompact A := hR.mul hKc
  set B : Set H := σ '' ((fun a => d⁻¹ * a) '' A * C₁) with hBdef
  have hB : IsCompact B := ((hA.image (continuous_const.mul continuous_id)).mul hC₁).image hσc
  have hKKo : IsOpen ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hKo
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hD : IsCompact ((fun p : (H × H) × (H × H) => p.1 * p.2⁻¹) ''
      ((A ×ˢ B) ×ˢ ((K.prod K : Subgroup (H × H)) : Set (H × H)))) :=
    ((hA.prod hB).prod hKKc).image (continuous_fst.mul continuous_snd.inv)
  have key : ∀ y₁ y₂ : H, y₁⁻¹ * d * σ y₂ ∈ C₁ → y₂⁻¹ * d' * σ y₁ ∈ C₂ →
      ∃ t ∈ twCent (swTw σ) (d, d'), ∃ a ∈ A, ∃ b ∈ B, ((y₁, y₂) : H × H) = t * (a, b) := by
    intro y₁ y₂ h₁ h₂
    have hN : y₁⁻¹ * (d * σ d') * y₁ ∈ C₁ * σ '' C₂ := by
      refine Set.mem_mul.2 ⟨_, h₁, _, ⟨_, h₂, rfl⟩, ?_⟩
      simp only [map_mul, map_inv, hσ]
      group
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) (d * σ d')) K y₁
    have ez : Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁) * k⁻¹ = h * y₁ := by
      rw [e, mul_inv_cancel_right]
    have hh' : h * (d * σ d') = d * σ d' * h := hh
    have hq : DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁ ∈ S := by
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [ez, MonoidHom.id_apply]
      have : (h * y₁)⁻¹ * (d * σ d') * (h * y₁) = y₁⁻¹ * (d * σ d') * y₁ := by
        rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (d * σ d') h y₁, ← hh']
        group
      rw [this]; exact hN
    have hw : h * y₁ ∈ A := by
      rw [← ez]
      exact Set.mem_mul.2 ⟨_, ⟨_, hq, rfl⟩, _, inv_mem hk, rfl⟩
    have ht := (mem_twCent_swTw σ hσ d d' (h⁻¹, d' * σ h⁻¹ * d'⁻¹)).2 ⟨inv_mem hh, rfl⟩
    set t₂ := d' * σ h⁻¹ * d'⁻¹ with ht₂
    have e₁ : h⁻¹ * d = d * σ t₂ := congrArg Prod.fst ht
    have e₂ : d⁻¹ * h * d = (σ t₂)⁻¹ := by
      have : σ t₂ = d⁻¹ * (h⁻¹ * d) := by rw [e₁]; group
      rw [this]; group
    refine ⟨(h⁻¹, t₂), ht, h * y₁, hw, t₂⁻¹ * y₂,
      ⟨(d⁻¹ * (h * y₁)) * (y₁⁻¹ * d * σ y₂), Set.mem_mul.2 ⟨_, ⟨_, hw, rfl⟩, _, h₁, rfl⟩, ?_⟩, ?_⟩
    · have : d⁻¹ * (h * y₁) * (y₁⁻¹ * d * σ y₂) = (d⁻¹ * h * d) * σ y₂ := by group
      rw [this, e₂, map_mul, map_inv, hσ, hσ]
    · ext <;> simp
  refine finite_of_subset_mul (twCent (swTw σ) (d, d')) (K.prod K) hKKo _ hD
    (fun x => ∃ k ∈ K.prod K, f ((x * k)⁻¹ * (d, d') * swTw σ (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, a, ha, b, hb, e⟩ := key (x * k).1 (x * k).2 (hf _ hx).1 (hf _ hx).2
  have e' : x * k = t * (a, b) := e
  refine ⟨t, ht, (a, b) * k⁻¹, ⟨(((a, b)), k), ⟨⟨ha, hb⟩, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e', mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.LocHypSplit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosetsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_twisted_double_cosets : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.LocHypSplit.finite_doubleCosets_split | exact GlobalTheory.CompanionTheory.LocHypSplit.finite_doubleCosets_split | (intros; apply GlobalTheory.CompanionTheory.LocHypSplit.finite_doubleCosets_split <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluing
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.OneStepProof

open GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem subset_hull (S : Set (Sm E N)) : S ⊆ (hull S : Submodule ℂ (Sm E N)) := by
  intro φ hφ
  refine (Submodule.mem_sInf).2 ?_
  rintro U ⟨hS, -⟩
  exact hS hφ

theorem hull_le {S : Set (Sm E N)} {U : Submodule ℂ (Sm E N)} (hS : S ⊆ U) (hU : _root_.GlobalTheory.CuspRep.IsStable U) : hull S ≤ U :=
  sInf_le ⟨hS, hU⟩

theorem hull_ne_bot {S : Set (Sm E N)} {φ : Sm E N} (hφ : φ ∈ S) (h0 : φ ≠ 0) : hull S ≠ ⊥ := by
  intro h
  have h1 : φ ∈ (hull S : Submodule ℂ (Sm E N)) := subset_hull S hφ
  rw [h] at h1
  exact h0 ((Submodule.mem_bot ℂ).1 h1)

theorem exists_ne_of_hull {S : Set (Sm E N)} (hst : _root_.GlobalTheory.CuspRep.IsStable (hull S)) (T : Sm E N →ₗ[ℂ] Sm E N)
    (he : ∀ o, ∀ χ ∈ hull S, T (act o χ) = act o (T χ)) {ψ : Sm E N} (hψ : ψ ∈ hull S) (hT : T ψ ≠ 0) :
    ∃ φ ∈ S, T φ ≠ 0 := by
  by_contra hcon
  have hz : ∀ φ ∈ S, T φ = 0 := by
    intro φ hφ
    by_contra h
    exact hcon ⟨φ, hφ, h⟩
  have hK : _root_.GlobalTheory.CuspRep.IsStable (hull S ⊓ LinearMap.ker T) := by
    intro o χ hχ
    refine Submodule.mem_inf.2 ⟨hst o χ hχ.1, ?_⟩
    have h0 : T χ = 0 := LinearMap.mem_ker.1 hχ.2
    rw [LinearMap.mem_ker, he o χ hχ.1, h0, map_zero]
  have hS : S ⊆ (hull S ⊓ LinearMap.ker T : Submodule ℂ (Sm E N)) := fun φ hφ =>
    Submodule.mem_inf.2 ⟨subset_hull S hφ, LinearMap.mem_ker.2 (hz φ hφ)⟩
  exact hT (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (hull_le hS hK hψ)).2)

theorem sm_ne_zero {φ : Sm E N} {x : GA E N} (h : φ.1 x ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h rfl

theorem oneStep_of_parts : PairSlices → PairRestrict → PairFD → SliceType → PairStep₁ → PairStep₂ → HullGen → CapEquiv →
    OneStep := by
  intro hSl hRe hFD hST hP₁ hP₂ hHG hCE
  intro E _ _ _ a b ι _ K₁ K₂ W₁ W₂ Θ₁ Θ₂ Ω₁ Ω₂ f m₁ m₂ hW₁ hW₂ hF₁ hF₂ hf hT hs₁ hs₂ hA₁ hA₂ hN₁ hN₂ hC₁ hC₂ hI₁ hI₂
    hD₁ hD₂ hP
  obtain ⟨fd₁, fd₂⟩ := hFD E a b ι _ _ f hP
  have ty₁ : ∀ φ ∈ slices₁ f, TypeB K₁ W₁ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).1 φ m h
  have ty₂ : ∀ φ ∈ slices₂ f, TypeB K₂ W₂ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).2 φ m h
  obtain ⟨st₁, fg₁⟩ := hHG E a K₁ W₁ _ ty₁ fd₁
  obtain ⟨st₂, fg₂⟩ := hHG E b K₂ W₂ _ ty₂ fd₂

  have hU₁ : hull (slices₁ f) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    obtain ⟨φ, hφ⟩ := hs₁ i x.2
    refine hull_ne_bot (φ := φ) ⟨i, x.2, hφ⟩ (sm_ne_zero (x := x.1) ?_)
    rw [hφ]
    exact hx
  obtain ⟨t₁, T₁, r₁, g₁, l₁, e₁, i₁, ψ, hψ, hTψ⟩ :=
    hF₁ _ st₁ hA₁ fg₁ hN₁ hC₁ (fun τ => ⟨m₁ τ, hI₁ τ, hD₁ τ⟩) hU₁
  obtain ⟨φ, ⟨i₀, y, hφ⟩, hTφ⟩ := exists_ne_of_hull st₁ T₁ e₁ hψ hTψ
  obtain ⟨G₁ne, G₁p, G₁t, G₁h⟩ := hP₁ E a b ι K₁ K₂ W₁ W₂ _ t₁.space _ T₁ f hW₁ hW₂ st₁ e₁ i₁ hP hT
    ⟨i₀, y, φ, hφ, hTφ⟩

  have hsl : ∀ i m, sl₂ (ap₁ T₁ (f i)) m ∈ hull (slices₂ f) ∧
      (sl₂ (ap₁ T₁ (f i)) m).1 = fun x => ap₁ T₁ (f i) (m, x) :=
    fun i m => (hSl E a b _ _ _ (G₁p i)).2 m
  have hss : slices₂ (fun i => ap₁ T₁ (f i)) ⊆ (hull (slices₂ f) : Submodule ℂ (Sm E b)) := by
    rintro χ ⟨i, m, h⟩
    have hχ : χ = sl₂ (ap₁ T₁ (f i)) m := Subtype.ext (h.trans (hsl i m).2.symm)
    rw [hχ]
    exact (hsl i m).1
  have hle : hull (slices₂ fun i => ap₁ T₁ (f i)) ≤ hull (slices₂ f) := hull_le hss st₂
  have ty₂' : ∀ χ ∈ slices₂ (fun i => ap₁ T₁ (f i)), TypeB K₂ W₂ χ := by
    rintro χ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ _ (G₁t i)).2 χ m h
  obtain ⟨st₂', fg₂'⟩ := hHG E b K₂ W₂ _ ty₂' (hFD E a b ι _ _ _ G₁p).2
  have G₁p' : ∀ i, ap₁ T₁ (f i) ∈ pairSpace t₁.space (hull (slices₂ fun i => ap₁ T₁ (f i))) := fun i =>
    hRe E a b _ _ _ _ (G₁p i) fun m χ h => subset_hull _ ⟨i, m, h⟩
  have hU₂ : hull (slices₂ fun i => ap₁ T₁ (f i)) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 G₁ne
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    refine hull_ne_bot (φ := sl₂ (ap₁ T₁ (f i)) x.1) ⟨i, x.1, (hsl i x.1).2⟩ (sm_ne_zero (x := x.2) ?_)
    rw [(hsl i x.1).2]
    exact hx

  obtain ⟨t₂, T₂, r₂, g₂, l₂, e₂, i₂, ψ', hψ', hTψ'⟩ :=
    hF₂ _ st₂' (fun χ hχ => hA₂ χ (hle hχ)) fg₂' (fun χ hχ => hN₂ χ (hle hχ))
      (by
        obtain ⟨z, hz, h⟩ := hC₂
        exact ⟨z, hz, fun χ hχ => h χ (hle hχ)⟩)
      (fun τ => ⟨m₂ τ, ⟨(hI₂ τ).1, fun u χ hχ => (hI₂ τ).2 u χ (hle hχ)⟩, hD₂ τ⟩) hU₂
  obtain ⟨χ, ⟨i₃, y₃, hχ⟩, hTχ⟩ := exists_ne_of_hull st₂' T₂ e₂ hψ' hTψ'
  obtain ⟨Gne, Gp, Gt, Gh⟩ := hP₂ E a b ι K₁ K₂ W₁ W₂ _ _ t₂.space T₂ (fun i => ap₁ T₁ (f i)) hW₁ hW₂ st₂' e₂ i₂ G₁p' G₁t
    ⟨i₃, y₃, χ, hχ, hTχ⟩
  exact ⟨t₁, t₂, fun i => ap₂ T₂ (ap₁ T₁ (f i)), T₁ ψ, T₂ ψ', r₁, r₂, g₁, g₂, l₁, l₂, Gne, Gp, Gt,
    fun h c e => Gh h c (G₁h h c e), i₁ ψ hψ, hTψ,
    hCE E a _ T₁ ψ m₁ st₁ e₁ hψ (fun τ u => (hI₁ τ).2 u ψ hψ),
    i₂ ψ' hψ', hTψ',
    hCE E b _ T₂ ψ' m₂ st₂' e₂ hψ' (fun τ u => (hI₂ τ).2 u ψ' (hle hψ'))⟩

end GlobalTheory.CompanionTheory.EGlue.OneStepProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluingStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.single_gluing : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairRestrict → GlobalTheory.CompanionTheory.EGlue.PairFD → GlobalTheory.CompanionTheory.EGlue.SliceType → GlobalTheory.CompanionTheory.EGlue.PairStep₁ → GlobalTheory.CompanionTheory.EGlue.PairStep₂ → GlobalTheory.CompanionTheory.EGlue.HullGen → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.OneStep := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts | exact GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts | (intros; apply GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinates
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (n : ℕ) :
    HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n) where
  toFun b w := ⟨matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w, by
    refine mem_hermC.2 ?_
    ext a c
    simp only [Matrix.conjTranspose_apply, matC, RCLike.star_def]
    rw [← hconj, b.2 a c]⟩
  invFun G := ⟨fun a c => Θ.symm fun w => (G w : Matrix (Fin n) (Fin n) ℂ) a c, by
    intro a c
    apply Θ.injective
    funext w
    have h : (G w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 (G w).2
    rw [hconj]
    simp only [RingEquiv.apply_symm_apply]
    have := congrFun (congrFun h a) c
    simpa [Matrix.conjTranspose_apply] using this⟩
  left_inv b := by
    apply Subtype.ext
    ext a c
    simp [matC]
  right_inv G := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]
  map_add' b b' := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]

theorem continuous_hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n) := by
  refine continuous_pi fun w => Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  have h1 : Continuous fun b : HermR (Ainf F) σ n =>
      (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact (continuous_apply w).comp (hΘ.comp h1)

theorem continuous_hermEquiv_symm (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ.symm) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n).symm := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  refine hΘ.comp (continuous_pi fun w => ?_)
  have h1 : Continuous fun b : hermC n => (b : Matrix (Fin n) (Fin n) ℂ) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact h1.comp (continuous_apply w)

theorem continuous_symm (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    Continuous Θ.symm := by
  have e : (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) = (hΘ.homeomorph Θ).symm := by
    funext y
    apply (hΘ.homeomorph Θ).injective
    rw [Homeomorph.apply_symm_apply]
    exact Θ.apply_symm_apply y
  rw [e]
  exact (hΘ.homeomorph Θ).symm.continuous

theorem topAddGroup_tens (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    IsTopologicalAddGroup (Ainf F ⊗[F] E) := by
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · have : (fun p : (Ainf F ⊗[F] E) × (Ainf F ⊗[F] E) => p.1 + p.2) =
        fun p => Θ.symm (Θ p.1 + Θ p.2) := by
      funext p; simp
    rw [this]
    exact c2.comp ((c1.comp continuous_fst).add (c1.comp continuous_snd))
  · have : (fun x : Ainf F ⊗[F] E => -x) = fun x => Θ.symm (-Θ x) := by
      funext x; simp
    rw [this]
    exact c2.comp c1.neg

theorem exists_hermEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  intro F E _ _ _ _ _ σ _ e τ Θ hc n
  obtain ⟨hΘ, hconj, -, -⟩ := hc
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  haveI := topAddGroup_tens Θ hΘ
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  have h1 := continuous_hermEquiv σ Θ hconj c1 n
  have h2 := continuous_hermEquiv_symm σ Θ hconj c2 n
  refine ⟨hermEquiv σ Θ hconj n, fun b w => rfl, fun ν hν => ⟨?_, fun G hG => ?_⟩⟩
  · exact AddEquiv.isAddHaarMeasure_map ν (hermEquiv σ Θ hconj n) h1 h2
  · exact hG.comp_measurable h1.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinatesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLatticeMemIffEntries
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sum_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    x = ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] b k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]

theorem coord_sig {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E)
    (x : R ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ x) l =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k *
        (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] σ (b k)) l := by
  have h : sigR R σ x =
      ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] σ (b k)) := by
    conv_lhs => rw [sum_coord (R := R) b x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [sigR]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

variable [FiniteDimensional F E]

theorem trace_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) x =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k * algebraMap F R (Algebra.trace F E (b k)) := by
  conv_lhs => rw [sum_coord (R := R) b x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, GlobalTheory.LatVac.trace_tmul, one_mul, smul_eq_mul]

theorem trace_tmul_one {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (x : R ⊗[F] E) :
    (Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x + sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), TensorProduct.add_tmul, hx, hy, map_add (f := _)]
    abel
  | tmul a e =>
    have h1 : (a * algebraMap F R (Algebra.trace F E e)) ⊗ₜ[F] (1 : E) =
        a ⊗ₜ[F] algebraMap F E (Algebra.trace F E e) := by
      rw [mul_comm, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have h2 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [GlobalTheory.LatVac.trace_tmul, h1, hσ, TensorProduct.tmul_add, h2]

theorem half_trace_tmul {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (h2 : (2 : F) ≠ 0) (x : R ⊗[F] E)
    (hx : sigR R σ x = x) :
    (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', trace_tmul_one σ hσ, hx, ← two_smul F x, smul_smul,
    one_div, inv_mul_cancel₀ h2, one_smul]

end Loc

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem latH_iff_at {d : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e)
    (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ)
    (h2 : (2 : F) ≠ 0)
    (hh : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F)
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k ∈
      v.adicCompletionIntegers F)
    (hs : ∀ i k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] σ (b i)) k ∈
      v.adicCompletionIntegers F)
    (ht : ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F)
    (Y : HermR (Fv F v) σ n) :
    Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈
        (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  constructor
  · rintro ⟨hd, ho⟩ a i k
    rcases lt_trichotomy a i with h | h | h
    · exact ho a i h k
    · subst h
      have e := half_trace_tmul (R := Fv F v) σ hσ h2 ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) (Y.2 a a)
      have e2 : (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k =
          (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) *
          (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k := by
        conv_lhs => rw [← e]
        have e3 : (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) ⊗ₜ[F] (1 : E) =
            (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) • ((1 : Fv F v) ⊗ₜ[F] (1 : E)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e3, map_smul, Finsupp.smul_apply, smul_eq_mul]
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k ∈ v.adicCompletionIntegers F
      rw [e2]
      exact mul_mem (hd a) (h1 k)
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) k ∈ v.adicCompletionIntegers F
      have e : sigR (Fv F v) σ ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i a) =
          (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i := Y.2 a i
      rw [← e, coord_sig]
      exact sum_mem fun l _ => mul_mem (ho i a h l) (hs l k)
  · intro h
    refine ⟨fun i => ?_, fun i j _ k => h i j k⟩
    rw [trace_coord b]
    exact mul_mem hh (sum_mem fun l _ => mul_mem (h i i l) (ht l))

end Place

theorem latH_iff_latV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔ (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM n d b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  obtain ⟨I1, I2⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hT : ∀ k, ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F := by
    intro k
    by_cases h0 : Algebra.trace F E (b k) = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · filter_upwards [I2 _ h0] with v hv
      exact hv.le
  filter_upwards [I2 (1 / 2) (by norm_num), I1 1, Filter.eventually_all.2 fun i => I1 (σ (b i)),
    Filter.eventually_all.2 hT] with v hh h1 hs ht Y
  exact latH_iff_at σ (GlobalTheory.CMTrace.trace_eq hCM) b v n two_ne_zero hh.le h1 hs ht Y

end GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrable
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain
open scoped HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.WhitFree.CoefLim

theorem repr_map {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis A b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_linear (L : (R ⊗[F] E) →ₗ[R] R) : Continuous L := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (a c : Fin n) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c :=
  (continuous_id.matrix_elem a c).comp continuous_subtype_val

theorem continuous_trace_pair [FiniteDimensional F E] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) := by
  have h : (fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))))) =
      fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => ∑ a, ∑ c, (Algebra.trace R (R ⊗[F] E) ∘ₗ LinearMap.mulLeft R (T a c))
        ((B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a) := by
    funext B
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, Matrix.mul_apply, map_sum]
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
    (continuous_linear _).comp (continuous_entry σ c a)

end Cont

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_intH_iff (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    B ∈ intH σ b S ↔ ∀ v, v ∉ S → ∀ a i k, (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (a i : Fin n) (k : Fin d),
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr
        (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i)) a i) k =
      (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v := by
    intro v a i k
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin]
    rw [repr_map, repr_map]
    rfl
  simp only [intH, HeckeCharacterZeroLocus.SiegelWeilU.latV, Set.mem_setOf_eq, key]

theorem measurableSet_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intH (n := n) σ b S) := by
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : intH (n := n) σ b S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, ⋂ a : Fin n, ⋂ i : Fin n,
      ⋂ k : Fin d, {B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n | (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F} := by
    ext B
    simp only [mem_intH_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) := Valued.isOpen_valuationSubring _
  have hev : Continuous fun y : HeckeCharacterZeroLocus.SiegelWeilU.Af F => y v := RestrictedProduct.continuous_eval v
  have hsnd : Continuous (fun c : HeckeCharacterZeroLocus.SiegelWeilU.AF F => HeckeCharacterZeroLocus.SiegelWeilU.sndA F c) := continuous_snd
  have hc : Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v :=
    hev.comp (hsnd.comp ((continuous_linear (Finsupp.lapply k ∘ₗ
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr.toLinearMap)).comp (continuous_entry σ a i)))
  exact (hO.preimage hc).measurableSet

theorem eventually_mem_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop, B ∈ intH σ b S := by
  have hfin : ∀ (a i : Fin n) (k : Fin d), {v : HeightOneSpectrum (𝓞 F) |
      ¬ (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F}.Finite :=
    fun a i k => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)).2
  have hall : ∀ (a i : Fin n) (k : Fin d), ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop,
      ∀ v, v ∉ S → (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
    intro a i k
    filter_upwards [Filter.eventually_ge_atTop (hfin a i k).toFinset] with S hS v hv
    by_contra hcon
    exact hv (hS ((hfin a i k).mem_toFinset.2 hcon))
  have hall' := Filter.eventually_all.2 fun a : Fin n => Filter.eventually_all.2 fun i : Fin n =>
    Filter.eventually_all.2 fun k : Fin d => hall a i k
  filter_upwards [hall'] with S hS
  exact (mem_intH_iff σ b S B).2 fun v hv a i k => hS a i k v hv

end Adelic

theorem coefS_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ ψ hψ dx db d b Φ hI T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : Continuous fun B : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp ((continuous_const.mul (continuous_trace_pair σ _)).neg)
  have hf := hI.aestronglyMeasurable.mul hchar.aestronglyMeasurable
  unfold coefS coefN
  refine tendsto_integral_filter_of_dominated_convergence (fun B => ‖starN σ J ψ dx Φ B‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable ((intH (n := n) σ b S).indicator (fun _ => (1 : ℂ))) :=
      measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun B => ?_
    have h1 : ‖(intH (n := n) σ b S).indicator (fun _ => (1 : ℂ)) B‖ ≤ 1 := by
      by_cases h : B ∈ intH (n := n) σ b S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun B => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_intH σ b B] with S hS
    simp only [Set.indicator_of_mem hS, one_mul]
    rfl

end GlobalTheory.CompanionTheory.WhitFree.CoefLim
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrableStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_stabilizer_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto <;> assumption)
end
end

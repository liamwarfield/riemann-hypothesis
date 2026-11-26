module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosets
open GlobalTheory.BCT

namespace GlobalTheory.ConjRegroup

theorem finsum_fibres {H C : Type} (p : H → C) (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x := by
  classical
  have h1 : ∀ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x
      = ∑ x ∈ ha.toFinset, if c = p x then a x else 0 := by
    intro c
    rw [finsum_eq_sum_of_support_subset (s := ha.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp [Set.indicator_apply, eq_comm]
    · intro x hx
      have : a x ≠ 0 := fun h => hx (by simp [Set.indicator_apply, h])
      simpa using this
  simp_rw [h1]
  rw [finsum_sum_comm]
  · rw [finsum_eq_sum a ha]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [finsum_eq_single _ (p x)]
    · simp
    · intro c hc
      simp [hc]
  · intro x _
    refine (Set.finite_singleton (p x)).subset ?_
    intro c hc
    by_contra h
    exact hc (if_neg h)

theorem mk_eq_iff {H : Type} [Group H] (x y : H) :
    (Quot.mk _ x : TwCl (MonoidHom.id H)) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * g := by
  have he : Equivalence fun x y : H => ∃ g, y = g⁻¹ * x * (MonoidHom.id H) g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  exact Quot.eq.trans he.eqvGen_iff

theorem conj_injective {H : Type} [Group H] (r : H) :
    Function.Injective fun δ : H ⧸ twCent (MonoidHom.id H) r =>
      Quotient.out δ * r * (Quotient.out δ)⁻¹ := by
  intro δ ε h
  rw [← QuotientGroup.out_eq' δ, ← QuotientGroup.out_eq' ε, QuotientGroup.eq]
  change (Quotient.out δ)⁻¹ * Quotient.out ε * r = r * ((Quotient.out δ)⁻¹ * Quotient.out ε)
  simp only at h
  calc (Quotient.out δ)⁻¹ * Quotient.out ε * r
      = (Quotient.out δ)⁻¹ * (Quotient.out ε * r * (Quotient.out ε)⁻¹) * Quotient.out ε := by group
    _ = r * ((Quotient.out δ)⁻¹ * Quotient.out ε) := by rw [← h]; group

theorem range_conj {H : Type} [Group H] (c : TwCl (MonoidHom.id H)) :
    Set.range (fun δ : H ⧸ twCent (MonoidHom.id H) c.rep =>
      Quotient.out δ * c.rep * (Quotient.out δ)⁻¹)
      = {x | (Quot.mk _ x : TwCl (MonoidHom.id H)) = c} := by
  have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id H)) = c := Quot.out_eq c
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨δ, rfl⟩
    refine Eq.trans ?_ hc
    rw [mk_eq_iff]
    exact ⟨Quotient.out δ, by group⟩
  · intro h
    obtain ⟨g, hg⟩ := (mk_eq_iff x c.rep).1 (h.trans hc.symm)
    refine ⟨QuotientGroup.mk g, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (twCent (MonoidHom.id H) c.rep) g
    have hk2 : (k : H) * c.rep = c.rep * k := k.2
    rw [hk]
    calc g * k * c.rep * (g * k)⁻¹ = g * (k * c.rep) * (g * k)⁻¹ := by group
      _ = g * c.rep * g⁻¹ := by rw [hk2]; group
      _ = x := by rw [hg]; group

theorem finsum_eq_finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  rw [finsum_fibres (fun x => (Quot.mk _ x : TwCl (MonoidHom.id H))) a ha]
  refine finsum_congr fun c => ?_
  rw [← finsum_mem_def, ← range_conj c, finsum_mem_range (conj_injective (TwCl.rep c))]

end GlobalTheory.ConjRegroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosetsStatement
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets : ∀ {H : Type} [Group H] (a : H → ℂ), (Function.support a).Finite → ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  first | exact @GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | exact GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | (intros; apply GlobalTheory.ConjRegroup.finsum_eq_finsum_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroup
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.ClassSumUnfold

open Function

theorem finsum_eq_of_fiber {α β : Type} (Φ : α → β) (hΦ : Surjective Φ) (w : α → ℂ) (g : β → ℂ)
    (hfib : ∀ b, (Φ ⁻¹' {b}).Finite) (hw : (support w).Finite)
    (hwg : ∀ a, w a * ((Φ ⁻¹' {Φ a}).ncard : ℂ) = g (Φ a)) : ∑ᶠ a, w a = ∑ᶠ b, g b := by
  classical
  have hn : ∀ a, ((Φ ⁻¹' {Φ a}).ncard : ℂ) ≠ 0 := fun a => by
    have : 0 < (Φ ⁻¹' {Φ a}).ncard := (Set.ncard_pos (hfib _)).2 ⟨a, rfl⟩
    exact_mod_cast this.ne'
  have hw' : ∀ a, w a = g (Φ a) / ((Φ ⁻¹' {Φ a}).ncard : ℂ) := fun a => by
    rw [← hwg a, mul_div_cancel_right₀ _ (hn a)]
  set s := hw.toFinset with hs
  have hgs : support g ⊆ ↑(s.image Φ) := by
    intro b hb
    obtain ⟨a, rfl⟩ := hΦ b
    have : w a ≠ 0 := by
      intro h0; apply hb; rw [← hwg a, h0, zero_mul]
    rw [Finset.coe_image]
    exact ⟨a, by simpa [s] using this, rfl⟩
  rw [finsum_eq_sum_of_support_subset w (s := s) (by simp [s]), finsum_eq_sum_of_support_subset g hgs,
    ← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := s.image Φ) (fun i hi => Finset.mem_image_of_mem Φ hi)]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨a0, -, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.sum_congr rfl (fun a ha => by rw [hw' a, (Finset.mem_filter.1 ha).2]), Finset.sum_const, nsmul_eq_mul]
  by_cases hg : g (Φ a0) = 0
  · simp [hg]
  · have hfe : s.filter (fun a => Φ a = Φ a0) = (hfib (Φ a0)).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, s,
        Function.mem_support]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [hw' a, h]
        exact div_ne_zero hg (by simpa [h] using hn a)
    rw [hfe, ← Set.ncard_eq_toFinset_card _ (hfib _)]
    field_simp [hn a0]

end GlobalTheory.ClassSumUnfold

namespace GlobalTheory.ClassSumUnfold

open Function

variable {G H : Type} [Group G] [Group H]

theorem mem_conj_iff (K : Subgroup G) (x g : G) :
    g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem fiber_count (ι : H →* G) (hι : Injective ι) (Γ : Subgroup G) (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g)
    (T : Subgroup H) (Γ' : Subgroup G) (hΓ' : ∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) (K : Subgroup G) (x : G)
    (hfin : Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) (δ₀ : H ⧸ T) :
    ((fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * x)) ⁻¹'
        {DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * x)}).Finite ∧
    ((fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * x)) ⁻¹'
        {DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * x)}).ncard *
      Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out
        (DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * x)))).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  classical
  have hT : ∀ h, h ∈ T ↔ ι h ∈ Γ' := fun h => by
    rw [hΓ']
    exact ⟨fun h' => ⟨h, h', rfl⟩, fun ⟨t, ht, e⟩ => hι e ▸ ht⟩
  have hιΓ : ∀ h, ι h ∈ Γ := fun h => (hΓ _).2 ⟨h, rfl⟩
  have hΓ'Γ : ∀ g, g ∈ Γ' → g ∈ Γ := fun g hg => by
    obtain ⟨t, -, rfl⟩ := (hΓ' g).1 hg
    exact hιΓ t
  set S : Subgroup H := (Γ ⊓ K.map (MulAut.conj x).toMonoidHom).comap ι with hSdef
  have hS : ∀ h, h ∈ S ↔ x⁻¹ * ι h * x ∈ K := fun h => by
    simp only [hSdef, Subgroup.mem_comap, Subgroup.mem_inf, mem_conj_iff]
    exact ⟨fun h' => h'.2, fun h' => ⟨hιΓ h, h'⟩⟩
  have hcardS : Nat.card S = Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
    rw [← Subgroup.card_map_of_injective (K := S) hι, hSdef, Subgroup.map_comap_eq]
    congr 2
    refine inf_eq_right.2 (fun g hg => ?_)
    obtain ⟨h, rfl⟩ := (hΓ g).1 (Subgroup.mem_inf.1 hg).1
    exact ⟨h, rfl⟩
  haveI : Finite S := Nat.finite_of_card_ne_zero (hcardS ▸ (Nat.card_pos).ne')
  set h₀ := Quotient.out δ₀ with hh₀
  have hδ₀ : ((h₀ : H) : H ⧸ T) = δ₀ := QuotientGroup.out_eq' δ₀
  have hsm : ∀ s : S, s • δ₀ = (((s : H) * h₀ : H) : H ⧸ T) := fun s => by
    rw [← hδ₀]
    first
    | rfl
    | simp [Subgroup.smul_def, MulAction.Quotient.smul_mk]
  have hfo : (fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * x)) ⁻¹'
      {DoubleCoset.mk Γ' K ((ι h₀)⁻¹ * x)} = MulAction.orbit S δ₀ := by
    ext δ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · intro he
      obtain ⟨g', hg', k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ' K _ _).1 he
      obtain ⟨t, ht, rfl⟩ := (hΓ' g').1 hg'
      have e' : (ι h₀)⁻¹ = ι t * ((ι (Quotient.out δ))⁻¹ * x) * k * x⁻¹ := by
        rw [← e]; group
      have hsK : x⁻¹ * ι (Quotient.out δ * t⁻¹ * h₀⁻¹) * x = k := by
        simp only [map_mul, map_inv]
        rw [e']; group
      refine ⟨⟨Quotient.out δ * t⁻¹ * h₀⁻¹, (hS _).2 (hsK ▸ hk)⟩, ?_⟩
      rw [hsm]
      conv_rhs => rw [← QuotientGroup.out_eq' δ]
      rw [QuotientGroup.eq]
      have : (Quotient.out δ * t⁻¹ * h₀⁻¹ * h₀)⁻¹ * Quotient.out δ = t := by group
      simp only [this]
      exact ht
    · rintro ⟨s, rfl⟩
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T ((s : H) * h₀)
      rw [hsm, ht, DoubleCoset.eq]
      refine ⟨ι t, (hT t).1 t.2, x⁻¹ * ι s * x, (hS s).1 s.2, ?_⟩
      simp only [map_mul, map_inv]
      group
  obtain ⟨g', hg', k, hk, hy⟩ := DoubleCoset.mk_out_eq_mul Γ' K ((ι h₀)⁻¹ * x)
  set y := Quotient.out (DoubleCoset.mk Γ' K ((ι h₀)⁻¹ * x)) with hydef
  set a := g' * (ι h₀)⁻¹ with hadef
  let φ : S →* G := (MulAut.conj a).toMonoidHom.comp (ι.comp S.subtype)
  have hφ : ∀ s : S, φ s = a * ι s * a⁻¹ := fun s => rfl
  have hφi : Injective φ := by
    intro s s' e
    rw [hφ, hφ] at e
    exact Subtype.ext (hι (by simpa using e))
  have hstab : ∀ s : S, s ∈ MulAction.stabilizer S δ₀ ↔ ι ((s : H) * h₀)⁻¹ * ι h₀ ∈ Γ' := fun s => by
    rw [MulAction.mem_stabilizer_iff, hsm]
    conv_lhs => rw [← hδ₀]
    rw [QuotientGroup.eq, hT, map_mul]
  have hmap : (MulAction.stabilizer S δ₀).map φ = Γ' ⊓ K.map (MulAut.conj y).toMonoidHom := by
    ext z
    rw [Subgroup.mem_inf, mem_conj_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' := (hstab s).1 hs
      have hsK := (hS s).1 s.2
      constructor
      · have : φ s = g' * (ι ((s : H) * h₀)⁻¹ * ι h₀)⁻¹ * g'⁻¹ := by
          rw [hφ]; simp only [hadef, map_mul, map_inv]; group
        rw [this]
        exact Γ'.mul_mem (Γ'.mul_mem hg' (Γ'.inv_mem hs')) (Γ'.inv_mem hg')
      · have : y⁻¹ * φ s * y = k⁻¹ * (x⁻¹ * ι s * x) * k := by
          rw [hφ, hy]; simp only [hadef]; group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem hk) hsK) hk
    · rintro ⟨hz1, hz2⟩
      have hΓz : a⁻¹ * z * a ∈ Γ := by
        simp only [hadef]
        exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (Γ.mul_mem (hΓ'Γ _ hg') (Γ.inv_mem (hιΓ h₀)))) (hΓ'Γ _ hz1))
          (Γ.mul_mem (hΓ'Γ _ hg') (Γ.inv_mem (hιΓ h₀)))
      obtain ⟨s, hs⟩ := (hΓ _).1 hΓz
      have hsS : s ∈ S := by
        rw [hS, hs]
        have : x⁻¹ * (a⁻¹ * z * a) * x = k * (y⁻¹ * z * y) * k⁻¹ := by
          rw [hy]; simp only [hadef]; group
        rw [this]
        exact K.mul_mem (K.mul_mem hk hz2) (K.inv_mem hk)
      refine ⟨⟨s, hsS⟩, (hstab _).2 ?_, ?_⟩
      · have : ι (s * h₀)⁻¹ * ι h₀ = g'⁻¹ * z⁻¹ * g' := by
          simp only [map_mul, map_inv]
          rw [hs]; simp only [hadef]; group
        rw [this]
        exact Γ'.mul_mem (Γ'.mul_mem (Γ'.inv_mem hg') (Γ'.inv_mem hz1)) hg'
      · rw [hφ]
        show a * ι s * a⁻¹ = z
        rw [hs]; group
  have hcst : Nat.card (MulAction.stabilizer S δ₀) = Nat.card ↥(Γ' ⊓ K.map (MulAut.conj y).toMonoidHom) := by
    rw [← hmap, Subgroup.card_map_of_injective hφi]
  refine ⟨?_, ?_⟩
  · rw [hfo]
    exact Set.finite_range _
  · rw [hfo, ← hcst, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index, hcardS]

end GlobalTheory.ClassSumUnfold

namespace GlobalTheory.ClassSumUnfold

open Function

theorem unfold_classSum : ∀ {G H : Type} [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h, ι h = g) → ∀ (T : Subgroup H) (Γ' : Subgroup G), (∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) → ∀ (K : Subgroup G) (u : G → ℂ), (∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g) → Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) → (∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) → ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) = ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) := by
  intro G H _ _ ι hι Γ hΓ T Γ' hΓ' K u hu hfinQ hfinS hsupp
  classical
  haveI := hfinQ
  have hιΓ : ∀ h, ι h ∈ Γ := fun h => (hΓ _).2 ⟨h, rfl⟩
  have hu' : ∀ g' ∈ Γ', ∀ k ∈ K, ∀ g, u (g' * g * k) = u g := by
    intro g' hg' k hk g
    obtain ⟨t, ht, rfl⟩ := (hΓ' g').1 hg'
    exact hu t ht k hk g
  let Φ : DoubleCoset.Quotient (Γ : Set G) (K : Set G) × (H ⧸ T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun p => DoubleCoset.mk Γ' K ((ι (Quotient.out p.2))⁻¹ * Quotient.out p.1)
  let w : DoubleCoset.Quotient (Γ : Set G) (K : Set G) × (H ⧸ T) → ℂ := fun p =>
    ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out p.1)).toMonoidHom) : ℂ))⁻¹ *
      u ((ι (Quotient.out p.2))⁻¹ * Quotient.out p.1)
  have hwfin : (support w).Finite := by
    refine ((Set.finite_univ (α := DoubleCoset.Quotient (Γ : Set G) (K : Set G))).prod
      (Set.finite_iUnion (fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) => hsupp (Quotient.out q)))).subset ?_
    rintro ⟨q, δ⟩ hp
    refine ⟨Set.mem_univ _, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    exact right_ne_zero_of_mul hp
  have hπ : ∀ q q' δ δ', Φ (q', δ) = Φ (q, δ') → q' = q := by
    intro q q' δ δ' h
    obtain ⟨g', hg', k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ' K _ _).1 h
    have hΓ'Γ : g' ∈ Γ := by
      obtain ⟨t, -, rfl⟩ := (hΓ' g').1 hg'
      exact hιΓ t
    rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' q', DoubleCoset.eq]
    refine ⟨ι (Quotient.out δ') * g' * (ι (Quotient.out δ))⁻¹,
      Γ.mul_mem (Γ.mul_mem (hιΓ _) hΓ'Γ) (Γ.inv_mem (hιΓ _)), k, hk, ?_⟩
    have e' : Quotient.out q = ι (Quotient.out δ') * (g' * ((ι (Quotient.out δ))⁻¹ * Quotient.out q') * k) := by
      rw [← e]; group
    rw [e']; group
  have hsurj : Surjective Φ := by
    intro b
    obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K (Quotient.out b)
    obtain ⟨h, rfl⟩ := (hΓ γ).1 hγ
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T h
    refine ⟨(DoubleCoset.mk Γ K (Quotient.out b), (h : H ⧸ T)), ?_⟩
    show DoubleCoset.mk Γ' K ((ι (Quotient.out (h : H ⧸ T)))⁻¹ * Quotient.out (DoubleCoset.mk Γ K (Quotient.out b))) = b
    rw [ht, e]
    conv_rhs => rw [← DoubleCoset.out_eq' b]
    rw [DoubleCoset.eq]
    refine ⟨ι t, (hΓ' _).2 ⟨t, t.2, rfl⟩, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [map_mul]
    group
  have hfib_eq : ∀ q δ₀, Φ ⁻¹' {Φ (q, δ₀)} = (fun δ => (q, δ)) ''
      ((fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * Quotient.out q)) ⁻¹'
        {DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q)}) := by
    intro q δ₀
    ext ⟨q', δ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro h
      have hq := hπ q q' δ δ₀ h
      subst hq
      exact ⟨δ, h, rfl⟩
    · rintro ⟨δ', hδ', he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hδ'
  calc _ = ∑ᶠ p, w p := by
        rw [finsum_curry w hwfin]
        refine finsum_congr fun q => ?_
        rw [mul_finsum]
    _ = _ := by
      refine finsum_eq_of_fiber Φ hsurj w
        (fun b => ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out b)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out b))
        ?_ hwfin ?_
      · intro b
        obtain ⟨⟨q, δ₀⟩, rfl⟩ := hsurj b
        rw [hfib_eq]
        exact (fiber_count ι hι Γ hΓ T Γ' hΓ' K (Quotient.out q) (hfinS _) δ₀).1.image _
      · rintro ⟨q, δ₀⟩
        rw [hfib_eq, Set.ncard_image_of_injective _ (fun d d' e => by simpa using e)]
        obtain ⟨-, hc⟩ := fiber_count ι hι Γ hΓ T Γ' hΓ' K (Quotient.out q) (hfinS _) δ₀
        haveI := hfinS (Quotient.out q)
        have hS0 : Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) ≠ 0 := Nat.card_pos.ne'
        rw [← hc] at hS0
        obtain ⟨hn0, hc0⟩ := mul_ne_zero_iff.1 hS0
        obtain ⟨g', hg', k, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ' K ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q)
        have hue : u (Quotient.out (DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q))) =
            u ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q) := by rw [e, hu' g' hg' k hk]
        simp only [w, Φ]
        rw [hue, ← hc]
        push_cast
        field_simp

end GlobalTheory.ClassSumUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroupStatement
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup : ∀ {G H : Type} [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h, ι h = g) → ∀ (T : Subgroup H) (Γ' : Subgroup G), (∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) → ∀ (K : Subgroup G) (u : G → ℂ), (∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g) → Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) → (∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) → ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) = ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) := by
  first | exact @GlobalTheory.ClassSumUnfold.unfold_classSum | exact GlobalTheory.ClassSumUnfold.unfold_classSum | (intros; apply GlobalTheory.ClassSumUnfold.unfold_classSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClasses
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.Regroup

theorem finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H),
      ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) :=
  GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets a ha

theorem unfold {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (T : Subgroup H) (Γ' : Subgroup G) (hΓ' : ∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g)
    (K : Subgroup G) (u : G → ℂ) (hu : ∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h3 : ∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) =
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) :=
  GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup ι hι Γ hΓ T Γ' hΓ' K u hu h1 h2 h3

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x :=
  GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range

theorem finite_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) :=
  GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels

theorem finite_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) :=
  GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level

theorem finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU (E := E) (n := n), {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite :=
  GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction

theorem separable_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n), globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable :=
  GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

theorem support_conj_finite {G H : Type} [Group G] [Group H] (ι : H →* G) (Φ : G → ℂ) (x : G)
    (h4 : {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) (c : H) :
    {δ : H ⧸ twCent (MonoidHom.id H) c | (fun g : G => Φ (g⁻¹ * ι c * g)) ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image (f := fun δ : H ⧸ twCent (MonoidHom.id H) c => Quotient.out δ * c * (Quotient.out δ)⁻¹)
    (h4.subset ?_) ?_
  · rintro _ ⟨δ, hδ, rfl⟩
    show Φ (x⁻¹ * ι (Quotient.out δ * c * (Quotient.out δ)⁻¹) * x) ≠ 0
    have hδ' : Φ (((ι (Quotient.out δ))⁻¹ * x)⁻¹ * ι c * ((ι (Quotient.out δ))⁻¹ * x)) ≠ 0 := hδ
    convert hδ' using 2
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro δ₁ _ δ₂ _ e
    simp only at e
    rw [← Quotient.out_eq δ₁, ← Quotient.out_eq δ₂]
    apply QuotientGroup.eq.2
    change (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂)
    calc (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c
        = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₂ * c * (Quotient.out δ₂)⁻¹) * Quotient.out δ₂ := by group
      _ = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₁ * c * (Quotient.out δ₁)⁻¹) * Quotient.out δ₂ := by rw [e]
      _ = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂) := by group

theorem regroup_abstract {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (K : Subgroup G) (Φ : G → ℂ) (ψ : H → ℂ)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (k⁻¹ * g * k) = Φ g) (hψ : ∀ a b, ψ (b⁻¹ * a * b) = ψ a)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h4 : ∀ x : G, {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ =
    ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep *
      ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep) : Subgroup G) : Set G) (K : Set G),
        ((Nat.card ↥((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep)) ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
          Φ ((Quotient.out q)⁻¹ * ι c.rep * Quotient.out q) := by
  classical
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
  set D : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → TwCl (MonoidHom.id H) → ℂ := fun q c =>
    ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) with hD

  have s1 : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ = ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep * D q c := by
    intro q
    rw [finsum_classes _ ((h4 (Quotient.out q)).subset fun γ hγ => left_ne_zero_of_mul hγ)]
    refine finsum_congr fun c => ?_
    rw [hD, mul_finsum]
    refine finsum_congr fun δ => ?_
    have : ψ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = ψ c.rep := by
      simpa using hψ c.rep (Quotient.out δ)⁻¹
    rw [this, mul_comm]

  have hsupp : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      (Function.support fun c : TwCl (MonoidHom.id H) => ψ c.rep * D q c).Finite := by
    intro q
    refine ((h4 (Quotient.out q)).image (fun γ => (Quot.mk _ γ : TwCl (MonoidHom.id H)))).subset ?_
    intro (c : TwCl (MonoidHom.id H)) hc
    have hc' : D q c ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨δ, hδ⟩ : ∃ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
        Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hc' (by rw [hD]; simp only; rw [finsum_congr hn]; simp)
    refine ⟨_, hδ, ?_⟩
    change Quot.mk _ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = c
    exact (Quot.sound ⟨Quotient.out δ, by simp [mul_assoc]; rfl⟩).trans (Quot.out_eq c)
  simp_rw [s1]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [mul_finsum]
  rw [← finsum_sum_comm]
  · refine finsum_congr fun c => ?_
    have e2 := unfold ι hι Γ hΓ (twCent (MonoidHom.id H) c.rep) (Γ ⊓ twCent (MonoidHom.id G) (ι c.rep))
      (fun g => by
        constructor
        · rintro ⟨hg, hc⟩
          obtain ⟨h, rfl⟩ := (hΓ g).1 hg
          refine ⟨h, hι ?_, rfl⟩
          change ι h * ι c.rep = ι c.rep * ι h at hc
          change ι (h * c.rep) = ι (c.rep * h)
          rw [map_mul, map_mul, hc]
        · rintro ⟨t, ht, rfl⟩
          refine ⟨(hΓ _).2 ⟨t, rfl⟩, ?_⟩
          change ι t * ι c.rep = ι c.rep * ι t
          have ht' : t * c.rep = c.rep * t := ht
          rw [← map_mul, ht', map_mul])
      K (fun g => Φ (g⁻¹ * ι c.rep * g))
      (fun t ht k hk g => by
        have ht' : t * c.rep = c.rep * t := ht
        simp only [_root_.mul_inv_rev]
        have : (k⁻¹ * (g⁻¹ * (ι t)⁻¹) * ι c.rep * (ι t * g * k)) = k⁻¹ * (g⁻¹ * ι c.rep * g) * k := by
          have : (ι t)⁻¹ * ι c.rep * ι t = ι c.rep := by
            rw [← map_inv, ← map_mul, ← map_mul, mul_assoc, ← ht', inv_mul_cancel_left]
          calc _ = k⁻¹ * (g⁻¹ * ((ι t)⁻¹ * ι c.rep * ι t) * g) * k := by group
            _ = _ := by rw [this]
        rw [this, hΦ k hk])
      h1 h2 (fun x => support_conj_finite ι Φ x (h4 x) c.rep)
    rw [← mul_finsum, ← e2, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hD]
    simp only
    rw [mul_left_comm]
    congr 2
    refine finsum_congr fun δ => ?_
    congr 1
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro q _
    exact (hsupp q).subset fun c hc => right_ne_zero_of_mul hc

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_conj {G : Type} [Group G] (U : Subgroup G) (k : U) (y : G) :
    toSub U ((k : G)⁻¹ * y * k) = k⁻¹ * toSub U y * k := by
  unfold toSub
  by_cases hy : y ∈ U
  · rw [dite_eq_left hy, dite_eq_left (mul_mem (mul_mem (inv_mem k.2) hy) k.2)]
    ext
    simp
  · rw [dite_eq_right hy, dite_eq_right]
    · simp
    · intro h
      apply hy
      have := mul_mem (mul_mem k.2 h) (inv_mem k.2)
      simpa [mul_assoc] using this

theorem globFn_conj (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, IsHecke (K' w) (f w)) (k : finU (E := E) (n := n)) (hk : k ∈ globLev S K') (g : finU (E := E) (n := n)) :
    globFn S f (k⁻¹ * g * k) = globFn S f g := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  have hkw : cLoc w k.1 ∈ (K' w).map (UL n w).subtype := by
    have h1 := Subgroup.mem_iInf.1 hk w
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 hw)
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hkw
  have e2 : cLoc w (k⁻¹ * g * k).1 = ((k' : UL n w) : GLw n w)⁻¹ * cLoc w g.1 * (k' : GLw n w) := by
    have e' : (k' : GLw n w) = cLoc w k.1 := e
    rw [e']
    simp
  rw [e2, toSub_conj, ((hf w).2 k' hk' _).2, ((hf w).2 k'⁻¹ (inv_mem hk') _).1]

theorem chW_conj (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    chW lam (b⁻¹ * a * b).1.val.charpoly = chW lam a.1.val.charpoly := by
  congr 1
  have : (b⁻¹ * a * b).1.val = (b.1.val)⁻¹ * a.1.val * b.1.val := by
    simp [Matrix.coe_units_inv]
  rw [this]
  have h := Matrix.charpoly_units_conj (b.1)⁻¹ a.1.val
  simpa [Matrix.coe_units_inv] using h

theorem kernSum_eq_finsum_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → kernSum S lam K' f = ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then chW lam c.rep.1.val.charpoly * clsSum S K' f c.rep else 0 := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  obtain ⟨hmul, hinj, hmem⟩ := finPt_props E n
  let ι : UE E n →* finU (E := E) (n := n) := MonoidHom.mk' finPt hmul
  have key : ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly =
    ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), chW lam c.rep.1.val.charpoly *
      ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n)))
        (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) :=
    regroup_abstract ι hinj (ratFinU E n) hmem (globLev S K') (globFn S f) (fun γ => chW lam γ.1.val.charpoly)
      (globFn_conj S K' f hf.1) (chW_conj lam) (finite_classes E hU n hn S hS K' hK) (finite_stab E hU n hn S hS K' hK)
      (finite_supp E hU n hn S hS K' hK f hf)
  obtain ⟨w, hw, hsep⟩ := hreg
  unfold kernSum
  rw [key, mul_finsum]
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · rw [clsSum]
    ring
  · have h0 : ∀ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU (E := E) (n := n))) :
        Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) = 0 := fun q => by
      by_contra h
      exact hc (separable_of_globFn_ne_zero E n S K' f hf w hw hsep _ _ h)
    simp [h0]

end GlobalTheory.BCT.Regroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClassesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSum_eq_finsum_regular_rationalClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → kernSum S lam K' f = ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then chW lam c.rep.1.val.charpoly * clsSum S K' f c.rep else 0 := by
  first | exact @GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes | exact GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes | (intros; apply GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClasses
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  rw [GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum E hU n hn S hS lam K' hK f hf, GlobalTheory.T.kernelSum_eq_finsum_regular_rationalClasses E hU n hn S hS lam K' hK f hf hreg]
  congr 1
  unfold geomURat
  refine finsum_congr fun c => ?_
  split_ifs with h
  · rw [GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral E hU n hn S hS lam K' hK f hf c.rep h]; ring
  · rfl

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClassesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  first | exact @GlobalTheory.BCT.trOn_forms_hop_eq_geom | exact GlobalTheory.BCT.trOn_forms_hop_eq_geom | (intros; apply GlobalTheory.BCT.trOn_forms_hop_eq_geom <;> assumption)
end

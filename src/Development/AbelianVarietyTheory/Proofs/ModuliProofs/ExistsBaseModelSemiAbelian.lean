module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsOpenImmersionQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteOrderAutomorphismFixingLevelTrivialOnFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientModelByTameFiniteGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientModelByTameFiniteGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.QuotModel

theorem injective_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Function.Injective β := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  exact IsFractionRing.injective O F

theorem mono_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) : Mono (spMap β) := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  have : Epi (CommRingCat.ofHom β) := ⟨fun {Z} g₁ g₂ hg => by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (j := g₁.hom) (k := g₂.hom) ?_
    have e := congrArg CommRingCat.Hom.hom hg
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    exact e⟩
  exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom β).op

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : Function.Injective β) (p : Sp O) :
    p ∈ Set.range (spMap β) ↔ p.asIdeal = ⊥ := by
  have hk : RingHom.ker β = ⊥ := (RingHom.injective_iff_ker_eq_bot β).mp h
  constructor
  · rintro ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    show Ideal.comap β q.asIdeal = ⊥
    rw [hq, ← RingHom.ker_eq_comap_bot, hk]
  · intro hp
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap β ⊥ = p.asIdeal
    rw [hp, ← RingHom.ker_eq_comap_bot, hk]

theorem densePart {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) {X U : Scheme.{0}}
    (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (h₁ : Flat s) (h₂ : IsProjOver s) (h₃ : IsOpenImmersion jQ)
    (h₄ : Dense (Set.range jQ)) :
    IsLocallyNoetherian X ∧ genericPoints X ⊆ Set.range (jQ ≫ pullback.fst _ _ : U ⟶ X) ∧
      ∀ u : U, IsIso ((jQ ≫ pullback.fst _ _ : U ⟶ X).stalkMap u) := by
  obtain ⟨⟨hdom, hded⟩, -, hfr⟩ := h
  let _ := β.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdo, hqc⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ h₁ h₂ h₃ h₄
  obtain ⟨hg, hst, -⟩ := GlobalTheory.densePart_basic X U _ hpre hfl hdo hqc
  exact ⟨hN, hg, hst⟩

private theorem isReduced_of_isNormalScheme' (X : Scheme.{0}) (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

end GlobalTheory.QuotModel


open GlobalTheory.QuotModel in
theorem GlobalTheory.Models.exists_quotient_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst C.t.G.hom x ≫ (τ g).asIso.hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' Γ _ _ C b k r ν ρ₀ τ₀ ρ τ mu hβ hβ' hcomp hfin hrc hr hprop hmu hqp
    htame hin hgood hpush

  have sq : ∀ {S S' : Scheme.{0}} {ta : SAB H S} {tb : SAB H S'} {f : S ⟶ S'} (m : SABMap ta tb f),
      m.φ ≫ tb.G.hom = ta.G.hom ≫ f := fun m => m.cart.1.w
  have sqm : C.m.φ ≫ C.t.G.hom = t.G.hom ≫ C.j := sq C.m

  obtain ⟨X', π, s', jQ, hπ, hπfin, hπs, hnorm, hproj, hflat, hjover, hjopen, hjdense, hjc, hgen⟩ :=
    GlobalTheory.exists_quotient_model_scheme E H U F O c t β Γ C U' F' O' c' β' b k r ρ₀ ρ hβ hβ' hcomp hfin hrc hr
      (fun g => (hmu g).2.1)
  obtain ⟨hN', -, -⟩ := densePart hβ' s' jQ hflat hproj hjopen hjdense
  obtain ⟨-, hgenC, hstC⟩ := densePart hβ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hredX : IsReduced C.X := isReduced_of_isNormalScheme' _ C.normal
  have hgab : genericPoints C.X ⊆ abLocus C.t.G := by
    intro x hx
    obtain ⟨u, rfl⟩ := hgenC hx
    have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
      rw [C.ab_gen]; exact ⟨u, rfl⟩
    exact hu

  obtain ⟨t₁, ν', hν'τ, hgood'⟩ :=
    GlobalTheory.T.exists_semiAbelian_descent_tame_quotient E H Γ O C.X X' ρ π C.t C.s τ mu hπ hπfin hqp ⟨hredX, hgab⟩ (fun g => (hmu g).1) htame hin
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' C.m
  have key : ∀ (f : U ⟶ X') (n : SABMap t t₁ f), f = r ≫ jQ ≫ pullback.fst _ _ →
      ∃ n' : SABMap t t₁ (r ≫ jQ ≫ pullback.fst _ _), n'.φ = n.φ := by
    rintro f n rfl; exact ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := key _ n hjc.symm

  have hredU : IsReduced U := by
    have : ∀ u : U, _root_.IsReduced (U.presheaf.stalk u) := by
      intro u
      have hI : IsIso ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u) := hstC u
      exact isReduced_of_injective (inv ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u)).hom
        (ConcreteCategory.bijective_of_isIso _).1
    exact isReduced_of_isReduced_stalk U
  have hmono : Mono C.j := by
    have := mono_spMap hβ
    have := C.jQ_open
    dsimp only [Cpt.j]; infer_instance
  have hτ : ∀ g, (τ₀ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ₀ g).asIso.hom ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ ∧
      (τ₀ g).asIso.hom ≫ n₂.φ = n₂.φ := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hmu g
    refine ⟨(cancel_mono C.j).mp ?_, h4, ?_⟩
    · calc ((τ₀ g).asIso.hom ≫ t.G.hom) ≫ C.j = ((τ₀ g).asIso.hom ≫ C.m.φ) ≫ C.t.G.hom := by
            simp only [Category.assoc]; rw [← sqm]
        _ = (C.m.φ ≫ (mu g).φ) ≫ C.t.G.hom := by rw [← h3, h1]
        _ = C.m.φ ≫ C.t.G.hom ≫ (ρ g).asIso.hom := by simp only [Category.assoc]; rw [sq (mu g)]
        _ = t.G.hom ≫ C.j ≫ (ρ g).asIso.hom := by rw [← Category.assoc, sqm, Category.assoc]
        _ = (t.G.hom ≫ (ρ₀ g).asIso.hom) ≫ C.j := by rw [h2, Category.assoc]
    · rw [hn₂, hn, ← Category.assoc, ← h3, Category.assoc, hν'τ g]
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient E H Γ U U' X' ρ₀ r t t' t₁ τ₀ ν _ n₂ hr hredU hprop hτ

  have hπsurj : Function.Surjective π := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ C.X X' ρ π hπ).2.1.surj
  have hrsurj : Function.Surjective r := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ U U' ρ₀ r hr).2.1.surj
  have habπ : ∀ x, π x ∈ abLocus t₁.G ↔ x ∈ abLocus C.t.G := fun x =>
    abLocus_pullback abLocusOne t₁.semi ν'.cart.1 x

  have hbint : ∀ p : Sp O, (spMap b p).asIdeal = ⊥ → p.asIdeal = ⊥ := by
    intro p hp
    obtain ⟨⟨hdO, -⟩, -, -⟩ := hβ
    obtain ⟨⟨hdO', -⟩, -, -⟩ := hβ'
    let _ := b.toAlgebra
    have h2 : IsFinite (Spec.map (CommRingCat.ofHom b)) := hfin
    rw [IsFinite.SpecMap_iff] at h2
    have : Module.Finite O' O := h2
    have : Algebra.IsIntegral O' O := inferInstance
    exact Ideal.eq_bot_of_comap_eq_bot (R := O') hp
  have hpre : Function.Injective (pullback.fst s' (spMap β')) := by
    obtain ⟨-, -, hfr'⟩ := hβ'
    let _ := β'.toAlgebra
    have : IsPreimmersion (spMap β') := IsPreimmersion.of_isLocalization (nonZeroDivisors O')
    exact (pullback.fst s' (spMap β')).isEmbedding.injective
  have hab : pullback.fst s' (spMap β') ⁻¹' abLocus t₁.G = Set.range jQ := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx⟩ := hπsurj (pullback.fst s' (spMap β') w)
      have hxab : x ∈ abLocus C.t.G := (habπ x).1 (by rw [hx]; exact hw)
      have hs' : (s' (pullback.fst s' (spMap β') w)).asIdeal = ⊥ := by
        have e : s' (pullback.fst s' (spMap β') w) = spMap β' (pullback.snd s' (spMap β') w) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        rw [e]
        exact (mem_range_spMap (injective_of_isDedFrac hβ') _).1 ⟨_, rfl⟩
      have hsx : (C.s x).asIdeal = ⊥ := by
        apply hbint
        have e : spMap b (C.s x) = s' (π x) := by
          rw [← Scheme.Hom.comp_apply, ← hπs, Scheme.Hom.comp_apply]
        rw [e, hx]
        exact hs'
      obtain ⟨q, hq⟩ := (mem_range_spMap (injective_of_isDedFrac hβ) (C.s x)).2 hsx
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.s) (g := spMap β) x q hq.symm
      have hz : z ∈ Set.range C.jQ := by
        rw [← C.ab_gen]
        show pullback.fst C.s (spMap β) z ∈ abLocus C.t.G
        rw [hz1]
        exact hxab
      obtain ⟨u, rfl⟩ := hz
      obtain ⟨u', hu'⟩ := (hgen x).2 ⟨u, hz1⟩
      exact ⟨u', hpre (hu'.trans hx)⟩
    · rintro ⟨u', rfl⟩
      obtain ⟨u, rfl⟩ := hrsurj u'
      have e : pullback.fst s' (spMap β') (jQ (r u)) = π (C.j u) := by
        have h5 := congrArg (fun f : U ⟶ X' => f u) hjc
        simpa only [Scheme.Hom.comp_apply] using h5
      show pullback.fst s' (spMap β') (jQ (r u)) ∈ abLocus t₁.G
      rw [e, habπ]
      have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
        rw [C.ab_gen]; exact ⟨u, rfl⟩
      exact hu
  refine ⟨⟨X', s', hnorm, hproj, hflat, jQ, hjover, hjopen, hjdense, t₁, m', hab⟩, hgood' hgood hpush,
    ⟨⟨π, hπs, ?_, ν', hjc.symm, ?_⟩⟩⟩
  · refine MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.fst s' (spMap b))
      inferInstance ?_
    rw [pullback.lift_fst]
    exact hπfin
  · rw [hm', hn₂, hn]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientModelByTameFiniteGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_model_by_tame_finite_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst C.t.G.hom x ≫ (τ g).asIso.hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  first | exact @GlobalTheory.Models.exists_quotient_model | exact GlobalTheory.Models.exists_quotient_model | (intros; apply GlobalTheory.Models.exists_quotient_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem over_of_fix (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) {l₀ l₁ : Level H} {X₀ : Moduli D l₀}
    {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r} (hA : l₀.A = 1)
    (hc : LevComp X₁.univ X₀.univ r ν) {f : X₁.X ⟶ X₁.X} (m : SABMap X₁.univ.t X₁.univ.t f)
    (hm : ∀ a, (X₁.univ.eta a).left ≫ m.φ = f ≫ (X₁.univ.eta a).left) (hs : (f ≫ r) ≫ X₀.s = r ≫ X₀.s) :
    f ≫ r = r ∧ m.φ ≫ ν.φ = ν.φ := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp m ν rfl
  rw [← hn]
  refine LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ n ν (isReduced_moduli X₁) hs
    ⟨fun a => ?_, fun a => ?_⟩ hc
  · rw [hn, ← Category.assoc, LevelCover.sec_pow m _ _ (hm a), Category.assoc, hc.1, Category.assoc]
  · have e : X₁.univ.etaA a ^ (l₁.A / l₀.A) = X₁.univ.eta 0 ^ 0 := by
      rw [hA, Nat.div_one, pow_zero, ← Moduli.LevelAction.map_nsmul_of_add X₁.univ.etaA_add, X₁.univ.etaA_ker]
    rw [hn, Category.assoc, ← hc.2, e, ← Category.assoc, LevelCover.sec_pow m _ _ (hm 0), Category.assoc]

theorem exists_twist_of_fibre (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3) (hN : ToroidalLevelCompatibility (H := H) (D := D))
    {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X} {ν : SABMap X₁.univ.t X₀.univ.t r}
    {j : KA l₀ →+* KA l₁} (hd : l₀.Dvd l₁) (hM : l₁.M = l₀.M) (hMb : l₁.Mb = l₀.Mb)
    (hj : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom j) (hr : r ≫ X₀.s = X₁.s ≫ spMap j)
    (hc : LevComp X₁.univ X₀.univ r ν) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X₁.X)
    (h₁ : y ≫ r = y' ≫ r) (h₂ : y ≫ X₁.s = y' ≫ X₁.s) :
    ∃ (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist X₁ ρ.hom m.φ g (RingHom.id _) ∧ y' = y ≫ ρ.hom := by
  let c := LevelExist.minCoeff l₁
  have hM' : 0 < l₁.M' := LevelExist.M'_pos l₁
  have hz : ∀ a, a ∣ l₁.M' → zeta a ∈ c.F := fun a ha => by
    rw [LevelCover.zeta_dvd hM' ha]
    exact pow_mem c.zeta_mem _
  have hle : KA l₀ ≤ c.F := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (rfl | rfl)
    · exact c.le (baseKA l₁).ρ.2
    · exact hz _ (hd.2.2.trans (Nat.dvd_lcm_right _ _))
  let c₀ : Coeff l₀ := ⟨c.F, c.fin, c.conj, hz _ (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _))
    (hd.2.2.trans (Nat.dvd_lcm_right _ _))), hle⟩
  obtain ⟨r', j', ν', hj', hr', e₁, e₂, -, hF⟩ := hN l₀ l₁ X₀ X₁ hd
  obtain rfl : j = j' := RingHom.ext fun x => Subtype.ext ((hj x).trans (hj' x).symm)
  obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ X₀ _ _ _ _ X₁.univ _ _ ν ν'
    (isReduced_moduli X₁) (hr.trans hr'.symm) hc ⟨e₁, e₂⟩).1
  obtain ⟨rF, a₁, a₂, -, -, -, htr⟩ := hF c₀ c rfl
  obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ X₁.s)
  obtain ⟨θ, hθ⟩ : ∃ θ : c.F →+* k, θ.comp (IntermediateField.inclusion c.le).toRingHom = β := by
    letI : Algebra (KA l₁) k := β.toAlgebra
    letI : Algebra (KA l₁) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
    haveI := c.fin
    haveI : IsScalarTower ℚ (KA l₁) c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.IsAlgebraic (KA l₁) c.F := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l₁)
    exact ⟨(IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).toRingHom,
      (IsAlgClosed.lift (R := KA l₁) (S := c.F) (M := k)).comp_algebraMap⟩
  have w : y ≫ X₁.s = spMap θ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [LevCover.spMap_comp'', hθ, hβ]
  obtain ⟨⟨g, ρ, hg, ⟨hs, m, b₁, b₂⟩, -, hy⟩, -⟩ := htr k (pullback.lift y (spMap θ) w)
    (pullback.lift y' (spMap θ) (h₂ ▸ w)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, a₁, pullback.lift_fst_assoc, pullback.lift_fst_assoc, h₁]
      · rw [Category.assoc, Category.assoc, a₂, pullback.lift_snd_assoc, pullback.lift_snd_assoc])
  rw [pullback.lift_fst, pullback.lift_fst_assoc] at hy
  refine ⟨ρ, m, g.f l₁.A, ⟨by rw [hs, LevelCover.spMap_id', Category.comp_id], fun a => ?_, b₂⟩, hy⟩
  rw [← b₁, Moduli.LevelAction.eta_congr X₁.univ (x := g.f l₁.M a) (y := a) (by rw [hM, hMb]; exact hg.2.1 a)]

theorem exists_finite_invariant {l : Level H} (Xo : Moduli D l) :
    ∃ (κ : Type) (_ : Finite κ) (q : (D.La →ₗ[𝓞 E] D.La) → κ), ∀ g g', q g = q g' →
      ∀ x, Xo.univ.etaA (g x) = Xo.univ.etaA (g' x) := by
  obtain ⟨_, _⟩ := LevCover.datum_free D
  obtain ⟨κ, _, q, hq⟩ := LevCover.exists_finite_mod D.La l.A_pos
  haveI : Nonempty D.La := ⟨0⟩
  refine ⟨κ → κ, inferInstance, fun g c => q (g (Function.invFun q c)), fun g g' h x => ?_⟩
  obtain ⟨c, hc⟩ := hq _ _ (Function.invFun_eq (f := q) ⟨x, rfl⟩)
  obtain ⟨c', hc'⟩ := hq _ _ (congrFun h (q x))
  generalize Function.invFun q (q x) = y at hc hc'
  subst hc
  simp only [map_add (f := _), map_nsmul, hc', Xo.univ.etaA_add, Xo.univ.etaA_ker, _root_.mul_one]

section

variable {l₀ l₁ : Level H} {X₀ : Moduli D l₀} {X₁ : Moduli D l₁} {r : X₁.X ⟶ X₀.X}

def twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left) : Submonoid (autOver r) :=
  { carrier := {ω | ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧
      SemiTwist X₁ ω.1.asIso.hom (τ ω).asIso.hom g σ.toRingHom}
    mul_mem' := by
      rintro a b ⟨g, σ, h₁, h₂⟩ ⟨g', σ', h₁', h₂'⟩
      refine ⟨g' ∘ₗ g, σ.trans σ', by rw [RingEquiv.trans_apply, h₁, h₁'], ?_⟩
      have e₁ : (a * b).1.asIso.hom = b.1.asIso.hom ≫ a.1.asIso.hom := rfl
      have e₂ : (τ (a * b)).asIso.hom = (τ b).asIso.hom ≫ (τ a).asIso.hom := by rw [map_mul]; rfl
      have e₃ : (σ.trans σ').toRingHom = σ'.toRingHom.comp σ.toRingHom := RingHom.ext fun _ => rfl
      rw [e₁, e₂, e₃, LinearMap.coe_comp]
      exact h₂'.comp h₂
    one_mem' := by
      refine ⟨LinearMap.id, RingEquiv.refl _, rfl, ?_⟩
      rw [map_one]
      exact ⟨(Category.id_comp _).trans ((Category.comp_id _).symm.trans
          (congrArg _ (LevelCover.spMap_id' _).symm)),
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm,
        fun a => (Category.comp_id _).trans (Category.id_comp _).symm⟩ }

theorem inv_comp_square {X P : Scheme.{0}} (a : X ≅ X) (t : P ≅ P) {b : X ⟶ X} {u : P ⟶ P} {x y : X ⟶ P}
    (p₁ : y ≫ t.hom = a.hom ≫ x) (p₂ : y ≫ u = b ≫ x) : x ≫ t.inv ≫ u = (a.inv ≫ b) ≫ x := by
  rw [Category.assoc, ← p₂, Iso.eq_inv_comp, ← Category.assoc, ← p₁, Category.assoc, Iso.hom_inv_id_assoc]

theorem finite_twistMonoid (τ : autOver r →* Aut X₁.univ.t.G.left)
    (mu : ∀ ω : autOver r, SABMap X₁.univ.t X₁.univ.t ω.1.asIso.hom) (hmu : ∀ ω, (mu ω).φ = (τ ω).asIso.hom) :
    Finite (twistMonoid τ) := by
  obtain ⟨κ, _, q, hq⟩ := exists_finite_invariant X₁
  haveI := finite_fieldAut l₁
  have hch : ∀ ω : twistMonoid τ, ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁),
      SemiTwist X₁ ω.1.1.asIso.hom (τ ω.1).asIso.hom g σ.toRingHom := fun ω => by
    obtain ⟨g, σ, -, h⟩ := ω.2
    exact ⟨g, σ, h⟩
  choose g σ hg using hch
  refine Finite.of_injective (fun ω => (q (g ω), σ ω)) fun a b hab => ?_
  have h₁ := hq _ _ (congrArg Prod.fst hab)
  have h₂ : σ a = σ b := congrArg Prod.snd hab
  have e₀ : (b.1 * a.1⁻¹).1.asIso.hom = a.1.1.asIso.inv ≫ b.1.1.asIso.hom := rfl
  have e₁ : (τ (b.1 * a.1⁻¹)).asIso.hom = (τ a.1).asIso.inv ≫ (τ b.1).asIso.hom := by rw [map_mul, map_inv]; rfl
  have key : ∀ {x y : X₁.X ⟶ X₁.univ.t.G.left}, y ≫ (τ a.1).asIso.hom = a.1.1.asIso.hom ≫ x →
      y ≫ (τ b.1).asIso.hom = b.1.1.asIso.hom ≫ x → x ≫ (mu (b.1 * a.1⁻¹)).φ = (b.1 * a.1⁻¹).1.asIso.hom ≫ x := by
    intro x y p₁ p₂
    rw [hmu, e₀, e₁]
    exact inv_comp_square a.1.1.asIso (τ a.1).asIso p₁ p₂
  have hid : (b.1 * a.1⁻¹).1.asIso.hom = 𝟙 _ :=
    SemiTwist.eq_id (g := id) (σ := RingHom.id _) (mu (b.1 * a.1⁻¹)) ⟨by
      rw [e₀, Category.assoc, (hg b).1, ← h₂, ← (hg a).1, LevelCover.spMap_id', Category.comp_id]
      exact Iso.inv_hom_id_assoc a.1.1.asIso _,
      fun x => key ((hg a).2.1 x) ((hg b).2.1 x),
      fun x => key ((hg a).2.2 x) (h₁ x ▸ (hg b).2.2 x)⟩ rfl fun _ => rfl
  have : b.1 * a.1⁻¹ = 1 := Subtype.ext (Aut.ext (Iso.ext hid))
  exact Subtype.ext (mul_inv_eq_one.1 this).symm

theorem exists_mem_twistMonoid (hL : Out.Laws) (hL2 : Out.Laws2) (hL3 : Out.Laws3)
    {ν : SABMap X₁.univ.t X₀.univ.t r} {k : KA l₀ →+* KA l₁} (hA : l₀.A = 1)
    (hk : IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k) (hr : r ≫ X₀.s = X₁.s ≫ spMap k)
    (hc : LevComp X₁.univ X₀.univ r ν) (τ : autOver r →* Aut X₁.univ.t.G.left)
    (hτ : ∀ ω, (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (τ ω).asIso.hom ≫ X₁.univ.t.G.hom = X₁.univ.t.G.hom ≫ ω.1.asIso.hom)
    (ρ : X₁.X ≅ X₁.X) (m : SABMap X₁.univ.t X₁.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁)
    (h₁ : σ (baseKA l₁).ρ = (baseKA l₁).ρ) (h₂ : SemiTwist X₁ ρ.hom m.φ g σ.toRingHom) :
    ∃ ω ∈ twistMonoid τ, ω.1.asIso.hom = ρ.hom := by
  have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
  have hz : (baseKA l₀).ζ = 1 := by
    have := (baseKA l₀).ζ_prim.pow_eq_one
    rwa [hA, pow_one] at this
  have hσ : σ.toRingHom.comp k = k := field_hom_ext l₀ _ _ (by rw [RingHom.comp_apply, hkρ]; exact h₁)
    (by rw [hz, map_one, map_one])
  obtain ⟨o₁, o₂⟩ := over_of_fix hL hL2 hL3 hA hc m h₂.2.1 (by
    rw [Category.assoc, hr, ← Category.assoc, h₂.1, Category.assoc, LevCover.spMap_comp'', hσ])
  have e : m.φ = (τ ⟨Aut.of ρ, o₁⟩).asIso.hom :=
    ν.cart.1.hom_ext (o₂.trans (hτ _).1.symm) (m.cart.1.w.trans (hτ ⟨Aut.of ρ, o₁⟩).2.symm)
  exact ⟨⟨Aut.of ρ, o₁⟩, ⟨g, σ, h₁, e ▸ h₂⟩, rfl⟩

end

theorem exists_level_quotient : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left := by
  intro hL hL2 hL3 E _ _ _ H D Xo hpq hN l₀ l₁ r ν k hA hM hMb hk hr hc
  have hd : l₀.Dvd l₁ := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ one_dvd _⟩
  obtain ⟨hfin, het, hsur⟩ : IsFinite r ∧ Etale r ∧ Surjective r := by
    obtain ⟨k', r', ν', hr', hk', hc', -, -, -, h⟩ := LevelMap.exists_levelMap E H D Xo hN l₀ l₁ hd
    obtain rfl : k = k' := RingHom.ext fun x => Subtype.ext ((hk x).trans (hk' x).symm)
    obtain rfl : r = r' := (LevUniq.map_to_univ_unique hL hL2 hL3 E H D l₀ l₁ _ _ _ _ _ (Xo l₁).univ _ _ ν ν'
      (isReduced_moduli _) (hr.trans hr'.symm) hc hc').1
    exact h
  obtain ⟨τ, hτ⟩ := exists_liftAut ν.cart.1
  have hmu : ∀ ω : autOver r, ∃ m : SABMap (Xo l₁).univ.t (Xo l₁).univ.t ω.1.asIso.hom, m.φ = (τ ω).asIso.hom := fun ω => by
    obtain ⟨m, hm⟩ := LevelCover.sab_cancel ν ν ω.1.asIso.hom ω.2
    exact ⟨m, ν.cart.1.hom_ext (hm.trans (hτ ω).1.symm) (m.cart.1.w.trans (hτ ω).2.symm)⟩
  choose mu hmu using hmu
  let S := twistMonoid τ
  have hS := exists_mem_twistMonoid hL hL2 hL3 hA hk hr hc τ hτ
  haveI : Finite S := finite_twistMonoid τ mu hmu
  obtain ⟨T, hT⟩ := exists_subgroup_of_finite S
  refine ⟨T, inferInstance, Finite.of_injective (fun t : T => (⟨t.1, (hT _).1 t.2⟩ : S))
      fun a b h => Subtype.ext (congrArg (fun s : S => s.1) h),
    (autOver r).subtype.comp T.subtype, τ.comp T.subtype, fun t => mu t.1,
    Subtype.val_injective.comp Subtype.val_injective, ⟨inferInstance, fun t => t.1.2, ?_⟩, fun t => ?_⟩
  · refine invariant_descends r (fun t : T => t.1.1.asIso.hom) (fun t => t.1.2) fun F _ _ y y' hy => ?_
    obtain ⟨β, hβ⟩ := LevCover.exists_spMap (y ≫ (Xo l₁).s)
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (y' ≫ (Xo l₁).s)
    have hkρ : k (baseKA l₀).ρ = (baseKA l₁).ρ := Subtype.ext (hk _)
    have hb : β.comp k = β'.comp k := LevCover.spMap_inj' (by
      rw [← LevCover.spMap_comp'', ← LevCover.spMap_comp'', ← hβ, ← hβ', Category.assoc, Category.assoc, ← hr,
        ← Category.assoc, hy, Category.assoc])
    obtain ⟨σ, h₁, h₂⟩ := exists_fieldAut l₁ β β' (hkρ ▸ DFunLike.congr_fun hb (baseKA l₀).ρ)
    obtain ⟨ρ, m, g, h₃⟩ := exists_semiTwist_iso hpq l₀ hA hM hMb (Xo l₁) σ h₁
    obtain ⟨a, ha, ea⟩ := hS ρ m g σ h₁ h₃
    obtain ⟨ρ', m', g', h₄, h₅⟩ := exists_twist_of_fibre hL hL2 hL3 hN hd hM hMb hk hr hc (y ≫ ρ.hom) y'
      (by rw [Category.assoc, ← ea, show a.1.asIso.hom ≫ r = r from a.2, hy])
      (by rw [Category.assoc, h₃.1, ← Category.assoc, hβ, hβ', LevCover.spMap_comp'', h₂])
    obtain ⟨b, hb', eb⟩ := hS ρ' m' g' (RingEquiv.refl _) rfl h₄
    refine ⟨⟨b * a, (hT _).2 (S.mul_mem hb' ha)⟩, ?_⟩
    rw [h₅, Category.assoc, ← ea, ← eb]
    rfl
  · obtain ⟨g, σ, h₁, h₂⟩ := (hT _).1 t.2
    exact ⟨hmu _, (hτ _).1, h₂.2.1, g, σ, h₁, h₂.1, h₂.2.2⟩

end GlobalTheory.LevQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_level_quotient_by_finite_group : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LevQuot.exists_level_quotient
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompactModelAboveFullLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompactModelAboveFullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Top.exists_cpt_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  intro E _ _ _ H D Xo n N T l h S e β b hS _ hN hβ hb
  subst h
  obtain ⟨⟨_, _⟩, _, hfr⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS hN).2.2 β hβ
  let _ := β.toAlgebra
  obtain ⟨W, f₀, hW₀, hfin, -, fa, fs⟩ := T.fin l rfl (β.comp b) (fun x => (hβ (b x)).trans (hb x))
  have hsm := (Xo l).smooth
  have hnor : Geo.Tor.IsNormalScheme (Xo l).X :=
    (GlobalTheory.isNormalScheme_iff_pred _).mp (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let s₁ := pullback.snd T.s (spMap b)
  have hp : IsPullback (pullback.fst s₁ (spMap β) ≫ pullback.fst T.s (spMap b)) (pullback.snd s₁ (spMap β)) T.s
      (spMap (β.comp b)) := by
    rw [spMap_comp]
    exact (IsPullback.of_hasPullback s₁ (spMap β)).paste_horiz (IsPullback.of_hasPullback T.s (spMap b))
  let g := W.ι ≫ hp.isoPullback.inv
  have g₁ : (g ≫ pullback.fst _ _) ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, hp.isoPullback_inv_fst]
  have g₂ : g ≫ pullback.snd _ _ = W.ι ≫ pullback.snd _ _ := by
    rw [Category.assoc, hp.isoPullback_inv_snd]
  have hW : (f₀ ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = f₀ ≫ g := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open _ (KA l) _ (Xo l).X s₁ (Xo l).s (f₀ ≫ g ≫ pullback.fst _ _) g.opensRange (f₀ ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b T.proj) hnor inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans (Category.assoc _ _ _))
      (by
        rw [← Category.assoc]
        exact (congrArg (· ≫ _) hW).trans ((Category.assoc _ _ _).trans ((congrArg (f₀ ≫ ·) g₂).trans fs)))
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst T.s (spMap b)) T.t
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b) = T.a l rfl := by
    rw [← fa, ← g₁, ← Category.assoc f₀, ← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap (Xo l).univ.t T.t
      ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b)), n'.φ = (T.m l rfl).φ := by
    rw [hj]; exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) ∈ abLocus T.t.G := by
    intro p
    have e : pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) =
        pullback.fst T.s (spMap (β.comp b)) (hp.isoPullback.hom p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.isoPullback_hom_fst]
    rw [e]
    change p ∈ Set.range g ↔ hp.isoPullback.hom p ∈ pullback.fst T.s (spMap (β.comp b)) ⁻¹' abLocus T.t.G
    rw [← hW₀]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact z.2
    · intro hz
      refine ⟨⟨_, hz⟩, ?_⟩
      refine (Scheme.Hom.comp_apply _ _ _).trans ?_
      change hp.isoPullback.inv (hp.isoPullback.hom p) = p
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩, π ≫ pullback.fst _ _, ?_, mu, ?_, hj,
    hm.symm.trans hn', ?_⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne T.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β) ⟶ pullback s₁ (spMap β) :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β) (w y) = π (pullback.fst (π ≫ s₁) (spMap β) y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst T.s (spMap b) z ∈ abLocus T.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _
  · have P₁ := IsPullback.of_hasPullback T.t.G.hom (pullback.fst T.s (spMap b))
    have Q := GlobalTheory.isQProjOver_of_isPullback (P₁.paste_vert (IsPullback.of_hasPullback T.s (spMap b))) T.qproj
    have P₀ := IsPullback.of_hasPullback T.t.G.hom (π ≫ pullback.fst T.s (spMap b))
    let ψ := P₁.lift (pullback.fst T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd _ _ ≫ π)
      (by rw [Category.assoc]; exact P₀.w)
    have ψ₁ : ψ ≫ _ = _ := P₁.lift_fst _ _ _
    have ψ₂ : ψ ≫ _ = _ := P₁.lift_snd _ _ _
    have P₂ : IsPullback ψ (pullback.snd T.t.G.hom (π ≫ pullback.fst T.s (spMap b)))
        (pullback.snd T.t.G.hom (pullback.fst T.s (spMap b))) π :=
      IsPullback.of_right (by rw [ψ₁]; exact P₀) ψ₂ P₁
    have : IsFinite ψ := MorphismProperty.of_isPullback (P := @IsFinite) P₂.flip hπ
    have R := GlobalTheory.isQProjOver_comp_of_isFinite ψ Q
    rw [← Category.assoc, ψ₂, Category.assoc] at R
    exact R

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompactModelAboveFullLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactModel_above_fullLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  first | exact @GlobalTheory.Models.Top.exists_cpt_above | exact GlobalTheory.Models.Top.exists_cpt_above | (intros; apply GlobalTheory.Models.Top.exists_cpt_above <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsDominantPullbackFstOfFlatOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isDominant_pullback_fst_of_flat_of_injective {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (hβ : Function.Injective β) {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap β)) := by
  constructor
  intro x
  have hη : (spMap β) (IsLocalRing.closedPoint F) ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O)
      (PrimeSpectrum.comap β (IsLocalRing.closedPoint F)) (s x)).mp ?_
    intro a ha
    have ha' : β a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    have : a = 0 := hβ (by rw [ha', map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap s hη
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure
  rw [Scheme.Pullback.range_fst]
  exact ⟨_, hy'.symm⟩

theorem isPrimitiveRoot_map_of_isUnit {O k : Type} [CommRing O] [IsDomain O] [Field k] (ψ : O →+* k)
    {z : O} {A : ℕ} (hA : 0 < A) (hz : IsPrimitiveRoot z A) (hu : IsUnit (A : O)) :
    IsPrimitiveRoot (ψ z) A := by
  have : NeZero (A : k) := ⟨by simpa using (hu.map ψ).ne_zero⟩
  rw [← (Polynomial.isRoot_cyclotomic_iff (R := k) (n := A)), ← Polynomial.map_cyclotomic A ψ]
  exact Polynomial.IsRoot.map ψ (hz.isRoot_cyclotomic hA)

theorem galoisPart_eq_refl_of_fixes_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ρ : C.X ≅ C.X) (σ : KA l ≃+* KA l), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → ∀ (k : Type) [Field k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → σ = RingEquiv.refl _ := by
  intro E _ _ _ H D l Xo S β C r ρ σ hinc hS ⟨e, he⟩ hj hρ hr k _ x hx
  have hA := l.A_pos
  have : NeZero l.A := ⟨hA.ne'⟩
  have hβ : Function.Injective β := fun a b h => Subtype.ext (by
    have h1 := hinc a
    rw [h, hinc b] at h1
    exact h1.symm)
  let z : RZ H S l.A := ⟨zeta l.A, Subring.subset_closure (by simp)⟩
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hβz : β z = (baseKA l).ζ := Subtype.ext (hinc z)
  have hζ : IsPrimitiveRoot (baseKA l).ζ l.A := (baseKA l).ζ_prim
  have hz : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (hβz ▸ hζ) hβ
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have := C.flat
  have hd₁ := isDominant_pullback_fst_of_flat_of_injective β hβ C.s
  have hd₂ : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have hd : IsDominant C.j := by unfold Cpt.j; infer_instance
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s = Xo.s ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  let ev : RZ H S l.A → (Polynomial ℤ →+* RZ H S l.A) := fun y => (Polynomial.aeval y).toRingHom
  have hev : σ.toRingHom.comp (β.comp (ev z)) = β.comp (ev (z ^ a)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ev, hβz, ha]
  have key : ρ.hom ≫ C.s ≫ spMap (ev z) = C.s ≫ spMap (ev (z ^ a)) := by
    refine ext_of_isDominant C.j ?_
    rw [reassoc_of% hj, reassoc_of% hjs, reassoc_of% hjs, reassoc_of% hr]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← hev]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ C.s)
  have key₂ : CommRingCat.ofHom (ev z) ≫ ψ = CommRingCat.ofHom (ev (z ^ a)) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, Category.assoc, Category.assoc, ← key, reassoc_of% hx]
  have key₃ : ψ.hom z = ψ.hom z ^ a := by
    have := congrArg (fun f => f.hom Polynomial.X) key₂
    simpa [ev] using this
  have hp : IsPrimitiveRoot (ψ.hom z) l.A := isPrimitiveRoot_map_of_isUnit ψ.hom hA hz hAu
  have hmod : a ≡ 1 [MOD l.A] := by
    have hfin : IsOfFinOrder (ψ.hom z) := hp.isOfFinOrder hA.ne'
    rw [hp.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
    exact key₃.symm
  have hσζ : σ (baseKA l).ζ = (baseKA l).ζ := by
    rw [← ha]
    have hfin : IsOfFinOrder (baseKA l).ζ := hζ.isOfFinOrder hA.ne'
    rw [hζ.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one] at hmod
    exact hmod
  have hfinal : σ.toRingHom.toRatAlgHom = AlgHom.id ℚ (KA l) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) (s := {H.rt0, zeta l.A}) rfl ?_
    rintro y (rfl | rfl)
    · exact hρ
    · exact hσζ
  ext1 y
  exact DFunLike.congr_fun hfinal y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.BaseModelEx

theorem natCast_ne_zero_of_pt {R k : Type} [CommRing R] [Field k] (y : Sp k ⟶ Sp R) {S : ℕ} (h : IsUnit (S : R)) :
    (S : k) ≠ 0 := by
  have := h.map (Spec.preimage y).hom
  rw [map_natCast] at this
  exact this.ne_zero

theorem natCast_notMem {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (f : X ⟶ Sp R) (g : X ⟶ Sp R')
    {S : ℕ} (h : IsUnit (S : R')) (x : X) : (S : R) ∉ (f x).asIdeal := by
  have h1 : (S : X.residueField x) ≠ 0 := natCast_ne_zero_of_pt (X.fromSpecResidueField x ≫ g) h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  have h2 : f x = (Spec.map φ) (IsLocalRing.closedPoint _) := by
    rw [hφ]
    exact (congrArg f (Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint _))).symm
  rw [h2]
  intro hS
  have h3 : φ.hom (S : R) ∈ IsLocalRing.maximalIdeal (X.residueField x) := hS
  rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero] at h3
  exact h3 h1

theorem isUnit_RZ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S : ℕ} (A : ℕ) (hS : 0 < S) :
    IsUnit (S : RZ H S A) := by
  refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩ (Subtype.ext ?_)
  have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  simp [this]

theorem exists_restrict {Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (s : Z ⟶ Sp R) (b : R →+* R') {S : ℕ}
    [IsOpenImmersion (spMap b)] (hS : IsUnit (S : R'))
    (hr : ∀ x : Sp R, x ∈ Set.range (spMap b) ↔ (S : R) ∉ x.asIdeal) (ρ : Z ⟶ Z) :
    ∃ ρ' : pullback s (spMap b) ⟶ pullback s (spMap b), ρ' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := by
  refine ⟨IsOpenImmersion.lift (pullback.fst s (spMap b)) (pullback.fst _ _ ≫ ρ) ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Pullback.range_fst]
  have := natCast_notMem (pullback.fst s (spMap b) ≫ ρ ≫ s) (pullback.snd s (spMap b)) hS w
  rw [Set.mem_preimage, hr]
  simpa using this

theorem pow_hom_eq_iterate {X : Scheme.{0}} (r : Aut X) (m : ℕ) :
    (r ^ m).asIso.hom = (fun f : X ⟶ X => f ≫ r.asIso.hom)^[m] (𝟙 _) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ← ih, pow_succ']; rfl

theorem card_stab_ne_zero {X Y : Scheme.{0}} {Γ : Type} [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (x : Y ⟶ X) {n J : ℕ}
    (hn : n.Prime) (h : ∀ g, x ≫ (ρ g).asIso.hom = x → g ^ n ^ J = 1) {k : Type} [Field k] (hk : (n : k) ≠ 0) :
    (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0 := by
  let P : Subgroup Γ :=
    { carrier := {g | x ≫ (ρ g).asIso.hom = x}
      one_mem' := by
        show x ≫ (ρ 1).asIso.hom = x
        rw [map_one]; exact Category.comp_id x
      mul_mem' := by
        intro a b ha hb
        show x ≫ (ρ (a * b)).asIso.hom = x
        rw [map_mul]
        show x ≫ (ρ b).asIso.hom ≫ (ρ a).asIso.hom = x
        rw [← Category.assoc, show x ≫ (ρ b).asIso.hom = x from hb]; exact ha
      inv_mem' := by
        intro a ha
        show x ≫ (ρ a⁻¹).asIso.hom = x
        rw [map_inv]
        show x ≫ (ρ a).asIso.inv = x
        exact (Iso.comp_inv_eq (ρ a).asIso).mpr (show x ≫ (ρ a).asIso.hom = x from ha).symm }
  haveI : Fact n.Prime := ⟨hn⟩
  have hP : IsPGroup n P := fun g => ⟨J, Subtype.ext (h g.1 g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have : Nat.card {g // x ≫ (ρ g).asIso.hom = x} = n ^ m := hm
  rw [this, Nat.cast_pow]
  exact pow_ne_zero _ hk

theorem exists_baseModel : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN1 n J T l₀ hn hJ hA
  have hnp : n.Prime := hn.1
  have hM : 0 < l₀.M := by have := l₀.three_le; omega
  have hS : 0 < n * l₀.M := Nat.mul_pos hnp.pos hM
  have hN : 0 < n ^ J := pow_pos hnp.pos _
  have hdiv : n ^ J ∣ (n * l₀.M) ^ J := pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
  let l₁ : Level H := { l₀ with A := n ^ J, A_pos := hN }
  have h₁ : l₁.A = n ^ J := rfl
  have R₀ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₀ (n * l₀.M) 0 hS (by simp [hA])
  rw [hA] at R₀
  obtain ⟨⟨β, hβ⟩, ft₀, ded₀⟩ := R₀
  obtain ⟨⟨β₁, hβ₁⟩, ft₁, ded₁⟩ := GlobalTheory.BaseRing.isDedFrac_RZ E H l₁ (n * l₀.M) J hS hdiv
  obtain ⟨⟨b, hb⟩, hb2⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H (n * l₀.M) (n * l₀.M) 1 (n ^ J) J hS hN dvd_rfl (one_dvd _)
  obtain ⟨bfin, -, -⟩ := (hb2 b hb).1 rfl hdiv
  obtain ⟨⟨b', hb'⟩, hb2'⟩ := GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H n (n * l₀.M) (n ^ J) (n ^ J) J hS hN (dvd_mul_right _ _) dvd_rfl
  obtain ⟨bop, brange⟩ := (hb2' b' hb').2 rfl
  obtain ⟨C₁, q, hq, qm, qfin, qj, qφ, qp⟩ := GlobalTheory.T.exists_compactModel_above_fullLevel E H D Xo n (n ^ J) T l₁ h₁ (n * l₀.M) J β₁ b' hS
    (dvd_mul_right _ _) hdiv hβ₁ hb'
  obtain ⟨k, r, ν, hr, hk, lev, -, -, -, -, -, rsurj⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN1 l₀ l₁
    ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  obtain ⟨Γ, _, _, ρ₀, τ₀, ν₀, inj, quot, hω⟩ := GlobalTheory.T.moduli_level_quotient_by_finite_group L1 L2 L3 E H D Xo hD hN1 l₀ l₁ r ν k hA rfl rfl hk hr lev
  have hU : IsUnit ((n * l₀.M : ℕ) : RZ H (n * l₀.M) (n ^ J)) := isUnit_RZ H _ hS
  obtain ⟨ρ, τ, mu, hact⟩ := GlobalTheory.exists_action_model hext E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ C₁ _
    (pullback.lift q C₁.s hq) Γ ρ₀ τ₀ ν₀ (ded₁ β₁ hβ₁) ft₁ (Xo l₁).univ.proper inferInstance (fun g => (hω g).1) (by
      intro ω
      obtain ⟨h1, -, -, g, σ, h4, h5, h6⟩ := hω ω
      obtain ⟨ρZ, hρZ⟩ := T.sym l₁ h₁ (ρ₀ ω).asIso (ν₀ ω) g σ h4 h5 (by rw [h1]; exact h6)
      obtain ⟨ρ', hρ'⟩ := exists_restrict T.s b' hU brange ρZ.hom
      refine ⟨ρ', ?_⟩
      rw [← cancel_mono (pullback.fst T.s (spMap b'))]
      simp only [Category.assoc, hρ', pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, qj, hρZ])
  have hover : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).asIso.hom = x →
      (ρ₀ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s := by
    intro κ _ x ω hx
    obtain ⟨-, -, -, g, σ, h4, h5, -⟩ := hω ω
    have := GlobalTheory.galoisPart_eq_refl_of_fixes_point E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ρ ω).asIso σ hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 h4 h5 κ x hx
    subst this
    rw [h5]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  have hφ : ∀ ω, C₁.m.φ ≫ (mu ω).φ = (ν₀ ω).φ ≫ C₁.m.φ := fun ω => by
    rw [(hact ω).1, (hω ω).1]; exact (hact ω).2.2
  have htriv : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X) (ω : Γ), x ≫ (ρ ω).asIso.hom = x →
      pullback.fst C₁.t.G.hom x ≫ (mu ω).φ = pullback.fst C₁.t.G.hom x := by
    intro κ _ _ x ω hx
    exact GlobalTheory.T.finiteOrderAutomorphism_fixing_level_trivial_on_fixedFibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ν₀ ω) (ρ ω).asIso (mu ω) hβ₁ hS ⟨J, hdiv⟩
      (hact ω).2.1 (hφ ω) (dvd_mul_left _ _) (hover κ x ω hx) (by rw [(hω ω).1]; exact (hω ω).2.2.1)
      ⟨τ ω, Nat.card Γ, Nat.card_pos, by rw [← map_pow, pow_card_eq_one', map_one], (hact ω).1.symm⟩ κ x hx
  have hcard : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ C₁.X),
      (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : κ) ≠ 0 := by
    intro κ _ _ x
    refine card_stab_ne_zero ρ x (J := J) hnp (fun ω hx => ?_) ?_
    · obtain ⟨h1, -, h3, g, σ, -, -, h6⟩ := hω ω
      have := GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre L1 L2 L3 E H D l₁ (Xo l₁) (n * l₀.M) β₁ C₁ (ρ₀ ω).asIso (ν₀ ω) (ρ ω).asIso (mu ω) hβ₁ hS ⟨J, hdiv⟩
        (hact ω).2.1 (hφ ω) (hover κ x ω hx) (by rw [h1]; exact h3) g (by rw [h1]; exact h6) κ x hx (htriv κ x ω hx)
      apply inj
      rw [map_pow, map_one]
      exact Aut.ext (Iso.ext ((pow_hom_eq_iterate _ _).trans this))
    · have := natCast_ne_zero_of_pt (x ≫ C₁.s) hU
      rw [Nat.cast_mul] at this
      exact left_ne_zero_of_mul this
  have good₁ : Good C₁.t := good_pullback L3.gtBaseChange E H _ _ T.t C₁.t q qm T.good
  have push := GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D l₁ _ _ _ (baseKA l₁) _ (Xo l₁).s (Xo l₁).univ (Xo l₁).s β₁ C₁
    (ded₁ β₁ hβ₁) good₁.2.2
  have hcomm : β₁.comp b = k.comp β := by
    ext x
    exact (hβ₁ (b x)).trans ((hb x).trans ((hβ x).symm.trans (hk (β x)).symm))
  obtain ⟨C, good, ⟨above⟩⟩ := GlobalTheory.T.exists_quotient_model_by_tame_finite_group E H _ _ _ (Xo l₁).s (Xo l₁).univ.t β₁ _ _ _ (Xo l₀).s (Xo l₀).univ.t β Γ C₁
    b k r ν ρ₀ τ₀ ρ τ mu (ded₁ β₁ hβ₁) (ded₀ β hβ) hcomm bfin hr quot (Xo l₁).univ.proper
    (fun g => ⟨(hact g).1, (hact g).2.1, (hact g).2.2, (hω g).2.1⟩) qp hcard
    (fun κ _ _ x g hx => by rw [← (hact g).1]; exact htriv κ x g hx) good₁ push
  have hcop : (n ^ J).Coprime l₁.M := ((GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 n hn l₁).pow_left J
  exact ⟨⟨hA, β, hβ, C, good,
    GlobalTheory.T.levelChange_extends_base_model hext L1 L2 L3 E H D Xo n (n ^ J) T hD l₀ l₁ h₁ _ _ β β₁ C C₁ b r ν above b' q hq (ded₀ β hβ)
      (ded₁ β₁ hβ₁) ft₀ bfin qfin qj hA rfl rfl hcop lev rsurj ⟨k, hk, hr, hcomm⟩,
    l₁, rfl, rfl, h₁, β₁, hβ₁, C₁, b, hb, r, ν, lev, rsurj, above, b', hb', q, hq, qfin, qm, qj, qφ⟩⟩

end GlobalTheory.BaseModelEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_model_semiAbelian : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (n J : ℕ) (T : Top Xo n (n ^ J)) (l₀ : Level H), AuxiliaryInertOddPrime H n → 1 ≤ J → l₀.A = 1 → Nonempty (BaseModel T l₀) := by
  first | exact @GlobalTheory.BaseModelEx.exists_baseModel | exact GlobalTheory.BaseModelEx.exists_baseModel | (intros; apply GlobalTheory.BaseModelEx.exists_baseModel <;> assumption)
end

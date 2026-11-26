module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransport
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

theorem isTateEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' χ χ' e hψ hχ he
  classical
  obtain ⟨_, hv1, hord, hres, _⟩ := continuous_iso_keeps_valuation k k' i hi
  set u : kˣ →* k'ˣ := Units.map i.toRingHom.toMonoidHom with hu
  have hcoe : ∀ x : kˣ, ((u x : k'ˣ) : k') = i x := fun x => rfl
  have hle : ∀ x y : k, valuation k' (i x) ≤ valuation k' (i y) ↔ valuation k x ≤ valuation k y := by
    intro x y
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy' : i y ≠ 0 := by simpa using hy
      have h1 := hv1 (x / y)
      rw [map_div₀, map_div₀, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hy'),
        div_le_one₀ ((Valuation.pos_iff _).2 hy)] at h1
      exact h1
  have hsurj : ∀ x' : k'ˣ, ∃ x : kˣ, u x = x' := fun x' =>
    ⟨Units.map i.symm.toRingHom.toMonoidHom x', by ext; simp [hu]⟩
  have huinj : Function.Injective u := fun x y h => by
    ext; exact i.injective (by simpa [hcoe] using congrArg (fun z : k'ˣ => (z : k')) h)
  have hunif : ∀ a : ℕ, ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧
      valuation k' (i p) = uniformizer k' ^ a := by
    intro a
    obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
    obtain ⟨q, hq, hq'⟩ := exists_unit_pow k' a
    refine ⟨p, hp, ?_⟩
    rw [← hq, ← hcoe, valuation_eq_iff_ord, hord, hp', hq']
  have hfilt : ∀ (x : kˣ) (b : ℕ), u x ∈ unitFilt k' b ↔ x ∈ unitFilt k b := by
    intro x b
    obtain ⟨p, hp, hp'⟩ := hunif b
    simp only [unitFilt, Set.mem_setOf_eq]
    have e1 : valuation k' ((u x : k'ˣ) : k') = 1 ↔ valuation k (x : k) = 1 := by
      rw [← ord_eq_zero_iff, ← ord_eq_zero_iff, hord]
    have e2 : valuation k' (((u x : k'ˣ) : k') - 1) ≤ uniformizer k' ^ b ↔
        valuation k ((x : k) - 1) ≤ uniformizer k ^ b := by
      have hs : i ((x : k) - 1) = i x - 1 := by rw [map_sub, map_one]
      rw [← hp, ← hp', hcoe, ← hle, hs]
    rw [e1, e2]
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := he
  refine ⟨u c, a, R.image u, ?_, ?_, ?_, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := i.surjective x'
    rw [hcoe, hle, ← hc x]
    constructor
    · intro h y hy
      rw [← hψ]
      exact h (i y) ((hle y x).2 hy)
    · intro h y' hy'
      obtain ⟨y, rfl⟩ := i.surjective y'
      rw [hψ]
      exact h y ((hle y x).1 hy')
  · refine ⟨fun x' hx' => ?_, fun b hb => ?_⟩
    · obtain ⟨x, rfl⟩ := hsurj x'
      rw [hχ]
      exact ha.1 x ((hfilt x a).1 hx')
    · obtain ⟨x, hx, hx'⟩ := ha.2 b hb
      exact ⟨u x, (hfilt x b).2 hx, by rw [hχ]; exact hx'⟩
  · refine ⟨fun r' hr' => ?_, fun y' hy' => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr'
      rw [hord, hord]
      exact hR.1 r hr
    · obtain ⟨y, rfl⟩ := hsurj y'
      rw [hord, hord] at hy'
      obtain ⟨r, ⟨hr, hrv⟩, hru⟩ := hR.2 y hy'
      refine ⟨u r, ⟨Finset.mem_image_of_mem u hr, ?_⟩, ?_⟩
      · rw [hcoe, hcoe, hcoe, ← map_sub i, hle]
        exact hrv
      · rintro r' ⟨hr', hr'v⟩
        obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 hr'
        rw [hcoe, hcoe, hcoe, ← map_sub i, hle] at hr'v
        rw [hru r0 ⟨hr0, hr'v⟩]
  · rw [hres, Finset.sum_image (fun x _ y _ h => huinj h)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hχ, hcoe, hψ]

end GlobalTheory.LocalFieldIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransportStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  first | exact @GlobalTheory.LocalFieldIso.isTateEps_transport | exact GlobalTheory.LocalFieldIso.isTateEps_transport | (intros; apply GlobalTheory.LocalFieldIso.isTateEps_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductive
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilBrauer

theorem eq_of_induced : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  intro hB E Ω _ _ _ _ _ A w h ε ε' hε hε' hcp hchar hind
  classical
  set f : WD h → ℂˣ := fun x => ε x / ε' x with hf
  have fmul : ∀ x y, f (x.lpSum y) = f x * f y := by
    intro x y
    simp only [hf, hε, hε']
    exact mul_div_mul_comm _ _ _ _
  have fcp : ∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hcp x y hxy
    simp only [hf, h1, h2]
  have key : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → f (WD.mk (a.twist μ hμ)) = 1 := by
    intro n a μ hμ hfin
    let u : Weil h →* (Module.End ℂ (Fin n → ℂ))ˣ := a.ρ.toHomUnits
    let G : Subgroup (Module.End ℂ (Fin n → ℂ))ˣ := u.range
    have hGfin : Finite G := by
      have hr : (Set.range u).Finite := by
        refine Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
        refine hfin.subset ?_
        rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      have : ((G : Set (Module.End ℂ (Fin n → ℂ))ˣ)) = Set.range u := MonoidHom.coe_range u
      exact Set.finite_coe_iff.mpr (this ▸ hr)
    letI : Fintype G := Fintype.ofFinite G
    let π : Weil h →* G := u.rangeRestrict
    have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective u
    let ρG : Representation ℂ G (Fin n → ℂ) := (Units.coeHom _).comp G.subtype
    have hρG : ∀ σ, ρG (π σ) = a.ρ σ := fun σ => rfl
    have hπ1 : ∀ σ, π σ = 1 ↔ a.ρ σ = 1 := by
      intro σ
      constructor
      · intro h1
        rw [← hρG, h1, map_one]
      · intro h1
        apply Subtype.ext
        apply Units.ext
        exact h1
    have hopen : IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} := by
      have : {σ : Ine (F := E) A | π (ineIncl h σ) = 1} = {σ | a.ρ (ineIncl h σ) = 1} :=
        Set.ext fun σ => hπ1 _
      rw [this]
      exact a.smooth
    obtain ⟨r, H, χ, c, hbr⟩ := hB G (Fin n → ℂ) ρG
    have hi1 := fun i => GlobalTheory.T.induced_representation_character G (H i) (χ i)
    have hi2 := fun i => GlobalTheory.T.induced_representation_character G (H i) 1
    choose Rχ vχ hRχ using hi1
    choose R1 v1 hR1 using hi2
    have hp1 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (Rχ i) μ hμ
    have hp2 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (R1 i) μ hμ
    choose bχ hbχ using hp1
    choose b1 hb1 using hp2
    have span_of : ∀ (i : Fin r) (R : Representation ℂ G (Fin (H i).index → ℂ))
        (b : WDRep h (Fin (H i).index → ℂ)) (v : Fin (H i).index → ℂ),
        (∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ)) → Submodule.span ℂ (Set.range fun g => R g v) = ⊤ →
        Submodule.span ℂ (Set.range fun σ => b.ρ σ v) = ⊤ := by
      intro i R b v hb hs
      rw [eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨σ, rfl⟩ := hπs g
      show R (π σ) v ∈ _
      have e : R (π σ) v = (((μ σ)⁻¹ : ℂˣ) : ℂ) • b.ρ σ v := by
        rw [hb, LinearMap.smul_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
    have hpair : ∀ i, f (WD.mk (bχ i)) = f (WD.mk (b1 i)) := by
      intro i
      let H' := (H i).comap π
      have hidx : (H i).index = H'.index := (Subgroup.index_comap_of_surjective _ hπs).symm
      haveI : H'.FiniteIndex := ⟨by rw [← hidx]; exact Subgroup.index_ne_zero_of_finite⟩
      have hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H'} := by
        have hle : (π.comp (ineIncl h)).ker ≤ H'.comap (ineIncl h) := by
          intro σ hσ
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ
          show π (ineIncl h σ) ∈ H i
          rw [hσ]
          exact one_mem _
        exact Subgroup.isOpen_mono hle hopen
      let χ₁ : H' →* ℂˣ := μ.comp H'.subtype * (χ i).comp (π.subgroupComap (H i))
      let χ₂ : H' →* ℂˣ := μ.comp H'.subtype * (1 : H i →* ℂˣ).comp (π.subgroupComap (H i))
      have e1 : ∀ σ : H', (bχ i).ρ σ (vχ i) = (χ₁ σ : ℂ) • vχ i := by
        intro σ
        rw [hbχ, LinearMap.smul_apply, (hRχ i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have e2 : ∀ σ : H', (b1 i).ρ σ (v1 i) = (χ₂ σ : ℂ) • v1 i := by
        intro σ
        rw [hb1, LinearMap.smul_apply, (hR1 i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have hh := hind H' inferInstance hop χ₁ χ₂ _ (bχ i) (b1 i) (vχ i) (v1 i) hidx e1 e2
        (span_of i _ _ _ (hbχ i) (hRχ i).2.1) (span_of i _ _ _ (hb1 i) (hR1 i).2.1)
      simp only [hf]
      exact div_eq_div_iff_mul_eq_mul.mpr hh
    have hμ1 : f (WD.mk (WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ)) = 1 := by
      have := hchar μ hμ
      simp only [hf]
      exact div_eq_one.mpr this
    let F : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → Σ m, WDRep h (Fin m → ℂ) :=
      Sum.elim (Sum.elim (fun _ => ⟨n, a.twist μ hμ⟩)
          (fun _ => ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ⟩))
        (Sum.elim (fun i => ⟨_, bχ i⟩) (fun i => ⟨_, b1 i⟩))
    let cc : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → ℤ :=
      Sum.elim (Sum.elim (fun _ => 1) (fun _ => -(n : ℤ))) (Sum.elim (fun i => -c i) (fun i => c i))
    have htr : ∀ σ, ∑ j, (cc j : ℂ) * LinearMap.trace ℂ (Fin (F j).1 → ℂ) ((F j).2.ρ σ) = 0 := by
      intro σ
      have hb := hbr (π σ)
      rw [Module.finrank_fin_fun] at hb
      have t0 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inl (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inl (default : Unit)))).2.ρ σ) =
          (μ σ : ℂ) * LinearMap.trace ℂ (Fin n → ℂ) (ρG (π σ)) := by
        show LinearMap.trace ℂ (Fin n → ℂ) ((a.twist μ hμ).ρ σ) = _
        rw [WDRep.twist_ρ, map_smul, smul_eq_mul, hρG]
      have t1 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inr (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inr (default : Unit)))).2.ρ σ) = (μ σ : ℂ) := by
        show LinearMap.trace ℂ (Fin 1 → ℂ)
          ((WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ).ρ σ) = _
        rw [WDRep.ofChars_ρ]
        have e : (GlobalTheory.WeilDeligne.diagEnd fun _ : Fin 1 => (μ σ : ℂ)) = (μ σ : ℂ) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
          ext v i
          simp
        rw [e, map_smul, LinearMap.trace_one, smul_eq_mul, Module.finrank_fin_fun, Nat.cast_one,
          mul_one]
      have tχ : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inl i))).1 → ℂ)
          ((F (Sum.inr (Sum.inl i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((bχ i).ρ σ) = _
        rw [hbχ, map_smul, smul_eq_mul, (hRχ i).2.2]
      have t1' : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inr i))).1 → ℂ)
          ((F (Sum.inr (Sum.inr i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((b1 i).ρ σ) = _
        rw [hb1, map_smul, smul_eq_mul, (hR1 i).2.2]
        simp
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, t0, t1, tχ, t1']
      simp only [cc, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg, Int.cast_natCast,
        one_mul]
      have hs : ∑ i, -(c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)) +
          ∑ i, (c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)) =
          -(μ σ : ℂ) * ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) (π σ) -
            indFun (H i) (fun _ => 1) (π σ)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hs]
      linear_combination (μ σ : ℂ) * hb
    have hv := GlobalTheory.T.multiplicative_virtual_character E Ω A w h f fmul fcp _ (fun j => (F j).1) (fun j => (F j).2) cc htr
    have hμ1' : f (WD.mk (F (Sum.inl (Sum.inr (default : Unit)))).2) = 1 := hμ1
    have hp' : ∀ i, f (WD.mk (F (Sum.inr (Sum.inl i))).2) = f (WD.mk (F (Sum.inr (Sum.inr i))).2) :=
      hpair
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, hμ1', hp'] at hv
    simp only [cc, Sum.elim_inl, Sum.elim_inr, zpow_one, _root_.zpow_neg, _root_.one_zpow, inv_one,
      mul_one, ← Finset.prod_mul_distrib, _root_.inv_mul_cancel, Finset.prod_const_one] at hv
    exact hv
  intro x
  have hx := GlobalTheory.T.weil_deligne_induction_principle E Ω A w h (fun x => f x = 1)
    (fun x y hx hy => by rw [fmul, hx, hy, one_mul])
    (fun x y hxy hx => by rw [← fcp x y hxy, hx]) key x
  simp only [hf] at hx
  exact div_eq_one.mp hx

end GlobalTheory.WeilBrauer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductiveStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_unique_of_inductive : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  first | exact @GlobalTheory.WeilBrauer.eq_of_induced | exact GlobalTheory.WeilBrauer.eq_of_induced | (intros; apply GlobalTheory.WeilBrauer.eq_of_induced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeField
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem trace_map_of_adjoin_range_eq_top_of_finrank_eq : ∀ (E L E' L' : Type) [Field E] [Field L] [Algebra E L] [FiniteDimensional E L] [Field E'] [Field L'] [Algebra E' L'] (j : E →+* E') (jL : L →+* L'), (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Module.finrank E' L' = Module.finrank E L → ∀ z, Algebra.trace E' L' (jL z) = j (Algebra.trace E L z) := by
  intro E L E' L' _ _ _ _ _ _ _ j jL hcomp hadj hrank z
  classical
  set n := Module.finrank E L
  let b : Module.Basis (Fin n) E L := Module.finBasis E L
  have hpos : 0 < Module.finrank E' L' := by rw [hrank]; exact Module.finrank_pos
  haveI : FiniteDimensional E' L' := Module.finite_of_finrank_pos hpos
  let v : Fin n → L' := fun k => jL (b k)
  have hexp : ∀ w : L, jL w = ∑ k, j (b.repr w k) • v k := by
    intro w
    conv_lhs => rw [← b.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hcomp, ← Algebra.smul_def]
  have hspan : Submodule.span E' (Set.range jL) ≤ Submodule.span E' (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [hexp w]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hadj' : Subalgebra.toSubmodule (Algebra.adjoin E' (Set.range jL)) = Submodule.span E' (Set.range jL) := by
    apply Algebra.adjoin_eq_span_of_subset
    have : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL := by
      have := Submonoid.closure_eq (MonoidHom.mrange (jL : L →* L'))
      simpa using congrArg (fun S : Submonoid L' => (S : Set L')) this
    rw [this]; exact Submodule.subset_span
  have htop : (⊤ : Submodule E' L') ≤ Submodule.span E' (Set.range v) := by
    rw [hadj, Algebra.top_toSubmodule] at hadj'
    rw [hadj']; exact hspan
  let b' : Module.Basis (Fin n) E' L' := basisOfTopLeSpanOfCardEqFinrank v htop (by simp [hrank, n])
  have hb' : ∀ k, b' k = v k := fun k => by simp [b']
  have hrepr : ∀ w : L, ∀ i, b'.repr (jL w) i = j (b.repr w i) := by
    intro w i
    have : jL w = b'.equivFun.symm (fun k => j (b.repr w k)) := by
      rw [Module.Basis.equivFun_symm_apply, hexp w]
      simp [hb']
    rw [← b'.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', v, ← map_mul, hrepr]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeFieldStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_base_change_field : ∀ (E L E' L' : Type) [Field E] [Field L] [Algebra E L] [FiniteDimensional E L] [Field E'] [Field L'] [Algebra E' L'] (j : E →+* E') (jL : L →+* L'), (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Module.finrank E' L' = Module.finrank E L → ∀ z, Algebra.trace E' L' (jL z) = j (Algebra.trace E L z) := by
  first | exact @GlobalTheory.trace_map_of_adjoin_range_eq_top_of_finrank_eq | exact GlobalTheory.trace_map_of_adjoin_range_eq_top_of_finrank_eq | (intros; apply GlobalTheory.trace_map_of_adjoin_range_eq_top_of_finrank_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransport
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped IntermediateField

noncomputable section

theorem GlobalTheory.LocLanglands.exists_isLocalExt_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (c : Weil h ≃* Weil h'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → (∀ σ, WeilRel φ σ (c σ)) → ∀ L : IntermediateField E Ω, FiniteDimensional E L → IsLocalExt L h → ∃ (L' : IntermediateField E' Ω') (jL : L →+* L'), FiniteDimensional E' L' ∧ IsLocalExt L' h' ∧ Module.finrank E' L' = Module.finrank E L ∧ (∀ x : L, φ (x : Ω) = (jL x : Ω')) ∧ Algebra.adjoin E' (Set.range jL) = ⊤ := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j c hφ hc L hL hloc
  classical
  haveI := IsAlgClosure.isAlgebraic (R := E) (K := Ω)
  haveI := IsAlgClosure.isAlgebraic (R := E') (K := Ω')

  obtain ⟨α, rfl⟩ : ∃ α : Ω, E⟮α⟯ = L := by
    obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element E L
    refine ⟨(α₀ : Ω), ?_⟩
    have := congrArg (IntermediateField.map L.val) hα₀
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this
  have hint : IsIntegral E α := Algebra.IsIntegral.isIntegral α
  set α' : Ω' := φ α with hα'
  have hint' : IsIntegral E' α' := Algebra.IsIntegral.isIntegral α'
  set p := minpoly E α with hp
  set m' := minpoly E' α' with hm'
  have hcomp : (algebraMap E' Ω').comp j = (φ : Ω →+* Ω').comp (algebraMap E Ω) := by
    ext x; exact (hφ x).symm
  have key : ∀ β : Ω, φ (aeval β p) = aeval (φ β) (p.map j) := by
    intro β
    rw [aeval_def, aeval_def, eval₂_map, hcomp]
    exact Polynomial.hom_eval₂ p (algebraMap E Ω) (φ : Ω →+* Ω') β
  have hpmon : p.Monic := minpoly.monic hint
  have hqne : p.map j ≠ 0 := (hpmon.map j).ne_zero
  have hdvd : m' ∣ p.map j := minpoly.dvd E' α' (by rw [← key, minpoly.aeval]; simp)
  have hm'root : ∀ σ' : G E' Ω', aeval (σ' α') m' = 0 := by
    intro σ'
    rw [show σ' α' = (σ' : Ω' →ₐ[E'] Ω') α' from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hq : ∀ y : Ω', aeval y m' = 0 → aeval y (p.map j) = 0 := by
    intro y hy
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, hy, zero_mul]

  have horb : ∀ β : Ω, aeval β p = 0 → ∃ τ : Weil h, (τ : G E Ω) α = β := by
    intro β hβ
    have hmin : minpoly E β = minpoly E α :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ hpmon).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 hmin
    obtain ⟨τ, hτ⟩ := hloc σ
    refine ⟨τ, ?_⟩
    have := hτ ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩
    simp only [IntermediateField.algebraMap_apply] at this
    rw [this]; exact hσ

  set L' : IntermediateField E' Ω' := E'⟮α'⟯ with hL'
  have hsub : ∀ x : E⟮α⟯, φ (x : Ω) ∈ L' := by
    let S : IntermediateField E Ω := Subfield.toIntermediateField
      (L'.toSubfield.comap (φ : Ω →+* Ω')) (fun x => by
        show φ (algebraMap E Ω x) ∈ L'
        rw [hφ]; exact L'.algebraMap_mem (j x))
    have hle : E⟮α⟯ ≤ S := IntermediateField.adjoin_simple_le_iff.2
      (show φ α ∈ L' from IntermediateField.mem_adjoin_simple_self E' α')
    intro x
    exact hle x.2
  let jL : E⟮α⟯ →+* L' := RingHom.codRestrict ((φ : Ω →+* Ω').comp (algebraMap E⟮α⟯ Ω)) L' hsub
  refine ⟨L', jL, IntermediateField.adjoin.finiteDimensional hint', ?_, ?_, fun x => rfl, ?_⟩
  ·
    intro σ'
    have h1 : aeval (σ' α') (p.map j) = 0 := hq _ (hm'root σ')
    have h2 : aeval (φ.symm (σ' α')) p = 0 := by
      apply φ.injective; rw [key, φ.apply_symm_apply, h1, map_zero]
    obtain ⟨τ, hτ⟩ := horb _ h2
    refine ⟨c τ, fun x => ?_⟩
    have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
    have hx : (c τ : G E' Ω') α' = σ' α' := by
      rw [← e, hτ, φ.apply_symm_apply]
    have hle : L'.toSubalgebra ≤ AlgHom.equalizer ((c τ : G E' Ω') : Ω' →ₐ[E'] Ω') (σ' : Ω' →ₐ[E'] Ω') := by
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic, Algebra.adjoin_le_iff,
        Set.singleton_subset_iff]
      exact hx
    exact hle x.2
  · rw [IntermediateField.adjoin.finrank hint', IntermediateField.adjoin.finrank hint]
    apply le_antisymm
    · calc m'.natDegree ≤ (p.map j).natDegree := natDegree_le_of_dvd hdvd hqne
        _ = p.natDegree := natDegree_map j
    · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
      haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed E'
      have hsep : p.Separable := (minpoly.irreducible hint).separable
      have hnd : (p.aroots Ω).Nodup := nodup_roots (hsep.map)
      have hm'ne : m' ≠ 0 := minpoly.ne_zero hint'
      have hpne : p ≠ 0 := hpmon.ne_zero
      have himg : (p.aroots Ω).toFinset.image φ ⊆ (m'.aroots Ω').toFinset := by
        intro y hy
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hy
        rw [Multiset.mem_toFinset, mem_aroots] at hβ ⊢
        obtain ⟨τ, rfl⟩ := horb _ hβ.2
        refine ⟨hm'ne, ?_⟩
        have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
        rw [e]; exact hm'root _
      calc p.natDegree = (p.aroots Ω).card := IsAlgClosed.card_aroots_eq_natDegree.symm
        _ = (p.aroots Ω).toFinset.card := (Multiset.toFinset_card_of_nodup hnd).symm
        _ = ((p.aroots Ω).toFinset.image φ).card := (Finset.card_image_of_injective _ φ.injective).symm
        _ ≤ (m'.aroots Ω').toFinset.card := Finset.card_le_card himg
        _ ≤ (m'.aroots Ω').card := Multiset.toFinset_card_le _
        _ = m'.natDegree := IsAlgClosed.card_aroots_eq_natDegree
  ·
    apply Subalgebra.map_injective (f := L'.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, IntermediateField.range_val]
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (jL x).2
    · have hsg : ({α'} : Set Ω') ⊆ L'.val '' Set.range jL :=
        Set.singleton_subset_iff.2 ⟨jL ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩, ⟨_, rfl⟩, rfl⟩
      refine le_trans ?_ (Algebra.adjoin_mono hsg)
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransportStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_group_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (c : Weil h ≃* Weil h'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → (∀ σ, WeilRel φ σ (c σ)) → ∀ L : IntermediateField E Ω, FiniteDimensional E L → IsLocalExt L h → ∃ (L' : IntermediateField E' Ω') (jL : L →+* L'), FiniteDimensional E' L' ∧ IsLocalExt L' h' ∧ Module.finrank E' L' = Module.finrank E L ∧ (∀ x : L, φ (x : Ω) = (jL x : Ω')) ∧ Algebra.adjoin E' (Set.range jL) = ⊤ := by
  first | exact @GlobalTheory.LocLanglands.exists_isLocalExt_transport | exact GlobalTheory.LocLanglands.exists_isLocalExt_transport | (intros; apply GlobalTheory.LocLanglands.exists_isLocalExt_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.EpsUnique

theorem index_eq_finrank : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v), IsLocalExt L h → ∀ H : Subgroup (Weil h), (∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) → H.index = Module.finrank K L := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v h hL H hH
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  let f : Weil h → (L →ₐ[K] Ω) := fun σ => (σ : G K Ω).toAlgHom.comp (IsScalarTower.toAlgHom K L Ω)
  have hf : ∀ σ τ : Weil h, f σ = f τ ↔ σ⁻¹ * τ ∈ H := fun σ τ => by
    rw [hH, AlgHom.ext_iff]
    refine forall_congr' fun x => ?_
    show (σ : G K Ω) (algebraMap L Ω x) = (τ : G K Ω) (algebraMap L Ω x) ↔
      (σ : G K Ω).symm ((τ : G K Ω) (algebraMap L Ω x)) = _
    rw [AlgEquiv.symm_apply_eq, eq_comm]
  have hs : Function.Surjective f := fun s => by
    obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
    exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (s.liftNormal_commutes Ω x)⟩
  let g : Weil h ⧸ H → (L →ₐ[K] Ω) := Quotient.lift f fun σ τ hστ => (hf σ τ).2 (QuotientGroup.leftRel_apply.1 hστ)
  have hg : Function.Bijective g := by
    refine ⟨fun a b => Quotient.inductionOn₂ a b fun σ τ e => QuotientGroup.eq.2 ((hf σ τ).1 e), fun s => ?_⟩
    obtain ⟨σ, rfl⟩ := hs s
    exact ⟨QuotientGroup.mk σ, rfl⟩
  rw [Subgroup.index, Nat.card_eq_of_bijective g hg, Nat.card_eq_fintype_card, AlgHom.card]

theorem induces_of_eigenvector : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (r : Weil h' →* Weil h), (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) → (∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r)) → ∀ (n : ℕ) (b : WDRep h (Fin n → ℂ)) (u : Fin n → ℂ) (ξ : Weil h' →* ℂˣ), n = Module.finrank K L → (∀ σ, b.ρ (r σ) u = (ξ σ : ℂ) • u) → Submodule.span ℂ (Set.range fun σ => b.ρ σ u) = ⊤ → ∃ hξ : GlobalTheory.WeilDeligne.IsSmooth ξ, Induces (WD.lpOfChar h' ξ hξ) (WD.mk b) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' r hr hs n b u ξ hn hu hsp
  have hu0 : u ≠ 0 := by
    rintro rfl
    haveI : Nonempty (Fin n) := ⟨⟨0, hn ▸ Module.finrank_pos⟩⟩
    refine bot_ne_top (α := Submodule ℂ (Fin n → ℂ)) (hsp ▸ (Submodule.span_eq_bot.2 ?_).symm)
    rintro _ ⟨σ, rfl⟩
    simp
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := (hs _ b.ρ b.smooth).of_le fun σ hσ => by
    have h1 := hu σ
    rw [show b.ρ (r σ) = 1 from hσ] at h1
    exact Units.ext (smul_left_injective ℂ hu0 (by simpa using h1.symm))
  refine ⟨hξ, 1, n, _, b, (LinearMap.proj (0 : Fin 1)).smulRight u, rfl, rfl, by simp [hn], fun σ' σ hσ x => ?_, ?_⟩
  · rw [show σ = r σ' from Subtype.ext (AlgEquiv.ext fun z => (hσ z).trans (hr σ' z).symm)]
    simp [hu, smul_smul, mul_comm]
  · rw [eq_top_iff, ← hsp]
    refine Submodule.span_mono ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨(σ, fun _ => 1), by simp⟩

section One

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem induces_of_charPol {x y : WD h} (hxy : ∀ σ, x.charPol σ = y.charPol σ) : Induces x y := by
  obtain ⟨m, a, rfl⟩ := x.exists_rep
  obtain ⟨n, b, rfl⟩ := y.exists_rep
  simp only [WD.charPol_mk] at hxy
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq a.ρ b.ρ (GlobalTheory.T.weil_deligne_semisimple E Ω A w h m a) (GlobalTheory.T.weil_deligne_semisimple E Ω A w h n b)
    fun g => by
      have h1 := hxy g
      rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin m)),
        ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n))] at h1
      rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin m)),
        LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), Matrix.trace_eq_neg_charpoly_nextCoeff,
        Matrix.trace_eq_neg_charpoly_nextCoeff, h1]
  have hmn : n = m := by simpa using e.finrank_eq.symm
  refine ⟨m, n, a, b, e, rfl, rfl, by simp [hmn], fun σ' σ hσ u => ?_, ?_⟩
  · rw [show σ = σ' from Subtype.ext (AlgEquiv.ext hσ)]; exact he _ _
  · exact eq_top_iff.2 fun u _ => Submodule.subset_span ⟨(1, e.symm u), by simp⟩

theorem eps_eq_of_charPol {ε : EpsFamily A} (hε : IsDeligneEps ε) {ψ : AddChar (w.adicCompletion E) Circle}
    (hc : Continuous ψ) (h1 : ψ ≠ 1) {x y : WD h} (hxy : ∀ σ, x.charPol σ = y.charPol σ) :
    ε E w h ψ x = ε E w h ψ y := by
  have := hε.ind E E w w h h (isLocalExt_self h) ψ ψ hc h1 hc (fun z => by simp) x x y x
    (induces_of_charPol hxy) (induces_self x) rfl
  exact (mul_right_cancel this).symm

theorem exists_place (h : IsPlaceOver A w) (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra E L]
    [IsScalarTower E L Ω] : ∃ v : HeightOneSpectrum (𝓞 L), IsPlaceOver A v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := fun x => by
    have h1 : IsIntegral ℤ (algebraMap L Ω x) := x.2.map (algebraMap L Ω).toIntAlgHom
    have h2 : IsIntegral A (algebraMap L Ω x) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact hy ▸ y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  have hf : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω x) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h0 => ?_⟩, hf⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have h3 := (hf (algebraMap (𝓞 E) (𝓞 L) x)).1 (by
    have := (h x).2 hx
    rwa [IsScalarTower.algebraMap_apply E L Ω] at this)
  rw [h0, Ideal.mem_bot] at h3
  exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L) (by simpa using h3))

theorem exists_addChar (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E L]
    [IsScalarTower E L Ω] {v : HeightOneSpectrum (𝓞 L)} (hv : IsPlaceOver A v) (hL : IsLocalExt L h)
    {ψ : AddChar (w.adicCompletion E) Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ ψL : AddChar (v.adicCompletion L) Circle, Continuous ψL ∧ ψL ≠ 1 ∧
      ∀ z : L, ψL (algebraMap L _ z) = ψ (algebraMap E _ (Algebra.trace E L z)) := by
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.T.local_trace_completion E L Ω A w v h hv hL
  refine ⟨ψ.compAddMonoidHom T, hc.comp hT, fun h0 => h1 ?_, fun z => by simp [hT']⟩
  ext x
  refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => (ψ x : ℂ) = (1 : AddChar _ Circle) x) x
    (isClosed_eq (continuous_subtype_val.comp hc) (by simpa using continuous_const)) fun a => ?_
  obtain ⟨z, rfl⟩ := Algebra.trace_surjective E L a
  have := DFunLike.congr_fun h0 (algebraMap L _ z)
  simp only [AddChar.compAddMonoidHom_apply, hT', AddChar.one_apply] at this
  simp [this]

end One

section Two

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem addChar_transport (hP : PlaceIso A w A' w' φ j i) {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x) :
    Continuous ψ' ∧ ψ' ≠ 1 := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w'.adicCompletion E') := charZero_of_injective_algebraMap (algebraMap E' _).injective
  refine ⟨?_, fun h0 => h1 ?_⟩
  · have : (ψ' : _ → Circle) = ψ ∘ i.symm := funext fun x => by simp [← hψ]
    rw [this]
    exact hc.comp (GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation _ _ i hP.cont).1
  · ext x
    simp [← hψ, h0]

theorem eps_char (hG : GlobalArtinReciprocity) (hC : ChevalleyUnits) (hL : LocalLanglandsExists)
    (hP : PlaceIso A w A' w' φ j i) {ε : EpsFamily A} {ε' : EpsFamily A'} (hε : IsDeligneEps ε)
    (hε' : IsDeligneEps ε') {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x)
    {ξ : Weil h →* ℂˣ} (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) {ξ' : Weil h' →* ℂˣ} (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ')
    (hr : ∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') :
    ε E w h ψ (WD.lpOfChar h ξ hξ) = ε' E' w' h' ψ' (WD.lpOfChar h' ξ' hξ') := by
  obtain ⟨hc', h1'⟩ := addChar_transport hP hc h1 hψ
  obtain ⟨-, a, ha, -⟩ := hL E Ω A w h
  obtain ⟨-, a', ha', -⟩ := hL E' Ω' A' w' h'
  obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
  obtain ⟨χ', hχ', rfl⟩ := ha'.factor ξ' hξ'
  obtain ⟨c, hcr, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i hP
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w'.adicCompletion E') := charZero_of_injective_algebraMap (algebraMap E' _).injective
  refine Units.ext ((GlobalTheory.T.tate_epsilon_transport _ _ i hP.cont ψ ψ' χ χ' _ hψ (fun x => ?_) (hε.char E w h ψ hc h1 a ha χ hχ)).unique
    (hε'.char E' w' h' ψ' hc' h1' a' ha' χ' hχ'))
  obtain ⟨σ, rfl⟩ := ha.surj x
  have h2 := (hcr σ _).2 rfl
  rw [← GlobalTheory.T.localArtinMap_unique_transport_placeIso hG hC E Ω A w h E' Ω' A' w' h' φ j i hP a a' ha ha' σ _ h2]
  exact (hr σ _ h2).symm

theorem valuation_lt_one_iff_map (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) < 1 ↔ A.valuation z < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ φ.injective]

theorem eps_ind (hG : GlobalArtinReciprocity) (hC : ChevalleyUnits) (hLL : LocalLanglandsExists)
    (hP : PlaceIso A w A' w' φ j i) {ε : EpsFamily A} {ε' : EpsFamily A'} (hε : IsDeligneEps ε)
    (hε' : IsDeligneEps ε') {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x)
    (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (H : Subgroup (Weil h)) (hH : H.FiniteIndex) (hHo : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H})
    (χ₁ χ₂ : H →* ℂˣ) {n : ℕ} (b₁ b₂ : WDRep h (Fin n → ℂ)) (b₁' b₂' : WDRep h' (Fin n → ℂ))
    (e₁ : ∀ σ, b₁'.ρ (c σ) = b₁.ρ σ) (e₂ : ∀ σ, b₂'.ρ (c σ) = b₂.ρ σ) (v₁ v₂ : Fin n → ℂ) (hn : n = H.index)
    (k₁ : ∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) (k₂ : ∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂)
    (s₁ : Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤)
    (s₂ : Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤) :
    ε E w h ψ (WD.mk b₁) * ε' E' w' h' ψ' (WD.mk b₂') = ε E w h ψ (WD.mk b₂) * ε' E' w' h' ψ' (WD.mk b₁') := by
  obtain ⟨hc', h1'⟩ := addChar_transport hP hc h1 hψ
  obtain ⟨L, hfin, hL, hHL⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hH hHo
  obtain ⟨L', jL, hfin', hL', hdeg, hφ, hadj⟩ :=
    GlobalTheory.T.weil_group_transport E Ω A w h E' Ω' A' w' h' φ j c hP.ext (fun σ => (hcr σ _).2 rfl) L hfin hL
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : NumberField L' := NumberField.of_module_finite E' L'
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI : IsAlgClosure L' Ω' := ⟨IsAlgClosure.isAlgClosed E', Algebra.IsAlgebraic.tower_top (K := E') L'⟩
  obtain ⟨v, hv⟩ := exists_place h L
  obtain ⟨v', hv'⟩ := exists_place h' L'
  have hj : ∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x) := fun x =>
    Subtype.ext ((hφ _).symm.trans (hP.ext x))
  obtain ⟨iL, hiL, hiL'⟩ := GlobalTheory.T.completion_base_change_places E L E' L' w v w' v' j jL i
    (fun x => by rw [← hv, ← h]; rfl) (fun x => by rw [← hv', ← h']; rfl)
    (fun x => by
      rw [← hv, ← hv', ← valuation_lt_one_iff_map hP.mem]
      exact Iff.of_eq (congrArg (fun z => A'.valuation z < 1) (hφ _).symm))
    hj hadj hP.cont hP.loc
  have hPL : PlaceIso A v A' v' φ jL iL := ⟨hP.mem, hφ, hiL, hiL'⟩
  obtain ⟨ψL, hcL, h1L, hψL⟩ := exists_addChar L hv hL hc h1
  obtain ⟨ψL', hcL', -, hψL'⟩ := exists_addChar L' hv' hL' hc' h1'
  have hψi : ∀ x, ψL' (iL x) = ψL x := fun x => by
    refine (HeightOneSpectrum.denseRange_algebraMap L v).induction_on (p := fun x => ψL' (iL x) = ψL x) x
      (isClosed_eq (hcL'.comp hiL) hcL) fun z => ?_
    rw [hiL', hψL', hψL, GlobalTheory.T.trace_base_change_field E L E' L' j jL hj hadj hdeg, ← hP.loc, hψ]
  obtain ⟨r, hr, hrs⟩ := GlobalTheory.T.weil_group_restriction E L Ω A w v h hv
  obtain ⟨r', hr', hrs'⟩ := GlobalTheory.T.weil_group_restriction E' L' Ω' A' w' v' h' hv'
  have hn' : n = Module.finrank E L := hn.trans (index_eq_finrank E L Ω A w h hL H hHL)
  have m : ∀ σ, r σ ∈ H := fun σ => (hHL _).2 fun x => by rw [hr]; exact (σ : G L Ω).commutes x
  have m' : ∀ σ, (c.symm.toMonoidHom.comp r') σ ∈ H := fun σ => (hHL _).2 fun x => by
    apply φ.injective
    show φ ((c.symm (r' σ) : G E Ω) x) = _
    rw [(hcr _ (r' σ)).2 (c.apply_symm_apply _), hr', hφ]
    exact (σ : G L' Ω').commutes (jL x)
  have key : ∀ (χ : H →* ℂˣ) (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)) (u : Fin n → ℂ),
      (∀ σ, b'.ρ (c σ) = b.ρ σ) → (∀ σ : H, b.ρ σ u = (χ σ : ℂ) • u) →
      Submodule.span ℂ (Set.range fun σ => b.ρ σ u) = ⊤ →
      ∃ (x : WD hv) (x' : WD hv'), Induces x (WD.mk b) ∧ Induces x' (WD.mk b') ∧ x.lpDim = 1 ∧ x'.lpDim = 1 ∧
        ε L v hv ψL x = ε' L' v' hv' ψL' x' := by
    intro χ b b' u e k s
    obtain ⟨p, hp⟩ := induces_of_eigenvector E L Ω A w v h hv r hr hrs n b u (χ.comp (r.codRestrict H m)) hn'
      (fun σ => k ⟨r σ, m σ⟩) s
    obtain ⟨p', hp'⟩ := induces_of_eigenvector E' L' Ω' A' w' v' h' hv' r' hr' hrs' n b' u
      (χ.comp ((c.symm.toMonoidHom.comp r').codRestrict H m')) (hn'.trans hdeg.symm)
      (fun σ => by
        have := k ⟨_, m' σ⟩
        rw [← e] at this
        simpa using this)
      (by
        rw [← s, ← c.surjective.range_comp]
        simp only [Function.comp_def, e])
    refine ⟨_, _, hp, hp', by simp [WD.lpOfChar], by simp [WD.lpOfChar],
      eps_char hG hC hLL hPL hε hε' hcL h1L hψi p p' fun σ σ' hσ => congrArg χ (Subtype.ext ?_)⟩
    show r σ = c.symm (r' σ')
    rw [eq_comm, MulEquiv.symm_apply_eq, eq_comm, ← hcr]
    intro z
    rw [hr, hr']
    exact hσ z
  obtain ⟨x₁, x₁', i₁, i₁', d₁, d₁', q₁⟩ := key χ₁ b₁ b₁' v₁ e₁ k₁ s₁
  obtain ⟨x₂, x₂', i₂, i₂', d₂, d₂', q₂⟩ := key χ₂ b₂ b₂' v₂ e₂ k₂ s₂
  have t := hε.ind E L w v h hv hL ψ ψL hc h1 hcL hψL x₁ x₂ _ _ i₁ i₂ (d₁.trans d₂.symm)
  have t' := hε'.ind E' L' w' v' h' hv' hL' ψ' ψL' hc' h1' hcL' hψL' x₁' x₂' _ _ i₁' i₂' (d₁'.trans d₂'.symm)
  rw [← q₁, ← q₂] at t'
  apply mul_right_cancel (b := ε L v hv ψL x₂)
  rw [mul_right_comm, t, mul_assoc _ (ε' E' w' h' ψ' (WD.mk b₁')), t']
  simp only [mul_assoc, mul_comm, mul_left_comm]

end Two

theorem eps_eq_of_placeIso : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (ε : EpsFamily A) (ε' : EpsFamily A'), IsDeligneEps ε → IsDeligneEps ε' → ∀ (ψ : AddChar (w.adicCompletion E) Circle) (ψ' : AddChar (w'.adicCompletion E') Circle), Continuous ψ → ψ ≠ 1 → (∀ x, ψ' (i x) = ψ x) → ∀ (y : WD h) (y' : WD h'), WDRel φ y y' → ε E w h ψ y = ε' E' w' h' ψ' y' := by
  intro hG hC hB hLL E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP ε ε' hε hε' ψ ψ' hc h1 hψ y y' hy
  obtain ⟨hc', h1'⟩ := addChar_transport hP hc h1 hψ
  obtain ⟨S, hS, -, -, hSadd, -, -, -, -, hSchar⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i hP
  obtain ⟨c, hcr, hdeg, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i hP
  have rep : ∀ (n : ℕ) (b : WDRep h (Fin n → ℂ)), ∃ b' : WDRep h' (Fin n → ℂ),
      S (WD.mk b) = WD.mk b' ∧ ∀ σ, b'.ρ (c σ) = b.ρ σ := by
    intro n b
    let b' : WDRep h' (Fin n → ℂ) :=
      { ρ := b.ρ.comp c.symm.toMonoidHom
        N := b.N
        smooth := (hsm _ _).2 (b.smooth.of_le fun σ hσ => by simpa using hσ)
        semisimple := fun σ => b.semisimple _
        nilpotent := b.nilpotent
        comm := fun σ => by
          have := b.comm (c.symm σ)
          rw [← hdeg, c.apply_symm_apply, ← hq] at this
          exact this }
    have hb : ∀ σ, b'.ρ (c σ) = b.ρ σ := fun σ => congrArg b.ρ (c.symm_apply_apply σ)
    exact ⟨b', (hS _ _).1 ⟨n, b, b', rfl, rfl, rfl, fun σ σ' hσ => by rw [← (hcr _ _).1 hσ, hb]⟩, hb⟩
  have hpol : ∀ x σ, (S x).charPol (c σ) = x.charPol σ := by
    intro x σ
    obtain ⟨n, b, rfl⟩ := x.exists_rep
    obtain ⟨b', h2, h3⟩ := rep n b
    rw [h2, WD.charPol_mk, WD.charPol_mk, h3]
  rw [← (hS y y').1 hy]
  refine GlobalTheory.T.epsilon_unique_of_inductive hB E Ω A w h (ε E w h ψ) (fun x => ε' E' w' h' ψ' (S x)) (hε.add E w h ψ hc h1)
    (fun x z => by rw [hSadd, hε'.add E' w' h' ψ' hc' h1']) (fun x z hxz => ⟨eps_eq_of_charPol hε hc h1 hxz,
      eps_eq_of_charPol hε' hc' h1' fun σ => ?_⟩) (fun ξ hξ => ?_)
    (fun H hH hHo χ₁ χ₂ n b₁ b₂ v₁ v₂ hn k₁ k₂ s₁ s₂ => ?_) y
  · obtain ⟨σ, rfl⟩ := c.surjective σ
    rw [hpol, hpol, hxz]
  · have hξ' : GlobalTheory.WeilDeligne.IsSmooth (ξ.comp c.symm.toMonoidHom) :=
      (hsm _ _).2 (hξ.of_le fun σ hσ => by simpa using hσ)
    have hr : ∀ σ σ', WeilRel φ σ σ' → ξ σ = (ξ.comp c.symm.toMonoidHom) σ' := fun σ σ' hσ => by
      simp [← (hcr _ _).1 hσ]
    rw [hSchar ξ hξ _ hξ' hr]
    exact eps_char hG hC hLL hP hε hε' hc h1 hψ hξ hξ' hr
  · obtain ⟨b₁', f₁, e₁⟩ := rep n b₁
    obtain ⟨b₂', f₂, e₂⟩ := rep n b₂
    rw [f₁, f₂]
    exact eps_ind hG hC hLL hP hε hε' hc h1 hψ c hcr H hH hHo χ₁ χ₂ b₁ b₂ b₁' b₂' e₁ e₂ v₁ v₂ hn k₁ k₂ s₁ s₂

end GlobalTheory.LocLanglands.EpsUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIsoStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_transport_field_iso : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (ε : EpsFamily A) (ε' : EpsFamily A'), IsDeligneEps ε → IsDeligneEps ε' → ∀ (ψ : AddChar (w.adicCompletion E) Circle) (ψ' : AddChar (w'.adicCompletion E') Circle), Continuous ψ → ψ ≠ 1 → (∀ x, ψ' (i x) = ψ x) → ∀ (y : WD h) (y' : WD h'), WDRel φ y y' → ε E w h ψ y = ε' E' w' h' ψ' y' := by
  first | exact @GlobalTheory.LocLanglands.EpsUnique.eps_eq_of_placeIso | exact GlobalTheory.LocLanglands.EpsUnique.eps_eq_of_placeIso | (intros; apply GlobalTheory.LocLanglands.EpsUnique.eps_eq_of_placeIso <;> assumption)
end

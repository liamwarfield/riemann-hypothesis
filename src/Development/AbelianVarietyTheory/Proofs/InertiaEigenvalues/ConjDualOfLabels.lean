module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWild
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWild
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.ConjDual

theorem valuation_lt_one_iff {Ω : Type} [Field Ω] {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω)
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) : A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hA, map_inv₀,
    EmbeddingLike.map_eq_zero_iff]

theorem tame_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {a : WDRep h V}
    (ha : a.Tame) : a.dual.Tame := by
  intro σ hσ
  have h1 : a.ρ σ⁻¹ = 1 := ha σ⁻¹ ((Wild E A).inv_mem hσ)
  rw [WDRep.dual_ρ, h1]
  ext
  simp

theorem transport_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'} (s : E → E) (c : Ω ≃+* Ω)
    (hc : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (x : WD h) (x' : WD h') (n : ℕ)
    (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ))
    (hb : WD.mk b = x.lpDual) (hb' : WD.mk b' = x') (hN : b.N = b'.N)
    (hρ : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ') :
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧ (x.tame → x'.tame) := by
  subst hb'
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpDual_mk] at hb
    refine ⟨fun h0 => ?_, ?_, fun h0 => ?_⟩
    · rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0 ⊢
      rw [← hN, ← WD.monodromyZero_ofWeilDeligneRepClass_iff, hb, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.dual_N, h0]
      ext
      simp
    · have h1 := congrArg WD.lpDim hb
      rw [WD.lpDim_mk, WD.lpDim_mk, Subspace.dual_finrank_eq] at h1
      rw [WD.lpDim_mk, WD.lpDim_mk, h1]
    · rw [WD.tame_mk] at h0 ⊢
      have h1 : b.Tame := by
        rw [← WD.tame_mk, hb, WD.tame_mk]
        exact tame_dual h0
      intro τ' hτ'
      let σ : G E Ω :=
        { (c.trans ((τ' : G E Ω) : Ω ≃+* Ω)).trans c.symm with
          commutes' := fun r => by
            show c.symm ((τ' : G E Ω) (c (algebraMap E Ω r))) = _
            rw [hc, AlgEquiv.commutes, ← hc, RingEquiv.symm_apply_apply] }
      have hσ : ∀ z, c (σ z) = (τ' : G E Ω) (c z) := fun z => c.apply_symm_apply _
      have hw : σ ∈ Wild E A := fun y hy => by
        rw [valuation_lt_one_iff c hA, map_sub, map_div₀, map_one, hσ]
        exact hτ' _ ((_root_.map_ne_zero c).2 hy)
      rw [← hρ ⟨σ, Ine_le_Weil h (Wild_le_Ine hw)⟩ τ' hσ]
      exact h1 _ hw

theorem mono_dim_wild : ∀ (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧
    ((∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) → x.inePol σ = (X - 1) ^ x.lpDim) →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w'), σ ∈ wildSet D.nd (D.nd.plOm.1 w') → x'.inePol σ = (X - 1) ^ x'.lpDim) := by
  intro D w w' c hc hA x x' n b b' hb hb' hN hρ
  obtain ⟨h1, h2, h3⟩ := transport_dual (fun y => D.host.conj y) c hc hA x x' n b b' hb hb' hN hρ
  refine ⟨h1, h2, fun H σ _ hσ => ?_⟩
  exact (WD.tame_iff_inePol x').mp (h3 ((WD.tame_iff_inePol x).mpr
    fun τ hτ => H τ (Wild_le_Ine hτ) hτ)) σ hσ

end GlobalTheory.WeilDeligne.ConjDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWildStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneDualTransport_monodromy_dim_wild : ∀ (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧
    ((∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) → x.inePol σ = (X - 1) ^ x.lpDim) →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w'), σ ∈ wildSet D.nd (D.nd.plOm.1 w') → x'.inePol σ = (X - 1) ^ x'.lpDim) := by
  first | exact @GlobalTheory.WeilDeligne.ConjDual.mono_dim_wild | exact GlobalTheory.WeilDeligne.ConjDual.mono_dim_wild | (intros; apply GlobalTheory.WeilDeligne.ConjDual.mono_dim_wild <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRoots
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.LabTransport

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}

theorem val_lt_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A'.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc,
    map_eq_zero_iff _ c.injective]


omit [NumberField E] in
theorem normV_eq (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A')
    (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') : normV w' = normV w := by
  let t : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv s
  have h1 : w.asIdeal = w'.asIdeal.comap t := by
    ext x
    rw [Ideal.mem_comap, ← h x, ← h' (t x), ← val_lt_iff c hc, hs]
    rfl
  have h2 : w'.asIdeal = w.asIdeal.map (t : 𝓞 E →+* 𝓞 E) := by
    rw [h1]
    exact (Ideal.map_comap_of_surjective (t : 𝓞 E →+* 𝓞 E) t.surjective _).symm
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal w'.asIdeal t h2).toEquiv).symm


open Pointwise in
theorem mem_Ine_of (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) (h : γ ∈ Ine (F := E) A) : γ' ∈ Ine (F := E) A' := by
  refine ⟨?_, fun x hx => ?_⟩
  · change γ' • A' = A'
    ext x
    obtain ⟨x, rfl⟩ := γ'.surjective x
    obtain ⟨x, rfl⟩ := c.surjective x
    rw [← AlgEquiv.smul_def, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, hγ,
      ← hc, ← hc, apply_mem_iff_of_mem_Dec h.1]
  · obtain ⟨x, rfl⟩ := c.surjective x
    rw [hγ, ← map_sub, val_lt_iff c hc]
    refine h.2 x ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hc x).mpr hx

theorem mem_Ine_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) : γ' ∈ Ine (F := E) A' ↔ γ ∈ Ine (F := E) A :=
  ⟨mem_Ine_of c.symm (fun y => by rw [hc, c.apply_symm_apply])
    (fun y => by rw [eq_comm, c.symm_apply_eq, ← hγ, c.apply_symm_apply]), mem_Ine_of c hc hγ⟩


omit [NumberField E] in
theorem mem_Wild_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) : γ' ∈ Wild E A' ↔ γ ∈ Wild E A := by
  rw [mem_Wild, mem_Wild, c.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [map_ne_zero_iff _ c.injective, hγ, ← val_lt_iff c hc, map_sub c,
    map_div₀ c, map_one c]


omit [NumberField E] in
theorem exists_conj (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (γ : G E Ω) :
    ∃ γ' : G E Ω, ∀ y, γ' (c y) = c (γ y) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (c.symm.trans γ.toRingEquiv).trans c) fun x => ?_,
    fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective x
    show c (γ (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, AlgEquiv.commutes]
  · show c (γ (c.symm _)) = _
    rw [c.symm_apply_apply]


omit [NumberField E] in
theorem exists_conj' (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (γ' : G E Ω) :
    ∃ γ : G E Ω, ∀ y, γ' (c y) = c (γ y) := by
  obtain ⟨γ, hγ⟩ := exists_conj s.symm c.symm
    (fun x => by rw [c.symm_apply_eq, hs, s.apply_symm_apply]) γ'
  refine ⟨γ, fun y => ?_⟩
  have := hγ (c y)
  rw [c.symm_apply_apply] at this
  rw [this, c.apply_symm_apply]

variable [IsAlgClosure E Ω]

theorem lab_eq (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A')
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : WDRep h V) (b' : WDRep h' V)
    (hb : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ')
    {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) :
    WD.lab t γ' (WD.mk b') = WD.lab t γ (WD.mk b) := by
  have hiff : TeichmullerInertiaLabelCondition A' w' t γ' ↔ TeichmullerInertiaLabelCondition A w t γ := by
    unfold TeichmullerInertiaLabelCondition
    rw [normV_eq s c hs hc h h', mem_Ine_iff c hc hγ]
  by_cases H : TeichmullerInertiaLabelCondition A w t γ
  · have H' := hiff.mpr H
    have hsp : b.tameSpace = b'.tameSpace := by
      ext v
      rw [WDRep.mem_tameSpace, WDRep.mem_tameSpace]
      constructor
      · intro hv σ' hσ'
        obtain ⟨σ, hσ⟩ := exists_conj' s c hs (σ' : G E Ω)
        have h1 := (mem_Wild_iff c hc hσ).mp hσ'
        rw [← hb ⟨σ, Ine_le_Weil h (Wild_le_Ine h1)⟩ σ' fun z => (hσ z).symm]
        exact hv _ h1
      · intro hv σ hσ1
        obtain ⟨σ', hσ⟩ := exists_conj s c hs (σ : G E Ω)
        have h1 := (mem_Wild_iff c hc hσ).mpr hσ1
        rw [hb σ ⟨σ', Ine_le_Weil h' (Wild_le_Ine h1)⟩ fun z => (hσ z).symm]
        exact hv _ h1
    have he : WD.tameEig (WD.mk b') γ' = WD.tameEig (WD.mk b) γ := by
      rw [WD.tameEig_mk _ (Ine_le_Weil h' H'.2.1), WD.tameEig_mk _ (Ine_le_Weil h H.2.1),
        ← LinearEquiv.charpoly_conj (LinearEquiv.ofEq _ _ hsp)]
      congr 2
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact (LinearMap.congr_fun (hb ⟨γ, Ine_le_Weil h H.2.1⟩ ⟨γ', Ine_le_Weil h' H'.2.1⟩
        fun z => (hγ z).symm) v).symm
    rw [WD.lab_eq_iff H', he]
    exact ⟨WD.lab_monic _ _ _, WD.map_rootsBar_lab H _⟩
  · rw [WD.lab_of_not H, WD.lab_of_not (mt hiff.mp H)]

end General

theorem main : ∀ (D : D7) (k : Fin 2) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    ∀ γ γ' : GE D.nd, (∀ y, γ' (c y) = c (γ y)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ' x') =
      (Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ x)).map (·⁻¹) := by
  intro D k w w' c hs hc x x' n b b' hx hx' _ hb γ γ' hγ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  subst hx'
  rw [lab_eq D.host.conj.toRingEquiv c hs hc b b' hb (D.ntypes.teichC k) hγ, hx]
  exact LabDual.rootsBar_lab_lpDual _ _ _ _ _ _ _ _ x

end GlobalTheory.WeilDeligne.LabTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRootsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneLabel_transportDual_inverseRoots : ∀ (D : D7) (k : Fin 2) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    ∀ γ γ' : GE D.nd, (∀ y, γ' (c y) = c (γ y)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ' x') =
      (Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ x)).map (·⁻¹) := by
  first | exact @GlobalTheory.WeilDeligne.LabTransport.main | exact GlobalTheory.WeilDeligne.LabTransport.main | (intros; apply GlobalTheory.WeilDeligne.LabTransport.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTransposeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTranspose
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjLocComp

open GlobalTheory.TypeTame

theorem map_invTranspose {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (f : A →+* B) (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.map f (invTranspose n g) = invTranspose n (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  rw [invTranspose_val, ← map_inv]
  rfl

theorem exists_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (hσ : IsLocS S s σ) :
    ∃ (κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : L, κ (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧
      IsLocS S (conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  obtain ⟨i, T, hi, hiL, hTi, hTm, hTe⟩ := hσ
  obtain ⟨i₀, hi₀, hi₀', hi₀L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L s
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i₀ i hi₀ hi hi₀L hiL
  obtain ⟨i', hi', hi'', hi'L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L (conjSP s)
  let j : s.v.adicCompletion (maximalRealSubfield L) ≃+* (conjSP s).w.adicCompletion L := i'
  let κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L := i₀.symm.trans j
  have hκ : Continuous κ := hi'.comp hi₀'
  have hκ' : Continuous κ.symm := hi₀.comp hi''
  let ψ : GL (Fin n) ((conjSP s).w.adicCompletion L) →* GL (Fin n) (s.w.adicCompletion L) :=
    (invTranspose n).comp (Matrix.GeneralLinearGroup.map κ.symm.toRingHom)
  have hψc : Continuous ψ :=
    (continuous_invTranspose n).comp (Continuous.units_map _ (continuous_id.matrix_map hκ'))
  have hψκ : ∀ g, ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g) = invTranspose n g := fun g =>
    congrArg (invTranspose n) (GlobalTheory.LocCompSplit.gl_map_symm_map κ g)
  have hψs : Function.Surjective ψ := fun g =>
    ⟨Matrix.GeneralLinearGroup.map κ.toRingHom (invTranspose n g), by rw [hψκ, invTranspose_invTranspose]⟩
  have hj : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      Matrix.GeneralLinearGroup.map j.toRingHom g =
        Matrix.GeneralLinearGroup.map κ.toRingHom (Matrix.GeneralLinearGroup.map i₀.toRingHom g) := fun g => by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show j (g.val a b) = j (i₀.symm (i₀ (g.val a b)))
    rw [RingEquiv.symm_apply_apply]
  let σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L)) :=
    ⟨σ.V, σ.ρ.comp ψ, fun v => (σ.smooth v).preimage hψc,
      GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective σ.ρ ψ hψs σ.irr⟩
  refine ⟨κ, σ', LinearEquiv.refl ℂ σ.V, hκ, fun x => ?_, ⟨i', T, hi', hi'L, hTi, hTm, fun x hx a => ?_⟩, fun g a => ?_⟩
  · rw [← hi'L, conjSP_i, IsCMField.complexConj_apply_apply, ← hiL]
    show j (i₀.symm (i₀ (s.i x))) = j (s.i x)
    rw [RingEquiv.symm_apply_apply]
  · have h1 : ψ (Matrix.GeneralLinearGroup.map j.toRingHom (invTranspose n (s.loc n x))) =
        Matrix.GeneralLinearGroup.map i₀.toRingHom (s.loc n x) := by
      rw [hj, hψκ, map_invTranspose, invTranspose_invTranspose]
    have h2 := hTe x hx a
    rw [← h1, ← conjSP_loc] at h2
    exact h2
  · show σ.ρ (invTranspose n g) a = σ.ρ (ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g)) a
    rw [hψκ]

theorem exists_isLocS_conjSP : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  intro D n π s σ hσ
  obtain ⟨κ, σ', e, h1, h2, h3, h4⟩ := exists_conj π.S s σ hσ
  exact ⟨κ, σ', e, h1, fun x => by rw [h2, GlobalTheory.SplitPlaceOver.host_conj_eq'], h3, h4⟩

end GlobalTheory.ConjLocComp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  first | exact @GlobalTheory.ConjLocComp.exists_isLocS_conjSP | exact GlobalTheory.ConjLocComp.exists_isLocS_conjSP | (intros; apply GlobalTheory.ConjLocComp.exists_isLocS_conjSP <;> assumption)
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjPlaceDual

theorem conjPl_symm (D : D7) {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hy, GlobalTheory.SplitPlaceOver.host_conj_eq', GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

end GlobalTheory.ConjPlaceDual

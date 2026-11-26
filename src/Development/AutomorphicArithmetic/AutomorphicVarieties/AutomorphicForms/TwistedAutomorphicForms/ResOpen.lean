module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ResOpen
open ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af Formalism.ConjugateSelfDual UpperTheory.V.Base

theorem UpperTheory.V.Af.Tw.resOpen :
    UpperTheory.V.Af.Tw.ResOpen := by
  unfold UpperTheory.V.Af.Tw.ResOpen
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _
  have hre : resG F L Ω = UpperTheory.V.Base.galEmb F L Ω := rfl
  obtain ⟨hemb, hop, hidx⟩ := UpperTheory.V.Base.galEmbTop F L Ω
  rw [hre]
  refine ⟨⟨hemb, ?_⟩, ?_⟩
  · rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hop
  · rw [UpperTheory.V.Base.range_galEmb]
    exact hidx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ConjPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Af.Tw.conjPlace :
    UpperTheory.V.Af.Tw.ConjPlace := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h g hg w w' A hA hne hun
  haveI : Algebra.IsQuadraticExtension F L := ⟨h⟩
  have hc : Nat.card (L ≃ₐ[F] L) = 2 := (IsGalois.card_aut_eq_finrank F L).trans h
  obtain ⟨t, -, hu⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hc
  have h1 : g.restrictNormal L = t := by
    refine hu _ fun h1 => hg ?_
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩
    have := AlgEquiv.restrictNormal_commutes g L y
    rw [h1] at this
    exact this.symm
  have hlift : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (t x) := fun x => by
    rw [← h1]
    exact (AlgEquiv.restrictNormal_commutes g L x).symm
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hun.symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal w'.asIdeal
    (L ≃ₐ[F] L)
  obtain rfl : σ = t := hu σ fun h0 => hne (HeightOneSpectrum.ext (by rw [← hσ, h0, one_smul]))
  have hA' : ∀ x, g.toRingEquiv x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨g • A, fun x => ?_, fun s s' hs => ?_⟩
  · obtain ⟨y, rfl⟩ := MulAction.surjective σ x
    rw [← hσ, Ideal.smul_mem_pointwise_smul_iff, ← hA y, ← val_lt_one hA']
    have h2 : g.toRingEquiv (algebraMap L Ω (y : L)) = algebraMap L Ω ((σ • y : 𝓞 L) : L) := hlift y
    rw [h2]
  · have hss : ∀ x, s' (g x) = g (s x) := fun x => by
      refine (DFunLike.congr_fun hs (g x)).trans ?_
      show g (s (g.symm (g x))) = _
      rw [AlgEquiv.symm_apply_apply]
    have hD : s ∈ Dec (F := L) A → s' ∈ Dec (F := L) (g • A) := fun hs0 => by
      refine mem_Dec.2 ?_
      show resG F L Ω s' • g • A = g • A
      have h3 : resG F L Ω s • A = A := mem_Dec.1 hs0
      rw [hs, ← mul_smul, inv_mul_cancel_right, mul_smul, h3]
    have hle : ∀ y, (g • A).valuation (g y) ≤ 1 → A.valuation y ≤ 1 := fun y hy =>
      (A.valuation_le_one_iff _).2 ((hA' y).1 (((g • A).valuation_le_one_iff _).1 hy))
    refine ⟨fun hI => ⟨hD hI.1, fun x hx => ?_⟩, fun q hF => ⟨hD hF.1, fun x hx => ?_⟩⟩
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_sub]
      exact (val_lt_one hA' _).2 (hI.2 y (hle y hx))
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_pow, ← map_sub]
      exact (val_lt_one hA' _).2 (hF.2 y (hle y hx))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.Descend
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.Tw.descend :
    UpperTheory.V.Af.Tw.Descend := by
  unfold UpperTheory.V.Af.Tw.Descend
  intro F Ω B _ _ _ _ _ _ _ _ art hart ψ hψc hdiag hfin
  have hq := hart.quot
  have hker : art.ker ≤ ψ.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · refine sup_le ?_ ?_
      · rintro _ ⟨k, rfl⟩
        exact hdiag k
      · intro z hz
        unfold infConn at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact hfin _ rfl
    · exact isClosed_singleton.preimage hψc
  let fC : C(Ideles F, Gab F Ω) := ⟨art, hq.continuous⟩
  let gC : C(Ideles F, B) := ⟨ψ, hψc⟩
  have hfact : Function.FactorsThrough gC fC := by
    intro a b hab
    have hab' : a / b ∈ art.ker := by
      rw [MonoidHom.mem_ker, map_div]
      exact div_eq_one.2 hab
    have := hker hab'
    rw [MonoidHom.mem_ker, map_div] at this
    exact div_eq_one.1 this
  have hQ : Topology.IsQuotientMap fC := hq.isQuotientMap
  let κC := hQ.lift gC hfact
  have hκ : ∀ x, κC (art x) = ψ x := fun x => DFunLike.congr_fun (hQ.lift_comp gC hfact) x
  let κ₀ : Gab F Ω →* B := MonoidHom.mk' κC (by
    intro a b
    obtain ⟨x, rfl⟩ := hq.surjective a
    obtain ⟨y, rfl⟩ := hq.surjective b
    rw [← map_mul, hκ, hκ, hκ, map_mul])
  refine ⟨κ₀.comp (GlobalTheory.HeckeGal.toAb F Ω), ?_, ?_⟩
  · exact κC.continuous.comp (by
      first
        | exact QuotientGroup.continuous_mk
        | exact continuous_quot_mk)
  · intro x σ h
    show κC (GlobalTheory.HeckeGal.toAb F Ω σ) = ψ x
    rw [← h, hκ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.VerGroup
theorem UpperTheory.V.Af.Tw.verGroup :
    UpperTheory.V.Af.Tw.VerGroup := by
  unfold UpperTheory.V.Af.Tw.VerGroup
  intro H Γ B _ _ _ _ _ _ _ _ _ r hr hidx κ hκ
  classical
  set R := r.range with hR
  have hinj : Function.Injective r := hr.injective
  have hrs : ∀ s, r s ∈ R := fun s => MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hmem : ∀ a b : Γ, a * b ∈ R ↔ (a ∈ R ↔ b ∈ R) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hidx
  have hnorm : R.Normal := Subgroup.normal_of_index_eq_two hidx
  have hsq : ∀ g, g ∉ R → g * g ∈ R := fun g _ => (hmem g g).mpr Iff.rfl
  obtain ⟨g0, hg0⟩ : ∃ g0 : Γ, g0 ∉ R := by
    by_contra hcon
    push_neg at hcon
    have htop : R = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  let pre : Γ → H := fun γ => if h : γ ∈ R then (MonoidHom.mem_range.mp h).choose else 1
  have hpre : ∀ γ, γ ∈ R → r (pre γ) = γ := fun γ h => by
    dsimp only [pre]
    rw [dite_eq_left h]
    exact (MonoidHom.mem_range.mp h).choose_spec
  let k : Γ → B := fun γ => κ (pre γ)
  have kr : ∀ s, k (r s) = κ s := fun s => by
    show κ (pre (r s)) = κ s
    rw [hinj (hpre _ (hrs s))]
  have kmul : ∀ a, a ∈ R → ∀ b, b ∈ R → k (a * b) = k a * k b := by
    intro a ha b hb
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hb
    rw [← map_mul, kr, kr, kr, map_mul]
  have kinv : ∀ a, a ∈ R → k a⁻¹ = (k a)⁻¹ := by
    intro a ha
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha
    rw [← map_inv, kr, kr, map_inv]
  have k1 : k 1 = 1 := by
    have h := kr 1
    rwa [map_one, map_one] at h
  have L : ∀ g, g ∉ R → ∀ x, x ∈ R → k (g * x * g⁻¹) = k (g0 * x * g0⁻¹) := by
    intro g hg x hx
    have hh : g0⁻¹ * g ∈ R :=
      (hmem _ _).mpr (iff_of_false (fun h => hg0 (by simpa using R.inv_mem h)) hg)
    have hc : g0 * (g0⁻¹ * g) * g0⁻¹ ∈ R := hnorm.conj_mem _ hh g0
    have hx' : g0 * x * g0⁻¹ ∈ R := hnorm.conj_mem _ hx g0
    have e1 : g * x * g⁻¹ = (g0 * (g0⁻¹ * g) * g0⁻¹) * (g0 * x * g0⁻¹) *
        (g0 * (g0⁻¹ * g) * g0⁻¹)⁻¹ := by group
    rw [e1, kmul _ (R.mul_mem hc hx') _ (R.inv_mem hc), kmul _ hc _ hx', kinv _ hc,
      mul_inv_cancel_comm]
  let f : Γ → B := fun γ => if γ ∈ R then k γ * k (g0 * γ * g0⁻¹) else k (γ * γ)
  have fin : ∀ γ, γ ∈ R → f γ = k γ * k (g0 * γ * g0⁻¹) := fun γ h => if_pos h
  have fout : ∀ γ, γ ∉ R → f γ = k (γ * γ) := fun γ h => if_neg h
  have fmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x ∈ R <;> by_cases hy : y ∈ R
    · have hxy := R.mul_mem hx hy
      have cx := hnorm.conj_mem _ hx g0
      have cy := hnorm.conj_mem _ hy g0
      rw [fin _ hxy, fin _ hx, fin _ hy,
        show g0 * (x * y) * g0⁻¹ = (g0 * x * g0⁻¹) * (g0 * y * g0⁻¹) by group,
        kmul _ hx _ hy, kmul _ cx _ cy, mul_mul_mul_comm]
    · have hxy : x * y ∉ R := fun h => hy (((hmem x y).mp h).mp hx)
      have c1 : y * x * y⁻¹ ∈ R := hnorm.conj_mem _ hx y
      rw [fout _ hxy, fin _ hx, fout _ hy,
        show x * y * (x * y) = x * (y * x * y⁻¹) * (y * y) by group,
        kmul _ (R.mul_mem hx c1) _ (hsq y hy), kmul _ hx _ c1, L y hy x hx]
    · have hxy : x * y ∉ R := fun h => hx (((hmem x y).mp h).mpr hy)
      have c1 : x * y * x⁻¹ ∈ R := hnorm.conj_mem _ hy x
      rw [fout _ hxy, fout _ hx, fin _ hy,
        show x * y * (x * y) = (x * y * x⁻¹) * (x * x) * y by group,
        kmul _ (R.mul_mem c1 (hsq x hx)) _ hy, kmul _ c1 _ (hsq x hx), L x hx y hy,
        mul_comm (k (g0 * y * g0⁻¹)), mul_assoc, mul_comm (k (g0 * y * g0⁻¹))]
    · have hxy : x * y ∈ R := (hmem x y).mpr (iff_of_false hx hy)
      have hyx : y * x ∈ R := (hmem y x).mpr (iff_of_false hy hx)
      have hyy := hsq y hy
      have hxx := hsq x hx
      have c1 : x * (y * y) * x⁻¹ ∈ R := hnorm.conj_mem _ hyy x
      rw [fin _ hxy, fout _ hx, fout _ hy, ← L y hy _ hxy,
        show y * (x * y) * y⁻¹ = y * x by group, ← kmul _ hxy _ hyx,
        show x * y * (y * x) = x * (y * y) * x⁻¹ * (x * x) by group,
        kmul _ c1 _ hxx, L x hx _ hyy, ← L y hy _ hyy,
        show y * (y * y) * y⁻¹ = y * y by group, mul_comm]
  let ν : Γ →* B :=
    { toFun := f
      map_one' := by
        show f 1 = 1
        rw [fin _ R.one_mem, mul_one, mul_inv_cancel, k1, mul_one]
      map_mul' := fmul }
  have hσ : Continuous (fun s : H => pre (g0 * r s * g0⁻¹)) := by
    rw [hr.toIsEmbedding.toIsInducing.continuous_iff]
    have hcomp : (r ∘ fun s : H => pre (g0 * r s * g0⁻¹)) = fun s => g0 * r s * g0⁻¹ :=
      funext fun s => hpre _ (hnorm.conj_mem _ (hrs s) g0)
    rw [hcomp]
    exact (continuous_const.mul hr.continuous).mul continuous_const
  have hνr : (ν ∘ r) = fun s => κ s * κ (pre (g0 * r s * g0⁻¹)) := by
    funext s
    show f (r s) = _
    rw [fin _ (hrs s), kr]
  have hcont : Continuous ν := by
    apply continuous_of_continuousAt_one
    have h1 : ContinuousAt (ν ∘ r) 1 := by
      rw [hνr]
      exact (hκ.mul (hκ.comp hσ)).continuousAt
    rw [hr.continuousAt_iff, map_one] at h1
    exact h1
  refine ⟨ν, hcont, fun g hg => ⟨fun s s' hs => ?_, fun t ht => ?_⟩⟩
  · show κ s * κ s' = f (r s)
    rw [fin _ (hrs s), kr, ← L g hg _ (hrs s), ← hs, kr]
  · show κ t = f g
    rw [fout _ hg, ← ht, kr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.FrobInert
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Tw
open scoped Pointwise

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

omit [NumberField L] in
private theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have hb : IsIntegral ℤ (algebraMap L Ω (x : L)) := x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom
  have h : IsIntegral A (algebraMap L Ω (x : L)) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (int_mem A)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩

private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

omit [NumberField K] in
private theorem frob_val {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 ∧ (A.valuation x < 1 → A.valuation (σ x) < 1) := by
  have e : σ x = (σ x - x ^ q) + x ^ q := by ring
  have h1 := hσ.2 x hx
  constructor
  · rw [e]
    exact Valuation.map_add_le _ h1.le (by rw [map_pow]; exact pow_le_one₀ zero_le hx)
  · intro h
    rw [e]
    exact Valuation.map_add_lt _ h1 (by rw [map_pow]; exact pow_lt_one₀ zero_le h hq)

omit [NumberField K] in
private theorem frob_sq {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) :
    IsFrob A (q ^ 2) (σ * σ) := by
  refine ⟨mul_mem hσ.1 hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  have h2 := (frob_val hq hσ h1.le).2 h1
  have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
  have h3 := hσ.2 (x ^ q) hxq
  have e : (σ * σ) x - x ^ q ^ 2 = σ (σ x - x ^ q) + (σ (x ^ q) - (x ^ q) ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub, sq, pow_mul]; ring
  rw [e]
  exact Valuation.map_add_lt _ h2 h3

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Tw.frobInert :
    UpperTheory.V.Af.Tw.FrobInert := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hU hA σ hσ hn
  obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA
  have : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  have : IsGalois F L := inferInstance
  have hq : normV v ≠ 0 := by
    rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hu : w.under (𝓞 F) = v := HeightOneSpectrum.ext hwv.over.symm
  set c : L ≃ₐ[F] L := AlgEquiv.restrictNormalHom L σ with hc
  have hcx : ∀ x : L, algebraMap L Ω (c x) = σ (algebraMap L Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes σ L x
  have hc1 : c ≠ 1 := fun h => hn ⟨{ σ with
    commutes' := fun x => by
      have := hcx x
      rw [h] at this
      exact this.symm }, rfl⟩
  have := w.isMaximal
  have hcw : c • w.asIdeal = w.asIdeal := by
    have hmax : (c • w.asIdeal).IsMaximal := by
      exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ c)
    refine hmax.eq_of_le w.isPrime.ne_top ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hy |> fun h => (⟨c⁻¹ • y, h, smul_inv_smul c y⟩ : ∃ x ∈ w.asIdeal, c • x = y)
    rw [← hw] at hx ⊢
    have e : algebraMap L Ω ((c • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) := hcx x
    rw [e]
    exact (frob_val hq hσ hx.le).2 hx
  have huniq : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver v.asIdeal → P = w.asIdeal := by
    intro P _ _
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[F] L)
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    by_cases hg1 : g = 1
    · rw [← hg, hg1, one_smul]
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
      rw [← hg, hy g hg1, ← hy c hc1, hcw]
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 2 := by
    have := v.isPrime
    letI : Unique (v.asIdeal.primesOver (𝓞 L)) :=
      ⟨⟨⟨w.asIdeal, w.isPrime, hwv⟩⟩, fun P => Subtype.ext (huniq P.1 P.2.1 P.2.2)⟩
    have hs := Ideal.sum_ramification_inertia_eq_card (p := v.asIdeal) (S := 𝓞 L) (G := L ≃ₐ[F] L)
    rw [Fintype.sum_unique, IsGalois.card_aut_eq_finrank, h2] at hs
    have he := hU w hu
    rw [hu, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2 at hs
    rwa [he, one_mul] at hs
  refine ⟨w, fun u => ⟨fun h => HeightOneSpectrum.ext (huniq _ u.isPrime ⟨by rw [← h]; rfl⟩), fun h => h ▸ hu⟩,
    hw, fun t ht => ?_⟩
  have h3 := frob_sq hq hσ
  rw [← ht] at h3
  rw [normV_under (K := F), hu, hf]
  exact ⟨h3.1, h3.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.InfTriv
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.NormCompat

namespace UpperTheory.V.Af.Tw

variable {E : Type} [Field E] [NumberField E]

private theorem mem_infConn_of (w : InfinitePlace E) (x : (w.Completion)ˣ) (S : Set w.Completion)
    (hS : IsPreconnected S) (h0 : 0 ∉ S) (h1 : 1 ∈ S) (hx : (x : w.Completion) ∈ S) : infIdele E w x ∈ infConn E := by
  classical
  let T : Set (w.Completion)ˣ := Units.val ⁻¹' S
  have hT : IsPreconnected T := by
    have himg : Units.val '' T = S := by
      ext a
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ha
        have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
        exact ⟨Units.mk0 a ha0, ha, rfl⟩
    rw [← Units.isEmbedding_val₀.isInducing.isPreconnected_image, himg]
    exact hS
  let φ : (w.Completion)ˣ →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.mulSingle (fun v : InfinitePlace E => v.Completion) w)
  have hφ : Continuous φ := Continuous.units_map _ (continuous_mulSingle w)
  have hsub : φ '' T ⊆ connectedComponent (1 : (InfiniteAdeleRing E)ˣ) :=
    (hT.image _ hφ.continuousOn).subset_connectedComponent ⟨1, h1, map_one φ⟩
  unfold infConn
  refine ⟨φ x, hsub ⟨x, hx, rfl⟩, ?_⟩
  exact Units.ext rfl

private theorem mem_of_sign (N : Subgroup (Ideles E)) (hN : infConn E ≤ N)
    (hs : ∀ w : InfinitePlace E, w.IsReal → infIdele E w (-1) ∈ N) (w : InfinitePlace E) (x : (w.Completion)ˣ) :
    infIdele E w x ∈ N := by
  have key : ∀ (K : Type) [NormedField K] (e : w.Completion ≃ᵢ K), (∀ a, e a = 0 ↔ a = 0) → e 1 = 1 →
      ∀ T : Set K, IsPreconnected T → (0 : K) ∉ T → (1 : K) ∈ T →
      ∀ y : (w.Completion)ˣ, e y ∈ T → infIdele E w y ∈ N := by
    intro K _ e he0 he1 T hT hT0 hT1 y hy
    apply hN
    refine mem_infConn_of w y (e.symm '' T) (hT.image _ e.symm.continuous.continuousOn) ?_ ?_ ?_
    · rintro ⟨b, hb, hb0⟩
      have hb' : b = e 0 := by rw [← hb0, e.apply_symm_apply]
      rw [hb', (he0 0).2 rfl] at hb
      exact hT0 hb
    · refine ⟨1, hT1, ?_⟩
      rw [← he1]
      exact e.symm_apply_apply 1
    · exact ⟨e y, hy, e.symm_apply_apply _⟩
  rcases InfinitePlace.isReal_or_isComplex w with hr | hc
  · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hr
    have he0 : ∀ a, e a = 0 ↔ a = 0 := fun a =>
      map_eq_zero_iff (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)
        (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr).injective
    have he1 : e 1 = 1 := map_one (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)
    have hneg : ∀ a, e (-a) = - e a := fun a =>
      map_neg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr) a
    have hx0 : e x ≠ 0 := fun h => x.ne_zero ((he0 _).1 h)
    rcases lt_or_gt_of_ne hx0 with hlt | hgt
    · have hm : infIdele E w (-x) ∈ N := key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi
        (by simp) (by simp) (-x) (by
          show e (-(x : w.Completion)) ∈ Set.Ioi 0
          rw [hneg]
          exact neg_pos.2 hlt)
      have hx : x = (-1) * (-x) := by simp
      rw [hx, map_mul]
      exact N.mul_mem (hs w hr) hm
    · exact key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi (by simp) (by simp) x hgt
  · let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have he0 : ∀ a, e a = 0 ↔ a = 0 := fun a =>
      map_eq_zero_iff (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding w).injective
    have he1 : e 1 = 1 := map_one (InfinitePlace.Completion.extensionEmbedding w)
    refine key ℂ e he0 he1 {0}ᶜ ?_ (by simp) (by simp) x ?_
    · exact (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 0).isPreconnected
    · exact fun h => x.ne_zero ((he0 _).1 h)

private theorem eq_prod_infIdele (z : Ideles E) (hz : z.val.2 = 1) :
    ∃ y : ∀ w : InfinitePlace E, (w.Completion)ˣ, z = ∏ w, infIdele E w (y w) := by
  classical
  let y : ∀ w : InfinitePlace E, (w.Completion)ˣ := fun w => ⟨z.val.1 w, z.inv.1 w,
    congrFun (congrArg Prod.fst z.val_inv) w, congrFun (congrArg Prod.fst z.inv_val) w⟩
  refine ⟨y, ?_⟩
  ext1
  rw [Units.coe_prod]
  have h1 := map_prod (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
    (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ
  have h2 := map_prod (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
    (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ
  refine Prod.ext ?_ ?_
  · refine Eq.trans ?_ h1.symm
    funext v
    have h3 := map_prod (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) v)
      (fun i => (Pi.mulSingle i (z.val.1 i) : ∀ w : InfinitePlace E, w.Completion)) Finset.univ
    refine Eq.trans ?_ h3.symm
    rw [Finset.prod_eq_single v]
    · show z.val.1 v = Pi.mulSingle v (z.val.1 v) v
      rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      show Pi.mulSingle b (z.val.1 b) v = 1
      exact Pi.mulSingle_eq_of_ne hb.symm _
    · intro h
      exact absurd (Finset.mem_univ v) h
  · refine Eq.trans ?_ h2.symm
    rw [hz]
    symm
    apply Finset.prod_eq_one
    intro i _
    rfl

end UpperTheory.V.Af.Tw

theorem UpperTheory.V.Af.Tw.infTriv :
    UpperTheory.V.Af.Tw.InfTriv := by
  intro F Ω B _ _ _ _ _ _ _ _ _ art ha ν hν hc z σ hz hσ
  let N : Subgroup (Ideles F) := ((liftAb ν hν).comp art).ker
  have hN : infConn F ≤ N := fun x hx => by
    have h : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hx)
    show liftAb ν hν (art x) = 1
    rw [show art x = 1 from h, map_one]
  have hs : ∀ w : InfinitePlace F, w.IsReal → infIdele F w (-1) ∈ N := fun w hw => by
    obtain ⟨j, c, hj, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w hw
    show liftAb ν hν (art _) = 1
    rw [GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hj, liftAb_toAb]
    exact hc c ⟨j, hj⟩
  obtain ⟨y, hy⟩ := eq_prod_infIdele z hz
  have hm : z ∈ N := hy ▸ prod_mem fun w _ => mem_of_sign N hN hs w (y w)
  have hm' : liftAb ν hν (art z) = 1 := hm
  rwa [hσ, liftAb_toAb] at hm'
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.BoxUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LinkOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UlZero
noncomputable def UpperTheory.Reformulated.B.Rb1.Zc :
    {D N : Type} → [inst : Group D] → [TopologicalSpace D] → [inst_2 : AddCommGroup N] → Representation ℤ D N → Set (D → N) :=
    fun {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) ↦
      {z : D → N | IsLocallyConstant z ∧ ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t)}

theorem UpperTheory.Reformulated.B.Rb1.ul_zero :
    ∀ {D N : Type} [inst : Group D] [inst_1 : TopologicalSpace D] [inst_2 : IsTopologicalGroup D] [inst_3 : AddCommGroup N]
      (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
        ∀ z ∈ UpperTheory.Reformulated.B.Rb1.Zc ρ, (∀ s ∈ I, z s = (0 : N)) → z φ = (0 : N) → ∀ (s : D), z s = (0 : N) := by
  intro D N _ _ _ _ ρ I φ hcl z hz hI hφ s
  have hlc : IsLocallyConstant z := hz.1
  have hco : ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t) := hz.2
  have h1 : z 1 = 0 := by
    have h := hco 1 1
    rw [mul_one, map_one] at h
    simpa using h
  let K : Subgroup D :=
    { carrier := z ⁻¹' {0}
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = 0 := ha
        have hb' : z b = 0 := hb
        show z (a * b) = 0
        rw [hco, ha', hb', map_zero, add_zero]
      one_mem' := h1
      inv_mem' := by
        intro a ha
        have ha' : z a = 0 := ha
        show z a⁻¹ = 0
        have h := hco a⁻¹ a
        rw [inv_mul_cancel, h1, ha', map_zero, add_zero] at h
        exact h.symm }
  have hK : IsClosed (K : Set D) := hlc.isClosed_fiber 0
  have hle : I ⊔ Subgroup.zpowers φ ≤ K :=
    sup_le hI (by
      rw [Subgroup.zpowers_le]
      exact hφ)
  have htop : (⊤ : Subgroup D) ≤ K := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hK
  exact htop (Subgroup.mem_top s)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LeOf2
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LcOrbit
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

private theorem cardZ {k D M : Type} [CommRing k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (σ : Representation k D M) (hσ : ContAction σ)
    [Finite (H1 σ)] : Finite (Z1 σ) ∧ Nat.card (Z1 σ) * Nat.card (H0 σ) = Nat.card (H1 σ) * Nat.card M := by
  set B := Submodule.comap (Z1 σ).subtype (B1 σ) with hB
  have hBZ : B1 σ ≤ Z1 σ := by
    rintro f ⟨m, rfl⟩
    have hfun : (d0 σ m : D → M) = fun g => σ g m - m := funext fun g => amitsur_d0_apply σ m g
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (hσ.comp (Continuous.prodMk continuous_id continuous_const)).sub continuous_const
    · intro g h
      rw [amitsur_d0_apply, amitsur_d0_apply, amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 σ) = H0 σ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp [amitsur_d0_apply, sub_eq_zero]
  have hM : Nat.card M = Nat.card (H0 σ) * Nat.card (B1 σ) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 σ)),
      Nat.card_congr (d0 σ).quotKerEquivRange.toEquiv, hker]
    rfl
  have hZ : Nat.card (Z1 σ) = Nat.card B * Nat.card (H1 σ) := Submodule.card_eq_card_quotient_mul_card B
  have hBc : Nat.card B = Nat.card (B1 σ) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hBZ).toEquiv
  haveI : Finite (B1 σ) := by
    show Finite (LinearMap.range (d0 σ))
    exact Finite.of_surjective (d0 σ).rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hB1pos : 0 < Nat.card (B1 σ) := Nat.card_pos
  have hH1pos : 0 < Nat.card (H1 σ) := Nat.card_pos
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ, hBc]
    positivity
  · rw [hZ, hBc, hM]
    ring

private def zRep (n : ℕ) {D M : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M]
    (ρ : Representation ℤ D M) : Representation (ZMod n) D M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

private theorem cardInv {n : ℕ} {D M : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M] (χ : D →* (ZMod n)ˣ)
    (σ : Representation (ZMod n) D M) :
    Nat.card (H0 ((twDual χ σ).comp (MonoidHom.id D))) =
      Nat.card {f : M →+ ZMod n // ∀ s x, f (σ s x) = χ s * f x} := by
  apply Nat.card_congr
  exact
    { toFun := fun φ => ⟨(φ.1 : M →ₗ[ZMod n] ZMod n).toAddMonoidHom, by
        intro s x
        have h1 := (Representation.mem_invariants _ _).mp φ.2 s
        have h2 := congrArg (fun ψ : TDual (ZMod n) M => ψ (σ s x)) h1
        have hinv : σ s⁻¹ (σ s x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, twDual_apply, hinv] at h2
        exact h2.symm⟩
      invFun := fun f => ⟨f.1.toZModLinearMap n, by
        refine (Representation.mem_invariants _ _).mpr ?_
        intro g
        apply LinearMap.ext
        intro m
        have h1 := f.2 g (σ g⁻¹ m)
        have hinv : σ g (σ g⁻¹ m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [hinv] at h1
        exact h1.symm⟩
      left_inv := fun φ => Subtype.ext (LinearMap.ext fun m => rfl)
      right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun m => rfl) }

private theorem lc_orbit {D M : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M]
    (ρ : Representation ℤ D M) (h : IsOpen (ρ.ker : Set D)) (m : M) : IsLocallyConstant fun g => ρ g m := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun y => g⁻¹ * y) ⁻¹' (ρ.ker : Set D), h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro x hx
    have hk : ρ (g⁻¹ * x) = 1 := MonoidHom.mem_ker.mp hx
    have hx' : x = g * (g⁻¹ * x) := by group
    rw [hx', map_mul, Module.End.mul_apply, hk, Module.End.one_apply]

theorem UpperTheory.V.Z.J.leOf :
    ReciprocityTheory.Gal.LocalFiniteness → ReciprocityTheory.Gal.LocalTateDuality → ReciprocityTheory.Gal.LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), IsPlaceOver A v → ((l : ℕ) : NumberField.RingOfIntegers F) ∈ v.asIdeal → LE l (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v) := by
  intro hFin hTD hEC l _ F Ω _ _ _ _ _ A v hAv hlv
  unfold UpperTheory.V.Z.J.LE
  intro k hk N _ _ ρ hx hker
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod (l ^ k)) N := AddCommGroup.zmodModule hx
  letI tN : TopologicalSpace N := ⊥
  haveI : DiscreteTopology N := ⟨rfl⟩
  let σ : Representation (ZMod (l ^ k)) (Dec (F := F) A) N := zRep (l ^ k) ρ
  have hcont : ContAction σ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_exists_open]
    rintro ⟨g, x⟩
    obtain ⟨U, hU, hgU, hUc⟩ := (IsLocallyConstant.iff_exists_open _).mp (lc_orbit ρ hker x) g
    refine ⟨U ×ˢ {x}, hU.prod (isOpen_discrete _), ⟨hgU, rfl⟩, ?_⟩
    rintro ⟨g', x'⟩ ⟨hg', hx'⟩
    simp only [Set.mem_singleton_iff] at hx'
    subst hx'
    exact hUc g' hg'
  obtain ⟨hH0f, hH1f, hH2f, -⟩ := hFin F Ω l k N A σ v hk hAv hcont
  haveI := hH0f
  haveI := hH1f
  haveI := hH2f
  have hec := (hEC F Ω l k N A σ v hk hAv hcont).1 hlv
  obtain ⟨⟨e2⟩, -, -, -, hcup⟩ := hTD F Ω l k N A σ v hk hAv hcont
  obtain ⟨hZf, hZc⟩ := cardZ σ hcont
  haveI := hZf
  haveI hDf : Finite (N →ₗ[ZMod (l ^ k)] ZMod (l ^ k)) :=
    Finite.of_injective _ (LinearMap.coe_injective (R := ZMod (l ^ k)) (M := N) (M₃ := ZMod (l ^ k)))
  haveI hTf : Finite (TDual (ZMod (l ^ k)) N) := hDf
  have e1 := Nat.card_congr ((Equiv.ofBijective _ hcup).trans (by exact (LinearEquiv.congrRight e2).toEquiv))
  have e3 := e1.trans (by exact (Th.dualZ (l ^ k) _).1)
  have h2 := e3.trans (by exact cardInv _ σ)
  have h3 : Nat.card ↑(HomMu l k ((cycZ F Ω l).comp (Dec (F := F) A).subtype) ρ) = Nat.card (H2 σ) :=
    h2.symm
  have hZ : Zc ρ = ((Z1 σ : Submodule _ _) : Set ((Dec (F := F) A) → N)) := by
    ext z
    show (IsLocallyConstant z ∧ _) ↔ (Continuous z ∧ _)
    rw [IsLocallyConstant.iff_continuous]
    rfl
  have key : ∀ {a b c n e d : ℕ}, a * b = c * n → c = b * e * n ^ d → 0 < b → a = n ^ (1 + d) * e := by
    intro a b c n e d h1 h2 hb
    apply Nat.eq_of_mul_eq_mul_right hb
    rw [h1, h2]
    ring
  refine ⟨?_, ?_⟩
  · rw [hZ]
    exact Set.toFinite _
  · rw [hZ, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, h3]
    exact key hZc hec (by exact Nat.card_pos)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LeTrans
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.leTrans :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (e : D ≃ₜ* D') (ε : D' →* ℤ_[l]ˣ) (d : ℕ), LE l D' ε d → LE l D (ε.comp (e : D →* D')) d := by
  intro l _ D D' _ _ _ _ e ε d h k hk N _ _ ρ hN hker
  let ρ' : Representation ℤ D' N := ρ.comp (e.symm : D' →* D)
  have hρ' : ∀ s : D', ρ' s = ρ (e.symm s) := fun s => rfl
  have hker' : IsOpen (↑(MonoidHom.ker ρ') : Set D') := by
    have hset : (↑(MonoidHom.ker ρ') : Set D') = e.symm ⁻¹' (↑(MonoidHom.ker ρ) : Set D) := by
      ext s
      simp [hρ']
    rw [hset]
    exact hker.preimage (map_continuous e.symm)
  obtain ⟨hfin, hcard⟩ := h k hk N ρ' hN hker'
  have himg : Zc ρ = (fun z : D' → N => z ∘ e) '' Zc ρ' := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨z ∘ e.symm, ⟨hz1.comp_continuous (map_continuous e.symm), ?_⟩, ?_⟩
      · intro s t
        simp only [Function.comp_apply, map_mul, hρ']
        exact hz2 _ _
      · funext s
        simp
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      refine ⟨hw1.comp_continuous (map_continuous e), ?_⟩
      intro s t
      simp only [Function.comp_apply, map_mul]
      rw [hw2, hρ']
      simp
  have hinj : Function.Injective (fun z : D' → N => z ∘ e) := by
    intro z₁ z₂ hz
    funext s
    have := congrFun hz (e.symm s)
    simpa using this
  have hmu : HomMu l k (ε.comp (e : D →* D')) ρ = HomMu l k ε ρ' := by
    ext f
    simp only [HomMu, Set.mem_setOf_eq, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro hf s x
      rw [hρ']
      have := hf (e.symm s) x
      simpa using this
    · intro hf s x
      have := hf (e s) x
      rw [hρ'] at this
      simpa using this
  rw [himg, hmu]
  exact ⟨hfin.image _, by rw [Set.ncard_image_of_injective _ hinj]; exact hcard⟩
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

private noncomputable def isoOf {D D' : Type} [Group D] [TopologicalSpace D] [CompactSpace D] [Group D'] [TopologicalSpace D']
    [T2Space D'] (f : D →* D') (hc : Continuous f) (hb : Function.Bijective f) : D ≃ₜ* D' :=
  { MulEquiv.ofBijective f hb with
    continuous_toFun := hc
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := (MulEquiv.ofBijective f hb).toEquiv) hc).symm.continuous }

theorem UpperTheory.V.Z.J.leOf2 :
    GC.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Field κ] (Φ : Frame l κ) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] S K π ι A pl e c, GC.FLink (F := F) (Ω := Ω) l Φ S K π ι A pl e c → LocE Φ := by
  intro hP l _ κ _ Φ F Ω _ _ _ _ _ S K π ι A pl e c hL v
  have hrange := hL.loc.range v
  let f : Φ.Gv v →* Dec (A v) :=
    (ι v).codRestrict (Dec (A v)) (fun s => hrange ▸ (MonoidHom.mem_range.2 ⟨s, rfl⟩))
  have hfc : Continuous f := (hL.loc.cont v).subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hL.loc.ι_inj v (congrArg Subtype.val hab)
    · rintro ⟨g, hg⟩
      rw [← hrange] at hg
      obtain ⟨s, rfl⟩ := hg
      exact ⟨s, rfl⟩
  have hl := (hL.loc.mem (pl v)).1 ⟨v, rfl⟩
  have h0 := leOf hP.lf hP.lt hP.le l F Ω (A v) (pl v) (hL.loc.isOver v) hl
  have h1 := leTrans l (Φ.Gv v) (Dec (A v)) (isoOf f hfc hfb) _ _ h0
  rw [hL.dv v]
  convert h1 using 2
  ext s
  simp [hL.loc_eq, hL.eps]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.FiniteCocyclesOfFiniteH1
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnrLow
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

section SlopeTestRemainingChoices

variable {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]

private theorem ul_top (I : Subgroup D) (φ : D) (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (S : Subgroup D) (hS : IsClosed (S : Set D)) (hI : I ≤ S) (hφ : φ ∈ S) (s : D) : s ∈ S := by
  have := Subgroup.topologicalClosure_minimal _ (sup_le hI ((Subgroup.zpowers_le).2 hφ)) hS
  rw [h] at this
  exact this (Subgroup.mem_top s)

private theorem ul_lc (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) : IsLocallyConstant ρ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' ρ.ker, ho.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) = 1 := hx
  calc ρ x = ρ (g * (g⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = ρ g := by rw [map_mul, h, mul_one]

omit [TopologicalSpace D] [IsTopologicalGroup D] in
private theorem ul_mul (ρ : Representation ℤ D N) (s t : D) (y : N) : ρ (s * t) y = ρ s (ρ t y) := by
  rw [map_mul]; rfl

private theorem ul_zero (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) (z : D → N) (hz : z ∈ Zc ρ) (hI : ∀ s ∈ I, z s = 0)
    (hφ : z φ = 0) (s : D) : z s = 0 :=
  _root_.UpperTheory.Reformulated.B.Rb1.ul_zero ρ I φ h z hz hI hφ s

private theorem ul_ex [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [hn : I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (x : N) (hx : ∀ s ∈ I, ρ s x = x) : ∃ z ∈ Zc ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  have inv1 : ∀ s y, ρ s (ρ s⁻¹ y) = y := fun s y => by rw [← ul_mul, mul_inv_cancel, map_one]; rfl
  have inv2 : ∀ s y, ρ s⁻¹ (ρ s y) = y := fun s y => by rw [← ul_mul, inv_mul_cancel, map_one]; rfl
  have stab : ∀ s y, (∀ j ∈ I, ρ j y = y) → ∀ j ∈ I, ρ j (ρ s y) = ρ s y := fun s y hy j hj => by
    have h1 := hy _ (hn.conj_mem j hj s⁻¹)
    rw [inv_inv, ul_mul, ul_mul] at h1
    have h2 := congrArg (ρ s) h1
    rwa [inv1] at h2
  let T : Equiv.Perm N :=
    { toFun := fun y => x + ρ φ y
      invFun := fun y => ρ φ⁻¹ (y - x)
      left_inv := fun y => by simp only [add_sub_cancel_left, inv2]
      right_inv := fun y => by simp only [inv1, add_sub_cancel] }
  have hg : ∀ u : Subgroup.zpowers T, u ∈ Subgroup.zpowers (⟨T, Subgroup.mem_zpowers T⟩ : Subgroup.zpowers T) := by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, rfl⟩
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (Nat.card (Subgroup.zpowers T)) Nat.card_pos
  obtain ⟨τ, t1, t2, t3⟩ : ∃ τ : D →* Equiv.Perm N, IsLocallyConstant τ ∧ (∀ s ∈ I, τ s = 1) ∧ τ φ = T := by
    let e := (Subgroup.zpowers T).subtype.comp (zmodMulEquivOfGenerator hg rfl).toMonoidHom
    refine ⟨e.comp d, hd1.comp e, fun s hs => ?_, ?_⟩
    · rw [MonoidHom.comp_apply, hd2 s hs, map_one]
    · rw [MonoidHom.comp_apply, hd3]
      exact congrArg Subtype.val (zmodMulEquivOfGenerator_apply_ofAdd_one hg rfl)
  let S : Subgroup D :=
    { carrier := {s | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → τ s y = a + ρ s y}
      one_mem' := ⟨0, fun j _ => map_zero _, fun y _ => by simp⟩
      mul_mem' := fun {s t} ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ =>
        ⟨a + ρ s b, fun j hj => by rw [map_add (f := _), ha j hj, stab s b hb j hj], fun y hy => by
          rw [map_mul, Equiv.Perm.mul_apply, hb' y hy,
            ha' _ (fun j hj => by rw [map_add (f := _), hb j hj, stab t y hy j hj]), map_add (f := _), ul_mul, add_assoc]⟩
      inv_mem' := fun {s} ⟨a, ha, ha'⟩ =>
        ⟨-ρ s⁻¹ a, fun j hj => by rw [map_neg, stab _ a ha j hj], fun y hy => by
          rw [map_inv, Equiv.Perm.inv_eq_iff_eq,
            ha' _ (fun j hj => by rw [map_add (f := _), map_neg, stab _ a ha j hj, stab _ y hy j hj]),
            map_add, map_neg, inv1, inv1, add_neg_cancel_left]⟩ }
  have hS : ∀ s, s ∈ S := by
    refine ul_top I φ h S ?_ (fun s hs => ⟨0, fun j _ => map_zero _, fun y hy => ?_⟩) ⟨x, hx, fun y _ => ?_⟩
    · exact isOpen_compl_iff.1 (t1.prodMk (ul_lc ρ ho)
        {p | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → p.1 y = a + p.2 y}ᶜ)
    · rw [t2 s hs, hy s hs, zero_add]; rfl
    · rw [t3]; rfl
  refine ⟨fun s => τ s 0, ⟨t1.comp fun p => p 0, fun s t => ?_⟩, fun s hs => ?_, ?_⟩
  · obtain ⟨a, -, ha'⟩ := hS s
    obtain ⟨b, hb, hb'⟩ := hS t
    have h0 : ∀ j ∈ I, ρ j 0 = 0 := fun j _ => map_zero _
    show τ (s * t) 0 = τ s 0 + ρ s (τ t 0)
    rw [map_mul, Equiv.Perm.mul_apply, hb' 0 h0, map_zero, add_zero, ha' b hb, ha' 0 h0, map_zero, add_zero]
  · show τ s 0 = 0
    rw [t2 s hs]; rfl
  · show τ φ 0 = x
    rw [t3]
    show x + ρ φ 0 = x
    rw [map_zero, add_zero]

private theorem ul_abs [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    ∃ Z : AddSubgroup (D → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧
      (∀ z ∈ Z, ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  have hsub : ∀ {a b : D → N}, a ∈ Zc ρ → b ∈ Zc ρ → a - b ∈ Zc ρ := fun {a b} ha hb =>
    ⟨ha.1.sub hb.1, fun s t => by
      simp only [Pi.sub_apply, ha.2 s t, hb.2 s t, map_sub]; abel⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  let Z : AddSubgroup (D → N) := AddSubgroup.ofSub {z | z ∈ Zc ρ ∧ ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y}
    ⟨0, h0, 0, fun s _ => by simp⟩
    (fun a ⟨ha, Y, hY⟩ b ⟨hb, Y', hY'⟩ => by
      rw [← sub_eq_add_neg]
      refine ⟨hsub ha hb, Y - Y', fun s hs => ?_⟩
      rw [Pi.sub_apply, hY s hs, hY' s hs, map_sub]; abel)
  have hcob : ∀ Y : N, (fun s => ρ s Y - Y) ∈ Z := fun Y =>
    ⟨⟨(ul_lc ρ ho).comp fun p => p Y - Y, fun s t => by
      simp only [ul_mul, map_sub]; abel⟩, Y, fun _ _ => rfl⟩
  have hfin : Finite Z := by
    refine Finite.of_injective (fun z : Z => (z.2.2.choose, z.1 φ)) fun a b hab => Subtype.ext ?_
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 hab
    refine sub_eq_zero.1 (funext (ul_zero ρ I φ h _ (hsub a.2.1 b.2.1) (fun s hs => ?_) (sub_eq_zero.2 e2)))
    have e1' : a.2.2.choose = b.2.2.choose := e1
    rw [Pi.sub_apply, a.2.2.choose_spec s hs, b.2.2.choose_spec s hs, e1', sub_self]
  refine ⟨Z, hfin, fun z hz => hz.1, hcob, fun z hz => hz.2, ?_⟩
  let r : Z →+ (I → N) := AddMonoidHom.mk' (fun z s => z.1 s.1) fun _ _ => rfl
  let π : N →+ (I → N) := AddMonoidHom.mk' (fun Y s => ρ s.1 Y - Y) fun a b => funext fun s => by
    simp only [map_add (f := _), Pi.add_apply]; abel
  have hr : r.range = π.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨Y, hY⟩ := z.2.2
      exact ⟨Y, funext fun s => (hY s.1 s.2).symm⟩
    · rintro _ ⟨Y, rfl⟩
      exact ⟨⟨_, hcob Y⟩, rfl⟩
  have hk : Nat.card π.ker ≤ Nat.card r.ker := by
    have hex : ∀ x : π.ker, ∃ z : r.ker, z.1.1 φ = x.1 := fun x => by
      obtain ⟨z, z1, z2, z3⟩ := ul_ex ρ ho I φ h hd x.1 fun s hs => sub_eq_zero.1 (congrFun x.2 ⟨s, hs⟩)
      exact ⟨⟨⟨z, z1, 0, fun s hs => by rw [z2 s hs]; simp⟩, funext fun s => z2 s.1 s.2⟩, z3⟩
    choose f hf using hex
    exact Nat.card_le_card_of_injective f fun a b hab => Subtype.ext (by rw [← hf a, ← hf b, hab])
  rw [← π.ker.card_mul_index, ← r.ker.card_mul_index, AddSubgroup.index_ker, AddSubgroup.index_ker, hr]
  exact Nat.mul_le_mul_right _ hk

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.J.unrLow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), IsPlaceOver A v → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ (Dec (F := F) A) N), IsOpen (ρ.ker : Set (Dec (F := F) A)) → ∃ Z : AddSubgroup (Dec (F := F) A → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧ (∀ z ∈ Z, ∃ Y : N, ∀ s : Dec (F := F) A, s.1 ∈ Ine (F := F) A → z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  intro F Ω _ _ _ _ _ A v hA N _ _ ρ ho
  obtain ⟨φ, -, h1, h2⟩ := GC.decZhat F Ω v A hA
  haveI : ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal := ⟨fun n hn g => conj_mem_Ine g.2 hn⟩
  exact ul_abs ρ ho _ φ h1 h2
end

noncomputable section Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Z.J

section Count

variable {k G M : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k G M)

private def cls (L : Submodule k (H1 ρ)) : Set (G → M) :=
  {z | ∃ hz : z ∈ Z1 ρ, (Submodule.Quotient.mk ⟨z, hz⟩ : H1 ρ) ∈ L}

private theorem card_cls (h : ContAction ρ) (L : Submodule k (H1 ρ)) :
    (cls ρ L).ncard = Nat.card (B1 ρ) * Nat.card L := by
  have e1 : cls ρ L = Subtype.val '' ((fun z : Z1 ρ => (Submodule.Quotient.mk z : H1 ρ)) ⁻¹' (L : Set (H1 ρ))) := by
    ext z
    constructor
    · rintro ⟨hz, h⟩; exact ⟨⟨z, hz⟩, h, rfl⟩
    · rintro ⟨z, h, rfl⟩; exact ⟨z.2, h⟩
  have e2 := (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet
    ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup (L : Set (H1 ρ)))).trans (Nat.card_prod _ _)
  have e3 : Nat.card ((B1 ρ).comap (Z1 ρ).subtype) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles ρ h)).toEquiv
  rw [e1, Set.ncard_image_of_injective _ Subtype.val_injective, ← e3]
  exact e2

omit [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] in
private theorem card_coboundaries_mul_card_h0 : Nat.card (B1 ρ) * Nat.card (H0 ρ) = Nat.card M := by
  have e : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, funext_iff]
    exact forall_congr' fun g => sub_eq_zero
  rw [← e, Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ)), mul_comm]
  congr 1
  exact (Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv).symm

private theorem finite_z1_of_finite_h1 [Finite M] [Finite (H1 ρ)] : Finite (Z1 ρ) := by
  have : Finite (B1 ρ) := Finite.of_surjective _ (d0 ρ).surjective_rangeRestrict
  have : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  exact Finite.of_equiv (H1 ρ × (B1 ρ).comap (Z1 ρ).subtype)
    (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup)).symm

private theorem zc_iff (τ : Representation ℤ G M) (e : ∀ g m, ρ g m = τ g m) (z : G → M) : z ∈ Zc τ ↔ z ∈ Z1 ρ :=
  and_congr (IsLocallyConstant.iff_continuous z) (by simp only [← e])

end Count

private theorem ex_cls {n : ℕ} {G M : Type} [Group G] [TopologicalSpace G] [AddCommGroup M] [Module (ZMod n) M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod n) G M) (N : AddSubgroup (G → M))
    (h1 : ∀ z ∈ B1 ρ, z ∈ N) (h2 : ∀ z ∈ N, z ∈ Z1 ρ) :
    ∃ L : Submodule (ZMod n) (H1 ρ), cls ρ L = N := by
  refine ⟨((AddSubgroup.toZModSubmodule n N).comap (Z1 ρ).subtype).map (Submodule.mkQ _), ?_⟩
  ext z
  constructor
  · rintro ⟨hz, y, hy, e⟩
    have e' : y.1 - z ∈ B1 ρ := (Submodule.Quotient.eq ((B1 ρ).comap (Z1 ρ).subtype)).1 e
    have := N.sub_mem hy (h1 _ e')
    simpa using this
  · intro hz
    exact ⟨h2 z hz, ⟨z, _⟩, hz, rfl⟩

private theorem core {n : ℕ} {Γ M W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module (ZMod n) M]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M] [Fintype W] {D : W → Type} [∀ w, Group (D w)]
    [∀ w, TopologicalSpace (D w)] (ρ : Representation (ZMod n) Γ M) (τ : Representation ℤ Γ M) (e : ∀ g m, ρ g m = τ g m)
    (ι : ∀ w, D w →* Γ) (hι : ∀ w, Continuous (ι w)) (a b : ℕ) (h : ContAction ρ) [Finite (H1 ρ)]
    (gw : ∀ L : LocCond ρ ι, Nat.card (H0 ρ) * ∏ w, Nat.card (L w) ≤
      Nat.card (Sel ρ ι hι L) * b * (∏ w, Nat.card (H0 (ρ.comp (ι w)))) * a)
    (Z : ∀ w, AddSubgroup (D w → M)) (h1 : ∀ w, (Z w : Set (D w → M)) ⊆ Zc (τ.comp (ι w)))
    (h2 : ∀ w (Y : M), (fun s => τ (ι w s) Y - Y) ∈ Z w) :
    (Zc τ).Finite ∧ Nat.card M * ∏ w, Nat.card (Z w) ≤
      {z | z ∈ Zc τ ∧ ∀ w, (fun s => z (ι w s)) ∈ Z w}.ncard * b * a * Nat.card M ^ Fintype.card W := by
  have f := finite_z1_of_finite_h1 ρ
  refine ⟨(Set.toFinite (Z1 ρ : Set (Γ → M))).subset fun z hz => (zc_iff ρ τ e z).1 hz, ?_⟩
  choose L hL using fun w => ex_cls (ρ.comp (ι w)) (Z w)
    (fun z hz => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
      have : z = fun s => τ (ι w s) m - m := funext fun s => (hm s).trans (by rw [← e]; rfl)
      exact this ▸ h2 w m)
    (fun z hz => (zc_iff _ (τ.comp (ι w)) (fun g m => e _ m) z).1 (h1 w hz))
  have e1 : {z | z ∈ Zc τ ∧ ∀ w, (fun s => z (ι w s)) ∈ Z w} = cls ρ (Sel ρ ι hι L) := by
    ext z
    constructor
    · rintro ⟨hz, hw⟩
      refine ⟨(zc_iff ρ τ e z).1 hz, (mem_Sel _ _ _ _ _).2 fun w => ?_⟩
      have : z ∘ ι w ∈ cls (ρ.comp (ι w)) (L w) := by rw [hL]; exact hw w
      exact this.2
    · rintro ⟨hz, hw⟩
      refine ⟨(zc_iff ρ τ e z).2 hz, fun w => ?_⟩
      have : z ∘ ι w ∈ cls (ρ.comp (ι w)) (L w) := ⟨(restrictCocycles1 ρ (ι w) (hι w) ⟨z, hz⟩).2, (mem_Sel _ _ _ _ _).1 hw w⟩
      rwa [hL] at this
  have e4 : ∀ w, Nat.card (Z w) = Nat.card (B1 (ρ.comp (ι w))) * Nat.card (L w) := fun w => by
    rw [← card_cls _ (h.comp' (hι w)), hL]; rfl
  have e5 : Nat.card M ^ Fintype.card W =
      (∏ w, Nat.card (B1 (ρ.comp (ι w)))) * ∏ w, Nat.card (H0 (ρ.comp (ι w))) := by
    rw [← Finset.prod_mul_distrib]
    simp only [card_coboundaries_mul_card_h0, Finset.prod_const, Finset.card_univ]
  rw [e1, card_cls _ h, e5]
  simp only [e4, Finset.prod_mul_distrib]
  have e6 := Nat.mul_le_mul_left (Nat.card (B1 ρ) * ∏ w, Nat.card (B1 (ρ.comp (ι w)))) (gw L)
  rw [← card_coboundaries_mul_card_h0 ρ]
  convert e6 using 1 <;> ring

private theorem desc {Γ' Γ N : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [Group Γ]
    [TopologicalSpace Γ] [T2Space Γ] [AddCommGroup N] (p : Γ' →* Γ) (hp : Continuous p) (hs : Function.Surjective p)
    (ρ : Representation ℤ Γ N) (T : Set Γ') (hT : p.ker = (Subgroup.normalClosure T).topologicalClosure)
    (z : Γ' → N) (hz : z ∈ Zc (ρ.comp p)) (h0 : ∀ g ∈ T, z g = 0) : ∃ y ∈ Zc ρ, ∀ g, y (p g) = z g := by
  have hm : ∀ s t, z (s * t) = z s + ρ (p s) (z t) := hz.2
  have h1 : z 1 = 0 := by simpa using hm 1 1
  let H : Subgroup Γ' :=
    { carrier := {g | p g = 1 ∧ z g = 0}
      one_mem' := ⟨map_one p, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, mul_one], by rw [hm, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1, inv_one], by
        have := hm a⁻¹ a
        rw [inv_mul_cancel, h1, ha.2, map_zero, add_zero] at this
        exact this.symm⟩ }
  haveI : H.Normal := ⟨fun a ha g => ⟨by simp [ha.1], by
    rw [hm, hm, ha.2, map_zero, add_zero, map_mul, ha.1, mul_one, ← hm, mul_inv_cancel, h1]⟩⟩
  have hH : p.ker ≤ H := by
    have hT' : T ⊆ p.ker := by
      rw [hT]
      exact Subgroup.subset_normalClosure.trans (Subgroup.le_topologicalClosure _)
    rw [hT]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => ⟨hT' hg, h0 g hg⟩)
      ((isClosed_singleton.preimage hp).inter (hz.1.isClosed_fiber 0))
  have hy : ∀ g, z (Function.surjInv hs (p g)) = z g := fun g => by
    have : z (g⁻¹ * Function.surjInv hs (p g)) = 0 :=
      (hH (by rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel])).2
    conv_lhs => rw [← mul_inv_cancel_left g (Function.surjInv hs (p g)), hm, this, map_zero, add_zero]
  refine ⟨fun g => z (Function.surjInv hs g), ⟨fun s => ?_, fun s t => ?_⟩, hy⟩
  · rw [← (hp.isClosedMap.isQuotientMap hp hs).isOpen_preimage]
    convert hz.1 s using 1
    ext g
    simp only [Set.mem_preimage, hy]
  · obtain ⟨s, rfl⟩ := hs s
    obtain ⟨t, rfl⟩ := hs t
    beta_reduce
    rw [← map_mul, hy, hy, hy, hm]

private theorem tran {D G N : Type} [Group D] [TopologicalSpace D] [CompactSpace D] [Group G] [TopologicalSpace G] [T2Space G]
    [AddCommGroup N] (ι : D →* G) (hc : Continuous ι) (hi : Function.Injective ι) (H : Subgroup G) (hH : ι.range = H)
    (τ : Representation ℤ G N) (Z : AddSubgroup (D → N)) (h1 : (Z : Set (D → N)) ⊆ Zc (τ.comp ι))
    (h2 : ∀ Y : N, (fun s => τ (ι s) Y - Y) ∈ Z) :
    ∃ Z' : AddSubgroup (H → N), (Z' : Set (H → N)) ⊆ Zc (τ.comp H.subtype) ∧ (∀ Y : N, (fun s : H => τ s.1 Y - Y) ∈ Z') ∧
      Nat.card Z = Nat.card Z' ∧ ∀ z : G → N, (fun s : H => z s.1) ∈ Z' → (fun s => z (ι s)) ∈ Z := by
  subst hH
  have hj : Continuous ι.rangeRestrict := hc.subtype_mk _
  have hb : Function.Bijective ι.rangeRestrict :=
    ⟨fun a b h => hi (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let r : (ι.range → N) →+ (D → N) :=
    { toFun := fun z s => z (ι.rangeRestrict s), map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨Z.comap r, fun z hz => ⟨fun s => ?_, fun s t => ?_⟩, h2, ?_, fun z hz => hz⟩
  · rw [← (hj.isClosedMap.isQuotientMap hj hb.2).isOpen_preimage]
    exact (h1 hz).1 s
  · obtain ⟨s, rfl⟩ := hb.2 s
    obtain ⟨t, rfl⟩ := hb.2 t
    rw [← map_mul]
    exact (h1 hz).2 s t
  · exact (Nat.card_congr (((Equiv.ofBijective _ hb).symm.arrowCongr (Equiv.refl N)).subtypeEquiv fun z => Iff.rfl)).symm

private theorem numer {V W : Type} [Fintype V] [Fintype W] (m : V → W) (hm : Function.Injective m) (f : V → ℕ) (g : W → ℕ)
    (n x : ℕ) (hn : 0 < n) (h1 : ∀ v, f v = g (m v)) (h2 : ∀ w, w ∉ Set.range m → n ≤ g w)
    (h : n * ∏ w, g w ≤ x * n ^ Fintype.card W) : n * ∏ v, f v ≤ x * n ^ Fintype.card V := by
  classical
  let T : Finset W := Finset.univ.map ⟨m, hm⟩
  have e1 : ∏ w ∈ T, g w = ∏ v, f v := by simp [T, h1]
  have e2 : n ^ Tᶜ.card ≤ ∏ w ∈ Tᶜ, g w := Finset.pow_card_le_prod _ _ _ fun w hw => h2 w (by simpa [T] using hw)
  have e3 : T.card = Fintype.card V := by simp [T]
  rw [← Finset.prod_mul_prod_compl T, ← Finset.card_add_card_compl T, e1, e3, pow_add, ← mul_assoc, ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_left _ e2).trans h) (Nat.pow_pos hn)

private def zrep (n : ℕ) {Γ M : Type} [Group Γ] [AddCommGroup M] [Module (ZMod n) M] (ρ : Representation ℤ Γ M) :
    Representation (ZMod n) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    change ρ 1 m = m
    simp
  map_mul' g h := LinearMap.ext fun m => by
    change ρ (g * h) m = ρ g (ρ h m)
    simp

private theorem lc_orb {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M]
    (ρ : Representation ℤ Γ M) (h : IsOpen (ρ.ker : Set Γ)) (m : M) : IsLocallyConstant fun g => ρ g m := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' (ρ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have : ρ (g⁻¹ * x) = 1 := hx
  rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]

private theorem bare (P : GC.Hypotheses₂) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ContainsAbove T l)
    (ε : GS Ω (T : Set (HeightOneSpectrum (𝓞 F))) →* ℤ_[l]ˣ) (hε : ∀ g, ε (toGS Ω _ g) = cycZ F Ω l g)
    (A : T → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v.1) (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (k : ℕ) (hk0 : 0 < k) (N : Type) [AddCommGroup N] [Finite N]
    (τ : Representation ℤ (GS Ω (T : Set (HeightOneSpectrum (𝓞 F)))) N) (hk : ∀ x : N, l ^ k • x = 0)
    (ho : IsOpen (τ.ker : Set (GS Ω (T : Set (HeightOneSpectrum (𝓞 F))))))
    (Z : ∀ w : T, AddSubgroup (Dec (F := F) (A w) → N)) (h1 : ∀ w, (Z w : Set _) ⊆ Zc (τ.comp (locFam T A w)))
    (h2 : ∀ w (Y : N), (fun s => τ (locFam T A w s) Y - Y) ∈ Z w) :
    (Zc τ).Finite ∧ Nat.card N * ∏ w, Nat.card (Z w) ≤
      {z | z ∈ Zc τ ∧ ∀ w, (fun s => z (locFam T A w s)) ∈ Z w}.ncard * (HomMu l k ε τ).ncard *
        (∏ w, {x : N | τ (toGS Ω _ (c w)) x = x}.ncard) * Nat.card N ^ Fintype.card T := by
  classical
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) N) := ⟨AddCommGroup.zmodModule hk⟩
  letI : TopologicalSpace N := ⊥
  haveI : DiscreteTopology N := ⟨rfl⟩
  let ρ := zrep (l ^ k) τ
  have hρ : ∀ g m, ρ g m = τ g m := fun _ _ => rfl
  have hcont : ContAction ρ := continuous_prod_of_discrete_right.2 fun m => (lc_orb τ ho m).continuous
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := k) (S := T) hT
  have hcont' : ContAction (twDual μ ρ) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hcont
  have hμε : ∀ g, ((μ g : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = PadicInt.toZModPow k ((ε g : ℤ_[l]ˣ) : ℤ_[l]) := fun g => by
    obtain ⟨g, rfl⟩ : ∃ s, toGS Ω _ s = g := QuotientGroup.mk_surjective g
    rw [hε, ← MonoidHom.comp_apply, hμ]
    rfl
  haveI : Finite (TDual (ZMod (l ^ k)) N) := GlobalTheory.DualSide.finite_TDual
  haveI := (P.gf F Ω l k N T ρ hk0 hT hcont).2.1
  haveI := (P.gf F Ω l k _ T (twDual μ ρ) hk0 hT hcont').2.1
  have harch : archH0Card T ρ c = ∏ w, {x : N | τ (toGS Ω _ (c w)) x = x}.ncard := by
    rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
      Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
    rfl
  have hdual : Nat.card (H0 (twDual μ ρ)) ≤ (HomMu l k ε τ).ncard := by
    haveI : Finite (N →+ ZMod (l ^ k)) := DFunLike.finite _
    refine Nat.card_le_card_of_injective (β := HomMu l k ε τ)
      (fun y => ⟨AddMonoidHom.mk' (fun x => y.1 x) (fun a b => map_add (show N →ₗ[ZMod (l ^ k)] ZMod (l ^ k) from y.1) a b), fun s x => ?_⟩) fun a b h => ?_
    · have := congrArg (fun φ : TDual (ZMod (l ^ k)) N => φ (ρ s x)) (y.2 s)
      beta_reduce at this
      rw [twDual_apply, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self, hμε] at this
      exact this.symm
    · exact Subtype.ext (LinearMap.ext fun x => DFunLike.congr_fun (congrArg Subtype.val h) x)
  refine core ρ τ hρ (locFam T A) (continuous_locFam T A) _ _ hcont (fun L => ?_) Z h1 h2
  have h := P.gw F Ω l k N T ρ hk0 hl hT hcont μ hμ A hA c (fun w _ => hc w) L
  rw [← harch]
  refine le_trans ?_ (h.ge.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdual))))
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ Nat.card_pos)

end Helpers

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

theorem UpperTheory.V.Z.J.gwlOf :
    GC.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Field κ] (Φ : Frame l κ) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] S K π ι A pl e c, GC.FLink (F := F) (Ω := Ω) l Φ S K π ι A pl e c → GWL Φ := by
  intro P l _ κ _ Φ F Ω _ _ _ _ _ S K π ι A pl e c h k hk0 N _ _ ρ hk ho Z h1 h2
  classical
  haveI := h.real
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨A', hA', hAA⟩ : ∃ A' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ValuationSubring Ω,
      (∀ v, IsPlaceOver (A' v) v) ∧ ∀ v, A' (pl v) = A v := by
    refine ⟨Function.extend pl A fun v => (exists_isPlaceOver Ω v).choose, fun q => ?_, h.loc.inj.extend_apply _ _⟩
    by_cases hq : ∃ v, pl v = q
    · obtain ⟨v, rfl⟩ := hq
      rw [h.loc.inj.extend_apply]
      exact h.loc.isOver v
    · rw [Function.extend_apply' _ _ _ hq]
      exact (exists_isPlaceOver Ω q).choose_spec
  obtain ⟨S', p, hSS, hp, hps, hπ, hker⟩ := GC.levelS F Ω l S K Φ.Γ π h.g
  have hS' : ContainsAbove S' l := fun v hv => hSS (h.g.above v hv)
  have hS : ∀ q, q ∈ S ↔ ∃ v, pl v = q := fun q =>
    ⟨fun hq => (h.loc.mem q).2 (h.only q hq), fun hq => h.g.above q ((h.loc.mem q).1 hq)⟩
  have hZ : ∀ q : S', ∃ Z' : AddSubgroup (Dec (F := F) (A' q.1) → N),
      (Z' : Set _) ⊆ Zc ((ρ.comp π).comp (Dec (F := F) (A' q.1)).subtype) ∧
      (∀ Y : N, (fun s : Dec (F := F) (A' q.1) => ρ (π s.1) Y - Y) ∈ Z') ∧
      (∀ v, pl v = q.1 → Nat.card (Z v) = Nat.card Z' ∧
        ∀ z : G F Ω → N, (fun s : Dec (F := F) (A' q.1) => z s.1) ∈ Z' → (fun s => z (ι v s)) ∈ Z v) ∧
      (q.1 ∉ S → Nat.card N ≤ Nat.card Z' ∧
        ∀ z ∈ Z', ∃ Y : N, ∀ s : Dec (F := F) (A' q.1), s.1 ∈ Ine (F := F) (A' q.1) → z s = ρ (π s.1) Y - Y) := by
    rintro ⟨q, hq'⟩
    by_cases hq : q ∈ S
    · obtain ⟨v, rfl⟩ := (hS q).1 hq
      have hl : Φ.loc v = π.comp (ι v) := MonoidHom.ext (h.loc_eq v)
      obtain ⟨Z', a1, a2, a3⟩ := tran (ι v) (h.loc.cont v) (h.loc.ι_inj v) (Dec (F := F) (A' (pl v)))
        (by rw [hAA, h.loc.range]) (ρ.comp π) (Z v) (by have := h1 v; rwa [hl] at this)
        (by have := h2 v; rwa [hl] at this)
      refine ⟨Z', a1, a2, fun v' hv => ?_, fun hq' => absurd hq hq'⟩
      obtain rfl := h.loc.inj hv
      exact a3
    · obtain ⟨Z', -, a1, a2, a3, a4⟩ := unrLow F Ω (A' q) q (hA' q) N ((ρ.comp π).comp (Dec (F := F) (A' q)).subtype)
        (ho.preimage (h.g.cont.comp continuous_subtype_val))
      exact ⟨Z', a1, a2, fun v hv => absurd ((hS q).2 ⟨v, hv⟩) hq, fun _ => ⟨a4, a3⟩⟩
  choose Z' b1 b2 b3 b4 using hZ
  subst hπ
  obtain ⟨f, hb⟩ := bare P l h.g.odd S' hS' (Φ.eps.comp p) h.eps (fun q => A' q.1) (fun q => hA' q.1)
    (fun w => c (e.symm w)) (fun w => by simpa using h.cc (e.symm w)) k hk0 N (ρ.comp p) hk (ho.preimage hp) Z' b1 b2
  have hinj : Function.Injective fun z : Φ.Γ → N => z ∘ p := hps.injective_comp_right
  have hf : (ZL Φ ρ fun v => Z v).Finite :=
    Set.Finite.of_finite_image (f.subset (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨hz.1.1.comp_continuous hp, fun s t => by simpa using hz.1.2 (p s) (p t)⟩)) hinj.injOn
  refine ⟨hf, numer (fun v => (⟨pl v, hSS ((hS _).2 ⟨v, rfl⟩)⟩ : S')) (fun a b hab => h.loc.inj (congrArg Subtype.val hab))
    _ (fun q => Nat.card (Z' q)) _ _ Nat.card_pos (fun v => (b3 _ v rfl).1)
    (fun q hq => (b4 q fun hq' => hq (let ⟨v, hv⟩ := (hS _).1 hq'; ⟨v, Subtype.ext hv⟩)).1) (hb.trans ?_)⟩
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul ?_ (le_of_eq ?_)) (le_of_eq ?_))
  · refine le_trans (Set.ncard_le_ncard ?_ (hf.image fun z => z ∘ p)) (Set.ncard_image_le hf)
    rintro z ⟨hz, hw⟩
    obtain ⟨y, hy, hyz⟩ := desc p hp hps ρ _ (hker A' hA') z hz (by
      intro x hx
      obtain ⟨q, g, hg, rfl⟩ := Set.mem_iUnion.1 hx
      obtain ⟨Y, hY⟩ := (b4 ⟨q.1, q.2.1⟩ q.2.2).2 _ (hw _)
      have hg1 : g ∈ (p.comp (toGS Ω _)).ker := by
        rw [h.g.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨q.1, q.2.2, A' q.1, hA' q.1, hg⟩
      have := hY ⟨g, Ine_le_Dec _ hg.1⟩ hg.1
      rw [MonoidHom.mem_ker.1 hg1, map_one, one_apply_eq_self, sub_self] at this
      exact this)
    refine ⟨y, ⟨hy, fun v => ?_⟩, funext hyz⟩
    have := (b3 ⟨pl v, hSS ((hS _).2 ⟨v, rfl⟩)⟩ v rfl).2 (fun g => z (toGS Ω _ g)) (hw _)
    simpa only [h.loc_eq, MonoidHom.comp_apply, hyz, SetLike.mem_coe] using this
  · congr 1
    ext φ
    exact (hps.forall (p := fun s => ∀ x, φ (ρ s x) = PadicInt.toZModPow k (Φ.eps s : ℤ_[l]) * φ x)).symm
  · exact Fintype.prod_equiv e.symm _ _ fun w => by rw [h.cw]; rfl
end

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.Z.J

namespace UpperTheory.V.J

def UnitOfP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
    (ξ : R.S.R →ₐ[c₁.O] c₁.O) (r : G L Ω →* GL (Fin 3) (Qbar l)),
    (∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1) →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 = (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1) →
    ∀ v : Φ.V, PotCrysAt r (k.pl v) → ∀ i j,
    (∀ g : Φ.Gv v, (ξ (R.S.ρ.ψ v i g).val).1 = (ξ (R.S.ρ.ψ v j g).val).1 * (cycBar ℚ Ω l (k.j v g).1 : Qbar l)) →
    ∃ i' : Fin 2, UnitAt (R.S.ρ.map (ξ : R.S.R →+* c₁.O)) v i'

theorem tanA_of (hP : GC.Hypotheses₂) (hD : DegEq) (hU : UnitOfP) : TanA := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f R ξ r hr _ hI v hc i j hij
  obtain ⟨i', hu⟩ := hU Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f R ξ r hr hI v hc i j hij
  obtain ⟨cw, hcw, S, K, π, ι', A, pl, e', cc, hF⟩ := linkOf Ω l c.O η _ σ g₁ B M hL.atl L Φ k _ f R.C₀ R.ok
    (hD Ω l ι c N e ψ η σ g₁ B M hL L Φ k v).1
  obtain ⟨δ, hδ, δ', hδ', hi⟩ := Z.J.tan l c₁.O (Φ.ext f) R.C₀ R.ok R.T.lne cw hcw
    (gwlOf hP l _ _ _ Ω S K π ι' A pl e' cc hF) (fun w => leOf2 hP l _ { Φ.ext f with cw := cw } _ Ω S K π ι' A pl e' cc hF w) R.S ξ v i' hu
  exact ⟨δ, hδ.1, δ', hδ'.1, hδ.2, hδ'.2, hi⟩

end UpperTheory.V.J

end

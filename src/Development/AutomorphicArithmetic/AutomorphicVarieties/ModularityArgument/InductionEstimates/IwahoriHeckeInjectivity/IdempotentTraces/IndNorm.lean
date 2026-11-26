module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SwapAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwSummand
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem aux {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G → G) (he : Function.Surjective e) (U : H →L[ℂ] H) (h1 : ∀ v, ‖U v‖ = ‖v‖)
    (h2 : Function.Surjective U) (h3 : ∀ g v, U (π g v) = π (e g) (U v)) (hc : ∀ v, U v ∈ W ↔ v ∈ W) (V : Submodule ℂ H) :
    IsSummandOf π W V ↔ IsSummandOf π W (V.map U.toLinearMap) := by
  let I : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, h1⟩
  have hinj : Function.Injective U := I.injective
  have hcm : ∀ X : Submodule ℂ H, (X.map U.toLinearMap).comap U.toLinearMap = X :=
    fun X => Submodule.comap_map_eq_of_injective hinj X
  have hmc : ∀ X : Submodule ℂ H, (X.comap U.toLinearMap).map U.toLinearMap = X :=
    fun X => Submodule.map_comap_eq_of_surjective h2 X
  have cl1 : ∀ X : Submodule ℂ H, IsClosed (X : Set H) → IsClosed (X.map U.toLinearMap : Set H) :=
    fun X hX => I.isometry.isClosedEmbedding.isClosedMap _ hX
  have cl2 : ∀ X : Submodule ℂ H, IsClosed (X : Set H) → IsClosed (X.comap U.toLinearMap : Set H) :=
    fun X hX => hX.preimage U.continuous
  have i1 : ∀ X : Submodule ℂ H, π.IsInvariant X → π.IsInvariant (X.map U.toLinearMap) := by
    rintro X hX g _ ⟨v, hv, rfl⟩
    obtain ⟨g, rfl⟩ := he g
    exact ⟨_, hX g v hv, h3 g v⟩
  have i2 : ∀ X : Submodule ℂ H, π.IsInvariant X → π.IsInvariant (X.comap U.toLinearMap) := fun X hX g v hv => by
    show U _ ∈ X
    rw [h3]
    exact hX _ _ hv
  constructor
  · intro h
    refine ⟨?_, cl1 _ h.closed, i1 _ h.inv, fun e => h.ne_bot ?_, fun X hX c i => ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact (hc v).2 (h.le hv)
    · rw [← hcm V, e, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 hinj
    · rcases h.irred _ ((Submodule.comap_mono hX).trans (hcm V).le) (cl2 _ c) (i2 _ i) with e | e
      · left; rw [← hmc X, e, Submodule.map_bot]
      · right; rw [← hmc X, e]
  · intro h
    have a1 := cl2 _ h.closed
    have a2 := i2 _ h.inv
    rw [hcm] at a1 a2
    refine ⟨fun v hv => (hc v).1 (h.le ⟨v, hv, rfl⟩), a1, a2, fun e => h.ne_bot ?_, fun X hX c i => ?_⟩
    · rw [e, Submodule.map_bot]
    · rcases h.irred _ (Submodule.map_mono hX) (cl1 _ c) (i1 _ i) with e | e
      · left; rw [← hcm X, e, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 hinj
      · right; rw [← hcm X, e, hcm]

theorem UpperTheory.ConvolutionTheory.Dp.twSummand :
    UpperTheory.ConvolutionTheory.Dp.TwSummand := by
  intro K _ _ n μ _ θ V
  obtain ⟨h1, h2, h3⟩ := twUnitary K n μ θ
  have hinj : Function.Injective θ.U := (⟨θ.U.toLinearMap, h1⟩ : LL μ →ₗᵢ[ℂ] LL μ).injective
  refine aux _ _ θ.e θ.e.surjective θ.U h1 h2 h3 (fun v => ?_) V
  have e : θ.U (PositivityTheory.Rg.Tf.Core.Pc μ v) = PositivityTheory.Rg.Tf.Core.Pc μ (θ.U v) := DFunLike.congr_fun θ.U_comm v
  have a : ∀ x, PositivityTheory.Rg.Tf.Core.Pc μ x = x ↔ x ∈ cuspidalL2 μ := fun x => Submodule.starProjection_eq_self_iff
  rw [← a, ← a, ← e, hinj.eq_iff]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbTwo
theorem UpperTheory.Reformulated.B.Qe21.emb_two :
    ∀ {K M : Type} [inst : Field K] [NumberField K]
    [inst_2 : Field M] [NumberField M] [inst_4 : Algebra K M] [IsGalois K M],
    Module.finrank K M = (2 : ℕ) →
      ∀ (σ : Gal(M/K)),
        σ ≠ (1 : Gal(M/K)) →
          ∀ (τ τ' : M →+* ℂ),
            τ ≠ τ' →
              τ.comp (Algebra.algebraMap K M) = τ'.comp (Algebra.algebraMap K M) →
                τ.comp σ.toRingEquiv.toRingHom = τ' := by
  intro K M _ _ _ _ _ _ h2 σ hσ τ τ' hne hc
  obtain ⟨ρ, hρ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq τ τ' hc
  have hcard : Nat.card Gal(M/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Gal(M/K))).1 hcard
  have h1 : ρ.symm ≠ 1 := by
    intro h
    apply hne
    rw [← hρ, h]
    ext x
    rfl
  have h3 : σ = ρ.symm := (hy σ hσ).trans (hy _ h1).symm
  rw [← hρ, h3]
  ext x
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.NormOfSplit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SignMs
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem neg_ne_self_unit (a : ℂˣ) : -a ≠ a := by
  intro h
  have h1 : -(a : ℂ) = a := by simpa using congrArg Units.val h
  have h2 : (a : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h1
  exact a.ne_zero h2

private theorem half_of_neg_stable (n : ℕ) : ∀ A : Multiset ℂˣ, A.card ≤ n → A.map (fun x => -x) = A →
    ∃ B' : Multiset ℂˣ, A = B' + B'.map fun b => -b := by
  induction n with
  | zero =>
    intro A hA _
    have : A = 0 := Multiset.card_eq_zero.1 (Nat.le_zero.1 hA)
    exact ⟨0, by simp [this]⟩
  | succ n ih =>
    intro A hA hs
    by_cases h0 : A = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h0
    have hna : -a ∈ A := by
      rw [← hs]
      exact Multiset.mem_map_of_mem _ ha
    obtain ⟨A₁, rfl⟩ := Multiset.exists_cons_of_mem ha
    have hna₁ : -a ∈ A₁ := (Multiset.mem_cons.1 hna).resolve_left (neg_ne_self_unit a)
    obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hna₁
    have hC : C.map (fun x => -x) = C := by
      rw [Multiset.map_cons, Multiset.map_cons, neg_neg, Multiset.cons_swap] at hs
      exact (Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 hs)
    have hc : C.card ≤ n := by
      simp only [Multiset.card_cons] at hA
      omega
    obtain ⟨B', hB'⟩ := ih C hc hC
    refine ⟨a ::ₘ B', ?_⟩
    rw [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons, ← hB']

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.signMs :
    SignMs := by
  intro A B _ _ hs hq
  obtain ⟨B', hB'⟩ := half_of_neg_stable _ A le_rfl hs
  refine ⟨B', ?_, hB'⟩
  have h : B'.map (· ^ 2) + B'.map (· ^ 2) = B + B := by
    rw [← hq, hB', Multiset.map_add (f := _), Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun x _ => by simp
  ext x
  have := congrArg (Multiset.count x) h
  simp only [Multiset.count_add] at this
  omega
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem norm_of_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (h : GM.Split M (w.under (𝓞 K))) :
    Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
  haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w]
    have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
      ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  have nv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      Formalism.ConjugateSelfDual.normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [nv, nv]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, Nat.eq_one_of_mul_eq_one_left h1, pow_one]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.sysOf :
    SysOf := by
  intro K M _ _ _ _ _ _ _ _ h2 π π' P hsw hW
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  obtain ⟨χ, hχ, hP⟩ := R.twoParts_holds K M hp (2 * 2) P (Fin 2) (fun _ => 2) ![π, π'] (by norm_num)
    (fun _ => by norm_num) (by simp) hW
  obtain ⟨η, hη⟩ := R.classChar2 K M hp
  obtain ⟨j, hj0, hj, rfl⟩ := (R.normCharPow_holds K M hp η hη).1 χ hχ
  obtain rfl : j = 1 := by omega
  rw [pow_one] at hP
  filter_upwards [hW, hη.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (R.decomp K M hp)] with w hw hg hd
  have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
    have nv : Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) =
        Ideal.absNorm (w.under (𝓞 K)).asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [nv]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm _
  refine ⟨fun w' hne hu => ?_, fun hn => ?_⟩
  · have hn : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
      rcases hd with hd | hd
      · exact hd.2 w rfl
      · exact absurd (congrArg Subtype.val ((Nat.card_eq_one_iff_unique.1 hd.1).1.elim ⟨w', hu⟩ ⟨w, rfl⟩)) hne
    obtain ⟨A, hA, B, hB, e⟩ := hw 1 (by rw [pow_one]; exact hn)
    have e' : A = B 0 + B 1 := by simpa [Fin.sum_univ_two] using e
    exact ⟨B 0, B 1, hB 0, (hsw w w' hu.symm (Or.inl hne.symm) _).1 (hB 1), e' ▸ hA⟩
  · have hne : Formalism.ConjugateSelfDual.normV w ≠ Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := fun e => by
      have : (2 : ℕ) = 1 := Nat.pow_right_injective hq ((hn.symm.trans e).trans (pow_one _).symm)
      omega
    have hv : η.val (w.under (𝓞 K)) = -1 := by
      have h := hg.2.resolve_left hne
      rw [h2] at h
      exact Units.ext (IsPrimitiveRoot.coe_units_iff.2 h).eq_neg_one_of_two_right
    obtain ⟨A, hA, B, hB, e⟩ := hw 2 hn
    have hB0 : π.HasSat w (B 0) := hB 0
    have hB1 : π.HasSat w (B 1) := (hsw w w rfl (Or.inr fun h => hne (norm_of_split w h)) _).1 (hB 1)
    have e1 : B 1 = B 0 := hB1.unique hB0
    have hT := hA.twist hg.1
    rw [hP, hv] at hT
    have hs : A.map (fun x => -x) = A := by simpa using hT.unique hA
    obtain ⟨B', h3, h4⟩ := signMs A (B 0) hA.card hB0.card hs (by rw [e, Fin.sum_univ_two, e1])
    exact ⟨A, B', h3 ▸ hB0, h4, hA⟩
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem U_invol {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ)
    (h : ∀ g, θ.e (θ.e g) = g) (v : L2 μ) : θ.U (θ.U v) = v := by
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by
    rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h2, q2⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e.symm hg' hp'
  have hs : ∀ g, θ.e.symm (θ.e.symm g) = g := fun g => by
    have := h (θ.e.symm (θ.e.symm g))
    rw [θ.e.apply_symm_apply, θ.e.apply_symm_apply] at this
    exact this.symm
  refine Lp.ext ?_
  filter_upwards [θ.U_spec (θ.U v), q2.quasiMeasurePreserving.ae_eq_comp (θ.U_spec v)] with y a b
  simp only [Function.comp_apply] at b
  rw [a, b, h2, hs]
  congr 1
  exact Quotient.out_eq y

private theorem irr_of {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {V : Submodule ℂ (L2 μ)} (h : IsSummand μ V) : CuspIrr μ V :=
  ⟨h.le, h.closed, h.ne_bot, fun g v hv => h.inv g v hv, fun ρ a b c => h.irred ρ a b c⟩

private theorem unr_of_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (v : Pl K) (h : GM.Split M v) : GM.Unr M v := by
  rintro ⟨w, hl⟩
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hl.over
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w]
    have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
      ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.2 (Nat.eq_one_of_mul_eq_one_right h1)

private theorem sat_iff {M : Type} [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] {n : ℕ} {μ : Measure (G1 M n)} [μ.IsHaarMeasure]
    {π : CuspSub M n} {V : Submodule ℂ (L2 μ)} (h : Dp.Carries μ π V) (w : Pl M) (B : Multiset ℂˣ) :
    (CG.mk π).HasSat w B ↔ SSat μ V w (B.map fun b : ℂˣ => (b : ℂ)) := by
  rw [Dp.sSatIff M n μ π V h w]
  constructor
  · exact fun hB => ⟨B, rfl, hB⟩
  · rintro ⟨B', e, hB⟩
    rw [Multiset.map_injective Units.val_injective e]
    exact hB

private theorem exAt {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (hn : 0 < n) {μ : Measure (G1 E n)}
    [μ.IsHaarMeasure] {V : Submodule ℂ (L2 μ)} (hV : IsSummand μ V) (S : Set (Pl E)) (h : ∀ w ∉ S, ∃ B, SSat μ V w B) :
    ∃ m B, At μ S V m B := by
  choose m hm using fun τ => ((Dp.parEx E n hn μ V hV).1 τ).exists
  refine ⟨m, fun w => if hw : ∃ B, SSat μ V w B then hw.choose else 0, hm, fun w hw => ?_⟩
  have hx := h w hw
  simp only [dif_pos hx]
  exact hx.choose_spec

private theorem emb_two {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (h2 : Module.finrank K M = 2) (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) (τ τ' : M →+* ℂ) (hne : τ ≠ τ')
    (he : τ.comp (algebraMap K M) = τ'.comp (algebraMap K M)) : τ.comp σ.toRingEquiv.toRingHom = τ' :=
  _root_.UpperTheory.Reformulated.B.Qe21.emb_two h2 σ hσ τ τ' hne he

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indNorm :
    CoreInd → IndNorm := by
  intro hC K M _ _ _ _ _ _ _ _ h2 π hn hc hb
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (M ≃ₐ[K] M) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : M ≃ₐ[K] M)
  have hgen : ∀ τ : M ≃ₐ[K] M, τ ∈ Subgroup.zpowers σ := fun τ => mem_zpowers_of_prime_card hcard hσ
  obtain ⟨-, hAtE, -, -, -, θ, hθ, hst⟩ :=
    UpperTheory.ConvolutionTheory.T.carryLift K M σ hgen hp 2 two_pos (BW.mu1 M 2) (BW.mu1 K 2)
  have hG := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc K M σ h2 hgen 2 two_pos (BW.mu1 M 2) θ
  have hIsGal := hG.1.1 hθ
  obtain ⟨hinv, -, hspl⟩ := hG.2 hθ
  obtain ⟨τ₁, hτ₁⟩ : ∃ V, Dp.Carries (BW.mu1 M 2) π V :=
    ⟨_, (Dp.exSummand M 2 _ π _).2 ⟨(Dp.normIff M 2 π).1 hn, rfl⟩⟩
  have hs₁ := hτ₁.summand
  obtain ⟨τ₂, hτ₂d⟩ : ∃ τ₂, τ₁.map (θ.U : L2 (BW.mu1 M 2) →ₗ[ℂ] L2 (BW.mu1 M 2)) = τ₂ := ⟨_, rfl⟩
  have hs₂ : IsSummand (BW.mu1 M 2) τ₂ := hτ₂d ▸ (Dp.twSummand M 2 _ θ τ₁).1 hs₁
  have hback : τ₂.map (θ.U : L2 (BW.mu1 M 2) →ₗ[ℂ] L2 (BW.mu1 M 2)) = τ₁ := by
    rw [← hτ₂d]
    ext v
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      show θ.U (θ.U u) ∈ τ₁
      rwa [U_invol θ hinv]
    · intro hv
      exact ⟨θ.U v, ⟨v, hv, rfl⟩, U_invol θ hinv v⟩
  have hne : τ₁ ≠ τ₂ := fun e => hc σ hσ ((hst π τ₁ hτ₁).2 (hτ₂d.trans e.symm) σ)
  have hPair : Pair (BW.mu1 M 2) τ₁ τ₂ := ⟨irr_of hs₁, irr_of hs₂, Dp.multiplicity_one_cuspidal_spectrum_normOneGL M 2 _ τ₁ τ₂ hs₁ hs₂ hne⟩
  obtain ⟨π', hτ₂, -⟩ := Dp.exCusp M 2 _ τ₂ hs₂
  obtain ⟨hsI, hsS⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.swapAt K M σ h2 hgen τ₁ τ₂ θ hPair hIsGal hτ₂d hback
  obtain ⟨Λ₁, t₁, S₁, hfin, hAt₁⟩ := hAtE τ₁ hs₁
  let S : Finset (Pl K) := (hfin.image fun w => w.under (𝓞 K)).toFinset.filter (GM.Split M)
  have hS : ∀ v, v ∈ S ↔ GM.Split M v ∧ ∃ w ∈ S₁, w.under (𝓞 K) = v := fun v => by
    simp [S, and_comm]
  have hSs : ∀ v ∈ S, GM.Split M v := fun v hv => ((hS v).1 hv).1
  have hSu : ∀ v ∉ S, GM.Unr M v := fun v _ => by
    by_cases h : GM.Split M v
    · exact unr_of_split v h
    · exact (hb v h).1
  have other : ∀ w : Pl M, GM.Split M (w.under (𝓞 K)) → ∃ w' : Pl M, w' ≠ w ∧ w'.under (𝓞 K) = w.under (𝓞 K) := fun w h => by
    obtain ⟨e, -⟩ := hspl _ h
    haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have hx : e (e.symm ⟨w, hl⟩ + 1) ≠ ⟨w, hl⟩ := fun hh => by
      have := e.injective (hh.trans (e.apply_symm_apply _).symm)
      revert this
      generalize e.symm _ = i
      revert i
      decide
    exact ⟨(e (e.symm ⟨w, hl⟩ + 1)).1, fun hh => hx (Subtype.ext hh), HeightOneSpectrum.ext (e _).2.over.symm⟩
  have hSat₁ : ∀ w : Pl M, w.under (𝓞 K) ∉ S → ∃ B, SSat (BW.mu1 M 2) τ₁ w B := fun w hw => by
    by_cases h : GM.Split M (w.under (𝓞 K))
    · exact ⟨t₁ w, hAt₁.2 w fun hm => hw ((hS _).2 ⟨h, w, hm, rfl⟩)⟩
    · obtain ⟨B, hB⟩ := (hb _ h).2 w rfl
      exact ⟨_, (sat_iff hτ₁ w B).1 hB⟩
  have hSat₂ : ∀ w : Pl M, w.under (𝓞 K) ∉ S → ∃ B, SSat (BW.mu1 M 2) τ₂ w B := fun w hw => by
    by_cases h : GM.Split M (w.under (𝓞 K))
    · obtain ⟨w', hne', hu⟩ := other w h
      obtain ⟨B, hB⟩ := hSat₁ w' (hu ▸ hw)
      exact ⟨B, (hsS w w' hu.symm (Or.inl hne'.symm) B).2 hB⟩
    · obtain ⟨B, hB⟩ := hSat₁ w hw
      exact ⟨B, (hsS w w rfl (Or.inr h) B).2 hB⟩
  obtain ⟨m₁, B₁, hA₁⟩ := exAt two_pos hs₁ {w | w.under (𝓞 K) ∈ S} hSat₁
  obtain ⟨m₂, B₂, hA₂⟩ := exAt two_pos hs₂ {w | w.under (𝓞 K) ∈ S} hSat₂
  obtain ⟨V, Λ, t, hV, ⟨S₃, hf₃, hA₃⟩, hΛ, ht⟩ :=
    hC K M σ h2 hgen τ₁ τ₂ θ hPair hIsGal hτ₂d hback S hSs hSu m₁ m₂ B₁ B₂ hA₁ hA₂ (BW.mu1 K (2 + 2))
  obtain ⟨P, hP, -⟩ := Dp.exCusp K (2 + 2) _ V hV
  refine ⟨P, ?_, ?_⟩
  · refine sysOf K M h2 (CG.mk π) (CG.mk π') (CG.mk P) (fun w w' hu hor B => ?_) ?_
    · rw [sat_iff hτ₂, sat_iff hτ₁]
      exact hsS w w' hu hor _
    · have hev : ∀ᶠ w : Pl M in cofinite, w.under (𝓞 K) ∉ S₃ :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hf₃.compl_mem_cofinite
      have hev' : ∀ᶠ w : Pl M in cofinite, w.under (𝓞 K) ∉ S :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually S.finite_toSet.compl_mem_cofinite
      filter_upwards [ht, hev, hev'] with w hw₁ hw₃ hwS f hf
      obtain ⟨C₁, e₁, c₁⟩ := (Dp.sSatIff M 2 _ π τ₁ hτ₁ w _).1 (hA₁.2 w hwS)
      obtain ⟨C₂, e₂, c₂⟩ := (Dp.sSatIff M 2 _ π' τ₂ hτ₂ w _).1 (hA₂.2 w hwS)
      obtain ⟨C₃, e₃, c₃⟩ := (Dp.sSatIff K (2 + 2) _ P V hP _ _).1 (hA₃.2 _ hw₃)
      have hnorm : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
          Formalism.ConjugateSelfDual.normV v = Ideal.absNorm v.asIdeal := by
        intro F _ _ v
        rw [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
        rw [hnorm]
        exact NumberField.HeightOneSpectrum.one_lt_absNorm _
      have hfr : f = resDeg K w := by
        have hpl : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ resDeg K w :=
          by
            rw [hnorm, hnorm]
            exact (UpperTheory.ConvolutionTheory.T.places K M hp).2.2.2.2.1 w
        exact Nat.pow_right_injective hq (hf.symm.trans hpl)
      refine ⟨C₃, c₃, ![C₁, C₂], ?_, ?_⟩
      · intro i
        fin_cases i
        · exact c₁
        · exact c₂
      · apply Multiset.map_injective Units.val_injective
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [Multiset.map_add (f := _), ← e₁, ← e₂, hw₁, bcSat, e₃, hfr]
        simp [Multiset.map_map, Function.comp_def]
  · intro τ τ' m m' hne' hk hm hm'
    have e1 : m₁ τ = m := ((Dp.parEx M 2 two_pos _ τ₁ hs₁).1 τ).unique (hA₁.1 τ) ((Dp.sInfIff M 2 _ π τ₁ hτ₁ τ m).2 hm)
    have e2 : m₂ τ = m' := by
      refine ((Dp.parEx M 2 two_pos _ τ₂ hs₂).1 τ).unique (hA₂.1 τ) ((hsI τ m').2 ?_)
      rw [emb_two h2 σ hσ τ τ' hne' hk]
      exact (Dp.sInfIff M 2 _ π τ₁ hτ₁ τ' m').2 hm'
    have e3 : Λ (τ.comp (algebraMap K M)) = m + m' := by
      have := congrFun hΛ τ
      simp only [bcInf] at this
      rw [← this, e1, e2]
    have h4 := hA₃.1 (τ.comp (algebraMap K M))
    rw [e3] at h4
    exact (Dp.sInfIff K (2 + 2) _ P V hP _ _).1 h4

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlagU

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem finite_translation_mul (g h : GL (Fin a) (Af F)) (φ : TR.Sm F a) :
    TR.finRep F a (g * h) φ = TR.finRep F a g (TR.finRep F a h φ) := by
  rw [map_mul]; rfl

private theorem center_algebra_translation_comm (g : GL (Fin a) (Af F)) {z : Module.End ℂ (TR.Sm F a)} (hz : z ∈ TR.Zalg F a) :
    TR.finRep F a g * z = z * TR.finRep F a g := by
  have key : TR.Zalg F a ≤ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    have hE : ∀ i j, TR.Eop v i j ∈ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
      intro i j
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (TR.lie_rt_fin _ g).symm
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.list_prod_mem _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (key hz) _ rfl

private theorem compact_finite_translation_comm (g : GL (Fin a) (Af F)) (k : TR.Kinf F a) (φ : TR.Sm F a) :
    TR.cptRep F a k (TR.finRep F a g φ) = TR.finRep F a g (TR.cptRep F a k φ) := by
  refine Subtype.ext (funext fun x => ?_)
  change φ.1 (x * TR.infGL F a (Unitary.toUnits k) * finGL F a g) =
    φ.1 (x * finGL F a g * TR.infGL F a (Unitary.toUnits k))
  rw [mul_assoc, mul_assoc, TR.infGL_comm]

private theorem automorphic_form_translate (φ : TR.Sm F a) (g : GL (Fin a) (Af F)) (h : TR.IsAutForm φ) :
    TR.IsAutForm (TR.finRep F a g φ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 (ratGL F a γ * x * finGL F a g) = φ.1 (x * finGL F a g)
    rw [mul_assoc, h.left]
  · have e : {k | TR.finRep F a k (TR.finRep F a g φ) = TR.finRep F a g φ} =
        (fun k => g⁻¹ * k * g) ⁻¹' {k | TR.finRep F a k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hk
        rw [finite_translation_mul, finite_translation_mul, hk, ← finite_translation_mul, inv_mul_cancel, map_one]
        rfl
      · intro hk
        have := congrArg (TR.finRep F a g) hk
        rwa [← finite_translation_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, finite_translation_mul] at this
    rw [e]
    exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ)).map (TR.finRep F a g)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (compact_finite_translation_comm g k φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a)).map (TR.finRep F a g))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, LinearMap.congr_fun (center_algebra_translation_comm g hz) φ⟩
  · obtain ⟨C, N, hC⟩ := h.growth (x * finGL F a g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (x * TR.infGL F a y * finGL F a g)‖ ≤ _
    rw [mul_assoc, TR.infGL_comm, ← mul_assoc]
    exact hC y

private theorem automorphic_form_linear_combination (φ ψ : TR.Sm F a) (c : ℂ) (h : TR.IsAutForm φ) (h' : TR.IsAutForm ψ) :
    TR.IsAutForm (φ + c • ψ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 _ + c * ψ.1 _ = φ.1 _ + c * ψ.1 _
    rw [h.left, h'.left]
  · rw [isOpen_iff_mem_nhds]
    intro k₀ hk₀
    have hO : IsOpen ((fun k => k₀⁻¹ * k) ⁻¹' ({k | TR.finRep F a k φ = φ} ∩ {k | TR.finRep F a k ψ = ψ})) :=
      (h.level.inter h'.level).preimage (continuous_const.mul continuous_id)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
    · simp
    · rintro k ⟨h1, h2⟩
      have h1' : TR.finRep F a (k₀⁻¹ * k) φ = φ := h1
      have h2' : TR.finRep F a (k₀⁻¹ * k) ψ = ψ := h2
      have h3 : TR.finRep F a (k₀⁻¹ * k) (φ + c • ψ) = φ + c • ψ := by rw [map_add (f := _), map_smul, h1', h2']
      have h4 : TR.finRep F a k₀ (φ + c • ψ) = φ + c • ψ := hk₀
      change TR.finRep F a k (φ + c • ψ) = φ + c • ψ
      rw [← mul_inv_cancel_left k₀ k, finite_translation_mul, h3, h4]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ) ⊔
        Submodule.span ℂ (Set.range fun k => TR.cptRep F a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z ψ) '' TR.Zalg F a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
  · obtain ⟨C, N, hC⟩ := h.growth x
    obtain ⟨D, M, hD⟩ := h'.growth x
    refine ⟨|C| + ‖c‖ * |D|, N + M, fun y => ?_⟩
    have h1 : 1 ≤ TR.height y := by
      unfold TR.height
      have := norm_nonneg (TR.toL y.val)
      have := norm_nonneg (TR.toL (y⁻¹).val)
      linarith
    have bound : ∀ (B : ℝ) (n : ℕ), n ≤ N + M → B * TR.height y ^ n ≤ |B| * TR.height y ^ (N + M) := fun B n hn =>
      mul_le_mul (le_abs_self B) (pow_le_pow_right₀ h1 hn) (pow_nonneg (zero_le_one.trans h1) n) (abs_nonneg B)
    have b1 := (hC y).trans (bound C N (Nat.le_add_right _ _))
    have b2 := (hD y).trans (bound D M (Nat.le_add_left _ _))
    change ‖φ.1 _ + c * ψ.1 _‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, add_mul, mul_assoc]
    exact add_le_add b1 (mul_le_mul_of_nonneg_left b2 (norm_nonneg c))

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_operators_commute_on_automorphic_forms :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), TR.IsAutForm (0 : TR.Sm F a) ∧ (∀ (φ : TR.Sm F a) (g : GL (Fin a) (Af F)), TR.IsAutForm φ → TR.IsAutForm (TR.finRep F a g φ)) ∧ ∀ (φ ψ : TR.Sm F a) (z : ℂ), TR.IsAutForm φ → TR.IsAutForm ψ → TR.IsAutForm (φ + z • ψ) := by
  intro F _ _ _ a
  exact ⟨TR.isAutForm_const (Submodule.zero_mem _), automorphic_form_translate, automorphic_form_linear_combination⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EventuallyMemHeckeLevelAndIwahoriCongruence
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_not {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ¬ ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dite_eq_right h]
  rfl

private theorem cmp_cont (l : ℕ) [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L) :
    Continuous fun k : finU (E := L) (n := n) => cmp n w ((away l L n).rangeRestrict (k : UA L n)) := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · simp only [cmp_of h]
    exact ((UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).1 w).comp continuous_subtype_val
  · simp only [cmp_not h]
    exact continuous_const

private theorem cmp_ev (l : ℕ) [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L)
    (U : Subgroup (GLw n w)) (hU : IsOpen (U : Set (GLw n w))) :
    ∀ᶠ k : finU (E := L) (n := n) in nhds 1, cmp n w ((away l L n).rangeRestrict (k : UA L n)) ∈ U := by
  refine (hU.preimage (cmp_cont l n w)).mem_nhds ?_
  change cmp n w ((away l L n).rangeRestrict ((1 : finU (E := L) (n := n)) : UA L n)) ∈ U
  rw [OneMemClass.coe_one, map_one, map_one]
  exact one_mem U

private theorem cmp_int {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (x : UA L n) (hx : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) :
    cmp n w ((away l L n).rangeRestrict x) ∈ KO (w.adicCompletion L) (Fin n) := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rwa [cmp_of h]
  · rw [cmp_not h]
    exact one_mem _

private theorem pi_mem_first_iwahori_filtration {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) (b : ℕ)
    (g : ∀ v, G v) (hg : ∀ v, g v ∈ (I v).I1 b) : g ∈ (piIwa I).I1 b := by
  choose x hx t ht y hy e using fun v => (iwMem _ (I v) b (g v)).2.1.1 (hg v)
  exact (iwMem _ (piIwa I) b g).2.1.2 ⟨x, fun v _ => hx v, t, fun v _ => ht v, y, fun v _ => hy v, funext e⟩

theorem UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), IsOpen (τ₀.ker : Set (KT n (wt s))) → ∀ (K : (hset Q τ₀).Lev) (b : ℕ), ∀ᶠ k : finU (E := L) (n := n) in nhds 1, (∃ u : Ub n s, u ∈ (hset Q τ₀).lev K ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧ (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ hτ K b
  obtain ⟨hc, hK, hint⟩ := UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hτ
  have h1 : ∀ᶠ k : finU (E := L) (n := n) in nhds 1,
      (fun u : s.St => cmp n (s.w u) ((away l L n).rangeRestrict (k : UA L n)) : GV n (wt s)) ∈ U := by
    refine (hU.preimage (continuous_pi fun u : s.St => cmp_cont l n (s.w u))).mem_nhds ?_
    have h0 : (1 : KT n (wt s)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      exact one_mem τ₀.ker
    have e : (fun u : s.St => cmp n (s.w u) ((away l L n).rangeRestrict ((1 : finU (E := L) (n := n)) : UA L n)) : GV n (wt s)) = 1 := by
      funext u
      rw [OneMemClass.coe_one, map_one, map_one]
      rfl
    rw [Set.mem_preimage, e]
    exact h0
  have h2 := cmp_ev l n (s.w s.v0) _ (hK (s.w s.v0) 1)
  have h3 : ∀ᶠ k : finU (E := L) (n := n) in nhds 1, ∀ q : Q.Q, cmp n (Q.wq q) ((away l L n).rangeRestrict (k : UA L n)) ∈ K.1 q :=
    Filter.eventually_all.2 fun q => cmp_ev l n (Q.wq q) (K.1 q) (K.2 q).1
  have h4 : ∀ᶠ k : finU (E := L) (n := n) in nhds 1, ∀ v : V.frame.Vl,
      cLoc (s.w v.1) (k : UA L n) ∈ Kc ((s.w v.1).adicCompletion L) n (b + 1) := by
    haveI : Finite V.frame.Vl := (hset Q τ₀).finV.finite
    refine Filter.eventually_all.2 fun v => ?_
    refine ((hK (s.w v.1) (b + 1)).preimage ((hc (s.w v.1)).comp continuous_subtype_val)).mem_nhds ?_
    change cLoc (s.w v.1) ((1 : finU (E := L) (n := n)) : UA L n) ∈ Kc ((s.w v.1).adicCompletion L) n (b + 1)
    rw [OneMemClass.coe_one, map_one]
    exact one_mem _
  filter_upwards [hint, h1, h2, h3, h4] with k k0 k1 k2 k3 k4
  have hu : (away l L n).rangeRestrict (k : UA L n) ∈ Ub n s :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => cmp_int _ (k0 _), k2⟩
  refine ⟨⟨⟨_, hu⟩, UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K _ (fun w _ => cmp_int _ (k0 w)) k3, rfl, ?_⟩, ?_⟩
  · have : toKT n s ⟨_, hu⟩ ∈ Subtype.val ⁻¹' U := k1
    rw [hUe] at this
    exact this
  · exact pi_mem_first_iwahori_filtration (fun v : V.frame.Vl => glIwa ((s.w v.1).adicCompletion L) n) b _ fun v =>
      (glBridge ((s.w v.1).adicCompletion L) n ℂ 1).2.2.2.2.1 b (k4 v)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamWeightsOfLocalArtinCharacters
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_q {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((normV w : ℕ) : Qbar l) ≠ 0 ∧ ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd : l ∣ normV w := by
    rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec] at hw
    have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
    rw [(Nat.prime_dvd_prime_iff_eq hq Fact.out).1 hw]
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact_mod_cast Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)

private theorem abs_art {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (c : ℤ) (s : Weil h) :
    (GlobalTheory.SmGL.absPow (w.adicCompletion F) (c : ℂ) (a s) : ℂ) = ((normV w : ℕ) : ℂ) ^ (c * deg s) := by
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV, Complex.cpow_intCast,
    mul_comm, zpow_mul]
  push_cast
  rfl

private theorem cont_smooth {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] {B : Type} [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (f : X →* B) (hf : IsOpen (f.ker : Set X)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : B))).congr ?_
  filter_upwards [hf.mem_nhds f.ker.one_mem] with x hx
  exact (MonoidHom.mem_ker.1 hx).symm

theorem UpperTheory.deRham_weights_of_localArtin_characters :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := F) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (m : Fin n → ℤ), (∀ i j, i < j → m j + 2 ≤ m i) → ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ), (∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j)) → (∀ j (s : Weil h), ‖ι.symm (ω j (a s) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m j * deg s)) → Hi.DRat ι h r (fun _ => Finset.univ.val.map fun j => -m j) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → ∃ κ : Fin n → Dec (F := F) A →* (Qbar l)ˣ, W.HasFlag r κ ∧ ∀ j (s : Weil h), (κ j (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) = ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
  intro N F Ω _ _ _ _ _ l _ hl ι n w hw A h a ha r hr m hm ω hω hn hD
  obtain ⟨q0, q1⟩ := norm_q w hw
  have q2 : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 q0
  have hcyc : Continuous (cycBar F Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)
  have key : ∀ j, ∃ κ : Dec (F := F) A →* (Qbar l)ˣ, Continuous κ ∧ ∀ s : Weil h,
      (κ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) =
        ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
    intro j
    let φ := ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ)
    have hφ : GlobalTheory.SmGL.IsSmoothChar φ :=
      (hω j).mul (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _))
    let ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp φ
    have hξ : ∀ s, (ξ (a s) : Qbar l) = ι.symm (ω j (a s) : ℂ) * ((normV w : ℕ) : Qbar l) ^ (-m j * deg s) := by
      intro s
      show ι.symm ((ω j (a s) : ℂ) * (GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ) (a s) : ℂ)) = _
      rw [abs_art ha, map_mul, map_zpow₀, map_natCast]
    have hc : Continuous ξ := by
      refine cont_smooth ξ (Subgroup.isOpen_mono (fun x hx => ?_) hφ)
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]
    obtain ⟨κ, ⟨c1, c2⟩, -⟩ := UpperTheory.V.Loc.laExists N.aut.art h a ha ξ hc fun x => by
      obtain ⟨s, rfl⟩ := ha.surj x
      rw [hξ, norm_mul, hn, norm_zpow, ← zpow_add₀ q2.ne', neg_mul, add_neg_cancel, zpow_zero]
    refine ⟨κ * ((cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m j,
      c1.mul ((continuous_zpow (m j)).comp (hcyc.comp continuous_subtype_val)), fun s => ?_⟩
    show ((κ (Subgroup.inclusion (Weil_le_Dec h) s) * cycBar F Ω l (s : G F Ω) ^ m j : (Qbar l)ˣ) : Qbar l) * _ = _
    rw [c2, Units.val_mul, hξ, Units.val_zpow_eq_zpow_val, neg_mul, zpow_neg, mul_right_comm,
      inv_mul_cancel_right₀ (zpow_ne_zero _ q0)]
  choose κ hκ hv using key
  refine ⟨κ, (UpperTheory.V.Loc.ordFlagU N F Ω l hl ι n w hw A h a ha r hr (fun j _ => -m j)
    (fun _ i j hij => ?_) ω κ (fun j => ⟨hω j, hκ j, fun s g hg _ => ?_⟩) (fun i j hij => ?_) hD).1, hv⟩
  · have := hm i j hij
    show -m i < -m j
    omega
  · obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
    have h1 := hv j s
    rw [UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s, mul_zpow, ← zpow_mul, mul_comm (deg s), mul_comm (_ ^ _),
      ← mul_assoc] at h1
    refine (mul_right_cancel₀ (zpow_ne_zero _ q0) h1).trans ?_
    congr 1
    haveI := finite_contEmb (l := l) w
    letI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    simp
  · have hi := hn i (frob h)
    have hj := hn j (frob h)
    rw [deg_frob, mul_one] at hi hj
    have hij' : m i ≠ m j ∧ m i ≠ m j + 1 := by
      rcases lt_or_gt_of_ne hij with h1 | h1
      · have := hm _ _ h1; omega
      · have := hm _ _ h1; omega
    refine ⟨fun e => hij'.1 ?_, fun e => hij'.2 ?_⟩
    · rw [e, hj] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
    · have h1 := abs_art ha 1 (frob h)
      rw [deg_frob, mul_one, zpow_one, Int.cast_one] at h1
      rw [e, MonoidHom.mul_apply, Units.val_mul, h1, map_mul, map_natCast, norm_mul, hj, ← zpow_add_one₀ q2.ne'] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
end

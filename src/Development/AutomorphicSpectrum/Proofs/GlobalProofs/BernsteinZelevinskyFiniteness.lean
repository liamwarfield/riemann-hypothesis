module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
namespace GlobalTheory.CompanionTheory.Published

theorem bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  fun k _ _ _ _ => ⟨GlobalTheory.T.irreducible_smooth_admissible_GL k, GlobalTheory.T.jacquet_module_finite_length k, GlobalTheory.T.parabolic_induction_finite_length k, GlobalTheory.T.parabolic_induction_contragredient k⟩

end GlobalTheory.CompanionTheory.Published
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernstein_zelevinsky_finiteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  first | exact @GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | exact GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | (intros; apply GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal
open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

attribute [local instance 2000] Rep.hV2

theorem dualityFor_absGal (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (χ : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* (ZMod (l ^ r))ˣ)
    (hχ : ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ ((χ σ : ZMod (l ^ r)).val))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) M)
    (hrho : ContAction rho) : ReciprocityTheory.Neutral.Bridge.DualityFor χ rho hrho := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  have hD : ∀ (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (m : ZMod (l ^ r)),
      e.symm ((χ g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g (e.symm m) := by
    intro g m
    have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g x =
          (χ g : ZMod (l ^ r)).val • x := by
      intro x
      rw [galRootsOfUnity_ρ_apply]
      apply Additive.toMul.injective
      rw [toMul_ofMul, toMul_nsmul]
      apply Subtype.ext
      apply Units.ext
      rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
      refine hχ g _ ?_
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
    refine Eq.trans ?_ (key _).symm
    refine Eq.trans ?_ (map_nsmul e.symm _ m)
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact PositivityTheory.LocalTateOrthogonality.Gcoh.tate_core PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep PositivityTheory.LocalTateOrthogonality.Gcoh.gc0
    PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    χ e.symm hD M rho hrho

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hrho
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (hA ((p : ℕ) : 𝓞 F)).2 hpv
    simpa using this
  obtain ⟨ι, h⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat F A hval
  let E : ReciprocityTheory.Neutral.Cmp.GK F ι ≃ₜ* Dec (F := F) A := ReciprocityTheory.Neutral.Cmp.equiv h
  let χ : Dec (F := F) A →* (ZMod (l ^ r))ˣ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype
  have hχ : ∀ (σ : ReciprocityTheory.Neutral.Cmp.GK F ι) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ (((χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ :
        (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro σ ζ hζ
    have e1 := ReciprocityTheory.Neutral.Cmp.cycZ_res (F := F) ι l σ
    have e3 : (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ =
        Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom
          (cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p)) := by
      rw [← e1]
      rfl
    rw [e3]
    exact cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) ζ hζ
  have hD := dualityFor_absGal p (ReciprocityTheory.Neutral.Cmp.Kloc F ι)
    (ReciprocityTheory.Neutral.Cmp.finiteDimensional_Kloc ι) l r
    (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) hχ M
    (rho.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A))
    (ReciprocityTheory.Neutral.Bridge.contAction_comp E hrho)
  exact ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp E χ hrho hD

end GlobalTheory.CompanionTheory.Hypotheses₂
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

variable {F : Type} [Field F] [NumberField F]

theorem singleV_apply_self' (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : (singleV F v s) v = s := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v s

theorem singleV_apply_ne' (v w : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (h : w ≠ v) :
    (singleV F v s) w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) s h

theorem singleV_mul_box (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (b : Af F) :
    singleV F v s * b = singleV F v (s * b v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change (singleV F v s) w * b w = (singleV F v (s * b v)) w
  by_cases h : w = v
  · subst h
    rw [singleV_apply_self', singleV_apply_self']
  · rw [singleV_apply_ne' v w _ h, singleV_apply_ne' v w _ h, zero_mul]

open Classical in
theorem sum_singleV_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (c : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, singleV F v (c v)) w = if w ∈ T then c w else 0 := by
  classical
  have h1 : (∑ v ∈ T, singleV F v (c v)) w = ∑ v ∈ T, (singleV F v (c v)) w :=
    map_sum (evalV F w) _ T
  rw [h1]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun v _ hv => singleV_apply_ne' v w _ (Ne.symm hv))
      (fun h => absurd hw h), singleV_apply_self']
  · exact Finset.sum_eq_zero fun v hv => singleV_apply_ne' v w _ (fun h => hw (h ▸ hv))

theorem singleV_mem_boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hU : ∀ v, (0 : Fv F v) ∈ U v) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v)
    (hS : v ∈ S → s ∈ U v) (hO : v ∉ S → s ∈ v.adicCompletionIntegers F) :
    singleV F v s ∈ Coef.boxA S U := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hS hw
    · rw [singleV_apply_ne' v w _ h]; exact hU w
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hO hw
    · rw [singleV_apply_ne' v w _ h]; exact zero_mem _

theorem annF_boxA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  intro F _ _ ψ hψ S hS U hU
  classical
  ext b
  constructor
  · intro hb
    have key : ∀ v (s : Fv F v), (v ∈ S → s ∈ U v) → (v ∉ S → s ∈ v.adicCompletionIntegers F) →
        psiV F ψ v (s * b v) = 1 := by
      intro v s h1 h2
      have := hb _ (singleV_mem_boxA S U hU v s h1 h2)
      rwa [singleV_mul_box, psiF_singleV] at this
    refine ⟨fun v hv s hs => key v s (fun _ => hs) (fun h => absurd hv h), fun v hv => ?_⟩
    have hmem : b v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) :=
      fun s hs => key v s (fun h => absurd h hv) (fun _ => hs)
    rw [hS v hv] at hmem
    exact hmem
  · rintro ⟨hb1, hb2⟩ y ⟨hy1, hy2⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.adelic_character_trivial_almost_everywhere F ψ hψ
    set c := y * b with hc
    have hcv : ∀ v, c v = y v * b v := fun v => rfl
    set T' := T ∪ S with hT'
    set e : Af F := ∑ v ∈ T', singleV F v (c v) with he
    have hcint : ∀ v, v ∉ S → c v ∈ v.adicCompletionIntegers F := fun v hv => by
      rw [hcv]; exact mul_mem (hy2 v hv) (hb2 v hv)
    have hd : psiF ψ (c - e) = 1 := by
      have happ : ∀ w, (c - e) w = c w - (if w ∈ T' then c w else 0) := fun w => by
        rw [← sum_singleV_apply T' c w]; rfl
      refine hT _ (fun w => ?_) (fun w hw => ?_)
      · rw [happ]
        split_ifs with h
        · rw [sub_self]; exact zero_mem _
        · rw [sub_zero]
          exact hcint w (fun hw => h (Finset.mem_union_right _ hw))
      · rw [happ, if_pos (Finset.mem_union_left _ hw), sub_self]
    have hsum : psiF ψ e = 1 := by
      rw [he]
      refine Finset.sum_induction _ (fun x => psiF ψ x = 1) (fun a b ha hb => by rw [psiF_add, ha, hb, one_mul])
        (psiF_zero ψ) (fun v _ => ?_)
      rw [psiF_singleV]
      by_cases hv : v ∈ S
      · rw [hcv]; exact hb1 v hv (y v) (hy1 v hv)
      · have h1 : c v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := by
          rw [hS v hv]; exact hcint v hv
        have := h1 1 (one_mem _)
        rwa [one_mul] at this
    have : c = (c - e) + e := by abel
    change psiF ψ c = 1
    rw [this, psiF_add, hd, hsum, one_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventuallyStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_annihilator_box_product : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA <;> assumption)
end
end

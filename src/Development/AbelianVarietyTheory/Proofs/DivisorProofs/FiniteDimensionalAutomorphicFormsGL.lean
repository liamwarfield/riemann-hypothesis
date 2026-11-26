module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulIncl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSlowlyIncreasingKilledCapelliPo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSlowlyIncreasingSmoothingMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSlowlyIncreasingSmoothingMem
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth

noncomputable section

open GlobalTheory.AutGrowth.SmoothFinite

namespace GlobalTheory.CapKilledSmooth

theorem smoothing_mem_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (ν : Measure (Lie E b)) [ν.IsAddHaarMeasure] (α : Lie E b → ℂ), IsTest (invSet E b) α → KInv α → ∀ (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (ψ : Sm E b), ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q → ψ.1 ∈ growth E b → ∃ h : smoothing ν α ψ.1 ∈ Sm E b, (⟨smoothing ν α ψ.1, h⟩ : Sm E b) ∈ GlobalTheory.CapKilled.space E b L W q := by
  intro E _ _ _ b ν _ α hα hK L W hW q ψ hψ hg
  obtain ⟨⟨⟨hl, hL⟩, hk⟩, hq⟩ := hψ
  have h := GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E b ν α hα ψ.1 ψ.2
  refine ⟨h, GlobalTheory.CapKilled.mem_space.2 ⟨fun γ g => ?_, fun k hk' => ?_, fun g => ?_, fun τ u => ?_, fun l => ?_⟩⟩
  · show smoothing ν α ψ.1 (ratGL E b γ * g) = smoothing ν α ψ.1 g
    have hl' : ∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g := hl
    simp only [smoothing, chart, mul_assoc, hl']
  · apply Subtype.ext; funext g
    show smoothing ν α ψ.1 (g * finGL E b k) = smoothing ν α ψ.1 g
    have hw : (fun x => ψ.1 (x * finGL E b k)) = ψ.1 := congrArg Subtype.val (hL k hk')
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · obtain ⟨s, c, hc⟩ := GlobalTheory.HCFct.exists_interp W hW
    have hpt : ∀ (k : Kinf E b) (x : GA E b), ψ.1 (x * infGL E b (Unitary.toUnits k)) =
        ∑ i : s, ψ.1 (x * infGL E b (Unitary.toUnits i.1)) * (c i).1 k := fun k x => hc _ (hk x) k
    have hfun : ∀ k : Kinf E b, (fun x => ψ.1 (x * infGL E b (Unitary.toUnits k))) =
        (∑ i : s, (c i).1 k • cptRep E b i.1 ψ : Sm E b).1 := by
      intro k; funext x
      rw [hpt k x, Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
      rfl
    have e : (fun k : Kinf E b => (cptRep E b k ⟨smoothing ν α ψ.1, h⟩).1 g) =
        ∑ i : s, (smoothing ν α (cptRep E b i.1 ψ).1 g) • (c i).1 := by
      funext k
      have e1 : (cptRep E b k ⟨smoothing ν α ψ.1, h⟩).1 g =
          smoothing ν α ψ.1 (g * infGL E b (Unitary.toUnits k)) := rfl
      rw [e1, ← GlobalTheory.T.smoothing_right_translate_maxCompact E b ν α hK ψ.1 k g, hfun k]
      have hsum : ∀ (t : Finset s) (f : s → Sm E b),
          smoothing ν α (∑ i ∈ t, f i).1 = ∑ i ∈ t, smoothing ν α (f i).1 := by
        intro t f
        classical
        induction t using Finset.induction_on with
        | empty => funext x; simp [smoothing, chart]
        | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, smoothing_add ν hα, ih]
      rw [hsum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smoothing_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [e]
    exact W.sum_mem fun i _ => W.smul_mem _ (c i).2
  · have hz : Polynomial.aeval (cap (a := b) τ u) (q τ u) ∈ Zalg E b := by
      show _ ∈ Algebra.adjoin ℂ _
      exact Algebra.adjoin_mono (s := {cap (a := b) τ u}) (by rintro _ rfl; exact ⟨τ, u, rfl⟩)
        (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    apply Subtype.ext
    rw [GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing E b ν α hα ψ h _ hz, (GlobalTheory.CapKilled.mem_killed.1 hq) τ u]
    funext g
    simp [smoothing, chart]
  · obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E b) β ∧
        ((l.map (lie E b)).prod (⟨smoothing ν α ψ.1, h⟩ : Sm E b)).1 = smoothing ν β ψ.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density E b ν β hβ ψ.1 ψ.2 X g
    rw [e]
    exact GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing E b ν β hβ ψ.1 hg

end GlobalTheory.CapKilledSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSlowlyIncreasingSmoothingMemStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliKilled_slowlyIncreasing_smoothing_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (ν : Measure (Lie E b)) [ν.IsAddHaarMeasure] (α : Lie E b → ℂ), IsTest (invSet E b) α → KInv α → ∀ (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (ψ : Sm E b), ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q → ψ.1 ∈ growth E b → ∃ h : smoothing ν α ψ.1 ∈ Sm E b, (⟨smoothing ν α ψ.1, h⟩ : Sm E b) ∈ GlobalTheory.CapKilled.space E b L W q := by
  first | exact @GlobalTheory.CapKilledSmooth.smoothing_mem_space | exact GlobalTheory.CapKilledSmooth.smoothing_mem_space | (intros; apply GlobalTheory.CapKilledSmooth.smoothing_mem_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFiniten
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFiniten
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CapKilled

open Polynomial

theorem aeval_restrict_val {M : Type} [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M) (p : Submodule ℂ M)
    (h : ∀ x ∈ p, f x ∈ p) (P : ℂ[X]) (v : p) :
    ((aeval (f.restrict h) P) v : M) = aeval f P (v : M) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [map_add (f := _), hP, hQ]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
    congr 1
    induction n generalizing v with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem finiteDimensional_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ)) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → (∀ z ∈ Zalg E b, ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q) → FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) := by
  intro E _ _ _ b hP hint L hL W hW q hq hstab
  classical
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := b) τ u ∈ Zalg E b := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let V := GlobalTheory.CapKilled.space E b L W q
  let R : (E →+* ℂ) × Fin (b + 1) → Module.End ℂ V := fun p =>
    (cap (a := b) p.1 ((p.2 : ℕ) : ℂ)).restrict (fun ψ hψ => hstab _ (hcap _ _) ψ hψ)
  have hR : ∀ p (v : V), ((R p v : V) : Sm E b) = cap (a := b) p.1 ((p.2 : ℕ) : ℂ) (v : Sm E b) := fun _ _ => rfl
  let T : Finset (Module.End ℂ V) := Finset.univ.image R
  have key := GlobalTheory.FinEig.fd_of_finset T ?_ ?_ ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  · intro u hu u' hu'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.1 hu'
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hR, hR, hR, hR, ← Module.End.mul_apply,
      (GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hcap _ _) (hcap _ _)).eq, Module.End.mul_apply]
  · intro u hu
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨q p.1 ((p.2 : ℕ) : ℂ), hq _ _, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [aeval_restrict_val]
    exact (GlobalTheory.CapKilled.mem_space.1 v.2).2.2.2.1 _ _
  · intro c
    let w : (E →+* ℂ) → ℂ → Fin (b + 1) → ℂ := fun τ u => Classical.choose (hint τ u)
    have hw : ∀ τ u, cap (a := b) τ u = ∑ j : Fin (b + 1), w τ u j • cap (a := b) τ ((j : ℕ) : ℂ) :=
      fun τ u => Classical.choose_spec (hint τ u)
    let c' : (E →+* ℂ) → ℂ → ℂ := fun τ u => ∑ j : Fin (b + 1), w τ u j * c (R (τ, j))
    let χ : Module.End ℂ (Sm E b) → ℂ := fun z =>
      if h : z ∈ Zalg E b then Classical.choose (GlobalTheory.CuspRep.Zalg_acts_by_scalar E b c' z h) else 0
    let J := (⊤ : Submodule ℂ V) ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ V) (c u))
    have hJcap : ∀ v ∈ J, ∀ τ u, cap (a := b) τ u ((v : V) : Sm E b) = c' τ u • ((v : V) : Sm E b) := by
      intro v hv τ u
      have hj : ∀ j : Fin (b + 1), cap (a := b) τ ((j : ℕ) : ℂ) ((v : V) : Sm E b) =
          c (R (τ, j)) • ((v : V) : Sm E b) := by
        intro j
        have h1 : v ∈ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ V) (c u)) := hv.2
        rw [Submodule.mem_iInf] at h1
        have h1' := h1 (R (τ, j))
        rw [Submodule.mem_iInf] at h1'
        have h2 := h1' (Finset.mem_image_of_mem R (Finset.mem_univ _))
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h2
        have h3 := congrArg (fun x : V => (x : Sm E b)) h2
        simpa only [hR, Submodule.coe_smul] using h3
      rw [hw τ u, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, hj, smul_smul, c', Finset.sum_smul]
    have hJz : ∀ v ∈ J, ∀ z ∈ Zalg E b, z ((v : V) : Sm E b) = χ z • ((v : V) : Sm E b) := by
      intro v hv z hz
      simp only [χ, dif_pos hz]
      exact Classical.choose_spec (GlobalTheory.CuspRep.Zalg_acts_by_scalar E b c' z hz) _ (hJcap v hv)
    have hmem : ∀ v ∈ J, ((v : V) : Sm E b) ∈ GlobalTheory.HCF.formsGL E b L W {χ} 1 := by
      intro v hv
      obtain ⟨hleft, hfix, hK, _, htame⟩ := GlobalTheory.CapKilled.mem_space.1 (v : V).2
      have hkfin : FiniteDimensional ℂ
          (Submodule.span ℂ (Set.range fun k => cptRep E b k ((v : V) : Sm E b))) := by
        obtain ⟨s, bb, hb⟩ := GlobalTheory.HCFct.exists_interp W hW
        have e : ∀ k, cptRep E b k ((v : V) : Sm E b) =
            ∑ i : s, (bb i).1 k • cptRep E b i.1 ((v : V) : Sm E b) := by
          intro k
          apply Subtype.ext
          funext g
          have := hb _ (hK g) k
          simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          rw [this]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        haveI : FiniteDimensional ℂ
            (Submodule.span ℂ (Set.range fun i : s => cptRep E b i.1 ((v : V) : Sm E b))) :=
          FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
        refine Submodule.finiteDimensional_of_le
          (S₂ := Submodule.span ℂ (Set.range fun i : s => cptRep E b i.1 ((v : V) : Sm E b)))
          (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        show cptRep E b k ((v : V) : Sm E b) ∈ _
        rw [e k]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      refine ⟨⟨hleft, ?_, hkfin, ?_, growth_of_tame htame⟩, hfix, hK, χ, rfl, ?_⟩
      · exact isOpen_stab_of_mem_nhds (finRep E b) _
          (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
      · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {((v : V) : Sm E b)})
          (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        show z _ ∈ _
        rw [hJz v hv z hz]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · intro zs hlen hzs
        obtain ⟨z, rfl⟩ := List.length_eq_one_iff.1 hlen
        simp only [List.foldr_cons, List.foldr_nil]
        rw [hJz v hv z (hzs z (List.mem_singleton_self z)), sub_self]
    haveI := hP L hL W hW {χ} (Set.finite_singleton χ) 1
    let Φ : J →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W {χ} 1) :=
      LinearMap.codRestrict _ (V.subtype.comp J.subtype) fun v => Submodule.subset_span (hmem v.1 v.2)
    have hinj : Function.Injective Φ := fun v v' h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W {χ} 1) => (x : Sm E b)) h))
    exact Module.Finite.of_injective Φ hinj

end GlobalTheory.CapKilled

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFinitenStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameKilledCapelliSpace_finiteDimensional_of_finiteness : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ)) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → (∀ z ∈ Zalg E b, ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q) → FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) := by
  first | exact @GlobalTheory.CapKilled.finiteDimensional_space | exact GlobalTheory.CapKilled.finiteDimensional_space | (intros; apply GlobalTheory.CapKilled.finiteDimensional_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMem
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CapKilled

theorem zalg_mem_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ)
    (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W →
    ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (z : Module.End ℂ (Sm E b)), z ∈ Zalg E b →
    ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q := by
  intro E _ _ _ b L W hW q z hz ψ hψ
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_space.1 hψ
  refine mem_space.2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Zalg_stable (V := leftInv E b) (fun X _ h => lie_mem_leftInv X h) hz ψ h1
  · exact Zalg_stable (V := fixL E b L) (fun X _ h => lie_mem_fixL L X h) hz ψ h2
  · intro g
    obtain ⟨s, c, hc⟩ := GlobalTheory.HCFct.exists_interp W hW
    have hk : ∀ k : Kinf E b, cptRep E b k ψ = ∑ i : s, (c i).1 k • cptRep E b i.1 ψ := by
      intro k
      apply Subtype.ext
      funext h
      have := hc _ (h3 h) k
      rw [this]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    have e : (fun k : Kinf E b => (cptRep E b k (z ψ)).1 g) =
        ∑ i : s, (z (cptRep E b i.1 ψ)).1 g • (c i).1 := by
      funext k
      have hcomm := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E b k z hz) ψ
      simp only [Module.End.mul_apply] at hcomm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hcomm, hk k, map_sum]
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W.sum_mem fun i _ => W.smul_mem _ (c i).2
  · intro τ u
    have hcap : cap (a := b) τ u ∈ Zalg E b := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hp : Polynomial.aeval (cap (a := b) τ u) (q τ u) ∈ Zalg E b := Algebra.adjoin_le (Set.singleton_subset_iff.2 hcap) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    have hcomm := (KilledFin.Zalg_commute hz hp).eq
    have := LinearMap.congr_fun hcomm ψ
    simp only [Module.End.mul_apply] at this
    rw [← this, h4 τ u, map_zero]
  · exact Zalg_stable (V := tame E b) (fun X _ h => lie_mem_tame X h) hz ψ h5

end GlobalTheory.CapKilled
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMemStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInvariantKilledSmoothSpace_centre_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (z : Module.End ℂ (Sm E b)), z ∈ Zalg E b → ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q := by
  first | exact @GlobalTheory.CapKilled.zalg_mem_space | exact GlobalTheory.CapKilled.zalg_mem_space | (intros; apply GlobalTheory.CapKilled.zalg_mem_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSlowlyIncreasingKilledCapelliPo
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth Filter Topology

theorem GlobalTheory.CapKilled.finite_of_finiteness : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ),
    (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ),
      FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) →
    ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ),
      FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) →
      ∃ V : Submodule ℂ (Sm E b), FiniteDimensional ℂ V ∧ ∀ ψ : Sm E b, (∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g) →
        (∀ k ∈ L, finRep E b k ψ = ψ) → (∀ g : GA E b, (fun k : Kinf E b => (cptRep E b k ψ).1 g) ∈ W) →
        (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ.1 (g * infGL E b y)‖ ≤ C * height y ^ N) →
        (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → ψ ∈ V := by
  intro E _ _ _ b hP L hL W hW q hq
  have hfin : FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) :=
    GlobalTheory.T.tameKilledCapelliSpace_finiteDimensional_of_finiteness E b hP (GlobalTheory.T.capelliDet_eq_linearCombination_nat_nodes E b) L hL W hW q hq (GlobalTheory.T.tameInvariantKilledSmoothSpace_centre_mem E b L W hW q)
  refine ⟨GlobalTheory.CapKilled.space E b L W q, hfin, fun ψ h1 h2 h3 h4 h5 => ?_⟩
  let ν : Measure (Lie E b) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E b ν
  let V' : Submodule ℂ (GA E b → ℂ) := (GlobalTheory.CapKilled.space E b L W q).map (Sm E b).subtype
  have hc : IsClosed (V' : Set (GA E b → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hM : ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q :=
    ⟨⟨⟨h1, h2⟩, h3⟩, GlobalTheory.CapKilled.mem_killed.2 h5⟩
  have hmem : ∀ n, smoothing ν (α n) ψ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := GlobalTheory.T.capelliKilled_slowlyIncreasing_smoothing_mem E b ν (α n) (hα n).1 (hα n).2 L W hW q ψ hM h4
    exact ⟨_, hv, rfl⟩
  have hψ : ψ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim ψ.1 ψ.2 g) (Eventually.of_forall hmem)
  obtain ⟨χ, hχ, e⟩ := hψ
  have e' : χ = ψ := Subtype.ext e
  exact e' ▸ hχ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSlowlyIncreasingKilledCapelliPoStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_slowlyIncreasing_killed_capelliPolynomials : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → ∃ V : Submodule ℂ (Sm E b), FiniteDimensional ℂ V ∧ ∀ ψ : Sm E b, (∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g) → (∀ k ∈ L, finRep E b k ψ = ψ) → (∀ g : GA E b, (fun k : Kinf E b => (cptRep E b k ψ).1 g) ∈ W) → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ.1 (g * infGL E b y)‖ ≤ C * height y ^ N) → (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → ψ ∈ V := by
  first | exact @GlobalTheory.CapKilled.finite_of_finiteness | exact GlobalTheory.CapKilled.finite_of_finiteness | (intros; apply GlobalTheory.CapKilled.finite_of_finiteness <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIntegralLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIntegralLeftInvariant
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviConstTerm

theorem setIntegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃ₜ+ G) (hT : ∀ x ∈ Γ, T x ∈ Γ)
    (hT' : ∀ x ∈ Γ, T.symm x ∈ Γ) (h : G → ℂ) (hinv : ∀ (γ : Γ) (x : G), h (γ +ᵥ x) = h x) :
    ∫ x in 𝓕, h (T x) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have key : ∀ U : G ≃ₜ+ G, (∀ x ∈ Γ, U x ∈ Γ) → (∀ x ∈ Γ, U.symm x ∈ Γ) →
      MeasurePreserving U μ μ ∧ IsAddFundamentalDomain Γ (U ⁻¹' 𝓕) μ := by
    intro U hU hU'
    have hmeas : Measurable U := U.continuous.measurable
    haveI : (μ.map U).IsAddHaarMeasure := U.isAddHaarMeasure_map μ
    have hc := Measure.isAddLeftInvariant_eq_smul (μ.map U) μ
    have hq : Measure.QuasiMeasurePreserving U μ μ := ⟨hmeas.aemeasurable, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
    have hS : IsAddFundamentalDomain Γ (U ⁻¹' 𝓕) μ := by
      refine h𝓕.preimage_of_equiv (e := fun γ : Γ => (⟨U.symm γ, hU' _ γ.2⟩ : Γ)) hq ?_ ?_
      · refine ⟨fun x y hxy => Subtype.ext (U.symm.injective (congrArg Subtype.val hxy)), fun y => ⟨⟨U y, hU _ y.2⟩, ?_⟩⟩
        exact Subtype.ext (U.symm_apply_apply _)
      · intro γ x
        change U (U.symm γ + x) = (γ : G) + U x
        rw [map_add (f := _), U.apply_symm_apply]
    refine ⟨⟨hmeas, ?_⟩, hS⟩
    have h2 : μ (U ⁻¹' 𝓕) = 1 := (hS.measure_eq h𝓕).trans h1
    have h3 : μ.map U 𝓕 = 1 := by
      rw [Measure.map_apply₀ hmeas.aemeasurable (h𝓕.nullMeasurableSet.mono_ac hq.2), h2]
    rw [hc, Measure.smul_apply, h1] at h3
    have h4 : (μ.map U).addHaarScalarFactor μ = 1 := by
      simpa [ENNReal.smul_def] using h3
    rw [hc, h4, one_smul]
  have hmp := (key T hT hT').1
  have hS := (key T.symm hT' hT).2
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hpre : T ⁻¹' (T.symm ⁻¹' 𝓕) = 𝓕 := by ext x; simp
  calc ∫ x in 𝓕, h (T x) ∂μ = ∫ x in T ⁻¹' (T.symm ⁻¹' 𝓕), h (T x) ∂μ := by rw [hpre]
    _ = ∫ x in T.symm ⁻¹' 𝓕, h x ∂μ := hmp.setIntegral_preimage_emb hemb h _
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

variable {R : Type} [CommRing R] {a r : ℕ}

def IsBlockSL2Embedding (r : ℕ) (m : Matrix (Fin a) (Fin a) R) : Prop :=
  ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m i j = 0

def conjN (m n : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (m * nilM x * n) p.1.1 p.1.2

theorem nilM_conjN {m n : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) (hn : IsBlockSL2Embedding r n) (x : BlockIx a r → R) :
    nilM (conjN m n x) = m * nilM x * n := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simp only [nilM, Matrix.of_apply, dif_pos h]; rfl
  · rw [nilM, Matrix.of_apply, dite_eq_right h, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rcases hn k j with h1 | h1
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro l _
      rcases hm i l with h2 | h2
      · rw [nilM, Matrix.of_apply, dite_eq_right (fun h' => h (by omega)), mul_zero]
      · rw [h2, zero_mul]
    · rw [h1, mul_zero]

theorem nilM_add (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem conjN_add (m n : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    conjN m n (x + y) = conjN m n x + conjN m n y := by
  funext p
  simp only [conjN, nilM_add, mul_add, add_mul, Matrix.add_apply, Pi.add_apply]

theorem conjN_conjN {m n m' n' : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) (hn : IsBlockSL2Embedding r n)
    (h1 : m' * m = 1) (h2 : n * n' = 1) (x : BlockIx a r → R) : conjN m' n' (conjN m n x) = x := by
  funext p
  have : m' * (m * nilM x * n) * n' = nilM x := by
    rw [show m' * (m * nilM x * n) * n' = (m' * m) * nilM x * (n * n') by simp only [mul_assoc], h1, h2, one_mul,
      mul_one]
  rw [conjN, nilM_conjN hm hn, this, nilM, Matrix.of_apply, dif_pos p.2]

theorem continuous_conjN [TopologicalSpace R] [IsTopologicalRing R] (m n : Matrix (Fin a) (Fin a) R) :
    Continuous (conjN (r := r) m n) := by
  have h : Continuous (nilM : (BlockIx a r → R) → Matrix (Fin a) (Fin a) R) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine continuous_pi fun p => ?_
  exact ((continuous_const.matrix_mul h).matrix_mul continuous_const).matrix_elem _ _

theorem conjN_map {S : Type} [CommRing S] (φ : R →+* S) (m n : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) :
    conjN (m.map φ) (n.map φ) (fun p => φ (x p)) = fun p => φ (conjN m n x p) := by
  have : nilM (fun p => φ (x p)) = (nilM x).map φ := by
    ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp
  funext p
  rw [conjN, conjN, this, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

theorem IsBlockSL2Embedding.map {S : Type} [CommRing S] (φ : R →+* S) {m : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) :
    IsBlockSL2Embedding r (m.map φ) := fun i j => (hm i j).imp id fun h => by rw [Matrix.map_apply, h, map_zero]

theorem unip_mul (m : GL (Fin a) R) (hm : IsBlockSL2Embedding r m.val) (hm' : IsBlockSL2Embedding r m⁻¹.val) (x : BlockIx a r → R) :
    unip x * m = m * unip (conjN m⁻¹.val m.val x) := by
  apply Units.ext
  change (1 + nilM x) * m.val = m.val * (1 + nilM (conjN m⁻¹.val m.val x))
  rw [nilM_conjN hm' hm, mul_add, add_mul, one_mul, mul_one, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

theorem constTerm_levi_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (γ : GL (Fin r) E × GL (Fin (a - r)) E) (g : GA E a), ∫ x in 𝓕, f (unip x * (ratGL E a (GlobalTheory.LeviGA.blkGL hr γ) * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 f hf γ g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  obtain ⟨m, hm⟩ : ∃ m, m = GlobalTheory.LeviGA.blkGL hr γ := ⟨_, rfl⟩
  have hb : IsBlockSL2Embedding r m.val := hm ▸ GlobalTheory.LeviGA.blkGL_block hr γ
  have hb' : IsBlockSL2Embedding r m⁻¹.val := by
    rw [hm, ← map_inv]; exact GlobalTheory.LeviGA.blkGL_block hr γ⁻¹
  rw [← hm]
  have e1 : (ratGL E a m).val = m.val.map (algebraMap E (Ad E)) := rfl
  have e2 : (ratGL E a m)⁻¹.val = m⁻¹.val.map (algebraMap E (Ad E)) := rfl
  have hB : IsBlockSL2Embedding r (ratGL E a m).val := e1 ▸ hb.map _
  have hB' : IsBlockSL2Embedding r (ratGL E a m)⁻¹.val := e2 ▸ hb'.map _
  let T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := conjN (ratGL E a m)⁻¹.val (ratGL E a m).val
      invFun := conjN (ratGL E a m).val (ratGL E a m)⁻¹.val
      left_inv := conjN_conjN hB' hB (Units.mul_inv _) (Units.mul_inv _)
      right_inv := conjN_conjN hB hB' (Units.inv_mul _) (Units.inv_mul _)
      map_add' := conjN_add _ _
      continuous_toFun := continuous_conjN _ _
      continuous_invFun := continuous_conjN _ _ }
  have hL : ∀ x, f (unip x * (ratGL E a m * g)) = h (T x) := fun x => by
    rw [← mul_assoc, unip_mul _ hB hB', mul_assoc, hf]; rfl
  simp_rw [hL]
  refine setIntegral_comp_aut (ratN E a r) μ 𝓕 h𝓕 h1 T ?_ ?_ h hinv
  · rintro _ ⟨e, rfl⟩
    exact ⟨conjN m⁻¹.val m.val e, (conjN_map (algebraMap E (Ad E)) _ _ e).symm⟩
  · rintro _ ⟨e, rfl⟩
    exact ⟨conjN m.val m⁻¹.val e, (conjN_map (algebraMap E (Ad E)) _ _ e).symm⟩

end GlobalTheory.LeviConstTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIntegralLeftInvariantStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_integral_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (γ : GL (Fin r) E × GL (Fin (a - r)) E) (g : GA E a), ∫ x in 𝓕, f (unip x * (ratGL E a (GlobalTheory.LeviGA.blkGL hr γ) * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  first | exact @GlobalTheory.LeviConstTerm.constTerm_levi_invariant | exact GlobalTheory.LeviConstTerm.constTerm_levi_invariant | (intros; apply GlobalTheory.LeviConstTerm.constTerm_levi_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevel
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA GlobalTheory.AutGrowth Polynomial
open Formalism.REAL (qdet)

namespace GlobalTheory.GLSlice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ}

theorem qdet_eq_cap (τ : E →+* ℂ) (u : ℂ) : qdet (Eop (a := a) τ) u = cap τ (u - ((a : ℂ) - 1) / 2) := by
  rw [cap, sub_add_cancel]

theorem commute_aeval_rt (τ : E →+* ℂ) (u : ℂ) (P : ℂ[X]) (h : GA E a) :
    Commute (aeval (qdet (Eop (a := a) τ) u) P) (rt E a h) := by
  have h1 : Commute (qdet (Eop (a := a) τ) u) (rt E a h) := by
    rw [qdet_eq_cap, ← infGL_mul_finGL h, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ _ _).mul_right (commute_cap_finRep τ _ _)
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left _ _).mul_left (h1.pow_left n)

theorem isOpen_stab {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (h : ∀ k ∈ L, finRep E a k φ = φ) : IsOpen {k | finRep E a k φ = φ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hL.mem_nhds L.one_mem) h)

theorem lie_left {φ : Sm E a} {n : GA E a} (h : ∀ g, φ.1 (n * g) = φ.1 g) (X : Lie E a) (g : GA E a) :
    (lie E a X φ).1 (n * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (n * g) = chart φ.1 g := by
    funext x; simp only [chart, mul_assoc, h]
  rw [lie_apply, lie_apply, lieD, lieD, e]

theorem span_props (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ))
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} (hX : X.Finite) (N : ℕ) :
    ∃ Q : (E →+* ℂ) → ℂ → ℂ[X], (∀ τ u, Q τ u ≠ 0) ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N),
      (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧ φ.1 ∈ growth E a ∧
        ∀ τ u, aeval (qdet (Eop (a := a) τ) u) (Q τ u) φ = 0 := by
  refine ⟨fun τ u => ∏ χ ∈ hX.toFinset, (Polynomial.X - C (χ (qdet (Eop τ) u))) ^ N,
    fun τ u => Finset.prod_ne_zero_iff.2 fun χ _ => pow_ne_zero _ (X_sub_C_ne_zero _), fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨h1, h2, -, χ, hχ, h3⟩ := hφ
    refine ⟨h1.left, h2, h1.growth, fun τ u => ?_⟩
    beta_reduce
    generalize hz : qdet (Eop (a := a) τ) u = z
    have hzZ : z ∈ Zalg E a := by
      rw [← hz, qdet_eq_cap]; exact Algebra.subset_adjoin ⟨τ, _, rfl⟩
    have key : ∀ n : ℕ, (List.replicate n z).foldr (fun z f => z f - χ z • f) φ =
        aeval z ((Polynomial.X - C (χ z)) ^ n) φ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, map_sub, aeval_X, aeval_C]
        rfl
    have h4 := h3 (List.replicate N z) List.length_replicate fun y hy => (List.eq_of_mem_replicate hy) ▸ hzZ
    obtain ⟨R, hR⟩ := Finset.dvd_prod_of_mem (fun χ : Module.End ℂ (Sm E a) → ℂ => (Polynomial.X - C (χ z)) ^ N)
      (hX.mem_toFinset.2 hχ)
    rw [hR, mul_comm, map_mul, Module.End.mul_apply, ← key, h4, map_zero]
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => map_zero _, zero_mem _, fun _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    exact ⟨fun γ g => congrArg₂ (· + ·) (hx.1 γ g) (hy.1 γ g), fun k hk => by rw [map_add (f := _), hx.2.1 k hk, hy.2.1 k hk],
      add_mem hx.2.2.1 hy.2.2.1, fun τ u => by rw [map_add (f := _), hx.2.2.2, hy.2.2.2, add_zero]⟩
  | smul c x _ hx =>
    exact ⟨fun γ g => congrArg (c * ·) (hx.1 γ g), fun k hk => by rw [map_smul, hx.2.1 k hk],
      Submodule.smul_mem _ c hx.2.2.1, fun τ u => by rw [map_smul, hx.2.2.2, smul_zero]⟩

theorem exists_constTerm {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {r : ℕ}
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] {μ : Measure (BlockIx a r → Ad E)}
    {𝓕 : Set (BlockIx a r → Ad E)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (φ : Sm E a) (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) (hf : ∀ k ∈ L, finRep E a k φ = φ) :
    ∃ ψ : Sm E a, (∀ g, ψ.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∧
      ∀ τ u (P : ℂ[X]), aeval (qdet (Eop (a := a) τ) u) P φ = 0 → aeval (qdet (Eop (a := a) τ) u) P ψ = 0 := by
  let Γ : Submodule ℂ (Sm E a × Sm E a) :=
    { carrier := {x | (∀ γ g, x.1.1 (ratGL E a γ * g) = x.1.1 g) ∧ (∀ k ∈ L, finRep E a k x.1 = x.1) ∧
        ∀ g, x.2.1 g = ∫ y in 𝓕, x.1.1 (unip y * g) ∂μ}
      zero_mem' := ⟨fun _ _ => rfl, fun _ _ => map_zero _, fun _ => (integral_zero _ _).symm⟩
      add_mem' := fun {x y} hx hy => ⟨fun γ g => congrArg₂ (· + ·) (hx.1 γ g) (hy.1 γ g),
        fun k hk => (map_add _ _ _).trans (congrArg₂ (· + ·) (hx.2.1 k hk) (hy.2.1 k hk)), fun g =>
          (congrArg₂ (· + ·) (hx.2.2 g) (hy.2.2 g)).trans (integral_add
            (CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E a _ (isOpen_stab hL hx.2.1)) hx.1 μ h𝓕 g)
            (CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E a _ (isOpen_stab hL hy.2.1)) hy.1 μ h𝓕 g)).symm⟩
      smul_mem' := fun c x hx => ⟨fun γ g => congrArg (c * ·) (hx.1 γ g),
        fun k hk => (map_smul _ _ _).trans (congrArg (c • ·) (hx.2.1 k hk)), fun g =>
          (congrArg (c * ·) (hx.2.2 g)).trans (integral_const_mul c _).symm⟩ }
  have hlie : ∀ X, ∀ x ∈ Γ, (lie E a X x.1, lie E a X x.2) ∈ Γ := fun X x hx => by
    refine ⟨fun γ g => lie_left (hx.1 γ) X g, fun k hk => ?_, fun g => ?_⟩
    · exact (LinearMap.congr_fun (lie_rt_fin X k) x.1).symm.trans (congrArg (lie E a X) (hx.2.1 k hk))
    · change lieD X x.2.1 g = _
      rw [funext hx.2.2]
      exact (GlobalTheory.T.constant_term_automorphic_form_integral E a r μ 𝓕 hμ h𝓕 h1 x.1 hx.1 (isOpen_stab hL hx.2.1)).2 X g
  refine ⟨⟨_, (GlobalTheory.T.constant_term_automorphic_form_integral E a r μ 𝓕 hμ h𝓕 h1 φ hl (isOpen_stab hL hf)).1⟩, fun _ => rfl, fun τ u P hP => ?_⟩
  have h := rel_aeval_qdet Γ (Eop τ) (Eop τ)
    (fun i j x hx => Γ.smul_mem (1 / 2 : ℂ) (Γ.sub_mem (hlie _ x hx) (Γ.smul_mem Complex.I (hlie _ x hx)))) u P
    (φ, ⟨_, (GlobalTheory.T.constant_term_automorphic_form_integral E a r μ 𝓕 hμ h𝓕 h1 φ hl (isOpen_stab hL hf)).1⟩) ⟨hl, hf, fun _ => rfl⟩
  refine Subtype.ext (funext fun g => (h.2.2 g).trans ?_)
  simp only [hP]
  exact integral_zero _ _

theorem infGL_unip {r : ℕ} (x : BlockIx a r → Cinf E) : infGL E a (unip x) = unip fun p => sInf E (x p) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
    sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + nilM x i j) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j + nilM (fun p => sInf E (x p)) i j
  rw [map_add (f := _), ← add_assoc, sub_add_cancel]
  simp only [nilM, Matrix.of_apply]
  split_ifs <;> simp

theorem lieS_upper {r : ℕ} (hr : r ≤ a) {ψ : Sm E a} (h : ∀ (y : BlockIx a r → Ad E) g, ψ.1 (unip y * g) = ψ.1 g)
    {i j : Fin a} (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) (z : Cinf E) (p : GA E r × GA E (a - r)) :
    (lieS E a i j z ψ).1 (blkGL hr p) = 0 := by
  classical
  let x : BlockIx a r → Cinf E := Pi.single ⟨(i, j), hi, hj⟩ z
  have e : ∀ t : ℝ, toL (unip (t • x)).val = oneL E a + t • toL (Matrix.single i j z) := fun t => by
    ext i' j' : 2
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) i' j' + nilM (t • x) i' j' =
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i' j' + t • Matrix.single i j z i' j'
    congr 1
    simp only [nilM, Matrix.of_apply, Matrix.single_apply, x, Pi.smul_apply, Pi.single_apply, Subtype.mk.injEq,
      Prod.mk.injEq]
    by_cases hh : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hh
      simp [hi, hj]
    · rw [if_neg hh, smul_zero]
      split_ifs with h1 h2
      · exact absurd ⟨h2.1.symm, h2.2.symm⟩ hh
      · simp
      · rfl
  have hd := hasDerivAt_curve ψ (blkGL hr p) (fun t => unip (t • x)) (toL (Matrix.single i j z))
    (Units.ext (by simpa using e 0)) (by
      simp only [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single i j z))).const_add (oneL E a))
  have e2 : (fun t : ℝ => ψ.1 (blkGL hr p * infGL E a (unip (t • x)))) = fun _ => ψ.1 (blkGL hr p) := by
    funext t
    obtain ⟨y', hy'⟩ := blkGL_mul_unip hr p fun q => sInf E ((t • x) q)
    rw [infGL_unip, hy', h]
  rw [e2] at hd
  exact hd.unique (hasDerivAt_const _ _)

theorem exists_block_poly {r : ℕ} (hr : r ≤ a) (Q : (E →+* ℂ) → ℂ → ℂ[X]) (hQ : ∀ τ u, Q τ u ≠ 0) :
    ∃ q : (E →+* ℂ) → ℂ → ℂ[X], (∀ τ u, q τ u ≠ 0) ∧ ∀ ψ : Sm E a,
      (∀ (y : BlockIx a r → Ad E) g, ψ.1 (unip y * g) = ψ.1 g) →
      (∀ τ u, aeval (qdet (Eop (a := a) τ) u) (Q τ u) ψ = 0) → ∀ τ u p,
        (aeval (qdet (fun i j : Fin r => Eop (a := a) τ (fstIx hr i) (fstIx hr j)) u) (q τ u) ψ).1 (blkGL hr p) = 0 ∧
        (aeval (qdet (fun i j : Fin (a - r) => Eop (a := a) τ (sndIx hr i) (sndIx hr j)) u) (q τ u) ψ).1
          (blkGL hr p) = 0 := by
  let M' : Submodule ℂ (Sm E a) :=
    { carrier := {ψ | ∀ (y : BlockIx a r → Ad E) g, ψ.1 (unip y * g) = ψ.1 g}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun hx hy y g => congrArg₂ (· + ·) (hx y g) (hy y g)
      smul_mem' := fun c _ hx y g => congrArg (c * ·) (hx y g) }
  let K : Submodule ℂ (Sm E a) :=
    { carrier := {ψ | ∀ p : GA E r × GA E (a - r), ψ.1 (blkGL hr p) = 0}
      zero_mem' := fun _ => rfl
      add_mem' := fun hx hy p => (congrArg₂ (· + ·) (hx p) (hy p)).trans (add_zero _)
      smul_mem' := fun c _ hx p => (congrArg (c * ·) (hx p)).trans (mul_zero _) }
  have hM : ∀ X, ∀ ψ ∈ M', lie E a X ψ ∈ M' := fun X ψ hψ y g => lie_left (hψ y) X g
  have key := fun τ : E →+* ℂ => GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks (Sm E a) a r hr (Eop τ) (glRel_Eop τ) M' K
    (fun i j x hx => M'.smul_mem (1 / 2 : ℂ) (M'.sub_mem (hM _ x hx) (M'.smul_mem Complex.I (hM _ x hx))))
    (fun i j hi hj x hx => K.smul_mem (1 / 2 : ℂ) (K.sub_mem (lieS_upper hr hx hi hj _)
      (K.smul_mem Complex.I (lieS_upper hr hx hi hj _))))
    (fun i j hij x hx p => by
      obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
      obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
      obtain ⟨m₁, m₂⟩ := p
      rcases i with i | i <;> rcases j with j | j
      · have h0 : slice (fstIx hr) (blkGL hr (1, m₂)) x = 0 :=
          Subtype.ext (funext fun m => by rw [slice_apply, ← blkGL_eq_fst]; exact hx _)
        have h1 := Eop_slice (fstIx hr) (blkGL hr (1, m₂)) x τ i j
        rw [h0, map_zero] at h1
        rw [blkGL_eq_fst]
        exact (congrFun (congrArg Subtype.val h1) m₁).symm
      · simp at hij
      · simp at hij
      · have h0 : slice (sndIx hr) (blkGL hr (m₁, 1)) x = 0 :=
          Subtype.ext (funext fun m => by rw [slice_apply, ← blkGL_eq_snd]; exact hx _)
        have h1 := Eop_slice (sndIx hr) (blkGL hr (m₁, 1)) x τ i j
        rw [h0, map_zero] at h1
        rw [blkGL_eq_snd]
        exact (congrFun (congrArg Subtype.val h1) m₂).symm) (Q τ) (hQ τ)
  choose q hq0 hq using key
  exact ⟨q, hq0, fun ψ h1 h2 τ u p => ⟨(hq τ ψ h1 (h2 τ) u).1 p, (hq τ ψ h1 (h2 τ) u).2 p⟩⟩

theorem exists_translated {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Submodule ℂ (Kinf E a → ℂ)} (hW : FiniteDimensional ℂ W) {X : Set (Module.End ℂ (Sm E a) → ℂ)} (hX : X.Finite)
    (N : ℕ) {r : ℕ} (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {μ : Measure (BlockIx a r → Ad E)} {𝓕 : Set (BlockIx a r → Ad E)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (h1 : μ 𝓕 = 1) (t : GL (Fin a) (Af E)) (κ : Kinf E a) :
    ∃ (L' : Subgroup (GL (Fin a) (Af E))) (W' : Submodule ℂ (Kinf E a → ℂ)) (q : (E →+* ℂ) → ℂ → ℂ[X]),
      IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ FiniteDimensional ℂ W' ∧ (∀ τ u, q τ u ≠ 0) ∧
      ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∃ ψ : Sm E a,
        (∀ g, ψ.1 g = ∫ x in 𝓕, φ.1 (unip x * (g * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∧
        (∀ γ g, ψ.1 (ratGL E a (blkGL hr γ) * g) = ψ.1 g) ∧ (∀ k ∈ L', finRep E a k ψ = ψ) ∧
        (∀ g, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W') ∧ ψ.1 ∈ growth E a ∧ ∀ τ u p,
        (aeval (qdet (fun i j : Fin r => Eop (a := a) τ (fstIx hr i) (fstIx hr j)) u) (q τ u) ψ).1 (blkGL hr p) = 0 ∧
        (aeval (qdet (fun i j : Fin (a - r) => Eop (a := a) τ (sndIx hr i) (sndIx hr j)) u) (q τ u) ψ).1
          (blkGL hr p) = 0 := by
  obtain ⟨Q, hQ0, hQ⟩ := span_props L W hX N
  obtain ⟨q, hq0, hq⟩ := exists_block_poly hr Q hQ0
  refine ⟨L.comap (MulAut.conj t⁻¹).toMonoidHom, W.map (LinearMap.funLeft ℂ ℂ fun k => κ⁻¹ * k * κ), q,
    hL.preimage (f := fun k => t⁻¹ * k * t⁻¹⁻¹) ((continuous_const.mul continuous_id).mul continuous_const),
    inferInstance, hq0, fun φ hφ => ?_⟩
  obtain ⟨hl, hf, hg, hz⟩ := hQ φ hφ
  obtain ⟨c, hc, hcz⟩ := exists_constTerm hL hμ h𝓕 h1 φ hl hf
  let ψ : Sm E a := rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) c
  have hψ : ∀ g, ψ.1 g = c.1 (g * (finGL E a t * infGL E a (Unitary.toUnits κ))) := fun _ => rfl
  refine ⟨ψ, fun g => by rw [hψ, hc, mul_assoc g], fun γ g => ?_, fun k hk => ?_, fun g => ?_, ?_, hq ψ ?_ ?_⟩
  · rw [hψ, hψ, hc, hc, mul_assoc]
    exact GlobalTheory.T.constant_term_integral_left_invariant E a r hr μ 𝓕 hμ h𝓕 h1 φ.1 hl γ _
  · refine Subtype.ext (funext fun g => ?_)
    have hk' : t⁻¹ * k * t⁻¹⁻¹ ∈ L := hk
    have e : g * finGL E a k * (finGL E a t * infGL E a (Unitary.toUnits κ)) =
        g * (finGL E a t * infGL E a (Unitary.toUnits κ)) * finGL E a (t⁻¹ * k * t⁻¹⁻¹) := by
      have e' : k * t = t * (t⁻¹ * k * t⁻¹⁻¹) := by group
      rw [mul_assoc g, mul_assoc g, mul_assoc (finGL E a t), infGL_comm, ← mul_assoc (finGL E a k),
        ← mul_assoc (finGL E a t), ← map_mul, ← map_mul, e']
    change ψ.1 (g * finGL E a k) = _
    rw [hψ, hψ, hc, hc, e]
    refine integral_congr_ae (.of_forall fun x => ?_)
    beta_reduce
    rw [← mul_assoc]
    exact congrFun (congrArg Subtype.val (hf _ hk')) _
  · refine ⟨_, GlobalTheory.HCFct.constTerm_cptTranslate_mem E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ hφ
      (g * (finGL E a t * infGL E a (Unitary.toUnits κ))), funext fun k => ?_⟩
    change _ = ψ.1 (g * infGL E a (Unitary.toUnits k))
    have e : g * infGL E a (Unitary.toUnits k) * (finGL E a t * infGL E a (Unitary.toUnits κ)) =
        g * (finGL E a t * infGL E a (Unitary.toUnits κ)) * infGL E a (Unitary.toUnits (κ⁻¹ * k * κ)) := by
      have e' : k * κ = κ * (κ⁻¹ * k * κ) := by group
      rw [mul_assoc g, mul_assoc g, ← mul_assoc (infGL E a _), infGL_comm, mul_assoc (finGL E a t),
        mul_assoc (finGL E a t), ← map_mul, ← map_mul, ← map_mul, ← map_mul, e']
    rw [hψ, hc, e]
    rfl
  · have g1 : c.1 ∈ growth E a := fun g => by
      simp only [hc]
      exact GlobalTheory.T.constant_term_moderate_growth E a r μ 𝓕 hμ h𝓕 h1 φ hl (isOpen_stab hL hf) hg g
    have g2 := SmoothFinite.growth_cptRep g1 κ
    intro g
    obtain ⟨C, n, h⟩ := g2 (g * finGL E a t)
    refine ⟨C, n, fun y => ?_⟩
    rw [hψ, ← mul_assoc, mul_assoc g, infGL_comm, ← mul_assoc]
    exact h y
  · intro y g
    rw [hψ, hψ, hc, hc, mul_assoc]
    exact constTerm_unip_invariant E a r μ 𝓕 hμ h𝓕 φ.1 hl y _
  · intro τ u
    rw [← Module.End.mul_apply, (commute_aeval_rt τ u _ _).eq, Module.End.mul_apply, hcz τ u _ (hz τ u), map_zero]

theorem exists_slice_space (f : Fin b ↪ Fin a)
    (hb : ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) →
      ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite →
      ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N)))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Submodule ℂ (Kinf E a → ℂ)} (hW : FiniteDimensional ℂ W) (q : (E →+* ℂ) → ℂ → ℂ[X]) (hq : ∀ τ u, q τ u ≠ 0) :
    ∃ V : Submodule ℂ (GA E b → ℂ), FiniteDimensional ℂ V ∧ ∀ (ψ : Sm E a) (g : GA E a),
      (∀ γ m, ψ.1 (g * embGL f (ratGL E b γ * m)) = ψ.1 (g * embGL f m)) → (∀ k ∈ L, finRep E a k ψ = ψ) →
      (∀ g, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W) → ψ.1 ∈ growth E a →
      (∀ τ u m, (aeval (qdet (fun i j : Fin b => Eop (a := a) τ (f i) (f j)) u) (q τ u) ψ).1 (g * embGL f m) = 0) →
      (fun m => ψ.1 (g * embGL f m)) ∈ V := by
  obtain ⟨V, hV, h⟩ := GlobalTheory.T.finiteDimensional_slowlyIncreasing_killed_capelliPolynomials E b hb (L.comap (embGL f)) (hL.preimage (continuous_embGL f))
    (W.map (LinearMap.funLeft ℂ ℂ (embK f))) inferInstance (fun τ u => q τ (u + ((b : ℂ) - 1) / 2)) fun τ u => hq τ _
  refine ⟨V.map (Sm E b).subtype, inferInstance, fun ψ g h1 h2 h3 h4 h5 =>
    ⟨slice f g ψ, h _ h1 (fun k hk => ?_) (fun m => ?_) (growth_slice f g ψ h4) fun τ u => ?_, rfl⟩⟩
  · refine Subtype.ext (funext fun m => ?_)
    change ψ.1 (g * embGL f (m * finGL E b k)) = ψ.1 (g * embGL f m)
    rw [map_mul, embGL_finGL, ← mul_assoc]
    exact congrFun (congrArg Subtype.val (h2 _ hk)) _
  · refine ⟨_, h3 (g * embGL f m), funext fun k => ?_⟩
    change ψ.1 (g * embGL f m * infGL E a (Unitary.toUnits (embK f k))) =
      ψ.1 (g * embGL f (m * infGL E b (Unitary.toUnits k)))
    rw [map_mul, embGL_infGL, toUnits_embK, mul_assoc]
  · rw [cap, aeval_qdet_slice]
    exact Subtype.ext (funext fun m => h5 τ _ m)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem ratGL_blkGL {r : ℕ} (hr : r ≤ a) (γ : GL (Fin r) E × GL (Fin (a - r)) E) :
    ratGL E a (blkGL hr γ) = blkGL hr (ratGL E r γ.1, ratGL E (a - r) γ.2) :=
  map_blkGL hr (algebraMap E (Ad E)) γ

theorem slice_fst : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₁ : Submodule ℂ (GA E r → ℂ), FiniteDimensional ℂ V₁ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₂ : GA E (a - r), (fun m₁ : GA E r => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₁ := by
  intro E _ _ _ a hind L hL W hW X hX N r _ hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨L', W', q, hL', hW', hq, h⟩ := exists_translated hL hW hX N hr.le hμ h𝓕 h1 t κ
  obtain ⟨V, hV, hs⟩ := exists_slice_space (fstIx hr.le) (hind r hr) hL' hW' q hq
  refine ⟨V, hV, fun φ hφ m₂ => ?_⟩
  obtain ⟨ψ, e, h2, h3, h4, h5, h6⟩ := h φ hφ
  have := hs ψ (blkGL hr.le (1, m₂)) (fun γ m => by
    rw [← blkGL_eq_fst, ← blkGL_eq_fst, ← h2 (γ, 1) (blkGL hr.le (m, m₂)), ratGL_blkGL, ← map_mul]
    simp) h3 h4 h5 fun τ u m => by rw [← blkGL_eq_fst]; exact (h6 τ u _).1
  simpa only [← blkGL_eq_fst, e] using this

end GlobalTheory.GLSlice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_gl_of_open_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₁ : Submodule ℂ (GA E r → ℂ), FiniteDimensional ℂ V₁ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₂ : GA E (a - r), (fun m₁ : GA E r => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₁ := by
  first | exact @GlobalTheory.GLSlice.slice_fst | exact GlobalTheory.GLSlice.slice_fst | (intros; apply GlobalTheory.GLSlice.slice_fst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalAutomorphicFormsGL
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviCT

theorem exists_finset_eq_zero {K : Type} (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] :
    ∃ s : Finset K, ∀ w ∈ V, (∀ k ∈ s, w k = 0) → w = 0 := by
  classical
  let ev : K → (V →ₗ[ℂ] ℂ) := fun k => (LinearMap.proj k).comp V.subtype
  let f : Finset K → Submodule ℂ V := fun s => ⨅ k ∈ s, LinearMap.ker (ev k)
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min (Set.range f) ⟨_, ⟨∅, rfl⟩⟩
  have hle : ∀ k, f s ≤ LinearMap.ker (ev k) := fun k => by
    by_contra hk
    refine hmin (f (insert k s)) ⟨_, rfl⟩ (lt_of_le_of_ne ?_ fun heq => hk ?_)
    · exact le_iInf₂ fun j hj => iInf₂_le j (Finset.mem_insert_of_mem hj)
    · rw [← heq]; exact iInf₂_le k (Finset.mem_insert_self _ _)
  refine ⟨s, fun w hw h0 => funext fun k => ?_⟩
  have hmem : (⟨w, hw⟩ : V) ∈ f s := by
    simp only [f, Submodule.mem_iInf]
    intro j hj
    exact h0 j hj
  exact hle k hmem

def slices {M₁ M₂ : Type} (V₁ : Submodule ℂ (M₁ → ℂ)) (V₂ : Submodule ℂ (M₂ → ℂ)) : Submodule ℂ (M₁ × M₂ → ℂ) where
  carrier := {F | (∀ m₂, (fun m₁ => F (m₁, m₂)) ∈ V₁) ∧ ∀ m₁, (fun m₂ => F (m₁, m₂)) ∈ V₂}
  add_mem' ha hb := ⟨fun m₂ => V₁.add_mem (ha.1 m₂) (hb.1 m₂), fun m₁ => V₂.add_mem (ha.2 m₁) (hb.2 m₁)⟩
  zero_mem' := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
  smul_mem' c _ hF := ⟨fun m₂ => V₁.smul_mem c (hF.1 m₂), fun m₁ => V₂.smul_mem c (hF.2 m₁)⟩

theorem finiteDimensional_slices {M₁ M₂ : Type} (V₁ : Submodule ℂ (M₁ → ℂ)) (V₂ : Submodule ℂ (M₂ → ℂ))
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] : FiniteDimensional ℂ (slices V₁ V₂) := by
  obtain ⟨s, hs⟩ := exists_finset_eq_zero V₂
  let T : slices V₁ V₂ →ₗ[ℂ] (s → V₁) :=
    { toFun := fun F j => ⟨fun m₁ => F.1 (m₁, j.1), F.2.1 j.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T fun F G hFG => Subtype.ext (funext fun p => ?_)
  have h := hs (fun m₂ => F.1 (p.1, m₂) - G.1 (p.1, m₂)) (V₂.sub_mem (F.2.2 p.1) (G.2.2 p.1)) fun k hk => by
    have := congrArg (fun u : s → V₁ => (u ⟨k, hk⟩).1 p.1) hFG
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, sub_self]
  exact sub_eq_zero.1 (congrFun h p.2)

end GlobalTheory.LeviCT


open GlobalTheory.LeviCT in
theorem GlobalTheory.LeviCT.finiteDimensional_levi : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) => fun m : {m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)} => ∫ x in 𝓕, φ.1.1 (unip x * (m.1 * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ)) := by
  intro E _ _ _ a hind L hL W hW X hX N r h0 hra _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨V₁, hV₁, h₁⟩ := GlobalTheory.T.finiteDimensional_forms_gl_of_open_level E a hind L hL W hW X hX N r h0 hra μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨V₂, hV₂, h₂⟩ := GlobalTheory.T.finiteDimensional_forms_gl_of_open_level_induction E a hind L hL W hW X hX N r h0 hra μ 𝓕 hμ h𝓕 h1 t κ
  let blocks : {m : GA E a // ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0} → GA E r × GA E (a - r) :=
    fun m => Classical.choose (GlobalTheory.LeviGA.exists_blkGL hra.le m.1 m.2)
  have hb : ∀ m, GlobalTheory.LeviGA.blkGL hra.le (blocks m) = m.1 := fun m =>
    Classical.choose_spec (GlobalTheory.LeviGA.exists_blkGL hra.le m.1 m.2)
  haveI := finiteDimensional_slices V₁ V₂
  refine Submodule.finiteDimensional_of_le (S₂ := (slices V₁ V₂).map (LinearMap.funLeft ℂ ℂ blocks))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ, rfl⟩
  refine ⟨fun p => ∫ x in 𝓕, φ.1.1 (unip x * (GlobalTheory.LeviGA.blkGL hra.le p * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ,
    ⟨fun m₂ => h₁ φ.1 φ.2 m₂, fun m₁ => h₂ φ.1 φ.2 m₁⟩, ?_⟩
  funext m
  simp only [LinearMap.funLeft_apply, hb]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalAutomorphicFormsGLStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_automorphic_forms_GL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) => fun m : {m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)} => ∫ x in 𝓕, φ.1.1 (unip x * (m.1 * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ)) := by
  first | exact @GlobalTheory.LeviCT.finiteDimensional_levi | exact GlobalTheory.LeviCT.finiteDimensional_levi | (intros; apply GlobalTheory.LeviCT.finiteDimensional_levi <;> assumption)
end

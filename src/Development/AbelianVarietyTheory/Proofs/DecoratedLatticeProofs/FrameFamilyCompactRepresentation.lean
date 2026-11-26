module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameFamilyCompactRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanSeparately
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory

theorem exists_finset_eval_injective {Z : Type} (T : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ T] :
    ∃ Y : Finset Z, ∀ g ∈ T, (∀ y ∈ Y, g y = 0) → g = 0 := by
  classical
  let φ : Z → Module.Dual ℂ T := fun z => (LinearMap.proj z).comp T.subtype
  have hfg : (Submodule.span ℂ (Set.range φ)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs', hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [← Set.image_univ] at hs'
  obtain ⟨Y, -, rfl⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨Y, fun g hg hY => ?_⟩
  have hle : Submodule.span ℂ (Set.range φ) ≤ LinearMap.ker (Module.Dual.eval ℂ T ⟨g, hg⟩) := by
    rw [hspan, Submodule.span_le]
    intro ψ hψ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    simp [φ, hY y hy]
  funext z
  have hz := hle (Submodule.subset_span ⟨z, rfl⟩)
  simpa [φ] using hz

theorem finiteDimensional_span_separately (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type)
    (S : ∀ i, Submodule ℂ (X i → ℂ)) (hS : ∀ i, FiniteDimensional ℂ (S i)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}) := by
  classical
  choose Y hY using fun i => @exists_finset_eval_injective (X i) (S i) (hS i)
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}
      add_mem' := fun {f g} hf hg i x => (S i).add_mem (hf i x) (hg i x)
      zero_mem' := fun i x => (S i).zero_mem
      smul_mem' := fun c f hf i x => (S i).smul_mem c (hf i x) }
  have hle : Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i} ≤ P :=
    Submodule.span_le.2 fun f hf => hf
  let L : P →ₗ[ℂ] ((∀ i, Y i) → ℂ) :=
    { toFun := fun f y => (f : (∀ i, X i) → ℂ) (fun i => (y i : X i))
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfP : ∀ i x, (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) ∈ S i := f.2
    have key : ∀ A : Finset ι, ∀ x : ∀ i, X i, (∀ j ∉ A, x j ∈ Y j) →
        (f : (∀ i, X i) → ℂ) x = 0 := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro x hx
        have h0 := congrFun hf (fun j => ⟨x j, hx j (by simp)⟩)
        simpa [L] using h0
      | @insert i A hiA ih =>
        intro x hx
        have hg : (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) = 0 := by
          refine hY i _ (hfP i x) ?_
          intro y hy
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst hji
            simpa using hy
          · rw [Function.update_of_ne hji]
            exact hx j (by simp [hji, hj])
        have h1 := congrFun hg (x i)
        simpa using h1
    apply Subtype.ext
    funext x
    exact key Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj)
  have : FiniteDimensional ℂ P := Module.Finite.of_injective L hL
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanCoefficients
namespace GlobalTheory.CoefficientSpanFinite

theorem finiteDimensional_span_coefficients {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) :
    FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let Φ : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range Φ := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ∘ₗ LinearMap.applyₗ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CoefficientSpanFinite
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.SepTypes

theorem coeffSpan_finiteDimensional {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | (apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients ..)

theorem coeffSpan_rtrans {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (c : G) {h : G → ℂ} (hh : h ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (fun k => h (k * c)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (fun k : G => k * c)) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ c w, funext fun k => ?_⟩
    simp [LinearMap.funLeft, map_mul]
  exact hle hh

theorem exists_space {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : ι → Type} [∀ i, Group (Γ i)] (K : Subgroup G) (j : (∀ i, Γ i) →* K)
    (hjs : Function.Surjective j) (a : ∀ i, Γ i → G) (hj : ∀ i k, (j (Pi.mulSingle i k) : G) = a i k)
    (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (Γ i) (W i)) :
    ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧
      (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧
      ∀ φ : G → ℂ, Continuous φ → (∀ i x, (fun k => φ (x * a i k)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ i)) →
        ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  let S : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ τ (k₀ : K), (fun κ => f (k₀ * j (Pi.mulSingle τ κ))) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ τ)}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun τ k₀ => Submodule.add_mem _ (ha.2 τ k₀) (hb.2 τ k₀)⟩
      zero_mem' := ⟨continuous_const, fun τ k₀ => Submodule.zero_mem _⟩
      smul_mem' := fun c {a} ha => ⟨ha.1.const_smul c, fun τ k₀ => Submodule.smul_mem _ c (ha.2 τ k₀)⟩ }
  have hfd : ∀ τ, FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)) := fun τ => coeffSpan_finiteDimensional (ρ τ)
  have hfin := GlobalTheory.finiteDimensional_span_separately ι Γ (fun τ => GlobalTheory.Published.AutFin.coeffSpan (ρ τ)) hfd
  have hupd : ∀ (x : ∀ τ, Γ τ) τ y,
      Function.update x τ y = Function.update x τ 1 * Pi.mulSingle τ y := by
    intro x τ y
    funext τ'
    by_cases h : τ' = τ
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
  let M := Submodule.span ℂ {F : (∀ τ, Γ τ) → ℂ |
    ∀ τ x, (fun y => F (Function.update x τ y)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ τ)}
  let T : S →ₗ[ℂ] M :=
    { toFun := fun f => ⟨fun x => (f : K → ℂ) (j x), Submodule.subset_span fun τ x => by
        have := f.2.2 τ (j (Function.update x τ 1))
        convert this using 2 with y
        rw [hupd x τ y, map_mul]⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hT : Function.Injective T := by
    intro a b hab
    have := congrArg (fun u : M => (u : (∀ τ, Γ τ) → ℂ)) hab
    apply Subtype.ext
    funext k
    obtain ⟨x, rfl⟩ := hjs k
    exact congrFun this x
  refine ⟨S, Module.Finite.of_injective T hT, fun f hf => hf.1, ?_, ?_⟩
  · intro f hf k
    refine ⟨hf.1.comp (continuous_id.mul continuous_const), fun τ k₀ => ?_⟩
    obtain ⟨κ₁, rfl⟩ := hjs k
    have key : ∀ κ, k₀ * j (Pi.mulSingle τ κ) * j κ₁ =
        (k₀ * j (Function.update κ₁ τ 1)) * j (Pi.mulSingle τ (κ * κ₁ τ)) := by
      intro κ
      rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul]
      congr 2
      funext τ'
      by_cases h : τ' = τ
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp only [key]
    exact coeffSpan_rtrans (ρ τ) (κ₁ τ) (hf.2 τ _)
  · intro φ hφ hty g
    refine ⟨hφ.comp (continuous_const.mul continuous_subtype_val), fun τ k₀ => ?_⟩
    have := hty τ (g * (k₀ : G))
    simpa only [Subgroup.coe_mul, hj, mul_assoc] using this

end GlobalTheory.SepTypes

theorem GlobalTheory.typesFiniteSpace : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ K : Subgroup (GA D V), (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧ (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧ ∀ φ : GA D V → ℂ, Continuous φ → (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) → ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  intro D θ _ V ε fr _ K ⟨j, hjs, hj⟩ W _ _ _ ρ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.SepTypes.exists_space K j hjs (fun τ k => kAt θ V τ (ε τ) (fr τ) k) hj W ρ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.SplitValuePow

theorem val_pow {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (N : ℕ) (w : HeightOneSpectrum (𝓞 L)) :
    (χ ^ N).val w = χ.val w ^ N := by
  unfold Formalism.L2.Host.HChar.val Formalism.L2.Host.HChar.locK Formalism.L2.Host.HChar.loc
  simp only [MonoidHom.comp_apply, SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem inf_pow {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (N : ℕ) (k : Lˣ) :
    (χ ^ N).inf k = χ.inf k ^ N := by
  unfold Formalism.L2.Host.HChar.inf
  simp only [MonoidHom.comp_apply, SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ a p ha ha0 hp w hw hfin
  obtain ⟨N, hN, hunr⟩ := GlobalTheory.T.exists_pow_heckeChar_unramified_everywhere D.host.E χ
  obtain ⟨n, hn2, hinf⟩ := ha
  have hn0 : ∀ τ, n τ ≠ 0 := fun τ h => ha0 τ (by have := hn2 τ; rw [h] at this; push_cast at this; linarith)
  have ht : ∀ v, (χ ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (χ ^ N).HasInf (Formalism.L2.Host.embPsi D.host) (fun g => (N : ℤ) * n (D.eTau.symm g)) := by
    intro k
    rw [inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Fintype.prod_equiv D.eTau _ _ fun τ => ?_
    show _ = _ ^ ((N : ℤ) * n (D.eTau.symm (D.eTau τ)))
    rw [Equiv.symm_apply_apply, ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  refine GlobalTheory.SplitValue.not_isOfFinOrder_val D (χ ^ N) _ p ht hinf'
    (fun g => mul_ne_zero (by exact_mod_cast hN.ne') (hn0 _)) hp w hw ?_
  rw [val_pow]
  exact hfin.pow

end GlobalTheory.SplitValuePow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpliStatement
open NumberField IsDedekindDomain Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  first | exact @GlobalTheory.SplitValuePow.not_isOfFinOrder_val | exact GlobalTheory.SplitValuePow.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValuePow.not_isOfFinOrder_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModule
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.DualWeylType

open GlobalTheory.ConjugateType

theorem dual_weyl_type : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  intro k n h lam H _ _ _ σ lamH hσ hK hrho

  obtain ⟨hσ', hK'⟩ := GlobalTheory.ConjTwist.conj_twist_isKTypeOf k _ 0 H σ hσ hK

  obtain ⟨E, iE1, iE2, iE3, π, J, hJ, hπ, hπK, hπJ⟩ := exists_conjugate_type k _ H _ hσ' hK'
  have hJσ : ∀ g u, π g (J u) = J (σ g u) := by
    intro g u
    rw [hπJ]
    simp only [zpow_zero, one_smul, map_star_star]

  have hlow : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -lamH (Fin.rev i)) =
      fun a => ((0 : ℤ) : ℝ) - Formalism.QuantumDeterminants.lowK (allPos k) lamH (Fin.rev a) := by
    rw [GlobalTheory.ConjTypeW.lowK_neg_rev]
    funext a
    simp
  have hnt : Nontrivial E := by
    obtain ⟨-, -, -, ⟨v, -, hv0, -⟩, -⟩ := hπK
    exact ⟨⟨v, 0, hv0⟩⟩
  have hHC : IsHCTypeU k (fun i => -lamH (Fin.rev i)) π := ⟨hnt, iE3, hπ, by rw [hlow]; exact hπK⟩

  obtain ⟨jE, hmem, hsurj, hfock, heq⟩ :=
    GlobalTheory.WeylConjType.exists_conj_weyl k n h lam _ hrho E π hHC

  let j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    { toFun := fun ξ => jE (J ξ)
      map_add' := fun x y => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c x => by
        rw [map_smulₛₗ, map_smulₛₗ, RingHom.id_apply, Complex.conj_conj] }
  have hj : ∀ ξ, j ξ = jE (J ξ) := fun _ => rfl

  let Φ : H →ₗ[ℂ] ConjSp E :=
    { toFun := fun ξ => ConjSp.mk (J ξ)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by
        show ConjSp.mk (J (c • x)) = c • ConjSp.mk (J x)
        have e := (ConjSp.mkL E).map_smulₛₗ (starRingEnd ℂ c) (J x)
        rw [Complex.conj_conj] at e
        rw [map_smulₛₗ]
        exact e }
  have hΦ : Function.Bijective Φ := hJ
  let Ψ : H ≃ₗ[ℂ] ConjSp E := LinearEquiv.ofBijective Φ hΦ
  let f := stdOrthonormalBasis ℂ (ConjSp E)
  refine ⟨j, _, f.toBasis.map Ψ.symm, fun ξ => hmem _, fun p hp => ?_, fun a a' => ?_, fun g hg ξ => ?_⟩
  · obtain ⟨η, rfl⟩ := hsurj p hp
    obtain ⟨ξ, rfl⟩ := hJ.2 η
    exact ⟨ξ, rfl⟩
  · have hb : ∀ a, J ((f.toBasis.map Ψ.symm) a) = ConjSp.out (f a) := by
      intro a
      rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
      have := Ψ.apply_symm_apply (f a)
      exact this
    rw [hj, hj, hfock, hb, hb]
    show ⟪f a', f a⟫_ℂ = _
    rw [orthonormal_iff_ite.1 f.orthonormal]
    rcases eq_or_ne a a' with rfl | hA
    · simp
    · rw [if_neg hA.symm, if_neg hA]
  · rw [hj, hj, ← hJσ, heq g hg]

end GlobalTheory.DualWeylType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModuleStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  first | exact @GlobalTheory.DualWeylType.dual_weyl_type | exact GlobalTheory.DualWeylType.dual_weyl_type | (intros; apply GlobalTheory.DualWeylType.dual_weyl_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.RealCoordCusp

theorem normSq_det_UJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Complex.normSq (uMat g).det = 1 := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h2 : star (uMat g).det * (uMat g).det = 1 := by
    have : (star (uMat g).det * (uMat g).det - 1) * (Formalism.REAL.Jm ε).det = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hJ
  have h3 : ((Complex.normSq (uMat g).det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3

variable (I : AutInst)

abbrev Idx : Type := Σ _ : Fin I.n, Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)

def cBasis : Module.Basis (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) ℝ (InfinitePlace I.F → Fin I.n → ℂ) :=
  Pi.basis fun _ => Pi.basis fun _ => Complex.basisOneI

theorem card_eq : Fintype.card (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) = Fintype.card (Idx I) := by
  simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Formalism.L2.SG.Pf.Tau.card_infinite_places, Formalism.L2.SG.Pf.Tau.card_integral_basis]
  ring

def rho : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin (Fintype.card (Idx I)) → ℝ) :=
  ((cBasis I).reindex (Fintype.equivFinOfCardEq (card_eq I))).equivFun

theorem rho_isRealCoord : IsRealCoord I (rho I) := by
  intro x y
  simp only [rho, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply, dotProduct]
  rw [(Fintype.equivFinOfCardEq (card_eq I)).symm.sum_comp
    (fun s => (cBasis I).repr x s * (cBasis I).repr y s)]
  simp only [cBasis, Fintype.sum_sigma, Pi.basis_repr, Complex.coe_basisOneI_repr, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bQ : Module.Basis (Idx I) ℚ (Fin I.n → I.E) := Pi.basis fun _ => integralBasis I.E

def eB : Fin (Fintype.card (Idx I)) → Fin I.n → I.E := fun k => bQ I ((Fintype.equivFin (Idx I)).symm k)

theorem bQ_apply (p : Idx I) : bQ I p = Pi.single p.1 (integralBasis I.E p.2) := by
  simp [bQ, Pi.basis_apply]

theorem eB_isZBasis : IsZBasis I (eB I) := by
  refine ⟨((bQ I).linearIndependent.comp _ (Fintype.equivFin (Idx I)).symm.injective).restrict_scalars' ℤ, ?_⟩
  intro u
  constructor
  · intro hu
    have hm := Formalism.L2.SG.Pf.Tau.mem_integral_vectors I I.n u (fun k => ⟨⟨u k, hu k⟩, rfl⟩)
    rw [Formalism.L2.SG.Pf.Tau.t8O, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨fun k => c ((Fintype.equivFin (Idx I)).symm k), ?_⟩
    rw [← hc, ← (Fintype.equivFin (Idx I)).symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [eB, bQ_apply]
  · rintro ⟨z, rfl⟩ i
    rw [← mem_integralClosure_iff]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine zsmul_mem ?_ _
    rw [eB, bQ_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      rw [mem_integralClosure_iff, integralBasis_apply]
      exact (RingOfIntegers.basis I.E _).isIntegral_coe
    · exact zero_mem _

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bm (y : I.Ginf) : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (uMat (y v)⁻¹)).restrictScalars ℝ).comp (LinearMap.proj v)

theorem vec_eq (y : I.Ginf) (u : Fin I.n → I.E) : GlobalTheory.CuspGeo.vec I y u = bm I y (GlobalTheory.CuspGeo.vec I 1 u) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  simp [GlobalTheory.CuspGeo.vec, bm, h1]

theorem det_bm (y : I.Ginf) : LinearMap.det (bm I y) = 1 := by
  rw [bm, LinearMap.det_pi]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  exact normSq_det_UJ _

theorem gm_eq {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) :
    gm I ρ y e = LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) * gm I ρ 1 e := by
  ext i j
  rw [Matrix.mul_apply]
  change ρ (GlobalTheory.CuspGeo.vec I y (e j)) i = (LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) *ᵥ
    (fun k => ρ (GlobalTheory.CuspGeo.vec I 1 (e j)) k)) i
  rw [LinearMap.toMatrix'_mulVec]
  simp [vec_eq I y]

theorem det_gm {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) : (gm I ρ y e).det = (gm I ρ 1 e).det := by
  rw [gm_eq, Matrix.det_mul, LinearMap.det_toMatrix', LinearMap.det_conj, det_bm, one_mul]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def qm : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (I.P v)⁻¹).restrictScalars ℝ).comp (LinearMap.proj v)

def sw : (Fin I.n × InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun z := fun v i => z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem qm_injective : Function.Injective (qm I) := by
  intro x y h
  funext v
  have h0 := congrFun h v
  simp only [qm, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at h0
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h2 := congrArg (fun w => I.P v *ᵥ w) h0
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

theorem sw_injective : Function.Injective (sw I) := by
  intro x y h
  funext q
  exact congrFun (congrFun h q.2) q.1

theorem vec_one_bQ (p : Idx I) :
    GlobalTheory.CuspGeo.vec I 1 (bQ I p) = qm I (sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p)) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  have h2 : (fun i => I.φ v (bQ I p i)) = sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p) v := by
    funext i
    rw [bQ_apply, Pi.single_apply]
    change _ = Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p (i, v)
    rw [Formalism.L2.SG.Pf.Tau.placeCoordsBasis_apply]
    split_ifs with h
    · subst h; rfl
    · exact map_zero _
  simp only [GlobalTheory.CuspGeo.vec, Pi.one_apply, inv_one, h1, Matrix.one_mulVec]
  rw [h2]
  rfl

theorem det_gm_one_ne : (gm I (rho I) 1 (eB I)).det ≠ 0 := by
  have hli : LinearIndependent ℝ (fun j => (gm I (rho I) 1 (eB I))ᵀ j) := by
    have hf : LinearMap.ker ((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) = ⊥ :=
      LinearMap.ker_eq_bot.2 ((rho I).injective.comp ((qm_injective I).comp (sw_injective I)))
    have h := ((Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n).linearIndependent.map' _ hf).comp _
      (Fintype.equivFin (Idx I)).symm.injective
    have heq : (fun j => (gm I (rho I) 1 (eB I))ᵀ j) =
        ((⇑((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) ∘ ⇑(Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n)) ∘
          ⇑(Fintype.equivFin (Idx I)).symm) := by
      funext j
      funext i
      simp only [Matrix.transpose_apply, gm, Matrix.of_apply, Function.comp_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe]
      rw [eB, vec_one_bQ]
    rw [heq]
    exact h
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

end GlobalTheory.RealCoordCusp


open GlobalTheory.RealCoordCusp in
theorem GlobalTheory.CuspGeo.covolume_const : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E)
    (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ),
    0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  intro I
  refine ⟨_, eB I, rho I, |(gm I (rho I) 1 (eB I)).det|, abs_pos.2 (det_gm_one_ne I), eB_isZBasis I,
    rho_isRealCoord I, fun y => by rw [det_gm]⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstantStatement
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_integralBasis_covolume_constant : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ), 0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  first | exact @GlobalTheory.CuspGeo.covolume_const | exact GlobalTheory.CuspGeo.covolume_const | (intros; apply GlobalTheory.CuspGeo.covolume_const <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAdditiveCharacterEqAdelic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProduct
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

theorem unrAt_iff_not_dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    χ.UnrAt v ↔ ¬ v.asIdeal ∣ (toHecke χ hu).conductor := by
  rw [HeckeCharacter.not_dvd_conductor_iff]
  constructor
  · intro h a ha
    rw [Submonoid.mem_units_iff] at ha
    have h1 : Valued.v (a : v.adicCompletion E) ≤ 1 := ha.1
    have h2 : Valued.v ((a⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := ha.2
    have h3 : Valued.v (a : v.adicCompletion E) = 1 := by
      refine le_antisymm h1 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
      exact (inv_le_one₀ (by simp [zero_lt_iff])).1 h2
    rw [MonoidHom.mem_ker]
    show (toHecke χ hu).localComponent v a = 1
    apply Circle.ext
    rw [coe_localComponent, h a h3]
    simp
  · intro h x hx
    have hx' : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
      rw [Submonoid.mem_units_iff]
      refine ⟨le_of_eq hx, ?_⟩
      show Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      have hx1 : Valued.v (x : v.adicCompletion E) = 1 := hx
      rw [hx1, inv_one]
    have h1 : (toHecke χ hu).localComponent v x = 1 := MonoidHom.mem_ker.1 (h hx')
    have h2 := coe_localComponent χ hu v x
    rw [h1] at h2
    ext
    simpa using h2.symm

theorem coeff_eq_val (χ : HChar E) (hu : IsUnitary χ) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ (toHecke χ hu).conductor) :
    (toHecke χ hu).coeff v.asIdeal = (χ.val v : ℂ) := by
  rw [(toHecke χ hu).coeff_asIdeal_eq_toIdele hv (unif_spec v), ← HeckeCharacter.localComponent_apply,
    coe_localComponent]
  rfl

theorem hasProd_eulerFactor_toHecke : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ),
    1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  intro E _ _ χ hu s hs
  have h : eulerFactor χ s = fun v : HeightOneSpectrum (𝓞 E) ↦
      (1 - (toHecke χ hu).coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
    funext v
    unfold eulerFactor
    by_cases hv : χ.UnrAt v
    · rw [if_pos hv, coeff_eq_val χ hu ((unrAt_iff_not_dvd_conductor χ hu v).1 hv)]
    · rw [if_neg hv, HeckeCharacter.coeff_asIdeal_of_dvd _
        (not_not.1 (mt (unrAt_iff_not_dvd_conductor χ hu v).2 hv))]
      simp
  rw [h]
  exact (toHecke χ hu).LFunction_hasProd_all hs

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProductStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_L_function_euler_product : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ), 1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnS
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBridge

theorem finEps_shift : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) :=
  fun _ _ _ χ a s => GlobalTheory.HeckeEpsAbs.finEps_eq χ a s

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnSStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_epsilon_factor_dependence_on_s : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | exact GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.finEps_shift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTerm
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTerm
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge.GaussSum

variable {E : Type} [Field E] [NumberField E]

theorem dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0)
    (h : ExpAt χ v m) : v.asIdeal ∣ (toHecke χ hu).conductor := by
  by_contra hv
  refine h.not_unrAt hm fun x hx => ?_
  have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
  have hmem : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
    refine Submonoid.mem_units_iff _ _ |>.2 ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx'.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]
  have h1 := (toHecke χ hu).localComponent_eq_one_of_not_dvd hv hmem
  have h2 := coe_localComponent χ hu v x
  rw [h1] at h2
  exact Units.ext (by simpa using h2.symm)

theorem hval (v : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_eq_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) = 1 := by
  exact (hval v _).trans ((v.valuation_eq_one_iff_notMem (K := E)).2 hy)

theorem valued_ne_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∈ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) ≠ 1 := by
  exact fun h => (v.valuation_eq_one_iff_notMem (K := E)).1 ((hval v _).symm.trans h) hy

theorem term_of_notMem (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal ∣ (toHecke χ hu).conductor) (c : Eˣ) {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) (y : E)) *
        psiAt v (((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) (y : E)) =
      gaussTerm χ v c (y : E) := by
  have hy0 : (y : E) ≠ 0 := by
    intro h0
    have : y = 0 := by exact_mod_cast h0
    exact hy (this ▸ v.asIdeal.zero_mem)
  have h1 := (toHecke χ hu).finiteTest_of_dvd hv (atFin v (Units.mk0 (y : E) hy0)) (valued_eq_one hy)
  have h2 : ((atFin v (Units.mk0 (y : E) hy0) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  rw [h2] at h1
  rw [h1, coe_localComponent, gaussTerm, dite_eq_right hy0, Units.val_inv_eq_inv_val]
  have h3 : ((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (c : E) := rfl
  rw [h3, map_div₀, div_eq_mul_inv, mul_comm (algebraMap E _ _)]
  rfl

theorem finiteTest_sum_eq_gaussSumAt (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (hm : m ≠ 0) (hE : ExpAt χ v m) :
    ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) =
      gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  have hv := dvd_conductor χ hu v hm hE
  rw [gaussSumAt]
  have hG : ∀ y : (𝓞 E ⧸ v.asIdeal ^ m)ˣ, gaussTerm χ v (unif v ^ (m + diffExp v)) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E) =
      (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) :=
    fun y => (term_of_notMem χ hu v hv _ (out_notMem v hm y)).symm
  rw [finsum_congr hG, ← finsum_mem_range (g := ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)) Units.val_injective
    (f := fun r : 𝓞 E ⧸ v.asIdeal ^ m => (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E))), finsum_mem_def]
  refine finsum_congr fun r => ?_
  by_cases hr : r ∈ Set.range ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)
  · rw [Set.indicator_of_mem hr]
  · rw [Set.indicator_of_notMem hr]
    have hmem : (Quotient.out r : 𝓞 E) ∈ v.asIdeal := by
      by_contra hn
      have h1 := Ideal.Quotient.isUnit_mk_pow_of_notMem v.asIdeal (n := m) hn
      rw [Ideal.Quotient.mk_out] at h1
      exact hr ⟨h1.unit, rfl⟩
    rw [(toHecke χ hu).finiteTest_eq_zero_of_dvd hv (valued_ne_one hmem), zero_mul]

end GlobalTheory.CompanionTheory.HeckeBridge.GaussSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTermStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_gauss_sum_local_term : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), m ≠ 0 → ExpAt χ v m → ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) * psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) = gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | exact GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPower
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPower
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeBridge.NotPow

open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (atInf)

theorem exists_ext_surj {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (hw : (InfinitePlace.mk φ).IsComplex) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧ (∀ k : L, e (algebraMap L _ k) = φ k) ∧
      Function.Surjective e ∧ ∀ x, ‖e x‖ = ‖x‖ := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_,
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw, fun x => ?_⟩
    · rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
      rfl
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_, fun y => ?_, fun x => ?_⟩
    · rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
        InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_conj _
    · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
        ((starRingEnd ℂ) y)
      exact ⟨x, by rw [RingHom.comp_apply, hx, Complex.conj_conj]⟩
    · rw [RingHom.comp_apply, Complex.norm_conj]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x

theorem exists_norm_one_zpow_ne (m : ℤ) (hm : m ≠ 0) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ m ≠ 1 := by
  refine ⟨Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_int_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hx : (m : ℂ) * (((Real.pi / m : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hx, Complex.exp_pi_mul_I]
  norm_num

private theorem exists_inclusion_mul_eq_mul_inclusion_of_normal {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ c : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous c ∧ ∀ k : L, c (algebraMap L _ k) = φ k := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_⟩
    rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
    rfl
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_⟩
    rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
      InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_conj _

private theorem denseRange_units_map_infiniteAdeleRing (E : Type) [Field E] [NumberField E] :
    DenseRange (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom) := by
  have hopen : IsOpenMap (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenMap_val (R := (w : InfinitePlace E) → w.Completion)
  have hd := InfiniteAdeleRing.denseRange_algebraMap E
  rw [DenseRange, dense_iff_inter_open]
  rintro V hV ⟨u, hu⟩
  obtain ⟨_, ⟨u', hu', rfl⟩, k, hk⟩ := hd.inter_open_nonempty _ (hopen V hV) ⟨u, u, hu, rfl⟩
  by_cases hk0 : k = 0
  · have h0 : (u' : InfiniteAdeleRing E) = 0 := by rw [← hk, hk0, map_zero]
    have h01 : (0 : InfiniteAdeleRing E) = 1 := by rw [← u'.mul_inv, h0, zero_mul]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨u', hu', 1, Units.ext (Subsingleton.elim _ _)⟩
  · exact ⟨u', hu', Units.mk0 k hk0, Units.ext (by simpa using hk)⟩

theorem comp_eq {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hb : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar E) {n : I → ℤ}
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (z : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    ((χ.1 (infIdele E _ z) : ℂˣ) : ℂ) =
      (e (z : (InfinitePlace.mk (φ i)).Completion) /
        ((‖e (z : (InfinitePlace.mk (φ i)).Completion)‖ : ℝ) : ℂ)) ^ n i := by
  classical
  choose c₀ hc₀ hc₀' using fun j => exists_inclusion_mul_eq_mul_inclusion_of_normal (φ j)
  let c : ∀ j, (InfinitePlace.mk (φ j)).Completion →+* ℂ := Function.update c₀ i e
  have hc : ∀ j, Continuous (c j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [c] using hec
    · simpa [c, hj] using hc₀ j
  have hc' : ∀ j (k : E), c j (algebraMap E _ k) = φ j k := by
    intro j k
    by_cases hj : j = i
    · subst hj
      simpa [c] using he k
    · simpa [c, hj] using hc₀' j k
  let ι0 : InfiniteAdeleRing E →* NumberField.AdeleRing (NumberField.RingOfIntegers E) E :=
    MonoidHom.inl (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E)
  have hι0 : Continuous ι0 := continuous_id.prodMk continuous_const
  obtain ⟨hχc, -⟩ := χ.2
  let Ψ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ((χ.1 (Units.map ι0 u) : ℂˣ) : ℂ)
  let Θ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ∏ j, (c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) /
      ((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ^ n j
  have hne : ∀ (j : I) (u : (InfiniteAdeleRing E)ˣ),
      c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) ≠ 0 := by
    intro j u h0
    have h1 := congrArg (fun x : InfiniteAdeleRing E => x (InfinitePlace.mk (φ j))) u.mul_inv
    have h2 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 0 := (map_eq_zero (c j)).1 h0
    change (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) *
      ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 1 at h1
    rw [h2, zero_mul] at h1
    exact zero_ne_one h1
  have hΨ : Continuous Ψ := Units.continuous_val.comp (hχc.comp (Continuous.units_map ι0 hι0))
  have hΘ : Continuous Θ := by
    refine continuous_finsetProd _ fun j _ => ?_
    have hcont : Continuous fun u : (InfiniteAdeleRing E)ˣ =>
        c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) :=
      (hc j).comp ((continuous_apply (InfinitePlace.mk (φ j))).comp Units.continuous_val)
    have hn0 : ∀ u : (InfiniteAdeleRing E)ˣ,
        (((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ≠ 0 :=
      fun u => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne j u))
    exact (hcont.div (Complex.continuous_ofReal.comp (continuous_norm.comp hcont)) hn0).zpow₀ (n j)
      fun u => Or.inl (div_ne_zero (hne j u) (hn0 u))
  have hkey : Ψ = Θ := by
    refine Continuous.ext_on (denseRange_units_map_infiniteAdeleRing E) hΨ hΘ ?_
    rintro _ ⟨k, rfl⟩
    have hdiag : Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) =
        Formalism.L2.Host.infDiag k := by
      apply Units.ext
      simp only [Formalism.L2.Host.infDiag, MonoidHom.coe_finsetProd, Finset.prod_apply, MonoidHom.coe_comp,
        Function.comp_apply, Units.coe_prod, Units.coe_map]
      have hprod : (∏ w, (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w
          (algebraMap E w.Completion (k : E)) : InfiniteAdeleRing E)) = algebraMap E (InfiniteAdeleRing E) (k : E) :=
        Finset.univ_prod_mulSingle (fun w : InfinitePlace E => algebraMap E w.Completion (k : E))
      rw [Finset.prod_congr rfl fun w _ => (show ((infIdele E w (Formalism.L2.Host.atInf w k) : Neutral.B1.Ideles E) :
          NumberField.AdeleRing (NumberField.RingOfIntegers E) E) =
          ι0 (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w (algebraMap E w.Completion (k : E))) from rfl)]
      exact (congrArg ι0 hprod.symm).trans (map_prod ι0 _ _)
    have hinf := hn k
    simp only [Formalism.L2.Host.HChar.inf, MonoidHom.coe_comp, Function.comp_apply] at hinf
    show ((χ.1 (Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k)) : ℂˣ) : ℂ) = _
    rw [hdiag]
    refine hinf.trans (Finset.prod_congr rfl fun j _ => ?_)
    show _ = (c j (algebraMap E _ (k : E)) / ((‖c j (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n j
    rw [hc' j]
  have hz := congrFun hkey
    (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z)
  have hι : Units.map ι0
      (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z) =
      infIdele E _ z := by
    apply Units.ext
    rfl
  simp only [Ψ, Θ] at hz
  rw [hι] at hz
  let a : ∀ w : InfinitePlace E, w.Completion :=
    Pi.mulSingle (InfinitePlace.mk (φ i)) (z : (InfinitePlace.mk (φ i)).Completion)
  change _ = ∏ j, (c j (a (InfinitePlace.mk (φ j))) /
      ((‖c j (a (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ^ n j at hz
  rw [hz, Finset.prod_eq_single i]
  · simp [a, c]
  · intro j _ hj
    have hw : InfinitePlace.mk (φ j) ≠ InfinitePlace.mk (φ i) := fun h => hj (hb.1 h)
    simp [a, Pi.mulSingle_eq_of_ne hw]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ideleModule_infIdele {E : Type} [Field E] [NumberField E] (w : InfinitePlace E)
    (z : (w.Completion)ˣ) :
    (ideleModule E (infIdele E w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  show (IdeleGroup.infiniteModule (infIdele E w z) * IdeleGroup.finiteModule (infIdele E w z) : ℝ) = _
  have hinf : IdeleGroup.infiniteModule (infIdele E w z : IdeleGroup E) = ‖(z : w.Completion)‖ ^ w.mult := by
    unfold IdeleGroup.infiniteModule
    rw [Fintype.prod_eq_single w]
    · show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w‖ ^ w.mult = _
      rw [Pi.mulSingle_eq_same]
    · intro w' hw'
      show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w'‖ ^ w'.mult = 1
      rw [Pi.mulSingle_eq_of_ne hw', norm_one, one_pow]
  have hfin : IdeleGroup.finiteModule (infIdele E w z : IdeleGroup E) = 1 := by
    unfold IdeleGroup.finiteModule
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    show ‖(1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E) v‖ = 1
    simp
  rw [hinf, hfin, mul_one]

theorem not_modulePow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  intro E _ _ _ I _ φ hcm χ hu n hn hex hτex
  obtain ⟨i, hi⟩ := hex
  obtain ⟨τ, hτ⟩ := hτex
  have hb := GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hcm
  have hw : (InfinitePlace.mk (φ i)).IsComplex := IsTotallyComplex.isComplex _
  obtain ⟨e, hec, he, hes, hen⟩ := exists_ext_surj (φ i) hw
  obtain ⟨ζ, hζ1, hζm⟩ := exists_norm_one_zpow_ne (n i) hi
  obtain ⟨y, rfl⟩ := hes ζ
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hy1 : ‖y‖ = 1 := by rw [← hen]; exact hζ1
  have h3 := comp_eq hb χ hn i e hec he (Units.mk0 y hy0)
  have h4 := ideleModule_infIdele (InfinitePlace.mk (φ i)) (Units.mk0 y hy0)
  have h5 := hτ (infIdele E _ (Units.mk0 y hy0))
  rw [GlobalTheory.CompanionTheory.HeckeBridge.coe_toIdele] at h5
  apply hζm
  simp only [Units.val_mk0] at h3 h4
  rw [hζ1, Complex.ofReal_one, div_one] at h3
  rw [← h3]
  refine h5.trans ?_
  rw [h4, hy1, one_pow, Complex.ofReal_one, Complex.one_cpow]

end GlobalTheory.CompanionTheory.HeckeBridge.NotPow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterNotNormPowerStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hecke_character_not_norm_power : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.NotPow.not_modulePow | exact GlobalTheory.CompanionTheory.HeckeBridge.NotPow.not_modulePow | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.NotPow.not_modulePow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponent
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

theorem comp_finiteUnitsSingle (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) =
      ((toHecke χ hu).localComponent v : (v.adicCompletion E)ˣ →* Circle) := by
  refine MonoidHom.ext fun a => ?_
  show (toHecke χ hu).toIdele (ofFinite (finiteUnitsSingle v a)) = (toHecke χ hu).localComponent v a
  rw [GroundTheory.Global.IdeleGroup.ofFinite_finiteUnitsSingle, GroundTheory.Global.HeckeCharacter.localComponent_apply]

private theorem toHecke_local_eq_one_iff (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) x = 1 ↔ χ.loc v x = 1 := by
  rw [comp_finiteUnitsSingle χ hu v]
  have h := coe_localComponent χ hu v x
  constructor
  · intro h1
    apply Units.ext
    rw [← h]
    have h1' : (toHecke χ hu).localComponent v x = 1 := h1
    rw [h1', Circle.coe_one, Units.val_one]
  · intro h1
    have h1' : (toHecke χ hu).localComponent v x = 1 := by
      apply Circle.ext
      rw [h, h1, Units.val_one, Circle.coe_one]
    exact h1'

theorem levelLe_iff_unitsLevel_le_ker (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔
      unitsLevel v n ≤ (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)).ker := by
  unfold Formalism.L2.Host.HChar.LevelLe
  constructor
  · intro h x hx
    rw [GroundTheory.Global.mem_unitsLevel] at hx
    rw [MonoidHom.mem_ker, toHecke_local_eq_one_iff χ hu v x]
    exact h x hx.1 hx.2
  · intro h x hux hx
    rw [← toHecke_local_eq_one_iff χ hu v x]
    exact h (GroundTheory.Global.mem_unitsLevel.mpr ⟨hux, hx⟩)

theorem levelLe_iff_conductorExponentAt (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) v ≤ n := by
  rw [levelLe_iff_unitsLevel_le_ker χ hu v n]
  exact GroundTheory.Global.unitsLevel_le_ker_iff v GroundTheory.Global.Circle.noSmallSubgroups _
    (((toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite).comp
      (GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle v))

private theorem asIdeal_pow_dvd_finprod_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a : HeightOneSpectrum R → ℕ} (ha : (Function.support a).Finite) (v : HeightOneSpectrum R) (k : ℕ) :
    v.asIdeal ^ k ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ k ≤ a v := by
  classical
  have hfin : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ a w).Finite := by
    rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact ha
  constructor
  · intro hk
    by_contra hlt
    rw [not_le] at hlt
    set b : HeightOneSpectrum R → ℕ := Function.update a v 0 with hb
    have hbfin : (Function.support b).Finite := by
      refine ha.subset (fun w hw => ?_)
      by_cases hwv : w = v
      · subst hwv
        simp [hb] at hw
      · simpa [hb, Function.update_of_ne hwv] using hw
    have hcfin : (Function.mulSupport fun w : HeightOneSpectrum R =>
        w.asIdeal ^ (if w = v then a v else 0)).Finite := by
      refine (Set.finite_singleton v).subset (fun w hw => ?_)
      rw [Set.mem_singleton_iff]
      by_contra hwv
      exact hw (by simp [hwv])
    have hbfin' : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ b w).Finite := by
      rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact hbfin
    have hsingle : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ (if w = v then a v else 0) = v.asIdeal ^ a v := by
      rw [finprod_eq_single _ v (fun w hw => by simp [hw])]
      simp
    have hsplit : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w =
        v.asIdeal ^ a v * ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w := by
      rw [← hsingle, ← finprod_mul_distrib hcfin hbfin']
      refine finprod_congr fun w => ?_
      by_cases hwv : w = v
      · subst hwv
        simp [hb]
      · simp [hb, hwv, Function.update_of_ne hwv]
    rw [hsplit] at hk
    have hpow : v.asIdeal ^ k = v.asIdeal ^ a v * v.asIdeal ^ (k - a v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow] at hk
    have hne0 : v.asIdeal ^ a v ≠ 0 := pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
    have hk' := (mul_dvd_mul_iff_left hne0).mp hk
    have hv : v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w :=
      (dvd_pow_self _ (by omega)).trans hk'
    have h1 := (GroundTheory.Global.asIdeal_dvd_finprod_iff hbfin v).mp hv
    simp [hb] at h1
  · intro hk
    exact (pow_dvd_pow _ hk).trans
      (finprod_mem_dvd (f := fun w : HeightOneSpectrum R => w.asIdeal ^ a w) v hfin)

theorem multiplicity_conductor_toHecke (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (h : ExpAt χ v m) :
    multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  have hcont : Continuous ((toHecke χ hu).toIdele.comp ofFinite) :=
    (toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite
  have hfin := GroundTheory.Global.IdeleGroup.finite_support_conductorExponentAt
    GroundTheory.Global.Circle.noSmallSubgroups _ hcont
  have hne := (toHecke χ hu).conductor_ne_bot
  have hcond : χ.IsCond (toHecke χ hu).conductor := by
    unfold Formalism.L2.Host.HChar.IsCond
    refine ⟨hne, fun w n => ?_⟩
    rw [levelLe_iff_conductorExponentAt χ hu w n]
    have h1 := asIdeal_pow_dvd_finprod_iff hfin w (n + 1)
    change _ ↔ ¬ w.asIdeal ^ (n + 1) ∣ ∏ᶠ u : HeightOneSpectrum (𝓞 E),
      u.asIdeal ^ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) u
    rw [h1]
    constructor <;> intro h2 <;> omega
  exact (GlobalTheory.CMVal.ExpAt.unique h ((GlobalTheory.CMVal.isCond_iff_expAt χ hne).mp hcond v)).symm

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponentStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_conductor_exponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), ExpAt χ v m → multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke <;> assumption)
end
end

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeFE
variable {E : Type} [Field E] [NumberField E]

theorem L_cond (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (h : ExpAt χ v m) :
    multiplicity v.asIdeal (toHecke χ hu).conductor = m := GlobalTheory.T.hecke_character_conductor_exponent E χ hu v m h

theorem L_inf {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (hu : IsUnitary χ)
    (n : I → ℤ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) :
    (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧
      ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs :=
  GlobalTheory.T.cm_hecke_character_infinity_type E I φ hφ χ hu n hi i

theorem L_notPow {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (hu : IsUnitary χ)
    (n : I → ℤ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E,
      ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) :=
  GlobalTheory.T.cm_hecke_character_not_norm_power E I φ hφ χ hu n hi hn

theorem L_euler (χ : HChar E) (hu : IsUnitary χ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := GlobalTheory.T.hecke_L_function_euler_product E χ hu s hs

theorem L_shift (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    finEps χ a s = finEps χ a (1 / 2) *
      (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) := GlobalTheory.T.finite_epsilon_factor_dependence_on_s E χ a s

theorem ord_unif (v : HeightOneSpectrum (𝓞 E)) (k : ℕ) :
    ord ((atFin v (unif v ^ k) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = k := by
  have h := valued_eq_exp_neg_ord (v := v) (Units.ne_zero (atFin v (unif v ^ k)))
  have h2 : Valued.v ((atFin v (unif v ^ k) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-(k : ℤ)) := by
    have h3 : Valued.v ((atFin v (unif v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
    rw [map_pow, Units.val_pow_eq_pow_val, map_pow, h3, ← WithZero.exp_nsmul]
    simp
  rw [h2, WithZero.exp_inj] at h
  omega

theorem differentExp_eq (v : HeightOneSpectrum (𝓞 E)) : differentExp v = (diffExp v : ℤ) :=
  count_coeIdeal_eq_multiplicity v _root_.differentIdeal_ne_bot

theorem L_ramInt (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) (h : ExpAt χ v m) :
    ∫ y, (toHecke χ hu).finiteTest v y *
        (localAdelicChar E v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * y) : ℂ)
        ∂haarIntegers (v.adicCompletion E) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  have hc : multiplicity v.asIdeal (toHecke χ hu).conductor = m := L_cond χ hu v m h
  have hG := GlobalTheory.T.hecke_gauss_sum_local_term E χ hu v m hm h
  simp only [GlobalTheory.T.local_additive_character_eq_adelic] at hG
  rw [GlobalTheory.T.haar_integral_integers_finite_sum E v m _ (fun y hy => by rw [(toHecke χ hu).finiteTest_eq_zero hy, zero_mul]) (fun y k hk => ?_), hG]
  set c : v.adicCompletion E := ((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) with hcdef
  have hcv : Valued.v c = WithZero.exp (-((m + diffExp v : ℕ) : ℤ)) := by
    have h3 : Valued.v ((atFin v (unif v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
    rw [hcdef, map_pow, Units.val_pow_eq_pow_val, map_pow, h3, ← WithZero.exp_nsmul]
    simp
  have hψ : localAdelicChar E v (c⁻¹ * k) = 1 := by
    refine localAdelicChar_eq_one_of_mem ((mem_localInvDifferent_iff_valued v _).2 ?_)
    show _ ≤ WithZero.exp (differentExp v)
    rw [map_mul, map_inv₀, hcv, ← WithZero.exp_neg, differentExp_eq]
    calc _ ≤ WithZero.exp (- -((m + diffExp v : ℕ) : ℤ)) * WithZero.exp (-(m : ℤ)) := mul_le_mul' le_rfl hk
      _ = _ := by
        rw [← WithZero.exp_add]
        congr 1
        push_cast
        ring
  rw [(toHecke χ hu).finiteTest_add y (by rw [hc]; exact hk), mul_add, AddChar.map_add_eq_mul, hψ, mul_one]

theorem L_locUnr (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (h : ExpAt χ v 0) :
    localEpsilon (localChar (toHecke χ hu) v) (localAdelicChar E v) (1 / 2) = locEps χ v 0 (1 / 2) := by
  have hv : ¬ v.asIdeal ∣ (toHecke χ hu).conductor := fun hd =>
    (multiplicity_pos_of_dvd hd (Ideal.finiteMultiplicity v.isPrime.ne_top (toHecke χ hu).conductor_ne_bot)).ne' (L_cond χ hu v 0 h)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [(toHecke χ hu).localEpsilon_half_of_not_dvd v hv (atFin v (unif v ^ (0 + diffExp v)))
    (by rw [ord_unif, differentExp_eq, zero_add]), coe_localComponent, locEps, if_pos rfl, mul_one, mul_assoc,
    ← Complex.cpow_add _ _ hN]
  have : -(1 / 2 : ℂ) * ((0 + diffExp v : ℕ) : ℂ) + (diffExp v : ℂ) / 2 = 0 := by
    push_cast
    ring
  rw [this, Complex.cpow_zero, mul_one]
  rfl

theorem L_locRam (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) (h : ExpAt χ v m) :
    localEpsilon (localChar (toHecke χ hu) v) (localAdelicChar E v) (1 / 2) = locEps χ v m (1 / 2) := by
  have hc := L_cond χ hu v m h
  have hv : v.asIdeal ∣ (toHecke χ hu).conductor := by
    by_contra hd
    exact hm (hc ▸ multiplicity_eq_zero_of_not_dvd hd)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [(toHecke χ hu).localEpsilon_half_of_dvd v hv (atFin v (unif v ^ (m + diffExp v)))
    (by rw [ord_unif, differentExp_eq, HeckeCharacter.condExp_eq, hc]; push_cast; rfl),
    L_ramInt χ hu v hm h, coe_localComponent, locEps, if_neg hm, hc]
  set c : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((m : ℂ) / 2) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Ne, Complex.cpow_eq_zero_iff]
    tauto
  have h1 : (Real.sqrt ((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ) : ℂ) = c := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), hcdef]
    push_cast
    rw [← Complex.natCast_cpow_natCast_mul]
    congr 1
    ring
  have h2 : (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ)) = c * c := by
    rw [hcdef, ← Complex.cpow_add _ _ hN]
    push_cast
    rw [add_halves, Complex.cpow_natCast]
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ) * ((m + diffExp v : ℕ) : ℂ)) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ ((diffExp v : ℂ) / 2) = c⁻¹ := by
    rw [← Complex.cpow_add _ _ hN, hcdef, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  have h4 : ((χ.locK v (unif v ^ (m + diffExp v)) : ℂˣ) : ℂ) = ((χ.loc v (atFin v (unif v ^ (m + diffExp v))) : ℂˣ) : ℂ) := rfl
  rw [h4]
  have h5 : c * (c * c)⁻¹ = c⁻¹ := by
    field_simp
  linear_combination (((χ.loc v (atFin v (unif v ^ (m + diffExp v))) : ℂˣ) : ℂ) * gaussSumAt χ v m (unif v ^ (m + diffExp v))) * (h5 - h3)

theorem bijective_mk {I : Type} {φ : I → E →+* ℂ} (hφ : IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  constructor
  · intro i j h
    have h' : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := h
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    have h1 := hk i (Or.inl rfl)
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact h1.trans (hk j (Or.inl e)).symm
    · exact h1.trans (hk j (Or.inr (by rw [← e]; ext x; simp))).symm
  · intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · show InfinitePlace.mk (φ i) = w
      rw [← e, InfinitePlace.mk_embedding]
    · show InfinitePlace.mk (φ i) = w
      rw [← InfinitePlace.mk_conjugate_eq, ← e, InfinitePlace.mk_embedding]

section
variable {I : Type} [Fintype I] {φ : I → E →+* ℂ} [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {n : I → ℤ}

theorem gammaFactor_toHecke (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (s : ℂ) :
    (toHecke χ hu).gammaFactor s = archFactor n s := by
  rw [HeckeCharacter.gammaFactor, archFactor, ← (Equiv.ofBijective _ (bijective_mk hφ)).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨h1, h2⟩ := L_inf φ hφ χ hu n hi i
  have hc : ¬ (InfinitePlace.mk (φ i)).IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
  have e : (((n i).natAbs : ℕ) : ℂ) = ((|n i| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  show (toHecke χ hu).infiniteGamma (InfinitePlace.mk (φ i)) s = _
  rw [HeckeCharacter.infiniteGamma, if_neg hc, h1, h2, e, Complex.Gammaℂ_def]
  simp

theorem prod_weight_toHecke (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) :
    (∏ w, (-Complex.I) ^ ((toHecke χ hu).infiniteWeight w).natAbs) = archEps n := by
  rw [archEps, ← Finset.prod_pow_eq_pow_sum, ← (Equiv.ofBijective _ (bijective_mk hφ)).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  show (-Complex.I) ^ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = _
  rw [(L_inf φ hφ χ hu n hi i).2]

theorem rootNumber_toHecke (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n)
    {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    (toHecke χ hu).rootNumber = archEps n * finEps χ a (1 / 2) := by
  have h1 := (toHecke χ hu).finiteFourier_mul_eq_finprod_localEpsilon
    (toHecke χ hu).toFractionalIdeal_conductorDifferentIdele
  have h2 : (∏ᶠ v, localEpsilon (localChar (toHecke χ hu) v) (localAdelicChar E v) (1 / 2)) = finEps χ a (1 / 2) := by
    refine finprod_congr fun v => ?_
    by_cases hv : a v = 0
    · have := ha v
      rw [hv] at this ⊢
      exact L_locUnr χ hu v this
    · exact L_locRam χ hu v hv (ha v)
  rw [h2] at h1
  rw [HeckeCharacter.rootNumber, HeckeCharacter.fourierConst, prod_weight_toHecke hφ hu hi, ← h1]
  ring

def conductorNormalizedCompletedLFunction (χ : HChar E) (hu : IsUnitary χ) (s : ℂ) : ℂ :=
  ((toHecke χ hu).discrNormConductor : ℂ) ^ (-(s / 2)) * (toHecke χ hu).completedLFunction s

theorem isCompletedL_completed (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n)
    (hn : ∃ i, n i ≠ 0) : IsCompletedL χ n (conductorNormalizedCompletedLFunction χ hu) := by
  have hA : ((toHecke χ hu).discrNormConductor : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (toHecke χ hu).discrNormConductor_pos.ne'
  refine ⟨?_, fun s hs => ⟨_, L_euler χ hu hs, ?_⟩⟩
  · refine Differentiable.mul (fun s => ?_)
      ((toHecke χ hu).differentiable_completedLFunction (L_notPow φ hφ χ hu n hi hn))
    exact ((differentiableAt_id.div_const 2).neg).const_cpow (Or.inl hA)
  · rw [conductorNormalizedCompletedLFunction, (toHecke χ hu).completedLFunction_eq hs, gammaFactor_toHecke hφ hu hi, ← mul_assoc, ← mul_assoc,
      ← Complex.cpow_add _ _ hA, neg_add_cancel, Complex.cpow_zero, one_mul]

theorem absNorm_conductor_toHecke (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    Ideal.absNorm (toHecke χ hu).conductor = a.prod fun v k => Ideal.absNorm v.asIdeal ^ k := by
  have hm := fun v => L_cond χ hu v (a v) (ha v)
  have h : (toHecke χ hu).conductorPrimes = a.support := by
    ext v
    rw [HeckeCharacter.mem_conductorPrimes, Finsupp.mem_support_iff, ← hm v]
    constructor
    · intro h
      exact (multiplicity_pos_of_dvd h (Ideal.finiteMultiplicity v.isPrime.ne_top (toHecke χ hu).conductor_ne_bot)).ne'
    · intro h
      by_contra h'
      exact h (multiplicity_eq_zero_of_not_dvd h')
  rw [HeckeCharacter.absNorm_conductor, Finsupp.prod, h]
  exact Finset.prod_congr rfl fun v _ => by rw [hm v]

theorem discrNormConductor_toHecke (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    ((toHecke χ hu).discrNormConductor : ℂ) =
      (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) := by
  rw [HeckeCharacter.discrNormConductor, absNorm_conductor_toHecke hu ha, ← Complex.ofReal_natCast, Nat.cast_mul,
    Nat.cast_natAbs, Int.cast_abs]

theorem completed_eq (hφ : IsCMType φ) (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0)
    (hu' : IsUnitary χ⁻¹) (s : ℂ) :
    conductorNormalizedCompletedLFunction χ hu s = (toHecke χ hu).rootNumber * ((toHecke χ hu).discrNormConductor : ℂ) ^ (1 / 2 - s) *
      conductorNormalizedCompletedLFunction χ⁻¹ hu' (1 - s) := by
  have hA : ((toHecke χ hu).discrNormConductor : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (toHecke χ hu).discrNormConductor_pos.ne'
  rw [conductorNormalizedCompletedLFunction, conductorNormalizedCompletedLFunction, toHecke_inv χ hu hu', HeckeCharacter.discrNormConductor_inv,
    (toHecke χ hu).completedLFunction_eq_rootNumber_mul_of_not (L_notPow φ hφ χ hu n hi hn) s]
  have e : ((toHecke χ hu).discrNormConductor : ℂ) ^ (-(s / 2)) =
      ((toHecke χ hu).discrNormConductor : ℂ) ^ (1 / 2 - s) *
        ((toHecke χ hu).discrNormConductor : ℂ) ^ (-((1 - s) / 2)) := by
    rw [← Complex.cpow_add _ _ hA]
    congr 1
    ring
  rw [e]
  ring

end

end GlobalTheory.CompanionTheory.HeckeFE

theorem GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation := by
  intro E _ _ _ I _ φ hφ χ n a hu hi hn ha
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hi' := GlobalTheory.Published.HeckeFEModel.hasInf_inv hi
  have hn' : ∃ i, -n i ≠ 0 := hn.imp fun i h => neg_ne_zero.2 h
  refine ⟨conductorNormalizedCompletedLFunction χ hu, conductorNormalizedCompletedLFunction χ⁻¹ hu', isCompletedL_completed hφ hu hi hn,
    isCompletedL_completed hφ hu' hi' hn', fun s => ?_⟩
  rw [L_shift χ a s, ← discrNormConductor_toHecke hu ha, completed_eq hφ hu hi hn hu' s, rootNumber_toHecke hφ hu hi ha]
  ring
end
end

theorem GlobalTheory.Top.heckeTateFE : GlobalTheory.Published.HeckeTateFunctionalEquation :=
  GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation

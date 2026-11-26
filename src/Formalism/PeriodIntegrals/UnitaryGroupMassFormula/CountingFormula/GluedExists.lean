module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GluedLatticeMassFormula
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanRankOneLine
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IsomFixIff
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeMapExtension
open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace OrbitSumPf

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

def split (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (hz0 : h1 z z ≠ 0) : VecSplit h1 (hPerp h1 z) where
  x₀ := z
  ι := (wPerp h1 z).subtype
  inj := Subtype.val_injective
  hx₀ := hz0
  isom := fun _ _ => rfl
  orth := fun a => a.2
  cover := fun v => ⟨h1 z v / h1 z z, ⟨v - (h1 z v / h1 z z) • z, by
      show h1 z (v - (h1 z v / h1 z z) • z) = 0
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz0, sub_self]⟩, by simp⟩

variable {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1}

theorem mul_mem_hz {σ τ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) (hτ : τ ∈ hz h1 z) : σ * τ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨mul_mem hσ.1 hτ.1, ?_⟩
  show σ (τ z) = z
  rw [hτ.2, hσ.2]

theorem inv_mem_hz {σ : V1 ≃ₗ[K] V1} (hσ : σ ∈ hz h1 z) : σ⁻¹ ∈ hz h1 z := by
  simp only [hz, Set.mem_setOf_eq] at *
  refine ⟨inv_mem hσ.1, ?_⟩
  show σ.symm z = z
  rw [LinearEquiv.symm_apply_eq, hσ.2]

variable (hz0 : h1 z z ≠ 0)

private theorem gmap_mul_lemma {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (a b : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (a * b) N = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b N) := by
  simp only [Formalism.HermitianLatticesTheory.gmap, ← Submodule.map_comp]
  rfl

theorem gmap_inv_gmap' {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (a : W ≃ₗ[K] W) (N : Submodule (𝓞 K) W) : Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a N) = N := by
  rw [← gmap_mul_lemma, inv_mul_cancel]
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem card_stabZ_conj {τ : V1 ≃ₗ[K] V1} (hτ : τ ∈ hz h1 z) (M : Submodule (𝓞 K) V1) :
    Nat.card (stabZ h1 z (Formalism.HermitianLatticesTheory.gmap τ M)) = Nat.card (stabZ h1 z M) := by
  apply Nat.card_congr
  refine
    { toFun := fun σ => ⟨τ⁻¹ * σ.1 * τ, ?_⟩
      invFun := fun σ => ⟨τ * σ.1 * τ⁻¹, ?_⟩
      left_inv := fun σ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun σ => Subtype.ext (by simp [mul_assoc]) }
  · obtain ⟨a1, a2⟩ := σ.2
    exact ⟨mul_mem_hz (mul_mem_hz (inv_mem_hz hτ) a1) hτ, by
      rw [gmap_mul_lemma, gmap_mul_lemma, a2, gmap_inv_gmap']⟩
  · obtain ⟨a1, a2⟩ := σ.2
    refine ⟨mul_mem_hz (mul_mem_hz hτ a1) (inv_mem_hz hτ), ?_⟩
    rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap', a2]

end OrbitSumPf

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace GluedLatticeMass

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

theorem z_ne_zero {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at hz0

theorem orthK_span (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) :
    Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z}) = wPerp h1 z := by
  ext x
  simp only [Formalism.L2.SG.Pf.Cnt.orthK, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H z (Submodule.mem_span_singleton_self z)
  · intro hx u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hx' : h1 z x = 0 := hx
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx', smul_zero]

theorem glueSet_iff {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) (Λ : Submodule (𝓞 K) V1) :
    Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) ↔
      IsGlueLat h1 z Λ := by
  have hz : z ≠ 0 := z_ne_zero hz0
  unfold Formalism.L2.SG.Pf.Cnt.GlueSet IsGlueLat
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hl, hu, he⟩
    have hzmem : z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K) := by
      rw [he]
      exact Submodule.mem_span_singleton_self z
    refine ⟨hl, hu, hzmem.1, fun c hc => ?_⟩
    have hcz : c • z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K) :=
      ⟨hc, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)⟩
    rw [he] at hcz
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hcz
    refine ⟨o, ?_⟩
    rw [← algebraMap_smul K o z] at ho
    exact (smul_left_injective K hz ho)
  · rintro ⟨hl, hu, hzΛ, hp⟩
    refine ⟨hl, hu, ?_⟩
    ext y
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨hyΛ, hyU⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyU
      obtain ⟨o, ho⟩ := hp c hyΛ
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ o (Submodule.mem_span_singleton_self z)
    · intro hy
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨Λ.smul_mem o hzΛ, ?_⟩
      rw [← algebraMap_smul K o z]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)

theorem isomFix_iff (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (g : V1 ≃ₗ[K] V1) :
    g ∈ Formalism.L2.SG.Pf.Cnt.isomFix h1 (Submodule.span K {z}) ↔ g ∈ hz h1 z := by
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, hfix z (Submodule.mem_span_singleton_self z)⟩
  · rintro ⟨hg, hfz⟩
    refine ⟨hg, fun u hu => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, hfz]

theorem stabFix_eq (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (Λ : Submodule (𝓞 K) V1) :
    Formalism.L2.SG.Pf.Cnt.stabFix h1 (Submodule.span K {z}) Λ = stabZ h1 z Λ := by
  ext g
  exact and_congr (isomFix_iff h1 z g) Iff.rfl

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3 GluedLatticeMass OrbitSumPf

namespace GluedLatticeMass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

theorem vF_neg (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : vF 𝔭 (-n) = vF 𝔭 n := by
  unfold vF
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq, neg_mem_iff]

theorem vF_eq_vT {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : ℕ} (ht : 0 < t) :
    vF 𝔭 ((t : ℕ) : 𝓞 F) = vT F t 𝔭 := by
  have ht0 : ((t : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast ht.ne'
  have hI : Ideal.span {((t : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht0
  have hne : 𝔭 ≠ ⊥ := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.ne_bot h𝔭
  have hp : Prime 𝔭 := Ideal.prime_of_isPrime hne h𝔭.isPrime
  rw [Formalism.L2.SG.Pf.G1.vF_eq_multiplicity h𝔭 ht0, vT,
    UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hp.irreducible, normalize_eq]

theorem nondeg {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hH : GlueHyp K F h1 z t) :
    Formalism.L2.SG.Pf.Cnt.Nondeg h1 := by
  obtain ⟨_, _, hs, hzz, ht, hd⟩ := hH
  have hz0 : h1 z z ≠ 0 := by
    rw [hzz, neg_ne_zero]
    exact_mod_cast ht.ne'
  intro x hx
  obtain ⟨c, w, rfl⟩ := (split h1 z hz0).cover x
  have hwz : h1 w.1 z = 0 := by
    rw [← hs.eq z w.1]
    have : h1 z w.1 = 0 := w.2
    rw [this, map_zero]
  have e1 := hx z
  change h1 (c • z + w.1) z = 0 at e1
  rw [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hwz, add_zero,
    smul_eq_mul] at e1
  have hc : c = 0 := by
    have h2 : (starRingEnd K) c = 0 := (mul_eq_zero.1 e1).resolve_right hz0
    simpa using h2
  subst hc
  have e2 := hx w.1
  change h1 ((0 : K) • z + w.1) w.1 = 0 at e2
  rw [zero_smul, zero_add] at e2
  by_contra hx0
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hx0
    change (0 : K) • z + ((0 : wPerp h1 z) : V1) = 0
    simp
  have hpos := hd w hw0 (Classical.arbitrary (K →+* ℂ))
  have e3 : hPerp h1 z w w = 0 := e2
  rw [e3, map_zero] at hpos
  simp at hpos

theorem isCompl_span {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) :
    IsCompl (Submodule.span K {z}) (wPerp h1 z) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : h1 z (c • z) = 0 := hxw
    rw [map_smul, smul_eq_mul] at this
    rw [(mul_eq_zero.1 this).resolve_right hz0, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨c, w, rfl⟩ := (split h1 z hz0).cover x
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)) w.2

theorem jordan_rank_one_line {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hzz : h1 z z = -((t : ℕ) : K))
    (ht : 0 < t) (hz : z ≠ 0) (𝔭 : Ideal (𝓞 F)) :
    Formalism.L2.SG.Pf.Cnt.IsJordanIn h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭
      (fun _ => z) (fun _ => -((t : ℕ) : 𝓞 F)) := by
  have h1r : finrank K (Submodule.span K {z}) = 1 := finrank_span_singleton hz
  have hne : Nonempty (Fin (finrank K (Submodule.span K {z}))) := by
    rw [h1r]
    exact ⟨0⟩
  refine ⟨fun _ => Submodule.mem_span_singleton_self z, ?_, ?_, ?_, ?_⟩
  · rw [Set.range_const]
  · intro i j hij
    exfalso
    apply hij
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_eq i.2 h1r
    have hj : j.val < 1 := lt_of_lt_of_eq j.2 h1r
    omega
  · intro i
    rw [hzz]
    simp
  · intro i
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    exact ht.ne'

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3 GluedLatticeMass OrbitSumPf
open Formalism.L2.SG.Pf.Cnt (cMass)

namespace GluedLatticeMass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

theorem sum_reps_eq {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {s s' : Finset (Submodule (𝓞 K) V1)}
    (hs : IsHzReps h1 z s) (hs' : IsHzReps h1 z s') :
    ∑ M ∈ s, ((Nat.card (stabZ h1 z M) : ℕ) : ℝ)⁻¹ = ∑ M ∈ s', ((Nat.card (stabZ h1 z M) : ℕ) : ℝ)⁻¹ := by
  have ex : ∀ {A B : Finset (Submodule (𝓞 K) V1)}, IsHzReps h1 z A → IsHzReps h1 z B →
      ∀ M ∈ A, ∃ M' ∈ B, ∃ σ ∈ hz h1 z, Formalism.HermitianLatticesTheory.gmap σ M' = M := by
    intro A B hA hB M hM
    obtain ⟨M', ⟨hM', σ, hσ, e⟩, -⟩ := hB.2 M (hA.1 M hM)
    exact ⟨M', hM', σ, hσ, e⟩
  choose i hi σi hσi ei using ex hs hs'
  choose j hj σj hσj ej using ex hs' hs
  refine Finset.sum_bij' i j hi hj ?_ ?_ ?_
  · intro M hM
    have hu := hs.2 (i M hM) (hs'.1 _ (hi M hM))
    refine hu.unique ⟨hj _ (hi M hM), σj _ (hi M hM), hσj _ _, ej _ _⟩
      ⟨hM, (σi M hM)⁻¹, inv_mem_hz (hσi M hM),
        (congrArg (Formalism.HermitianLatticesTheory.gmap (σi M hM)⁻¹) (ei M hM)).symm.trans (gmap_inv_gmap' _ _)⟩
  · intro M hM
    have hu := hs'.2 (j M hM) (hs.1 _ (hj M hM))
    refine hu.unique ⟨hi _ (hj M hM), σi _ (hj M hM), hσi _ _, ei _ _⟩
      ⟨hM, (σj M hM)⁻¹, inv_mem_hz (hσj M hM),
        (congrArg (Formalism.HermitianLatticesTheory.gmap (σj M hM)⁻¹) (ej M hM)).symm.trans (gmap_inv_gmap' _ _)⟩
  · intro M hM
    rw [← card_stabZ_conj (hσi M hM) (i M hM), ei M hM]

theorem alphaStd_ratio (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) :
    alphaStd K 𝔭 k / alphaStd K 𝔭 (k - 1) = 1 - etaF K F 𝔭 ^ k * (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpos := alphaStd_pos hK hF h𝔭 j
  rw [Nat.add_sub_cancel]
  unfold alphaStd at hpos ⊢
  rw [Finset.prod_Icc_succ_top (by omega), mul_div_cancel_left₀ _ hpos.ne']

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glued_lattice_mass_formula {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hH : GlueHyp K F h1 z t)
    (hk : 1 ≤ finrank K (wPerp h1 z)) (hne : ∃ M, IsGlueLat h1 z M) {s : Finset (Submodule (𝓞 K) V1)}
    (hs : IsHzReps h1 z s) :
    ∑ M ∈ s, ((Nat.card (stabZ h1 z M) : ℕ) : ℝ)⁻¹ =
      cMass K F (finrank K (wPerp h1 z)) * (t : ℝ) ^ (finrank K (wPerp h1 z) * finrank ℚ F) *
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
          (if ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 then
            1 - etaF K F 𝔭.1 ^ finrank K (wPerp h1 z) *
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K (wPerp h1 z) : ℤ)) else 1) := by
  have hH' := hH
  obtain ⟨hK, hF, hsym, hzz, ht, hd⟩ := hH'
  have hz0 : h1 z z ≠ 0 := by
    rw [hzz, neg_ne_zero]
    exact_mod_cast ht.ne'
  have hz : z ≠ 0 := z_ne_zero hz0
  set k := finrank K (wPerp h1 z) with hkdef
  have hC : IsCompl (Submodule.span K {z}) (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    exact isCompl_span hz0
  have hP : Formalism.L2.SG.Pf.Cnt.PosDefOn h1 (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    intro x hx hx0 φ
    exact hd ⟨x, hx⟩ (fun h => hx0 (congrArg Subtype.val h)) φ
  have hLat : Formalism.L2.SG.Pf.Cnt.IsLatIn (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) :=
    ⟨Submodule.fg_span_singleton z, Submodule.span_span_of_tower (𝓞 K) K {z}⟩
  have hInt : Formalism.HermitianLatticesTheory.IsIntegralLat h1 (Submodule.span (𝓞 K) {z}) := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hzz]
    obtain ⟨c, hc⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range (K := K) a
    rw [← hc]
    refine Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem c)
      (Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) ?_)
    rw [Submodule.mem_one]
    exact ⟨-((t : ℕ) : 𝓞 K), by simp⟩
  have hGS : (Formalism.L2.SG.Pf.Cnt.GlueSet h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z})).Nonempty := by
    obtain ⟨M, hM⟩ := hne
    exact ⟨M, (glueSet_iff hz0 M).2 hM⟩
  have hMC : MassConst K F (finrank K (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z}))) (cMass K F k) := by
    rw [orthK_span]
    exact massConst_cMass hK hF k hk
  obtain ⟨s', hs'1, hs'2, -, hsum⟩ := Formalism.L2.SG.Pf.Cnt.gluing_mass_holds K F V1 hK hF h1 hsym (nondeg hH)
    _ hC hP _ hLat hInt hGS (cMass K F k) hMC
  have hs' : IsHzReps h1 z s' := by
    refine ⟨fun M hM => (glueSet_iff hz0 M).1 (hs'1 M hM), fun M hM => ?_⟩
    obtain ⟨Λ₁, ⟨h1s, g, hg, e⟩, hu⟩ := hs'2 M ((glueSet_iff hz0 M).2 hM)
    exact ⟨Λ₁, ⟨h1s, g, (isomFix_iff h1 z g).1 hg, e⟩,
      fun Λ₂ ⟨h2s, g2, hg2, e2⟩ => hu Λ₂ ⟨h2s, g2, (isomFix_iff h1 z g2).2 hg2, e2⟩⟩
  rw [sum_reps_eq hs hs']
  simp only [stabFix_eq] at hsum
  rw [hsum, orthK_span]

  have hJ : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      Formalism.L2.SG.Pf.Cnt.vJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭.1 = vT F t 𝔭.1 ∧
      Formalism.L2.SG.Pf.Cnt.cJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭.1 =
        if ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 then 1 else 0 := by
    intro 𝔭
    have h1r : finrank K (Submodule.span K {z}) = 1 := finrank_span_singleton hz
    obtain ⟨e1, e2⟩ := Formalism.L2.SG.Pf.G9.vJ_cJ_eq Formalism.L2.SG.Pf.Cnt.jordan_invariants_holds hK hF hsym hLat 𝔭.2
      (jordan_rank_one_line hzz ht hz 𝔭.1)
    have hv : vF 𝔭.1 (-((t : ℕ) : 𝓞 F)) = vT F t 𝔭.1 := by rw [vF_neg, vF_eq_vT 𝔭.2 ht]
    refine ⟨?_, ?_⟩
    · rw [e1]
      unfold Formalism.L2.SG.Pf.Cnt.vJof
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, h1r, one_smul, hv]
    · rw [e2]
      unfold Formalism.L2.SG.Pf.Cnt.cJof
      have ht0 : ((t : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast ht.ne'
      have hiff : vF 𝔭.1 (-((t : ℕ) : 𝓞 F)) ≠ 0 ↔ ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 := by
        rw [vF_neg, ← Nat.one_le_iff_ne_zero, ← Formalism.L2.SG.Pf.G1.mem_pow_iff 𝔭.2 ht0 1, pow_one]
      by_cases h : ((t : ℕ) : 𝓞 F) ∈ 𝔭.1
      · rw [if_pos h, Finset.filter_true_of_mem (fun i _ => hiff.2 h), Finset.card_univ,
          Fintype.card_fin, h1r]
      · rw [if_neg h, Finset.filter_false_of_mem (fun i _ => fun hh => h (hiff.1 hh)),
          Finset.card_empty]
  have hnM : Formalism.L2.SG.Pf.Cnt.nM F h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) =
      (t : ℝ) ^ finrank ℚ F := by
    unfold Formalism.L2.SG.Pf.Cnt.nM
    have e := tprod_supT (F := F) ht (fun P => (Ideal.absNorm P : ℝ) ^ vT F t P)
    beta_reduce at e
    rw [← prod_absNorm_pow ht, ← e]
    refine tprod_congr fun 𝔭 => ?_
    rw [(hJ 𝔭).1]
    by_cases h : ((t : ℕ) : 𝓞 F) ∈ 𝔭.1
    · rw [if_pos h]
    · rw [if_neg h, ← vF_eq_vT 𝔭.2 ht, Formalism.L2.SG.Pf.G1.vF_of_notMem 𝔭.2 h, pow_zero]
  have hratio : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 k /
      alphaStd K 𝔭.1 (k - Formalism.L2.SG.Pf.Cnt.cJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭.1)) =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (if ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 then
        1 - etaF K F 𝔭.1 ^ k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) else 1) := by
    refine tprod_congr fun 𝔭 => ?_
    rw [(hJ 𝔭).2]
    by_cases h : ((t : ℕ) : 𝓞 F) ∈ 𝔭.1
    · rw [if_pos h, if_pos h, alphaStd_ratio hK hF 𝔭.2 hk]
    · rw [if_neg h, if_neg h, Nat.sub_zero, div_self (alphaStd_pos hK hF 𝔭.2 k).ne']
  rw [hnM, hratio, ← pow_mul, mul_comm (finrank ℚ F) k]

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3 GluedLatticeMass OrbitSumPf

namespace GluedLatticeMass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glued_exists {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hH : GlueHyp K F h1 z t)
    (hk2 : 2 ≤ finrank K (wPerp h1 z))
    (hU0 : ∃ Λ₀ : Submodule (𝓞 K) V1, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h1 Λ₀) :
    ∃ M, IsGlueLat h1 z M := by
  have hH' := hH
  obtain ⟨hK, hF, hsym, hzz, ht, hd⟩ := hH'
  have hz0 : h1 z z ≠ 0 := by
    rw [hzz, neg_ne_zero]
    exact_mod_cast ht.ne'
  have hz : z ≠ 0 := z_ne_zero hz0
  have hC : IsCompl (Submodule.span K {z}) (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    exact isCompl_span hz0
  have hP : Formalism.L2.SG.Pf.Cnt.PosDefOn h1 (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    intro x hx hx0 φ
    exact hd ⟨x, hx⟩ (fun h => hx0 (congrArg Subtype.val h)) φ
  have hLat : Formalism.L2.SG.Pf.Cnt.IsLatIn (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) :=
    ⟨Submodule.fg_span_singleton z, Submodule.span_span_of_tower (𝓞 K) K {z}⟩
  have hInt : Formalism.HermitianLatticesTheory.IsIntegralLat h1 (Submodule.span (𝓞 K) {z}) := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hzz]
    obtain ⟨c, hc⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range (K := K) a
    rw [← hc]
    refine Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem c)
      (Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) ?_)
    rw [Submodule.mem_one]
    exact ⟨-((t : ℕ) : 𝓞 K), by simp⟩
  have hcJ : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      Formalism.L2.SG.Pf.Cnt.cJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭 <
        finrank K (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    intro 𝔭 h𝔭
    rw [orthK_span]
    have h1r : finrank K (Submodule.span K {z}) = 1 := finrank_span_singleton hz
    obtain ⟨-, e2⟩ := Formalism.L2.SG.Pf.G9.vJ_cJ_eq Formalism.L2.SG.Pf.Cnt.jordan_invariants_holds hK hF hsym hLat h𝔭
      (jordan_rank_one_line hzz ht hz 𝔭)
    rw [e2]
    have hle : Formalism.L2.SG.Pf.Cnt.cJof 𝔭
        (fun _ : Fin (finrank K (Submodule.span K {z})) => -((t : ℕ) : 𝓞 F)) ≤ 1 := by
      unfold Formalism.L2.SG.Pf.Cnt.cJof
      calc _ ≤ (Finset.univ : Finset (Fin (finrank K (Submodule.span K {z})))).card :=
            Finset.card_filter_le _ _
        _ = 1 := by rw [Finset.card_univ, Fintype.card_fin, h1r]
    omega
  obtain ⟨M, hM⟩ := Formalism.L2.SG.Pf.Cnt.glueExists_holds K F V1 hK hF h1 hsym (nondeg hH) _ hC hP hU0 _ hLat
    hInt hcJ
  exact ⟨M, (glueSet_iff hz0 M).1 hM⟩

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

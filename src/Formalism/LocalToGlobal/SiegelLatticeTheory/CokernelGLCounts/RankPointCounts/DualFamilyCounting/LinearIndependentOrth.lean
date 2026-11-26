module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetNeOfTotPos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_subset_span {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) V) :
    (locF 𝔭 L : Set V) ⊆ Submodule.span K (L : Set V) := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp L x).1 hx
  have ht0 : algebraMap F K (t : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero (ne_zero_of_notMem ht)
  have h1 : algebraMap F K (t : F) • x ∈ Submodule.span K (L : Set V) := by
    rw [← jι_eq', algebraMap_smul]; exact Submodule.subset_span htx
  exact (Submodule.smul_mem_iff _ ht0).1 h1

theorem le_span_of_locF {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {U : Submodule K V}
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {n : ℕ} {b : Fin n → V}
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 M) :
    U ≤ Submodule.span K (Set.range b) := by
  rw [← hM.2, Submodule.span_le]
  intro x hx
  have h1 : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]; exact LocF.le_locF 𝔭 M hx
  have h2 := locF_subset_span hp _ h1
  rwa [Submodule.span_span_of_tower] at h2

theorem linearIndependent_orth {m : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (w : Fin m → V)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) (hwn : ∀ j, h (w j) (w j) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := congrArg (h (w k)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hwo k j (Ne.symm hj), mul_zero])
    (by simp)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hwn k)

theorem family_top_holds : FamTop := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hw : ∀ j, w j ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hb : ∀ i, b i ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := by
    intro i
    have hg' : glueFam K 𝔭 b a π w τ (Sum.inl i) ∈
        Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := Submodule.subset_span ⟨Sum.inl i, rfl⟩
    simp only [glueFam, Sum.elim_inl] at hg'
    by_cases hi : vF 𝔭 (a i) = 0
    · rwa [if_pos hi] at hg'
    · rw [if_neg hi] at hg'
      have h0 : (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) ≠ 0 := by
        apply pow_ne_zero; apply inv_ne_zero; rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
      have h1 := (Submodule.smul_mem_iff _ h0).1 hg'
      have h2 := Submodule.sub_mem _ h1 (hw (τ i))
      rwa [add_sub_cancel_right] at h2
  have hU : U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (le_span_of_locF hp hM hbL) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i))
  have hli : LinearIndependent K w := linearIndependent_orth h w hwo fun j => by
    rw [(hwn j).1]; exact (map_ne_zero _).2 (hwn j).2
  have hle : Submodule.span K (Set.range w) ≤ orthK h U :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hwW j)
  have hfr : finrank K (Submodule.span K (Set.range w)) = finrank K (orthK h U) := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hW : orthK h U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (Submodule.eq_of_le_of_finrank_eq hle hfr).ge
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hw j))
  rw [eq_top_iff, ← hUc.sup_eq_top]
  exact sup_le hU hW

end Formalism.L2.SG.Pf.GluingBases
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TotallyPositiveAll
noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem emb_surj (D : Formalism.BasicNotions.D7) : Function.Surjective D.host.emb := by
  intro φ
  unfold Formalism.BasicNotions.Host.emb Formalism.BasicNotions.Host.sigmaOf

  have key : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, D.host.φ₀.comp (σ : D.host.E →+* D.host.E) = φ := by
    classical
    let f : (D.host.E ≃ₐ[ℚ] D.host.E) → (D.host.E →ₐ[ℚ] ℂ) :=
      fun σ => (D.host.φ₀.toRatAlgHom).comp (σ : D.host.E →ₐ[ℚ] D.host.E)
    have hinj : Function.Injective f := by
      intro σ τ h
      ext x
      have h1 : D.host.φ₀ (σ x) = D.host.φ₀ (τ x) := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) h
      exact D.host.φ₀.injective h1
    have hcard : Fintype.card (D.host.E ≃ₐ[ℚ] D.host.E) = Fintype.card (D.host.E →ₐ[ℚ] ℂ) := by
      haveI : IsGalois ℚ D.host.E := inferInstance
      rw [AlgHom.card ℚ D.host.E ℂ, ← IsGalois.card_aut_eq_finrank ℚ D.host.E, Fintype.card_eq_nat_card]
    obtain ⟨σ, hσ⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 φ.toRatAlgHom
    refine ⟨σ, ?_⟩
    ext x
    have h2 : D.host.φ₀ (σ x) = φ x := congrArg (fun g : D.host.E →ₐ[ℚ] ℂ => g x) hσ
    exact h2
  obtain ⟨σ, hσ⟩ := key
  refine ⟨D.host.gal σ, ?_⟩
  simp only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact hσ

theorem totally_positive_all : TotPosAll := by
  intro D x hx hpos φ
  obtain ⟨g, rfl⟩ := emb_surj D φ
  by_cases hg : g ∈ D.R.Psi
  · have h1 := hpos (D.eTau.symm ⟨g, hg⟩)
    simpa using h1
  · have hmem : g * D.R.cc ∈ D.R.Psi := by
      rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
      have h2 : g.1.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
      rw [Prod.fst_mul, Prod.snd_mul, h2]
      first
        | rfl
        | decide
        | (simp [Formalism.HC.Frame.cc]; done)
        | (simp [Formalism.HC.Frame.cc, Formalism.HC.c0])
    have h1 := hpos (D.eTau.symm ⟨g * D.R.cc, hmem⟩)
    simp only [Equiv.apply_symm_apply] at h1
    have hc : D.host.conj x = x := (Formalism.MainNotions.S.Inh.tie_star D x).symm.trans hx
    have he : D.host.emb (g * D.R.cc) x = D.host.emb g x := by
      change D.host.φ₀ ((D.host.gal.symm (g * D.R.cc)) x) = D.host.φ₀ ((D.host.gal.symm g) x)
      rw [map_mul, AlgEquiv.mul_apply]
      congr 2
    rw [he] at h1
    exact h1

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem rational_pair_holds : RatPair := ratPair_of R1.totally_positive_all

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def LastUnit : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∀ j : Fin (finrank K (orthK h U)), (j : ℕ) + 1 = finrank K (orthK h U) →
      ∃ l : K, l ≠ 0 ∧ InP 𝔭 0 (algebraMap F K (c j) * (l * star l)) ∧
        InP 𝔭 0 (algebraMap F K (c j) * (l * star l))⁻¹

theorem lastRescale_of (hL : LastUnit) : LastRescale := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  have hm : 0 < finrank K (orthK h U) := lt_of_le_of_lt (Nat.zero_le _) hc
  set j₀ : Fin (finrank K (orthK h U)) := ⟨finrank K (orthK h U) - 1, by omega⟩ with hj₀
  obtain ⟨l, hl0, hl1, hl2⟩ :=
    hL K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg j₀ (by simp [j₀]; omega)
  obtain ⟨hwW, hwo, hwn, hτ, hu, hcong, hτl, hunit⟩ := hg
  obtain ⟨μ, hμ⟩ := (hF (l * star l)).1 (by rw [star_mul', star_star, mul_comm])
  have hμ0 : μ ≠ 0 := by
    intro e; rw [e, map_zero] at hμ
    exact mul_ne_zero hl0 (star_ne_zero.2 hl0) hμ.symm
  let w' := Function.update w j₀ (l • w j₀)
  let c' := Function.update c j₀ (μ * c j₀)
  have hw'₀ : w' j₀ = l • w j₀ := Function.update_self _ _ _
  have hw'n : ∀ j, j ≠ j₀ → w' j = w j := fun j hj => Function.update_of_ne hj _ _
  have hc'₀ : c' j₀ = μ * c j₀ := Function.update_self _ _ _
  have hc'n : ∀ j, j ≠ j₀ → c' j = c j := fun j hj => Function.update_of_ne hj _ _
  have hτ₀ : ∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j₀ := by
    intro i hi e
    have := hτl i hi
    rw [e] at this
    simp [j₀] at this
    omega
  refine ⟨w', c', ⟨?_, ?_, ?_, hτ, hu, ?_, ?_⟩⟩
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀]; exact Submodule.smul_mem _ _ (hwW j₀)
    · rw [hw'n j hj]; exact hwW j
  · intro j k hjk
    by_cases hj : j = j₀
    · have hk : k ≠ j₀ := fun e => hjk (hj.trans e.symm)
      rw [hj, hw'₀, hw'n k hk, form_smul_left, hwo _ _ (hj ▸ hjk), mul_zero]
    · by_cases hk : k = j₀
      · rw [hk, hw'₀, hw'n j hj, form_smul_right, hwo _ _ (hk ▸ hjk), mul_zero]
      · rw [hw'n j hj, hw'n k hk]; exact hwo j k hjk
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀, hc'₀, form_smul_smul, (hwn j₀).1, map_mul, hμ]
      refine ⟨by ring, mul_ne_zero hμ0 (hwn j₀).2⟩
    · rw [hw'n j hj, hc'n j hj]; exact hwn j
  · intro i hi
    rw [hc'n _ (hτ₀ i hi)]; exact hcong i hi
  · intro j hnp
    by_cases hj : j = j₀
    · rw [hj, hc'₀]
      refine ⟨?_, ?_⟩
      · rw [map_mul, hμ, mul_comm]; exact hl1
      · rw [map_inv₀, map_mul, hμ, mul_comm]; exact hl2
    · rw [hc'n j hj]
      refine hunit j ?_ hnp
      have h1 := j.isLt
      have h2 : (j : ℕ) ≠ finrank K (orthK h U) - 1 := fun e => hj (Fin.ext e)
      omega

end Formalism.L2.SG.Pf.GluingBases
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.SdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
  PI.UnitaryGroupMassFormula.LocJacTyp.Sd.finDim

theorem boxScaleL_holds : BoxScaleL := by
  intro F E _ _ _ _ _ v ι _ hE μ _ x hx
  classical
  let z : ι → Fv F v ⊗[F] E := fun i => LocVol.sc v (x i)
  let f := PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v z
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hdet : LinearMap.det f = ∏ i, x i ^ 2 := by
    have hdet_norm : LinearMap.det f = ∏ i, Algebra.norm (Fv F v) (z i) := by
      unfold f PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL
      rw [LinearMap.det_pi]
      simp only [Algebra.norm_apply]
    rw [hdet_norm]
    refine Finset.prod_congr rfl fun i _ => ?_
    change Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) (x i)) = _
    rw [Algebra.norm_algebraMap, hrank]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hx i)
  set S := Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | LocVol.sc v (x i) * c ∈ LocVol.OEv v} with hSdef
  have hpre : S = f ⁻¹' (Set.univ.pi fun _ : ι => LocVol.OEv v) := by
    ext y
    simp [S, f, z, PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
  have hcont : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hS : MeasurableSet S := by
    rw [hpre]
    refine (IsOpen.preimage hcont ?_).measurableSet
    exact isOpen_set_pi Set.finite_univ fun i _ => PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v
  have himg : f '' S = Set.univ.pi fun _ : ι => LocVol.OEv v := by
    rw [hpre, Set.image_preimage_eq]
    intro y
    refine ⟨fun i => ((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i, ?_⟩
    funext i
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
    change (x i ⊗ₜ[F] (1 : E)) * (((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i) = y i
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hx i), one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  let b := Module.finBasis (Fv F v) (ι → Fv F v ⊗[F] E)
  let e0 := b.equivFun
  let e : (ι → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have h := hLM (Fv F v) (ι → Fv F v ⊗[F] E) (Fin _) ⟨e⟩ f hdet0 μ inferInstance S hS
  have hne : (∏ i, x i ^ 2) ≠ 0 := hdet ▸ hdet0
  rw [himg, hdet, PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hne, PI.UnitaryGroupMassFormula.LocJacTyp.BM.absV_prod] at h
  have hpos : ∀ i, 0 < PI.LocJacTyp.absV v (x i) := fun i => PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v (hx i)
  have hP : 0 < ∏ i, PI.LocJacTyp.absV v (x i ^ 2) :=
    Finset.prod_pos fun i _ => by rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow]; exact pow_pos (hpos i) 2
  have hR := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hP.le] at hR
  change (μ S).toReal = (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ∏ i, (PI.LocJacTyp.absV v (x i) ^ 2)⁻¹
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _ at hR
  rw [hR, Finset.prod_inv_distrib]
  simp_rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow] at hP ⊢
  field_simp

theorem sdFromAnn_holds : SdFromAnn := by
  intro F E _ _ _ _ _ ψ v d _ hE hd hann ι _
  classical
  have hone : (1 : Fv F v ⊗[F] E) ∈ PI.LocJacTyp.OEv v := by
    simpa using PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hinv : LocVol.sc v d * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
    change (d ⊗ₜ[F] (1 : E)) * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hd, one_mul,
      ← Algebra.TensorProduct.one_def]
  have hker : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ := by
    refine PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ (2 * d⁻¹) (mul_ne_zero two_ne_zero (inv_ne_zero hd)) ?_
    intro c hc
    have h1 := (hann (d⁻¹ ⊗ₜ[F] (1 : E))).mpr (by rw [hinv]; exact hone)
    have h2 := h1 (c • (1 : Fv F v ⊗[F] E)) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.oev_smul v hc hone)
    have htr : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E)))
        = c * (2 * d⁻¹) := by
      have : c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E))
          = algebraMap (Fv F v) (Fv F v ⊗[F] E) (c * d⁻¹) := by
        rw [Algebra.smul_def, mul_one, map_mul]; rfl
      rw [this, Algebra.trace_algebraMap, hrank]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [← htr]; exact h2
  have hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1 := by
    by_contra hall
    push_neg at hall
    obtain ⟨t0, ht0⟩ := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v
    have h1 := (hann ((d⁻¹ ⊗ₜ[F] (1 : E)) * t0)).mp (fun x _ => hall _)
    rw [← mul_assoc, hinv, one_mul] at h1
    exact ht0 h1
  obtain hex := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hker hnt ι
  have hμ : LocVol.sdE ψ v ι = hex.choose := by
    change PI.LocJacTyp.sdE ψ v ι = _
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq, dite_eq_left hex]
  have hsd := hex.choose_spec
  rw [hμ]
  haveI : hex.choose.IsAddHaarMeasure := hsd.1
  refine ⟨hsd.1, inferInstance, ?_⟩
  set μ := hex.choose
  have hDopen := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_dbox (E := E) v ψ hker ι
  have hDcpt := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_dbox (E := E) v ψ hker hnt ι
  have htest := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test v ψ ι μ hsd hDopen.measurableSet hDcpt.measure_lt_top
  have hD : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox v ψ ι
      = Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | LocVol.sc v d * c ∈ LocVol.OEv v} := by
    ext y
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => hann (y i)
  have hbs := boxScaleL_holds v ι hE μ (fun _ => d) (fun _ => hd)
  rw [← hD] at hbs
  simp only [Measure.real] at htest
  rw [hbs] at htest
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ((μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
      ∏ _i : ι, (PI.LocJacTyp.absV v d ^ 2)⁻¹) = 1 at htest
  set a := (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal
  have hpos : 0 < PI.LocJacTyp.absV v d := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hd
  rw [Finset.prod_const, Finset.card_univ] at htest
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hsq : a ^ 2 = (PI.LocJacTyp.absV v d ^ Fintype.card ι) ^ 2 := by
    have hq : 0 < ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι := by positivity
    have : a ^ 2 * ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι = 1 := by
      rw [← htest]; ring
    rw [inv_pow, ← pow_mul] at this
    field_simp at this
    rw [this]; ring
  exact (pow_left_inj₀ ha (pow_nonneg hpos.le _) two_ne_zero).mp hsq

end Formalism.L2.SG.Pf.NcVal.SdW
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVTop
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem unramAt_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) : UnramAt (E := E) v := by
  intro P hP hP0 _
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  let c : Gal(E/F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => (hc.fixed (algebraMap F E r)).2 ⟨r, rfl⟩)
  haveI : P.LiesOver (P.under (𝓞 F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 F) hP0
  have hcard : Nat.card (P.inertia Gal(E/F)) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P Gal(E/F)]
  by_contra hne
  have hG : Nat.card Gal(E/F) = 2 := by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hc.deg2)
      | (rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]; exact hc.deg2)
  haveI : Fact (Nat.card Gal(E/F)).Prime := ⟨by rw [hG]; exact Nat.prime_two⟩
  have htop : P.inertia Gal(E/F) = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (P.inertia Gal(E/F)) with h | h
    · exfalso
      apply hne
      rw [← hcard, h]
      simp
    · exact h
  have hcI : c ∈ P.inertia Gal(E/F) := htop ▸ Subgroup.mem_top c
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P (hP.isMaximal hP0)
  apply hθ
  have h1 := hcI θ
  have e : c • θ = t := by
    apply RingOfIntegers.coe_injective
    rw [ht]
    rfl
  rw [e] at h1
  have : θ - t = -(t - θ) := by ring
  rw [this]
  exact P.neg_mem h1

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omega_standard_holds : OmVStd X ψ := by
  intro h1 h2
  refine ⟨?_, ?_, h1, h2⟩
  · unfold IsCMExt
    refine ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, ?_⟩
    exact fun τ x => X.B.I.cm.cmUnram.2.1 τ x
  · unfold IsHermND
    have hH := X.B.I.J_herm
    unfold Formalism.UG.IsHerm at hH
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have h3 := congrFun (congrFun hH i) j
    exact h3

theorem omega_lattice_holds : OmVLat X := ⟨X.B.I.L, Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg, rfl⟩

theorem omega_unramified_holds : OmVUnram X := fun v => unramAt_of_cm X.B.I.cm v

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArithG
noncomputable section

namespace Formalism.L2.SG.Pf.NcArithG

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem rm_eq (D : D7) : D.R.m = 2 * (D.R.rS + 1) := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  show D.R.m = 2 * (D.R.m / 2 - 1 + 1)
  omega

theorem cMass_succ {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (k : ℕ) (hk : 2 ≤ k) :
    Formalism.L2.SG.Pf.Cnt.cMass K F k = Formalism.L2.SG.Pf.Cnt.cMass K F (k - 1) * Formalism.HermitianLatticesTheory.massRatioRightSide K k := by
  unfold Formalism.L2.SG.Pf.Cnt.cMass
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.prod_Icc_succ_top (by omega), Nat.add_sub_cancel, mul_assoc]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncValueC_of_global (a' Ω ATyp A' AT PT : ℝ)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (ha : 0 < a') (hATyp : 0 < ATyp) (hA' : 0 < A') (hPT : 0 < PT)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * Ω)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Module.finrank ℚ D.host.F) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Module.finrank ℚ D.host.F *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Module.finrank ℚ D.host.F : ℕ) : ℤ)) *
        |(NumberField.discr D.host.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F))
    (hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp)
    (hG3 : Ω = |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A')
    (hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A')
    (hG5 : AT * ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i = PT)
    (hRM : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
      Formalism.L2.SG.Pf.Cnt.cMass D.host.E D.host.F D.R.k * ((Tw u : ℕ) : ℝ) ^ (D.R.k * Module.finrank ℚ D.host.F) * PT)
    (hV : Formalism.HermitianLatticesTheory.vInv D.host.E =
      |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2)
    (hfE : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F)
    (hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1))) :
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by

  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  set dd : ℝ := |(NumberField.discr D.host.F : ℝ)| with hdd
  set f : ℕ := Module.finrank ℚ D.host.F with hfdef
  set k : ℕ := D.R.k with hkdef
  set s : ℕ := D.R.rS with hsdef
  set gg : ℝ := ((Lat.gS D : ℕ) : ℝ) with hgg
  set TT : ℝ := ((Tw u : ℕ) : ℝ) with hTT
  set Lk : ℝ := ∏ i ∈ Finset.Icc (k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hLk
  have hm : D.R.m = 2 * (s + 1) := rm_eq D
  have hk5 : D.R.m + 3 ≤ k := D.R.m_add_three_le_k
  have hk2 : 2 ≤ k := by omega
  have hr : D.R.r = k + 2 * s + 1 := by
    show D.R.k + D.R.m - 1 = k + 2 * s + 1
    omega
  have hf : 0 < f := Module.finrank_pos
  have hdpos : 0 < dd := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hgpos : 0 < gg := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    rw [hgg]
    unfold Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  have hTpos : 0 < TT := by rw [hTT]; exact_mod_cast (D.mem u).A.T_prime.pos

  obtain ⟨hp, hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZZ, hPP, hal, -⟩ := hP
  have hKp : ∀ p, 0 < B.μKp p := fun p => (hp p).2.2.2.2.2.1
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => hKp p)

  have hLkpos : 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc k hk2
  have hLkk : 0 < Lk := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi2
  have hcm := (Formalism.L2.SG.Pf.Asm.cMass_spec hKc hFc (k - 1) (by omega)).1
  have hIcc : (∏ i ∈ Finset.Icc k D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i) =
      Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k * Lk := by
    have hIo : Finset.Ioc k D.R.r = Finset.Icc (k + 1) D.R.r := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [Finset.Icc_eq_cons_Ioc (show k ≤ D.R.r by omega), Finset.prod_cons, hLk, hIo]

  have hvI : 2 * Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) := by rw [hV]; ring
  have hvIpos : 0 < Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [hV]; positivity
  have hpow1 : (dd ^ ((1 : ℝ) / f)) ^ f = dd := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
    rw [show (1 : ℝ) / f * (f : ℝ) = 1 by field_simp]
    exact Real.rpow_one dd
  have hsq : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ f) = dd ^ ((1 : ℝ) / 2) := by
    rw [hvI, hpow1, Real.sqrt_eq_rpow]
  have hvk : (Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (k * f) = dd ^ (k : ℝ) / 2 ^ (k * f) := by
    have h2 : Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) / 2 := by rw [hV]
    rw [h2, div_pow, pow_mul', hpow1, Real.rpow_natCast]

  set e : ℝ := -(8 * (s : ℝ) ^ 3 + 6 * (s : ℝ) ^ 2 + 6 * k * (s : ℝ) ^ 2 + s) / 3 with he
  set Xe : ℝ := ((s : ℝ) + 1) * (8 * (s : ℝ) ^ 2 + 10 * s + 3) / 3 with hXe
  set e2 : ℝ := (D.R.r : ℝ) * (2 * s + 1) - ((2 * (s : ℝ) + 1) ^ 2) / 2 with he2
  set E1 : ℝ := -((2 * s * (s + 1) * (k - 1) : ℕ) : ℝ) + 1 / 2 - k with hE1
  have hrR : (D.R.r : ℝ) = k + 2 * s + 1 := by rw [hr]; push_cast; ring
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hexp : e = E1 - Xe + e2 := by
    rw [he, hE1, hXe, he2, hrR]
    push_cast
    rw [hk1]
    ring
  have hde : dd ^ e = dd ^ E1 * (dd ^ Xe)⁻¹ * dd ^ e2 := by
    rw [hexp, Real.rpow_add hdpos, Real.rpow_sub hdpos, div_eq_mul_inv]
  have hdE1 : dd ^ E1 = dd ^ ((-((2 * s * (s + 1) * (k - 1) : ℕ) : ℤ) : ℤ) : ℝ) * dd ^ ((1 : ℝ) / 2) *
      (dd ^ (k : ℝ))⁻¹ := by
    rw [hE1, ← Real.rpow_neg hdpos.le, ← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
    congr 1
    push_cast
    ring

  have hgc : gg ^ ((s + 1) * (2 * s + 3) * f) * gg ^ (D.R.m * f * (k - 1)) =
      gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f) := by
    rw [← pow_add]
    congr 1
    rw [hm]
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    ring
  have hgpow : gg ^ (-(((s + 1) * (2 * k + 2 * s + 1) * f : ℕ) : ℤ)) =
      (gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hTpow : TT ^ (-((k * f : ℕ) : ℤ)) = (TT ^ (k * f))⁻¹ := by rw [zpow_neg, zpow_natCast]

  have hal : B.al = AT * A' / ATyp := by rw [eq_div_iff hATyp.ne']; exact hG4
  have hAT : AT = PT / Lk := by rw [eq_div_iff hLkk.ne']; exact hG5
  have hratio : Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k =
      ((Nat.factorial (k - 1) : ℝ) ^ f * (dd ^ (k : ℝ) / 2 ^ (k * f)) / Real.pi ^ (k * f)) /
        dd ^ ((1 : ℝ) / 2) * Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [hfE, hsq, Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2, mul_pow, ← pow_mul, div_pow, hvk]
    ring
  have hratio_pos : 0 < Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k := Formalism.HermitianLattices.Ext.L3.massRatio_pos hKc k hk2

  have hKrat : B.μKnat / B.μH' = (B.μKnat / B.μK) * (Ω / a') := by
    have h1 : B.μK / B.μH' = Ω / a' := by
      rw [div_eq_div_iff hH'.ne' ha.ne']
      linarith [hS]
    rw [← h1]
    field_simp
  unfold Formalism.L2.SG.Pf.NcAsm.NcValueC
  rw [← hB]
  calc _ = dd ^ E1 * 2 ^ (k * f) * (Real.pi ^ k / (Nat.factorial (k - 1) : ℝ)) ^ f * TT ^ (-((k * f : ℕ) : ℤ)) *
          A' / ATyp := by
        unfold Formalism.L2.SG.Pf.Cnt.cExpl
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        rw [hIcc, hRM, cMass_succ k hk2, hratio, hal, hAT, hdE1,
          ← Real.rpow_intCast dd, hTpow, div_pow, ← pow_mul]
        have hpi : 0 < Real.pi := Real.pi_pos
        have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
        field_simp
    _ = Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' *
          ngFac D := by
        rw [show Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat /
            B.μH' * ngFac D = (Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN') *
            (B.unitLevelVolume / B.volZZ) * (B.μKnat / B.μH') * ngFac D by ring]
        rw [hR, hG1, hKrat, hG2, hG3, hng]
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        try rw [← hgg]
        try rw [← hTT]
        rw [hde, hgpow, Real.rpow_neg hdpos.le]
        rw [← hgc]
        have hX : 0 < dd ^ Xe := Real.rpow_pos_of_pos hdpos _
        have he2p : 0 < dd ^ e2 := Real.rpow_pos_of_pos hdpos _
        have hgA : 0 < gg ^ ((s + 1) * (2 * s + 3) * f) := pow_pos hgpos _
        have hgC : 0 < gg ^ (D.R.m * f * (k - 1)) := pow_pos hgpos _
        field_simp

end Formalism.L2.SG.Pf.NcArithG
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MmIntOfEZ
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmInt_of_EZ {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hR : IsRowReps D F0 what₂)
    {Z : MatZ D} {F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')} (hz : F'.zt = F'.fl.z) (hZ : ZhatL (lf D F0) F' = Z)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z)) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : IsRowLat D F0 Λ) (hE : F' ∈ EZ (Tn u') F0 Λ Z) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') := by
  have hG := (((mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR Z F' hz hZ hP).2 Λ).mp ⟨hΛ, hE⟩
  by_contra hI
  rw [Formalism.L2.SG.Pf.Asm.glueSet_eq_empty (U := UPair D F0 F') hI] at hG
  exact hG

end Formalism.L2.SG.Pf.Cnt
end

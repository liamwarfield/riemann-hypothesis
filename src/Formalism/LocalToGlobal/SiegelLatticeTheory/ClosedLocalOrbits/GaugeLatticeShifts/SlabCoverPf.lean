module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem slabCoverC_of (hGF : GFInfInj) (hSA : NStrongApprox) (hNL : NLift) (hNR : NRatLam)
    (hRL : RatLeviC) (hPD : PsiDdC) : SlabCoverC := by
  intro D X Y u Ωs hKL hNeat hΩ
  have hK := Y.hK
  refine ⟨?_, ?_⟩
  ·
    rintro y ⟨n, h, k, hn, hk, hy⟩
    obtain ⟨ρ, ⟨γ, κ, hγκ⟩, -⟩ := Y.colReps u h
    have hs0 : ((γ : X.B.I.GA))⁻¹ ∈ Srat X u := inv_mem (gam_srat X u _ γ.2)
    obtain ⟨hn', -⟩ := nfinConj_holds X u (iotaF X u γ)⁻¹ n hn
    rw [Subgroup.coe_inv, inv_inv, iotaF_coe] at hn'
    obtain ⟨ν, hνS, hνK⟩ := hSA D X Y u ρ _ hKL hn'
    have hκ : (X.xu u)⁻¹ * (((κ : Hfin X u)) : X.B.I.Gf) * X.xu u ∈ X.K2 := κ.2
    set s1 : X.B.I.GA := ν * ((γ : X.B.I.GA))⁻¹ with hs1
    obtain ⟨t, ht, htΩ⟩ := (hΩ ρ).2.1 (s1 * y).1
    obtain ⟨s2, hs2, hs21, hs2K⟩ := hNL D X Y u ρ t ht
    refine ⟨s2 * s1, mul_mem hs2 (mul_mem hνS hs0), ρ, ?_, ?_⟩
    · show (s2 * s1 * y).1 ∈ Ωs ρ
      rw [mul_assoc, Prod.fst_mul, hs21]
      exact htΩ
    · refine ⟨_, hK.2.1 _ hs2K _ (hK.2.1 _ hνK _ (hK.2.1 _ hκ _ hk)), ?_⟩
      show _ = (s2 * s1 * y).2
      rw [hs1]
      simp only [Prod.snd_mul, Prod.snd_inv, hy, hγκ, Subgroup.coe_mul, iotaF_coe]
      group
  ·
    intro ρ ρ' y s hs hy hsy
    obtain ⟨hy1, k, hk, hyk⟩ := hy
    obtain ⟨hsy1, k', hk', hsyk⟩ := hsy
    have hyk' : ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k = y.2 := hyk
    have hsyk' : ((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u * k' = s.2 * y.2 := hsyk
    have hg : (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 := by
      have e : (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) =
          k' * k⁻¹ := by
        calc (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)
            = (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * (s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k)) * k⁻¹ := by
              group
          _ = (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u * k') * k⁻¹ := by
              rw [hyk', ← hsyk']
          _ = k' * k⁻¹ := by group
      rw [e]; exact hK.2.1 _ hk' _ (hK.2.2.1 _ hk)
    obtain ⟨hs1, hs2⟩ := sratComp_holds X u s hs
    obtain ⟨ν, η, hνη, hνG, hν1, hν2, hη⟩ := hRL D X u s (Subgroup.mem_inf.1 hs).1 hs1 hs2
    obtain ⟨ηg, hηg⟩ : ∃ ηg : Gam X u, ηg = ⟨η, hη⟩ := ⟨_, rfl⟩
    have hs2e : s.2 = ν.2 * η.2 := by rw [hνη]; rfl
    obtain ⟨hn1, -⟩ := nfinConj_holds X u ((Y.cs u).h ρ')⁻¹ ν.2 hν2
    have hLD := levelDec_of_psiDd (X := X) (u := u) (hPD D X)
    obtain ⟨h1, hh1⟩ : ∃ h1 : Hfin X u, h1 = ((Y.cs u).h ρ')⁻¹ * iotaF X u ηg * (Y.cs u).h ρ := ⟨_, rfl⟩
    have e1 : (X.xu u)⁻¹ * ((((Y.cs u).h ρ')⁻¹ : Hfin X u) * ν.2 * ((((Y.cs u).h ρ')⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
        (h1 : X.B.I.Gf)) * X.xu u =
        (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) := by
      rw [hs2e, hh1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaF_coe, hηg]
      group
    have hh1K : (X.xu u)⁻¹ * (h1 : X.B.I.Gf) * X.xu u ∈ X.K2 := (hLD _ hn1 h1 (e1 ▸ hg)).1
    have hρρ : ρ' = ρ := by
      refine (Y.colReps u ((Y.cs u).h ρ)).unique ⟨ηg⁻¹, ⟨h1, hh1K⟩, ?_⟩ ⟨1, 1, by simp⟩
      show (Y.cs u).h ρ = iotaF X u ηg⁻¹ * (Y.cs u).h ρ' * h1
      rw [map_inv, hh1]
      group
    subst hρρ
    have hmem : ((Y.cs u).h ρ')⁻¹ * iotaF X u ηg * (Y.cs u).h ρ' ∈ Ku X u Y.hK := by
      rw [← hh1]; exact hh1K
    have hη1 : ηg = 1 := hNeat ((Y.cs u).h ρ') ηg hmem
    have hη1' : η = 1 := by
      have := congrArg Subtype.val hη1
      rw [hηg] at this
      exact this
    have hsν : s = ν := by rw [hνη, hη1', mul_one]
    subst hsν
    have hsN := hNR D X Y u ρ' s hKL hνG hν1 hν2 hg
    have hs1' : s.1 = 1 := (hΩ ρ').2.2 y.1 hy1 s.1 hsN hsy1
    exact ⟨hGF D X s hνG hs1', rfl⟩

theorem finite_infinite_injective : GFInfInj := by
  intro D X s hs h1
  change s ∈ X.B.I.GFset at hs
  obtain ⟨γ, -, hinf, hfin⟩ := hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hv := hinf v
  rw [h1, Pi.one_apply] at hv
  have hv' : (X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
      X.B.I.P v = 1 := by
    rw [← hv]; simp [uMat]
  have hPu : IsUnit (X.B.I.P v).det := Matrix.isUnit_det_of_left_inverse hv'
  have h2 : (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) = 1 := by
    calc (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v)
        = (X.B.I.P v * (X.B.I.P v)⁻¹) * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
            (X.B.I.P v * (X.B.I.P v)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul, Matrix.mul_one]
      _ = X.B.I.P v * ((X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
            X.B.I.P v) * (X.B.I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv', Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
  have hγ := Matrix.map_injective (f := ⇑(X.B.I.φ v)) (RingHom.injective _)
    (h2.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)] at hfin
  unfold AutInst.fmat at hfin
  have h2' : s.2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa using hfin
  exact Prod.ext h1 h2'

theorem nLift_of (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) : NLift := by
  intro D X Y u ρ t ht
  obtain ⟨x, n, hL, rfl, hn⟩ := ht
  have hi := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ x n hL hn
  have hf := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ x n hL hn
  refine ⟨x, Subgroup.mem_inf.2 ⟨Formalism.L2.SG.TermOp.ratLink_mem (X := X) hL,
    Subgroup.subset_closure ⟨fun v => (hi v).1, ⟨hf.1, hf.2.1⟩⟩⟩, rfl, (hNC D X Y u ρ x n hn hL).1⟩

theorem nStrongApprox_of (hD : NDense) : NStrongApprox := by
  intro D X Y u ρ n hKL hn
  set a : X.B.I.Gf := ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u
  have hKo : IsOpen X.K2 := (level_subgroup_isClopen X Y.hK hKL).isOpen
  have hc : Continuous fun m : X.B.I.Gf => a⁻¹ * (m * n) * a :=
    (continuous_const.mul (continuous_id.mul continuous_const)).mul continuous_const
  have hninv : n⁻¹ ∈ X.NfinU u := (nfinGroup_holds (X := X) (u := u)).2 n hn
  obtain ⟨ν, hνG, hν1, hν2, hνU⟩ := hD D X u n⁻¹ hninv _ (hKo.preimage hc)
    (by show a⁻¹ * (n⁻¹ * n) * a ∈ X.K2; rw [inv_mul_cancel, mul_one, inv_mul_cancel]; exact Y.hK.1)
  exact ⟨ν, Subgroup.mem_inf.2 ⟨hνG, Subgroup.subset_closure ⟨fun v => (hν1 v).1, ⟨hν2.1, hν2.2.1⟩⟩⟩, hνU⟩

theorem slab_covering_of_strong_approx (hD : NDense) (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) (hRL : RatLeviC) (hPD : PsiDdC) :
    SlabCoverC :=
  slabCoverC_of finite_infinite_injective (nStrongApprox_of hD) (nLift_of hNC) nilradical_rational_lattice hRL hPD

end Formalism.L2.SG.Pf.SlabCoverPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem levi_one_iff {δ : X.B.I.Gf} (gδ : Good X δ) :
    levi TR δ = 1 ↔ ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  refine ⟨fun h1 i => ?_, fun h => Formalism.L2.SG.Pf.AmpIota.levi_eq_one_of TR gδ h⟩
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set w := X.B.I.fmat δ *ᵥ X.bw i with hwdef
  have hwL : w ∈ X.B.I.Lf := K_mv X.B.I gδ.1.1 (hB i)
  have hwM := gδ.1.2.2 i
  have hd := dual_coords X hwL
  have hZe : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w) := fun a =>
    Z_pair_Mo X (hE0 a) (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · exact (X.gramIntegral a b).1
      · exact ((X.weightVectorsIntegral l).2.2 a).1) _ hwM
  have hZz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 w) :=
    Z_pair_Mo X hZ0 (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · rw [hA_symm]; exact Z_sig X.B.I X.B.g ((X.formsAtZero).2 b).1
      · exact (X.weightVectorsIntegral l).1) _ hwM
  have hbw0 : ∀ j, hA X.B.I (X.bw j) w = 0 := fun j => by
    rw [hwdef, X.bw_w j, X.bw_w i, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
    have := X.ew_orth
    linear_combination (hA X.B.I (X.bw j) (X.B.I.fmat δ *ᵥ X.bw i)) * this
  have hcoef : ∀ j : Fin D.R.k, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) := by
    intro j
    have hI := hA_int X.B.I (hBd j) hwL
    have hIt : ((if j = i then 1 else 0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hres : ∀ v, TR.res v ⟨_, sub_mem hI hIt⟩ = 0 := by
      intro v
      have hent : leviM TR δ v j i = if j = i then 1 else 0 := by
        rw [← levi_coe TR gδ, h1, Pi.one_apply, Units.val_one, Matrix.one_apply]
      have e : (⟨_, sub_mem hI hIt⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, hI⟩ - ⟨_, hIt⟩ := by
        apply Subtype.ext; simp
      rw [e, map_sub]
      have h2 : TR.res v ⟨_, hI⟩ = leviM TR δ v j i := by
        show _ = resT TR v (hA X.B.I (X.bwd j) (X.B.I.fmat δ *ᵥ X.bw i))
        rw [resT_of_mem TR v hI]
      rw [h2, hent]
      by_cases h : j = i
      · subst h
        have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 1 := by apply Subtype.ext; simp
        rw [if_pos rfl, this, map_one, sub_self]
      · have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 0 := by apply Subtype.ext; simp [h]
        rw [if_neg h, this, map_zero, sub_self]
    have hZ := (TR.res_ker ⟨_, sub_mem hI hIt⟩).1 hres
    have e : X.ew * (hA X.B.I (X.bwd j) w - if j = i then 1 else 0) =
        hA X.B.I (X.bwd j) w - if j = i then X.ew else 0 := by
      rw [mul_sub, ← bwc_ew δ j i]
      split_ifs <;> ring
    simpa [e] using hZ
  have e1 : (X.B.I.fmat δ - 1) *ᵥ X.bw i = (w - repr0 X w) +
      ((∑ a, hA X.B.I (X.f0 a) w • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) w • X.f0 a) - hA X.B.I X.z0 w • X.z0 +
        (∑ j, (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) • X.bw j) +
        (∑ j, hA X.B.I (X.bw j) w • X.bwd j)) := by
    have hbi : (∑ j, (if j = i then X.ew else 0) • X.bw j) = X.bw i := by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (X.bw_w i).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwdef]
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib, hbi]
    abel
  rw [e1]
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      s ∈ Set.range X.e0 → c • s ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c s hc hs => by
    have : c • s = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • s := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hs)
  refine add_mem (mL_Mo X.B.I hd) (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF0 a) hwL) ⟨a, rfl⟩
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (hZe a) (hF0 a))
  · exact mL_Mo X.B.I (Z_smul_mL X hZz hZ0)
  · exact sum_mem fun j _ => mL_Mo X.B.I (Z_smul_mL X (hcoef j) (hB j))
  · refine sum_mem fun j _ => ?_
    rw [hbw0, zero_smul]; exact zero_mem _

theorem iotaOf_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    Good X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      NCong X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ = levi Y.TR ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (s₂.pt.2 * s₁.pt.2⁻¹) * (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) *
        iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ := by
  have hTF := Formalism.L2.SG.Full.Full.frameTie (X := X) u u'
  have hN := adm_norm_of_fixed_frames (Y.cs u) (Y.cs u') hTF (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm (Y.cs u) (Y.cs u') (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) hN
  have g1 := hA s₁
  have g2 := hA s₂
  have n1 := hN s₁
  have n2 := hN s₂
  have k1 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₁
  have k2 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₂
  rw [← hl, ← hl'] at g2 n2 k2
  have e : (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
      (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u) =
      kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₂.pt *
      (kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₁.pt)⁻¹ := by
    unfold kOf; group
  rw [e]
  refine ⟨good_mul X g2 (good_inv X g1), ncong_mul X k2 n2 (ncong_inv X k1 n1), ?_⟩
  unfold iotaOf
  rw [← hl, ← hl', levi_mul Y.TR g2 (good_inv X g1), mul_assoc, ← levi_mul Y.TR (good_inv X g1) g1, inv_mul_cancel,
    levi_one, mul_one]

end Formalism.L2.SG.Pf.IotaDictPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AdTriv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (δ : X.B.I.Gf) : Prop :=
  ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)

def RatTriv {D : D7} (u : D.what₂.Word) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x ∈ Lrep Λ (lf D (X.Fu u)), β x - x ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u))

def IotaDictC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic → s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrameLocX
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem frameLoc_X (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    FrameLoc (X.B.I.ε v) D.R.k (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
      (Tw u) (Tw u') := by
  refine
    { dim := (Formalism.L2.SG.Pf.card_frame X).symm
      k_pos := by have := D.R.m_add_three_le_k; omega
      sig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
      e_li := ?_
      ee := fun a b => (hJ_X X v _ _).trans (by rw [X.ee]; simp)
      ez := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
      ez' := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u' a).1]; simp)
      zz := (hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
      zz' := (hJ_X X v _ _).trans (by rw [X.zu_norm u']; simp [Tw])
      T_pos := Tw_pos u
      T'_pos := Tw_pos u' }
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_fsum_r] at h
  have hfe : ∀ i, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR i)) = if i = j then 1 else 0 :=
    fun i => (hJ_X X v _ _).trans (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [h]
  unfold hJ
  simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Defs

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def concreteLevelAdelicSubset (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2.1 _ ha

def UcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.Gf :=
  Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u) ⊓ (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom

def RcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Formalism.L2.SG.Pf.NinfSub (I := X.B.I) X.eR (X.zR u)).prod (UcS X u hK c)

def GcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.Ginf := (RcS X u hK c).map (MonoidHom.fst _ _)

end Defs

def NOinfEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), NOinf X u = (GcS X u hK (X.xu u) : Set X.B.I.Ginf)

def NOcolEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl),
    Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ =
      (GcS X u Y.hK (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) : Set X.B.I.Ginf)

def GcCountC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf), Countable (GcS X u hK c)

def FundMeasEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Γ : Subgroup X.B.I.Ginf) (Ω Ω' : Set X.B.I.Ginf),
    (Γ : Set X.B.I.Ginf) ⊆ X.NinfU u → Countable Γ → IsSFund X.B.I Γ Ω → IsSFund X.B.I Γ Ω' →
      X.muN u Ω = X.muN u Ω'

def IndexVolC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Γ Γ' : Subgroup X.B.I.Ginf) (Ω : Set X.B.I.Ginf),
    Γ' ≤ Γ → (Γ : Set X.B.I.Ginf) ⊆ X.NinfU u → Countable Γ → Γ'.relIndex Γ ≠ 0 → IsSFund X.B.I Γ Ω →
      ∃ Ω', IsSFund X.B.I Γ' Ω' ∧ X.muN u Ω' = (Γ'.relIndex Γ : ℝ≥0∞) * X.muN u Ω

def IndexTransferC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (g h : Hfin X u),
    (GcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (GcS X u hK ((g : X.B.I.Gf) * X.xu u)) =
        (UcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (UcS X u hK ((g : X.B.I.Gf) * X.xu u)) ∧
      (UcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (UcS X u hK ((g : X.B.I.Gf) * X.xu u)) ≠ 0

def ConjUC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (g : Hfin X u) (c : X.B.I.Gf),
    UcS X u hK ((g : X.B.I.Gf) * c) = (UcS X u hK c).map (MulAut.conj (g : X.B.I.Gf)).toMonoidHom

def GcFundC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (h : Hfin X u),
    ∃ Ω, IsSFund X.B.I (GcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)) Ω

def GcConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK),
    (GcS X u hK ((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) * X.xu u) : Set X.B.I.Ginf) =
      (fun s => (γ : X.B.I.GA).1 * s * (γ : X.B.I.GA).1⁻¹) '' (GcS X u hK ((h : X.B.I.Gf) * X.xu u) : Set X.B.I.Ginf)

def HinfConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (h : X.B.I.Ginf), h ∈ Hinf X u → ∀ Ω : Set X.B.I.Ginf,
    MeasurableSet Ω → X.muN u ((fun s => h * s * h⁻¹) '' Ω) = X.muN u Ω

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSteps
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word),
    ∃ F : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V →
        Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      ∀ Λ₁ ∈ Y.what₂ u', ∀ Λ₂ ∈ Y.what₂ u', ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA),
        RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ₂ = Λ₁ →
          ∃ f ∈ F Λ₁ Λ₂, f⁻¹ * σ ∈ NLam Λ₂ (lf D (X.Fu u'))

theorem tsum_comp_le_of_fibre {ι κ β : Type*} (φ : ι → κ) (g : κ → ℝ≥0∞) (M : ℕ)
    (hfib : ∀ k, ∃ (S : Finset β) (e : ι → β), S.card ≤ M ∧
      ∀ i, φ i = k → e i ∈ S ∧ ∀ j, φ j = k → e i = e j → i = j) :
    ∑' i, g (φ i) ≤ (M : ℝ≥0∞) * ∑' k, g k := by
  rw [← (Equiv.sigmaFiberEquiv φ).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  obtain ⟨S, e, hS, he⟩ := hfib k
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hc : s.card ≤ M := by
    refine le_trans ?_ hS
    refine Finset.card_le_card_of_injOn (fun i => e (i : ι)) (fun i _ => (he i.1 i.2).1) ?_
    intro i _ j _ hij
    exact Subtype.ext ((he i.1 i.2).2 j.1 j.2 hij)
  calc ∑ i ∈ s, g (φ ((Equiv.sigmaFiberEquiv φ) ⟨k, i⟩))
      = ∑ i ∈ s, g k := Finset.sum_congr rfl fun i _ => by
          show g (φ i.1) = g k
          rw [i.2]
    _ = (s.card : ℝ≥0∞) * g k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ≥0∞) * g k := by gcongr

end Formalism.L2.SG.Pf.SlabCount
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjHSymmApply
noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem HG_compact {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) :
    IsCompact (HG ε e p z : Set (UJ ε)) := by
  set Q : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε} ∩ ((⋂ a, {g | g *ᵥ e a = e a}) ∩
    ((⋂ a, {g | g *ᵥ p a = p a}) ∩ {g | g *ᵥ z = z})) with hQ
  have e1 : (HG ε e p z : Set (UJ ε)) = (fun g : UJ ε => Formalism.MainNotions.S.uMat g) ⁻¹' Q := by
    ext g
    simp only [coe_HG, HLoc, hQ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨g.2, h.1, h.2.1, h.2.2⟩, fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩
  have hQc : IsClosed Q := by
    refine (isClosed_eq ((continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id)
      continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
        continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
          continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)))
  have hzz : hJ ε z z ≠ 0 := by
    rw [Fw.zz]; exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Fw.T_ne)
  have hQk : IsCompact Q := Formalism.L2.SG.Pf.frame_compact ε e p z w Fw.ee Fw.pp Fw.ep Fw.ez Fw.pz hzz Fw.ww Fw.ew Fw.pw
    Fw.zw hdim.symm hQc (fun g hg => ⟨hg.1, fun a => Set.mem_iInter.1 hg.2.1 a,
      fun a => Set.mem_iInter.1 hg.2.2.1 a, hg.2.2.2⟩)
  rw [e1]
  exact ((Formalism.REAL.uJEmb n ε).1).isCompact_preimage hQk

def conjH (h : UJ ε) : UJ ε ≃ₜ UJ ε := (Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)

theorem conjH_apply (h x : UJ ε) : conjH h x = h * x * h⁻¹ := rfl

section Conj

theorem map_conj_isHaarS {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε}
    (hh : h ∈ HG ε e p z) : IsHaarS (NLoc ε e z) (μ.map (conjH h)) := by
  obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hμ
  have hmeas : Measurable (conjH h) := (conjH h).continuous.measurable
  set E := (conjH h).toMeasurableEquiv with hE
  have hEe : ⇑E = ⇑(conjH h) := rfl
  refine ⟨⟨?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [← hEe]; exact E.sigmaFinite_map
  · intro h0
    apply hne
    have := congrArg (fun m : Measure (UJ ε) => m Set.univ) h0
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, FunLike.coe_zero,
      Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.1 this
  · rw [Measure.map_apply hmeas (show MeasurableSet (NLoc ε e z)ᶜ from (NG_closed ε e z).measurableSet.compl)]
    refine measure_mono_null (s := (conjH h) ⁻¹' (NLoc ε e z)ᶜ) (t := (NLoc ε e z)ᶜ)
      (fun x hx hxN => hx ?_) hcompl
    exact conj_mem ε e p z hh hxN
  · have ht' : h⁻¹ * t * h ∈ (NG ε e z) := by
      have := conj_mem ε e p z ((HG ε e p z).inv_mem hh) ht
      simpa using this
    have hcomm : (fun x => t * x) ∘ conjH h = conjH h ∘ (fun x => h⁻¹ * t * h * x) := by
      funext x; simp only [Function.comp_apply, conjH_apply]; group
    rw [Measure.map_map (measurable_const_mul t) hmeas, hcomm,
      ← Measure.map_map hmeas (measurable_const_mul _), hinv _ ht']
  · refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmeas hK.measurableSet]
    have : (conjH h) ⁻¹' K = (conjH h).symm '' K := (congrFun (conjH h).image_symm K).symm
    rw [this]
    exact (hK.image (conjH h).symm.continuous).measure_lt_top

theorem conj_haar_eq {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k)
    {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε} (hh : h ∈ HG ε e p z) :
    μ.map (conjH h) = μ := by
  have : LocallyCompactSpace (NG ε e z) := (NG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (NG ε e z) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hNm : MeasurableSet ((NG ε e z) : Set (UJ ε)) := (NG_closed ε e z).measurableSet
  have memb : MeasurableEmbedding (Subtype.val : (NG ε e z) → UJ ε) := MeasurableEmbedding.subtype_coe hNm
  set m0 : Measure (UJ ε) := (Measure.haar : Measure (NG ε e z)).map Subtype.val with hm0

  have huniq : ∀ ν : Measure (UJ ε), IsHaarS (NLoc ε e z) ν → ∃ c : ℝ≥0, ν = c • m0 := by
    intro ν hν
    obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hν
    set ν' : Measure (NG ε e z) := ν.comap Subtype.val with hν'
    have hrestr : ν.restrict ((NG ε e z) : Set (UJ ε)) = ν := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hcompl
    have hmapν : ν'.map Subtype.val = ν := by
      rw [hν', memb.map_comap, Subtype.range_coe, hrestr]
    have himg : ∀ (t : (NG ε e z)) (A : Set (NG ε e z)), Subtype.val '' ((fun x => t * x) ⁻¹' A) =
        (fun x => (t : UJ ε) * x) ⁻¹' (Subtype.val '' A) := by
      intro t A
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t * y, hy, rfl⟩
      · rintro ⟨a, ha, hax⟩
        have hxS : x ∈ (NG ε e z) := by
          have : x = ((t⁻¹ * a : (NG ε e z)) : UJ ε) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hax]; group
          rw [this]; exact (t⁻¹ * a).2
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        show t * ⟨x, hxS⟩ ∈ A
        have : t * ⟨x, hxS⟩ = a := Subtype.ext (by simpa using hax.symm)
        rw [this]; exact ha
    have hνinv : ν'.IsMulLeftInvariant := by
      refine ⟨fun t => ?_⟩
      ext A hA
      rw [Measure.map_apply (measurable_const_mul t) hA, hν', memb.comap_apply, memb.comap_apply, himg,
        ← Measure.map_apply (measurable_const_mul _) (memb.measurableSet_image.2 hA), hinv _ t.2]
    have hνfin : IsFiniteMeasureOnCompacts ν' := by
      refine ⟨fun K hK => ?_⟩
      rw [hν', memb.comap_apply]
      exact (hK.image continuous_subtype_val).measure_lt_top
    have hνeq : ν' = ν'.haarScalarFactor Measure.haar • Measure.haar :=
      Measure.isMulLeftInvariant_eq_smul ν' Measure.haar
    refine ⟨ν'.haarScalarFactor Measure.haar, ?_⟩
    conv_lhs => rw [← hmapν, hνeq]
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable]

  obtain ⟨C', hC'c, hC'n⟩ : ∃ C' : Set (NG ε e z), IsCompact C' ∧ C' ∈ 𝓝 (1 : (NG ε e z)) := by
    obtain ⟨C', h1, h2⟩ := exists_compact_mem_nhds (1 : (NG ε e z))
    exact ⟨C', h1, h2⟩
  have hC'pos : 0 < (Measure.haar : Measure (NG ε e z)) C' := Measure.measure_pos_of_mem_nhds _ hC'n
  set C : Set (UJ ε) := Subtype.val '' C' with hC
  have hHc := HG_compact Fw hdim
  set K : Set (UJ ε) := (fun q : UJ ε × UJ ε => q.1 * q.2 * q.1⁻¹) '' ((HG ε e p z : Set (UJ ε)) ×ˢ C) with hK
  have hKc : IsCompact K :=
    (hHc.prod (hC'c.image continuous_subtype_val)).image (by fun_prop)
  have hKN : K ⊆ ((NG ε e z) : Set (UJ ε)) := by
    rintro _ ⟨⟨h', x⟩, ⟨hh', ⟨x', _, rfl⟩⟩, rfl⟩
    exact conj_mem ε e p z hh' x'.2
  have hCK : C ⊆ K := fun x hx => ⟨(1, x), ⟨(HG ε e p z).one_mem, hx⟩, by simp⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hm0K : m0 K = (Measure.haar : Measure (NG ε e z)) (Subtype.val ⁻¹' K) := by
    rw [hm0, Measure.map_apply measurable_subtype_coe hKm]
  have hm0pos : 0 < m0 K := by
    rw [hm0K]
    refine lt_of_lt_of_le hC'pos (measure_mono ?_)
    intro x hx
    exact hCK ⟨x, hx, rfl⟩
  have hm0fin : m0 K < ⊤ := by
    rw [hm0K]
    exact ((NG_closed ε e z).isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top
  have hinvK : (conjH h) ⁻¹' K = K := by
    ext x
    constructor
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, hxe⟩
      refine ⟨(h⁻¹ * h', x'), ⟨(HG ε e p z).mul_mem ((HG ε e p z).inv_mem hh) hh', hx'⟩, ?_⟩
      have hxe' : h' * x' * h'⁻¹ = h * x * h⁻¹ := hxe
      show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = x
      rw [show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * x' * h'⁻¹) * h by group, hxe']
      group
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, rfl⟩
      refine ⟨(h * h', x'), ⟨(HG ε e p z).mul_mem hh hh', hx'⟩, ?_⟩
      simp only [conjH_apply]
      group

  obtain ⟨c1, h1⟩ := huniq μ hμ
  obtain ⟨c2, h2⟩ := huniq _ (map_conj_isHaarS hμ hh)
  have hK12 : (μ.map (conjH h)) K = μ K := by
    rw [Measure.map_apply (conjH h).continuous.measurable hKm, hinvK]
  have hc : (c2 : ℝ≥0∞) = c1 := by
    have e2 : (μ.map (conjH h)) K = c2 * m0 K := by
      conv_lhs => rw [h2]
      rfl
    have e1 : μ K = c1 * m0 K := by
      conv_lhs => rw [h1]
      rfl
    rw [e2, e1] at hK12
    exact (ENNReal.mul_left_inj hm0pos.ne' hm0fin.ne).1 hK12
  rw [h2, h1]
  congr 1
  exact_mod_cast hc

end Conj

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

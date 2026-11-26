module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutAt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormRepChange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FibSumOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountHoldsAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefXiTyped
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupFunHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeNormalizedOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApprox
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaPlusThHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OrbitStabilizerIndexHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEFinal
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEOf
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem bOf_unique (a : Formalism.L2.SG.PairVal.GLR D) (b : Formalism.L2.SG.PairVal.MatR D)
    (hW : (a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b = ptMat w) : VolPinAsm.bOf w a = b := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  have h1 : (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * ptMat w
      = (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) *
          ((a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b) := by rw [hW]
    _ = (ptMat w)⁻¹ * ((((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D)) *
          ptMat w * b := by simp only [Matrix.mul_assoc]
    _ = b := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul]

theorem mem_stabInt_glob (hA : ∀ p, Agree δ M p) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' δ M w) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ AP M δ u u' w p := by
  have hset : ∀ a : VolPinAsm.StG w, (a : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ↔
      ∀ p, πP M δ u u' w (hA p) a ∈ AP M δ u u' w p := by
    intro a
    obtain ⟨ha, hb, hW⟩ := bOf_spec w a
    rw [mem_stabIntSet_iff δ M u u' hA w]
    refine ⟨fun h p => ?_, fun hp => ⟨ha, _, hb, hW, hp⟩⟩
    obtain ⟨-, b, -, hW', hp⟩ := h
    have e := bOf_unique w (a : Formalism.L2.SG.PairVal.GLR D) b hW'
    rw [← e] at hp
    exact hp p
  constructor
  · intro hg

    set K : Subgroup (Formalism.L2.SG.PairVal.GLR D) :=
      (Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p)).map
        (VolPinAsm.StG w).subtype with hK
    have hle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ K := by
      unfold Formalism.L2.SG.PairVal.stabInt
      rw [Subgroup.closure_le]
      intro a ha
      have haSt : a ∈ VolPinAsm.StG w := by
        obtain ⟨h1, b, hb, hW, -⟩ := ha
        exact ⟨h1, b, hb, hW⟩
      refine ⟨⟨a, haSt⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob]
      exact (hset ⟨a, haSt⟩).1 ha
    obtain ⟨g', hg', e⟩ := hle hg
    have : g' = g := Subtype.ext e
    rw [this, SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob] at hg'
    exact hg'
  · intro hp
    exact Subgroup.subset_closure ((hset g).2 hp)

theorem lOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    lOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = lOf δ M p L U * lOf δ M p g b * lOf δ M p L⁻¹ U⁻¹ := by
  rw [Matrix.mul_assoc L g, lOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), lOf_mul δ M hA g b L⁻¹ U⁻¹, Matrix.mul_assoc]

theorem ρOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    ρOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p g b * ρOf δ M p L U := by
  rw [Matrix.mul_assoc L g, ρOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), ρOf_mul δ M hA g b L⁻¹ U⁻¹]

theorem mem_CZ_glob (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  have hmem (a : Formalism.L2.SG.PairVal.GLR D) : a ∈ ZsVolCut.CZ M δ u u' Zh L ↔ a ∈ ZsVolCut.stZSet M δ u u' Zh L := by
    let K : Subgroup (Formalism.L2.SG.PairVal.GLR D) := {
      carrier := ZsVolCut.stZSet M δ u u' Zh L
      one_mem' := by
        refine ⟨1, ?_, ZsVolGrp.isLoUni_one, 1, ZsVolGrp.isUpUni_one, by simp, fun p => ⟨1, 1, ZsVolGrp.intLow_one _, ZsVolGrp.intUp_one _, fun Zh' => ?_⟩⟩
        · simp [Matrix.nonsing_inv_mul L hLdet]
        · simp [ZsVolGrp.zhatOM_zhatOM]
      mul_mem' := by
        rintro x y ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩ ⟨y', hy, hyl, by', hby, hyZ, hyp⟩
        refine ⟨x' * y', ?_, ?_, by' * bx, ZsVolGrp.isUpUni_mul hby hbx, ?_, fun p => ?_⟩
        · rw [Units.val_mul, hx, hy, Units.val_mul]
          calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L * (L⁻¹ * (y' : Formalism.L2.SG.PairVal.MatR D) * L) =
              L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) * (y' : Formalism.L2.SG.PairVal.MatR D) * L := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [Matrix.mul_nonsing_inv L hLdet, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        · rw [Units.val_mul]
          exact ZsVolGrp.isLoUni_mul hxl hyl
        · rw [Units.val_mul]
          calc (x' : Formalism.L2.SG.PairVal.MatR D) * (y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh * (by' * bx) =
              (x' : Formalism.L2.SG.PairVal.MatR D) * ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh * by') * bx := by
                simp only [Matrix.mul_assoc]
            _ = ZhatOM Zh := by rw [hyZ, hxZ]
        · obtain ⟨l1, ρ1, hl1, hρ1, h1⟩ := hxp p
          obtain ⟨l2, ρ2, hl2, hρ2, h2⟩ := hyp p
          refine ⟨l1 * l2, ρ2 * ρ1, ZsVolGrp.intLow_mul _ hl1 hl2, ZsVolGrp.intUp_mul _ hρ2 hρ1, fun Zh' => ?_⟩
          have e : ((x' * y' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh' * (by' * bx) =
              (x' : Formalism.L2.SG.PairVal.MatR D) *
                ZhatOM (ZhatOM ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh' * by')) * bx := by
            rw [ZsVolGrp.zhatOM_zhatOM, Units.val_mul]
            simp only [Matrix.mul_assoc]
          rw [e, h1, h2]
          simp only [Matrix.mul_assoc]
      inv_mem' := by
        rintro x ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩
        obtain ⟨hxi, hxi1, hxi2⟩ := ZsVolGrp.isLoUni_inv hxl
        obtain ⟨hbi, hbi1, hbi2⟩ := ZsVolGrp.isUpUni_inv hbx
        have hZ : ((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh * bx⁻¹ = ZhatOM Zh := by
          rw [Matrix.coe_units_inv]
          calc (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ZhatOM Zh * bx⁻¹ =
              (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh * bx) * bx⁻¹ := by rw [hxZ]
            _ = ZhatOM Zh := by
              simp only [← Matrix.mul_assoc]
              rw [hxi1, Matrix.one_mul, Matrix.mul_assoc, hbi2, Matrix.mul_one]
        refine ⟨x'⁻¹, ?_, by rw [Matrix.coe_units_inv]; exact hxi, bx⁻¹, hbi, hZ, fun p => ?_⟩
        · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, hx]
          have hLi := Matrix.nonsing_inv_mul L hLdet
          have hiL := Matrix.mul_nonsing_inv L hLdet
          refine Matrix.inv_eq_left_inv ?_
          calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * L * (L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L) =
              L⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * (L * L⁻¹) * (x' : Formalism.L2.SG.PairVal.MatR D)) * L := by
                simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hiL, Matrix.mul_one, hxi1, Matrix.mul_one, hLi]
        · obtain ⟨l, ρ, hl, hρ, h⟩ := hxp p
          obtain ⟨hli, hli1, hli2⟩ := ZsVolGrp.intLow_inv _ hl
          obtain ⟨hρi, hρi1, hρi2⟩ := ZsVolGrp.intUp_inv _ hρ
          refine ⟨l⁻¹, ρ⁻¹, hli, hρi, fun Zh' => ?_⟩
          have h2 := h (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh' * bx⁻¹))
          have e : (x' : Formalism.L2.SG.PairVal.MatR D) *
              ZhatOM (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Zh' * bx⁻¹)) * bx =
              ZhatOM Zh' := by
            rw [ZsVolGrp.zhatOM_zhatOM, Matrix.coe_units_inv]
            simp only [← Matrix.mul_assoc]
            rw [hxi2, Matrix.one_mul, Matrix.mul_assoc, hbi1, Matrix.mul_one]
          rw [e, ZsVolGrp.zhatOM_zhatOM] at h2
          conv_rhs => rw [h2]
          simp only [← Matrix.mul_assoc]
          rw [hli1, Matrix.one_mul]
          simp only [Matrix.mul_assoc, hρi2, Matrix.mul_one]
    }
    have hK : (K : Set _) = ZsVolCut.stZSet M δ u u' Zh L := rfl
    change a ∈ Subgroup.closure (ZsVolCut.stZSet M δ u u' Zh L) ↔ _
    rw [← hK, Subgroup.closure_eq]
    exact Iff.rfl
  rw [hmem]
  obtain ⟨ha, hb, hW⟩ := bOf_spec w g
  set gm : Formalism.L2.SG.PairVal.MatR D := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) with hgm
  set b := VolPinAsm.bOf w (g : Formalism.L2.SG.PairVal.GLR D) with hb'
  have hmemC : ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU ↔
      Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) ∧
        Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) := by
    intro p
    rw [lOf_conj M δ (hA p), ρOf_conj M δ (hA p)]
    rfl
  simp only [hmemC]
  constructor
  · rintro ⟨a', ha'eq, ha'lo, b', hb'up, hZ', hloc⟩ p
    have ea' : ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = L * gm * L⁻¹ := by
      have h := ha'eq
      rw [← hgm] at h
      rw [h]
      calc ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
          = (L * L⁻¹) * (a' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) := by rw [hLi.2.2]; simp
        _ = L * (L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L) * L⁻¹ := by simp only [Matrix.mul_assoc]
    have eb' : b' = U⁻¹ * b * U := by
      have h1 : gm * ptMat w * (U * b' * U⁻¹) = ptMat w := by
        have := hZ'
        rw [hZ, ea'] at this
        have h2 : L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [this]
        calc gm * ptMat w * (U * b' * U⁻¹) = (L⁻¹ * L) * gm * (L⁻¹ * L) * ptMat w * U * b' * U⁻¹ := by
              rw [hLi.2.1]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
          _ = L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
          _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := h2
          _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
          _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]
      have e := bOf_unique w (g : Formalism.L2.SG.PairVal.GLR D) _ h1
      rw [← hb'] at e
      rw [e]
      calc b' = (U⁻¹ * U) * b' * (U⁻¹ * U) := by rw [hUi.2.1]; simp
        _ = U⁻¹ * (U * b' * U⁻¹) * U := by simp only [Matrix.mul_assoc]
    obtain ⟨l, ρ, hl, hρ, hZl⟩ := hloc p
    obtain ⟨el, eρ⟩ := uniq δ M u u' (hA p) _ b' ha'lo hb'up l ρ (fun i => hl.1 i) (fun i => hρ.1 i) hZl
    rw [← ea', ← eb', ← el, ← eρ]
    exact ⟨hl, hρ⟩
  · intro hp
    set a'm := L * gm * L⁻¹ with ha'm
    have ha'lo : IsLoUni a'm := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hL ha) hLi.1
    have hb'up : IsUpUni (U⁻¹ * b * U) := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUi.1 hb) hU
    have hginv : ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * gm = 1 := by
      rw [hgm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hginv' : gm * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = 1 := by
      rw [hgm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    let a' : Formalism.L2.SG.PairVal.GLR D :=
      ⟨a'm, L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹,
        by
          calc a'm * (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹)
              = L * gm * (L⁻¹ * L) * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv', Matrix.mul_one, hLi.2.2],
        by
          calc (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹) * a'm
              = L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * (L⁻¹ * L) * gm * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv, Matrix.mul_one, hLi.2.2]⟩
    refine ⟨a', ?_, ha'lo, U⁻¹ * b * U, hb'up, ?_, fun p => ⟨_, _, (hp p).1, (hp p).2,
      move δ M u u' (hA p) a'm (U⁻¹ * b * U) ha'lo hb'up⟩⟩
    · show gm = L⁻¹ * a'm * L
      calc gm = (L⁻¹ * L) * gm * (L⁻¹ * L) := by rw [hLi.2.1]; simp
        _ = L⁻¹ * a'm * L := by simp only [ha'm, Matrix.mul_assoc]
    · show a'm * ZhatOM Zh * (U⁻¹ * b * U) = ZhatOM Zh
      rw [hZ]
      calc a'm * (L * ptMat w * U) * (U⁻¹ * b * U) = L * gm * (L⁻¹ * L) * ptMat w * (U * U⁻¹) * b * U := by
            simp only [ha'm, Matrix.mul_assoc]
        _ = L * (gm * ptMat w * b) * U := by
            rw [hLi.2.1, hUi.2.2, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = L * ptMat w * U := by rw [hW]

theorem idxRatio_self {G : Type} [Group G] (A : Subgroup G) : Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A A = 1 := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio; simp [Subgroup.relIndex_self]

theorem idxRatio_subgroupOf {G : Type} [Group G] (A B K : Subgroup G) (hA : A ≤ K) (hB : B ≤ K) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.subgroupOf K) (B.subgroupOf K) = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A B := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_subgroupOf hA, Subgroup.relIndex_subgroupOf hB]

theorem cz_le (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) :
    Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L ≤ VolPinAsm.StG w := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  change Subgroup.closure (ZsVolCut.stZSet M δ u u' Zh L) ≤ VolPinAsm.StG w
  rw [Subgroup.closure_le]
  intro a ha
  obtain ⟨a', ha'eq, ha'lo, b', hb'up, hZ', -⟩ := ha
  refine ⟨?_, U * b' * U⁻¹, ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hU hb'up) hUi.1, ?_⟩
  · rw [ha'eq]; exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLi.1 ha'lo) hL
  · rw [ha'eq]
    rw [hZ] at hZ'
    calc L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L * ptMat w * (U * b' * U⁻¹)
        = L⁻¹ * ((a' : Formalism.L2.SG.PairVal.MatR D) * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [hZ']
      _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_of (hap : ApproxC M δ u u' F0 what₂) (hloc : LocIdxC M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') := by
  intro γ w F' L U hE
  obtain ⟨S, hS, hfin, happrox⟩ := hap γ w F' L U hE
  have hA := hE.1
  have hL : IsLoUni L := hE.2.2.2.2.2.2.2.1
  have hU : IsUpUni U := hE.2.2.2.2.2.2.2.2.1
  have hZ : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U := hE.2.2.2.2.2.2.2.2.2
  have hset : Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ⊆ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w) := by
    intro a ha
    obtain ⟨h1, b, hb, hW, -⟩ := ha
    exact ⟨h1, b, hb, hW⟩
  have hAle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ VolPinAsm.StG w := fun x hx =>
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.closure_subset_StSet Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed _ _ hset hx
  have hCle := cz_le M δ u u' w L U hL hU _ hZ
  rw [← idxRatio_subgroupOf _ _ _ hAle hCle]
  have e1 : (Formalism.L2.SG.PairVal.stabInt D u u' δ M w).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_stabInt_glob M δ u u' w hA g
  have e2 : (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' (ZhatL (lf D F0) F') L).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => CPL M δ u u' w (hA p) L U hL hU) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_CZ_glob M δ u u' w hA L U hL hU _ hZ g
  rw [e1, e2, Formalism.L2.SG.Pf.ProdE.idxRatio_glob _ _ _ S hS (fun p => (hfin p).1) (fun p => (hfin p).2) happrox]
  have hl := fun p => hloc γ w F' L U hE p
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  · exact Finset.prod_congr rfl fun p _ => hl p
  · intro p hp
    by_contra hpS
    apply hp
    show Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
      (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) = 1
    rw [← hl p, hS p hpS, idxRatio_self]

end Formalism.L2.SG.Pf.ProdE
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ProdE

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_CZ_of_approxC (hap : ApproxC M δ u u' F0 what₂) (hst : Formalism.L2.SG.Pf.ProdEP2Cut.StepsU M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  prodE_of M δ u u' F0 what₂ hap (Formalism.L2.SG.Pf.ProdEP2Cut.locIdxC_of_count M δ u u' F0 what₂ hst)

end Formalism.L2.SG.Pf.ProdE
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupFinal
noncomputable section

namespace Formalism.L2.SG.Pf.TupFinal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG

theorem repAtTup_of_stab {D : D7} (Zd : TermLoc.LocDat D) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))
    (hS : Pf.TupGlob.StabApprox Zd u u') : Pf.FibPart.RepAtTup Zd.M Zd.δ u u' F0 what₂ :=
  Pf.TupOnto.repAtTup_of_glob Zd.M Zd.δ u u' F0 what₂ (Pf.TupGlob.globMove_of u u' hS (Pf.FibD.dict_holds Zd))

end Formalism.L2.SG.Pf.TupFinal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LamOfTermScal
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SumFr

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lam_of_termScal {γ γ' : TermDef.Term D u u' F0 what₂} (h : Corank.TermScal D γ γ') : γ'.lam = γ.lam := by
  obtain ⟨p, h1, h2, -⟩ := h
  rw [← h1, ← h2]
  rfl

theorem sumFr_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂)
    (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hP : PrimeHyp D u (Tu D u'))
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hR : IsRowReps D F0 what₂)
    (hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤) :
    SumFr M δ u u' F0 what₂ := by
  intro γ w _ w' hG' _ Z hZ
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, eligRel_holds⟩
  have hclsFin : (clsSet F0 u' γ.lam Z).Finite :=
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin γ.lam γ.mem Z)
  have hfrSub : frPart γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  let S : Set (TermDef.Term D u u' F0 what₂) :=
    {γ' | (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z}
  have hlam : ∀ γ' ∈ S, γ'.lam = γ.lam := fun γ' h => lam_of_termScal h.1.1
  have hrep : ∀ γ' ∈ S, RepIn u u' F0 what₂ γ' Z := fun γ' h => hC hpre γ' w' hG' Z hZ h.1.2 h.2
  have hsub : ∀ γ' ∈ S, PairVal.orbT D u u' F0 what₂ γ' Z ⊆ frPart γ Z := by
    rintro γ' h O ⟨F', hF', hr, rfl⟩
    refine ⟨F', ?_, ⟨γ', h.1.1, hr⟩, ?_⟩
    · have e := hlam γ' h
      rw [e] at hF'
      exact hF'
    · have e := hlam γ' h
      ext F''
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact Iff.rfl
  have horbFin : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Finite := fun γ' h =>
    (hclsFin.subset hfrSub).subset (hsub γ' h)
  have hne : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Nonempty := by
    intro γ' h
    obtain ⟨F', hF', hr⟩ := hrep γ' h
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard = (PairVal.orbT D u u' F0 what₂ γ' Z).ncard := by
    intro γ' h
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ' w' Z h.1.2 hZ (hrep γ' h)]
  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ O ∈ frPart γ Z,
        {γ' : TermDef.Term D u u' F0 what₂ | γ'.lam = γ.lam ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ' Z} := by
      intro γ' h
      obtain ⟨O, hO⟩ := hne γ' h
      simp only [Set.mem_iUnion]
      exact ⟨O, hsub γ' h hO, hlam γ' h, hO⟩
    refine Set.Finite.subset (Set.Finite.biUnion (hclsFin.subset hfrSub) (fun O _ => ?_)) hU
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hbU : (hclsFin.subset hfrSub).toFinset =
      hSfin.toFinset.biUnion (fun γ' => if h : γ' ∈ S then (horbFin γ' h).toFinset else ∅) := by
    ext O
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · rintro ⟨F', hF', ⟨γ', hsc, hr⟩, rfl⟩
      have e := lam_of_termScal hsc
      obtain ⟨Λ, m, c⟩ := γ
      obtain ⟨Λ', m', c'⟩ := γ'
      simp only at e
      subst e
      obtain ⟨hpd, hc⟩ := hr
      have hγ' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) = termOf Λ' m' F' (pd_of_ez hF') := by
        exact congrArg (fun cls => TermDef.Term.mk Λ' m' cls) hc.symm
      have hS' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) ∈ S := by
        refine ⟨⟨hsc, ?_⟩, ?_⟩
        · rw [hγ']
          exact eligAt_termOf Λ' m' hZ hF'
        · rw [hγ']
          exact hD hpre _ w' Z (eligAt_termOf Λ' m' hZ hF') hZ (repIn_termOf Λ' m' hF')
      refine ⟨⟨Λ', m', c'⟩, hS', ?_⟩
      simp only [dif_pos hS', Set.Finite.mem_toFinset]
      exact ⟨F', hF', ⟨hpd, hc⟩, rfl⟩
    · rintro ⟨γ', hγ'S, hO⟩
      have hO' : O ∈ (horbFin γ' hγ'S).toFinset := by simpa only [dif_pos hγ'S] using hO
      exact hsub γ' hγ'S ((Set.Finite.mem_toFinset _).1 hO')
  have hdisj : ∀ γ₁ ∈ hSfin.toFinset, ∀ γ₂ ∈ hSfin.toFinset, γ₁ ≠ γ₂ →
      Disjoint (if h : γ₁ ∈ S then (horbFin γ₁ h).toFinset else ∅)
        (if h : γ₂ ∈ S then (horbFin γ₂ h).toFinset else ∅) := by
    intro γ₁ h₁ γ₂ h₂ hne12
    rw [Set.Finite.mem_toFinset] at h₁ h₂
    rw [dif_pos h₁, dif_pos h₂, Finset.disjoint_left]
    intro O hO₁ hO₂
    rw [Set.Finite.mem_toFinset] at hO₁ hO₂
    exact hne12 (orbT_disj ((hlam γ₁ h₁).trans (hlam γ₂ h₂).symm) hO₁ hO₂)
  have hcount : ((frPart γ Z).ncard : ℝ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (hclsFin.subset hfrSub), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ' hγ' => ?_)
    have h := (Set.Finite.mem_toFinset hSfin).1 hγ'
    rw [dif_pos h, hnc γ' h, Set.ncard_eq_toFinset_card _ (horbFin γ' h)]
  refine ⟨hclsFin.subset hfrSub, ?_⟩
  haveI : Fintype {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} =>
    ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
  have h1 : ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) =
      ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ' => Set.Finite.mem_toFinset hSfin) _
  have h2 : (((frPart γ Z).ncard : ℝ) : ℂ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) := by
    rw [hcount]
    push_cast
    rfl
  have key := h1.symm.trans h2.symm
  have key' : ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) = ((frPart γ Z).ncard : ℂ) := by
    rw [key]
    push_cast
    rfl
  exact Eq.mpr (congrArg (HasSum _) key'.symm) hs

end SumFr

end Formalism.L2.SG.Pf.FibPart
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneSmulApply
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MatAlg

variable {K : Type*} [Field K] {n : ℕ}

theorem lam_form {A Δ : Matrix (Fin n) (Fin n) K} (hA : IsLo A) (a : K) :
    (A + a • Δ) * A⁻¹ = 1 + a • (Δ * A⁻¹) := by
  have hu : IsUnit A.det := by rw [det_lo' hA]; exact isUnit_one
  rw [Matrix.add_mul, Matrix.mul_nonsing_inv A hu, Matrix.smul_mul]

theorem mu_form {B Δ : Matrix (Fin n) (Fin n) K} (hB : IsUp B) (a : K) :
    B⁻¹ * (B + a • Δ) = 1 + a • (B⁻¹ * Δ) := by
  have hu : IsUnit B.det := by rw [det_up' hB]; exact isUnit_one
  rw [Matrix.mul_add, Matrix.nonsing_inv_mul B hu, Matrix.mul_smul]

theorem one_smul_apply (a : K) (N : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (1 + a • N) i j = (if i = j then 1 else 0) + a * N i j := by
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

end MatAlg

section Typed

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem sgn_mem_O (p : PlF D) (k : ℕ) :
    (-1 : (D.s.atP p).Fp) ^ k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) k


set_option maxHeartbeats 4000000 in
theorem locReal_typed (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (hMp : (M p).split ≠ none) :
    LocRealAt M δ u u' p := by
  intro w O hO
  obtain ⟨Y, -, ⟨w₀, -, ⟨ξ, η⟩, hYeq⟩, rfl⟩ := hO
  haveI := (D.s.atP p).lf
  have hAg := (hA p).2.2.2.2.2
  rcases hM' : (M p).split with _ | g
  · exact absurd hM' hMp
  rcases hR : (D.s.atP p).split with _ | sg
  · simp only [hM', hR] at hAg
  simp only [hM', hR] at hAg
  obtain ⟨hge, hgq⟩ := hAg
  set Zd : LocDat D := ⟨δ, M, hA⟩
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  set s : Fin (D.R.rS + 1) → (D.s.atP p).Fp := fun a => (-1) ^ (D.R.rS - a.val) with hsdef
  have hSd : S = Matrix.diagonal s := rfl
  have hs : ∀ a, s a * s a = 1 := fun a => sgn_sq' D.R.rS a
  have hSS : S * S = 1 := sg_sq _
  set cfv := cf Zd p with hcfv
  set cfiv := cfi Zd p with hcfiv
  have hcc : ∀ a, cfv a * cfiv a = 1 := cf_cfi Zd p
  have hcc' : ∀ a, cfiv a * cfv a = 1 := cfi_cf Zd p
  have hdd : Matrix.diagonal cfv * Matrix.diagonal cfiv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hcc]
  have hdd' : Matrix.diagonal cfiv * Matrix.diagonal cfv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hcc']
  have conj1 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv = X := by
    intro X
    rw [show Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv =
      (Matrix.diagonal cfv * Matrix.diagonal cfiv) * X * (Matrix.diagonal cfv * Matrix.diagonal cfiv) by
        simp only [Matrix.mul_assoc], hdd, Matrix.one_mul, Matrix.mul_one]
  have conj2 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv = X := by
    intro X
    rw [show Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv =
      (Matrix.diagonal cfiv * Matrix.diagonal cfv) * X * (Matrix.diagonal cfiv * Matrix.diagonal cfv) by
        simp only [Matrix.mul_assoc], hdd', Matrix.one_mul, Matrix.mul_one]
  have hSt : S.transpose = S := Matrix.diagonal_transpose _
  have sconj : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, S * (S * X * S) * S = X := by
    intro X
    rw [show S * (S * X * S) * S = (S * S) * X * (S * S) by simp only [Matrix.mul_assoc], hSS, Matrix.one_mul,
      Matrix.mul_one]

  obtain ⟨Gl, Gu, hGl, hGu, hM0⟩ := target_fact Zd p sg hR g hM' hge hgq u u' w
  have hGlu : IsUnit Gl.det := by rw [det_lo' hGl]; exact isUnit_one
  have hGuu : IsUnit Gu.det := by rw [det_up' hGu]; exact isUnit_one
  set Λ₀ := Loc.uLow ξ * Gl⁻¹ with hΛ₀
  set V₀ := Gu⁻¹ * Loc.uUp w₀ η with hV₀
  have hΛ₀lo : IsLo Λ₀ := isLo_mul (isLo_uLow ξ) (isLo_inv hGl)
  have hV₀up : IsUp V₀ := isUp_mul (isUp_inv hGu) (isUp_uUp w₀ η)
  have hY : Y = Λ₀ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * V₀ := by
    rw [hYeq, hΛ₀, hV₀]
    rw [show Loc.uLow ξ * Gl⁻¹ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * (Gu⁻¹ * Loc.uUp w₀ η) =
      Loc.uLow ξ * (Gl⁻¹ * Gl) * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * (Gu * Gu⁻¹) * Loc.uUp w₀ η by
        simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul Gl hGlu, Matrix.mul_nonsing_inv Gu hGuu, Matrix.mul_one,
      Matrix.mul_one]
  set A1 := Λ₀.map (p1 sg.e) with hA1
  set A2 := Λ₀.map (p2 sg.e) with hA2
  set B1 := V₀.map (p1 sg.e) with hB1
  set B2 := V₀.map (p2 sg.e) with hB2
  have hA1lo : IsLo A1 := isLo_map _ hΛ₀lo
  have hA2lo : IsLo A2 := isLo_map _ hΛ₀lo
  have hB1up : IsUp B1 := isUp_map _ hV₀up
  have hB2up : IsUp B2 := isUp_map _ hV₀up
  have hΛ₀glue : Λ₀ = glue sg.e A1 A2 := mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])
  have hV₀glue : V₀ = glue sg.e B1 B2 := mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])

  set Lp := glue sg.e (Matrix.diagonal cfiv * A1 * Matrix.diagonal cfv)
    (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S).transpose with hLp
  set Up := glue sg.e (Matrix.diagonal cfv * B1 * Matrix.diagonal cfiv)
    (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S).transpose with hUp
  have hLplo : IsLo Lp := isLo_glue sg.e (isLo_conj hA1lo cfiv cfv hcc')
    (isLo_transpose (isUp_sconj s cfv cfiv hSd hs hcc hB2up))
  have hUpup : IsUp Up := isUp_glue sg.e (isUp_conj hB1up cfv cfiv hcc)
    (isUp_transpose (isLo_sconj s cfiv cfv hSd hs hcc' hA2lo))

  obtain ⟨c', hc'0, hc'⟩ := clear_Fp p
    (ι := (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕
      (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (Sum.elim (fun t => cfv t.2.1 * cfiv t.2.2.1 * (if t.1 = 0 then A1⁻¹ else A2⁻¹) t.2.2.1 t.2.2.2)
      (fun t => (if t.1 = 0 then B1⁻¹ else B2⁻¹) t.2.1 t.2.2.1 * cfiv t.2.2.1 * cfv t.2.2.2))
  haveI := (D.s.atP p).ellPrime
  set ℓ : 𝓞 D.host.F := ((Loc.resChar p : ℕ) : 𝓞 D.host.F) with hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rw [hℓ, Ne, Nat.cast_eq_zero]; exact (Fact.out : (Loc.resChar p).Prime).ne_zero
  have hℓq : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F ℓ) = (sg.q : (D.s.atP p).Fp) := by
    rw [hℓ, map_natCast, map_natCast, sg.q_eq]
  refine ⟨Lp, Up, ℓ * c', mul_ne_zero hℓ0 hc'0, hLplo, hUpup, ?_⟩
  intro L B hL hB hLc hBc
  choose oL hoL hLeq using hLc
  choose oB hoB hBeq using hBc
  set a' := (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c') with ha'
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hq
  have ha : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F (ℓ * c')) = q * a' := by
    rw [map_mul, map_mul, hℓq]
  simp only [ha] at hLeq hBeq
  have hOc : ∀ x ∈ (D.s.atP p).O, p1 sg.e x ∈ 𝒪[(D.s.atP p).Fp] ∧ p2 sg.e x ∈ 𝒪[(D.s.atP p).Fp] := by
    intro x hx
    have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
    rw [← hO] at hx
    have h1 := IntegralGeneration.fst_mem (g := g) hx
    have h2 := IntegralGeneration.snd_mem (g := g) hx
    rw [hge] at h1 h2
    exact ⟨h1, h2⟩
  set oL1 := (Matrix.of oL).map (p1 sg.e) with hoL1
  set oL2 := (Matrix.of oL).map (p2 sg.e) with hoL2
  set oB1 := (Matrix.of oB).map (p1 sg.e) with hoB1
  set oB2 := (Matrix.of oB).map (p2 sg.e) with hoB2
  have hcomp : ∀ (X : PairVal.MatR D) (Xp : MatP D p) (o : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      (∀ i j, (D.s.atP p).ιE (X i j) - Xp i j =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (q * a') * o i j) →
      X.map φ1 = Xp.map (p1 sg.e) + (q * a') • (Matrix.of o).map (p1 sg.e) ∧
      X.map φ2 = Xp.map (p2 sg.e) + (q * a') • (Matrix.of o).map (p2 sg.e) := by
    intro X Xp o h
    refine ⟨?_, ?_⟩
    · ext i j
      have h' := congrArg (p1 sg.e) (h i j)
      rw [map_sub, map_mul, fst_proj_algebraMap] at h'
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ1,
        RingHom.comp_apply]
      rw [← h']; ring
    · ext i j
      have h' := congrArg (p2 sg.e) (h i j)
      rw [map_sub, map_mul, snd_proj_algebraMap] at h'
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ2,
        RingHom.comp_apply]
      rw [← h']; ring
  obtain ⟨hL1, hL2⟩ := hcomp L Lp oL hLeq
  obtain ⟨hB1', hB2'⟩ := hcomp B Up oB hBeq
  have sS : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      S * (S * X * S) * S = X := sconj
  have hΛ1 : Matrix.diagonal cfv * L.map φ1 * Matrix.diagonal cfiv =
      A1 + (q * a') • (Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv) := by
    rw [hL1, hLp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj1, Matrix.mul_smul, Matrix.smul_mul]
  have hV1 : Matrix.diagonal cfiv * B.map φ1 * Matrix.diagonal cfv =
      B1 + (q * a') • (Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv) := by
    rw [hB1', hUp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj2, Matrix.mul_smul, Matrix.smul_mul]
  have hΛ2 : Matrix.diagonal cfv * (S * (B.map φ2).transpose * S) * Matrix.diagonal cfiv =
      A2 + (q * a') • (Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv) := by
    rw [hB2', hUp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S =
      Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv by
        rw [show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S =
          (S * S) * (Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv) * (S * S) by simp only [Matrix.mul_assoc],
          hSS, Matrix.one_mul, Matrix.mul_one], conj1]
  have hV2 : Matrix.diagonal cfiv * (S * (L.map φ2).transpose * S) * Matrix.diagonal cfv =
      B2 + (q * a') • (Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv) := by
    rw [hL2, hLp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S =
      Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv by
        rw [show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S =
          (S * S) * (Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv) * (S * S) by simp only [Matrix.mul_assoc],
          hSS, Matrix.one_mul, Matrix.mul_one], conj2]
  have hA1u : IsUnit A1.det := by rw [det_lo' hA1lo]; exact isUnit_one
  have hA2u : IsUnit A2.det := by rw [det_lo' hA2lo]; exact isUnit_one
  have hB1u : IsUnit B1.det := by rw [det_up' hB1up]; exact isUnit_one
  have hB2u : IsUnit B2.det := by rw [det_up' hB2up]; exact isUnit_one
  set Δ1 := Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv with hΔ1
  set Δ2 := Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv with hΔ2
  set E1 := Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv with hE1
  set E2 := Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv with hE2
  set lam := glue sg.e ((A1 + (q * a') • Δ1) * A1⁻¹) ((A2 + (q * a') • Δ2) * A2⁻¹) with hlam
  set mu := glue sg.e (B1⁻¹ * (B1 + (q * a') • E1)) (B2⁻¹ * (B2 + (q * a') • E2)) with hmu
  have hlamL : (glue sg.e (A1 + (q * a') • Δ1) (A2 + (q * a') • Δ2) : MatP D p) = lam * Λ₀ := by
    refine mat_eq sg.e ?_ ?_
    · rw [Matrix.map_mul, hlam, glue_map_fst, glue_map_fst]
      show A1 + (q * a') • Δ1 = (A1 + (q * a') • Δ1) * A1⁻¹ * A1
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A1 hA1u, Matrix.mul_one]
    · rw [Matrix.map_mul, hlam, glue_map_snd, glue_map_snd]
      show A2 + (q * a') • Δ2 = (A2 + (q * a') • Δ2) * A2⁻¹ * A2
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A2 hA2u, Matrix.mul_one]
  have hVmu : (glue sg.e (B1 + (q * a') • E1) (B2 + (q * a') • E2) : MatP D p) = V₀ * mu := by
    refine mat_eq sg.e ?_ ?_
    · rw [Matrix.map_mul, hmu, glue_map_fst, glue_map_fst]
      show B1 + (q * a') • E1 = B1 * (B1⁻¹ * (B1 + (q * a') • E1))
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B1 hB1u, Matrix.one_mul]
    · rw [Matrix.map_mul, hmu, glue_map_snd, glue_map_snd]
      show B2 + (q * a') • E2 = B2 * (B2⁻¹ * (B2 + (q * a') • E2))
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B2 hB2u, Matrix.one_mul]
  have h1 : CntLocal.ZZP (M := M) δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      lam * Y * mu := by
    have hZ := zz_fact Zd p sg hR g hM' hge hgq u u' w hL hB
    rw [hM0, hΛ1, hΛ2, hV1, hV2, hlamL, hVmu] at hZ
    rw [hZ, hY]
    simp only [Matrix.mul_assoc]

  have hqO : q ∈ 𝒪[(D.s.atP p).Fp] := sg.q.2
  have hR_of : ∀ x : (D.s.atP p).Ep, ∀ t1 t2 : (D.s.atP p).Fp, t1 ∈ 𝒪[(D.s.atP p).Fp] → t2 ∈ 𝒪[(D.s.atP p).Fp] →
      ∀ d : (D.s.atP p).Fp, d ∈ 𝒪[(D.s.atP p).Fp] → sg.e x = (d + q * t1, d + q * t2) → x ∈ (M p).R := by
    intro x t1 t2 ht1 ht2 d hd hx
    rw [IntegralGeneration.mem_R_of_split hM' x, hge, hx, hgq]
    refine ⟨Subring.add_mem _ hd (Subring.mul_mem _ hqO ht1), Subring.add_mem _ hd (Subring.mul_mem _ hqO ht2),
      t1 - t2, Subring.sub_mem _ ht1 ht2, by ring⟩
  have hδO : ∀ i j : Fin (D.R.rS + 1), (if i = j then (1 : (D.s.atP p).Fp) else 0) ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j; split_ifs; exact Subring.one_mem _; exact Subring.zero_mem _
  have hoL1 : ∀ i j, oL1 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoL i j)).1
  have hoL2 : ∀ i j, oL2 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoL i j)).2
  have hoB1 : ∀ i j, oB1 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoB i j)).1
  have hoB2 : ∀ i j, oB2 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoB i j)).2
  have hsO : ∀ a, s a ∈ 𝒪[(D.s.atP p).Fp] := fun a => sgn_mem_O p _
  have hSe : ∀ (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) (i k : Fin (D.R.rS + 1)),
      (S * X.transpose * S) i k = s i * X k i * s k := by
    intro X i k
    rw [hSd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hT1 : ∀ i j, a' * (Δ1 * A1⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hΔ1, conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inl (0, i, k, j))
    simp only [Sum.elim_inl, if_true] at hz
    rw [show a' * (cfv i * oL1 i k * cfiv k * A1⁻¹ k j) = oL1 i k * (a' * (cfv i * cfiv k * A1⁻¹ k j)) by ring]
    exact Subring.mul_mem _ (hoL1 i k) hz
  have hT2 : ∀ i j, a' * (Δ2 * A2⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hΔ2, conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inl (1, i, k, j))
    simp only [Sum.elim_inl, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz
    rw [hSe, show a' * (cfv i * (s i * oB2 k i * s k) * cfiv k * A2⁻¹ k j) =
      (s i * oB2 k i * s k) * (a' * (cfv i * cfiv k * A2⁻¹ k j)) by ring]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO i) (hoB2 k i)) (hsO k)) hz
  have hU1 : ∀ i j, a' * (B1⁻¹ * E1) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hE1, mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inr (0, i, k, j))
    simp only [Sum.elim_inr, if_true] at hz
    rw [show a' * (B1⁻¹ i k * (cfiv k * oB1 k j * cfv j)) = oB1 k j * (a' * (B1⁻¹ i k * cfiv k * cfv j)) by ring]
    exact Subring.mul_mem _ (hoB1 k j) hz
  have hU2 : ∀ i j, a' * (B2⁻¹ * E2) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hE2, mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inr (1, i, k, j))
    simp only [Sum.elim_inr, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz
    rw [hSe, show a' * (B2⁻¹ i k * (cfiv k * (s k * oL2 j k * s j) * cfv j)) =
      (s k * oL2 j k * s j) * (a' * (B2⁻¹ i k * cfiv k * cfv j)) by ring]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO k) (hoL2 j k)) (hsO j)) hz
  have hlo1 : IsLo (A1 + (q * a') • Δ1) := by
    rw [← hΛ1]; exact isLo_conj (isLo_map φ1 hL) _ _ hcc
  have hlo2 : IsLo (A2 + (q * a') • Δ2) := by
    rw [← hΛ2]
    exact isLo_conj (isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc
  have hup1 : IsUp (B1 + (q * a') • E1) := by
    rw [← hV1]; exact isUp_conj (isUp_map φ1 hB) _ _ hcc'
  have hup2 : IsUp (B2 + (q * a') • E2) := by
    rw [← hV2]
    exact isUp_conj (isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc'
  have hlamI : TieN.IntLow (M p) lam := by
    have hlo : IsLo lam := isLo_glue sg.e (isLo_mul hlo1 (isLo_inv hA1lo)) (isLo_mul hlo2 (isLo_inv hA2lo))
    refine ⟨hlo.1, hlo.2, fun i j => ?_⟩
    refine hR_of (lam i j) (a' * (Δ1 * A1⁻¹) i j) (a' * (Δ2 * A2⁻¹) i j) (hT1 i j) (hT2 i j) _ (hδO i j) ?_
    rw [hlam, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, lam_form hA1lo, lam_form hA2lo, one_smul_apply,
      one_smul_apply]
    ring_nf
  have hmuI : TieN.IntUp (M p) mu := by
    have hup : IsUp mu := isUp_glue sg.e (isUp_mul (isUp_inv hB1up) hup1) (isUp_mul (isUp_inv hB2up) hup2)
    refine ⟨hup.1, fun i j hij => hup.2 j i hij, fun i j => ?_⟩
    refine hR_of (mu i j) (a' * (B1⁻¹ * E1) i j) (a' * (B2⁻¹ * E2) i j) (hU1 i j) (hU2 i j) _ (hδO i j) ?_
    rw [hmu, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, mu_form hB1up, mu_form hB2up, one_smul_apply,
      one_smul_apply]
    ring_nf
  have hlamu : IsUnit lam.det := by rw [det_lo' ⟨hlamI.1, hlamI.2.1⟩]; exact isUnit_one
  have hmuu : IsUnit mu.det := by rw [det_up' ⟨hmuI.1, fun a b hab => hmuI.2.1 b a hab⟩]; exact isUnit_one
  have h2 : Y = lam⁻¹ * (lam * Y * mu) * mu⁻¹ := by
    rw [show lam⁻¹ * (lam * Y * mu) * mu⁻¹ = (lam⁻¹ * lam) * Y * (mu * mu⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul lam hlamu, Matrix.mul_nonsing_inv mu hmuu, Matrix.one_mul, Matrix.mul_one]
  unfold tupZ
  exact kkOrb_eq_of hlamI hmuI (intLow_inv hlamI) (intUp_inv hmuI) h1 (by rw [h1]; exact h2)

theorem exist_holds (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) : Exist M δ u u' :=
  exist_of u u' hA (fun p hp => locReal_typed hA u u' p hp)

end Typed

end Formalism.L2.SG.Pf.PCountEx
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_deep {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hsig : (VS D).SigOK) (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hst : ProdEP2Cut.StepsU M δ u u' F0 what₂)
    (hSA : TupGlob.StabApprox ⟨δ, M, hA⟩ u u')
    (hFS : FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂) :
    CutAt M δ L u u' F0 what₂ := by
  have hRA : FibPart.RepAtTup M δ u u' F0 what₂ := TupFinal.repAtTup_of_stab ⟨δ, M, hA⟩ u u' F0 what₂ hSA
  have hTF := FibQ.tupFun_holds M δ u u' F0 what₂
  have hOZ := TupOrb.orbZT_holds M δ u u' F0 what₂
  have hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤ :=
    fun Λ hΛ Z => ZsVolFin.finR D u u' F0 what₂ hrows Z Λ hΛ
  have hN : PairVal.NormRepExists D u u' F0 what₂ := PCount.normRepExists_ctx ⟨hc, hrows, hP⟩
  have hM : Formalism.L2.SG.Pf.NormRepMove D u u' :=
    norm_representative_move D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') (Formalism.L2.SG.Closed.TermEqIff_holds D u u')
      (Formalism.L2.SG.Closed.TermFun_holds D u u') hP hsig
  exact cutAt_of_leaves hA hc hP hrows hN hM (local_phase_typed_places hA) (ZsVolAsm.volIdxProd_of_prodE M δ u u' F0 what₂ hP
      (ProdE.prodE_CZ_of_approxC M δ u u' F0 what₂ (ProdEApprox.approxC M δ u u' F0 what₂) hst))
    (fun _ => PCountEx.exist_holds hA u u')
    (fun _ => FibPart.sumFr_of M δ hTF hRA hOZ hA hc hP hN hrows hfin)
    (fun _ => FrameGlobalPatching.frGlob_of_fstar hFS) (PCount.intGenP_holds ⟨δ, M, hA⟩) PCount.tau_one_holds
    (PCount.partnerCount_holds_all ⟨δ, M, hA⟩)
    (FibPart.fibSum_of M δ hTF hRA hOZ) (densTh_of_ga (SplitCoefficientComponents.GaPlusTh_holds M δ u u'))

def CutLeavesDeep (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (_L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ProdEP2Cut.StepsU M δ u u' F0 what₂ ∧
      TupGlob.StabApprox ⟨δ, M, hA⟩ u u' ∧
      FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂

theorem rowsDatumP_of_deep {D : Formalism.BasicNotions.D7} (h : CutLeavesDeep D) : RowsDatumP D := by
  unfold CutLeavesDeep at h
  unfold RowsDatumP
  intro hsig δ M hA L u u' hc hP F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨hst, hSA, hFS⟩ := h hsig δ M hA L u u' hc hP F0 what₂ hrows
  exact rowsDatum_at (cutAt_of_deep (L := L) hsig hA hc hP hrows hst hSA hFS)
    (eligFinite_of (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') hsig hrows) hrows ϖ hϖ nc hnc

end Formalism.L2.SG.Pf.Coef

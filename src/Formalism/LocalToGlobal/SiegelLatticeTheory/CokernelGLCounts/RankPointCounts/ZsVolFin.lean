module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensAtD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFin
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFin

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal PI.UnitaryGroupMassFormula.CntFormula
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reps (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) :
    ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
      ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K := by
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F₁, hF₁⟩ := hne
    simp only [EZ, Set.mem_ofPred_eq] at hF₁
    have hG := hF₁.1.2.2
    rw [gz_eq, hF₁.2.2.2.2] at hG
    obtain ⟨R, hR1⟩ := rank_gram D _ _ Z hG
    have hfix := fixedOK_of_rows D u F0 what₂ hR hΛ
    obtain ⟨Wf, hWf, hW⟩ := orbit_count_first_stage D (Tn u') F0 Λ hfix Z R hR1
    obtain ⟨Af, hAf, hA⟩ := orbit_count_second_stage D (Tn u') F0 Λ hfix Z R hR1 Wf hWf
    refine ⟨_, finite_level_index D (Tn u') F0 Λ hfix Z R hR1 Wf Af hWf hAf, ?_⟩
    intro F' hF'
    have hx := good_places_integral D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n₁, hn₁, h₁⟩ := hW _ hx
    have hx₁ := good_move D (Tn u') F0 Λ Z hx hn₁
    obtain ⟨n₂, hn₂, h₂, h₃⟩ := hA _ hx₁ h₁
    refine ⟨n₁.trans n₂, (unipotent_integral_isGroup D F0 Λ).2.2 n₁ hn₁ n₂ hn₂, ?_⟩
    refine ⟨good_move D (Tn u') F0 Λ Z hx₁ hn₂, ?_, h₃⟩
    have h₄ : pWf D (act D n₂ (act D n₁ (F'.fl.e, F'.fl.z))) ∈ Wf := h₂ ▸ h₁
    exact h₄
  · exact ⟨∅, Set.finite_empty, fun F' hF' => (hne ⟨F', hF'⟩).elim⟩

theorem fin0 (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨K, hK, hKrep⟩ := reps D u u' F0 what₂ hR Z Λ hΛ
  have hgrp := unipotent_integral_isGroup D F0 Λ
  let g : ((Fin D.R.rS → (VS D).V) × (VS D).V) → Set (LFlag (VS D) D.R.rS (Tn u')) :=
    fun k => {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧
      ∃ n ∈ N0 F0 Λ, ((fun a => n (F''.fl.e a)), n F''.fl.z) = k}
  have hsub : {O | ∃ F' ∈ EZ (Tn u') F0 Λ Z,
      O = {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}} ⊆ g '' K := by
    rintro O ⟨F', hF', rfl⟩
    obtain ⟨n, hn, hk⟩ := hKrep F' hF'
    refine ⟨_, hk, ?_⟩
    ext F''
    simp only [g, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hF'', m, hm, hme⟩
      refine ⟨hF'', n.trans m.symm, hgrp.2.2 n hn _ (hgrp.2.1 m hm), fun a => ?_, ?_⟩
      · have h := congrFun (congrArg Prod.fst hme) a
        simp only at h
        simp [← h]
      · have h := congrArg Prod.snd hme
        simp only at h
        simp [← h]
    · rintro ⟨hF'', m, hm, he, hz⟩
      refine ⟨hF'', m.symm.trans n, hgrp.2.2 _ (hgrp.2.1 m hm) n hn, ?_⟩
      ext a <;> simp [← he, ← hz]
  simp only [cntE]
  exact ((hK.image g).subset hsub).encard_lt_top.ne

theorem finR (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨F1, he1, hz1⟩ := Formalism.MainNotions.S.Inh.tie_flagG_nonempty D u
  have hT : Tn u ≠ 0 := by exact_mod_cast (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u).ne'
  obtain ⟨β, hβ, hβe, hβz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT rfl F0 F1
  have hrows := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hmem : Formalism.HermitianLatticesTheory.gmap β Λ ∈ what₂.image (Formalism.HermitianLatticesTheory.gmap β) := Finset.mem_image_of_mem _ hΛ
  have hRo : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) := by
    refine ⟨?_, ?_, hrows, ⟨_, hmem⟩⟩
    · rw [← he1]
      funext a
      exact hβe a
    · rw [← hz1]
      exact hβz
  have h := fin0 D u u' _ _ hRo Z _ hmem
  rwa [Formalism.L2.SG.Pf.Cnt.counting_iso_inverse D β hβ (Tn u') F0 Λ Z] at h

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbitFinite_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbFinE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hfin := finR D u u' F0 what₂ hH.2.2.1 (ZhatL (lf D F0) F') γ.lam γ.mem
  unfold cntE at hfin
  refine (Set.encard_ne_top_iff.mp hfin).subset ?_
  rintro O ⟨F'', hF'', _, rfl⟩
  exact ⟨F'', hF'', rfl⟩

end Formalism.L2.SG.Pf.ZsVolFin

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioMap
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioRetr
noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

variable {G : Type} [Group G]

structure Retr (S N : Subgroup G) (π : G → G) : Prop where
  le : S ≤ N
  mul : ∀ x ∈ N, ∀ y ∈ N, π (x * y) = π x * π y
  mem : ∀ x ∈ N, π x ∈ S
  id : ∀ s ∈ S, π s = s

theorem Retr.one {S N : Subgroup G} {π : G → G} (h : Retr S N π) : π 1 = 1 := by
  have h1 := h.mul 1 N.one_mem 1 N.one_mem
  rw [mul_one] at h1
  simpa using h1

theorem Retr.inv {S N : Subgroup G} {π : G → G} (h : Retr S N π) {x : G} (hx : x ∈ N) : π x⁻¹ = (π x)⁻¹ := by
  have h1 := h.mul x⁻¹ (N.inv_mem hx) x hx
  rw [inv_mul_cancel, h.one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

def img {S N : Subgroup G} {π : G → G} (h : Retr S N π) (H : Subgroup G) (hH : H ≤ N) : Subgroup G where
  carrier := π '' H
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, H.mul_mem hx hy, h.mul x (hH hx) y (hH hy)⟩
  one_mem' := ⟨1, H.one_mem, h.one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, H.inv_mem hx, h.inv (hH hx)⟩

theorem cj_eq_cj_img {S N : Subgroup G} {π : G → G} (h : Retr S N π) {H : Subgroup G} (hH : H ≤ N) {g₀ : G}
    (hg : g₀ ∈ N) (hC : cj g₀ H ≤ S) : cj g₀ H = cj (π g₀) (img h H hH) := by
  ext y
  rw [mem_cj, mem_cj]
  constructor
  · intro hy
    have hyS : y ∈ S := hC ((mem_cj).2 hy)
    have hyN : y ∈ N := h.le hyS
    refine (Set.mem_image π _ _).2 ⟨g₀ * y * g₀⁻¹, hy, ?_⟩
    rw [h.mul _ (N.mul_mem hg hyN) _ (N.inv_mem hg), h.mul _ hg _ hyN, h.inv hg, h.id y hyS]
  · intro hy
    obtain ⟨x, hx, hxe⟩ := (Set.mem_image π _ _).1 hy
    have hz : g₀⁻¹ * x * g₀ ∈ cj g₀ H := by
      rw [mem_cj]
      simpa [mul_assoc] using hx
    have hzS := hC hz
    have e1 : π (g₀⁻¹ * x * g₀) = g₀⁻¹ * x * g₀ := h.id _ hzS
    rw [h.mul _ (N.mul_mem (N.inv_mem hg) (hH hx)) _ hg, h.mul _ (N.inv_mem hg) _ (hH hx), h.inv hg,
      hxe] at e1
    have hyz : y = g₀⁻¹ * x * g₀ := by
      rw [← e1]
      group
    rw [hyz]
    simpa [mul_assoc] using hx

end Formalism.L2.SG.Pf.ProdEP2Core
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

abbrev GG (p : PlF D) : Type := GLp p × (GLp p)ᵐᵒᵖ

def KP (p : PlF D) : Subgroup (GG p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) ((x.1 : GLp p) : MP p) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) ((x.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.intLow_one _, ZsVolGrp.intUp_one _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1 * y.1 : GLp p)) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1)⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.intLow_inv _ hx1).1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) ((((x.2)⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.intUp_inv _ hx2).1

def StabX (p : PlF D) (X : MP p) : Subgroup (GG p) where
  carrier := {x | ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) = X}
  one_mem' := by simp
  mul_mem' := by
    rintro x y hx hy
    show ((x.1 * y.1 : GLp p) : MP p) * X * (((x.2 * y.2).unop : GLp p) : MP p) = X
    rw [MulOpposite.unop_mul, Units.val_mul, Units.val_mul]
    calc (x.1 : MP p) * (y.1 : MP p) * X * (((y.2.unop : GLp p) : MP p) * ((x.2.unop : GLp p) : MP p))
        = (x.1 : MP p) * ((y.1 : MP p) * X * ((y.2.unop : GLp p) : MP p)) * ((x.2.unop : GLp p) : MP p) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [show (y.1 : MP p) * X * ((y.2.unop : GLp p) : MP p) = X from hy]; exact hx
  inv_mem' := by
    rintro x hx
    have hx' : ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) = X := hx
    show (((x.1)⁻¹ : GLp p) : MP p) * X * ((((x.2)⁻¹).unop : GLp p) : MP p) = X
    rw [MulOpposite.unop_inv]
    have h1 : (((x.1)⁻¹ : GLp p) : MP p) * (x.1 : MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : ((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    conv_lhs => rw [← hx']
    calc (((x.1)⁻¹ : GLp p) : MP p) * ((x.1 : MP p) * X * ((x.2.unop : GLp p) : MP p)) *
          (((x.2.unop)⁻¹ : GLp p) : MP p)
        = ((((x.1)⁻¹ : GLp p) : MP p) * (x.1 : MP p)) * X *
            (((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p)) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

variable {p : PlF D}

def g0 (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) : GG p :=
  (⟨lOf δ M p L U, lOf δ M p L⁻¹ U⁻¹,
      (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (lp_inv M δ hA L U hL hU), lp_inv M δ hA L U hL hU⟩,
    MulOpposite.op ⟨ρOf δ M p L U, ρOf δ M p L⁻¹ U⁻¹, up_inv M δ hA L U hL hU,
      (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (up_inv M δ hA L U hL hU)⟩)

def XP (w : Point D.host.E (D.R.rS + 1)) (L U : Formalism.L2.SG.PairVal.MatR D) : MP p :=
  lOf δ M p L U * Y0 M δ u u' w p * ρOf δ M p L U

def Ag (w : Point D.host.E (D.R.rS + 1)) : Subgroup (GG p) := (AP M δ u u' w p).map (StP M δ u u' w p).subtype

def Cg (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) : Subgroup (GG p) :=
  (CPL M δ u u' w hA L U hL hU).map (StP M δ u u' w p).subtype

theorem idxRatio_map {G : Type} [Group G] (S : Subgroup G) (A C : Subgroup S) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A C = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.map S.subtype) (C.map S.subtype) := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective]

def CShapeAt (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) : Prop :=
  Cg M δ u u' w hA L U hL hU = cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U))

def CountAt (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (v : ℝ) : Prop :=
  ∃ (N : Subgroup (GG p)) (π : GG p → GG p) (hR : Retr (StP M δ u u' w p) N π)
    (hHN : KP M p ⊓ StabX p (XP M δ u u' w L U) ≤ N),
    g0 M δ hA L U hL hU ∈ N ∧ img hR _ hHN ≤ Ag M δ u u' w ∧ (img hR _ hHN).relIndex (Ag M δ u u' w) ≠ 0 ∧
      v = ((img hR _ hHN).relIndex (Ag M δ u u' w) : ℝ)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

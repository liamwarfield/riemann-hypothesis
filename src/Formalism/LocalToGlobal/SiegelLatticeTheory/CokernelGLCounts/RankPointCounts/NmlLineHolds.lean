module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsomHTSymm
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.YvMemUUE
noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem X_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).1

theorem X'_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).2

theorem z_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.z ∈ UUE Λ F F' := by
  rw [← hL.2]
  exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))

theorem z'_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  rw [← hL'.2]
  exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem yv_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') :
    yv F.fl F'.fl ∈ UUE Λ F F' := by
  have hf : ∀ b, F'.fl.fvec b ∈ UUE Λ F F' := by
    intro b
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact z'_mem_UUE Λ hΛ.toIsLattice F F' hL hL'
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact X'_le_UUE Λ hΛ F F' hL hL' (Submodule.subset_span ⟨i, rfl⟩)
  unfold yv omp
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hf b))) (Submodule.smul_mem _ _ (z_mem_UUE Λ hΛ.toIsLattice F F' hL hL'))

theorem hT_Hp_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT h v = 0 := by
  rw [hT_swap v h, Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv, star_zero]

theorem hT_UUE_Hp (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT v h = 0 :=
  Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv

theorem hT_X_yv (F : FlagG S r T) (F' : FlagG S r T') {x : S.V} (hx : x ∈ F.X) : S.hT x (yv F F') = 0 := by
  have hker : F.X ≤ LinearMap.ker (S.hT (yv F F')) := by
    rw [Formalism.MainNotions.S.FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hT_swap]
    have h := brS_yv_e (F := F) (F' := F') a
    rw [Formalism.MainNotions.S.brS] at h
    rw [h, star_zero]
  have h1 : S.hT (yv F F') x = 0 := hker hx
  rw [hT_swap, h1, star_zero]

theorem hT_z_yv (F : FlagG S r T) (F' : FlagG S r T') : S.hT F.z (yv F F') = 0 := by
  have h := pairing_yVector_z (F := F) (F' := F')
  rwa [Formalism.MainNotions.S.brS] at h

theorem UUE_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UUE Λ F' F = UUE Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.UUE Formalism.MainNotions.S.Lat.UU
  congr 1
  ac_rfl

theorem Hp_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp Λ F' F = Hp Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.Hp
  rw [UUE_symm]

theorem line_pair (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (Fl : LFlag S r T) (F1 F2 : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ F1) (hL2 : IsLift Λ F2) (hG1 : Gval Fl F1 ≠ 0) (hG12 : Gval Fl F2 = Gval Fl F1)
    (hT : T ≠ 0) (hTs : star T = T) (hTh : Th Λ Fl F1 F2 β = Hp Λ Fl F1) :
    yv Fl.fl F2.fl - (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) •
        yv Fl.fl F1.fl ∈ Fl.fl.X ∧
      (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) *
        star (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) = 1 := by
  set y1 := yv Fl.fl F1.fl with hy1
  set y2 := yv Fl.fl F2.fl with hy2
  set c := brS S y2 y1 / brS S y1 y1 with hc
  have hG1' : Formalism.MainNotions.S.Gflag Fl.fl F1.fl ≠ 0 := hG1
  have hb1 : brS S y1 y1 ≠ 0 := by
    rw [hy1, brS_yv_yv Fl.fl F1.fl hTs]
    exact mul_ne_zero hT hG1'
  have hb12 : brS S y2 y2 = brS S y1 y1 := by
    rw [hy1, hy2, brS_yv_yv Fl.fl F2.fl hTs, brS_yv_yv Fl.fl F1.fl hTs]
    exact congrArg (T * ·) hG12
  obtain ⟨hfin, hk1⟩ := Formalism.L2.SG.NGCut.CorankRelation.finrank_Hp k hdim Λ hΛ Fl F1 hL hL1 hG1

  have hy2H : ∀ h ∈ Hp Λ Fl F1, S.hT h y2 = 0 := by
    intro h hh
    rw [← hTh] at hh
    unfold Formalism.MainNotions.S.Lat.Th at hh
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs] at hp
    obtain ⟨-, hp2, hpX, -⟩ := hp
    have e : p.1 = (p.1 - p.2) + p.2 := by abel
    simp only [LinearMap.fst_apply]
    rw [e, map_add (f := _), LinearMap.add_apply, hT_X_yv Fl.fl F2.fl hpX,
      hT_Hp_UUE Λ Fl F2 hp2 (yv_mem_UUE Λ hΛ Fl F2 hL hL2), add_zero]
  have hv : y2 - c • y1 ∈ Fl.fl.X := by
    refine Formalism.L2.SG.NGCut.NormalVectorPairings.line Fl.fl hT (Hp Λ Fl F1) ?_ ?_ ?_ ?_ ?_ hb1 ?_ ?_
    · intro x hx h hh
      exact hT_UUE_Hp Λ Fl F1 hh (X_le_UUE Λ hΛ Fl F1 hL hL1 hx)
    · intro h hh
      exact hT_UUE_Hp Λ Fl F1 hh (z_mem_UUE Λ hΛ.toIsLattice Fl F1 hL hL1)
    · intro x hx hxH
      exact Formalism.L2.SG.NGCut.CorankRelation.Xsp_Hp_eq_zero Λ hΛ Fl F1 hL hL1 hG1 hx hxH
    · omega
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      exact ⟨fun x hx => hT_X_yv Fl.fl F1.fl hx, hT_z_yv Fl.fl F1.fl,
        fun h hh => hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1)⟩
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      refine ⟨fun x hx => ?_, ?_, fun h hh => ?_⟩
      · rw [map_sub, map_smul, hT_X_yv Fl.fl F2.fl hx, hT_X_yv Fl.fl F1.fl hx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hT_z_yv, hT_z_yv, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hy2H h hh, hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1),
          smul_zero, sub_zero]
    · rw [sub_eq_add_neg, ← neg_smul, brS_add_left, brS_smul_left, hc]
      field_simp
      ring
  refine ⟨hv, ?_⟩

  set x := y2 - c • y1 with hx
  have hy2x : y2 = x + c • y1 := by
    rw [hx]
    abel
  have hxx : brS S x x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_X Fl.fl hv hv
  have hyx : brS S y1 x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_yv Fl.fl F1.fl hv
  have hxy : brS S x y1 = 0 := by
    rw [Formalism.MainNotions.S.brS, hT_swap, hT_X_yv Fl.fl F1.fl hv, star_zero]
  have hmod : brS S y2 y2 = c * star c * brS S y1 y1 := by
    rw [hy2x, brS_add_left, brS_add_right, brS_add_right, brS_smul_left, brS_smul_left,
      brS_smul_right, brS_smul_right, hxx, hxy, hyx]
    ring
  rw [hb12] at hmod
  have h1 : (1 : E) * brS S y1 y1 = c * star c * brS S y1 y1 := by rw [one_mul]; exact hmod
  exact (mul_right_cancel₀ hb1 h1).symm

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem isom_hT {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) : S.hT (γ x) (γ y) = S.hT x y := h x y

theorem mapLF_fl {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T') :
    (mapLF γ L).fl = mapFlag γ h L.fl := by
  unfold mapLF; rw [dif_pos h]

theorem mapLF_fl_z {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T') :
    (mapLF γ L).fl.z = γ L.fl.z := by
  rw [mapLF_fl h]; rfl

private theorem mapFlag_fvec' {T0 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (i : Fin (r + 1)) : (mapFlag γ h F).fvec i = γ (F.fvec i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

private theorem Zhat_mapFlag' {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    Zhat (mapFlag γ h F) (mapFlag γ h F') = Zhat F F' := by
  ext a b
  simp [Zhat, brS, mapFlag_fvec', isom_hT h]

private theorem Gflag_mapFlag {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    Gflag (mapFlag γ h F) (mapFlag γ h F') = Gflag F F' := by
  simp only [Gflag, Dl, Zhat_mapFlag']

private theorem yv_mapFlag {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    yv (mapFlag γ h F) (mapFlag γ h F') = γ (yv F F') := by
  simp only [yv, omp, Dl, Zhat_mapFlag', mapFlag_fvec']
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, mapFlag]

private theorem mapFlag_X' {T0 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) : (mapFlag γ h F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  simp only [FlagG.X, mapFlag]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

private theorem mem_Hp_iff_orthogonal {T0 T1 : E} (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T0) (F' : LFlag S r T1)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') (h : S.V) :
    h ∈ Hp Λ F F' ↔ ((∀ x ∈ F.fl.X, S.hT x h = 0) ∧ S.hT F.fl.z h = 0 ∧
      (∀ x ∈ F'.fl.X, S.hT x h = 0) ∧ S.hT F'.fl.z h = 0) := by
  constructor
  · intro hh
    exact ⟨fun x hx => hT_UUE_Hp Λ F F' hh (X_le_UUE Λ hΛ F F' hF hF' hx),
      hT_UUE_Hp Λ F F' hh (z_mem_UUE Λ hΛ.toIsLattice F F' hF hF'),
      fun x hx => hT_UUE_Hp Λ F F' hh (X'_le_UUE Λ hΛ F F' hF hF' hx),
      hT_UUE_Hp Λ F F' hh (z'_mem_UUE Λ hΛ.toIsLattice F F' hF hF')⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hU : UU Λ F F' ≤ (LinearMap.ker (S.hT.flip h)).restrictScalars
        (NumberField.RingOfIntegers E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro x hx
        simpa using h1 x hx.2
      · rw [Submodule.span_singleton_le_iff_mem, hF.2]
        simpa using h2
      · intro x hx
        simpa using h3 x hx.2
      · rw [Submodule.span_singleton_le_iff_mem, hF'.2]
        simpa using h4
    have key : UUE Λ F F' ≤ LinearMap.ker (S.hT.flip h) := by
      unfold UUE spanE
      rw [Submodule.span_le]
      intro u hu
      exact hU hu
    simp only [Hp, orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro u hu
    simpa using key hu

private theorem isLattice_sup_span_singleton (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (v : S.V) :
    Submodule.IsFullLattice E (Λ ⊔ Submodule.span (NumberField.RingOfIntegers E) {v}) := by
  let : Submodule.IsFullLattice E Λ := hΛ
  exact Submodule.IsFullLattice.of_le_of_fg E le_sup_left
    (hΛ.fg.sup (Submodule.fg_span_singleton v))

private theorem flagG_ext_of_e_eq_of_z_eq {T0 : E} (F G : FlagG S r T0) (he : F.e = G.e) (hz : F.z = G.z) :
    F = G := by
  cases F
  cases G
  simp only at he hz
  subst he
  subst hz
  rfl

theorem line_pair' (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (Fl : LFlag S r T) (L0 : LFlag S r T') (γ1 γ2 : S.V ≃ₗ[E] S.V)
    (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ2 : γ2 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ (mapLF γ1 L0)) (hL2 : IsLift Λ (mapLF γ2 L0))
    (hG1 : Gval Fl (mapLF γ1 L0) ≠ 0) (hG12 : Gval Fl (mapLF γ2 L0) = Gval Fl (mapLF γ1 L0))
    (hT' : T' ≠ 0) (hTs' : star T' = T')
    (hTh : Th Λ Fl (mapLF γ1 L0) (mapLF γ2 L0) (γ2 * γ1⁻¹) = Hp Λ Fl (mapLF γ1 L0)) :
    γ2.symm (yv (mapLF γ2 L0).fl Fl.fl) -
        (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) •
        γ1.symm (yv (mapLF γ1 L0).fl Fl.fl) ∈ L0.fl.X ∧
      (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) *
        star (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) = 1 := by
  have hδ : γ1 * γ2⁻¹ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem hγ1 (inv_mem hγ2)
  set δ := γ1 * γ2⁻¹ with hδd
  set Λ' := Λ ⊔ Submodule.span (NumberField.RingOfIntegers E) {δ Fl.fl.z} with hΛ'd
  have hΛ' : Submodule.IsFullLattice E Λ' := isLattice_sup_span_singleton Λ hΛ _
  have hle : Λ ≤ Λ' := le_sup_left
  have hL1' : IsLift Λ' (mapLF γ1 L0) := ⟨hle hL1.1, hL1.2⟩
  have hL' : IsLift Λ' Fl := ⟨hle hL.1, hL.2⟩
  have hB : IsLift Λ' (mapLF δ Fl) := by
    refine ⟨?_, ?_⟩
    · rw [mapLF_fl_z hδ]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · simp only [mapLF, dif_pos hδ]
      rw [hL.2]
      rfl
  have eF1 : (mapLF γ1 L0).fl = mapFlag γ1 hγ1 L0.fl := mapLF_fl hγ1 L0
  have eF2 : (mapLF γ2 L0).fl = mapFlag γ2 hγ2 L0.fl := mapLF_fl hγ2 L0
  have eB : (mapLF δ Fl).fl = mapFlag δ hδ Fl.fl := mapLF_fl hδ Fl
  have eflag : mapFlag γ1 hγ1 L0.fl = mapFlag δ hδ (mapFlag γ2 hγ2 L0.fl) := by
    apply flagG_ext_of_e_eq_of_z_eq
    · funext a
      simp [mapFlag, hδd]
    · simp [mapFlag, hδd]
  have hb : yv (mapLF γ1 L0).fl (mapLF δ Fl).fl = δ (yv (mapLF γ2 L0).fl Fl.fl) := by
    rw [eF1, eB, eF2, eflag, yv_mapFlag]
  have hGA : Gval (mapLF γ1 L0) Fl ≠ 0 := by
    simp only [Gval]
    rw [Gflag_swap]
    exact hG1
  have hGB : Gval (mapLF γ1 L0) (mapLF δ Fl) = Gval (mapLF γ1 L0) Fl := by
    have e1 : Gflag (mapLF γ1 L0).fl (mapLF δ Fl).fl = Gflag (mapLF γ2 L0).fl Fl.fl := by
      rw [eF1, eB, eF2, eflag, Gflag_mapFlag]
    have e2 : Gflag (mapLF γ1 L0).fl Fl.fl = Gflag Fl.fl (mapLF γ1 L0).fl := Gflag_swap _ _
    have e3 : Gflag (mapLF γ2 L0).fl Fl.fl = Gflag Fl.fl (mapLF γ2 L0).fl := Gflag_swap _ _
    show Gflag (mapLF γ1 L0).fl (mapLF δ Fl).fl = Gflag (mapLF γ1 L0).fl Fl.fl
    rw [e1, e2, e3]
    exact hG12
  have hTh' : Th Λ' (mapLF γ1 L0) Fl (mapLF δ Fl) δ = Hp Λ' (mapLF γ1 L0) Fl := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
      exact hp.1.1.1
    · intro h hh
      have hh1 := (mem_Hp_iff_orthogonal Λ' hΛ' (mapLF γ1 L0) Fl hL1' hL' h).1 hh
      have hh0' : h ∈ Hp Λ (mapLF γ1 L0) Fl := (mem_Hp_iff_orthogonal Λ hΛ (mapLF γ1 L0) Fl hL1 hL h).2 hh1
      have hh0 : h ∈ Hp Λ Fl (mapLF γ1 L0) := by
        rw [Hp_symm]
        exact hh0'
      rw [← hTh] at hh0
      obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hh0
      obtain ⟨⟨⟨hpa, hpb⟩, hpc⟩, hpd⟩ := hp
      have hp1' : p.1 = h := hp1
      have hpc' : p.1 - p.2 ∈ Fl.fl.X := hpc
      have hpd' : (γ2 * γ1⁻¹) p.1 - p.2 ∈ (mapLF γ2 L0).fl.X := hpd
      have c2 := (mem_Hp_iff_orthogonal Λ hΛ Fl (mapLF γ2 L0) hL hL2 p.2).1 hpb
      have hXF1 : (mapLF γ1 L0).fl.X = ((mapLF γ2 L0).fl.X).map (δ : S.V →ₗ[E] S.V) := by
        rw [eF1, eF2, eflag, mapFlag_X']
      have hXB : (mapLF δ Fl).fl.X = (Fl.fl.X).map (δ : S.V →ₗ[E] S.V) := by
        rw [eB, mapFlag_X']
      have hzF1 : (mapLF γ1 L0).fl.z = δ (mapLF γ2 L0).fl.z := by
        rw [mapLF_fl_z hγ1, mapLF_fl_z hγ2]
        simp [hδd]
      have hzB : (mapLF δ Fl).fl.z = δ Fl.fl.z := mapLF_fl_z hδ Fl
      refine Submodule.mem_map.2 ⟨(h, δ p.2), ⟨⟨⟨hh, ?_⟩, ?_⟩, ?_⟩, rfl⟩
      · refine (mem_Hp_iff_orthogonal Λ' hΛ' (mapLF γ1 L0) (mapLF δ Fl) hL1' hB (δ p.2)).2 ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [hXF1] at hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
          rw [show (δ : S.V →ₗ[E] S.V) y = δ y from rfl, isom_hT hδ]
          exact c2.2.2.1 y hy
        · rw [hzF1, isom_hT hδ]
          exact c2.2.2.2
        · intro x hx
          rw [hXB] at hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
          rw [show (δ : S.V →ₗ[E] S.V) y = δ y from rfl, isom_hT hδ]
          exact c2.1 y hy
        · rw [hzB, isom_hT hδ]
          exact c2.2.1
      · show h - δ p.2 ∈ Xsp (mapLF γ1 L0)
        show h - δ p.2 ∈ (mapLF γ1 L0).fl.X
        rw [hXF1]
        refine Submodule.mem_map.2 ⟨_, hpd', ?_⟩
        rw [← hp1']
        simp [hδd, map_sub]
      · show δ h - δ p.2 ∈ (mapLF δ Fl).fl.X
        rw [hXB]
        refine Submodule.mem_map.2 ⟨_, hpc', ?_⟩
        rw [← hp1']
        simp [map_sub]
  have LP := line_pair k hdim Λ' hΛ' (mapLF γ1 L0) Fl (mapLF δ Fl) δ hL1' hL' hB hGA hGB hT' hTs' hTh'
  rw [hb] at LP
  set w1 := yv (mapLF γ1 L0).fl Fl.fl with hw1
  set w2 := yv (mapLF γ2 L0).fl Fl.fl with hw2
  have hc1 : brS S (δ w2) w1 = brS S (γ2.symm w2) (γ1.symm w1) := by
    simp only [brS]
    rw [← isom_hT hγ1 (γ1.symm w1) (γ2.symm w2)]
    simp [hδd]
  have hc2 : brS S w1 w1 = brS S (γ1.symm w1) (γ1.symm w1) := by
    simp only [brS]
    rw [← isom_hT hγ1 (γ1.symm w1) (γ1.symm w1)]
    simp
  rw [hc1, hc2] at LP
  refine ⟨?_, LP.2⟩
  have hX : (mapLF γ1 L0).fl.X = L0.fl.X.map (γ1 : S.V →ₗ[E] S.V) := by
    rw [eF1, mapFlag_X']
  have h1 := LP.1
  rw [hX] at h1
  obtain ⟨a, ha, hae⟩ := Submodule.mem_map.1 h1
  convert ha using 1
  apply γ1.injective
  rw [show (γ1 : S.V →ₗ[E] S.V) a = γ1 a from rfl] at hae
  rw [hae]
  simp [hδd, map_sub, map_smul]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem G_ne_of_Gt {t : TauC Y u u'} (h : Gt t ≠ 0) : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
  intro h'
  apply h
  simp only [Formalism.L2.SG.TermOp.Gt]
  rw [if_pos]
  exact (Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _).trans h'

theorem line_occ (t0 t : TauC Y u u') (h0 : Gt t0 ≠ 0) (h : Gt t ≠ 0) (hR : RelC Y u u' t0 t) (hG : t.G = t0.G)
    (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') :
    (yT Y u u' t - coefA Y u u' t0 t • yT Y u u' t0 ∈ (X.Fu u).X ∧
      coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1) ∧
    (yT' Y u u' t - coefA' Y u u' t0 t • yT' Y u u' t0 ∈ (X.Fu u').X ∧
      coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1) := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  obtain ⟨hrow, hs0⟩ := hR
  have hlam : t.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
  have hlam' : t.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
  have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
  have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
  have hL1 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
  have hL2 : IsLift t0.lam t.frame := by rw [← hlam]; exact t.rep.2.2.2.2.1
  have hG1 := G_ne_of_Gt Y h0
  have hG12 : Gval (lf D (X.Fu u)) t.frame = Gval (lf D (X.Fu u)) t0.frame := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, hG]
  have hs0' : Lat.s0 t0.lam (lf D (X.Fu u)) t0.frame t.frame (t.lin * t0.lin⁻¹) D.R.k = 1 := by
    have h1 : Formalism.L2.SG.TermOp.s0T t0 t = 1 := hs0
    unfold Formalism.L2.SG.TermOp.s0T at h1
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩] at h1
    exact h1
  have hTh := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t.frame _ hLF hL1 hG1).1 hs0'
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTs : star ((Tu D u : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := star_natCast _
  have hTs' : star ((Tu D u' : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E) := star_natCast _
  refine ⟨line_pair D.R.k hdim t0.lam hlat (lf D (X.Fu u)) t0.frame t.frame _ hLF hL1 hL2 hG1 hG12 hTE hTs hTh,
    line_pair' D.R.k hdim t0.lam (by first | exact hlat | exact hlat.toIsLattice) (lf D (X.Fu u)) (lf D (X.Fu u')) t0.lin t.lin t0.rep.2.2.1 t.rep.2.2.1 hLF
      hL1 hL2 hG1 hG12 hTE' hTs' hTh⟩

theorem NmlLine_holds : NmlLine := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC γ hγ t0 t h0 h hp0 hp hR => ?_⟩
  unfold Formalism.L2.SG.NGCut.Ctx at hC
  have hT : 3 ≤ Tu D u := hC.2.1.2.2.2.1
  have hT' : 3 ≤ Tu D u' := hC.2.1.2.2.2.2.1
  have hG : t.G = t0.G := by
    have e := gval_occ Y t (by rw [hp]; exact hγ)
    have e0 := gval_occ Y t0 (by rw [hp0]; exact hγ)
    rw [hp] at e
    rw [hp0] at e0
    have e1 : t.G = Gval (lf D (X.Fu u)) t.frame :=
      Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _
    have e2 : t0.G = Gval (lf D (X.Fu u)) t0.frame :=
      Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _
    rw [e1, e2, e, e0]
  have L := line_occ Y t0 t h0 h hR hG hT hT'
  exact ⟨L.1.2, L.2.2⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings

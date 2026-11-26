module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaConj
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.MatchGen
noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dn_match_gen (T : Forms0 D u) (v : (D.mem u).A.vT) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδv : bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 = 1) (c c2 c1 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κd : T.cls0.lev.U)
    (hrel : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (hLc : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c)
    (hLd : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c)
    (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (x2 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c2))
    (hxy : ∀ w, x2 w = x (dniEquiv T v c2 c γd hLc hLd w))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (hs1 : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η.1 = 1)
    (hs2 : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η2.1 = 1)
    (h1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c2).1 * η2.1 * κ2.1)
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hl2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2))
    (hf1 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = x (T.lv0.prk v c ⟨_, hw⟩))
    (hf2 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x2 (T.lv0.prk v c2 ⟨_, hw⟩)) :
    η2.1⁻¹ * κd.1 * η.1 ∈ T.cls0.lev.U := by
  classical
  set g' : GL (Fin (D.R.N 0)) D.host.E := γd * γ2.1 with hg'
  have hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    rw [hg', Units.val_mul]
    exact rlv_chainP _ _ _ (by rw [hLc]) hl2
  have hLkinv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c2 :=
    dni_inv_eq γd (dni_lk T v c2 c _ hLc hLd)
  have hf' : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x (T.lv0.prk v c ⟨_, hw⟩) := by
    intro w hw
    have e1 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) = γ2.1.1 *ᵥ w.1 := by
      rw [hg', Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hw2 : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := by
      rw [← e1]; exact dni_mem_of _ hLkinv hw
    rw [hf2 w hw2, hxy, dniEquiv_prk]
    refine congrArg x (congrArg (T.lv0.prk v c) (Subtype.ext ?_))
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (γ2.1.1 *ᵥ w.1) = (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1
    rw [hg', Units.val_mul, Matrix.mulVec_mulVec]
  have hPc := dnk_latP T v c c1 c3 x γ.1 g' hl1 hf1 hl' hf'
  set Γ : GL (Fin (D.R.N 0)) D.host.E := γ2.1⁻¹ * γd⁻¹ * γ.1 with hΓdef
  have hPΓ : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    have e2 : (γ.1⁻¹ * g')⁻¹ = Γ := by rw [hg', hΓdef]; group
    have := localization_inv_smul_eq _ (γ.1⁻¹ * g') hPc
    rwa [e2] at this
  have hPdΓ : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    have e3 : g'⁻¹ * γ.1 = Γ := by rw [hg', hΓdef]; group
    have := localization_smul_cancel _ g' γ.1 (hl1.trans hl'.symm)
    rwa [e3] at this
  have hΓU : Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := mul_mem (mul_mem (inv_mem γ2.2) (inv_mem hγd)) γ.2
  have hUΓ := matching_unitary_eq T.cls0 c c1 c2 c3 γ.1 γ2.1 γd η η2 δ κ κ2 κd h1 h2 hrel
  have hQd : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (Ld D u 0 (Nat.zero_le _) c3) :=
    local_dual_Q_eq_of_P T.atT v c3 c1 Γ hΓU hPΓ
  have eΓ : ∀ z, (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) = γ.1.1 *ᵥ z := by
    intro z
    have e4 : g' * Γ = γ.1 := by rw [hg', hΓdef]; group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e4]
  have hF : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩) := by
    intro z hz
    obtain ⟨b, hbP, hbQ, hb⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPdΓ.le hQd.le
      (x := (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ⟨z, hz, rfl⟩
    obtain ⟨r, hr, b', hb'⟩ := rlv_norm T.atT v b hbP hbQ
    have hmem : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
      rw [hb', mul_smul]; exact Submodule.smul_mem _ _ hb
    refine ⟨r, hr, hmem, ?_⟩
    have hγz : γ.1.1 *ᵥ z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
      rw [← hl1]; exact mem_localization_of_mem₂ _ ⟨z, hz, rfl⟩
    obtain ⟨s, hs, hsz⟩ := (rlv_mem_locP _ _ _).1 hγz
    set R := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r with hR
    have e4 : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • (R • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))) = R • (s • (γ.1.1 *ᵥ z)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, eΓ, smul_comm]
    have e5 : γ.1.1 *ᵥ (s • (R • z)) = R • (s • (γ.1.1 *ᵥ z)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]
    have hin : R • (s • (γ.1.1 *ᵥ z)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left (Submodule.smul_mem _ R hsz)
    have hRz : R • z ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz
    obtain ⟨w3, hw3def⟩ : ∃ w3 : ↥(Ld D u 0 (Nat.zero_le _) c3), w3.1 = s • (R • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) :=
      ⟨s • (⟨_, hmem⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)), rfl⟩
    obtain ⟨w1, hw1def⟩ : ∃ w1 : ↥(Ld D u 0 (Nat.zero_le _) c1), w1.1 = s • (R • z) :=
      ⟨s • (⟨R • z, hRz⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)), rfl⟩
    have hw3 : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by rw [hw3def, e4]; exact hin
    have hw1 : γ.1.1 *ᵥ w1.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by rw [hw1def, e5]; exact hin
    have hA := hf' w3 hw3
    have hB := hf1 w1 hw1
    have ew3 : w3 = s • (⟨_, hmem⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)) := Subtype.ext hw3def
    have ew1 : w1 = s • (⟨R • z, hRz⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)) := Subtype.ext hw1def
    have pA : T.lv0.pr v c3 w3 = T.atT.res v s • T.lv0.pr v c3 ⟨_, hmem⟩ := by rw [ew3, T.lv0.pr_smul]
    have pB : T.lv0.pr v c1 w1 = T.atT.res v s • T.lv0.pr v c1 ⟨R • z, hRz⟩ := by rw [ew1, T.lv0.pr_smul]
    rw [pA, map_smul] at hA
    rw [pB, map_smul] at hB
    have hres : T.atT.res v s ≠ 0 := fun h0 => hs (RingHom.mem_ker.2 h0)
    have key : T.atT.res v s • (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, hmem⟩) =
        T.atT.res v s • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨R • z, hRz⟩) := by
      refine hA.trans (Eq.trans ?_ hB.symm)
      refine congrArg x (congrArg (T.lv0.prk v c) (Subtype.ext ?_))
      show (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 = γ.1.1 *ᵥ w1.1
      rw [hw3def, hw1def, e4, e5]
    exact smul_right_injective _ hres key
  have hloc := local_unitary_of_matching_zero T v c3 c1 Γ hΓU hUΓ hPΓ hPdΓ hF
  exact matching_move_mem_level_zero T v c c1 c2 c3 γ.1 γ2.1 γd η η2 δ κ κ2 κd hs1 hs2 hδv h1 h2 hrel hloc

end SameDiaZero

end
end

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}

theorem mulLat_one_GL {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    mulLat ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) L = L := by
  unfold mulLat
  simp


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eSame_one (T : Forms0 D u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c1 c3 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (h1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hf : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = g (T.lv0.prk v c ⟨_, hw⟩))
    (g1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η2.1 = 1)
    (g2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c).1 * η2.1 * κ2.1)
    (gl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (gf : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = ((a : (D.mem u).A.Fv v) • g) (T.lv0.prk v c ⟨_, hw⟩)) :
    η2.1⁻¹ * (η.1 * δ.1) ∈ T.cls0.lev.U := by

  have hδ' := Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.isDia_conj T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 hδ κ
  have hcl := T.val0.dil v a k hk c1 _ hδ'
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hcl
  have hκ0 : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γ', hγ', hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx1 : (T.cls0.y c1 * Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.conjPt T.cls0.lev δ κ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' * (T.cls0.y ((D.fm u).dil 0 v a c1)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  generalize hc1' : (D.fm u).dil 0 v a c1 = c1' at hx1
  have hLat1 := diamond_lattice_transport T v k _ hδ' c1 c1' γ' hγ' ⟨κ0.1, hκ0⟩ hx1

  obtain ⟨ε, hε1⟩ : ∃ ε : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), ε.1 = η.1 * δ.1 := ⟨η * δ, rfl⟩
  obtain ⟨κε, hκε⟩ : ∃ κε : T.cls0.lev.U, κε.1 = κ.1 * κ0.1⁻¹ := ⟨⟨_, mul_mem κ.2 (inv_mem hκ0)⟩, rfl⟩
  obtain ⟨γε, hγε⟩ : ∃ γε : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), γε.1 = γ.1 * γ' := ⟨⟨_, mul_mem γ.2 hγ'⟩, rfl⟩
  have hε : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') ε.1 = 1 := by
    intro v' hv'
    rw [hε1, map_mul, h1 v' hv', hδ.1 v' hv', one_mul]
  have h1ε : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γε.1 * (T.cls0.y c1').1 = (T.cls0.y c).1 * ε.1 * κε.1 := by
    have eγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (T.cls0.y c).1 * η.1 * κ.1 * (T.cls0.y c1).1⁻¹ := by rw [← h2]; group
    have hx1' : (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' * (T.cls0.y c1').1 * κ0.1 := hx1
    have eγ' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' = (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) * κ0.1⁻¹ * (T.cls0.y c1').1⁻¹ := by
      rw [hx1']; group
    rw [hγε, hε1, hκε, map_mul, eγ, eγ']
    group
  have hlε : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γε.1.1 (Ld D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    rw [hγε, Units.val_mul]
    exact rlv_chainP _ _ _ hl (by rw [hLat1.2])
  have hfε : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1')) (hw : γε.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1' (T.lv0.pr v c1' w) = ((a : (D.mem u).A.Fv v) • g) (T.lv0.prk v c ⟨_, hw⟩) := by
    intro w hw
    have hw1 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1 ∈ Ld D u 0 (Nat.zero_le _) c1 := by rw [← hLat1.2]; exact ⟨w.1, w.2, rfl⟩
    have eback : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) = w.1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hz2 : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) ∈ Ld D u 0 (Nat.zero_le _) c1' := by rw [eback]; exact w.2
    have ew : γε.1.1 *ᵥ w.1 = γ.1.1 *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) := by
      rw [hγε, Units.val_mul, Matrix.mulVec_mulVec]
    have hw' : γ.1.1 *ᵥ (⟨_, hw1⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      show γ.1.1 *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) ∈ _
      rw [← ew]; exact hw
    have d := Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k _ hδ' c1 c1' γ' ⟨κ0.1, hκ0⟩ hx1 _ hw1 hz2
    rw [pr_congr T v c1' w ⟨_, hz2⟩ eback.symm, d, hf ⟨_, hw1⟩ hw', LinearMap.smul_apply, zsmul_eq_mul, hk,
      smul_eq_mul]
    have ep : T.lv0.prk v c ⟨_, hw'⟩ = T.lv0.prk v c ⟨_, hw⟩ := congrArg (T.lv0.prk v c) (Subtype.ext ew.symm)
    rw [ep]

  have hL1 := mulLat_one_GL (D := D) (clsCrd D u 0 (Nat.zero_le _) c)
  have hLd1 := mulLat_one_GL (D := D) (Ld D u 0 (Nat.zero_le _) c)
  have hxy : ∀ w, ((a : (D.mem u).A.Fv v) • g) w = ((a : (D.mem u).A.Fv v) • g) (dniEquiv T v c c 1 hL1 hLd1 w) := by
    intro w
    obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
    rw [dniEquiv_prk]
    congr 2
    apply Subtype.ext
    show z.1 = ((1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1
    rw [Units.val_one, Matrix.one_mulVec]
  have htriv : (T.cls0.y c).1 * (1 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N 0)) D.host.E) * (T.cls0.y c).1 * (1 : T.cls0.lev.U).1 := by
    simp only [OneMemClass.coe_one, map_one, mul_one, one_mul]
  have hm := dn_match_gen T v 1 (by simp only [OneMemClass.coe_one, map_one]) c c c1' c3 1 (one_mem _) 1 htriv
    hL1 hLd1 ((a : (D.mem u).A.Fv v) • g) ((a : (D.mem u).A.Fv v) • g) hxy γε γ2 ε η2 κε κ2 hε g1 h1ε g2 hlε gl hfε gf
  have efin : η2.1⁻¹ * (η.1 * δ.1) = η2.1⁻¹ * (1 : T.cls0.lev.U).1 * ε.1 := by
    rw [hε1, OneMemClass.coe_one, mul_one]
  rw [efin]
  exact hm


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eSame (T : Forms0 D u) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.EDiaSame0F T := by
  intro v a k hk δ hδ c
  classical
  choose γ1 η1 κ1 hs1 hr1 hl1 hf1 ht1 using fun x : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} => T.down_natural_level_zero v c x.1 x.2
  let σ : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} ≃ {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} :=
    { toFun := fun x => ⟨(a : (D.mem u).A.Fv v) • x.1, smul_ne_zero (Units.ne_zero a) x.2⟩
      invFun := fun x => ⟨((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x.1, smul_ne_zero (Units.ne_zero _) x.2⟩
      left_inv := fun x => Subtype.ext (by
        show ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • ((a : (D.mem u).A.Fv v) • x.1) = x.1
        rw [smul_smul, Units.inv_mul, one_smul])
      right_inv := fun x => Subtype.ext (by
        show (a : (D.mem u).A.Fv v) • (((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x.1) = x.1
        rw [smul_smul, Units.mul_inv, one_smul]) }
  refine ⟨σ, η1, fun x => ⟨γ1 x, κ1 x, hs1 x, hr1 x, fun h => ?_⟩, fun x => ?_⟩
  · funext s
    rw [ht1 x h s _ (is_translate_inverse T (γ1 x) s), Units.val_inv_eq_inv_val]
    rfl
  · exact eSame_one T v a k hk δ hδ c _ _ x.1 (γ1 x) (γ1 (σ x)) (η1 x) (η1 (σ x)) (κ1 x) (κ1 (σ x))
      (hs1 x) (hr1 x) (hl1 x) (hf1 x) (hs1 (σ x)) (hr1 (σ x)) (hl1 (σ x)) (hf1 (σ x))

end SameDiaZero

end

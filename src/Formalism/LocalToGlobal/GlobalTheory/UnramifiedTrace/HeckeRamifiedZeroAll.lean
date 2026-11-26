module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfSameTe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.EqualDiagonalEntriesAll

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiamondSamePlaceMatchings
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.UpSame
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.UpFSame
noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upFSame (T : Forms0 D u) (v : (D.mem u).A.vT) (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ)
    (c c1 c2 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (κd : T.cls0.lev.U)
    (hx : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1)
    (γ γ2 : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ2 : γ2 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}))
    (h5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
        (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩))
    (g5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c3))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c2),
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 x) = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hx⟩))
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3)) :
    ∀ w (hw : w ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) •
          (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈
          Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          k • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • w,
            Submodule.smul_mem _ _ hw⟩) := by
  intro w hw
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨hdd, hfg, hH⟩ := rlv_coordFacts (D := D) (u := u) 0 (Nat.zero_le _)
  have hLat := diamond_lattice_transport T v k δ hδ c c2 γd hγd κd hx
  have memInv : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c,
      ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈
        Ld D u 0 (Nat.zero_le _) c2 := by
    intro y hy
    rw [← hLat.2, mem_mul_lattice_iff] at hy
    exact hy
  have hΓU : (γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) ∈
      UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (mul_mem (inv_mem hγ2) (inv_mem hγd)) hγ
  have hne1 : (1 : 𝓞 D.host.E) ∉ T.atT.Pv v := (T.atT.Pv v).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)

  have hQd := local_dual_Q_eq_of_P T.atT v c3 c1 _ hΓU hP
  obtain ⟨a1, ha1P, ha1Q, ha1⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPd.le hQd.le
    (x := ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)
    ⟨w, hw, rfl⟩

  have hPw : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w ∈
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) :=
    (rlv_mem_locP _ _ _).2 ⟨1, hne1, by rw [one_smul]; exact ⟨w, hw, rfl⟩⟩
  rw [h4, rlv_mem_locP] at hPw
  obtain ⟨s, hs, hsw⟩ := hPw
  have hs' : s • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈
      Ld D u 0 (Nat.zero_le _) c := by
    rw [smul_comm]; exact natSmul_mem_of_sup _ _ hT0 z hz _ hsw
  have e1 : Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) (Ld D u 0 (Nat.zero_le _) c1) =
      clsCrd D u 0 (Nat.zero_le _) c1 := hdd c1
  have hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) ≤
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    have hg1 : cT (sigD D : D.host.E →+* D.host.E) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        gramN D 0 (Nat.zero_le _) * (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = gramN D 0 (Nat.zero_le _) := hγ
    refine rlv_dualQ (sigD D) rlv_sig_sig (gramN D 0 (Nat.zero_le _)) hH _ hg1 (T.atT.Pv v) (hfg c) (hdd c).le ?_
    rw [e1]; exact h3.ge
  have hne1Q : (1 : 𝓞 D.host.E) ∉ rlvQ T.atT v := (rlvQ T.atT v).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have hQw := hQ ((rlv_mem_locP _ _ _).2 ⟨1, hne1Q, by rw [one_smul]; exact ⟨w, hw, rfl⟩⟩)
  obtain ⟨t, ht, htw⟩ := (rlv_mem_locP _ _ _).1 hQw
  have ht' : t • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈
      Ld D u 0 (Nat.zero_le _) c := by
    rw [smul_comm]; exact Submodule.smul_mem _ _ (cls_le_ld T c htw)
  obtain ⟨a2, ha2P, ha2Q, ha2⟩ := avoid_two _ _ _ _ s t hs ht hs' ht'

  have haP : a1 * a2 ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha1P ha2P
  have haQ : a1 * a2 ∉ rlvQ T.atT v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha1Q ha2Q
  obtain ⟨r, hr, b, hb⟩ := rlv_norm T.atT v (a1 * a2) haP haQ
  have m1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
      (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈
      Ld D u 0 (Nat.zero_le _) c3 := by
    rw [hb, show b * (a1 * a2) = (b * a2) * a1 by ring, mul_smul]
    exact Submodule.smul_mem _ _ ha1
  have m2 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
      ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈ Ld D u 0 (Nat.zero_le _) c := by
    rw [hb, show b * (a1 * a2) = (b * a1) * a2 by ring, mul_smul]
    exact Submodule.smul_mem _ _ ha2
  refine ⟨r, hr, m1, ?_⟩
  have eV1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w)) =
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) := by
    rw [Matrix.mulVec_smul, smul_comm]
  have hB : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w)) ∈ Ld D u 0 (Nat.zero_le _) c := by
    rw [eV1]; exact m2
  have eV2 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) =
      ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
          ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) := by
    have eg : (γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) =
        ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
          ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [Matrix.mulVec_smul, eg, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]
  have hA : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) ∈
      Ld D u 0 (Nat.zero_le _) c2 := by
    rw [eV2]; exact memInv _ m2
  calc (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, m1⟩)
      = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hA⟩) := g5 ⟨_, m1⟩ hA
    _ = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, memInv _ m2⟩) := congrArg _ (pr_congr T v c2 ⟨_, hA⟩ ⟨_, memInv _ m2⟩ eV2)
    _ = k • (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, m2⟩) :=
        Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k δ hδ c c2 γd κd hx _ m2 (memInv _ m2)
    _ = k • (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hB⟩) := by
        rw [pr_congr T v c ⟨_, m2⟩ ⟨_, hB⟩ eV1.symm]
    _ = _ := congrArg (fun t => k • t) (h5 ⟨_, Submodule.smul_mem _ _ hw⟩ hB).symm

end SameDiaZero

end
end

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upSame_one (T : Forms0 D u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c2 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κd : T.cls0.lev.U)
    (hx : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (c1 c3 : (D.mem u).C.cls 0) (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (m : 𝓞 D.host.E) (hmP : m ∉ T.atT.Pv v)
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (h1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}))
    (h5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩))
    (g1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η2.1 = 1)
    (g2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c2).1 * η2.1 * κ2.1)
    (g3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (clsCrd D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2))
    (g4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))}))
    (g5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ2.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 x) = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hx⟩)) :
    η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) ∈ T.cls0.lev.U := by

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
  have hLat := diamond_lattice_transport T v k δ hδ c c2 γd hγd κd hx
  have hInv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c2 := by
    rw [← hLat.2, rlv_mulLat_inv]

  have hκdP := ((T.cls0.lev.U_eq _).1 κd.2).1
  obtain ⟨ε, hε1⟩ : ∃ ε : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), ε.1 = κd.1 * δ.1⁻¹ * η.1 * δ.1 * κd.1⁻¹ :=
    ⟨⟨_, mul_mem (mul_mem (mul_mem (mul_mem hκdP (inv_mem δ.2)) η.2) δ.2) (inv_mem hκdP)⟩, rfl⟩
  obtain ⟨κε, hκε⟩ : ∃ κε : T.cls0.lev.U, κε.1 = κd.1 * κ.1 * κ0.1⁻¹ :=
    ⟨⟨_, mul_mem (mul_mem κd.2 κ.2) (inv_mem hκ0)⟩, rfl⟩
  have hγε : (γd⁻¹ * γ.1 * γ' : GL (Fin (D.R.N 0)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := mul_mem (mul_mem (inv_mem hγd) γ.2) hγ'
  have hε : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') ε.1 = 1 := by
    intro v' hv'
    rw [hε1]
    simp only [map_mul, map_inv, h1 v' hv', hδ.1 v' hv', inv_one, mul_one, one_mul, mul_inv_cancel]
  have h1ε : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γd⁻¹ * γ.1 * γ') * (T.cls0.y c1').1 = (T.cls0.y c2).1 * ε.1 * κε.1 := by
    have eγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (T.cls0.y c).1 * η.1 * κ.1 * (T.cls0.y c1).1⁻¹ := by rw [← h2]; group
    have hx' : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1 := hx
    have eγd : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd = (T.cls0.y c).1 * δ.1 * κd.1⁻¹ * (T.cls0.y c2).1⁻¹ := by rw [hx']; group
    have hx1' : (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' * (T.cls0.y c1').1 * κ0.1 := hx1
    have eγ' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' = (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) * κ0.1⁻¹ * (T.cls0.y c1').1⁻¹ := by
      rw [hx1']; group
    rw [hε1, hκε, map_mul, map_mul, map_inv, eγ, eγd, eγ']
    group
  have htriv : (T.cls0.y c2).1 * (1 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N 0)) D.host.E) * (T.cls0.y c2).1 * (1 : T.cls0.lev.U).1 := by
    simp only [OneMemClass.coe_one, map_one, mul_one, one_mul]

  have s1 := use₄ (T.atT.Pv v) γ2.1 g3
  have s2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2) := by rw [hInv]
  have hP0 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [Units.val_mul, Units.val_mul]
    exact rlv_chainP (T.atT.Pv v) _ _ (rlv_chainP (T.atT.Pv v) _ _ s1 s2) h3
  have t1 := use₄ (T.atT.Pv v) γ2.1 g4
  have eG : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) =
      Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)} := by
    rw [show mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) =
        mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) ⊔
          mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) from
        Submodule.map_sup _ _ _, hInv]
    congr 1
    unfold mulLat
    rw [Submodule.map_span, Set.image_singleton]
    congr 2
    show ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z) = (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)
    rw [Matrix.mulVec_smul]
  have sc : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))}) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)}) := by
    rw [smul_comm_OE]
    exact localization_LshKer_eq_localization_sup _ _ _ m hmP
  have s2' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z})) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))}) := by
    rw [eG, sc]
  have hPd0 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [Units.val_mul, Units.val_mul]
    exact rlv_chainP (T.atT.Pv v) _ _ (rlv_chainP (T.atT.Pv v) _ _ t1 s2') h4
  have eΓ : ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      ((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) := by
    simp only [inv_one, mul_one, Units.val_mul, mul_assoc]
  have s3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by rw [hLat1.1]
  have s3' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c1) := by rw [hLat1.2]
  have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ]; exact rlv_chainP (T.atT.Pv v) _ _ hP0 s3
  have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ]; exact rlv_chainP (T.atT.Pv v) _ _ hPd0 s3'

  have hF : ∀ w (hw : w ∈ Ld D u 0 (Nat.zero_le _) c1'), ∃ r : 𝓞 D.host.F, r ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈ Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1' (T.lv0.pr v c1' ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w, Submodule.smul_mem _ _ hw⟩) := by
    intro w hw
    have hw1 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w ∈ Ld D u 0 (Nat.zero_le _) c1 := by rw [← hLat1.2]; exact ⟨w, hw, rfl⟩
    obtain ⟨r, hr, hmem, hf⟩ := upFSame T v k δ hδ c c1 c2 c3 γd hγd κd hx γ.1 γ2.1 γ.2 γ2.2 z hz h3 h4 h5 g5
      hP0 hPd0 _ hw1
    have eΓw : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) =
        (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, eΓ]
    have h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
      rw [eΓw]; exact hmem
    refine ⟨r, hr, h, ?_⟩
    have hz1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hw1
    have eback : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) = (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hz2 : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈ Ld D u 0 (Nat.zero_le _) c1' := by
      rw [eback]; exact Submodule.smul_mem _ _ hw
    have d := Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k _ hδ' c1 c1' γ' ⟨κ0.1, hκ0⟩ hx1 _ hz1 hz2
    rw [pr_congr T v c3 ⟨_, h⟩ ⟨_, hmem⟩ eΓw, hf, ← d,
      pr_congr T v c1' ⟨_, hz2⟩ ⟨_, Submodule.smul_mem _ _ hw⟩ eback]

  have hΓ : (γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (mul_mem (inv_mem γ2.2) (inv_mem (one_mem _))) hγε
  have hU := matching_unitary_eq T.cls0 c2 c1' c2 c3 _ γ2.1 1 ε η2 1 κε κ2 1 h1ε g2 htriv
  have hloc := local_unitary_of_matching_zero T v c3 c1' _ hΓ hU hP hPd hF
  have hmm := matching_move_mem_level_zero T v c2 c1' c2 c3 _ γ2.1 1 ε η2 1 κε κ2 1 hε g1
    (by simp only [OneMemClass.coe_one, map_one]) h1ε g2 htriv hloc
  have efin : η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) = η2.1⁻¹ * (1 : T.cls0.lev.U).1 * ε.1 * κd.1 := by
    rw [hε1, OneMemClass.coe_one]
    group
  rw [efin]
  exact mul_mem hmm κd.2


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upSame (T : Forms0 D u) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.UpDiaSame0F T := by
  intro v a k hk δ hδ c γd hγd κd hx
  set c2 := (D.fm u).dil 0 v a c with hc2
  have hLat := diamond_lattice_transport T v k δ hδ c c2 γd hγd κd hx
  have hInv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c2 := by
    rw [← hLat.2, rlv_mulLat_inv]
  have memInv : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c, ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈ Ld D u 0 (Nat.zero_le _) c2 := by
    intro y hy
    rw [← hLat.2, mem_mul_lattice_iff] at hy
    exact hy
  have memFwd : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c2, (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈ Ld D u 0 (Nat.zero_le _) c := by
    intro y hy
    rw [← hLat.2]
    exact ⟨y, hy, rfl⟩
  have eInvFwd : ∀ y : Fin (D.R.N 0) → D.host.E, ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have eFwdInv : ∀ y : Fin (D.R.N 0) → D.host.E, (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

  obtain ⟨m, hm⟩ := T.atT.res_surj v ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)
  have hmP : m ∉ T.atT.Pv v := by
    intro h
    rw [AtTTied.Pv, RingHom.mem_ker, hm] at h
    exact Units.ne_zero _ h
  have hkm : T.atT.res v (k : 𝓞 D.host.E) * T.atT.res v m = 1 := by
    rw [map_intCast, hk, hm, Units.mul_inv]
  have hmk : T.atT.res v m * T.atT.res v (k : 𝓞 D.host.E) = 1 := by
    rw [mul_comm]; exact hkm
  have hDFz : ∀ y : ↥(Ld D u 0 (Nat.zero_le _) c), (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y.1, memInv _ y.2⟩) =
      k • (D.fm u).fv 0 v c (T.lv0.pr v c y) :=
    fun y => Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k δ hδ c c2 γd κd hx y.1 y.2 (memInv _ y.2)

  choose zf hzf using fun x : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} => T.lv0.pr_surj v c x.1
  have hz1 : ∀ x, (D.fm u).fv 0 v c (T.lv0.pr v c (zf x)) = 1 := fun x => by rw [hzf x]; exact x.2
  choose γ η κ h1 h2 h3 h4 h5 h6 using fun x => T.up_natural_level_zero v c (zf x) (hz1 x)

  let z2 : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} → ↥(Ld D u 0 (Nat.zero_le _) c2) :=
    fun x => m • (⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1, memInv _ (zf x).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c2))
  have hz2 : ∀ x, (D.fm u).fv 0 v c2 (T.lv0.pr v c2 (z2 x)) = 1 := by
    intro x
    show (D.fm u).fv 0 v c2 (T.lv0.pr v c2 (m • (⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1, memInv _ (zf x).2⟩ :
      ↥(Ld D u 0 (Nat.zero_le _) c2)))) = 1
    rw [T.lv0.pr_smul, map_smul, hDFz (zf x), hz1 x, smul_eq_mul, zsmul_eq_mul, mul_one, hk, hm, Units.inv_mul]
  choose γ2 η2 κ2 g1 g2 g3 g4 g5 g6 using fun x => T.up_natural_level_zero v c2 (z2 x) (hz2 x)

  choose zl hzl using fun y : {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} => T.lv0.pr_surj v c2 y.1
  let w1 : {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} → ↥(Ld D u 0 (Nat.zero_le _) c) :=
    fun y => (k : 𝓞 D.host.E) • (⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))
  have hinvf : ∀ y, (D.fm u).fv 0 v c (T.lv0.pr v c (w1 y)) = 1 := by
    intro y
    have e := hDFz ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩
    rw [pr_congr T v c2 ⟨_, memInv _ (memFwd _ (zl y).2)⟩ (zl y) (eInvFwd _), hzl y, y.2] at e
    show (D.fm u).fv 0 v c (T.lv0.pr v c ((k : 𝓞 D.host.E) •
      (⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)))) = 1
    rw [T.lv0.pr_smul, map_smul, smul_eq_mul, map_intCast, ← zsmul_eq_mul]
    exact e.symm
  let σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
      {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} :=
    { toFun := fun x => ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩
      invFun := fun y => ⟨T.lv0.pr v c (w1 y), hinvf y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hm1 : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (z2 x).1 ∈ Ld D u 0 (Nat.zero_le _) c := memFwd _ (z2 x).2
        have e1 := pr_tr T v c2 c (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) hLat.2 (zl ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩) (z2 x) (hzl _)
          (memFwd _ (zl _).2) hm1
        have e2 : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (z2 x).1 = (m • zf x).1 := by
          show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1)) = m • (zf x).1
          rw [Matrix.mulVec_smul, eFwdInv]
        show T.lv0.pr v c ((k : 𝓞 D.host.E) • (⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩).1,
          memFwd _ (zl _).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))) = x.1
        rw [T.lv0.pr_smul, e1, pr_congr T v c ⟨_, hm1⟩ (m • zf x) e2, T.lv0.pr_smul, hzf x, smul_smul, hkm,
          one_smul]
      right_inv := by
        intro y
        apply Subtype.ext
        have hm1 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (w1 y).1 ∈ Ld D u 0 (Nat.zero_le _) c2 := memInv _ (w1 y).2
        have e1 := pr_tr T v c c2 ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) hInv (zf ⟨T.lv0.pr v c (w1 y), hinvf y⟩) (w1 y) (hzf _)
          (memInv _ (zf _).2) hm1
        have e2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (w1 y).1 = ((k : 𝓞 D.host.E) • zl y).1 := by
          show ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((k : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1)) = (k : 𝓞 D.host.E) • (zl y).1
          rw [Matrix.mulVec_smul, eInvFwd]
        show T.lv0.pr v c2 (m • (⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf ⟨T.lv0.pr v c (w1 y), hinvf y⟩).1,
          memInv _ (zf _).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c2))) = y.1
        rw [T.lv0.pr_smul, e1, pr_congr T v c2 ⟨_, hm1⟩ ((k : 𝓞 D.host.E) • zl y) e2, T.lv0.pr_smul, hzl y,
          smul_smul, hmk, one_smul] }
  refine ⟨σ, η, fun y => η2 (σ.symm y), ?_, ?_, ?_⟩
  · intro x
    have hmv : IsUpMvF T v c (T.lv0.pr v c (zf x)) (η x) :=
      ⟨γ x, κ x, h1 x, h2 x, fun h => by
        funext s
        rw [h6 x h s _ (is_translate_inverse T (γ x) s), Units.val_inv_eq_inv_val]
        rfl⟩
    rw [hzf x] at hmv
    exact hmv
  · intro y
    have hmv : IsUpMvF T v c2 (T.lv0.pr v c2 (z2 (σ.symm y))) (η2 (σ.symm y)) :=
      ⟨γ2 _, κ2 _, g1 _, g2 _, fun h => by
        funext s
        rw [g6 _ h s _ (is_translate_inverse T (γ2 _) s), Units.val_inv_eq_inv_val]
        rfl⟩
    have e : T.lv0.pr v c2 (z2 (σ.symm y)) = y.1 := congrArg Subtype.val (σ.apply_symm_apply y)
    rw [e] at hmv
    exact hmv
  · intro x
    show (η2 (σ.symm (σ x))).1⁻¹ * κd.1 * (δ.1⁻¹ * (η x).1 * δ.1) ∈ T.cls0.lev.U
    rw [σ.symm_apply_apply]
    exact upSame_one T v a k hk δ hδ c c2 γd hγd κd hx _ _ (zf x).1 (zf x).2 m hmP (γ x) (γ2 x) (η x) (η2 x)
      (κ x) (κ2 x) (h1 x) (h2 x) (h3 x) (h4 x) (h5 x) (g1 x) (g2 x) (g3 x) (g4 x) (g5 x)

end SameDiaZero

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.DnDiaSame0FHolds
noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal CrossDiaZero
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}

theorem inv_mulVec_self {E : Type} [Field E] {n : ℕ} (g : GL (Fin n) E) (z : Fin n → E) :
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem dnk_latP_smul (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (μ : (D.mem u).A.Fv v) (hμ : μ ≠ 0)
    (γ γ' : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun' : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = μ • g (T.lv0.prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by
  have hfun2 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = (μ • g) (T.lv0.prk v c ⟨_, hx⟩) := fun x hx =>
    (hfun' x hx).trans (LinearMap.smul_apply μ g _).symm
  have eq1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) := by
    ext y
    rw [dnk_char T v c c2 (μ • g) γ' hl' hfun2 y, dnk_char T v c c1 g γ hl hfun y]
    simp only [LinearMap.smul_apply, smul_eq_zero, hμ, false_or]
  have L1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c1) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) :=
    le_antisymm (dnk_lk_locP T v c1) (localization_mono₂ _ le_sup_left)
  have L2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c2) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2) :=
    le_antisymm (dnk_lk_locP T v c2) (localization_mono₂ _ le_sup_left)
  have M1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L1.le) (rlv_locP_mulLat_le _ _ L1.ge)
  have M2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L2.le) (rlv_locP_mulLat_le _ _ L2.ge)
  rw [M1, M2] at eq1
  exact localization_smul_cancel _ γ γ' eq1


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dn_same_loc (T : Forms0 D u) (v : (D.mem u).A.vT) (k : ℤ) (hμ : ((k : ℤ) : (D.mem u).A.Fv v) ≠ 0)
    (c c2 c1 c3 c1' : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hLc : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c)
    (hLd : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c)
    (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (x2 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c2))
    (hxy : ∀ w, x2 w = ((k : ℤ) : (D.mem u).A.Fv v) • x (dniEquiv T v c2 c γd hLc hLd w))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hl2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2))
    (hf1 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = x (T.lv0.prk v c ⟨_, hw⟩))
    (hf2 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x2 (T.lv0.prk v c2 ⟨_, hw⟩))
    (γe : GL (Fin (D.R.N 0)) D.host.E) (hγe : γe ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hLc1 : mulLat (γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1') = clsCrd D u 0 (Nat.zero_le _) c1)
    (hLd1 : mulLat (γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1') = Ld D u 0 (Nat.zero_le _) c1)
    (hdf : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1)
      (hz2 : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈ Ld D u 0 (Nat.zero_le _) c1'),
      (D.fm u).fv 0 v c1' (T.lv0.pr v c1' ⟨_, hz2⟩) = k • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨z, hz⟩))
    (hU : (T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe)) * (T.cls0.y c1').1 ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    bc (prV (E := D.host.E) (T.atT.eV v).1) ((T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe)) *
      (T.cls0.y c1').1) ∈ T.cls0.lev.Uloc (T.atT.eV v).1 := by
  classical
  set g' : GL (Fin (D.R.N 0)) D.host.E := γd * γ2.1 with hg'
  have hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    rw [hg', Units.val_mul]
    exact rlv_chainP _ _ _ (by rw [hLc]) hl2
  have hLkinv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c2 :=
    dni_inv_eq γd (dni_lk T v c2 c _ hLc hLd)
  have hf' : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = ((k : ℤ) : (D.mem u).A.Fv v) • x (T.lv0.prk v c ⟨_, hw⟩) := by
    intro w hw
    have e1 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) = γ2.1.1 *ᵥ w.1 := by
      rw [hg', Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hw2 : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := by
      rw [← e1]; exact dni_mem_of _ hLkinv hw
    rw [hf2 w hw2, hxy, dniEquiv_prk]
    refine congrArg (fun t => ((k : ℤ) : (D.mem u).A.Fv v) • x (T.lv0.prk v c t)) (Subtype.ext ?_)
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (γ2.1.1 *ᵥ w.1) = (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1
    rw [hg', Units.val_mul, Matrix.mulVec_mulVec]
  have hPc := dnk_latP_smul T v c c1 c3 x ((k : ℤ) : (D.mem u).A.Fv v) hμ γ.1 g' hl1 hf1 hl' hf'
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
  have hQd : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (Ld D u 0 (Nat.zero_le _) c3) :=
    local_dual_Q_eq_of_P T.atT v c3 c1 Γ hΓU hPΓ
  have eΓ : ∀ z, (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) = γ.1.1 *ᵥ z := by
    intro z
    have e4 : g' * Γ = γ.1 := by rw [hg', hΓdef]; group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e4]
  have hFc : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ r : 𝓞 D.host.F, r ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          ((k : ℤ) : (D.mem u).A.Fv v) • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • z, Submodule.smul_mem _ _ hz⟩) := by
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
    set R := (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) with hR
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
        T.atT.res v s • (((k : ℤ) : (D.mem u).A.Fv v) • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨R • z, hRz⟩)) := by
      rw [smul_comm (T.atT.res v s) ((k : ℤ) : (D.mem u).A.Fv v), hB]
      refine hA.trans ?_
      refine congrArg (fun t => ((k : ℤ) : (D.mem u).A.Fv v) • x (T.lv0.prk v c t)) (Subtype.ext ?_)
      show (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 = γ.1.1 *ᵥ w1.1
      rw [hw3def, hw1def, e4, e5]
    exact smul_right_injective _ hres key
  have eΓ2 : γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) = Γ * γe := by rw [hΓdef]; group
  have hΓ2 : γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by rw [eΓ2]; exact mul_mem hΓU hγe
  have hP2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1')) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ2, Units.val_mul, rlv_mulLat_mul, hLc1]; exact hPΓ
  have hPd2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1')) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ2, Units.val_mul, rlv_mulLat_mul, hLd1]; exact hPdΓ
  refine local_unitary_of_matching_zero T v c3 c1' _ hΓ2 hU hP2 hPd2 ?_
  intro z hz
  have hz1 : (γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈ Ld D u 0 (Nat.zero_le _) c1 := dni_mem_of _ hLd1 hz
  obtain ⟨r, hr, hmem, hval⟩ := hFc _ hz1
  have eΓz : ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z = (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) := by
    rw [eΓ2, Units.val_mul, Matrix.mulVec_mulVec]
  have hmem2 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
    rw [eΓz]; exact hmem
  refine ⟨r, hr, hmem2, ?_⟩
  have hRz1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz1
  have eback : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) = (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • z := by
    rw [Matrix.mulVec_smul, inv_mulVec_self]
  have hz2 : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) ∈ Ld D u 0 (Nat.zero_le _) c1' := by
    rw [eback]; exact Submodule.smul_mem _ _ hz
  have hd := hdf _ hRz1 hz2
  rw [← Int.cast_smul_eq_zsmul ((D.mem u).A.Fv v)] at hd
  rw [pr_congr T v c3 ⟨_, hmem2⟩ ⟨_, hmem⟩ (congrArg (fun t => (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • t) eΓz), hval, pr_congr T v c1' ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • z, Submodule.smul_mem _ _ hz⟩ ⟨_, hz2⟩ eback.symm, hd]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dn_same_one (T : Forms0 D u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c2 c1 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κd : T.cls0.lev.U)
    (hrel : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (hLc : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c)
    (hLd : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c)
    (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (x2 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c2))
    (hxy : ∀ w, x2 w = ((k : ℤ) : (D.mem u).A.Fv v) • x (dniEquiv T v c2 c γd hLc hLd w))
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
    η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) ∈ T.cls0.lev.U := by
  classical
  have hμ : ((k : ℤ) : (D.mem u).A.Fv v) ≠ 0 := by rw [hk]; exact a.ne_zero

  have hδ' := isDia_conj T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 hδ κ
  have hcl := T.val0.dil v a k hk c1 _ hδ'
  obtain ⟨c1', hc1'⟩ : ∃ c1', (D.fm u).dil 0 v a c1 = c1' := ⟨_, rfl⟩
  rw [hc1'] at hcl
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hcl
  have hκ0 : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γe, hγe, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx1 : (T.cls0.y c1 * conjPt T.cls0.lev δ κ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γe * (T.cls0.y c1').1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨hLc1, hLd1⟩ := diamond_lattice_transport T v k _ hδ' c1 c1' γe hγe ⟨κ0.1, hκ0⟩ hx1
  have hdf : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1)
      (hz2 : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈ Ld D u 0 (Nat.zero_le _) c1'),
      (D.fm u).fv 0 v c1' (T.lv0.pr v c1' ⟨_, hz2⟩) = k • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨z, hz⟩) :=
    fun z hz hz2 => diaFun_same T v k _ hδ' c1 c1' γe ⟨κ0.1, hκ0⟩ hx1 z hz hz2

  have hκdU : κd.1 ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((T.cls0.lev.U_eq _).1 κd.2).1
  obtain ⟨η', hη'⟩ : ∃ η' : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), η'.1 = κd.1 * (δ.1⁻¹ * η.1 * δ.1) * κd.1⁻¹ :=
    ⟨⟨_, mul_mem (mul_mem hκdU (mul_mem (mul_mem (inv_mem δ.2) η.2) δ.2)) (inv_mem hκdU)⟩, rfl⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : T.cls0.lev.U, κ'.1 = κd.1 * κ.1 * κ0.1⁻¹ :=
    ⟨κd * κ * (⟨κ0.1, hκ0⟩ : T.cls0.lev.U)⁻¹, rfl⟩
  have hs' : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η'.1 = 1 := by
    intro w hw
    rw [hη']
    simp only [map_mul, map_inv, hs1 w hw, hδ.1 w hw, inv_one, mul_one, mul_inv_cancel]
  have ey2 : (T.cls0.y c2).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd)⁻¹ * ((T.cls0.y c).1 * δ.1) * κd.1⁻¹ := by
    rw [hrel]; group
  have ey1 : (T.cls0.y c1').1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γe)⁻¹ * ((T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1)) * κ0.1⁻¹ := by
    have h := hx1
    simp only [Subgroup.coe_mul, conjPt_coe] at h
    rw [h]; group
  have ey : (T.cls0.y c).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 * κ.1⁻¹ * η.1⁻¹ := by
    rw [h1]; group
  have h1' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γd⁻¹ * γ.1 * γe) * (T.cls0.y c1').1 = (T.cls0.y c2).1 * η'.1 * κ'.1 := by
    rw [hη', hκ', ey1, ey2, ey]
    simp only [map_mul, map_inv]
    group
  have h3 : (T.cls0.y c2).1 * (1 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N 0)) D.host.E) * (T.cls0.y c2).1 * (1 : T.cls0.lev.U).1 := by
    simp only [OneMemClass.coe_one, map_one, one_mul, mul_one]
  have hU := matching_unitary_eq T.cls0 c2 c1' c2 c3 (γd⁻¹ * γ.1 * γe) γ2.1 1 η' η2 1 κ' κ2 1 h1' h2 h3
  have hloc := dn_same_loc T v k hμ c c2 c1 c3 c1' γd hγd hLc hLd x x2 hxy γ γ2 hl1 hl2 hf1 hf2 γe hγe hLc1 hLd1 hdf hU
  have hm := matching_move_mem_level_zero T v c2 c1' c2 c3 (γd⁻¹ * γ.1 * γe) γ2.1 1 η' η2 1 κ' κ2 1 hs' hs2
    (by simp only [OneMemClass.coe_one, map_one]) h1' h2 h3 hloc
  have e2 : η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) = (η2.1⁻¹ * (1 : T.cls0.lev.U).1 * η'.1) * κd.1 := by
    rw [hη', OneMemClass.coe_one]; group
  rw [e2]
  exact mul_mem hm κd.2


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dnDiaSame0F_holds (T : Forms0 D u) : DnDiaSame0F T := by
  intro v a k hk δ hδ c γd hγd κd hrel
  obtain ⟨hLc, hLd⟩ := diamond_lattice_transport T v k δ hδ c ((D.fm u).dil 0 v a c) γd hγd κd hrel

  obtain ⟨z, hz⟩ := dni_exists_one T v ((D.fm u).dil 0 v a c)
  have hw : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) c := dni_mem_of _ hLd z.2
  have hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a c) := by
    rw [inv_mulVec_self]; exact z.2
  have hdf := diaFun_same T v k δ hδ c _ γd κd hrel _ hw hz2
  rw [pr_congr T v _ ⟨_, hz2⟩ z (inv_mulVec_self γd z.1), hz] at hdf
  set φ : (D.fm u).lk 0 v ((D.fm u).dil 0 v a c) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c :=
    (dniEquiv T v ((D.fm u).dil 0 v a c) c γd hLc hLd).trans (LinearEquiv.smulOfUnit a) with hφdef
  have hφ : ∀ w, φ w = ((k : ℤ) : (D.mem u).A.Fv v) • dniEquiv T v ((D.fm u).dil 0 v a c) c γd hLc hLd w := by
    intro w; rw [hk]; rfl
  have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk T.atT 0 (Nat.zero_le _) v ((D.fm u).dil 0 v a c) :=
    Submodule.mem_sup_left (dnk_tld T _ z.1 z.2)
  have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (dnk_tld T c _ hw)
  have hkw : (D.fm u).fv 0 v c (T.lv0.pr v c (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)))) = 1 := by
    rw [map_zsmul, map_zsmul]; exact hdf.symm
  have hTkw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))).1 ∈
      Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (dnk_tld T c _ (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))).2)
  have hte : φ ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = (D.fm u).te 0 v c := by
    rw [← T.lv0.te v _ z hz h1, ← T.lv0.te v c _ hkw hTkw, hφ, dniEquiv_prk]
    have e : (⟨(((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))).1, hTkw⟩ :
        ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = k • (⟨_, hTw⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) := by
      apply Subtype.ext
      show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (k • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1)) =
        k • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1))
      exact smul_comm _ _ _
    rw [e, map_zsmul, ← Int.cast_smul_eq_zsmul ((D.mem u).A.Fv v)]
    refine congrArg (fun t => ((k : ℤ) : (D.mem u).A.Fv v) • T.lv0.prk v c t) (Subtype.ext ?_)
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1)
    exact Matrix.mulVec_smul _ _ _
  have hne0 : ∀ {c0 : (D.mem u).C.cls 0} (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c0)),
      x ((D.fm u).te 0 v c0) = 1 → x ≠ 0 := by
    intro c0 x hx h0
    rw [h0, LinearMap.zero_apply] at hx
    exact zero_ne_one hx
  choose γ1 η1 κ1 hs1 hr1 hl1 hf1 ht1 using fun x : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) //
    x ((D.fm u).te 0 v c) = 1} => T.down_natural_level_zero v c x.1 (hne0 x.1 x.2)
  choose γ2 η2 κ2 hs2 hr2 hl2 hf2 ht2 using fun x : {x : Module.Dual ((D.mem u).A.Fv v)
    ((D.fm u).lk 0 v ((D.fm u).dil 0 v a c)) // x ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = 1} =>
    T.down_natural_level_zero v ((D.fm u).dil 0 v a c) x.1 (hne0 x.1 x.2)
  refine ⟨dualSigma φ _ _ hte, η1, η2,
    fun x => ⟨γ1 x, κ1 x, hs1 x, hr1 x, fun h => ?_⟩, fun x => ⟨γ2 x, κ2 x, hs2 x, hr2 x, fun h => ?_⟩, fun x => ?_⟩
  · funext s
    rw [ht1 x h s _ (is_translate_inverse T (γ1 x) s), Units.val_inv_eq_inv_val]
    rfl
  · funext s
    rw [ht2 x h s _ (is_translate_inverse T (γ2 x) s), Units.val_inv_eq_inv_val]
    rfl
  · exact dn_same_one T v a k hk δ hδ c _ _ _ γd hγd κd hrel hLc hLd x.1 _
      (fun w => by rw [dualSigma_apply, hφ, map_smul]) (γ1 x) (γ2 _) (η1 x) (η2 _) (κ1 x) (κ2 _) (hs1 x) (hs2 _)
      (hr1 x) (hr2 _) (hl1 x) (hl2 _) (hf1 x) (hf2 _)

end SameDiaZero

end
end

namespace SameDiaZero

theorem diamond_same_place_matchings : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.SameAll := by
  intro D u T
  refine ⟨?_, ?_, ?_⟩
  · apply upSame <;> assumption
  · apply dnDiaSame0F_holds <;> assumption
  · first
      | (apply eSame <;> assumption)
      | (apply e_main <;> assumption)
      | (apply eDiaSame0F <;> assumption)

end SameDiaZero
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.MulLatticeOne
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

theorem mul_lattice_one {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Matrix.one_mulVec] using hy
  · intro hx
    exact ⟨x, hx, by simp [Matrix.one_mulVec]⟩

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
theorem pt_agree1 (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (w1 : Fin (D.R.N 0) → D.host.E) (s1 : 𝓞 D.host.E)
    (hz1 : s1 • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) (hs1 : s1 ∉ T.atT.Pv v) (y : (D.fm u).lk 0 v c)
    (hy1 : T.lv0.prk v c ⟨_, hz1⟩ = T.atT.res v s1 • y)
    (g1 g3 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (h1 : g1 y = 1) (h3 : g3 y = 1) :
    ∀ l ∈ clsCrd D u 0 (Nat.zero_le _) c, ∀ (e : 𝓞 D.host.E)
      (hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      g1 (T.lv0.prk v c ⟨_, hY⟩) = g3 (T.lv0.prk v c ⟨_, hY⟩) := by
  intro l hl e hY
  have hl' : s1 • l ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left (Submodule.smul_mem _ _ hl)
  have hTl : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (s1 • l) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.smul_mem _ _ hl'
  have hTl0 : T.lv0.prk v c ⟨_, hTl⟩ = 0 :=
    (T.lv0.prk_ker v c _).2 (Submodule.smul_mem_smul (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v)) hl')
  have e0 : s1 • (⟨_, hY⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) =
      (⟨_, hTl⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) + e • (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) := by
    apply Subtype.ext
    show s1 • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (s1 • l) + e • (s1 • w1)
    rw [smul_add, smul_comm s1 (((D.mem u).A.T : ℕ) : 𝓞 D.host.E), smul_comm s1 e]
  have hp : T.lv0.prk v c ⟨_, hY⟩ = T.atT.res v e • y := by
    have h := congrArg (T.lv0.prk v c) e0
    rw [T.lv0.prk_smul, map_add (f := _), T.lv0.prk_smul, hTl0, zero_add, hy1, smul_comm] at h
    exact smul_right_injective _ (res_ne T hs1) h
  rw [hp, map_smul, map_smul, h1, h3]


set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem valSame_pt (T : Forms0 D u) : ValSame T := by
  intro v c G hG g η κ μ g' η' κ' μ' y hP hP'
  obtain ⟨_, γ, hD, z, γ1, κ1, hz1, hU, hpt⟩ := hP
  obtain ⟨_, γ', hD', z', γ1', κ1', hz1', hU', hpt'⟩ := hP'
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  obtain ⟨u1', u2', u3', u4', u5', -⟩ := hU'
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ1 μ κ1 u1 u2 u3 u4 u5
  have H3 := comp_of_moves T v c g' γ' η' κ' hD'.1 hD'.2.1 hD'.2.2.1 hD'.2.2.2.1 z' γ1' μ' κ1' u1' u2' u3' u4' u5'
  have hg1 := (ptz_val T hD z _ hpt).trans hz1
  have hg3 := (ptz_val T hD' z' _ hpt').trans hz1'
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  obtain ⟨s3, hs3, hw3, hy3⟩ := hpt'
  have hlat := le_antisymm (ptLat_holds T v c _ _ s1 s3 hw1 hw3 hs1 hs3 y hy1 hy3)
    (ptLat_holds T v c _ _ s3 s1 hw3 hw1 hs3 hs1 y hy3 hy1)
  have hm := comp_cmp T v c _ _ _ _ g g' _ _ (hcomp T η κ μ) (hcomp T η' κ' μ') _ _ H1 H3 hlat
    (dn_fwd T hD z.1 z.2) (pt_agree1 T v c _ s1 hw1 hs1 y hy1 g g' hg1 hg3)
  exact val_of_mem T v (T.cls0.y c) (hcomp T η' κ' μ') (hcomp T η κ μ) H3.1 H1.1 hm G hG


set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem valTe_pt (T : Forms0 D u) : ValTe T := by
  intro v c G hG g η κ μ hP
  obtain ⟨_, γ, hD, z, γ1, κ1, hz1, hU, hpt⟩ := hP
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ1 μ κ1 u1 u2 u3 u4 u5
  have hg1 := (ptz_val T hD z _ hpt).trans hz1
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z0.1 z0.2)
  have e1 : ((1 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).1.1 :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = 1 := by simp
  have hw3v : ((((D.mem u).A.T : ℕ) : D.host.E))⁻¹ • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) = z0.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ hTne]
  have H3 : IsCompMv T v c c ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) g 1 1 1 := by
    refine ⟨fun v' _ => by simp, by simp, ?_, ?_, ?_⟩
    · rw [e1, mul_lattice_one]
    · rw [e1, mul_lattice_one, hw3v]
      exact ld_locP T v c z0 (by rw [hz0]; exact one_ne_zero)
    · intro x hx
      have hx' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
        Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c x.1 x.2)
      have e2 : (⟨_, hx⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hx'⟩ := by
        apply Subtype.ext
        show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) •
            ((1 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).1.1 *ᵥ x.1) =
          (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x.1
        rw [e1, Matrix.one_mulVec]
      rw [e2, projection_kernel_eq_functional T v c x hx', map_smul, hg1, smul_eq_mul, mul_one]
  have hw3 : (1 : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul]; exact hT0
  have hy3 : T.lv0.prk v c ⟨_, hw3⟩ = T.atT.res v 1 • (D.fm u).te 0 v c := by
    have e3 : (⟨_, hw3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hT0⟩ := Subtype.ext (one_smul _ _)
    rw [e3, T.lv0.te v c z0 hz0 hT0, map_one, one_smul]
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  have hlat := le_antisymm
    (ptLat_holds T v c _ _ s1 1 hw1 hw3 hs1 (one_nmem T) _ hy1 hy3)
    (ptLat_holds T v c _ _ 1 s1 hw3 hw1 (one_nmem T) hs1 _ hy3 hy1)
  have hm := comp_cmp T v c _ _ (γ.1.1 *ᵥ z.1) _ g g (γ * γ1) 1 (hcomp T η κ μ) 1 (κ * κ1) 1 H1 H3 hlat
    (dn_fwd T hD z.1 z.2) (fun _ _ _ _ => rfl)
  have h := val_of_mem T v (T.cls0.y c) 1 (hcomp T η κ μ) H3.1 H1.1 hm G hG
  rw [mul_one] at h
  exact h

theorem dUAll_holds : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  dUAll_of_same_te fun _ _ T => ⟨valSame_pt T, valTe_pt T⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

theorem hecke_ramified_zero_all : ∀ (D : D7) (u : D.what₂.Word), HidaSetting D u → RT.ConcreteFormsLevelZero D u → HeckeRamifiedLevelZero D u :=
  Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.hecke_ramified_zero_of_matchings_and_du SameDiaZero.diamond_same_place_matchings dUAll_holds

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end

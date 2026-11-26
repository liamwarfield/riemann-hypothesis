module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TNotinSq

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.ProjectionKernelEqFunctional
section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.NatSmulInv
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

theorem nat_smul_inv {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) (hN : (N : E) ≠ 0) (a : 𝓞 E) (w : Fin n → E) :
    ((N : ℕ) : 𝓞 E) • (a • (((N : ℕ) : E)⁻¹ • w)) = a • w := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_natCast]
  rw [mul_left_comm, mul_inv_cancel_left₀ hN]

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem comp_cmp (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c3 : (D.mem u).C.cls 0)
    (w1 w3 : Fin (D.R.N 0) → D.host.E)
    (g1 g3 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (Γ1 Γ3 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h1 h3 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (k1 k3 : T.cls0.lev.U)
    (H1 : IsCompMv T v c c1 w1 g1 Γ1 h1 k1) (H3 : IsCompMv T v c c3 w3 g3 Γ3 h3 k3)
    (hw : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3}))
    (hw1 : w1 ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hg : ∀ l ∈ clsCrd D u 0 (Nat.zero_le _) c, ∀ (e : 𝓞 D.host.E)
      (hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      g1 (T.lv0.prk v c ⟨_, hY⟩) = g3 (T.lv0.prk v c ⟨_, hY⟩)) :
    h3.1⁻¹ * h1.1 ∈ T.cls0.lev.U := by
  obtain ⟨s1, e1, p1, d1, f1⟩ := H1
  obtain ⟨s3, e3, p3, d3, f3⟩ := H3
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have eM : ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      ((Γ3.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Γ1.1.1 := Units.val_mul _ _
  have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ (CrossDiaZero.use₄ (T.atT.Pv v) Γ3.1 p3) p1
  have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ (CrossDiaZero.use₄ (T.atT.Pv v) Γ3.1 d3) (d1.trans hw)
  have hΓU : Γ3.1⁻¹ * Γ1.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (inv_mem Γ3.2) Γ1.2
  have hQd := local_dual_Q_eq_of_P T.atT v c3 c1 (Γ3.1⁻¹ * Γ1.1) hΓU hP
  have eback : ∀ y : Fin (D.R.N 0) → D.host.E,
      Γ3.1.1 *ᵥ (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) =
        Γ1.1.1 *ᵥ y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
  refine trip_mem T v c c1 c3 Γ1 Γ3 h1 h3 k1 k3 s1 s3 e1 e3 hP hPd ?_
  intro z hz
  obtain ⟨b, hbP, hbQ, hb⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPd.le hQd.le
    (x := ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ⟨z, hz, rfl⟩
  obtain ⟨r, hr, b', hb'⟩ := rlv_norm T.atT v b hbP hbQ
  set R := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r with hR
  have hmem : R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
      Ld D u 0 (Nat.zero_le _) c3 := by
    rw [hb', mul_smul]; exact Submodule.smul_mem _ _ hb
  refine ⟨r, hr, hmem, ?_⟩
  have hRz : R • z ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz

  have hloc : Γ1.1.1 *ᵥ (R • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) := by
    rw [← d1]; exact mem_localization_of_mem₂ _ ⟨_, hRz, rfl⟩
  obtain ⟨t0, ht0, ht0m⟩ := (rlv_mem_locP _ _ _).1 hloc
  obtain ⟨l0, hl0, m0, hm0, em⟩ := Submodule.mem_sup.1 ht0m
  obtain ⟨e0, rfl⟩ := Submodule.mem_span_singleton.1 hm0
  obtain ⟨t1, ht1, ht1w⟩ := (rlv_mem_locP _ _ _).1 hw1
  set t := t1 * t0 with ht
  have htP : t ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht1 ht0
  have eW : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (t • (R • z))) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 := by
    rw [Matrix.mulVec_smul, ht, mul_smul, ← em, smul_add, smul_add]
    congr 1
    rw [show t1 • (e0 • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1)) = (t1 * e0) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) from
      smul_smul _ _ _, nat_smul_inv _ hTne, mul_comm]
  have hl : t1 • l0 ∈ clsCrd D u 0 (Nat.zero_le _) c := Submodule.smul_mem _ _ hl0
  have hYL : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 ∈ clsCrd D u 0 (Nat.zero_le _) c := by
    refine add_mem (Submodule.smul_mem _ _ hl) ?_
    rw [mul_smul]; exact Submodule.smul_mem _ _ ht1w
  have hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left hYL
  have hX1m : t • (R • z) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hRz
  have hX1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (⟨_, hX1m⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (t • (R • z))) ∈ _
    rw [eW]; exact hY
  have hX3m : t • (R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) ∈
      Ld D u 0 (Nat.zero_le _) c3 := Submodule.smul_mem _ _ hmem
  have eX3 : Γ3.1.1 *ᵥ (t • (R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))) =
      Γ1.1.1 *ᵥ (t • (R • z)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, eback, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hX3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ (⟨_, hX3m⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ _) ∈ _
    rw [eX3]; exact hX1
  have q1 := f1 ⟨_, hX1m⟩ hX1
  have q3 := f3 ⟨_, hX3m⟩ hX3
  have qg := hg _ hl _ hY
  have k1e : T.lv0.prk v c ⟨_, hX1⟩ = T.lv0.prk v c ⟨_, hY⟩ := congrArg _ (Subtype.ext eW)
  have k3e : T.lv0.prk v c ⟨_, hX3⟩ = T.lv0.prk v c ⟨_, hY⟩ := by
    refine congrArg _ (Subtype.ext ?_)
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ _) = _
    rw [eX3, eW]
  rw [k1e] at q1
  rw [k3e] at q3
  have pr1 : T.lv0.pr v c1 ⟨_, hX1m⟩ = T.atT.res v t • T.lv0.pr v c1 ⟨_, Submodule.smul_mem _ _ hz⟩ :=
    T.lv0.pr_smul v c1 t ⟨_, Submodule.smul_mem _ _ hz⟩
  have pr3 : T.lv0.pr v c3 ⟨_, hX3m⟩ = T.atT.res v t • T.lv0.pr v c3 ⟨_, hmem⟩ :=
    T.lv0.pr_smul v c3 t ⟨_, hmem⟩
  rw [pr1, map_smul] at q1
  rw [pr3, map_smul] at q3
  have hres : T.atT.res v t ≠ 0 := fun h0 => htP (RingHom.mem_ker.2 h0)
  exact smul_right_injective _ hres (q3.trans (qg.symm.trans q1.symm))

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUPt0FOfVals
section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfParts
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def DnMvL (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
    (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) ∧
  (∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (hx : γ.1.1 *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = g (T.lv0.prk v c ⟨_, hx⟩)) ∧
  ∀ (h : (D.mem u).C.Y 0 → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (T.val0.eY s') (T.val0.eY s) →
    (D.fm u).dnT 0 v c g h s = (((T.cls0.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

def UpMvL (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (z : ↥(Ld D u 0 (Nat.zero_le _) c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
    (T.cls0.y ((D.fm u).up 0 v c (T.lv0.pr v c z))).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
  (∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z))))
    (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
    (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩)) ∧
  ∀ (h : (D.mem u).C.Y 0 → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (T.val0.eY s') (T.val0.eY s) →
    (D.fm u).upT 0 v c (T.lv0.pr v c z) h s = (((T.cls0.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

def IsPtZ (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (y : (D.fm u).lk 0 v c) : Prop :=
  ∃ (s : 𝓞 D.host.E), s ∉ T.atT.Pv v ∧ ∃ (hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    T.lv0.prk v c ⟨_, hz⟩ = T.atT.res v s • y

def IsPt (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g)) (y : (D.fm u).lk 0 v c) : Prop :=
  ∃ z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)), T.lv0.pr v _ z = x ∧ IsPtZ T v c g γ z y

theorem dnMvL_ex (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (hg : g ≠ 0) :
    ∃ p : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ×
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      DnMvL T v c g p.1 p.2.1 p.2.2 := by
  obtain ⟨γ, η, κ, h⟩ := T.down_natural_level_zero v c g hg
  exact ⟨(γ, η, κ), h⟩

theorem upMvL_ex (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1) :
    ∃ p : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ×
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      UpMvL T v c z p.1 p.2.1 p.2.2 := by
  obtain ⟨γ, η, κ, h⟩ := T.up_natural_level_zero v c z hz
  exact ⟨(γ, η, κ), h⟩

set_option maxHeartbeats 4000000 in
theorem dnMvL_dnMvs (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {κ : T.cls0.lev.U} (h : DnMvL T v c g γ η κ) :
    (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
    ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T γ κ h := by
  obtain ⟨h1, h2, -, -, h5⟩ := h
  refine ⟨h1, h2, fun f => funext fun s => ?_⟩
  unfold natTr0
  rw [h5 f s _ ?_, Units.val_inv_eq_inv_val]
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ *
    (atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← mul_assoc]
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

set_option maxHeartbeats 4000000 in
theorem upMvL_isUp (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {z : ↥(Ld D u 0 (Nat.zero_le _) c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {κ : T.cls0.lev.U} (h : UpMvL T v c z γ η κ) : IsUpMvF T v c (T.lv0.pr v c z) η := by
  unfold IsUpMvF
  obtain ⟨h1, h2, -, -, -, h6⟩ := h
  refine ⟨γ, κ, h1, h2, ?_⟩
  intro f
  funext s
  unfold natTr0
  rw [h6 f s _ ?_, Units.val_inv_eq_inv_val]
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) γ.1.1 τ *
    (atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← mul_assoc]
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

def IsPair (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (μ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (y : (D.fm u).lk 0 v c) : Prop :=
  g ≠ 0 ∧ ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), DnMvL T v c g γ η κ ∧
    ∃ (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
      (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ' : T.cls0.lev.U),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ z) = 1 ∧ UpMvL T v ((D.fm u).dn 0 v c g) z γ' μ κ' ∧
      IsPtZ T v c g γ z y

def PtEx (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ z, ∃ y, IsPtZ T v c g γ z y

def PtWd (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ x y y', IsPt T v c g γ x y → IsPt T v c g γ x y' → y = y'

def PtInj (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ x x' y, IsPt T v c g γ x y → IsPt T v c g γ x' y → x = x'

def PtSurj (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), g ≠ 0 →
    ∀ γ η κ, DnMvL T v c g γ η κ → ∀ y, ∃ x, IsPt T v c g γ x y

def ValSame (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∀ G ∈ AdFun T.cls0.lev (embT D),
    ∀ g η κ μ g' η' κ' μ' y, IsPair T v c g η κ μ y → IsPair T v c g' η' κ' μ' y →
      G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c * hcomp T η' κ' μ')

def ValTe (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∀ G ∈ AdFun T.cls0.lev (embT D),
    ∀ g η κ μ, IsPair T v c g η κ μ ((D.fm u).te 0 v c) → G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c)

def ValDia (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0), ∃ τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ,
    ∀ G ∈ AdFun T.cls0.lev (embT D), ∀ (a : ((D.mem u).A.Fv v)ˣ) g η κ μ,
      IsPair T v c g η κ μ ((a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c) →
      ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
      ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ → G (T.cls0.y c * hcomp T η κ μ) = G (T.cls0.y c * δ)


set_option maxHeartbeats 8000000 in
theorem dUPt0F_of (T : Forms0 D u) (hE : PtEx T) (hW : PtWd T) (hI : PtInj T) (hS : PtSurj T)
    (vS : ValSame T) (vT : ValTe T) (vD : ValDia T) : DUPt0F T := by
  classical
  unfold DUPt0F
  intro v c
  obtain ⟨P, hP⟩ : ∃ P : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) × UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      ∀ g, g ≠ 0 → DnMvL T v c g (P g).1 (P g).2.1 (P g).2.2 :=
    ⟨fun g => if hg : g ≠ 0 then (dnMvL_ex T v c g hg).choose else 1,
      fun g hg => by simp only [dif_pos hg]; exact (dnMvL_ex T v c g hg).choose_spec⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)),
      ∀ g x, T.lv0.pr v _ (Z g x) = x.1 :=
    ⟨fun g x => (T.lv0.pr_surj v _ x.1).choose, fun g x => (T.lv0.pr_surj v _ x.1).choose_spec⟩
  have hZ1 : ∀ g x, (D.fm u).fv 0 v _ (T.lv0.pr v _ (Z g x)) = 1 := fun g x => by rw [hZ]; exact x.2
  obtain ⟨Q, hQ⟩ : ∃ Q : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) × UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) × T.cls0.lev.U,
      ∀ g x, UpMvL T v ((D.fm u).dn 0 v c g) (Z g x) (Q g x).1 (Q g x).2.1 (Q g x).2.2 :=
    ⟨fun g x => (upMvL_ex T v _ (Z g x) (hZ1 g x)).choose, fun g x => (upMvL_ex T v _ (Z g x) (hZ1 g x)).choose_spec⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (_ : {x // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1}), (D.fm u).lk 0 v c,
      ∀ g x, g ≠ 0 → IsPtZ T v c g (P g).1 (Z g x) (Y g x) :=
    ⟨fun g x => if hg : g ≠ 0 then (hE v c g hg _ _ _ (hP g hg) (Z g x)).choose else 0,
      fun g x hg => by simp only [dif_pos hg]; exact (hE v c g hg _ _ _ (hP g hg) (Z g x)).choose_spec⟩
  have key : ∀ g, g ≠ 0 → ∀ z y, IsPtZ T v c g (P g).1 z y → g y = (D.fm u).fv 0 v _ (T.lv0.pr v _ z) := by
    intro g hg z y hz0
    obtain ⟨s, hs, hz, hy⟩ := hz0
    obtain ⟨-, -, -, h4, -⟩ := hP g hg
    have hres : T.atT.res v s ≠ 0 := fun h0 => hs ((RingHom.mem_ker).2 h0)
    have hx : (P g).1.1.1 *ᵥ (s • z).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [Submodule.coe_smul, Matrix.mulVec_smul]; exact hz
    have h4' := h4 (s • z) hx
    have e : T.lv0.prk v c ⟨_, hx⟩ = T.lv0.prk v c ⟨_, hz⟩ := by
      congr 1; apply Subtype.ext; simp only [Submodule.coe_smul, Matrix.mulVec_smul]
    rw [e, hy, T.lv0.pr_smul] at h4'
    simp only [map_smul, smul_eq_mul] at h4'
    exact (mul_left_cancel₀ hres h4').symm
  have hpair : ∀ g (hg : g ≠ 0) x, IsPair T v c g (P g).2.1 (P g).2.2 (Q g x).2.1 (Y g x) :=
    fun g hg x => ⟨hg, (P g).1, hP g hg, Z g x, (Q g x).1, (Q g x).2.2, hZ1 g x, hQ g x, hY g x hg⟩
  refine ⟨fun g => (P g).1, fun g => (P g).2.1, fun g => (P g).2.2, fun g x => (Q g x).2.1, ?_, ?_, Y,
    (vD v c).choose, ?_, ?_, ?_⟩
  · intro g hg
    exact dnMvL_dnMvs T (hP g hg)
  · intro g x
    have h := upMvL_isUp T (hQ g x)
    rwa [hZ] at h
  · intro g hg x
    rw [key g hg _ _ (hY g x hg), hZ]
    exact x.2
  · intro g hg y hy
    obtain ⟨x', z', hz', hpz⟩ := hS v c g hg _ _ _ (hP g hg) y
    have hx1 : (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x' = 1 := by
      rw [← hz', ← key g hg z' y hpz, hy]
    refine ⟨⟨x', hx1⟩, ?_, ?_⟩
    · exact hW v c g hg _ _ _ (hP g hg) x' _ _ ⟨Z g ⟨x', hx1⟩, hZ g _, hY g _ hg⟩ ⟨z', hz', hpz⟩
    · intro x hx
      apply Subtype.ext
      refine hI v c g hg _ _ _ (hP g hg) x.1 x' y ⟨Z g x, hZ g x, ?_⟩ ⟨z', hz', hpz⟩
      rw [← hx]
      exact hY g x hg
  · intro G hG
    have hD : ∀ p : PD D u v c, (p.1 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) ≠ 0 := fun p h0 => by
      have h := p.1.2
      rw [h0, LinearMap.zero_apply] at h
      exact zero_ne_one h
    refine ⟨fun p hp => ?_, fun p q hpq => ?_, fun p q hpq => ?_, fun a q hq k hk δ hδ => ?_⟩
    · have h := hpair _ (hD p) p.2
      rw [hp] at h
      exact vT v c G hG _ _ _ _ h
    · have h1 := hpair _ (hD p) p.2
      have h2 := hpair _ q.1.2 q.2
      rw [← hpq] at h2
      exact vS v c G hG _ _ _ _ _ _ _ _ _ h1 h2
    · have h1 := hpair _ p.1.2 p.2
      have h2 := hpair _ q.1.2 q.2
      rw [← hpq] at h2
      exact vS v c G hG _ _ _ _ _ _ _ _ _ h1 h2
    · have h := hpair _ q.1.2 q.2
      rw [hq] at h
      exact (vD v c).choose_spec G hG a _ _ _ _ h k hk δ hδ

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem lp_smul_map (P : Ideal (𝓞 E)) [P.IsPrime] (A : Matrix (Fin n) (Fin n) E)
    (M N : Submodule (𝓞 E) (Fin n → E)) (h : ∀ m ∈ M, A *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ P N)
    (x : Fin n → E) (hx : x ∈ P • M) : A *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N) := by
  refine Submodule.smul_induction_on (p := fun x => A *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N)) hx
    (fun p hp m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hsm⟩ := h m hm
    refine ⟨s, hs, ?_⟩
    show s • (A *ᵥ (p • m)) ∈ P • N
    rw [Matrix.mulVec_smul, smul_comm]
    exact Submodule.smul_mem_smul hp hsm
  · show A *ᵥ (x + y) ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N)
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy

theorem inv_mv (g : GL (Fin n) E) (z : Fin n → E) :
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem res_ne (T : Forms0 D u) {v : (D.mem u).A.vT} {s : 𝓞 D.host.E} (hs : s ∉ T.atT.Pv v) :
    T.atT.res v s ≠ 0 := fun h => hs ((RingHom.mem_ker).2 h)

section Mv

variable (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
  {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
  {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
  {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}

theorem dn_fwd (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E)
    (hm : m ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) :
    γ.1.1 *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
  have h1 : γ.1.1 *ᵥ m ∈ mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) := by
    rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.mem_mul_lattice_iff γ.1, inv_mv]
    exact hm
  have h2 : γ.1.1 *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) :=
    ⟨1, (T.atT.Pv v).primeCompl.one_mem, by simpa using h1⟩
  rw [hD.2.2.1] at h2
  exact h2

theorem dn_bwd (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E)
    (hm : m ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ m ∈
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) := by
  have h1 : m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
    CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hm)
  rw [← hD.2.2.1] at h1
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 htm
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
  refine (rlv_mem_locP _ _ _).2 ⟨t, ht, ?_⟩
  rw [← Matrix.mulVec_smul, ← hxe, inv_mv]
  exact hx

end Mv

theorem ptz_sub (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    (z z' : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) {y y' : (D.fm u).lk 0 v c}
    (s s' : 𝓞 D.host.E) (hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c)
    (hz' : s' • (γ.1.1 *ᵥ z'.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c)
    (hy : T.lv0.prk v c ⟨_, hz⟩ = T.atT.res v s • y) (hy' : T.lv0.prk v c ⟨_, hz'⟩ = T.atT.res v s' • y') :
    ∃ w : ↥(Lk T.atT 0 (Nat.zero_le _) v c), w.1 = (s * s') • (γ.1.1 *ᵥ (z.1 - z'.1)) ∧
      T.lv0.prk v c w = (T.atT.res v s * T.atT.res v s') • (y - y') := by
  refine ⟨s' • ⟨_, hz⟩ - s • ⟨_, hz'⟩, ?_, ?_⟩
  · show s' • (s • (γ.1.1 *ᵥ z.1)) - s • (s' • (γ.1.1 *ᵥ z'.1)) = _
    rw [Matrix.mulVec_sub, smul_sub, smul_smul, smul_smul, mul_comm s' s]
  · rw [map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy, hy', smul_smul, smul_smul, smul_sub,
      mul_comm (T.atT.res v s') _]

theorem ptEx_holds (T : Forms0 D u) : PtEx T := by
  intro v c g _ γ η κ hD z
  obtain ⟨s, hs, hsz⟩ := (rlv_mem_locP _ _ _).1 (dn_fwd T hD z.1 z.2)
  have hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left hsz
  refine ⟨(T.atT.res v s)⁻¹ • T.lv0.prk v c ⟨_, hz⟩, s, hs, hz, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ (res_ne T hs), one_smul]

theorem ptWd_holds (T : Forms0 D u) : PtWd T := by
  rintro v c g _ γ η κ hD x y y' ⟨z, hzx, s, hs, hz, hy⟩ ⟨z', hzx', s', hs', hz', hy'⟩
  obtain ⟨w, hw, hpw⟩ := ptz_sub T z z' s s' hz hz' hy hy'
  have hd : (z - z').1 ∈ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) :=
    (T.lv0.pr_ker v _ (z - z')).1 (by rw [map_sub, hzx, hzx', sub_self])
  obtain ⟨t, ht, htd⟩ := (rlv_mem_locP _ _ _).1 (lp_smul_map _ γ.1.1 _ _ (dn_fwd T hD) _ hd)
  have h0 : T.lv0.prk v c (t • w) = 0 := by
    refine (T.lv0.prk_ker v c _).2 ?_
    show t • w.1 ∈ _
    rw [hw, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mono le_rfl le_sup_left htd)
  rw [T.lv0.prk_smul, hpw, smul_smul] at h0
  have hne : T.atT.res v t * (T.atT.res v s * T.atT.res v s') ≠ 0 :=
    mul_ne_zero (res_ne T ht) (mul_ne_zero (res_ne T hs) (res_ne T hs'))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hne)

theorem ptInj_holds (T : Forms0 D u) : PtInj T := by
  rintro v c g _ γ η κ hD x x' y ⟨z, hzx, s, hs, hz, hy⟩ ⟨z', hzx', s', hs', hz', hy'⟩
  obtain ⟨w, hw, hpw⟩ := ptz_sub T z z' s s' hz hz' hy hy'
  rw [sub_self, smul_zero] at hpw
  have hwP : w.1 ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := (T.lv0.prk_ker v c w).1 hpw
  have hb := lp_smul_map _ ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    _ _ (dn_bwd T hD) _ hwP
  rw [hw, ← Matrix.mulVec_smul, inv_mv] at hb
  obtain ⟨t, ht, htd⟩ := (rlv_mem_locP _ _ _).1 hb
  have h0 : T.lv0.pr v _ ((t * (s * s')) • (z - z')) = 0 := by
    refine (T.lv0.pr_ker v _ _).2 ?_
    show (t * (s * s')) • (z.1 - z'.1) ∈ _
    rw [mul_smul]
    exact htd
  rw [T.lv0.pr_smul, map_sub, hzx, hzx'] at h0
  have hne : T.atT.res v (t * (s * s')) ≠ 0 := by
    rw [map_mul, map_mul]
    exact mul_ne_zero (res_ne T ht) (mul_ne_zero (res_ne T hs) (res_ne T hs'))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hne)

theorem dn_img (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}
    (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E) (hm : m ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    ∃ t : 𝓞 D.host.E, t ∉ T.atT.Pv v ∧
      ∃ x ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g), γ.1.1 *ᵥ x = t • m := by
  have h1 : m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
    CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hm)
  rw [← hD.2.2.1] at h1
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 htm
  exact ⟨t, ht, x, hx, hxe⟩

theorem one_nmem (T : Forms0 D u) {v : (D.mem u).A.vT} : (1 : 𝓞 D.host.E) ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)

set_option maxHeartbeats 1000000 in
theorem ptSurj_holds (T : Forms0 D u) : PtSurj T := by
  intro v c g _ γ η κ hD y
  obtain ⟨w0, hw0⟩ := T.lv0.prk_surj v c y
  obtain ⟨t, ht, x, hx, hxe⟩ := dn_img T hD w0.1 w0.2
  obtain ⟨r, hr⟩ := T.atT.res_surj v (T.atT.res v t)⁻¹
  have htne := res_ne T ht
  have hrx : r • x ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) := Submodule.smul_mem _ r hx
  have hz1 : (1 : 𝓞 D.host.E) • (γ.1.1 *ᵥ (r • x)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul, Matrix.mulVec_smul, hxe, smul_smul]
    exact Submodule.smul_mem _ _ w0.2
  refine ⟨T.lv0.pr v _ ⟨r • x, hrx⟩, ⟨r • x, hrx⟩, rfl, 1, one_nmem T, hz1, ?_⟩
  have e : (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = (r * t) • w0 := by
    apply Subtype.ext
    show (1 : 𝓞 D.host.E) • (γ.1.1 *ᵥ (r • x)) = (r * t) • w0.1
    rw [one_smul, Matrix.mulVec_smul, hxe, smul_smul]
  rw [e, T.lv0.prk_smul, map_mul, hr, inv_mul_cancel₀ htne, one_smul, map_one, one_smul, hw0]

theorem dUPt0F_of_vals (T : Forms0 D u) (vS : ValSame T) (vT : ValTe T) (vD : ValDia T) : DUPt0F T :=
  dUPt0F_of T (ptEx_holds T) (ptWd_holds T) (ptInj_holds T) (ptSurj_holds T) vS vT vD

theorem dUAll_of_vals (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), ValSame T ∧ ValTe T ∧ ValDia T) :
    Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll := dUAll_of fun D u T =>
  duFib_of_pt T (dUPt0F_of_vals T (h D u T).1 (h D u T).2.1 (h D u T).2.2)

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

theorem projection_kernel_eq_functional (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (y : ↥(Ld D u 0 (Nat.zero_le _) c))
    (hy : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    T.lv0.prk v c ⟨_, hy⟩ = (D.fm u).fv 0 v c (T.lv0.pr v c y) • (D.fm u).te 0 v c := by
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  obtain ⟨e, he⟩ := T.atT.res_surj v ((D.fm u).fv 0 v c (T.lv0.pr v c y))
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z0.1 z0.2)
  have hte := T.lv0.te v c z0 hz0 hT0
  have hk : (y - e • z0).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    refine (T.lv0.fv_ker v c (y - e • z0)).1 ?_
    rw [map_sub, map_sub, T.lv0.pr_smul, map_smul, hz0, he, smul_eq_mul, mul_one, sub_self]
  have hTk : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (y - e • z0).1 ∈
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.smul_mem_smul (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v)) hk
  have h0 : T.lv0.prk v c ((⟨_, hy⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - e • ⟨_, hT0⟩) = 0 := by
    refine (T.lv0.prk_ker v c _).2 ?_
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y.1 - e • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) ∈ _
    rw [smul_comm e, ← smul_sub]
    exact hTk
  rw [map_sub, T.lv0.prk_smul, hte, he, sub_eq_zero] at h0
  exact h0

theorem ld_locP (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z3 : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz3 : (D.fm u).fv 0 v c (T.lv0.pr v c z3) ≠ 0) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {z3.1}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
    obtain ⟨e, he⟩ := T.atT.res_surj v ((D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, htx⟩) *
      ((D.fm u).fv 0 v c (T.lv0.pr v c z3))⁻¹)
    have hk : ((⟨_, htx⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)) - e • z3).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      refine (T.lv0.fv_ker v c _).1 ?_
      rw [map_sub, map_sub, T.lv0.pr_smul, map_smul, he, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hz3, mul_one,
        sub_self]
    have hl := CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hk)
    obtain ⟨r, hr, hrl⟩ := (rlv_mem_locP _ _ _).1 hl
    refine (rlv_mem_locP _ _ _).2 ⟨r * t, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hr ht, ?_⟩
    have e1 : (r * t) • x = r • (t • x - e • z3.1) + (r * e) • z3.1 := by
      rw [smul_sub, mul_smul, mul_smul, sub_add_cancel]
    rw [e1]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hrl)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · exact localization_mono₂ _ (sup_le (CrossDiaZero.cls_le_ld T c)
      ((Submodule.span_singleton_le_iff_mem _ _).2 z3.2))


set_option maxHeartbeats 4000000 in
theorem ptz_val (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}
    (hD : DnMvL T v c g γ η κ) (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (y : (D.fm u).lk 0 v c)
    (hy : IsPtZ T v c g γ z y) : g y = (D.fm u).fv 0 v _ (T.lv0.pr v _ z) := by
  obtain ⟨s, hs, hz, hy⟩ := hy
  have hz' : γ.1.1 *ᵥ (s • z).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [Submodule.coe_smul, Matrix.mulVec_smul]; exact hz
  have h4 := hD.2.2.2.1 (s • z) hz'
  have e1 : T.lv0.prk v c ⟨_, hz'⟩ = T.lv0.prk v c ⟨_, hz⟩ := by
    congr 1
    apply Subtype.ext
    show γ.1.1 *ᵥ (s • z).1 = s • (γ.1.1 *ᵥ z.1)
    rw [Submodule.coe_smul, Matrix.mulVec_smul]
  rw [e1, hy, T.lv0.pr_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h4
  exact (mul_left_cancel₀ (res_ne T hs) h4).symm

def PtLatF (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (w1 w3 : Fin (D.R.N 0) → D.host.E) (s1 s3 : 𝓞 D.host.E)
    (hz1 : s1 • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) (hz3 : s3 • w3 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    s1 ∉ T.atT.Pv v → s3 ∉ T.atT.Pv v → ∀ y : (D.fm u).lk 0 v c,
    T.lv0.prk v c ⟨_, hz1⟩ = T.atT.res v s1 • y → T.lv0.prk v c ⟨_, hz3⟩ = T.atT.res v s3 • y →
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
              Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) ≤
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3})

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem valDia_of_lat (T : Forms0 D u) (hL : PtLatF T) : ValDia T := by
  intro v c
  refine ⟨Equiv.inv _, ?_⟩
  intro G hG a g η κ μ hP k hk δ hδ
  obtain ⟨_, γ, hD, z, γ', κ', hz1, hU, hpt⟩ := hP
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ' μ κ' u1 u2 u3 u4 u5
  have hga := (ptz_val T hD z _ hpt).trans hz1
  have hkb : ((k : ℤ) : (D.mem u).A.Fv v) = ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := hk
  have hgte : g ((D.fm u).te 0 v c) = ((k : ℤ) : (D.mem u).A.Fv v) := by
    rw [hkb, Units.val_inv_eq_inv_val]
    rw [map_smul, smul_eq_mul] at hga
    exact eq_inv_of_mul_eq_one_right hga

  have hcl := T.val0.dil v a⁻¹ k hkb c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hrel : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a⁻¹ c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨hLc, hLd⟩ := diamond_lattice_transport T v k δ hδ c ((D.fm u).dil 0 v a⁻¹ c) γd hγd ⟨κ0.1, hκ⟩ hrel
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  obtain ⟨ea, hea⟩ := T.atT.res_surj v (a : (D.mem u).A.Fv v)
  have hfz3 : (D.fm u).fv 0 v c (T.lv0.pr v c (ea • z0)) = (a : (D.mem u).A.Fv v) := by
    rw [T.lv0.pr_smul, map_smul, hz0, hea, smul_eq_mul, mul_one]
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hw3v : ((((D.mem u).A.T : ℕ) : D.host.E))⁻¹ • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) =
      (ea • z0).1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ hTne]
  have H3 : IsCompMv T v c ((D.fm u).dil 0 v a⁻¹ c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) g
      ⟨γd, hγd⟩ δ (⟨κ0.1, hκ⟩⁻¹) := by
    refine ⟨hδ.1, ?_, congrArg _ hLc, ?_, ?_⟩
    · show bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
          (T.cls0.y ((D.fm u).dil 0 v a⁻¹ c)).1 = (T.cls0.y c).1 * δ.1 * κ0.1⁻¹
      simp only [Subgroup.coe_mul] at hrel
      rw [hrel, mul_inv_cancel_right]
    · show Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
          (Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a⁻¹ c))) = _
      rw [hLd, hw3v]
      exact ld_locP T v c (ea • z0) (by rw [hfz3]; exact Units.ne_zero a)
    · intro x hx
      have hw : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Ld D u 0 (Nat.zero_le _) c :=
        CrossDiaZero.dni_mem_of _ hLd x.2
      have hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
          ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈
          Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a⁻¹ c) := by
        rw [inv_mv]; exact x.2
      have hdf := UnramifiedDiagonal.diaFun_same T v k δ hδ c _ γd ⟨κ0.1, hκ⟩ hrel _ hw hz2
      rw [CrossDiaZero.pr_congr T v _ ⟨_, hz2⟩ x (inv_mv γd x.1)] at hdf
      rw [hdf]
      have hp := projection_kernel_eq_functional T v c ⟨_, hw⟩ hx
      show _ = g (T.lv0.prk v c ⟨_, hx⟩)
      rw [hp, map_smul, hgte, smul_eq_mul, zsmul_eq_mul, mul_comm]

  have hw3 : (1 : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul]; exact Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c _ (ea • z0).2)
  have hy3 : T.lv0.prk v c ⟨_, hw3⟩ = T.atT.res v 1 • ((a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c) := by
    have hT3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [← one_smul (𝓞 D.host.E) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1)]; exact hw3
    have e3 : (⟨_, hw3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hT3⟩ := Subtype.ext (one_smul _ _)
    rw [e3, projection_kernel_eq_functional T v c (ea • z0) hT3, hfz3, map_one, one_smul]
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  have hlat := le_antisymm
    (hL v c _ _ s1 1 hw1 hw3 hs1 (one_nmem T) _ hy1 hy3)
    (hL v c _ _ 1 s1 hw3 hw1 (one_nmem T) hs1 _ hy3 hy1)
  have hm := comp_cmp T v c _ _ (γ.1.1 *ᵥ z.1) _ g g (γ * γ') ⟨γd, hγd⟩ (hcomp T η κ μ) δ (κ * κ')
    (⟨κ0.1, hκ⟩⁻¹) H1 H3 hlat (dn_fwd T hD z.1 z.2) (fun _ _ _ _ => rfl)
  exact val_of_mem T v (T.cls0.y c) δ (hcomp T η κ μ) hδ.1 H1.1 hm G hG

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem natS_cancel (N : ℕ) (hN : (N : E) ≠ 0) (a b : Fin n → E)
    (h : ((N : ℕ) : 𝓞 E) • a = ((N : ℕ) : 𝓞 E) • b) : a = b := by
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def, map_natCast] at hi
  exact mul_left_cancel₀ hN hi

theorem natS_inv (N : ℕ) (hN : (N : E) ≠ 0) (w : Fin n → E) : ((N : ℕ) : 𝓞 E) • ((N : E)⁻¹ • w) = w := by
  funext i
  simp [Algebra.smul_def, hN]

theorem smul_T_of (P : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) (σ τ : 𝓞 E)
    (hσT : ∀ p ∈ P, ∃ e : 𝓞 E, σ * p = e * τ) (q : Fin n → E) (hq : q ∈ P • N) :
    ∃ d' ∈ N, σ • q = τ • d' := by
  refine Submodule.smul_induction_on (p := fun q => ∃ d' ∈ N, σ • q = τ • d') hq
    (fun p hp n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨e, he⟩ := hσT p hp
    exact ⟨e • n, N.smul_mem e hn, by rw [smul_smul, he, mul_comm e τ, mul_smul]⟩
  · obtain ⟨d1, h1, e1⟩ := hx
    obtain ⟨d2, h2, e2⟩ := hy
    exact ⟨d1 + d2, N.add_mem h1 h2, by rw [smul_add, e1, e2, smul_add]⟩

end Gen

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ptLat_holds (T : Forms0 D u) : PtLatF T := by
  intro v c w1 w3 s1 s3 hz1 hz3 hs1 hs3 y hy1 hy3
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hdm : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    sub_mem (Submodule.smul_mem _ _ hz1) (Submodule.smul_mem _ _ hz3)
  have hd0 : T.lv0.prk v c ⟨_, hdm⟩ = 0 := by
    have e0 : (⟨_, hdm⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) =
        s3 • (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - s1 • (⟨_, hz3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :=
      Subtype.ext rfl
    rw [e0, map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy1, hy3, smul_smul, smul_smul, mul_comm, sub_self]
  have hdP : s3 • (s1 • w1) - s1 • (s3 • w3) ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c :=
    (T.lv0.prk_ker v c _).1 hd0
  obtain ⟨σ, hσ, hσT⟩ := exists_not_mem_Pv_mul_mem_span_T T v c
  obtain ⟨d', hd'L, hd'⟩ := smul_T_of _ _ σ _ hσT _ hdP
  have hW : (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) =
      d' + (σ * s1 * s3) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3) := by
    rw [← sub_eq_iff_eq_add]
    apply natS_cancel _ hTne
    rw [← hd', smul_sub, smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3),
      smul_comm (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (σ * s1 * s3), natS_inv _ hTne, natS_inv _ hTne, smul_sub,
      smul_smul, smul_smul, smul_smul, smul_smul, mul_right_comm σ s3 s1]
  have hd'loc := CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hd'L)
  obtain ⟨t', ht', ht'd⟩ := (rlv_mem_locP _ _ _).1 hd'loc
  intro x hx
  obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨l, hl, m, hm, em⟩ := Submodule.mem_sup.1 htx
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hm
  have hP : (T.atT.Pv v).IsPrime := inferInstance
  refine (rlv_mem_locP _ _ _).2 ⟨t' * (σ * s1 * s3) * t, ?_, ?_⟩
  · intro h
    rcases hP.mem_or_mem h with h | h
    · rcases hP.mem_or_mem h with h | h
      · exact ht' h
      · rcases hP.mem_or_mem h with h | h
        · rcases hP.mem_or_mem h with h | h
          · exact hσ h
          · exact hs1 h
        · exact hs3 h
    · exact ht h
  · rw [mul_smul, ← em, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ hl)) ?_
    rw [smul_comm (t' * (σ * s1 * s3)) e, mul_smul t' (σ * s1 * s3), hW, smul_add, smul_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ ht'd))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))))

theorem valDia_holds (T : Forms0 D u) : ValDia T :=
  valDia_of_lat T (ptLat_holds T)

theorem dUAll_of_same_te (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), ValSame T ∧ ValTe T) :
    Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  dUAll_of_vals fun D u T => ⟨(h D u T).1, (h D u T).2, valDia_holds T⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end

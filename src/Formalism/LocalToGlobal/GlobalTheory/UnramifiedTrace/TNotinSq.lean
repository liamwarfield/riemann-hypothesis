module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfPt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.SameCommon

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.MulLatSupSpan
section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TripMem
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
theorem val_of_mem (T : Forms0 D u) (v : (D.mem u).A.vT)
    (y h1 h2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hs1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h1.1 = 1)
    (hs2 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h2.1 = 1)
    (hm : h1.1⁻¹ * h2.1 ∈ T.cls0.lev.U)
    (G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ)
    (hG : G ∈ AdFun T.cls0.lev (embT D)) :
    G (y * h2) = G (y * h1) := by
  have hx : (y * h2).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (1 : GL (Fin (D.R.N 0)) D.host.E) * (y * h1).1 * (⟨h1.1⁻¹ * h2.1, hm⟩ : T.cls0.lev.U).1 := by
    simp [mul_assoc]
  have key := hG 1 (one_mem _) (y * h1) (y * h2) ⟨h1.1⁻¹ * h2.1, hm⟩ hx
  have hχ : ((T.cls0.lev.chi ⟨h1.1⁻¹ * h2.1, hm⟩ : ℂˣ) : ℂ) = 1 := by
    rw [T.cls0.lev.chi_triv ⟨h1.1⁻¹ * h2.1, hm⟩ (fun w hw => ?_)]
    · rfl
    have hne : w ≠ (T.atT.eV v).1 := fun h => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.level_places_not_bad T.atT v (h ▸ hw)
    show bc (prV (E := D.host.E) w) (h1.1⁻¹ * h2.1) = 1
    rw [map_mul, map_inv, hs1 w hne, hs2 w hne, inv_one, one_mul]
  funext s
  rw [key s s (fun τ => by simp [atInf, Matrix.map_one]), hχ, one_mul]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem trip_mem (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c3 : (D.mem u).C.cls 0)
    (Γ1 Γ3 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h1 h3 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (k1 k3 : T.cls0.lev.U)
    (hs1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h1.1 = 1)
    (hs3 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h3.1 = 1)
    (e1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * h1.1 * k1.1)
    (e3 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1 * (T.cls0.y c3).1 = (T.cls0.y c).1 * h3.1 * k3.1)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3))
    (hF : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) •
          (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
          Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    h3.1⁻¹ * h1.1 ∈ T.cls0.lev.U := by
  have hΓ : ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E)) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (inv_mem Γ3.2) Γ1.2
  have hX : (T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Γ3.1⁻¹ * Γ1.1) *
      (T.cls0.y c1).1 = k3.1⁻¹ * (h3.1⁻¹ * h1.1) * k1.1 := by
    rw [map_mul, map_inv]
    rw [show (T.cls0.y c3).1⁻¹ * ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1) * (T.cls0.y c1).1 =
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1 * (T.cls0.y c3).1)⁻¹ *
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1 * (T.cls0.y c1).1) by group, e1, e3]
    group
  have hmem := fun x => T.cls0.lev.21 x
  have H := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.local_unitary_of_matching_zero T v c3 c1 (Γ3.1⁻¹ * Γ1.1) hΓ (by
    rw [hX]
    exact mul_mem (mul_mem (inv_mem ((hmem _).1 k3.2).1) (mul_mem (inv_mem h3.2) h1.2)) ((hmem _).1 k1.2).1) hP hPd hF
  have hh : h3.1⁻¹ * h1.1 = k3.1 * ((T.cls0.y c3).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Γ3.1⁻¹ * Γ1.1) * (T.cls0.y c1).1) * k1.1⁻¹ := by
    rw [hX]; group
  refine (hmem _).2 ⟨mul_mem (inv_mem h3.2) h1.2, fun w => ?_⟩
  by_cases hw : w = (T.atT.eV v).1
  · rw [hw, hh, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (((hmem _).1 k3.2).2 _) H) (inv_mem (((hmem _).1 k1.2).2 _))
  · rw [map_mul, map_inv, hs1 w hw, hs3 w hw, inv_one, one_mul]
    exact one_mem _

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

theorem localization_sup_congr {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P : Ideal R) [P.IsPrime]
    {X Y : Submodule R W} (S : Submodule R W) (h : Formalism.HermitianLatticesTheory.localization₂ P X = Formalism.HermitianLatticesTheory.localization₂ P Y) :
    Formalism.HermitianLatticesTheory.localization₂ P (X ⊔ S) = Formalism.HermitianLatticesTheory.localization₂ P (Y ⊔ S) := by
  have key : ∀ {X Y : Submodule R W}, Formalism.HermitianLatticesTheory.localization₂ P X = Formalism.HermitianLatticesTheory.localization₂ P Y →
      Formalism.HermitianLatticesTheory.localization₂ P (X ⊔ S) ≤ Formalism.HermitianLatticesTheory.localization₂ P (Y ⊔ S) := by
    intro X Y h x hx
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsx
    have ha0 : a ∈ Formalism.HermitianLatticesTheory.localization₂ P X := ⟨1, P.primeCompl.one_mem, by simpa using ha⟩
    rw [h] at ha0
    obtain ⟨t, ht, hta⟩ := ha0
    refine ⟨t * s, P.primeCompl.mul_mem ht hs, ?_⟩
    rw [mul_smul, ← hab, smul_add]
    exact Submodule.add_mem_sup hta (S.smul_mem t hb)
  exact le_antisymm (key h) (key h.symm)

theorem mulLat_sup_span {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    mulLat g (L ⊔ Submodule.span (𝓞 E) {y}) = mulLat g L ⊔ Submodule.span (𝓞 E) {g *ᵥ y} := by
  unfold mulLat
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  rfl

variable {D : D7} {u : D.what₂.Word}

def IsCompMv (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (Γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (k : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * h.1 * k.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat Γ.1.1 (clsCrd D u 0 (Nat.zero_le _) c1)) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat Γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w}) ∧
  ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1))
    (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ.1.1 *ᵥ x.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩)


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem comp_of_moves (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (d1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (d2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (d3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (d4 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η' : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : T.cls0.lev.U)
    (u1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1)
    (u2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
      (T.cls0.y ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z))).1 =
        (T.cls0.y ((D.fm u).dn 0 v c g)).1 * η'.1 * κ'.1)
    (u3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ'.1.1 (clsCrd D u 0 (Nat.zero_le _)
        ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (u4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ'.1.1 (Ld D u 0 (Nat.zero_le _)
        ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}))
    (u5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z))))
      (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = (D.fm u).fv 0 v _ (T.lv0.pr v _ ⟨_, hx⟩)) :
    IsCompMv T v c ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)) (γ.1.1 *ᵥ z.1) g (γ * γ')
      (hcomp T η κ η') (κ * κ') := by
  have eM : ((γ * γ').1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = γ.1.1 * γ'.1.1 := by
    simp only [Subgroup.coe_mul, Units.val_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v' hv'
    simp only [hcomp, kU, Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, d1 v' hv', u1 v' hv', one_mul, mul_one,
      mul_inv_cancel]
  · simp only [hcomp, kU, Subgroup.coe_mul, InvMemClass.coe_inv, map_mul]
    rw [mul_assoc, u2, ← mul_assoc, ← mul_assoc, d2]
    group
  · rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ d3 u3
  · rw [eM]
    refine rlv_chainP (T.atT.Pv v) _ _ ?_ u4
    rw [mulLat_sup_span, Matrix.mulVec_smul]
    exact localization_sup_congr _ _ d3
  · intro x hx
    have hmem : γ'.1.1 *ᵥ x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) := by
      rw [← u4]; exact mem_localization_of_mem₂ _ ⟨x.1, x.2, rfl⟩
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hmem
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 htx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have hTE : ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by simp
    have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast (D.mem u).A.T_prime.ne_zero

    have e1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • a + r • z.1 := by
      have : (t • x).1 = t • x.1 := rfl
      rw [this, Matrix.mulVec_smul, ← e, smul_add]
      congr 1
      rw [smul_comm, ← algebraMap_smul D.host.E (((D.mem u).A.T : ℕ) : 𝓞 D.host.E), ← algebraMap_smul D.host.E r,
        ← algebraMap_smul D.host.E r, smul_smul, smul_smul]
      congr 1
      simp only [map_natCast]
      field_simp
    have hin : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) := by
      rw [e1]
      exact add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ z.2)
    have e2 : γ.1.1 *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1)) =
        t • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ * γ').1.1 *ᵥ x.1)) := by
      have : (t • x).1 = t • x.1 := rfl
      rw [this, eM, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm]
    have hin2 : γ.1.1 *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [e2]; exact Submodule.smul_mem _ _ hx
    have f1 := u5 (t • x) hin
    have f2 := d4 ⟨_, hin⟩ hin2
    have p1 : T.lv0.prk v c ⟨_, hin2⟩ = T.atT.res v t • T.lv0.prk v c ⟨_, hx⟩ := by
      rw [← T.lv0.prk_smul]
      exact congrArg _ (Subtype.ext e2)
    rw [T.lv0.pr_smul, map_smul, f2, p1, map_smul] at f1
    have hres : T.atT.res v t ≠ 0 := fun h0 => ht (RingHom.mem_ker.2 h0)
    exact smul_right_injective _ hres f1

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem t_notin_sq (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ T.atT.Pv v ^ 2 := by
  intro hT
  obtain ⟨x0, hx0⟩ : ∃ x0, (D.fm u).fv 0 v c x0 ≠ 0 := by
    by_contra h
    apply (D.fm u).fv_ne 0 v c
    ext x0
    by_contra hx
    exact h ⟨x0, by rwa [LinearMap.zero_apply] at hx⟩
  obtain ⟨z, hz⟩ := T.lv0.pr_surj v c (((D.fm u).fv 0 v c x0)⁻¹ • x0)
  have hx : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 := by
    rw [hz, map_smul, smul_eq_mul, inv_mul_cancel₀ hx0]
  have hTz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z.1 z.2)
  have hte := T.lv0.te v c z hx hTz
  have hsq : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := by
    have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ (T.atT.Pv v ^ 2) • Ld D u 0 (Nat.zero_le _) c :=
      Submodule.smul_mem_smul hT z.2
    rw [pow_two, Submodule.mul_smul] at h1
    exact Submodule.smul_mono le_rfl le_sup_right h1
  have h0 := (T.lv0.prk_ker v c ⟨_, hTz⟩).2 hsq
  rw [hte] at h0
  exact (D.fm u).te_ne 0 v c h0


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_not_mem_Pv_mul_mem_span_T (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    ∃ s : 𝓞 D.host.E, s ∉ T.atT.Pv v ∧ ∀ p ∈ T.atT.Pv v, ∃ e : 𝓞 D.host.E,
      s * p = e * (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  have hle : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} ≤ T.atT.Pv v :=
    (Ideal.span_singleton_le_iff_mem _).2 (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v))
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ T.atT.Pv v := by
    intro h
    apply t_notin_sq T v c
    have h2 : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} ≤ T.atT.Pv v ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span rfl)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun p hp => ?_⟩
  have hm : s * p ∈ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} := by
    rw [hJ, mul_comm s p]; exact Ideal.mul_mem_mul hp hsJ
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨e, he.symm⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end

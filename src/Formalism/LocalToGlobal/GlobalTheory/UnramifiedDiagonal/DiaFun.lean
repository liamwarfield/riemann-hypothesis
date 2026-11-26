module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.LemmaBSecondBranchOfLength
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaFun
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem diaFun_same (T : Forms0 D u) (v : (D.mem u).A.vT) (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c2 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (κd : T.cls0.lev.U)
    (h : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1)
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈
      Ld D u 0 (Nat.zero_le _) c2) :
    (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hz2⟩) = k • (D.fm u).fv 0 v c (T.lv0.pr v c ⟨z, hz⟩) := by
  have h1 := (mem_local_dual_lattice_iff' T.cls0 c (T.atT.eV v).1
    (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))).1
    (Submodule.subset_span ⟨z, hz, rfl⟩)
  have h2 := (mem_local_dual_lattice_iff' T.cls0 c2 (T.atT.eV v).1
    (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
      ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a))).1
    (Submodule.subset_span ⟨_, hz2, rfl⟩)
  rw [T.fv0 v c2 ⟨_, hz2⟩ h2, T.fv0 v c ⟨z, hz⟩ h1]
  refine (congrArg (T.fMe0 v) ?_).trans (map_zsmul (T.fMe0 v) k _)
  have hκ : bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 ∈ T.cls0.lev.Uloc (T.atT.eV v).1 :=
    ((T.cls0.lev.U_eq _).1 κd.2).2 _
  rw [T.cls0.lev.UlocAlt _ (T.atT.eV v).2] at hκ
  obtain ⟨hgκ, hfix⟩ := (Subgroup.mem_inf.1 hκ).2
  obtain ⟨-, -, hgδ, hfδ⟩ := hδ
  have hw' : bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1 * bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 =
      bc (prV (E := D.host.E) (T.atT.eV v).1) (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd) *
        bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c2).1 * bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 := by
    have e0 := congrArg (bc (prV (E := D.host.E) (T.atT.eV v).1)) h
    simp only [Subgroup.coe_mul, map_mul] at e0
    exact e0
  have eg : (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
      ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a)) =
      (((bc (prV (E := D.host.E) (T.atT.eV v).1)
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd))⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
        (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)) := by
    rw [← map_inv, ← map_inv]
    funext a
    rw [RingHom.map_mulVec]
    rfl
  have hdd : (((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _)) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))) = ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))) := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hu : (((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))) ∈
      latS (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (T.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb)) := by
    refine (hgδ _).2 ?_
    rw [hdd]
    exact h1
  have key : (((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c2).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
      (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
        ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a)) =
      ((bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
        ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))) := by
    have gid : ∀ (Yc Dl Y2 G K : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] (T.atT.eV v).1.adicCompletion D.host.F)),
        Yc * Dl = G * Y2 * K → Y2⁻¹ * G⁻¹ = K * Dl⁻¹ * Yc⁻¹ := by
      intro Yc Dl Y2 G K e0
      have : Y2 = G⁻¹ * (Yc * Dl) * K⁻¹ := by rw [e0]; group
      rw [this]; group
    have gm := congrArg Units.val (gid _ _ _ _ _ hw')
    rw [Units.val_mul, Units.val_mul, Units.val_mul] at gm
    rw [eg, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, gm]
  have e1 : T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, h2⟩ =
      T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, hu⟩ := by
    refine Eq.trans ?_ (hfix ⟨_, hu⟩)
    congr 1
    exact Subtype.ext key
  have e2 := hfδ ⟨_, hu⟩
  have e3 : (⟨(bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1).1 *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))), (hgδ _).1 hu⟩ :
      latS (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (T.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb))) =
      ⟨((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))), h1⟩ := Subtype.ext hdd
  calc T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, h2⟩
      = T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, hu⟩ := e1
    _ = k • T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨(bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1).1 *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))), (hgδ _).1 hu⟩ := e2.symm
    _ = k • T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))), h1⟩ := by rw [e3]

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaSame
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word}

theorem conj_off (v : HeightOneSpectrum (𝓞 D.host.F))
    (η δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := D.host.E) v') η.1 = 1)
    (hδ : ∀ v', v' ≠ v → bc (prV (E := D.host.E) v') δ.1 = 1) :
    ∀ v', v' ≠ v → bc (prV (E := D.host.E) v') (δ⁻¹ * η * δ).1 = 1 := by
  intro v' hv'
  have e : (δ⁻¹ * η * δ).1 = δ.1⁻¹ * η.1 * δ.1 := rfl
  rw [e, map_mul, map_mul, map_inv, hη v' hv', hδ v' hv']
  simp

def UpDiaSame0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
    ∀ (c : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E),
      γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    ∀ κd : T.cls0.lev.U,
      (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κd.1 →
    ∃ (σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
        {x : (D.fm u).lv 0 v ((D.fm u).dil 0 v a c) // (D.fm u).fv 0 v ((D.fm u).dil 0 v a c) x = 1})
      (Mv : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Mv2 : {x : (D.fm u).lv 0 v ((D.fm u).dil 0 v a c) // (D.fm u).fv 0 v ((D.fm u).dil 0 v a c) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsUpMvF T v c x.1 (Mv x)) ∧ (∀ x, IsUpMvF T v _ x.1 (Mv2 x)) ∧
      ∀ x, (Mv2 (σ x)).1⁻¹ * κd.1 * (δ.1⁻¹ * (Mv x).1 * δ.1) ∈ T.cls0.lev.U

def DnDiaSame0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
    ∀ (c : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E),
      γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    ∀ κd : T.cls0.lev.U,
      (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κd.1 →
    ∃ (σ : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} ≃
        {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v ((D.fm u).dil 0 v a c)) //
          x ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = 1})
      (Mv : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Mv2 : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v ((D.fm u).dil 0 v a c)) //
          x ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsDnMvF T v c x.1 (Mv x)) ∧ (∀ x, IsDnMvF T v _ x.1 (Mv2 x)) ∧
      ∀ x, (Mv2 (σ x)).1⁻¹ * κd.1 * (δ.1⁻¹ * (Mv x).1 * δ.1) ∈ T.cls0.lev.U


set_option maxHeartbeats 4000000 in
theorem diaU_same (T : Forms0 D u) (hM : UpDiaSame0F T) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    dia D u 0 v a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v a φ) := by
  classical
  obtain ⟨g, hg, hgφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  obtain ⟨G, hG, hGφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl (Uop D u 0 v φ) (U_op_preserves_forms_zero T v φ hφ)
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  have hgδ := S0.adelic_function_right_translate_diamond T.cls0.lev (Forms.embT D) _ _ (S0.level_places_not_bad T.atT v) hδ hgA
  have hdφ : ∀ c1, dia D u 0 v a φ c1 =
      fun s => g (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v a c1 (φ ((D.fm u).dil 0 v a c1)) = _
    rw [hgφ]
    exact T.val0.dilT v a k hk c1 δ hδ g hgA
  funext c
  have hcl := T.val0.dil v a k hk c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨σ, Mv, Mv2, hMv, hMv2, hm⟩ := hM v a k hk δ hδ c γd hγd ⟨κ0.1, hκ⟩ hx
  have hL : dia D u 0 v a (Uop D u 0 v φ) c =
      fun s => G (T.cls0.y c * δ) (T.val0.eY s) := by
    show (D.fm u).dilT 0 v a c (Uop D u 0 v φ ((D.fm u).dil 0 v a c)) = _
    rw [hGφ]
    exact T.val0.dilT v a k hk c δ hδ G hGA
  rw [hL, U_op_eq_move_sum T v (dia D u 0 v a φ) hgδ hdφ c Mv hMv]
  funext s
  rw [S0.adelic_value_translate T.cls0.lev (Forms.embT D) (fun τ x => S0.embedding_conj_compat D τ x) hGA γd hγd _ _
    ⟨κ0.1, hκ⟩ hx]
  have hG2 : ∀ y', G (T.cls0.y ((D.fm u).dil 0 v a c)) y' =
      ∑ x, g (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 x) y' := by
    intro y'
    have h1 := congrFun (hGφ ((D.fm u).dil 0 v a c)) (T.val0.eY.symm y')
    rw [U_op_eq_move_sum T v φ hgA hgφ _ Mv2 hMv2] at h1
    change _ = G (T.cls0.y ((D.fm u).dil 0 v a c)) (T.val0.eY (T.val0.eY.symm y')) at h1
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [hG2, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv2 (σ x)).1⁻¹ * κ0.1 * (δ.1⁻¹ * (Mv x).1 * δ.1), hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv2 (σ x)
  have hx2 : (T.cls0.y c * Mv x * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 (σ x)).1 * m.1 := by
    have e2 : (T.cls0.y c * Mv x * δ).1 = (T.cls0.y c * δ).1 * (δ.1⁻¹ * (Mv x).1 * δ.1) := by
      simp only [Subgroup.coe_mul]; group
    rw [e2, hx]
    simp only [Subgroup.coe_mul, m]
    group
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv2 (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hχ : T.cls0.lev.chi m = T.cls0.lev.chi ⟨κ0.1, hκ⟩ := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (S0.level_places_not_bad T.atT v) ((Mv2 (σ x))⁻¹) (δ⁻¹ * Mv x * δ)
      hs2i (conj_off _ _ _ hs1 hδ.1) ⟨κ0.1, hκ⟩ 1 m
      (by simp only [m, Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  rw [S0.adelic_value_translate T.cls0.lev (Forms.embT D) (fun τ x => S0.embedding_conj_compat D τ x) hgA γd hγd _ _
    m hx2, hχ]


set_option maxHeartbeats 4000000 in
theorem diaD_same (T : Forms0 D u) (hM : DnDiaSame0F T) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    dia D u 0 v a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v a φ) := by
  classical
  obtain ⟨g, hg, hgφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  obtain ⟨G, hG, hGφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl (Dop D u 0 v φ) (D_op_preserves_forms_zero T v φ hφ)
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  have hgδ := S0.adelic_function_right_translate_diamond T.cls0.lev (Forms.embT D) _ _ (S0.level_places_not_bad T.atT v) hδ hgA
  have hdφ : ∀ c1, dia D u 0 v a φ c1 =
      fun s => g (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v a c1 (φ ((D.fm u).dil 0 v a c1)) = _
    rw [hgφ]
    exact T.val0.dilT v a k hk c1 δ hδ g hgA
  funext c
  have hcl := T.val0.dil v a k hk c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨σ, Mv, Mv2, hMv, hMv2, hm⟩ := hM v a k hk δ hδ c γd hγd ⟨κ0.1, hκ⟩ hx
  have hL : dia D u 0 v a (Dop D u 0 v φ) c =
      fun s => G (T.cls0.y c * δ) (T.val0.eY s) := by
    show (D.fm u).dilT 0 v a c (Dop D u 0 v φ ((D.fm u).dil 0 v a c)) = _
    rw [hGφ]
    exact T.val0.dilT v a k hk c δ hδ G hGA
  rw [hL, D_op_eq_move_sum T v (dia D u 0 v a φ) hgδ hdφ c Mv hMv]
  funext s
  rw [S0.adelic_value_translate T.cls0.lev (Forms.embT D) (fun τ x => S0.embedding_conj_compat D τ x) hGA γd hγd _ _
    ⟨κ0.1, hκ⟩ hx]
  have hG2 : ∀ y', G (T.cls0.y ((D.fm u).dil 0 v a c)) y' =
      ∑ x, g (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 x) y' := by
    intro y'
    have h1 := congrFun (hGφ ((D.fm u).dil 0 v a c)) (T.val0.eY.symm y')
    rw [D_op_eq_move_sum T v φ hgA hgφ _ Mv2 hMv2] at h1
    change _ = G (T.cls0.y ((D.fm u).dil 0 v a c)) (T.val0.eY (T.val0.eY.symm y')) at h1
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [hG2, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv2 (σ x)).1⁻¹ * κ0.1 * (δ.1⁻¹ * (Mv x).1 * δ.1), hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv2 (σ x)
  have hx2 : (T.cls0.y c * Mv x * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 (σ x)).1 * m.1 := by
    have e2 : (T.cls0.y c * Mv x * δ).1 = (T.cls0.y c * δ).1 * (δ.1⁻¹ * (Mv x).1 * δ.1) := by
      simp only [Subgroup.coe_mul]; group
    rw [e2, hx]
    simp only [Subgroup.coe_mul, m]
    group
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv2 (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hχ : T.cls0.lev.chi m = T.cls0.lev.chi ⟨κ0.1, hκ⟩ := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (S0.level_places_not_bad T.atT v) ((Mv2 (σ x))⁻¹) (δ⁻¹ * Mv x * δ)
      hs2i (conj_off _ _ _ hs1 hδ.1) ⟨κ0.1, hκ⟩ 1 m
      (by simp only [m, Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  rw [S0.adelic_value_translate T.cls0.lev (Forms.embT D) (fun τ x => S0.embedding_conj_compat D τ x) hgA γd hγd _ _
    m hx2, hχ]

theorem diamond_same_place_of_matchings (T : Forms0 D u) (hU : UpDiaSame0F T) (hD : DnDiaSame0F T) : DiamondOperatorCommutationAtPlace D u :=
  fun v a φ hφ => ⟨diaU_same T hU v a φ hφ, diaD_same T hD v a φ hφ⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
end

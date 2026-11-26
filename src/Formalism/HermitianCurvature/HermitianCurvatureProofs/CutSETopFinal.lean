module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpRFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralCompositionZero

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhR
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace RhRPf

section pair

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem fst_mul_apply (p q : Pr V) (v : V) : (p * q).1 v = p.1 (q.1 v) := rfl
theorem fst_mkP (a a' : Module.End ℂ V) : (mkP a a').1 = a := rfl

end pair

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem list_cb_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Ψ : RadSp k r z z' π π'),
    ((((ls.map L.cb).prod).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (ls.map fun a => star (c a)).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g
  | [], Ψ => by
    funext c g
    simp only [List.map_nil, List.prod_nil, one_smul]
    rfl
  | a :: ls, Ψ => by
    funext c g
    rw [List.map_cons, List.prod_cons, fst_mul_apply, hL.2.2.2.2.1 a, fst_mkP, X.op_apply,
      list_cb_apply X L hL ls Ψ]
    simp only [crd, opL, cbOp, List.map_cons, List.prod_cons, mul_smul]

theorem list_c_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Ψ : RadSp k r z z' π π'),
    ((((ls.map L.c).prod).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (ls.map fun a => c a).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g
  | [], Ψ => by
    funext c g
    simp only [List.map_nil, List.prod_nil, one_smul]
    rfl
  | a :: ls, Ψ => by
    funext c g
    rw [List.map_cons, List.prod_cons, fst_mul_apply, hL.2.2.1 a, fst_mkP, X.op_apply,
      list_c_apply X L hL ls Ψ]
    simp only [crd, opL, cOp, List.map_cons, List.prod_cons, mul_smul]

theorem drb_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Ψ : RadSp k r z z' π π') :
    (((L.Drb).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      CutMP.dMul (CutMP.drbF r) (Ψ : Fn k r (Wq →L[ℂ] Wp)) := by
  have e : L.Drb = ((List.finRange r).map L.cb).prod := by
    rw [R.LevelData.Drb, List.ofFn_eq_map]
  rw [e, list_cb_apply X L hL]
  funext c g
  simp only [CutMP.dMul, CutMP.drbF, map_prod]
  congr 1

theorem dr_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Ψ : RadSp k r z z' π π') :
    (((L.Dr).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      CutMP.dMul (CutMP.drF r) (Ψ : Fn k r (Wq →L[ℂ] Wp)) := by
  have e : L.Dr = ((List.finRange r).map L.c).prod := by
    rw [R.LevelData.Dr, List.ofFn_eq_map]
  rw [e, list_c_apply X L hL]
  funext c g
  simp only [CutMP.dMul, CutMP.drF]
  congr 1

theorem st_fst {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} (X : ActualOps P.k P.r z z' π π')
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hQQ : ∀ Y, st.QQ Y = M.sgn P l0 • X.QQ Y)
    (Y : ℂ) (a b : Fin 2) : (st.QQ Y a b).1 = M.sgn P l0 • X.t Y a b := by
  rw [hQQ Y, Matrix.smul_apply, ActualOps.QQ, Matrix.of_apply, Qx8.smul_mkP]
  rfl

theorem t_slice_congr (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) (Ψ : RadSp k r z z' π π')
    (F : Fn k r (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ DomR k r z z')
    (hF : ∀ y ∈ Glev k r (Fin.last r) ∩ Qx8.Dp k r z z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 y = F x.1 y) :
    tL k r z z' (Fin.last r) Y a b ((Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1) x.2 =
      tL k r z z' (Fin.last r) Y a b (F x.1) x.2 := by
  have hs := Qx8.slice_smooth Ψ.2 hx.1
  exact (transfer_linear_local _ k r z z' (Fin.last r) (Qx8.Dp k r z z') Y a b _ _ 0 (Qx8.Dp_open k r z z') hs
    (Qx8.smoothLev_congr (Qx8.Dp_open k r z z') hs (fun y hy => (hF y hy).symm)) x.2
    ⟨hx.2.1, hx.2.2⟩).2 hF

end RhRPf

open RhRPf in
theorem spectral_right_rho_action : RDSRhR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨_, _, hL, hQQ, -⟩ := hD
  refine ⟨M.sgn P l0, ?_⟩
  intro J hJ Φ hΦ x hx
  have eT : L.Tprod Y = Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y P.r := by
    rw [Formalism.FourierDecayAlt.P.TLB.rma_pref_take, ← Formalism.FourierDecayAlt.P.TLB.tprod_take_all]
  have hch := PBN.radSide_chain X L hL Y P.r le_rfl

  have hA : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Ar Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vAB P.r Y P.r) 0) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    have h1 := (hch Φ (x.1, y) hxy).1
    rw [← eT] at h1
    rw [R.LevelData.Ar, h1]
    simp only [crd, Q.cmp, if_true]
    exact (PBN.vAB_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).1
  have hB : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Br Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vAB P.r Y P.r) 1) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    have h1 := (hch Φ (x.1, y) hxy).2
    rw [← eT] at h1
    rw [R.LevelData.Br, h1]
    simp only [crd, Q.cmp, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact (PBN.vAB_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).2
  have e1 : (((RhR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (((L.Drb).1 ((st.QQ Y 1 0).1 ((L.Ar Y).1 Φ) + (st.QQ Y 1 1).1 ((L.Br Y).1 Φ)) :
        RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, drb_apply X L hL, st_fst X st l0 hQQ, st_fst X st l0 hQQ]
  simp only [CutMP.dMul, CutMP.rhGrp, Submodule.coe_add, Pi.add_apply, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, QL, grp]
  rw [X.t_apply Y 1 0 _ x hx, X.t_apply Y 1 1 _ x hx,
    t_slice_congr X Y 1 0 _ _ x hx hA, t_slice_congr X Y 1 1 _ _ x hx hB]
  simp only [smul_add, smul_comm (CutMP.drbF P.r x.1) (M.sgn P l0)]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrpFinal
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSNicePoly
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrp
open MeasureTheory
open scoped Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSNicePoly : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ →
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), NiceAll D F → NiceAll D (B.opApply Θ F) ∧ NiceAll D (B.opAdj Θ F)

section swap

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end swap

theorem opProp1_of_poly (hN : RDSNicePoly) {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq} (hP : CutMP.PolyOp o κ Θ)
    (hC : B.Commutes D (B.GPos D) Θ) : OpProp1 D Θ := by
  obtain ⟨hS, hG, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hP
  refine ⟨hS _, hC, fun ε _ => ⟨κ, Nat.cast_nonneg _, fun T hT => ?_⟩, fun F hF => hN k r Wp Wq D o κ Θ hP F hF⟩
  obtain ⟨-, -, hb⟩ := hG κ le_rfl T hT
  obtain ⟨C₁, hC₁⟩ := hb (B.opOrder Θ + 5)
  exact ⟨C₁, fun u v hu hv hl g hg _ => hC₁ u v hu hv hl g hg⟩

section ffl

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem ffl_mono {D₁ D₂ : Set (Q.Mx k r)} (h : ∀ g ∈ Q.Glev k r 0, g ∈ D₂ → g ∈ D₁) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r z z' π π' 0 D₁) : J ∈ Q.FFl k r z z' π π' 0 D₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨fun g₀ hg₀ => h1 g₀ ⟨hg₀.1, h g₀ hg₀.1 hg₀.2⟩, fun g hg n hn => h2 g ⟨hg.1, h g hg.1 hg.2⟩ n hn,
    fun g hg n hn => h3 g ⟨hg.1, h g hg.1 hg.2⟩ n hn, fun g hg u hu u' hu' => h4 g ⟨hg.1, h g hg.1 hg.2⟩ u hu u' hu'⟩

end ffl

theorem rDSOpRGrp_of_nice (hN : RDSNicePoly) : RDSOpRGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadP_of_steps CutMP.residue_first_move_holds CutMP.residue_second_move_holds k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.ri_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_positive_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

theorem rDSOpRvGrp_of_nice (hN : RDSNicePoly) : RDSOpRvGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadM_of_parts CutMP.mirror_residue_beta_holds CutMP.mirror_residue_top_holds CutMP.GrpMA.mirror_residue_first_move
    CutMP.mirror_residue_second_move (CutMP.jDRvConseq_of CutMP.mirror_residue_continuity) k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.rim_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rvhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_minus_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Formalism.FourierDecayAlt.P.CutSE
end
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_nice_polynomial : RDSNicePoly := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF
  obtain ⟨-, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd hgO (not_lt.2 (hFs g hg hne))
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
end
end

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_right_group_action : RDSOpRGrp := rDSOpRGrp_of_nice spectral_nice_polynomial

theorem spectral_adjoint_right_group : RDSOpRvGrp := rDSOpRvGrp_of_nice spectral_nice_polynomial

end Formalism.FourierDecayAlt.P.CutSE
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhvR
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace RhvRPf

open RhRPf

theorem pbOp_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem vABs_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
      ∀ c ∈ OmX r, (vABs r Y i).1 f₁ c = (vABs r Y i).1 f₂ c ∧ (vABs r Y i).2 f₁ c = (vABs r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    by_cases hi : i < r
    · simp only [vABs, dif_pos hi]
      have hsub : ∀ c' ∈ OmX r, (Y • f₁ - pbOp ⟨i, hi⟩ f₁) c' = (Y • f₂ - pbOp ⟨i, hi⟩ f₂) c' := by
        intro c' hc'
        simp only [Pi.sub_apply, Pi.smul_apply]
        rw [h c' hc', pbOp_loc _ h hc']
      have hcb : ∀ c' ∈ OmX r, cbOp ⟨i, hi⟩ f₁ c' = cbOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbOp]
        rw [h c' hc']
      have hcbi : ∀ c' ∈ OmX r, cbiOp ⟨i, hi⟩ f₁ c' = cbiOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbiOp]
        rw [h c' hc']
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply]
        rw [(vABs_loc Y i _ _ hsub c hc).1, (vABs_loc Y i _ _ hcb c hc).2]
      · exact (vABs_loc Y i _ _ hcbi c hc).1
    · simp only [vABs, dif_neg hi]
      exact vABs_loc Y i f₁ f₂ h c hc

def rowP {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) A :=
  ((List.ofFn fun l => (L.Tvl Y l)ᵀ).take n).prod

theorem partialProduct_succ {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) (h : n < r) :
    rowP L Y (n + 1) = rowP L Y n * (L.Tvl Y ⟨n, h⟩)ᵀ := by
  unfold rowP
  rw [List.take_add_one, List.prod_append]
  have e : (List.ofFn fun l => (L.Tvl Y l)ᵀ)[n]? = some ((L.Tvl Y ⟨n, h⟩)ᵀ) := by simp [h]
  rw [e]
  simp

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rowSide_chain (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) :
    ∀ n, n ≤ r → ∀ (Ψ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (((rowP L Y n 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).1 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
        (((rowP L Y n 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).2 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2
  | 0, _, Ψ, x, _ => by
    have e : rowP L Y 0 = 1 := by simp [rowP]
    rw [e]
    refine ⟨rfl, ?_⟩
    simp [vABs, crd]
    rfl
  | n + 1, hn, Ψ, x, hx => by
    have h : n < r := by omega
    have ih := rowSide_chain X L hL Y n (by omega)
    have ev : vABs (E := Wq →L[ℂ] Wp) r Y (n + 1) =
        (fun f => (vABs r Y n).1 (Y • f - pbOp ⟨n, h⟩ f) - (vABs r Y n).2 (cbOp ⟨n, h⟩ f),
          fun f => (vABs r Y n).1 (cbiOp ⟨n, h⟩ f)) := by
      show (if h : n < r then _ else _) = _
      rw [dif_pos h]
    have e00 : rowP L Y (n + 1) 0 0 =
        rowP L Y n 0 0 * (algebraMap ℂ _ Y - L.pb ⟨n, h⟩) + rowP L Y n 0 1 * (-L.cb ⟨n, h⟩) := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have e01 : rowP L Y (n + 1) 0 1 = rowP L Y n 0 0 * L.cbi ⟨n, h⟩ := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have hpb : JCx2.rma_fst _ (L.pb ⟨n, h⟩) = X.op ⟨n, h⟩ 3 := by rw [hL.2.1]; rfl
    have hcb : JCx2.rma_fst _ (L.cb ⟨n, h⟩) = X.op ⟨n, h⟩ 4 := by rw [hL.2.2.2.2.1]; rfl
    have hcbi : (L.cbi ⟨n, h⟩).1 = X.op ⟨n, h⟩ 5 := by rw [hL.2.2.2.2.2.1]; rfl
    refine ⟨?_, ?_⟩
    · have h1 : (((rowP L Y (n + 1) 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (Y • Ψ - X.op ⟨n, h⟩ 3 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 -
            (((rowP L Y n 0 1).1 (X.op ⟨n, h⟩ 4 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        change (JCx2.rma_fst _ (rowP L Y (n + 1) 0 0) Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
        rw [e00]
        simp only [map_add, map_mul, map_sub, map_neg, AlgHom.commutes, LinearMap.add_apply,
          LinearMap.sub_apply, LinearMap.neg_apply, mul_apply_eq_comp, Module.algebraMap_end_apply,
          hpb, hcb, ← sub_eq_add_neg, Submodule.coe_sub, Pi.sub_apply]
        rfl
      rw [h1, (ih _ x hx).1, (ih _ x hx).2, ev]
      simp only [Submodule.coe_sub, Submodule.coe_smul, X.op_apply]
      rfl
    · have h1 : (((rowP L Y (n + 1) 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (X.op ⟨n, h⟩ 5 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        rw [e01, fst_mul_apply, hcbi]
      rw [h1, (ih _ x hx).1, ev]
      simp only [X.op_apply]
      rfl

end RhvRPf

open RhRPf RhvRPf in
theorem spectral_adjoint_rho_action : RDSRhvR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨_, _, hL, hQQ, -⟩ := hD
  refine ⟨M.sgn P l0, ?_⟩
  intro J hJ Φ hΦ x hx
  have hT : (L.Tvprod Y)ᵀ = rowP L Y P.r := by
    rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose L Y, rowP, List.take_of_length_le (by simp)]
  have eA : L.Avr Y = rowP L Y P.r 0 0 := by rw [← hT]; rfl
  have eB : L.Bvr Y = rowP L Y P.r 0 1 := by rw [← hT]; rfl
  have hch := rowSide_chain X L hL Y P.r le_rfl
  have hA : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Avr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 0) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eA, (hch Φ (x.1, y) hxy).1]
    simp only [crd, Q.cmp, if_true]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).1
  have hB : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Bvr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 1) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eB, (hch Φ (x.1, y) hxy).2]
    simp only [crd, Q.cmp, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).2
  have e1 : (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (((L.Dr).1 ((st.QQ Y 0 1).1 ((L.Avr Y).1 Φ) + (st.QQ Y 1 1).1 ((L.Bvr Y).1 Φ)) :
        RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, dr_apply X L hL, st_fst X st l0 hQQ, st_fst X st l0 hQQ]
  simp only [CutMP.dMul, CutMP.rhvGrp, Submodule.coe_add, Pi.add_apply, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, QL, grp]
  rw [X.t_apply Y 0 1 _ x hx, X.t_apply Y 1 1 _ x hx,
    t_slice_congr X Y 0 1 _ _ x hx hA, t_slice_congr X Y 1 1 _ _ x hx hB]
  simp only [smul_add, smul_comm (CutMP.drF P.r x.1) (M.sgn P l0)]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpX
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace OpX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.AdmissibleLieWords PI.UnitaryCorollaryDerivatives.CRH

section ubl

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ckOn_of_contDiff {m : ℕ∞} {f : B.Mat k r → E} (hf : ContDiff ℝ ∞ f) : B.CkOn m (B.GV k r) f :=
  sCkOn_mono le_top fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩

theorem ubl_add' {f₁ f₂ : B.Mat k r → E} {S : Set (B.Mat k r)} (hSG : S ⊆ B.GV k r) {n e γ : ℕ}
    (h₁ : UBL f₁ S n e γ) (h₂ : UBL f₂ S n e γ) : UBL (fun g => f₁ g + f₂ g) S n e γ := by
  obtain ⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩ := h₂
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
    obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
    have hlie := admissible_word_mem_lie hw
    have hG := hSG hg
    have e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g :=
      Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG
        ⟨hgV, hgW⟩
    rw [e0, Dw_add hlie (ckOn_of_contDiff ha) (ckOn_of_contDiff hb) g hG,
      ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]
    have b1 := hb₁ w hw g hg
    have b2 := hb₂ w hw g hg
    calc ‖Dw w f₁ g + Dw w f₂ g‖ ≤ ‖Dw w f₁ g‖ + ‖Dw w f₂ g‖ := norm_add_le _ _
      _ ≤ C₁ * B.gN g ^ (e + γ * w.length) + C₂ * B.gN g ^ (e + γ * w.length) := add_le_add b1 b2
      _ = (C₁ + C₂) * B.gN g ^ (e + γ * w.length) := by ring
  · obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
    obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
    exact ⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hG' hg' => by
      simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]⟩

theorem ubl_smulC (c : ℂ) {f : B.Mat k r → E} {S : Set (B.Mat k r)} (hSG : S ⊆ B.GV k r) {n e γ : ℕ}
    (h : UBL f S n e γ) : UBL (fun g => c • f g) S n e γ := by
  have := ubl_clm ((c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) hSG h
  simpa using this

theorem ubl_sumRange {f : ℕ → B.Mat k r → E} {S : Set (B.Mat k r)} (hSG : S ⊆ B.GV k r) {n e γ : ℕ}
    (h : ∀ i, UBL (f i) S n e γ) : ∀ N : ℕ, UBL (fun g => ∑ i ∈ Finset.range N, f i g) S n e γ
  | 0 => by
    simpa using ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl
  | N + 1 => by
    have := ubl_add' hSG (ubl_sumRange hSG h N) (h N)
    simpa [Finset.sum_range_succ] using this

end ubl

section radial

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def OpAt (x : (Fin r → ℂ) × Mx k r) (T : Module.End ℂ (RadSp k r z z' π π'))
    (M : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : RadSp k r z z' π π', (T Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = M ((Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2)

theorem opAt_aeval {x : (Fin r → ℂ) × Mx k r} {a : Pr (RadSp k r z z' π π')}
    {M : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)} (h : OpAt x a.1 M) (p : Polynomial ℂ) :
    OpAt x (Polynomial.aeval a p).1 (Polynomial.aeval M p) := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro Φ
    rw [Polynomial.aeval_C, Polynomial.aeval_C]
    show ((c • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
    simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq =>
    intro Φ
    rw [map_add (f := _), map_add (f := _)]
    show (((Polynomial.aeval a p).1 Φ + (Polynomial.aeval a q).1 Φ : RadSp k r z z' π π') :
      Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply]
    rw [hp Φ, hq Φ]
  | monomial n c hn =>
    intro Φ
    have e1 : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    have e2 : Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n) * a := by
      simp only [map_mul, Polynomial.aeval_X]
    have e3 : Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ n) * M := by
      simp only [map_mul, Polynomial.aeval_X]
    rw [e1, e2, e3]
    show ((Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n)).1 (a.1 Φ) : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
    rw [hn (a.1 Φ), h Φ]
    rfl

end radial

section equiv

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem aeval_intertwine (φ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (hφa : ∀ A B, φ (A + B) = φ A + φ B)
    (hφs : ∀ (c : ℂ) A, φ (c • A) = c • φ A) {M N : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)}
    (h : ∀ A, M (φ A) = φ (N A)) (p : Polynomial ℂ) :
    ∀ A, Polynomial.aeval M p (φ A) = φ (Polynomial.aeval N p A) := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro A
    simp [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hφs]
  | add p q hp hq =>
    intro A
    simp only [map_add (f := _), ContinuousLinearMap.add_apply, hp, hq, hφa]
  | monomial n c hn =>
    intro A
    have e1 : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    have e3 : ∀ K : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp), Polynomial.aeval K (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval K (Polynomial.C c * Polynomial.X ^ n) * K := fun K => by
      simp only [map_mul, Polynomial.aeval_X]
    rw [e1, e3 M, e3 N, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, h, hn]

end equiv

end OpX

section main

open OpX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.AdmissibleLieWords PI.UnitaryCorollaryDerivatives.CRH

theorem spectral_operator_X : RDSOpX := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYi
  subst hz hz' hπ hπ'
  obtain ⟨B0, -, hxf⟩ := x_fibre_of_parts big_cell_values omega_polynomial_facts capelli_vector_frame
    capelli_vector_equivariance Wp Wq P D X
  obtain ⟨hfb, hfeq, hfrad⟩ := hxf Y
  obtain ⟨-, -, hpoly⟩ := actual_algebra_facts Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD
  obtain ⟨q, hq⟩ := hpoly Y hYi
  obtain ⟨-, -, hL, hQQ, -, -, -, hst⟩ := hD
  set s : ℂ := M.sgn P l0 with hs
  set xf : B.Mat P.k P.r → C6.EndH Wp Wq := TL.xFib D B0 (Y + ((P.k : ℂ) - 2) / 2) with hxfdef
  set cf : B.Mat P.k P.r → C6.EndH Wp Wq := fun g =>
    ((Gf P.k P.r D.z D.z' g : ℝ) : ℂ)⁻¹ • Polynomial.aeval (s • xf g) q with hcf
  let T0 : B.DTerm P.k P.r Wp Wq :=
    { coef := cf
      coefAdj := fun g => HilbertSchmidtVectorization.adjH (cf g)
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun g A B' => HilbertSchmidtVectorization.adjH_spec (cf g) A B' }

  let fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq := fun _ => xf
  have hfib : ∀ j, C6.FibBound D (fib j) := fun _ => hfb
  have hP1 : U.IsPolyDeg 0 (fun _ : B.Mat P.k P.r => (1 : ℂ)) := ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
  have hsum : cf = fun g => ∑ i ∈ Finset.range (q.natDegree + 1), (q.coeff i * s ^ i) •
      (((fun _ : B.Mat P.k P.r => (1 : ℂ)) g * C6.monoM D 0 0 1 g) •
        C6.Epart fib (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) g) := by
    funext g
    simp only [hcf]
    rw [Polynomial.aeval_eq_sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : C6.monoM D 0 0 1 g = (((Gf P.k P.r D.z D.z' g : ℝ) : ℂ))⁻¹ := by simp [C6.monoM]
    have he : C6.Epart fib (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) g = xf g ^ i := by
      simp [C6.Epart, B.Rw, List.map_replicate, List.prod_replicate, fib]
    rw [hm, he, smul_pow, smul_smul, smul_smul, smul_smul, one_mul]
    congr 1
    ring
  have hU : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      UBL cf {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1)) := by
    intro ε hε n
    set S : Set (B.Mat P.k P.r) := {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} with hSdef
    have hSG : S ⊆ B.GV P.k P.r := fun g hg => hg.1
    set c₀ : ℝ := min ε (ε ^ 2) with hc₀
    have hc₀p : 0 < c₀ := lt_min hε (by positivity)
    have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (P.r + 2))) ∨ l = Fin.last (P.r + 1)) →
        c₀ ≤ Complex.normSq (Dmin P.k P.r D.z D.z' g l) := by
      intro g hg l hl
      rcases hl with hl | rfl
      · simp at hl
      · have := Formalism.FourierDecayAlt.P.gram_function_last_minor P.k P.r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg.2
        exact (min_le_left _ _).trans this
    have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf P.k P.r D.z D.z' g : ℝ) : ℂ) := by
      intro g hg
      rw [Complex.normSq_ofReal]
      have h1 := hg.2
      have : ε ^ 2 ≤ Gf P.k P.r D.z D.z' g * Gf P.k P.r D.z D.z' g := by nlinarith
      exact (min_le_right _ _).trans this
    rw [hsum]
    refine ubl_sumRange hSG (fun i => ubl_smulC _ hSG ?_) _
    have hes : ∀ e ∈ List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r))), ∀ X ∈ e.2, B.inLie P.k P.r X := by
      intro e he X hX
      rw [List.mem_replicate] at he
      rw [he.2] at hX
      simp at hX
    have h := Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_coefP D fib hfib ∅ (fun _ => (1 : ℂ)) (0 : Fin (P.r + 2) → ℕ)
      (0 : Fin (P.r + 2) → ℕ) 1 (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) hP1
      (fun _ _ _ => ⟨rfl, rfl⟩) hes hε (fun g hg => hg) hc₀p hSD hSGf n
    exact ubl_mono hSG h (by simp) le_rfl
  have hUa : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      UBL (fun g => HilbertSchmidtVectorization.adjH (cf g)) {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1)) :=
    fun ε hε n => ubl_clm HilbertSchmidtVectorization.adjR
      (S := {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g})
      (fun g hg => hg.1) (hU ε hε n)
  have hck : ∀ f : B.Mat P.k P.r → C6.EndH Wp Wq,
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, UBL f {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1))) →
      B.CkOn ⊤ (B.GPos D) f := by
    intro f hf g₀ hg₀
    obtain ⟨-, hl⟩ := hf _ hg₀.2 0
    obtain ⟨f', hf', V, hV, hgV, hff⟩ := hl g₀ ⟨hg₀.1, le_rfl⟩
    exact ⟨V, f', hV, hgV, hf'.contDiffOn, fun g hg hgG => hff g hgG hg⟩
  refine ⟨T0, ⟨rfl, hck cf hU, hck _ hUa, ?_, ?_⟩, ?_⟩
  ·
    intro p hp g hg A
    have hgd : g ∈ C6.domL D ∅ := ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
    set φ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp) := fun J =>
      (D.π (Matrix.of p.1.1)).comp (J.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hφ
    have hφa : ∀ A B', φ (A + B') = φ A + φ B' := fun A B' => by
      simp only [hφ, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    have hφs : ∀ (c : ℂ) A, φ (c • A) = c • φ A := fun c A => by
      simp only [hφ, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    have hint : ∀ J, (s • xf g) (φ J) = φ ((s • xf (B.sgs p g)) J) := fun J => by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hφs]
      exact congrArg (s • ·) (hfeq p hp g hgd J)
    have h2 := aeval_intertwine φ hφa hφs hint q A
    show cf g (φ A) = φ (cf (B.sgs p g) A)
    simp only [hcf, ContinuousLinearMap.smul_apply]
    rw [h2, hφs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g]
  ·
    intro ε hε m
    obtain ⟨⟨C1, hC1, hb1⟩, -⟩ := hU ε hε m
    obtain ⟨⟨C2, hC2, hb2⟩, -⟩ := hUa ε hε m
    refine ⟨max C1 C2, ((3 * (P.r + 1) * m : ℕ) : ℝ), by positivity, fun u v hu hv hl g hg hgε => ?_⟩
    have hw : admitted m (wL u ++ wR v) := ⟨u, v, hu, hv, hl, rfl⟩
    have hS : g ∈ {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} := ⟨hg, hgε⟩
    have hg1 := gN_ge_one hg
    have hpow : B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) ≤ B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      apply pow_le_pow_right₀ hg1
      rw [len_LR]
      have := Nat.mul_le_mul_left (3 * (P.r + 1)) hl
      omega
    have hpos : 0 ≤ B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) := by positivity
    constructor
    · show ‖B.dLR u v cf g‖ ≤ _
      rw [dLR_eq]
      calc _ ≤ C1 * B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) := hb1 _ hw g hS
        _ ≤ max C1 C2 * B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ) :=
          mul_le_mul (le_max_left _ _) hpow hpos (le_trans hC1 (le_max_left _ _))
    · show ‖B.dLR u v (fun g => HilbertSchmidtVectorization.adjH (cf g)) g‖ ≤ _
      rw [dLR_eq]
      calc _ ≤ C2 * B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) := hb2 _ hw g hS
        _ ≤ max C1 C2 * B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ) :=
          mul_le_mul (le_max_right _ _) hpow hpos (le_trans hC2 (le_max_right _ _))
  ·
    intro Ψ x hx
    set g : B.Mat P.k P.r := wCell P.k P.r (Fin.last P.r) x.1 * x.2 with hgdef
    have hcell := big_cell_values P.k P.r Wp Wq D
    have hGGpos : (0 : ℝ) < GGl P.k P.r D.z D.z' x.2 := hx.2.2
    have hGGi : Formalism.FourierDecayAlt.P.TLB.MulAt x L.GGi.1 ((GGl P.k P.r D.z D.z' x.2 : ℂ))⁻¹ := by
      rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact Formalism.FourierDecayAlt.P.TLB.act_fn X x hx 5
    have hDri : Formalism.FourierDecayAlt.P.TLB.MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) :=
      Formalism.FourierDecayAlt.P.TLB.mulAt_ofFn L.ci _ fun l => Formalism.FourierDecayAlt.P.TLB.act_ci X L hL x l
    have hDrbi : Formalism.FourierDecayAlt.P.TLB.MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹) :=
      Formalism.FourierDecayAlt.P.TLB.mulAt_ofFn L.cbi _ fun l => Formalism.FourierDecayAlt.P.TLB.act_cbi X L hL x l
    have hGi : Formalism.FourierDecayAlt.P.TLB.MulAt x (GiR L).1 (((Gf P.k P.r D.z D.z' g : ℝ) : ℂ))⁻¹ := by
      rw [hgdef, (hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv,
        ← Finset.prod_inv_distrib, map_prod, ← Finset.prod_inv_distrib]
      exact Formalism.FourierDecayAlt.P.TLB.mulAt_mul (Formalism.FourierDecayAlt.P.TLB.mulAt_mul hDri hDrbi) hGGi
    have hX : OpAt x (st.x Y).1 (s • xf g) := by
      intro Φ
      have e1 : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hst.tau Y, ← mul_assoc, L.GGi_GG, one_mul]
      rw [e1, hQQ Y]
      show (L.GGi.1 ((s • X.QQ Y 1 1).1 Φ) : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
      rw [hGGi]
      have e3 : (s • X.QQ Y 1 1).1 Φ = s • X.t Y 1 1 Φ := by
        rw [Algebra.smul_def]
        rfl
      rw [e3, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hfrad Φ x hx, ContinuousLinearMap.smul_apply,
        smul_smul, smul_smul]
      have hne : ((GGl P.k P.r D.z D.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hGGpos.ne'
      congr 1
      field_simp
    have hXi : OpAt x (st.xi Y).1 (Polynomial.aeval (s • xf g) q) := by
      rw [hq]; exact opAt_aeval hX q
    show (((GiR L).1 ((st.xi Y).1 Ψ) : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      cf g ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
    rw [hGi, hXi]
    rfl

end main

end Formalism.FourierDecayAlt.P.CutSE
end
end

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_R : RDSOpR := rDSOpR_of_parts spectral_right_group_action spectral_operator_X spectral_right_rho_action spectral_composition_zero

theorem spectral_operator_R_adjoint : RDSOpRv := rDSOpRv_of_parts spectral_adjoint_right_group spectral_operator_X spectral_adjoint_rho_action spectral_composition_zero

theorem actual_compact_theorem : Formalism.FourierDecayAlt.P5.ThmPActualCpt := thmPActualCpt_of_R spectral_operator_R spectral_operator_R_adjoint

end Formalism.FourierDecayAlt.P.CutSE

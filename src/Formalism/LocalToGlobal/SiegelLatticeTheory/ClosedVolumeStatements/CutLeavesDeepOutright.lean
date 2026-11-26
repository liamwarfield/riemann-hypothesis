module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutDeep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsCompactIntLowSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsLoOfIntLow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobPOfInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIF

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCut
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabApprox
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.P2MemZ2OfMemZ2
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Gen

theorem map3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (A B C : Matrix (Fin n) (Fin n) R) :
    (A * B * C).map f = A.map f * B.map f * C.map f := by rw [Matrix.map_mul, Matrix.map_mul]

theorem split_R {Fp : Type*} [Field Fp] (O : Subring Fp) {q : Fp} (hq : q ∈ O) {x₁ x₂ d : Fp} (hd : d ∈ O)
    (h1 : x₁ - d ∈ lat O q) (h2 : x₂ - d ∈ lat O q) : x₁ ∈ O ∧ x₂ ∈ O ∧ ∃ t ∈ O, x₁ - x₂ = q * t := by
  obtain ⟨y₁, hy₁, e₁⟩ := h1
  obtain ⟨y₂, hy₂, e₂⟩ := h2
  have f₁ : x₁ = d + q * y₁ := by rw [← e₁]; ring
  have f₂ : x₂ = d + q * y₂ := by rw [← e₂]; ring
  refine ⟨?_, ?_, y₁ - y₂, O.sub_mem hy₁ hy₂, by rw [f₁, f₂]; ring⟩
  · rw [f₁]; exact O.add_mem hd (O.mul_mem hq hy₁)
  · rw [f₂]; exact O.add_mem hd (O.mul_mem hq hy₂)

end Gen

section BadG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem firstProj_mem_integers (p : PlF D) (e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp)
    {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) : p1 e y ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at hy
  exact Formalism.L2.SG.Pf.LocModel.LM.DeltaC.mem_of_isIntegral_fp (D.s.atP p)
    (hy.map (((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp e.toAlgHom).restrictScalars
      𝒪[(D.s.atP p).Fp]))

theorem p2_mem_Z2_of_mem_Z2 (p : PlF D) (e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp)
    {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) : p2 e y ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at hy
  exact Formalism.L2.SG.Pf.LocModel.LM.DeltaC.mem_of_isIntegral_fp (D.s.atP p)
    (hy.map (((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).comp e.toAlgHom).restrictScalars
      𝒪[(D.s.atP p).Fp]))

theorem map_stab {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} {a Y b : Matrix (Fin n) (Fin n) R}
    (h : a * Y * b = Y) : a.map f * Y.map f * b.map f = Y.map f := by rw [← map3, h]

set_option maxHeartbeats 1000000 in
theorem target_G (u u' : D.what₂.Word) (p : PlF D) {g : Loc.SplitG (Zd.M p).L} (hM : (Zd.M p).split = some g)
    (w : Point D.host.E (D.R.rS + 1)) {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hR : (D.s.atP p).split with _ | sg <;> simp only [hM, hR] at hAg
  obtain ⟨hge, hgq⟩ := hAg
  have hσ : ∀ a, fσ w (fσ w a) = a := fσ_fσ w
  have hν : ∀ a : Fin (D.R.rS + 1), pv w.1 a ≠ 0 := fun a => pv_ne' w a
  have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
    have := sg.q_irr.ne_zero
    exact_mod_cast this
  have hqO : (sg.q : (D.s.atP p).Fp) ∈ 𝒪[(D.s.atP p).Fp] := sg.q.2
  have hcv := cf_cfi Zd p
  obtain ⟨hli, -, hll'⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨hρi, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  have hkL : IsLo (l⁻¹ * locL Zd p A₀ B₀) := isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p hA₀ hB₀)
  have hkR : IsUp (locR Zd p A₀ B₀ * ρ⁻¹) := isUp_mul (locR_up Zd p hA₀ hB₀) (isUp_of_intUp Zd hρi)
  have hk := key_stab Zd p hl hρ h
  have hY1 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map ((p1 sg.e).comp (D.s.atP p).ιE) *
          Matrix.diagonal (cf Zd p)) -
      (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
    rw [zz1' Zd p sg hR g hM hge hgq u u' Z₁, hZ, ptMat_mono']
  have hY2 : Sg (D.s.atP p).Fp D.R.rS * ((CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p).map
        (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Matrix.diagonal (cf Zd p)) -
      ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
    rw [zz2' Zd p sg hR g hM hge hgq u u' Z₁, sign_transpose_twisted, ← sg_map ((p2 sg.e).comp (D.s.atP p).ιE), ← Matrix.map_mul, hZ,
      ptMat_mono']
  have hs1 : IsUnit ((sg.q : (D.s.atP p).Fp)⁻¹) := IsUnit.mk0 _ (inv_ne_zero hq0)
  have hs2 : IsUnit (-(sg.q : (D.s.atP p).Fp)⁻¹) := IsUnit.mk0 _ (neg_ne_zero.2 (inv_ne_zero hq0))
  have hk1 := map_stab (p1 sg.e) hk
  rw [hY1] at hk1
  have hk2 := theta_stab (map_stab (p2 sg.e) hk)
  rw [hY2] at hk2
  obtain ⟨hT1lo, hT1pat, -⟩ := comp_target ((p1 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs1
    (isLo_map _ hkL) (isUp_map _ hkR) hk1
  obtain ⟨hT2lo, hT2pat, -⟩ := comp_target ((p2 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs2
    (theta_lo (isUp_map _ hkR)) (theta_up (isLo_map _ hkL)) hk2
  obtain ⟨t, ht0, htO, hb⟩ := bnd_mats (K := (D.s.atP p).Fp) 𝒪[(D.s.atP p).Fp] (fun s hs => by simpa using hs)
    (fun x => by
      obtain ⟨s, h0, hO, hx⟩ := bounded_Fp (L := D.s.atP p) x
      exact ⟨s, h0, hO, by simpa using hx⟩)
    ![cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁, cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁,
      cQ ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) U₁, cQ' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) U₁,
      Matrix.of fun i _ => ((p1 sg.e).comp (D.s.atP p).ιE) (pv w.1 i),
      Matrix.of fun i _ => ((p1 sg.e).comp (D.s.atP p).ιE) (pv w.1 i)⁻¹,
      cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ * (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) *
        cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁,
      cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁, cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁,
      cQ ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) U₁, cQ' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) U₁,
      Matrix.of fun i _ => ((p2 sg.e).comp (D.s.atP p).ιE) (pv w.1 i),
      Matrix.of fun i _ => ((p2 sg.e).comp (D.s.atP p).ιE) (pv w.1 i)⁻¹,
      cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ *
        (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁]
  refine ⟨glue sg.e
      (cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ * (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) *
        cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹
      (cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ *
        (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹,
    t * (t * (t * (t * (t * (sg.q : (D.s.atP p).Fp))))), by simp [ht0, hq0], ?_⟩
  intro X' hX' hpat hfree
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ hZ hX' hpat
  have hab := key_stab Zd p hl hρ ((corr_move Zd u u' p hA₀ hB₀ hgX hgY hst).trans h)
  have ha : IsLo (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) :=
    isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀))
  have hb' : IsUp (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) :=
    isUp_mul (locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)) (isUp_of_intUp Zd hρi)
  have hab1 := map_stab (p1 sg.e) hab
  rw [hY1] at hab1
  have hab2 := theta_stab (map_stab (p2 sg.e) hab)
  rw [hY2] at hab2
  have haX1 : (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)).map (p1 sg.e) =
      (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) * (Matrix.diagonal (cf Zd p) *
        (L₁ * X' * L₁⁻¹).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) := by
    rw [Matrix.map_mul (L := l⁻¹) (M := locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)),
      Matrix.map_mul (L := l⁻¹) (M := locL Zd p A₀ B₀), leftLocal_firstProj Zd p hM hge, leftLocal_firstProj Zd p hM hge, gX,
      Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (Matrix.diagonal (cfi Zd p)) (Matrix.diagonal (cf Zd p)), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have haX2 : Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹).map
        (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Matrix.diagonal (cf Zd p) * (L₁ * X' * L₁⁻¹).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Matrix.diagonal (cfi Zd p)) := by
    simp only [Matrix.map_mul (L := locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)),
      Matrix.map_mul (L := locR Zd p A₀ B₀), theta_mul]
    simp only [rightLocal_secondProj Zd p hM hge]
    simp only [theta_move, gX, Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (Matrix.diagonal (cfi Zd p)) (Matrix.diagonal (cf Zd p)), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have hG1 : EntIn (lat 𝒪[(D.s.atP p).Fp] (t * (t * (t * (t * (t * (sg.q : (D.s.atP p).Fp)))))))
      (X'.map ((p1 sg.e).comp (D.s.atP p).ιE) -
        (cP' ((p1 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ * (l⁻¹ * locL Zd p A₀ B₀).map (p1 sg.e) *
          cP ((p1 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹) := by
    refine ent_free _ hσ hX' hpat hT1lo hT1pat fun i j hf => ?_
    refine Exists.elim (hfree i j hf) fun y hye => ?_
    refine ⟨p1 sg.e y, firstProj_mem_integers p sg.e hye.1, ?_⟩
    have e1 := congrArg (p1 sg.e) hye.2
    simp only [map_sub, map_mul, fst_proj_algebraMap, glue, Matrix.of_apply, fst_proj_symm] at e1
    exact e1
  have hG2 : EntIn (lat 𝒪[(D.s.atP p).Fp] (t * (t * (t * (t * (t * (sg.q : (D.s.atP p).Fp)))))))
      (X'.map ((p2 sg.e).comp (D.s.atP p).ιE) -
        (cP' ((p2 sg.e).comp (D.s.atP p).ιE) (cfi Zd p) L₁ *
          (Sg (D.s.atP p).Fp D.R.rS * ((locR Zd p A₀ B₀ * ρ⁻¹).map (p2 sg.e)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) *
          cP ((p2 sg.e).comp (D.s.atP p).ιE) (cf Zd p) L₁)⁻¹) := by
    refine ent_free _ hσ hX' hpat hT2lo hT2pat fun i j hf => ?_
    refine Exists.elim (hfree i j hf) fun y hye => ?_
    refine ⟨p2 sg.e y, p2_mem_Z2_of_mem_Z2 p sg.e hye.1, ?_⟩
    have e1 := congrArg (p2 sg.e) hye.2
    simp only [map_sub, map_mul, snd_proj_algebraMap, glue, Matrix.of_apply, snd_proj_symm] at e1
    exact e1
  have hc1 := comp_main ((p1 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs1 (isLo_map _ hkL) (isUp_map _ hkR) hk1
    (isLo_map _ ha) (isUp_map _ hb') hab1 haX1 htO hqO
    (fun a => by simpa using hb 4 a a) (fun a => by simpa using hb 5 a a)
    (fun i j => by simpa using hb 0 i j) (fun i j => by simpa using hb 1 i j)
    (fun i j => by simpa using hb 2 i j) (fun i j => by simpa using hb 3 i j)
    (fun i j => by simpa using hb 6 i j) hG1
  have hc2 := comp_main ((p2 sg.e).comp (D.s.atP p).ιE) hcv hL₁ hU₁ hσ hν hs2 (theta_lo (isUp_map _ hkR))
    (theta_up (isLo_map _ hkL)) hk2 (theta_lo (isUp_map _ hb')) (theta_up (isLo_map _ ha)) hab2 haX2 htO hqO
    (fun a => by simpa using hb 11 a a) (fun a => by simpa using hb 12 a a)
    (fun i j => by simpa using hb 7 i j) (fun i j => by simpa using hb 8 i j)
    (fun i j => by simpa using hb 9 i j) (fun i j => by simpa using hb 10 i j)
    (fun i j => by simpa using hb 13 i j) hG2
  have hA2 : EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp))
      ((l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)).map (p2 sg.e) - 1) := by
    have := ent_theta hc2.2
    rwa [theta_sub_one, theta_theta] at this
  have hB2 : EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp))
      ((locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹).map (p2 sg.e) - 1) := by
    have := ent_theta hc2.1
    rwa [theta_sub_one, theta_theta] at this
  have hmem : ∀ M : MatP D p, EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp)) (M.map (p1 sg.e) - 1) →
      EntIn (lat 𝒪[(D.s.atP p).Fp] (sg.q : (D.s.atP p).Fp)) (M.map (p2 sg.e) - 1) → ∀ i j, M i j ∈ (Zd.M p).R := by
    intro M h1 h2 i j
    have hd : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) i j ∈ 𝒪[(D.s.atP p).Fp] := by
      rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    have e1 := h1 i j
    have e2 := h2 i j
    rw [Matrix.sub_apply, Matrix.map_apply] at e1 e2
    obtain ⟨m1, m2, m3⟩ := split_R 𝒪[(D.s.atP p).Fp] hqO hd e1 e2
    refine mem_R_of (Zd.M p) g hM (M i j) (by rw [hge]; exact m1) (by rw [hge]; exact m2) ?_
    rw [hge, hgq]
    exact m3
  refine ⟨?_, ?_⟩
  · have e : locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        l * (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) := by
      rw [← Matrix.mul_assoc, hll', Matrix.one_mul]
    rw [e]
    exact ZsVolGrp.intLow_mul (Zd.M p) hl ⟨ha.1, ha.2, hmem _ hc1.1 hA2⟩
  · have e : locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) * ρ := by
      rw [Matrix.mul_assoc, (ZsVolGrp.intUp_inv (Zd.M p) hρ).2.1, Matrix.mul_one]
    rw [e]
    exact ZsVolGrp.intUp_mul (Zd.M p) ⟨hb'.1, fun a b hab => hb'.2 b a hab, hmem _ hc1.2 hB2⟩ hρ

end BadG

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntDiag
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section IntM

variable {K : Type*} [CommRing K] (I : Subring K) {n : ℕ}

theorem int_mul {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem (hA i k) (hB k j)

theorem int_diag {d : Fin n → K} (hd : ∀ a, d a ∈ I) : ∀ i j, Matrix.diagonal d i j ∈ I := by
  intro i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact I.zero_mem

end IntM

section Good

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem gY_int (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) {U₁ X' : PairVal.MatR D} (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O)
    (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) :
    ∀ i j, ((gY w U₁ X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
  have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hcm : ∀ i j, ((cOf (fσ w) (fun a => pv w.1 a) X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    simp only [Matrix.map_apply, cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hν' _) (hX _ _)) (hν _)
  have hci : ∀ i j, (((cOf (fσ w) (fun a => pv w.1 a) X')⁻¹).map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    rw [ZsVolGrp.inv_eq_adj (det_up' hc)]
    have e := RingHom.map_adjugate (D.s.atP p).ιE (cOf (fσ w) (fun a => pv w.1 a) X')
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at e
    rw [e]
    exact ZsVolGrp.adj_mem (D.s.atP p).O hcm i j
  simp only [gY, Matrix.map_mul]
  exact int_mul _ (int_mul _ hU' hci) hU

theorem good_at (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {L₁ U₁ A₀ B₀ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX' : IsLo X') (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0)
    (hcf : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O)
    (hcfi : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O)
    (hA : ∀ i j, (D.s.atP p).ιE (A₀ i j) ∈ (D.s.atP p).O) (hB : ∀ i j, (D.s.atP p).ιE (B₀ i j) ∈ (D.s.atP p).O)
    (hL : ∀ i j, (D.s.atP p).ιE (L₁ i j) ∈ (D.s.atP p).O) (hL' : ∀ i j, (D.s.atP p).ιE (L₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O) (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) : GoodAt Zd p w L₁ U₁ A₀ B₀ X' := by
  obtain ⟨hgX, hgY, -⟩ : IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧ True := by
    have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
    have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
    have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
    exact ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, trivial⟩
  have hgYi := gY_int p w hX' hpat hU hU' hν hν' hX
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  have hlo := locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  have hup := locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  refine ⟨⟨hlo.1, hlo.2, fun i j => ?_⟩, ⟨hup.1, fun a b hab => hup.2 b a hab, fun i j => ?_⟩⟩
  · rw [hR, locL_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcf) ?_) (int_diag _ hcfi) i j
    simp only [gX, Matrix.map_mul]
    exact int_mul _ hA (int_mul _ (int_mul _ hL hX) hL')
  · rw [hR, locR_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcfi) ?_) (int_diag _ hcf) i j
    rw [Matrix.map_mul]
    exact int_mul _ hgYi hB

end Good

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem locTarget (Zd : LocDat D) (u u' : D.what₂.Word) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  rcases hM : (Zd.M p).split with _ | g
  · exact target_L Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h
  · exact target_G Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h

theorem cf_int (Zd : LocDat D) (p : PlF D) (hδ1 : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hδ2 : (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) (hu1 : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) :
    (∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O) ∧
      ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O := by
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have e2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E)⁻¹) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))⁻¹) := by
    rw [← map_inv₀ (D.s.atP p).ιF, ← (D.s.atP p).compat, map_inv₀ (algebraMap D.host.F D.host.E),
      map_ratCast (algebraMap D.host.F D.host.E)]
  have hy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p) ∈ (D.s.atP p).O := by
    unfold yP
    rw [map_mul, ← e1]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ1) hu1
  have hyi : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p)⁻¹ ∈ (D.s.atP p).O := by
    unfold yP
    rw [mul_inv, map_mul, ← e2]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ2) hu2
  exact ⟨fun a => by unfold cf; rw [map_pow]; exact pow_mem hyi _,
    fun a => by unfold cfi; rw [map_pow]; exact pow_mem hy _⟩

theorem stabApprox (Zd : LocDat D) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.TupGlob.StabApprox Zd u u' := by
  intro w Z₁ A₀ B₀ hAt hA₀ hB₀ hloc
  obtain ⟨L₁, U₁, hL₁u, hU₁u, e₁⟩ := hAt
  have hL₁ : IsLo L₁ := isLo_of_uni hL₁u
  have hU₁ : IsUp U₁ := isUp_of_uni hU₁u
  rw [zhatOM_eq] at e₁
  choose l ρ hl hρ hlr using hloc
  choose T c hc0 hT using fun p => locTarget Zd u u' p w hL₁ hU₁ e₁ hA₀ hB₀ (hl p) (hρ p) (hlr p)
  have hE : ∀ᶠ p in Filter.cofinite, ∀ (k : Fin 8) (i j : Fin (D.R.rS + 1)),
      (D.s.atP p).ιE ((![A₀, B₀, L₁, L₁⁻¹, U₁, U₁⁻¹, Matrix.of fun i _ => pv w.1 i,
        Matrix.of fun i _ => (pv w.1 i)⁻¹] : Fin 8 → PairVal.MatR D) k i j) ∈ (D.s.atP p).O :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      LocModel.LM.iotaIntegral_almost_all D _
  have hG := (LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅).and hE
  have hfin := Filter.eventually_cofinite.1 hG
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat D.s.atP hfin.toFinset (fun p => T p ij.1 ij.2) c (fun p _ => hc0 p)
  let X' : PairVal.MatR D := Matrix.of fun i j => if Free (fσ w) i j then t (i, j) else (1 : PairVal.MatR D) i j
  have hX'1 : ∀ i j, ¬ Free (fσ w) i j → X' i j = (1 : PairVal.MatR D) i j := fun i j h => by
    simp only [X', Matrix.of_apply, if_neg h]
  have hX'2 : ∀ i j, Free (fσ w) i j → X' i j = t (i, j) := fun i j h => by
    simp only [X', Matrix.of_apply, if_pos h]
  have hX' : IsLo X' :=
    ⟨fun a => by rw [hX'1 a a (fun h => lt_irrefl a h.1), Matrix.one_apply_eq],
      fun a b hab => by rw [hX'1 a b (fun h => absurd h.1 (not_lt.2 hab.le)), Matrix.one_apply_ne hab.ne]⟩
  have hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0 := fun i j hij => by
    have hf : ¬ Free (fσ w) i j := fun h => absurd h.2 (not_lt.2 hij.le)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rw [hX'1 i j hf, Matrix.one_apply_ne hne]
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ e₁ hX' hpat
  refine ⟨gX L₁ X', gY w U₁ X', hgX, hgY, hst, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · exact hT p X' hX' hpat fun i j hf => by rw [hX'2 i j hf]; exact ht1 (i, j) p hp
  · have hgp : _ ∧ _ := not_not.1 ((Set.Finite.mem_toFinset hfin).not.1 hp)
    obtain ⟨⟨hM, ⟨hδ1, hδ2⟩, ⟨hu1, hu2⟩, -⟩, hEp⟩ := hgp
    obtain ⟨hcf, hcfi⟩ := cf_int Zd p hδ1 hδ2 hu1 hu2
    have hXi : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O := by
      intro i j
      by_cases hf : Free (fσ w) i j
      · rw [hX'2 i j hf]; exact ht2 (i, j) p hp
      · rw [hX'1 i j hf, Matrix.one_apply]
        split_ifs
        · rw [map_one]; exact Subring.one_mem _
        · rw [map_zero]; exact Subring.zero_mem _
    exact good_at Zd p hM w hL₁ hU₁ hA₀ hB₀ hX' hpat hcf hcfi
      (fun i j => hEp 0 i j) (fun i j => hEp 1 i j) (fun i j => hEp 2 i j) (fun i j => hEp 3 i j)
      (fun i j => hEp 4 i j) (fun i j => hEp 5 i j) (fun a => hEp 6 a a) (fun a => hEp 7 a a) hXi

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutLeavesDeep_of_betaInt (D : Formalism.BasicNotions.D7)
    (hB : ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
      (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
      (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), BetaInt ⟨δ, M, hA⟩ u u' F0 what₂) :
    Formalism.L2.SG.Pf.Coef.CutLeavesDeep D := by
  intro _ δ M hA _ u u' hc hP F0 what₂ hR
  refine ⟨fun γ w F' L U hE p => ⟨Formalism.L2.SG.Pf.CountAt.countAt_holds (M := M) (δ := δ) (γ := γ) (w := w) (F' := F') (L := L) (U := U) (hE := hE) (p := p) ..,
    by intros; apply Formalism.L2.SG.Pf.ProdEP2Uni.unimodAt_holds⟩,
    Formalism.L2.SG.Pf.TupGlobApprox.stabApprox _ u u', ?_⟩
  exact fStarC_of_int ⟨δ, M, hA⟩ ⟨hc, hR, hP⟩ (hB δ M hA u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

namespace Formalism.L2.SG.Closed

theorem CutLeavesDeep_outright (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.Pf.Coef.CutLeavesDeep D := Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.cutLeavesDeep_of_betaInt D
  (fun _ _ _ u u' F0 what₂ => Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.betaInt_holds _ u u' F0 what₂)

end Formalism.L2.SG.Closed

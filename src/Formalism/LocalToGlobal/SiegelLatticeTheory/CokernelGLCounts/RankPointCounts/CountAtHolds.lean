module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCellRel

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XPEqZzp
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBaseT
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBase
noncomputable section

namespace Formalism.L2.SG.Pf.CountBase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem zhatOM_sg (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ZhatOM X * Sg D.host.E D.R.rS = X := by
  ext a b
  simp only [ZhatOM, Sg, Matrix.mul_diagonal]
  rw [mul_comm, ← mul_assoc, ← mul_pow]
  simp

theorem modMat_ord (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) :
    Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (ptMat w).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) =
      modMat δ T T' p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  ext a b
  rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
  by_cases hb : b = sgF w a
  · rw [if_pos hb, if_pos hb, modMat_blk Zd]
    simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
    subst hb
    ring
  · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]

theorem baseConj_L (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    Formalism.L2.SG.Pf.ProdE.Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w = a.mat := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hY := Formalism.L2.SG.Pf.PCount.zzp_sgn_ord Zd u u' p hM (ZhatOM (ptMat w))
  rw [zhatOM_sg] at hY
  have hmat := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  rw [hmat]
  unfold Formalism.L2.SG.Pf.ProdE.Y0
  congr 1
  rw [show Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p =
    Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p from rfl, hY]
  exact modMat_ord hA _ _ p hM w

end Formalism.L2.SG.Pf.CountBase
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Corner

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLo_of_uni {L : Matrix (Fin n) (Fin n) R} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni {U : Matrix (Fin n) (Fin n) R} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem uni_of_isLo {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) : IsLoUni L :=
  fun a b => ⟨fun hab => h.2 a b hab, fun e => by subst e; exact h.1 a⟩

theorem uni_of_isUp {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) : IsUpUni U :=
  fun a b => ⟨fun hab => h.2 b a hab, fun e => by subst e; exact h.1 a⟩

end Corner

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def glOfLo {L : MP p} (h : IsLo L) : GLp p :=
  ⟨L, L⁻¹, Matrix.mul_nonsing_inv L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1])⟩

def glOfUp {U : MP p} (h : IsUp U) : GLp p :=
  ⟨U, U⁻¹, Matrix.mul_nonsing_inv U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1])⟩

theorem glue_one_one {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ} :
    glue e (1 : Matrix (Fin n) (Fin n) Fp) 1 = 1 :=
  mat_eq e (by rw [glue_map_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [glue_map_snd, Matrix.map_one _ (map_zero _) (map_one _)])

theorem corner_fix {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ}
    {l ρ Δ : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hl : IsLoUni l) (hρ : IsUpUni ρ) (k1 k2 : Fp)
    (h1 : Δ.map (p1 e) = k1 • Ecorner n) (h2 : Δ.map (p2 e) = k2 • Ecorner n) : l * Δ * ρ = Δ := by
  apply mat_eq e
  · rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]
  · rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]


set_option maxHeartbeats 4000000 in
theorem baseAt_typed (hA : ∀ p, Agree δ M p) (g : Loc.SplitG (M p).L) (hM : (M p).split = some g)
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    BaseAt M δ u u' w p a := by
  have hAg := (hA p).2.2.2.2.2
  rw [hM] at hAg
  obtain ⟨sg, hR, hge, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hs] at hAg; exact hAg.elim
    · rw [hs] at hAg; exact ⟨sg, rfl, hAg.1, hAg.2⟩
  let Zd : LocDat D := ⟨δ, M, hA⟩
  have hzz := Formalism.L2.SG.Pf.PCountEx.zz_fact Zd p sg hR g hM hge hgq u u' w (L := 1) (B := 1)
    Formalism.L2.SG.Pf.PCountEx.isLo_one' Formalism.L2.SG.Pf.PCountEx.isUp_one'
  have e1 : Matrix.diagonal (cf Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e2 : Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e3 : Matrix.diagonal (cfi Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  have e4 : Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  rw [e1, e2, e3, e4, glue_one_one, Matrix.one_mul, Matrix.mul_one] at hzz
  have hz : ZhatOM (ptMat w) = ptMat w * Sg D.host.E D.R.rS := by
    have h := Formalism.L2.SG.Pf.CountBase.zhatOM_sg (ptMat w)
    calc ZhatOM (ptMat w) = ZhatOM (ptMat w) * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
      _ = ptMat w * Sg D.host.E D.R.rS := by rw [h]
  rw [Matrix.one_mul, Matrix.mul_one, ← hz] at hzz
  have hYg : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = _ := hzz
  obtain ⟨Gl, Gu, hGl, hGu, hT⟩ := Formalism.L2.SG.Pf.PCountEx.target_fact Zd p sg hR g hM hge hgq u u' w
  have hY0 : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = Gl * modMat δ (D.mem u).A.T (D.mem u').A.T p w * Gu :=
    hzz.trans hT
  have hshE : Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Formalism.MainNotions.S.LocalSplitGroups.cornerSh δ (D.mem u).A.T (D.mem u').A.T p w • Ecorner D.R.rS := by
    ext i j
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Ecorner, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hsh : Gl * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w * Gu =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [hshE, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hGl hGu]
  have hmod := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  refine ⟨⟨(glOfLo p hGl, MulOpposite.op (glOfUp p hGu)), uni_of_isLo hGl, uni_of_isUp hGu⟩, ?_, ?_⟩
  · show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Gl * a.mat * Gu
    rw [hmod, Matrix.mul_add, Matrix.add_mul, hsh, ← hY0]
  · intro x

    have hd1 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p1 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -((D.mem u).A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_fst, Formalism.L2.SG.Pf.PCount.mm1' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hd2 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p2 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then ((D.mem u').A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_snd, Formalism.L2.SG.Pf.PCount.mm2' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hfix := corner_fix sg.e x.2.1 x.2.2 _ _ hd1 hd2
    have hphi : phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat +
        (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w) := by
      show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
        _
      rw [hmod]; abel
    rw [hphi, smul_def, smul_def, Matrix.mul_add, Matrix.add_mul, hfix]
    constructor
    · intro h; exact add_right_cancel h
    · intro h; rw [h]

theorem baseAt_holds (hA : ∀ p, Agree δ M p) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) : BaseAt M δ u u' w p a := by
  rcases hM : (M p).split with _ | g
  · have h := Formalism.L2.SG.Pf.CountBase.baseConj_L hA u u' w p hM a ha
    refine ⟨1, ?_, fun x => ?_⟩
    · rw [OneMemClass.coe_one, one_smul]; exact h
    · show _ ↔ _
      rw [show phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat from h]
  · exact baseAt_typed M δ u u' w p hA g hM a ha

end Formalism.L2.SG.Pf.CountAt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockCounting
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockCounting

open Formalism.MainNotions.S Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P.Phase

variable {R : Type} [CommRing R] {n : ℕ} (a : Loc.Pt R n)

abbrev sz : List ℕ := a.blocks.map (fun b => (b.2 : ℕ))

theorem sz_sum : (sz a).sum = n := a.size

def bk (i : Fin n) : ℕ := blk (sz a) i

def rv (i : Fin n) : Fin n :=
  ⟨revIn (sz a) i, by have := revIn_lt (sz a) i (by rw [sz_sum]; exact i.2); rwa [sz_sum] at this⟩

def cc (i : Fin n) : R := (((a.blocks.map Prod.fst).getD (bk a i) 1 : Rˣ) : R)

theorem rv_rv (i : Fin n) : rv a (rv a i) = i :=
  Fin.ext (revIn_revIn (sz a) i (by rw [sz_sum]; exact i.2))

theorem bk_rv (i : Fin n) : bk a (rv a i) = bk a i := blk_revIn (sz a) i (by rw [sz_sum]; exact i.2)

theorem bk_mono {i j : Fin n} (h : i ≤ j) : bk a i ≤ bk a j := blk_mono (sz a) i j h

theorem rv_anti {i j : Fin n} (h : i < j) (hb : bk a i = bk a j) : rv a j < rv a i :=
  revIn_anti (sz a) i j (by rw [sz_sum]; exact j.2) h hb

theorem rv_lt_of_bk_lt {i j : Fin n} (h : bk a i < bk a j) : rv a i < rv a j := by
  by_contra hc
  have := bk_mono a (not_lt.1 hc)
  rw [bk_rv, bk_rv] at this
  omega

theorem cc_rv (i : Fin n) : cc a (rv a i) = cc a i := by unfold cc; rw [bk_rv]

theorem cc_unit (i : Fin n) : IsUnit (cc a i) := Units.isUnit _

theorem mat_apply (i j : Fin n) : a.mat i j = if j = rv a i then cc a i else 0 := by
  have h := Formalism.MainNotions.LocalModelPeriodLattices.ptEntryL_eq a.blocks i j (by rw [a.size]; exact i.2)
  show Loc.ptEntryL a.blocks i j = _
  rw [h]
  simp only [Fin.ext_iff, rv, cc, bk]

theorem sameBlock_iff (i j : Fin n) : Loc.sameBlock a.blocks i j = true ↔ bk a i = bk a j :=
  Formalism.MainNotions.LocalOrbitGerms.Cls.sameBlock_iff a.blocks i j (by rw [a.size]; exact i.2) (by rw [a.size]; exact j.2)

end Formalism.L2.SG.Pf.BlockCounting

namespace Formalism.L2.SG.Pf.BlockCounting

open Formalism.MainNotions.S Matrix

variable {R : Type} [CommRing R] {n : ℕ} (a : Loc.Pt R n)

def bd (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j => if bk a i = bk a j then x i j else 0

def rvM (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j => M (rv a i) (rv a j)

variable {a}

theorem bd_lo {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : IsLoUni (bd a x) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold bd; split_ifs
    · exact (hx i j).1 h
    · rfl
  · subst h; unfold bd; rw [if_pos rfl]; exact (hx i i).2 rfl

theorem bd_one : bd a (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  unfold bd
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, if_neg]
    rintro rfl; exact h rfl

theorem bd_mul {x y : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) (hy : IsLoUni y) :
    bd a (x * y) = bd a x * bd a y := by
  ext i j
  simp only [bd, Matrix.mul_apply]
  by_cases hij : bk a i = bk a j
  · rw [if_pos hij]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : bk a i = bk a k
    · rw [if_pos hk, if_pos (hk.symm.trans hij)]
    · rw [if_neg hk, zero_mul]
      by_cases h1 : i < k
      · rw [(hx i k).1 h1, zero_mul]
      · by_cases h2 : k < j
        · rw [(hy k j).1 h2, mul_zero]
        · exfalso
          have e1 := bk_mono a (not_lt.1 h1)
          have e2 := bk_mono a (not_lt.1 h2)
          omega
  · rw [if_neg hij]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : bk a i = bk a k
    · rw [if_pos hk, if_neg (fun e => hij (hk.trans e)), mul_zero]
    · rw [if_neg hk, zero_mul]

theorem bd_inv {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : bd a x⁻¹ = (bd a x)⁻¹ := by
  obtain ⟨hi, -, h2⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx
  have : bd a x * bd a x⁻¹ = 1 := by rw [← bd_mul hx hi, h2, bd_one]
  exact (Matrix.inv_eq_right_inv this).symm

theorem bd_eq_one_iff {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) :
    bd a x = 1 ↔ ∀ i j : Fin n, i ≠ j → bk a i = bk a j → x i j = 0 := by
  constructor
  · intro h i j hij hb
    have := congrFun (congrFun h i) j
    simp only [bd, if_pos hb, Matrix.one_apply, if_neg hij] at this
    exact this
  · intro h
    ext i j
    unfold bd
    rw [Matrix.one_apply]
    split_ifs with h1 h2 h2
    · subst h2; exact (hx i i).2 rfl
    · exact h i j h2 h1
    · subst h2; exact absurd rfl h1
    · rfl

theorem rvM_mul (M N : Matrix (Fin n) (Fin n) R) : rvM a (M * N) = rvM a M * rvM a N := by
  ext i j
  simp only [rvM, Matrix.mul_apply]
  exact (Fintype.sum_equiv ⟨rv a, rv a, rv_rv a, rv_rv a⟩ _ _ (fun k => by simp [rv_rv])).symm

theorem rvM_one : rvM a (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp only [rvM, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e => h (by rw [← rv_rv a i, e, rv_rv])), if_neg h]

theorem rvM_up {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : IsUpUni (rvM a (bd a x)) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold rvM bd
    split_ifs with hb
    · rw [bk_rv, bk_rv] at hb
      exact (hx _ _).1 (rv_anti a h hb.symm)
    · rfl
  · subst h; unfold rvM bd; rw [if_pos rfl]; exact (hx _ _).2 rfl

theorem bd_mat (x : Matrix (Fin n) (Fin n) R) : bd a x * a.mat = a.mat * rvM a (bd a x) := by
  ext i j
  have h1 : (bd a x * a.mat) i j = bd a x i (rv a j) * cc a (rv a j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (rv a j)]
    · rw [mat_apply, if_pos (rv_rv a j).symm]
    · intro k _ hk
      rw [mat_apply, if_neg (fun e => hk (by rw [e, rv_rv])), mul_zero]
    · simp
  have h2 : (a.mat * rvM a (bd a x)) i j = cc a i * bd a x i (rv a j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
    · rw [mat_apply, if_pos rfl, rvM, rv_rv]
    · intro k _ hk
      rw [mat_apply, if_neg hk, zero_mul]
    · simp
  rw [h1, h2, cc_rv]
  unfold bd
  split_ifs with hb
  · have : cc a i = cc a j := by unfold cc; rw [hb, bk_rv]
    rw [this, mul_comm]
  · simp

def ccU (a : Loc.Pt R n) (i : Fin n) : Rˣ := (a.blocks.map Prod.fst).getD (bk a i) 1

theorem cc_eq (i : Fin n) : cc a i = (ccU a i : R) := rfl

theorem ccU_rv (i : Fin n) : ccU a (rv a i) = ccU a i := by unfold ccU; rw [bk_rv]

def matI (a : Loc.Pt R n) : Matrix (Fin n) (Fin n) R := fun i j => if j = rv a i then (((ccU a i)⁻¹ : Rˣ) : R) else 0

theorem matI_mul : matI a * a.mat = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
  · rw [matI, if_pos rfl, mat_apply, rv_rv, Matrix.one_apply]
    by_cases h : j = i
    · subst h; rw [if_pos rfl, if_pos rfl, cc_eq, ccU_rv]; exact Units.inv_mul _
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro k _ hk
    rw [matI, if_neg hk, zero_mul]
  · simp

theorem bd_of_stab {l ρ : Matrix (Fin n) (Fin n) R} (hl : IsLoUni l) (hρ : IsUpUni ρ)
    (h : l * a.mat * ρ = a.mat) : bd a l = l := by
  obtain ⟨hρi, -, hρ2⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hρ
  have e : l * a.mat = a.mat * ρ⁻¹ := by
    calc l * a.mat = l * a.mat * (ρ * ρ⁻¹) := by rw [hρ2, Matrix.mul_one]
      _ = l * a.mat * ρ * ρ⁻¹ := by rw [Matrix.mul_assoc (l * a.mat)]
      _ = a.mat * ρ⁻¹ := by rw [h]
  ext i j
  unfold bd
  split_ifs with hb
  · rfl
  · symm
    rcases lt_or_gt_of_ne (show i ≠ j from fun h' => hb (by rw [h'])) with hij | hij
    · exact (hl i j).1 hij
    ·
      have e1 := congrFun (congrFun e i) (rv a j)
      have lhs : (l * a.mat) i (rv a j) = l i j * cc a j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · rw [mat_apply, if_pos rfl]
        · intro k _ hk
          rw [mat_apply, if_neg (fun e' => hk (by rw [← rv_rv a k, ← e', rv_rv])), mul_zero]
        · simp
      have rhs : (a.mat * ρ⁻¹) i (rv a j) = cc a i * ρ⁻¹ (rv a i) (rv a j) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
        · rw [mat_apply, if_pos rfl]
        · intro k _ hk
          rw [mat_apply, if_neg hk, zero_mul]
        · simp
      have hlt : bk a j < bk a i := lt_of_le_of_ne (bk_mono a hij.le) (fun e' => hb e'.symm)
      have hz : ρ⁻¹ (rv a i) (rv a j) = 0 := (hρi _ _).1 (rv_lt_of_bk_lt a hlt)
      rw [lhs, rhs, hz, mul_zero] at e1
      exact ((cc_unit a j).mul_left_eq_zero).1 e1

theorem rho_of_stab {l ρ : Matrix (Fin n) (Fin n) R} (hl : IsLoUni l) (hρ : IsUpUni ρ)
    (h : l * a.mat * ρ = a.mat) : ρ = rvM a (bd a l⁻¹) := by
  have hb := bd_of_stab hl hρ h
  obtain ⟨hli, h1, -⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hl
  have e : a.mat * ρ = l⁻¹ * a.mat := by
    calc a.mat * ρ = (l⁻¹ * l) * a.mat * ρ := by rw [h1, Matrix.one_mul]
      _ = l⁻¹ * (l * a.mat * ρ) := by simp only [Matrix.mul_assoc]
      _ = l⁻¹ * a.mat := by rw [h]
  have hbi : bd a l⁻¹ = l⁻¹ := by rw [bd_inv hl, hb]
  have e2 : a.mat * ρ = a.mat * rvM a (bd a l⁻¹) := by rw [e, ← bd_mat, hbi]
  calc ρ = matI a * (a.mat * ρ) := by rw [← Matrix.mul_assoc, matI_mul, Matrix.one_mul]
    _ = matI a * (a.mat * rvM a (bd a l⁻¹)) := by rw [e2]
    _ = rvM a (bd a l⁻¹) := by rw [← Matrix.mul_assoc, matI_mul, Matrix.one_mul]

end Formalism.L2.SG.Pf.BlockCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut Formalism.L2.SG.Pf.BlockCounting

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

section Retr

variable {p}

def loU {l : MP p} (h : IsLoUni l) : GLp p :=
  ⟨l, l⁻¹, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv h).2.2, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv h).2.1⟩

def upU {l : MP p} (h : IsUpUni l) : GLp p :=
  ⟨l, l⁻¹, (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv h).2.2, (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv h).2.1⟩

variable (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))

theorem UP_lo (x : UP p) : IsLoUni (((x : GG p).1 : GLp p) : MP p) := x.2.1

theorem UP_up (x : UP p) : IsUpUni (((x : GG p).2.unop : GLp p) : MP p) := x.2.2

def retrFun (x : UP p) : UP p :=
  ⟨(loU (bd_lo (a := a) (UP_lo x)),
      MulOpposite.op (upU (rvM_up (a := a) (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (UP_lo x)).1))),
    bd_lo (UP_lo x), rvM_up (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (UP_lo x)).1⟩

theorem retrFun_fst (x : UP p) : ((((retrFun a x : UP p) : GG p).1 : GLp p) : MP p) =
    bd a (((x : GG p).1 : GLp p) : MP p) := rfl

theorem retrFun_snd (x : UP p) : ((((retrFun a x : UP p) : GG p).2.unop : GLp p) : MP p) =
    rvM a (bd a (((x : GG p).1 : GLp p) : MP p)⁻¹) := rfl

theorem UP_ext {x y : UP p} (h1 : (((x : GG p).1 : GLp p) : MP p) = (((y : GG p).1 : GLp p) : MP p))
    (h2 : (((x : GG p).2.unop : GLp p) : MP p) = (((y : GG p).2.unop : GLp p) : MP p)) : x = y := by
  apply Subtype.ext
  apply Prod.ext
  · exact Units.ext h1
  · exact MulOpposite.unop_injective (Units.ext h2)

def retr : UP p →* UP p where
  toFun := retrFun a
  map_one' := by
    apply UP_ext
    · rw [retrFun_fst]; exact bd_one
    · rw [retrFun_snd]
      show rvM a (bd a (1 : MP p)⁻¹) = 1
      rw [inv_one, bd_one, rvM_one]
  map_mul' x y := by
    have hx := UP_lo x
    have hy := UP_lo y
    apply UP_ext
    · show bd a ((((x * y : UP p) : GG p).1 : GLp p) : MP p) = bd a _ * bd a _
      exact bd_mul hx hy
    · show rvM a (bd a ((((x * y : UP p) : GG p).1 : GLp p) : MP p)⁻¹) =
        rvM a (bd a (((y : GG p).1 : GLp p) : MP p)⁻¹) * rvM a (bd a (((x : GG p).1 : GLp p) : MP p)⁻¹)
      have e : ((((x * y : UP p) : GG p).1 : GLp p) : MP p) =
          (((x : GG p).1 : GLp p) : MP p) * (((y : GG p).1 : GLp p) : MP p) := rfl
      rw [e, Matrix.mul_inv_rev, bd_mul (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hy).1
        (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1, rvM_mul]

theorem smul_UP (x : UP p) (X : MP p) :
    x • X = (((x : GG p).1 : GLp p) : MP p) * X * (((x : GG p).2.unop : GLp p) : MP p) := rfl

theorem retr_stab (x : UP p) : retr a x • a.mat = a.mat := by
  rw [smul_UP]
  show bd a _ * a.mat * rvM a (bd a _) = a.mat
  have hx := UP_lo x
  rw [bd_mat, Matrix.mul_assoc, ← rvM_mul, ← bd_mul hx (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1,
    (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).2.2, bd_one, rvM_one, Matrix.mul_one]

theorem retr_id (s : UP p) (hs : s • a.mat = a.mat) : retr a s = s := by
  rw [smul_UP] at hs
  apply UP_ext
  · exact bd_of_stab (UP_lo s) (UP_up s) hs
  · exact (rho_of_stab (UP_lo s) (UP_up s) hs).symm

theorem intLow_bd {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : Formalism.MainNotions.S.TieN.IntLow (M p) (bd a l) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · unfold bd; rw [if_pos rfl]; exact h1 i
  · unfold bd; split_ifs
    · exact h2 i j hij
    · rfl
  · unfold bd; split_ifs
    · exact h3 i j
    · exact (M p).R.zero_mem

theorem intUp_rvM {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (rvM a (bd a l)) := by
  have hl2 := h.2.1
  have hb := intLow_bd M a h
  obtain ⟨h1, h2, h3⟩ := hb
  refine ⟨fun i => h1 _, fun i j hij => ?_, fun i j => h3 _ _⟩
  show bd a l (rv a i) (rv a j) = 0
  unfold bd
  split_ifs with hb'
  · rw [bk_rv, bk_rv] at hb'
    exact hl2 _ _ (rv_anti a hij hb'.symm)
  · rfl

theorem retr_K (k : UP p) (hk : k ∈ KU M p) : retr a k ∈ KU M p := by
  obtain ⟨h1, -⟩ := hk
  have hi := (Formalism.L2.SG.Pf.ZsVolGrp.intLow_inv (M p) h1).1
  exact ⟨intLow_bd M a h1, intUp_rvM M a hi⟩

theorem blockRetr_holds : BlockRetr M p a := by
  refine ⟨retr a, ⟨fun x => (MulAction.mem_stabilizer_iff).symm, fun x => retr_stab a x,
    fun s hs => retr_id a s hs, fun x => MonoidHom.mem_ker, fun k hk => retr_K M a k hk⟩, fun x => ?_⟩
  have hx := UP_lo x
  constructor
  · intro h
    have h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1 := by
      rw [← retrFun_fst a x]
      show ((((retr a x : UP p) : GG p).1 : GLp p) : MP p) = 1
      rw [h]; rfl
    refine ⟨hx, fun i j hij hs => ?_⟩
    exact (bd_eq_one_iff hx).1 h1 i j hij ((sameBlock_iff a i j).1 hs)
  · rintro ⟨-, hV⟩
    have h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1 :=
      (bd_eq_one_iff hx).2 fun i j hij hb => hV i j hij ((sameBlock_iff a i j).2 hb)
    apply UP_ext
    · show bd a _ = _
      rw [h1]; rfl
    · show rvM a (bd a _) = _
      rw [bd_inv hx, h1, inv_one, rvM_one]; rfl

end Retr

end Formalism.L2.SG.Pf.CountAt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountWt
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf MeasureTheory
open Classical

variable {D : Formalism.BasicNotions.D7}

theorem wtL_eq_wtZ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (ha : modPt δ T T' p w = some a) (Y : MatP D p) :
    wtL M δ T T' p w Y = wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) := by
  have hmat : a.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w a ha
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 ∈ kkOrb M p Y} =
      {xy | zAt a xy ∈ orbR (M p) (Y + shM δ T T' p w)} := by
    ext xy
    simp only [Set.mem_ofPred_eq]
    rw [mem_orbR_iff M δ T T' p w Y (zAt a xy), zAt_eq hmat xy, add_sub_cancel_right]
  unfold wtL wtZ muA
  simp only [ha]
  rw [hset]

theorem wtL_count (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (hOK : (M p).OK) (ha : modPt δ T T' p w = some a) {Y : MatP D p} (hY : ∀ i j, Y i j ∈ (M p).R) :
    {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.Finite ∧
    wtL M δ T T' p w Y = ({q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.ncard : ℝ) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hZ0 : ∀ i j, (Y + shM δ T T' p w) i j ∈ (M p).R := fun i j =>
    add_mem (hY i j) (shM_mem M δ T T' p w i j)
  obtain ⟨hfin, hsum⟩ := LocOrbCut.wt_gen (M p) hOK a (Y + shM δ T T' p w) hZ0
  set S := {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)} with hSdef
  have hsupp : (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w) then (1 : ℂ) else 0)) = S := by
    ext q
    simp [hSdef]
  rw [hsupp] at hfin
  refine ⟨hfin, ?_⟩
  rw [wtL_eq_wtZ M δ ha Y]
  have hc : (wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) : ℂ) = (S.ncard : ℂ) := by
    rw [hsum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [hsupp]; simp)]
    rw [Finset.sum_boole, Set.ncard_eq_toFinset_card S hfin]
    congr 2
    exact Finset.filter_true_of_mem (fun q hq => hfin.mem_toFinset.1 hq)
  exact_mod_cast hc

end Formalism.L2.SG.Pf.Coef
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem XP_eq_ZZP {p : PlF D} (hA : Agree δ M p) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (heq : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U) :
    XP M δ u u' (p := p) w L U = Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') := by
  unfold XP Y0
  rw [← move δ M u u' hA L U hL hU, Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM, ← heq,
    Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM]

theorem int_zzp (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    ∀ i j, (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) i j ∈
      (M p).R := by
  obtain ⟨hAg, hT, hrows, -, hel, ⟨hPD, hmk⟩, hadm, -⟩ := hE
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := Formalism.L2.SG.TermDef.Gt_mk hTF.1 ⟨F', hPD⟩
  have hGen := Formalism.L2.SG.TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨F', hPD⟩
  rw [hmk] at hGt hGen
  have hEZ : F' ∈ Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') F0 γ.lam (ZhatL (lf D F0) F') :=
    ⟨⟨hPD.1, hPD.2.1, fun h => hel.1.2 (hGt.trans h)⟩, hadm, hGen.1 hel.1.1, hPD.2.2, rfl⟩
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hAg u u' hT F0 what₂ hrows γ.lam γ.mem (ZhatL (lf D F0) F') F' hEZ p
  intro i j
  simp only [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI i j) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.CountAt
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbR_stable {p : PlF D} (Z0 : MP p) :
    ∀ Z ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0, ∀ l ρ, Formalism.MainNotions.S.TieN.IntLow (M p) l → Formalism.MainNotions.S.TieN.IntUp (M p) ρ →
      l * Z * ρ ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0 := by
  rintro Z ⟨l', ρ', hl', hρ', rfl⟩ l ρ hl hρ
  refine ⟨l * l', ρ' * ρ, Formalism.L2.SG.Pf.LocOrbCut.intLow_mul (M p) hl hl', Formalism.L2.SG.Pf.LocOrbCut.intUp_mul (M p) hρ' hρ, ?_⟩
  simp only [Matrix.mul_assoc]

theorem countAt_holds (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) := by
  have hA := hE.1 p
  have hL := hE.2.2.2.2.2.2.2.1
  have hU := hE.2.2.2.2.2.2.2.2.1
  have heq := hE.2.2.2.2.2.2.2.2.2
  obtain ⟨a, ha⟩ := Formalism.L2.SG.Pf.PCount.modPt_full (δ := δ) (D.mem u).A.T (D.mem u').A.T p hA.2.1 w
  obtain ⟨πa, hD, hker⟩ := blockRetr_holds M a
  have hB := baseAt_holds M δ u u' w p hE.1 a ha
  have hInt := int_zzp M δ u u' F0 what₂ γ w F' L U hE p
  have hgW : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
      Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
        Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [gU_smul, XP_eq_ZZP M δ u u' F0 hA w F' L U hL hU heq]
    rfl
  obtain ⟨hfin, hwt⟩ := Formalism.L2.SG.Pf.Coef.wtL_count M δ hA.1 ha hInt
  have hcard := card_cellRel M a πa hker (gU M δ u u' w hA L U hL hU a hB)
  rw [hgW] at hcard
  set Z0 : MP p := Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
    Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w with hZ0
  have hcos := Formalism.L2.SG.Pf.Coef.cellCos (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0) (orbR_stable M Z0)
  refine countAt_of_parts M δ u u' w hA L U hL hU a hB πa hD _ ?_ ?_
  · rw [hcard, ← hcos, hwt]
  · rw [Nat.card_ne_zero]
    refine ⟨⟨Quotient.mk _ (CountAb.toCell a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
      (gU M δ u u' w hA L U hL hU a hB) hD 1)⟩, ?_⟩
    have hcl := (Formalism.L2.SG.Pf.Coef.cellCos_finite_iff (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0)
      (orbR_stable M Z0)).1 hfin
    have hrange := fC_range M a πa hker (gU M δ u u' w hA L U hL hU a hB)
    rw [hgW] at hrange
    rw [← hrange] at hcl
    have hinj : Function.Injective (Set.rangeFactorization (fC M a πa hker (gU M δ u u' w hA L U hL hU a hB))) :=
      fun x y h => fC_inj M a πa hker _ (congrArg Subtype.val h)
    exact @Finite.of_injective _ _ hcl.to_subtype _ hinj

end Formalism.L2.SG.Pf.CountAt

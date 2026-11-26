module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomEmpty

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasV
namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def gd (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : B.Mat P.k P.r :=
  bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))

def wq (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : Fin (2 * P.r + P.k + 1) → ℂ :=
  D.prW P.k P.r p.T.base.z (D.cofR p.T.base (gd p d))

theorem vDecomp (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (d : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) (hG : 0 < TBB.Gp p (TBB.bigPt P.r d)) :
    ∃ hA ∈ UWset P.k P.r p.T.base.z, ∃ hB ∈ UWset P.k P.r p.T.base.z', ∃ l : ℂ,
      p.V F (TBB.bigPt P.r d) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d)) ∧
      hA *ᵥ wq p d = l • (p.m₀ *ᵥ p.ν') ∧ l ≠ 0 := by
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd
  have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  have hV : p.V F (TBB.bigPt P.r d) = D.orbJ p.T.base h'.choose
      (D.muR p.T.base h'.choose (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d))) F := by
    show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dite_eq_left ⟨hl, hG'⟩, dite_eq_left h']
  obtain ⟨hγ, hZγ, hDγ⟩ := h'.choose_spec
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'
  have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
  have hsec := p.T.base.sec.2 _ hζ
  have hγ' : gd p d ∈ B.GV P.k P.r := bigCellMem P.k P.r _ _ hc hsec.1
  have hZγ' : Zhat P.k P.r p.T.base.z p.T.base.z' (gd p d) = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) :=
    Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ
  have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (gd p d) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']; exact hG'
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
    ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
    _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
  have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB
    hfB F
  have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
    Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
  rw [hw] at hmono
  obtain ⟨a, ha, hpr⟩ := hDγ.1
  have hdet : (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.determinant_nonzero P.k P.r p.T.base.z p.T.base.z' (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base)
      (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) _ hpos
  refine ⟨hA, hhA, hB, hhB, (a : ℂ) * (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det, ?_, ?_,
    mul_ne_zero (by exact_mod_cast ha.ne') hdet⟩
  · rw [hV, ← hlaw]
    show _ = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d))
    rw [← hγs, hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]
  · have hZ1 := Formalism.FourierDecayAlt.P.Dx2.VV.zhat_conj p.T.base hhA hnA hfA hhB hnB hfB h'.choose
    have hcof := Formalism.FourierDecayAlt.P.Dx2.VV.cofR_conj p.T.base (sA := hA * nA)
      (Formalism.FourierDecayAlt.P.Dx2.VV.mul_fix hhB hfB) hZ1
    have hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0 := by
      rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
      have := p.T.base.T_pos
      intro h
      have h2 := congrArg Complex.re h
      simp at h2; linarith
    have hsinv := Formalism.FourierDecayAlt.P.Dx2.VV.prW_sinv p.T.base.z_mem hzz hhA hnA
      (Formalism.FourierDecayAlt.P.Dx2.VV.cofR_free p.T.base h'.choose)
    unfold wq
    rw [hγs, hcof, hsinv, hpr, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1),
      Matrix.one_mulVec]

end vec

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ}

theorem prW_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r (D.prW k r z v) := by
  intro i hi
  have hzi : z i = 0 := hz i hi
  simp only [D.prW]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hzi, mul_zero, sub_zero]
  split_ifs with h
  · exfalso; omega
  · rfl

theorem projection_hermitian_orthogonal (z v : Fin (2 * r + k + 1) → ℂ) (hzz : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (D.prW k r z v) z = 0 := by
  have key : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
      herm (Hpk k r) (x - c • y) z = herm (Hpk k r) x z - c * herm (Hpk k r) y z := by
    intro x y c
    simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  simp only [D.prW]
  rw [key, div_mul_cancel₀ _ hzz, sub_self]

def prWL (z : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) where
  toFun := D.prW k r z
  map_add' := Formalism.FourierDecayAlt.P.Dx2.DF.prW_add z
  map_smul' c v := Formalism.FourierDecayAlt.P.Dx2.DF.prW_smul z v c

theorem prW_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (D.prW k r z) :=
  (prWL (k := k) (r := r) z).continuous_of_finiteDimensional

theorem cofR_cont {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) : Continuous (D.cofR S) := by
  have hZ : Continuous (fun γ : B.Mat k r => Zhat k r S.z S.z' γ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Zhat, herm]
    exact continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))
  show Continuous (fun γ : B.Mat k r =>
    ∑ j, (Zhat k r S.z S.z' γ).adjugate j (Fin.last r) • (γ *ᵥ fvec k r S.z' j))
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply (Fin.last r)).comp ((continuous_apply j).comp hZ.matrix_adjugate)).smul
    (continuous_id.matrix_mulVec continuous_const)

theorem gd_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (c : Fin (P.r + 1) → ℂ) :
    gd p c = B.gq p.T.base ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r)) := rfl

end aux

section main

theorem typeNormMeas_of_typeComm_houseMeas (hTC : TypeComm) (hHM : HouseMeas) : TDM.TypeNormMeas := by
  intro Wp Wq _ _ _ _ _ _ P p Y A hThr hY ρ
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_base_parts p.T.base p.hF
  obtain ⟨hν, hνz, hνν, -, -⟩ := id p.hF
  have he : inWb P.k P.r (p.m₀ *ᵥ p.ν') := hmW p.ν' hν
  have hee : herm (Hpk P.k P.r) (p.m₀ *ᵥ p.ν') (p.m₀ *ᵥ p.ν') = 1 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (p.m₀ *ᵥ p.ν') p.T.base.z = 0 := by
    rw [hzeq, Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, hνz, mul_zero]
  have hzW : inWb P.k P.r p.T.base.z := (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base).1
  have hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
    have := p.T.base.T_pos
    intro h
    have h2 := congrArg Complex.re h
    simp at h2; linarith
  have hzneg : (herm (Hpk P.k P.r) p.T.base.z p.T.base.z).re < 0 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
    have := p.T.base.T_pos
    simp; linarith
  have he0 : p.m₀ *ᵥ p.ν' ≠ 0 := by
    intro h0; rw [h0] at hee; simp [herm] at hee
  obtain ⟨H, hHm, hHU, hHe⟩ := hHM P.k P.r p.T.base.z (p.m₀ *ᵥ p.ν') hzW hzneg he hez hee
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set D0 : Set (Fin (P.r + 1) → ℂ) := {c | (∀ i, c i ≠ 0) ∧ TT < Complex.normSq (c (Fin.last P.r))} with hD0def
  set Φ : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ‖B.hsVec ((p.TP.E ρ).comp ((p.T.base.π (H (wq p c))).comp (B.JF p.T.base Y (gd p c))))‖ with hΦ

  have hGform : ∀ c : Fin (P.r + 1) → ℂ, TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ a : Fin P.r, c a.castSucc) * (Complex.normSq (c (Fin.last P.r)) - TT) := by
    intro c
    show D.ptG TT P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    ring

  have h1 : ∀ c ∈ D0, ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖ = Φ c := by
    intro c hc
    obtain ⟨hd, hζ⟩ := hc
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [hGform]
      have h0 : (∏ a : Fin P.r, c a.castSucc) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hd _
      exact mul_pos (Complex.normSq_pos.2 h0) (by linarith)
    obtain ⟨hA, hhA, hB, hhB, l, hVeq, hAw, hl0⟩ := vDecomp p Y c hd hG
    set w := wq p c with hw
    have uA : IsUnit hA.det := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
    have hwA : w = hA⁻¹ *ᵥ (l • (p.m₀ *ᵥ p.ν')) := by
      rw [← hAw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uA, Matrix.one_mulVec]
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, Matrix.mulVec_zero] at hAw
      exact (smul_ne_zero hl0 he0) hAw.symm
    have hwW : inWb P.k P.r w := prW_inWb (k := P.k) (r := P.r) hzW _
    have hwz : herm (Hpk P.k P.r) w p.T.base.z = 0 := projection_hermitian_orthogonal (k := P.k) (r := P.r) _ _ hzz
    obtain ⟨l', hl'⟩ := hHe w hwW hwz hw0
    have hHUw := hHU w
    set Mw := H w with hMw
    have uH : IsUnit Mw.det := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hHUw.1
    have hl'0 : l' ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hl'
      apply hw0
      rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ uH, ← Matrix.mulVec_mulVec, hl', Matrix.mulVec_zero]
    have hHinv : Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν') = l'⁻¹ • w := by
      have h0 : Mw⁻¹ *ᵥ (Mw *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uH, Matrix.one_mulVec]
      rw [hl', Matrix.mulVec_smul] at h0
      calc Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν') = l'⁻¹ • (l' • Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν')) := by
            rw [smul_smul, inv_mul_cancel₀ hl'0, one_smul]
        _ = l'⁻¹ • w := by rw [h0]
    set g := hA * Mw⁻¹ with hgdef
    have hg : g ∈ UWset P.k P.r p.T.base.z :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hhA (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv (hHU w))
    have hge : g *ᵥ (p.m₀ *ᵥ p.ν') = (l'⁻¹ * l) • (p.m₀ *ᵥ p.ν') := by
      rw [hgdef, ← Matrix.mulVec_mulVec, hHinv, Matrix.mulVec_smul, hAw, smul_smul]
    have hcomm := hTC P Wp p.T.base.π p.T.base.z (p.m₀ *ᵥ p.ν') p.TP p.T.base.π_rep p.T.base.π_cont
      p.T.base.π_unitary (by have := p.hl.2.2; omega) hzW p.T.base.T_pos he hez hee g hg (l'⁻¹ * l) hge ρ
    have hgH : g * Mw = hA := by
      rw [hgdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uH, Matrix.mul_one]
    have hπA : p.T.base.π hA = (p.T.base.π g).comp (p.T.base.π Mw) := by
      rw [← hgH]; exact p.T.base.π_rep.2 g hg Mw hHUw
    have key : (p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base g hB
        ((p.TP.E ρ).comp ((p.T.base.π Mw).comp (B.JF p.T.base Y (gd p c)))) := by
      rw [hVeq, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply]
      unfold Formalism.FourierDecayAlt.P.Dx2.VV.Cin
      rw [hπA]
      ext v
      have := congrArg (fun L : Wp →L[ℂ] Wp => L ((p.T.base.π Mw) ((B.JF p.T.base Y (gd p c))
        ((p.T.base.π' hB⁻¹) v)))) hcomm
      simpa using this
    rw [key, CutBP.hsVec_norm_CinL p.T.base hg hhB]

  have h2 : ∀ c : Fin (P.r + 1) → ℂ, (∀ i, c i ≠ 0) → c ∉ D0 → p.V Y (TBB.bigPt P.r c) = 0 := by
    intro c hc hcD
    have hζ : Complex.normSq (c (Fin.last P.r)) ≤ TT := by
      by_contra h; exact hcD ⟨hc, lt_of_not_ge h⟩
    have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [hGform]
      exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (by linarith))
    show D.vecV p.T.base p.ν' p.m₀ Y (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dite_eq_right]
    exact fun h => hG h.2

  have hD0 : MeasurableSet D0 := by
    have ho1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ i, c i ≠ 0} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const
    have ho2 : IsOpen {c : Fin (P.r + 1) → ℂ | TT < Complex.normSq (c (Fin.last P.r))} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
    have ho : IsOpen D0 := ho1.inter ho2
    exact ho.measurableSet
  have hqmap : Set.MapsTo (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) D0
      (JF.QDom P.k P.r p.T.base.z p.T.base.z') := fun c hc => ⟨fun a => hc.1 _, hc.2⟩
  have hqc : Continuous (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_apply _)
  have hJ : ContinuousOn (fun c => B.JF p.T.base Y (gd p c)) D0 := by
    have h0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun q => B.JF p.T.base Y (B.gq p.T.base q))
        (JF.QDom P.k P.r p.T.base.z p.T.base.z') :=
      Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates P.k P.r Wp Wq p.T.base A 0 Y hThr hY
    have h1' : ContinuousOn (fun q => B.JF p.T.base Y (B.gq p.T.base q))
        (JF.QDom P.k P.r p.T.base.z p.T.base.z') := h0.continuousOn
    have e : (fun c => B.JF p.T.base Y (gd p c)) = (fun q => B.JF p.T.base Y (B.gq p.T.base q)) ∘
        (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) := by
      funext c; rw [Function.comp_apply, gd_eq]
    rw [e]
    exact h1'.comp hqc.continuousOn hqmap
  have hgd : ContinuousOn (fun c => gd p c) D0 := by
    have h1' : ContinuousOn (fun q => B.gq p.T.base q) (JF.QDom P.k P.r p.T.base.z p.T.base.z') :=
      (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn p.T.base 0).continuousOn
    have e : (fun c => gd p c) = (fun q => B.gq p.T.base q) ∘
        (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) := by
      funext c; rw [Function.comp_apply, gd_eq]
    rw [e]
    exact h1'.comp hqc.continuousOn hqmap
  have hwq : ContinuousOn (fun c => wq p c) D0 :=
    ((prW_cont (k := P.k) (r := P.r) p.T.base.z).comp (cofR_cont (k := P.k) (r := P.r) p.T.base)).comp_continuousOn hgd
  have hπH : Measurable (fun u => p.T.base.π (H u)) := by
    let U : Set (Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ) := UWset P.k P.r p.T.base.z
    let f : (Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp) :=
      fun m => p.T.base.π (Matrix.of m)
    have hf : ContinuousOn f U := p.T.base.π_cont
    have hH' : Measurable (fun u => (Matrix.of.symm (H u) : Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ)) :=
      hHm
    have hr : Continuous (U.restrict f) := hf.restrict
    exact hr.measurable.comp (hH'.subtype_mk (h := fun u => hHU u))
  have hA1 : AEStronglyMeasurable (fun c => p.T.base.π (H (wq p c))) (volume.restrict D0) :=
    (hπH.comp_aemeasurable (hwq.aemeasurable hD0)).aestronglyMeasurable
  have hA2 : AEStronglyMeasurable (fun c => B.JF p.T.base Y (gd p c)) (volume.restrict D0) :=
    hJ.aestronglyMeasurable hD0
  have hsc : Continuous (fun X : Wq →L[ℂ] Wp => B.hsVec X) := by
    unfold B.hsVec
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)
  have hGc : Continuous (fun x : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => ‖B.hsVec ((p.TP.E ρ).comp (x.1.comp x.2))‖) :=
    (hsc.comp (continuous_const.clm_comp (continuous_fst.clm_comp continuous_snd))).norm
  have h3 : AEStronglyMeasurable Φ (volume.restrict D0) := by
    have e : Φ = (fun x : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => ‖B.hsVec ((p.TP.E ρ).comp (x.1.comp x.2))‖) ∘
        (fun c => (p.T.base.π (H (wq p c)), B.JF p.T.base Y (gd p c))) := by
      rw [hΦ]; rfl
    rw [e]
    exact hGc.comp_aestronglyMeasurable (hA1.prodMk hA2)
  have hind : AEStronglyMeasurable (D0.indicator Φ) volume := (aestronglyMeasurable_indicator_iff hD0).2 h3
  refine hind.congr ?_
  filter_upwards [TDM.ae_all_ne P.r] with c hc
  by_cases hcD : c ∈ D0
  · rw [Set.indicator_of_mem hcD, h1 c hcD]
  · rw [Set.indicator_of_notMem hcD, h2 c hc hcD, ContinuousLinearMap.comp_zero]
    unfold B.hsVec
    simp only [ContinuousLinearMap.zero_apply]
    symm
    rw [norm_eq_zero]
    first
      | exact WithLp.toLp_zero 2 _
      | rfl
      | (ext i; simp)

end main

end

end Formalism.FourierDecayAlt.P.CutBP.TNM

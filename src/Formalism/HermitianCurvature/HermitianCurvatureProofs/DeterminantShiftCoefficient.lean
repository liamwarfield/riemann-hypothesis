module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantShiftCoefficient
open MvPolynomial Finset

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem detShift_prod_coeff {σ ι : Type*} [Fintype ι] (h c : ι → MvPolynomial σ ℂ)
    (hh : ∀ i, (h i).IsHomogeneous 1) (hc : ∀ i, (c i).IsHomogeneous 0)
    (d : σ →₀ ℕ) (hd : d.degree = Fintype.card ι) :
    AddMonoidAlgebra.coeff (∏ i, (h i + c i)) d = AddMonoidAlgebra.coeff (∏ i, h i) d := by
  classical
  rw [Finset.prod_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · simp
  · intro S _ hS
    have hH : ((∏ i ∈ S, h i) * ∏ i ∈ univ \ S, c i).IsHomogeneous S.card := by
      have := (IsHomogeneous.prod S h (fun _ => 1) (fun i _ => hh i)).mul
        (IsHomogeneous.prod (univ \ S) c (fun _ => 0) (fun i _ => hc i))
      simpa using this
    apply hH.coeff_eq_zero
    rw [hd]
    intro hcard
    exact hS (Finset.eq_univ_of_card S hcard.symm)
  · intro hn
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) hn

def detShiftSub : Fin 2 → Polynomial ℂ := ![Polynomial.X, -1]

theorem detShift_aeval_monomial (d : Fin 2 →₀ ℕ) (a : ℂ) :
    aeval detShiftSub (monomial d a) = Polynomial.C (a * (-1) ^ d 1) * Polynomial.X ^ d 0 := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [detShiftSub, Polynomial.algebraMap_eq, map_mul, map_pow, map_neg]
  ring

theorem detShift_aeval_coeff (Q : MvPolynomial (Fin 2) ℂ) (t j : ℕ) (hj : j ≤ t)
    (hQ : Q.IsHomogeneous t) :
    (aeval detShiftSub Q).coeff (t - j) =
      (-1) ^ j * AddMonoidAlgebra.coeff Q (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) := by
  classical
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  have hD0 : D 0 = t - j := by simp [hD]
  have hD1 : D 1 = j := by simp [hD]
  have hterm : ∀ d : Fin 2 →₀ ℕ, (aeval detShiftSub (monomial d (AddMonoidAlgebra.coeff Q d))).coeff (t - j) =
      if t - j = d 0 then AddMonoidAlgebra.coeff Q d * (-1) ^ d 1 else 0 := by
    intro d
    rw [detShift_aeval_monomial, Polynomial.coeff_C_mul_X_pow]
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single D]
  · rw [hterm, hD0, hD1, if_pos rfl, mul_comm]
  · intro d hd hne
    rw [hterm]
    split_ifs with h0
    · exfalso
      have hdeg : d.degree = t := by
        by_contra hne'
        exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero hne')
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      apply hne
      ext i
      fin_cases i
      · simp [hD0, ← h0]
      · simp only [Fin.mk_one, Fin.isValue, hD1]
        omega
    · rfl
  · intro hn
    rw [hterm, notMem_support_iff.mp hn]
    simp

theorem detShift_factor {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ) =
      ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) +
        (if σ i = i then -C ((i : ℕ) : ℂ) else 0) := by
  split_ifs <;> ring

theorem detShift_hom {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
  apply IsHomogeneous.add
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  · rw [mul_comm]
    exact isHomogeneous_C_mul_X _ _

theorem detShift_const {t : ℕ} (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then -C ((i : ℕ) : ℂ) else 0) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 0 := by
  split_ifs
  · exact (isHomogeneous_C _ _).neg
  · exact isHomogeneous_zero _ _ _

theorem detShift_subst {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) :
    aeval detShiftSub (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i))) = M.charpoly := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.charpoly, Matrix.det_apply', map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : σ i = i
  · rw [h]
    simp [detShiftSub, Matrix.charmatrix_apply_eq, Polynomial.algebraMap_eq]
    ring
  · simp [detShiftSub, h, Polynomial.algebraMap_eq]

theorem determinant_shift_coefficient : DetShiftCoeff := by
  intro t M j hj
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  set Q : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) with hQdef
  have hdeg : D.degree = t := by
    rw [hD, map_add (f := _), Finsupp.degree_single, Finsupp.degree_single]
    omega
  have hQ : Q.IsHomogeneous t := by
    apply IsHomogeneous.sum
    intro σ _
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ)]
    simpa using (isHomogeneous_C (Fin 2) (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
      (IsHomogeneous.prod (univ : Finset (Fin t)) _ (fun _ => 1) (fun i _ => detShift_hom M σ i))
  have hPQ : AddMonoidAlgebra.coeff (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i))) D =
      AddMonoidAlgebra.coeff Q D := by
    rw [hQdef, coeff_sum, coeff_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ), coeff_C_mul, coeff_C_mul]
    congr 1
    simp_rw [detShift_factor M σ]
    exact detShift_prod_coeff _ _ (detShift_hom M σ) (detShift_const σ) D (by simp [hdeg])
  rw [hPQ]
  have hC := detShift_aeval_coeff Q t j hj hQ
  rw [hQdef, detShift_subst] at hC
  rw [hC, ← hQdef, ← mul_assoc, ← mul_pow, show ((-1 : ℂ) * -1) = 1 by norm_num, one_pow, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepAPf
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JDRvStepAOfLvlA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LvlA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D' : Set (Q.Mx k r)) (Y : ℂ),
    inWb k r z → inWb k r z' → Q.IsDom k r z z' (TemperedBoundGL3.lr hr).castSucc D' →
    ∀ J₀ ∈ Q.FFl k r z z' π π' (TemperedBoundGL3.lr hr).castSucc D', ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      g ∈ Qx6.Dc1 (TemperedBoundGL3.lr hr) D' c →
      NLv k r z z' (TemperedBoundGL3.lr hr).castSucc (Q.uC k r (Fin.last r) Y - 1) J₀
          (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * g) =
        -((Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ)) •
              Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g -
            pbOp (TemperedBoundGL3.lr hr) (fun c' => Q.tL k r z z' (Fin.last r) Y 0 1
              (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c' (TemperedBoundGL3.lr hr)) * x)) g) c) -
          (star (c (TemperedBoundGL3.lr hr)))⁻¹ •
            Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g

section ops

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem nlv_smulC (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) (u : ℂ) :
    Formalism.FourierDecayAlt.P5.SmulC (E := X) (NLv k r z z' l u) := by
  intro α f
  funext x
  simp only [NLv, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) _ _ u α f, Pi.smul_apply, smul_comm]

theorem nlv_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) (f : Q.Mx k r → X) :
    NLv k r z z' l u (fun x => f (Q.wCell k r i c * x)) = fun x => NLv k r z z' l u f (Q.wCell k r i c * x) := by
  funext x
  simp only [NLv]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [TemperedBoundGL3.hermitian_invariant_cell_action i hc hz x]
  congr 1
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f _ _ u _) x

end ops

theorem jDRvStepA_of_lvlA (h : LvlA) : JDRvStepA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  obtain ⟨hJ₀, hD'⟩ := TemperedBoundGL3.br1 hz hz' hD hJ hc (TemperedBoundGL3.lr hr)
  have hcg' : Q.wCell k r (TemperedBoundGL3.lr hr).succ c * g ∈ D := by rw [TemperedBoundGL3.lr_succ]; exact hcg
  have hgD' := TemperedBoundGL3.cell_preimage_mem_domain (TemperedBoundGL3.lr hr) hcg'
  have hL := h Wp Wq k r hr z z' π π' _ Y hz hz' hD' _ hJ₀ c hc g hg hgD'

  set l : Fin r := TemperedBoundGL3.lr hr with hl
  set J₀ := Q.resG k r l.castSucc J c with hJ₀def
  set W : (Fin r → ℂ) → ℂ := fun c' => ((‖c' l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) with hW
  set A' : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r l (c' l) * x)) g with hA'
  set T22 := Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r l (c l) * x)) g with hT22

  have hb := TemperedBoundGL3.br2 l (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1)) (nlv_smulC z z' _ _) c
    (nlv_left hz z' _ _ l.castSucc hc) J g
  rw [TemperedBoundGL3.lr_succ] at hb
  have eL : FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
      W c • NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J₀ (Q.w1 k r l (c l) * g) := by
    show Q.resG k r (Fin.last r) (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J) c g = _
    rw [hb]

  have eR : ∀ c' ∈ OmX r, (∀ a : Fin r, a.val < l.val → c' a = c a) →
      Q.resG k r (Fin.last r) J c' = fun x => W c' • J₀ (Q.w1 k r l (c' l) * x) := by
    intro c' hc' hcc
    rw [← TemperedBoundGL3.lr_succ hr, Qx6.resG_succ]
    funext x
    show W c' • Q.resG k r l.castSucc J c' (Q.w1 k r l (c' l) * x) = _
    rw [Qx6.ind_resG l.castSucc J c' hc' c hc (fun a ha => hcc a ha)]
  have eRc := eR c hc (fun _ _ => rfl)

  have hTop := mirror_residue_top_holds Wp Wq k r z z' π π' D Y hz hz' hD J hJ
  set f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c') g with hf₂
  have hgerm : (fun c' => FNv k r z z' Y J (Fin.last r) c' g) =ᶠ[𝓝 c] fun c' => -f₂ c' := by
    filter_upwards [Qx6.near_pt (Qx6.open_Dcell hD.1 (Fin.last r)) hc hcg] with c' hc'
    rw [hTop c' hc'.1 g hg hc'.2]
    rfl
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)).1
  have hf₂d : DifferentiableAt ℝ f₂ c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt (Formalism.FourierDecayAlt.P.Qx3.pres_tL z z' Y 0 1 _ hfam) (x := (c, g)) ⟨hc, hcg⟩ hg
  have hrr := Formalism.FourierDecayAlt.P.Qx3.pres_tL (i := l.succ) (U₀ := Qx6.UU (Qx6.Dc1 l (Qx6.Dcell D l.castSucc c))) z z' Y 0 1 _
    (Qx6.sf_rr Formalism.FourierDecayAlt.P.weyl_level_element_properties l hJ₀.1)
  rw [TemperedBoundGL3.lr_succ] at hrr
  have hA'd : DifferentiableAt ℝ A' c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt hrr (x := (c, g)) ⟨hc, hgD'⟩ hg
  have hWd : DifferentiableAt ℝ W c := Qx6.diff_gamma l _ hc
  have hf₃d : DifferentiableAt ℝ (fun c' => W c' • A' c') c := hWd.smul hA'd
  have hline : ∀ᶠ s in 𝓝 (c l), (fun c' => -f₂ c') (Function.update c l s) =
      (-1 : ℂ) • (fun c' => W c' • A' c') (Function.update c l s) := by
    filter_upwards [isOpen_ne.mem_nhds (hc l)] with s hs
    have hu : Function.update c l s ∈ OmX r := Qx6.update_mem_Om hc l hs
    have hcc : ∀ a : Fin r, a.val < l.val → Function.update c l s a = c a := fun a ha =>
      Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J (Function.update c l s)) g) = _
    rw [eR _ hu hcc, show (fun x => W (Function.update c l s) • J₀ (Q.w1 k r l (Function.update c l s l) * x)) =
      W (Function.update c l s) • (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W (Function.update c l s))
      (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)), neg_one_smul]
    rfl
  have hp1 : pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c = pbOp l (fun c' => -f₂ c') c :=
    Qx6.opL_germ l 3 hgerm
  have hp2 : pbOp l (fun c' => -f₂ c') c = (-1 : ℂ) • pbOp l (fun c' => W c' • A' c') c :=
    Qx6.opL_dir l 3 (-1) hf₂d.neg hf₃d hline
  have hp3 : pbOp l (fun c' => W c' • A' c') c = W c • pbOp l A' c + ((((Mdim k r l - 1 : ℕ) : ℂ) / 2) * W c) • A' c := by
    rw [Qx6.pbOp_smul l hc hWd hA'd, Qx6.pbOp_gamma l hc]

  have eF : FNv k r z z' Y J (Fin.last r) c g = -(W c • A' c) := by
    rw [hTop c hc g hg hcg]
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c) g) = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl
  have e11 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g = W c • T22 := by
    show Q.tL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J c) g = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 1 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl

  have hmd : ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) - 1 := by
    have : 1 ≤ Q.mdim k r (Fin.last r) := by simp [Q.mdim]
    push_cast [Nat.cast_sub this]
    ring
  have hMd : ((Mdim k r l - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) + 1 := by
    rw [Qx6.stp_Mdim, TemperedBoundGL3.lr_succ]
  have hU : Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) =
      Y - ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    rw [hmd, hMd]
    unfold Q.uC
    ring

  rw [eL, hL, hU]
  show _ = Y • FNv k r z z' Y J (Fin.last r) c g - pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c -
    (star (c l))⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g
  rw [hp1, hp2, hp3, eF, e11]
  module

end

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

theorem lvlA_last : LvlA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D' Y hz hz' hD J₀ hJ₀ c hc g hg hgD
  have h := Formalism.FourierDecayAlt.P.Qx6.lvlA (E := Wq →L[ℂ] Wp) hz hz' (TemperedBoundGL3.lr hr) (by show r - 1 + 1 = r; omega) hD hJ₀.1
    hJ₀.2.1 hJ₀.2.2.1 Y hc (by rw [TemperedBoundGL3.lr_succ]; exact hg) hgD
  rw [TemperedBoundGL3.lr_succ] at h
  exact h

theorem mirror_residue_first_move : JDRvStepA := jDRvStepA_of_lvlA lvlA_last

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightGeneratorWordEvaluation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace FExpR

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rep (m : ℕ∞) (O : Set (B.Mat k r)) (φ : B.Mat k r → E) : Prop :=
  ∃ F : B.Mat k r → E, ContDiffOn ℝ (m : WithTop ℕ∞) F O ∧ ∀ x ∈ O, x ∈ B.GV k r → φ x = F x

theorem rep_mono {m m' : ℕ∞} (hmm : m ≤ m') {O : Set (B.Mat k r)} {φ : B.Mat k r → E} (h : Rep m' O φ) :
    Rep m O φ := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, hF.of_le (by exact_mod_cast hmm), he⟩

theorem rep_RdV {m : ℕ∞} {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {X : B.Mat k r}
    (hX : B.inLie k r X) (h : Rep (m + 1) O φ) : Rep m O (RdV X φ) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => fderiv ℝ F x (x * X), ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hO (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).deriv

theorem rep_Rw {O : Set (B.Mat k r)} (hO : IsOpen O) {f : B.Mat k r → E} {N : ℕ} (h : Rep (N : ℕ∞) O f)
    (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) :
    Rep (m : ℕ∞) O (B.Rw w f) := by
  induction w generalizing m with
  | nil => exact rep_mono (by exact_mod_cast (by simpa using hle)) h
  | cons X w ih =>
    have e : B.Rw (X :: w) f = RdV X (B.Rw w f) := rfl
    rw [e]
    apply rep_RdV hO (hw X (by simp))
    have := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
    exact_mod_cast this

theorem rep_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {x X : B.Mat k r}
    (hx : x ∈ O) (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (h : Rep ((1 : ℕ) : ℕ∞) O φ) :
    HasDerivAt (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) (RdV X φ x) 0 := by
  obtain ⟨F, hF, he⟩ := h
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
  exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).differentiableAt.hasDerivAt

theorem rdV_congr {O : Set (B.Mat k r)} (hO : IsOpen O) {φ ψ : B.Mat k r → E}
    (he : ∀ y ∈ O, y ∈ B.GV k r → φ y = ψ y) {x X : B.Mat k r} (hx : x ∈ O) (hxG : x ∈ B.GV k r)
    (hX : B.inLie k r X) : RdV X φ x = RdV X ψ x := by
  show deriv (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => ψ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hγ := hasDerivAt_mul_exp_smul_zero x X
  have hγ0 := Formalism.FourierDecayAlt.P.B5.curve_zero x X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, x * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem wsEvalR_append (a b : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E)
    (x : B.Mat k r) : wsEvalR (a ++ b) u f x = wsEvalR a u f x + wsEvalR b u f x := by
  simp [wsEvalR, List.map_append, List.sum_append]

theorem wsEvalR_flatMap {α : Type} (F : α → List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ L : List α, wsEvalR (L.flatMap F) u f x = (L.map fun a => wsEvalR (F a) u f x).sum
  | [] => by simp [wsEvalR]
  | a :: L => by
    rw [List.flatMap_cons, wsEvalR_append, wsEvalR_flatMap F u f x L, List.map_cons, List.sum_cons]

theorem wsEvalR_map_mul (p : Polynomial ℂ) (φ : List (B.Mat k r) → List (B.Mat k r)) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)),
      wsEvalR (ws.map fun t => (p * t.1, φ t.2)) u f x = p.eval u • wsEvalR (ws.map fun t => (t.1, φ t.2)) u f x
  | [] => by simp [wsEvalR]
  | t :: ws => by
    have ih := wsEvalR_map_mul p φ u f x ws
    simp only [wsEvalR, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, Polynomial.eval_mul, mul_smul]

theorem fexp_words : ∀ (gens : List (GenW k r)), (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) →
    ∀ t ∈ fexp gens, t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, B.inLie k r X
  | [], _, t, ht => by
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | gn :: gs, hL, t, ht => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have ih := fexp_words gs hL'
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨dX, hdX, s, hs, rfl⟩
    · have := (ih s hs).1
      refine ⟨?_, (ih s hs).2⟩
      show s.2.length ≤ (gn :: gs).length
      simp only [List.length_cons]; omega
    · have := (ih s hs).1
      refine ⟨?_, ?_⟩
      · show (dX.2 :: s.2).length ≤ (gn :: gs).length
        simp only [List.length_cons]; omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact hL gn (by simp) dX hdX
        · exact (ih s hs).2 X hX

theorem ws_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {x X : B.Mat k r} (hx : x ∈ O)
    (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (u : ℂ) (f : B.Mat k r → E) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)), (∀ t ∈ ws, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f)) →
      HasDerivAt (fun s : ℝ => wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)))
        (wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x) 0
  | [], _ => by
    have e : ∀ y, wsEvalR ([] : List (Polynomial ℂ × List (B.Mat k r))) u f y = (0 : E) := fun y => by
      simp [wsEvalR]
    simp only [List.map_nil, e]
    exact hasDerivAt_const _ _
  | t :: ws, h => by
    have h1 := (rep_hasDerivAt hO hx hxG hX (h t (by simp))).const_smul (t.1.eval u)
    have h2 := ws_hasDerivAt hO hx hxG hX u f ws (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have e1 : (fun s : ℝ => wsEvalR (t :: ws) u f (x * NormedSpace.exp ((s : ℂ) • X))) =
        fun s : ℝ => t.1.eval u • B.Rw t.2 f (x * NormedSpace.exp ((s : ℂ) • X)) +
          wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)) := by
      funext s; simp only [wsEvalR, List.map_cons, List.sum_cons]
    have e2 : wsEvalR ((t :: ws).map fun t => (t.1, X :: t.2)) u f x =
        t.1.eval u • RdV X (B.Rw t.2 f) x + wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x := by
      simp only [wsEvalR, List.map_cons, List.sum_cons] <;> rfl
    rw [e1, e2]
    exact h1.add h2

theorem right_generator_word_evaluation (u : ℂ) : ∀ (gens : List (GenW k r)) (O : Set (B.Mat k r)) (f : B.Mat k r → E), IsOpen O →
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → Rep (gens.length : ℕ∞) O f → ∀ x ∈ O, x ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f x = wsEvalR (fexp gens) u f x
  | [], O, f, _, _, _, x, _, _ => by simp [fexp, wsEvalR, B.Rw]
  | gn :: gs, O, f, hO, hL, hf, x, hx, hxG => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have hf' : Rep (gs.length : ℕ∞) O f := rep_mono (by exact_mod_cast (by simp : gs.length ≤ (gn :: gs).length)) hf
    have IH := right_generator_word_evaluation u gs O f hO hL' hf'
    have hW := fexp_words gs hL'
    have hrep : ∀ t ∈ fexp gs, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f) := fun t ht =>
      rep_Rw hO hf t.2 (hW t ht).2 1 (by have := (hW t ht).1; simp only [List.length_cons]; omega)
    have hD : ∀ X, B.inLie k r X → RdV X (wsEvalR (fexp gs) u f) x =
        wsEvalR ((fexp gs).map fun t => (t.1, X :: t.2)) u f x := fun X hX =>
      (ws_hasDerivAt hO hx hxG hX u f (fexp gs) hrep).deriv
    have hR : wsEvalR (fexp (gn :: gs)) u f x = gn.1.eval u • wsEvalR (fexp gs) u f x +
        (gn.2.map fun dX => dX.1 • wsEvalR ((fexp gs).map fun t => (t.1, dX.2 :: t.2)) u f x).sum := by
      simp only [fexp]
      rw [wsEvalR_append, wsEvalR_flatMap]
      congr 1
      · have := wsEvalR_map_mul gn.1 id u f x (fexp gs)
        simpa using this
      · congr 1
        apply List.map_congr_left
        intro dX _
        have := wsEvalR_map_mul (Polynomial.C dX.1) (fun w => dX.2 :: w) u f x (fexp gs)
        simpa using this
    set Φ := (gs.map fun gn => genOpR gn u).foldr (fun T h => T h) f with hΦdef
    have hΦ : ∀ X, B.inLie k r X → RdV X Φ x = RdV X (wsEvalR (fexp gs) u f) x := fun X hX =>
      rdV_congr hO (fun y hy hyG => IH y hy hyG) hx hxG hX
    rw [hR]
    change gn.1.eval u • Φ x + (gn.2.map fun dX => dX.1 • RdV dX.2 Φ x).sum = _
    rw [IH x hx hxG]
    congr 2
    apply List.map_congr_left
    intro dX hdX
    have hX := hL gn (by simp) dX hdX
    rw [hΦ dX.2 hX, hD dX.2 hX]

end FExpR

theorem right_exponential_evaluation : FExpEvalR := by
  intro k r E _ _ gens u UU f hL hf g hg hgG
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf g hg
  exact FExpR.right_generator_word_evaluation u gens U f hU hL ⟨f', hf', he⟩ g hgU hgG

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordFamilySymbolHolds
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpCapLOfOf
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def wfam {d : ℕ} {α : Type} (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d :=
  L.map (fun t => (t.1, t.2.map F)) ++ [(c, [])]

def WFamApp : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ)
    (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ),
    WOp.app (wfam L F c) v x = (L.map fun t => t.1 * vfW (t.2.map F) v x).sum + c * v x

def WFamSymb : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ)
    (x ξ : Fin d → ℝ) (τ : α → ℂ), 1 ≤ j → (∀ t ∈ L, ∀ X ∈ t.2, ((ξ ⬝ᵥ F X x : ℝ) : ℂ) = τ X) →
    WOp.symb (wfam L F c) j x ξ = (L.map fun t => if t.2.length = j then t.1 * (t.2.map τ).prod else 0).sum

def TrRealLie : Prop :=
  ∀ (k r : ℕ) (A X : B.Mat k r), B.inLie k r A → B.inLie k r X →
    (((Matrix.trace (A * X)).re : ℝ) : ℂ) = Matrix.trace (A * X)

def CkLevOn : Prop :=
  ∀ (k r m : ℕ) (Dm : Set (B.Mat k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E),
    Q.CkLev k r 0 m Dm f → B.CkOn (m : ℕ∞) (B.GV k r ∩ Dm) f

theorem wfam_ok {d : ℕ} {α : Type} {O : Set (Fin d → ℝ)} (L : List (ℂ × List α))
    (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ) (hL : ∀ t ∈ L, t.2.length ≤ j)
    (hF : ∀ X, ContDiffOn ℝ ∞ (F X) O) : FamOK O (wfam L F c) j := by
  intro t ht
  rw [wfam, List.mem_append] at ht
  rcases ht with ht | ht
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    refine ⟨by simpa using hL t0 ht0, ?_⟩
    intro V hV
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hV
    exact hF X
  · simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, by simp⟩

theorem opCVOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCVOf := by
  intro hRw hCW k r z z' d O U κ Φ u hC hOm hCk hev j hj1 hjn
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨Ys, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r j hj1 hjn
  choose c hc using hev
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (Ys i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapROf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapROf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z' Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapLOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapLOf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VL κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).2), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VL κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • t.2.foldr Q.LdV u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).2, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ hΞ hcov
    rw [hS d _ L (VL κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ X hΞ ((hL t ht).2 X hX)])]
    exact hsym Ξ hΞ

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_family_apply_holds : WFamApp := by
  intro d α L F c v x
  simp [wfam, WOp.app, List.map_append, List.sum_append, vfW, Function.comp_def]

theorem word_family_symbol_holds : WFamSymb := by
  intro d α L F c j x ξ τ hj hτ
  have h0 : ¬ (0 = j) := by omega
  simp only [wfam, WOp.symb, List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_nil, h0, if_false, add_zero]
  congr 1
  refine List.map_congr_left (fun t ht => ?_)
  simp only [Function.comp_apply, List.length_map]
  split_ifs with hl
  · congr 1
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left (fun X hX => hτ t ht X hX))
  · rfl

theorem trace_real_lie_holds : TrRealLie := by
  intro k r A X hA hX
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose k r
  have hH2 : Hpk k r * Hpk k r = 1 := WeylGroupFacts.hpk_sq
  have eA : Aᴴ = -(Hpk k r * A * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hA
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have eX : Xᴴ = -(Hpk k r * X * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hX
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have hstar : star (Matrix.trace (A * X)) = Matrix.trace (A * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, eX, eA, neg_mul_neg]
    calc Matrix.trace (Hpk k r * X * Hpk k r * (Hpk k r * A * Hpk k r))
        = Matrix.trace (Hpk k r * (X * (Hpk k r * Hpk k r) * A * Hpk k r)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * (Hpk k r * Hpk k r) * A * Hpk k r) * Hpk k r) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * A) := by simp only [Matrix.mul_assoc, hH2, Matrix.mul_one]
      _ = Matrix.trace (A * X) := Matrix.trace_mul_comm _ _
  exact Complex.conj_eq_iff_re.mp hstar

theorem smooth_on_levels_holds : CkLevOn := by
  intro k r m Dm E _ _ f hf g₀ hg₀
  have hg₀' : g₀ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hg₀.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg₀.2⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀'
  exact ⟨U, F, hU, hgU, by exact_mod_cast hF, fun g hg hgG => hfF g hg ⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩

theorem operator_capelli_vector : OpCVOf := opCVOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_right_capelli : OpCapROf := opCapROf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_left_capelli : OpCapLOf := opCapLOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

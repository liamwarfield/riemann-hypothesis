module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaV

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapARep
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem exists_polyOp_qminor_sum {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : ι → Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) (a j) (b j) u F g := by
  have h := fun j => qminorWordSum k r t (a j) (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => ?_, fun g => ?_⟩
      · simp [T₀, pTerm]
      · simp [T₀, pTerm]
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      simp [T₀, pTerm]
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

end Formalism.FourierDecayAlt.P.CutMP.QMinOp

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

noncomputable section

theorem capBeta_pd (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capBeta k r c) := by
  unfold capBeta
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))) fun a l => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Matrix.mulVec]
  refine pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun j _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun c _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul (pd_entry _ _) (pd_const _ 0))

theorem capAlphaV_pd (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capAlphaV k r B) := by
  unfold capAlphaV
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) fun a l => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine pd_sum _ fun m _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  refine pd_sum _ fun l _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem capelli_representation_holds : JDACapRep := by
  intro k r Wp Wq _ _ _ _ _ y
  classical
  have hκ : r ≤ (r + 1) * (2 * r + k + 1) := by nlinarith
  have ho : r ≤ 2 * r + k + 1 := by omega
  obtain ⟨Θ, hP, hO, hE⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun c : Fin r → Fin (2 * r + k + 1) => StrictMono c) (fun _ => C3.xR k r r le_rfl)
    (fun c => c) (capBeta k r) (fun c _ => capBeta_pd k r c) (Q.uC k r 0 y)
  obtain ⟨Θv, hPv, hOv, hEv⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun B : Fin r → Fin (2 * r + k + 1) => StrictMono fun l => C3.keyS k r (B l)) (fun B => B)
    (fun _ => C3.sR k r r le_rfl) (capAlphaV k r) (fun B _ => capAlphaV_pd k r B)
    (y - ((2 * r + k : ℕ) : ℂ) / 2 + (r : ℂ) - 1)
  refine ⟨Θ, Θv, QMinOp.polyOp_mono hP ho hκ, QMinOp.polyOp_mono hPv ho hκ, hO, hOv, fun F g hg hF => ?_,
    fun F g hg hF => ?_⟩
  · rw [hO] at hF
    rw [hE {g} F hF g rfl hg, Finset.sum_filter]
    rfl
  · rw [hOv] at hF
    rw [hEv {g} F hF g rfl hg, Finset.sum_filter]
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg
    simp only [capAv, C3.AAvop, capAlphaV, hinv]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAVTr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section model

variable (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r)

def capaVpM (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => L.Tvl Y l).prod

theorem capaVpM_zero (Y : ℂ) : capaVpM P L Y 0 = 1 := by
  simp [capaVpM]

theorem capaVpM_succ (Y : ℂ) (i : ℕ) (h : i < P.r) :
    capaVpM P L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * capaVpM P L Y i := by
  simp [capaVpM, List.take_add_one, h]

theorem capa_tvprod (Y : ℂ) : L.Tvprod Y = capaVpM P L Y P.r := by
  simp [R.LevelData.Tvprod, capaVpM, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem capa_Tvl_mul_0 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_Tvl_mul_1 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_actA_pb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.pbA P (MA.DQ P) l) f = fun ρ => MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cbi (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbiA P (MA.DQ P) l) f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

end model

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem capa_vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (Q.vAB P.r Y i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r Y i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 0) Φ =
        Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc (Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

theorem capa_vabm_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) =
          MA.actA P (capaVpM P L Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) =
          MA.actA P (capaVpM P L Y i 1 0) (trR P Bs.μsec e Φ)) := by
  obtain ⟨-, hpb, -, -, hcb, hcbi, -⟩ := hL
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (vABm P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (vABm P.r Y 0) 1) Φ = 0 := rfl
    have v0 : capaVpM P L Y 0 0 0 = 1 := by simp [capaVpM_zero]
    have v1 : capaVpM P L Y 0 1 0 = 0 := by simp [capaVpM_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (vABm P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (vABm P.r Y i) 1) Φ with hΦB
    have hv : vABm (X := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (vABm P.r Y i).1 f - pbOp ⟨i, h⟩ ((vABm P.r Y i).1 f) -
          cbOp ⟨i, h⟩ ((vABm P.r Y i).2 f), fun f => cbiOp ⟨i, h⟩ ((vABm P.r Y i).1 f)) := by
      simp only [vABm, dif_pos h]
    have e0 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 0) Φ =
        Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA - Q.crd (cbOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 1) Φ = Q.crd (cbiOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 3
    have hcB : FamR P Bs Dc (Q.crd (cbOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 4
    have hciA : FamR P Bs Dc (Q.crd (cbiOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 5
    have hdif : FamR P Bs Dc (Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_sub (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cbOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => star (c ⟨i, h⟩)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tci : trR P Bs.μsec e (Q.crd (cbiOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (star (c ⟨i, h⟩))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hdif hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hdif ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_pb hpl hk he hA, tc, tA, tB, capaVpM_succ P L Y i h, capa_Tvl_mul_0, hpb, hcb, actA_add, actA_mul,
        actA_mul, actA_neg, sub_eq_add_neg ((algebraMap ℂ (MA.A P (MA.DQ P))) Y), actA_add, actA_algebraMap, actA_neg,
        capa_actA_pb, capa_actA_cb, sub_eq_add_neg, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, capaVpM_succ P L Y i h, capa_Tvl_mul_1, actA_mul, hcbi, capa_actA_cbi]

end ind

theorem capelli_transition_holds : JDAVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ y
  have hA := (capa_vab_ind hpl hk he y P.r le_rfl Dc Φ hΦ).1
  have hAv := (capa_vabm_ind hpl hk he L hL y P.r le_rfl Dc Φ hΦ).1
  refine ⟨⟨hA.1, ?_⟩, ⟨hAv.1, ?_⟩⟩
  · rw [hA.2, R.LevelData.Ar, ← site_vector_eq_tensor_product P L hL y 0, sitesCommonSpace_v0_eq_Vp]
  · rw [hAv.2, R.LevelData.Avr, capa_tvprod]

theorem jDCapA_of_grp (hG : JDAGrp) : JDCapA := jDCapA_of_parts hG capelli_transition_holds residue_derivative_transition

end

end Formalism.FourierDecayAlt.P.CutMP
end

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDCapA_of_inv_toda (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_grp (jDAGrp_of_parts capelli_representation_holds hI hT hTv)

theorem jDCapA_of_inv_todaV (hI : JDACapInv) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_inv_toda hI jda_capelli_toda_proof hTv

theorem jDCapA_of_todaV (hTv : JDACapTodaV) : JDCapA := jDCapA_of_inv_todaV capelli_invariance_criterion hTv

theorem capelli_minors_holds : JDCapA := jDCapA_of_todaV jda_capelli_toda_mirror_proof

end Formalism.FourierDecayAlt.P.CutMP

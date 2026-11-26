module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellAction

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableOfAdj
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableEquivOps
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section aux

variable {k r : ℕ}

def pOf (a b c d : B.Mat k r) : B.SS k r :=
  ((Matrix.of.symm a, Matrix.of.symm b), (Matrix.of.symm c, Matrix.of.symm d))

theorem level_zero_iff (g : B.Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ B.GV k r := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem mat_inv_one : (1 : B.Mat k r)⁻¹ = 1 := by
  simp

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem rho_pOf (D : B.RealPlaceData k r Wp Wq) (a b c d : B.Mat k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D (pOf a b c d) F = fun x => (D.π a).comp ((F (a⁻¹ * b⁻¹ * x * d * c)).comp (D.π' c⁻¹)) := by
  funext x
  simp only [B.rho, B.sgs, pOf, Equiv.apply_symm_apply]

end aux

theorem equivariant_operators_holds : EquivOps := by
  intro hE k r Wp Wq _ _ _ _ _ D O P hDom hloc hsmul hsm hcomm J hJ
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  have hext : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → ∃ (f : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)),
      B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ IsOpen U ∧ g₀ ∈ U ∧
        ∀ x ∈ U, x ∈ B.GV k r → f x = J x :=
    fun g₀ hg hO => hE k r (Wq →L[ℂ] Wp) O J hDom.1 hS g₀ hg hO
  have one_N : (1 : B.Mat k r) ∈ Q.Nlev k r 0 := ⟨mem_n_one, (level_zero_iff _).2 uh_one⟩
  have one_S : ∀ z, (1 : B.Mat k r) ∈ Q.Slev k r z 0 :=
    fun z => ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, one_N, by simp⟩
  have hπ1 : D.π 1 = 1 := D.π_rep.1
  have hπ'1 : D.π' 1 = 1 := D.π'_rep.1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro g₀ hg₀
    have hgG := (level_zero_iff g₀).1 hg₀.1
    obtain ⟨f, U, hf, _, hfO, hUo, hgU, hfJ⟩ := hext g₀ hgG hg₀.2
    obtain ⟨U', F, hU', hgU', hF, hFe⟩ := hsm f hf hfO g₀ hg₀
    refine ⟨U ∩ U', F, hUo.inter hU', ⟨hgU, hgU'⟩, hF.mono Set.inter_subset_right, ?_⟩
    intro x hx hxG
    rw [← hFe x hx.2 hxG]
    exact hloc U J f hUo (fun y hy hyG => (hfJ y hy hyG).symm) x hx.1 ((level_zero_iff x).1 hxG)
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hng : n * g ∈ O := by
      have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z, n, hn, by simp⟩ 1 (one_S D.z')
      simpa using this
    have hngG : n * g ∈ B.GV k r := uh_mul hnG hgG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hngU1, hf1J⟩ := hext (n * g) hngG hng
    have hp : D.inSS (pOf 1 n⁻¹ 1 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_inv hnN
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 n⁻¹ 1 1) F = fun x => F (n * x) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv n (isUnit_of_uh hnG), mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (n * g) = P J (n * g) := hloc U1 f1 J hU1 hf1J (n * g) hngU1 hngG
    have hV : IsOpen ((fun x : B.Mat k r => n * x) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_const.matrix_mul continuous_id)).inter hDom.1
    have e2 : P (fun x => f1 (n * x)) g = P (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hngU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (n * x) hx.1 (uh_mul hnG hxG), Pi.smul_apply]
      exact hL x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hgn : g * n ∈ O := by
      have := hDom.2 g hg 1 (one_S D.z) n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z', n, hn, by simp⟩
      simpa using this
    have hgnG : g * n ∈ B.GV k r := uh_mul hgG hnG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hgnU1, hf1J⟩ := hext (g * n) hgnG hgn
    have hp : D.inSS (pOf 1 1 1 n) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_one
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact hnN
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 1 1 n) F = fun x => F (x * n) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (g * n) = P J (g * n) := hloc U1 f1 J hU1 hf1J (g * n) hgnU1 hgnG
    have hV : IsOpen ((fun x : B.Mat k r => x * n) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_id.matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => f1 (x * n)) g = P (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hgnU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (x * n) hx.1 (uh_mul hxG hnG), Pi.smul_apply]
      exact hR x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg h hh h' hh'
    have hgG := (level_zero_iff g).1 hg.1
    have hhG : h ∈ B.GV k r := hh.1
    have hh'G : h' ∈ B.GV k r := hh'.1
    have hu := isUnit_of_uh hhG
    have hu' := isUnit_of_uh hh'G
    have hhg : h * g * h' ∈ O := by
      have := hDom.2 g hg h ⟨h, hh, 1, one_N, by simp⟩ h' ⟨h', hh', 1, one_N, by simp⟩
      simpa using this
    have hhgG : h * g * h' ∈ B.GV k r := uh_mul (uh_mul hhG hgG) hh'G
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hhgU1, hf1J⟩ := hext (h * g * h') hhgG hhg
    have hp : D.inSS (pOf h⁻¹ 1 h' 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact uw_inv hh
      · exact mem_n_one
      · exact hh'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf h⁻¹ 1 h' 1) F =
        fun x => (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹)) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv h hu, mat_inv_one]
      simp [Matrix.mul_assoc]

    have eL : (D.π h⁻¹).comp (D.π h) = 1 := by
      rw [← D.π_rep.2 _ (uw_inv hh) _ hh, Matrix.nonsing_inv_mul h hu, hπ1]
    have eL' : (D.π h).comp (D.π h⁻¹) = 1 := by
      rw [← D.π_rep.2 _ hh _ (uw_inv hh), Matrix.mul_nonsing_inv h hu, hπ1]
    have eR : (D.π' h').comp (D.π' h'⁻¹) = 1 := by
      rw [← D.π'_rep.2 _ hh' _ (uw_inv hh'), Matrix.mul_nonsing_inv h' hu', hπ'1]
    have eR' : (D.π' h'⁻¹).comp (D.π' h') = 1 := by
      rw [← D.π'_rep.2 _ (uw_inv hh') _ hh', Matrix.nonsing_inv_mul h' hu', hπ'1]
    have eLv : ∀ w, D.π h⁻¹ (D.π h w) = w := fun w => by simpa using congrArg (fun L => L w) eL
    have eL'v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eL'
    have eRv : ∀ w, D.π' h' (D.π' h'⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eR
    have eR'v : ∀ w, D.π' h'⁻¹ (D.π' h' w) = w := fun w => by simpa using congrArg (fun L => L w) eR'
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    have e1 : P f1 (h * g * h') = P J (h * g * h') := hloc U1 f1 J hU1 hf1J _ hhgU1 hhgG
    have hV : IsOpen ((fun x : B.Mat k r => h * x * h') ⁻¹' U1 ∩ O) :=
      (hU1.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => (D.π h⁻¹).comp ((f1 (h * x * h')).comp (D.π' h'⁻¹))) g = P J g := by
      refine hloc _ _ _ hV ?_ g ⟨hhgU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J _ hx.1 (uh_mul (uh_mul hhG hxG) hh'G), hU x ⟨(level_zero_iff x).2 hxG, hx.2⟩ h hh h' hh']
      ext v
      simp [eLv, eRv]
    rw [e2] at hc
    beta_reduce at hc
    rw [e1] at hc

    rw [hc]
    ext v
    simp [eL'v, eR'v]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAFFStable_of_adjComm (hA : AdjComm) : JAFFStable :=
  jAFFStable_of_parts germ_operators_holds extension_locality_holds smooth_operators_holds hA equivariant_operators_holds positive_domain_condition_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem smooth_forms_stability_holds : JAFFStable := FFS.jAFFStable_of_adjComm FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightAverageSmoothComm
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegLiftOfParts
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def KrHyp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (j : ℕ) (hj : j ≤ r) (H : B.Mat k r → (Wq →L[ℂ] Wp)),
    (∀ x ∈ B.GV k r, Dmin k r Bs.z Bs.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) →
    (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
    ∀ y ∈ B.GV k r, Dmin k r Bs.z Bs.z' y ⟨j, by omega⟩ ≠ 0 →
      CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (Kr Bs H) y ∧
      ∀ (l : C.Letter) (e : Fin 2), Kr Bs (D.vLet k r Bs.z Bs.z' j hj l e H) y = D.vLet k r Bs.z Bs.z' j hj l e (Kr Bs H) y

theorem liftDegAll_of (hLF : LeftFubiniLemmas.LeftFubini) (hNF : LeftFubiniLemmas.NFHypL) (hKr : KrHyp) : LiftDegAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j s hj h τ ha w' a' b δ g hg
  have hsz : D.ptSize (h ++ [(s, τ)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hs1 : 1 ≤ s := (ha.1 (s, τ) (by simp)).1
  have hj1 : 1 ≤ j := by rw [← ha.2, hsz]; omega
  obtain ⟨X, _, μ, ℓ, sx, hsx, hFubG⟩ := hLF P.k P.r Wp Wq p.T p.hT j hj hj1 (h ++ [(s, τ)]) ha
  have hgG : g ∈ B.GV P.k (P.r - j) := hg.1
  have hg' : D.castM (by rw [ha.2]) g ∈ B.GV P.k (P.r - D.ptSize (h ++ [(s, τ)])) :=
    Formalism.FourierDecayAlt.P.PBE.castM_GV _ hgG
  have hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])) := ⟨ha.1, rfl⟩
  obtain ⟨hx₁G, hxi, hy⟩ := hNF P.k P.r (h ++ [(s, τ)]) (by rw [ha.2]; exact hj) _ hg' hl
  set PC : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → Prop := fun H =>
    (∀ x ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) H x) ∧
    (∃ R : ℝ, ∀ x ∈ B.GV P.k P.r, H x ≠ 0 → B.gN x ≤ R) with hPC
  refine liftDeg_core p.T F j s hj h τ ha w' a' b δ g X μ ℓ sx _ hsx hx₁G ?_ ?_ PC
    (fun H hH => hFubG g hg H (contOn_of_loc (S := {x | Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨j, by omega⟩ ≠ 0}) (fun x hx hxG => hH.1 x hxG hx)) hH.2) ?_
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).1)
    (fun H hH y hyG hyD => (hKr P.k P.r Wp Wq p.T.base j hj H hH.1 hH.2 y hyG hyD).2)
  · intro a₀ q ha₀
    rw [hxi a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : q.val < D.ptSize h + s
    · rw [dite_eq_left (by rw [hsz]; exact hq), if_pos hq]
      exact hmat_zb h s τ hl a₀.val q.val _ _
    · rw [dite_eq_right (by rw [hsz]; exact hq), if_neg hq]
  · intro a₀ q ha₀
    rw [hy a₀ q (by rw [hsz]; exact ha₀)]
    by_cases hq : P.r + P.k < q.val ∧ 2 * P.r + P.k - q.val < D.ptSize h + s
    · rw [dite_eq_left (by rw [hsz]; exact hq), if_pos hq, hmat_zb h s τ hl a₀.val _ _ _]
    · rw [dite_eq_right (by rw [hsz]; exact hq), if_neg hq]
  · intro w e
    refine ⟨fun x hxG hxD => uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' j hj hF.1 w e x hxD hxG, ?_⟩
    obtain ⟨R, hR⟩ := hF.2.1
    exact ⟨R, uwG_supp p.T.base.z p.T.base.z' F R hR j hj w e⟩

theorem degLift_of_parts (hLF : LeftFubiniLemmas.LeftFubini) (hKr : KrHyp) : KB.DegLift :=
  degLift_of (liftDegAll_of hLF LeftFubiniLemmas.normal_form_left_hypothesis hKr)

end Formalism.FourierDecayAlt.P.PBG
end
end

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section local_

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem foldT_congr_open {U : Set (Mat k r)} (hU : IsOpen U) :
    ∀ (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) {f₁ f₂ : Mat k r → E},
      (∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) →
      ∀ x ∈ U, x ∈ GV k r → Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₁ x = Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₂ x := by
  intro ts f₁ f₂ h
  induction ts with
  | nil => exact h
  | cons t ts ih =>
    intro x hx hxG
    show Top (Q.EH k r) t.1 t.2.1 t.2.2 (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₁) x =
      Top (Q.EH k r) t.1 t.2.1 t.2.2 (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts f₂) x
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.top_apply', Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.top_apply', Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.EH_apply,
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.EH_apply, ih x hx hxG,
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xa_unit _ _).1 ih,
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xb_unit _ _).1 ih]

theorem AA_congr_open {U : Set (Mat k r)} (hU : IsOpen U) {f₁ f₂ : Mat k r → E}
    (h : ∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) (m : ℕ) (hm : m ≤ r) (u ell : ℂ) {x : Mat k r} (hx : x ∈ U)
    (hxG : x ∈ GV k r) :
    C3.AAop k r m hm u f₁ x = C3.AAop k r m hm u f₂ x ∧ C3.AAvop k r m hm ell f₁ x = C3.AAvop k r m hm ell f₂ x := by
  refine ⟨?_, ?_⟩
  · simp only [C3.AAop]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminor_foldT, qminor_foldT]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [foldT_congr_open hU _ h x hx hxG]
    · rfl
  · simp only [C3.AAvop]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminor_foldT, qminor_foldT]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [foldT_congr_open hU _ h x hx hxG]
    · rfl

end local_

section hyp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem kr_smul (Bs : RealPlaceData k r Wp Wq) (a : Mat k r → ℂ) (G : Mat k r → (Wq →L[ℂ] Wp)) (y : Mat k r)
    (ha : ∀ ξ, InR Bs ξ → a (y * Matrix.of ξ.2 * Matrix.of ξ.1) = a y) :
    Kr Bs (fun g => a g • G g) y = a y • Kr Bs G y := by
  rw [kr_eq, kr_eq, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [ae_inR Bs] with ξ hξ
  simp only [rho_pR, ha ξ hξ, ContinuousLinearMap.smul_comp]
  rw [smul_comm]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem kr_zero (Bs : RealPlaceData k r Wp Wq) (y : Mat k r) : Kr Bs (fun _ => (0 : Wq →L[ℂ] Wp)) y = 0 := by
  simp [Kr]

theorem kr_AA_loc (Bs : RealPlaceData k r Wp Wq) (l : Fin (r + 2)) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ GV k r, Dmin k r Bs.z Bs.z' g l ≠ 0 → Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ H g)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → H g = 0) (m : ℕ) (hm : m ≤ r) (u ell : ℂ)
    {y : Mat k r} (hy : y ∈ GV k r) (hD : Dmin k r Bs.z Bs.z' y l ≠ 0) :
    Kr Bs (C3.AAop k r m hm u H) y = C3.AAop k r m hm u (Kr Bs H) y ∧
      Kr Bs (C3.AAvop k r m hm ell H) y = C3.AAvop k r m hm ell (Kr Bs H) y := by
  set c₀ := Dmin k r Bs.z Bs.z' y l with hc₀
  have hc0 : 0 < ‖c₀‖ := norm_pos_iff.mpr hD
  obtain ⟨χD, ⟨hχs, -, -⟩, hχ1, hχsupp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hD
  have hDc : Continuous (fun g : Mat k r => Dmin k r Bs.z Bs.z' g l) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' l).continuous
  set Ht : Mat k r → (Wq →L[ℂ] Wp) := fun g => χD (Dmin k r Bs.z Bs.z' g l) • H g with hHtdef
  have hHt : CkOn ⊤ (GV k r) Ht := by
    intro g0 hg0
    by_cases hmem : Dmin k r Bs.z Bs.z' g0 l ∈ tsupport χD
    · have hne : Dmin k r Bs.z Bs.z' g0 l ≠ 0 := by
        intro h0
        have := (hχsupp _ hmem).1
        rw [h0, norm_zero] at this
        linarith
      obtain ⟨U, f', hU, hgU, hf', he⟩ := hH g0 hg0 hne
      refine ⟨U, fun g => χD (Dmin k r Bs.z Bs.z' g l) • f' g, hU, hgU, ?_, fun g hg hgG => ?_⟩
      · exact ((hχs.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' l)).contDiffOn).smul hf'
      · show χD (Dmin k r Bs.z Bs.z' g l) • H g = χD (Dmin k r Bs.z Bs.z' g l) • f' g
        rw [he g hg hgG]
    · refine ⟨(fun g => Dmin k r Bs.z Bs.z' g l) ⁻¹' (tsupport χD)ᶜ, fun _ => 0,
        (isClosed_tsupport χD).isOpen_compl.preimage hDc, hmem, contDiffOn_const, fun g hg _ => ?_⟩
      show χD (Dmin k r Bs.z Bs.z' g l) • H g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul]
  have hzt : ∀ g ∈ GV k r, g ∉ C → Ht g = 0 := fun g hg hgC => by
    show χD (Dmin k r Bs.z Bs.z' g l) • H g = 0
    rw [hz g hg hgC, smul_zero]
  set V := {x : Mat k r | dist (Dmin k r Bs.z Bs.z' x l) c₀ < ‖c₀‖ / 4} with hV
  have hVo : IsOpen V := isOpen_lt (hDc.dist continuous_const) continuous_const
  have hyV : y ∈ V := by show dist c₀ c₀ < ‖c₀‖ / 4; rw [dist_self]; positivity
  have hHV : ∀ x ∈ V, x ∈ GV k r → H x = Ht x := by
    intro x hx _
    show H x = χD (Dmin k r Bs.z Bs.z' x l) • H x
    rw [hχ1 _ (le_of_lt hx), one_smul]
  have hKV : ∀ x ∈ V, x ∈ GV k r → Kr Bs H x = Kr Bs Ht x := by
    intro x hx _
    rw [kr_eq, kr_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    simp only [rho_pR, hHtdef, dmin_pR Bs hξ x l]
    rw [hχ1 _ (le_of_lt hx), one_smul]
  have hqV : ∀ ξ, InR Bs ξ → y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ V := by
    intro ξ hξ
    show dist (Dmin k r Bs.z Bs.z' (y * Matrix.of ξ.2 * Matrix.of ξ.1) l) c₀ < ‖c₀‖ / 4
    rw [dmin_pR Bs hξ y l, dist_self]; positivity
  have hqG : ∀ ξ, InR Bs ξ → y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ GV k r := fun ξ hξ =>
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hy hξ.2.1) hξ.1.1
  obtain ⟨hA, hAv⟩ := kr_AA_cpt Bs hHt hC hzt m hm u ell hy
  refine ⟨?_, ?_⟩
  · have e1 : Kr Bs (C3.AAop k r m hm u H) y = Kr Bs (C3.AAop k r m hm u Ht) y := by
      rw [kr_eq, kr_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_inR Bs] with ξ hξ
      simp only [rho_pR]
      rw [(AA_congr_open hVo hHV m hm u ell (hqV ξ hξ) (hqG ξ hξ)).1]
    rw [e1, hA, (AA_congr_open hVo hKV m hm u ell hyV hy).1]
  · have e1 : Kr Bs (C3.AAvop k r m hm ell H) y = Kr Bs (C3.AAvop k r m hm ell Ht) y := by
      rw [kr_eq, kr_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_inR Bs] with ξ hξ
      simp only [rho_pR]
      rw [(AA_congr_open hVo hHV m hm u ell (hqV ξ hξ) (hqG ξ hξ)).2]
    rw [e1, hAv, (AA_congr_open hVo hKV m hm u ell hyV hy).2]

end hyp

theorem right_average_smooth_comm : KrHyp := by
  intro k r Wp Wq _ _ _ _ _ _ Bs j hj H hH hRb y hy hD
  obtain ⟨R, hR⟩ := hRb
  have hC := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
  have hz : ∀ g ∈ B.GV k r, g ∉ {g : B.Mat k r | B.gN g ≤ R} → H g = 0 := by
    intro g hg hgC
    by_contra h
    exact hgC (hR g hg h)
  refine ⟨kr_loc Bs ⟨j, by omega⟩ hH hC hz y hy hD, fun le e => ?_⟩
  by_cases h0 : e = 1 ∧ j = 0
  · have e1 : D.vLet k r Bs.z Bs.z' j hj le e H = fun _ => 0 := by
      funext g; simp [D.vLet, h0]
    rw [e1, kr_zero]
    simp [D.vLet, h0]
  · have hm : j - e ≤ r := by omega
    obtain ⟨hA, hAv⟩ := kr_AA_loc Bs ⟨j, by omega⟩ hH hC hz (j - e) hm ((le.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2)
      ((le.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) hy hD
    rcases le with ⟨b, Y⟩
    cases b
    · have e1 : D.vLet k r Bs.z Bs.z' j hj (false, Y) e H = fun g =>
          (conj (Dmin k r Bs.z Bs.z' g ⟨j, by omega⟩))⁻¹ •
            C3.AAvop k r (j - e) hm ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) H g := by
        funext g; simp [D.vLet, h0]
      rw [e1, kr_smul Bs _ _ y (fun ξ hξ => by rw [dmin_pR Bs hξ y]), hAv]
      simp [D.vLet, h0]
    · have e1 : D.vLet k r Bs.z Bs.z' j hj (true, Y) e H = fun g =>
          (Dmin k r Bs.z Bs.z' g ⟨j, by omega⟩)⁻¹ •
            C3.AAop k r (j - e) hm ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) H g := by
        funext g; simp [D.vLet, h0]
      rw [e1, kr_smul Bs _ _ y (fun ξ hξ => by rw [dmin_pR Bs hξ y]), hA]
      simp [D.vLet, h0]

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLJCommC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_sa (k r o : ℕ) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (6 * (r : ℝ) * (o : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 : 0 ≤ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) := by positivity
  have h2 : 0 ≤ (r : ℝ) * (6 * (r : ℝ) + 1) := by positivity
  refine ⟨by linarith, ?_⟩
  nlinarith

theorem sAJCommC_of_thetaJ (hT : LT.ThetaJ) : SAJCommC := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ hΘ F hFs hFc _hFO U X hU hX hagree y hy hyU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl

  have hAg := QO.agree_qOf (T v).base X F U hX
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    QO.qOf (T v).base.z (T v).base.z' ⁻¹' U with hVdef
  have hVo : IsOpen V := QO.isOpen_qOf _ _ hU
  have hJV : ∀ g ∈ V, g ∈ B.GV S.G.k S.G.r → X g = B.JF (T v).base F g := fun g hg hgG =>
    hAg g ⟨hgG, hg.1⟩ hg.2
  have hq : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hy.1, by rw [← hTT]; exact hy.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base y ∈ V := ⟨hg0.2, by
    show QO.qOf (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ U
    rw [QO.qOf_gq (T v).base hq]; exact hyU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') X :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hX.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base y ∈ UU := ⟨hg0, hg0V⟩

  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs hFc
    (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) +
      (S.G.r : ℝ) * (4 * (S.G.r : ℝ) + 2 * (S.G.k : ℝ)) * (6 * (S.G.r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU
    (thrW_sa S.G.k S.G.r (B.opOrder Θ)) hΘ.1 hΘ.2 hFs hIn hUU hCkF
  have hg0G : B.gq (T v).base y ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun g => Tm.coefAdj g (X g)) (f' := fun g => Tm.coefAdj g (B.JF (T v).base F g))
      (fun g hg hgG => by simp only [hJV g hg hgG]) _ hg0V hg0G]

theorem sAJCommC_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : SAJCommC :=
  sAJCommC_of_thetaJ (LT.thetaJ_of_adjComm hAC)

theorem self_adjoint_commutation_compact : SAJCommC :=
  sAJCommC_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pair

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂]

theorem ssn_ckOn_subset {m : ℕ∞} {UU UU' : Set (Mat k r)} {f : Mat k r → E₁} (h : CkOn m UU f) (hs : UU' ⊆ UU) :
    CkOn m UU' f := fun g hg => h g (hs hg)

theorem ssn_ckOn_pair {m : ℕ∞} {UU : Set (Mat k r)} {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn m UU f₁) (h₂ : CkOn m UU f₂) : CkOn m UU (fun g => (f₁ g, f₂ g)) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => (f₁' g, f₂' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).prodMk (hc₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show (f₁ g, f₂ g) = (f₁' g, f₂' g)
  rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]

theorem ssn_Dw_pair {U : Set (Mat k r)} (hU : IsOpen U) {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn ⊤ (U ∩ GV k r) f₁) (h₂ : CkOn ⊤ (U ∩ GV k r) f₂) :
    ∀ w : List (Bool × Mat k r), (∀ x ∈ w, inLie k r x.2) → ∀ g ∈ GV k r, g ∈ U →
      Dw w (fun g => (f₁ g, f₂ g)) g = (Dw w f₁ g, Dw w f₂ g) := by
  intro w
  induction w with
  | nil => intro _ g _ _; rfl
  | cons x w ih =>
    intro hw g hg hgU
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    show Dx x (Dw w (fun g => (f₁ g, f₂ g))) g = (Dx x (Dw w f₁) g, Dx x (Dw w f₂) g)
    rw [Dx_congr_loc hx hU (f₂ := fun g => (Dw w f₁ g, Dw w f₂ g)) (fun g hg hgU => ih hw' g hg hgU) g hg hgU]
    have c₁ : CkOn 1 (U ∩ GV k r) (Dw w f₁) := CkOn_Dw hw' (sCkOn_mono le_top h₁)
    have c₂ : CkOn 1 (U ∩ GV k r) (Dw w f₂) := CkOn_Dw hw' (sCkOn_mono le_top h₂)
    have d₁ := CkOn_diff hx c₁ ⟨hgU, hg⟩ hg
    have d₂ := CkOn_diff hx c₂ ⟨hgU, hg⟩ hg
    rw [Dx_eq]
    exact (d₁.prodMk d₂).deriv

end pair

theorem datumBd_of_chain (hCh : SSn.ChainBd) : DatumBd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v Bg a a' ι Ψ hBg hD hΨ
  intro ε hε m
  set U : Set (B.Mat S.G.k S.G.r) := {g | ε / 2 < GfP S T v g} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  set K : Set (B.Mat S.G.k S.G.r) := {g | g ∈ B.GV S.G.k S.G.r ∧ ε ≤ GfP S T v g} with hKdef
  have hUG : U ∩ B.GV S.G.k S.G.r ⊆ B.GPos (T v).base := fun g hg =>
    ⟨hg.2, lt_trans (by linarith) hg.1⟩
  have hKU : K ⊆ U := fun g hg => show ε / 2 < GfP S T v g by linarith [hg.2]
  have hKG : K ⊆ B.GV S.G.k S.G.r := fun g hg => hg.1
  set F : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      B.Mat S.G.k S.G.r := fun g => (a g, (a' g, ι g)) with hFdef
  have cka : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a := ssn_ckOn_subset hD.1 hUG
  have cka' : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a' := ssn_ckOn_subset hD.2.1 hUG
  have ckι : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) ι := ssn_ckOn_subset hD.2.2.1 hUG
  have ckF : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) F := ssn_ckOn_pair cka (ssn_ckOn_pair cka' ckι)
  have hFb : ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r), (∀ X ∈ u, unitLie S.G.k S.G.r X) →
      (∀ X ∈ w, unitLie S.G.k S.G.r X) → u.length + w.length ≤ m → ∀ g ∈ K,
        ‖dLR u w F g‖ ≤ C * gN g ^ (Bg * m) := by
    intro m
    obtain ⟨C₁, h₁⟩ := hD.2.2.2.2.1 ε hε m
    obtain ⟨C₂, h₂⟩ := hD.2.2.2.2.2.1 ε hε m
    obtain ⟨C₃, h₃⟩ := hD.2.2.2.2.2.2.1 ε hε m
    refine ⟨C₁ + C₂ + C₃, fun u w hu hw hl g hg => ?_⟩
    have hlie := lie_LR (unit_lie hu) (unit_lie hw)
    have e1 : dLR u w F g = (dLR u w a g, (dLR u w a' g, dLR u w ι g)) := by
      rw [dLR_eq, dLR_eq, dLR_eq, dLR_eq]
      rw [ssn_Dw_pair hUo cka (ssn_ckOn_pair cka' ckι) _ hlie g hg.1 (hKU hg),
        ssn_Dw_pair hUo cka' ckι _ hlie g hg.1 (hKU hg)]
    rw [e1]
    have b₁ := h₁ u w hu hw hl g hg.1 hg.2
    have b₂ := h₂ u w hu hw hl g hg.1 hg.2
    have b₃ := h₃ u w hu hw hl g hg.1 hg.2
    calc ‖(dLR u w a g, (dLR u w a' g, dLR u w ι g))‖
        ≤ ‖dLR u w a g‖ + (‖dLR u w a' g‖ + ‖dLR u w ι g‖) :=
          (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (by positivity),
            (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (norm_nonneg _),
              le_add_of_nonneg_left (norm_nonneg _)⟩).trans (le_add_of_nonneg_left (norm_nonneg _))⟩)
      _ ≤ C₁ * gN g ^ (Bg * m) + (C₂ * gN g ^ (Bg * m) + C₃ * gN g ^ (Bg * m)) := by
          linarith
      _ = (C₁ + C₂ + C₃) * gN g ^ (Bg * m) := by ring
  obtain ⟨C, hC⟩ := hCh S.G.k S.G.r _ _ (fun x => Ψ x.1 x.2.1 x.2.2) hΨ F U K hUo ckF hKU hKG Bg hBg hFb m
  refine ⟨C, fun u w hu hw hl g hg hεg => ?_⟩
  have hgK : g ∈ K := ⟨hg, hεg⟩
  have hO : IsOpen {g : B.Mat S.G.k S.G.r | 0 < GfP S T v g} :=
    isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  have hlie := lie_LR (unit_lie hu) (unit_lie hw)
  have e : dLR u w (datumCoef S T v Ψ a a' ι) g = dLR u w (fun g => (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r => Ψ x.1 x.2.1 x.2.2) (F g)) g := by
    rw [dLR_eq, dLR_eq]
    refine Dw_congr_loc hlie hO (fun g' hg' hg'O => ?_) g hg (show 0 < GfP S T v g by linarith)
    exact datumCoef_pos S T v a a' ι Ψ ⟨hg', hg'O⟩
  rw [e]
  exact hC u w hu hw hl g hgK

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JDAToda

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem omB_eq {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Gauge.OmB Bs = Q.OmPlus k r Bs.z Bs.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this, show Dmin k r Bs.z Bs.z' g ⟨0, by omega⟩ = 1 by unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by show a.val + 1 ≤ r; have := a.isLt; omega)⟩

theorem gg_pos {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hcg : wCell k r (Fin.last r) c * g ∈ Gauge.OmB Bs) :
    0 < GGl k r Bs.z Bs.z' g := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hmin := big_cell_minors_holds k r Bs.z Bs.z' c μ Bs.z_mem Bs.z'_mem
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ Bs.z') Bs.z = zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r Bs.z Bs.z' (bigCell k r c μ) ⟨r, by omega⟩ = ∏ a, c a := by
    have h := hmin.1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    simp
  have hP0 : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r Bs.z Bs.z' (bigCell k r c μ) (Fin.last (r + 1)) =
      (∏ a, c a) * zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    unfold Formalism.QuantumDeterminants.zeta at hzeta
    rw [hr] at hzeta
    rw [← hzeta, mul_div_cancel₀ _ hP0]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r c μ) =
      Complex.normSq (∏ a, c a) * GGl k r Bs.z Bs.z' (B2.embWb k r μ) := by
    unfold Gf GGl
    rw [hlast, hr, Complex.normSq_mul]
    ring
  have h1 := hcg.1
  rw [e, hGf] at h1
  exact pos_of_mul_pos_right h1 (Complex.normSq_nonneg _)

theorem minorCell_of {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hf : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') J) (hLf : LeftEq k r Bs.z 0 (OmPlus k r Bs.z Bs.z') J)
    (hRf : RightEq k r Bs.z' 0 (OmPlus k r Bs.z Bs.z') J) (y : ℂ) (x : (Fin r → ℂ) × Mx k r)
    (hx : x ∈ DomR k r Bs.z Bs.z') :
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) J) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 := by
  have hRR := Formalism.FourierDecayAlt.P.right_rule_derivative
  have hLR := Formalism.FourierDecayAlt.P.left_rule_cell
  have hTC := Formalism.FourierDecayAlt.P.torus_cell
  have hGP := Formalism.FourierDecayAlt.P.gauge_positivity
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl
  have vAB_loc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)),
      (∀ c ∈ OmX r, f₁ c = f₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
      (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
    intro i
    induction i with
    | zero => intro f₁ f₂ h c hc; exact ⟨h c hc, rfl⟩
    | succ i ih =>
      intro f₁ f₂ h c hc
      have hi' := ih f₁ f₂ h
      by_cases hi : i < r
      · simp only [Q.vAB, dif_pos hi]
        refine ⟨?_, ?_⟩
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
          have hev : (Q.vAB r y i).1 f₁ =ᶠ[nhds c] (Q.vAB r y i).1 f₂ := by
            filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc'
            exact (hi' c' hc').1
          simp only [pOp, wirt, if_pos hc, hev.fderiv_eq]
          rw [(hi' c hc).1, (hi' c hc).2]
        · simp only [ciOp]
          rw [(hi' c hc).1]
      · simp only [Q.vAB, dif_neg hi]
        exact hi' c hc
  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    refine (vAB_loc r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1
  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (E := Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D J) J (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

theorem uC_zero (k r : ℕ) (y : ℂ) : Q.uC k r 0 y = y + ((2 * r + k : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.CutMP.JDAToda

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jda_capelli_toda_proof : JDACapToda := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  have hm := JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx
  have hcell := Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg
  simp only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢
  rw [← hm]
  simp only [Q.resG, capA]
  rw [hcell, JDAToda.uC_zero, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP
end
end

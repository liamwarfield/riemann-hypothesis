module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimET
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimTop
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

theorem limTopN_of_decay : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A b₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.CCle A 0 G b₀ → B.CkOn ⊤ (B.GV P.k P.r) G → LimTopN p nn G := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_empty
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn G A b₀ hA hG hGk γ hγ

  have hcut : ∀ (n : ℕ) (g : B.Mat P.k P.r),
      cutN P.k P.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
    rfl
  have hv := hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ G A b₀ (fun n g => cutN P.k P.r n g) hA hG hGk hcut

  have key : ∃ K : ℂ, ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), TBB.Ew p nn F (P.r + 1) [] γ =
      (K * B.hsInner (D.vecV p.T.base p.ν' p.m₀ F γ) (D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
    refine ⟨?_, fun F => ?_⟩
    swap
    unfold TBB.Ew TBB.NP KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hγ, hγ⟩, dite_eq_right (show ¬ (P.r + 1 ≤ P.r) by omega), if_pos rfl, if_pos rfl]
  obtain ⟨K, hK⟩ := key
  simp only [hK]
  have hs : Continuous (fun V : Wq →L[ℂ] Wp => B.hsVec V) := by
    unfold B.hsVec
    fun_prop
  have hcont : Continuous (fun V : Wq →L[ℂ] Wp => (K * B.hsInner V V).re) := by
    unfold B.hsInner
    exact Complex.continuous_re.comp (continuous_const.mul (hs.inner hs))
  exact (hcont.tendsto _).comp hv

theorem limTopN_cut_of_inCC : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → C6.IsCut0 χ →
    (∀ m : ℕ, B.InCC A₀ m F) → B.CkOn ⊤ (B.GV P.k P.r) F →
    ∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε) := by
  obtain ⟨c₃, hc₃⟩ := limTopN_of_decay
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn χ F A₀ hA hχ hF hFk ε hε
  obtain ⟨b₀, hb₀⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hF hε A₀ 0 (by simp)
  exact hc₃ Wp Wq P p nn (D.cutF p.T.base χ F ε) A₀ b₀ hA hb₀
    (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hFk ε)

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LimZeroNPf
open Filter Topology

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

noncomputable section

theorem limZeroN_of_formLimit (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

end

end Formalism.FourierDecayAlt.P.CutBP
end

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem amaps_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) :
    Amaps p f (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq)
      (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq) b 0 := by
  refine ⟨fun γ _ _ => by simp, fun γ _ _ => by simp, fun γ _ _ v => ?_, fun γ _ _ => ?_, fun γ _ _ => ?_⟩
  · simp only [mul_zero, pow_zero, one_mul, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    nlinarith [sq_nonneg ‖v‖]
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le

end place


end

end Formalism.FourierDecayAlt.P.CutBP
end

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimEvT (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR F 0 w [] []).re)

theorem limE_of_partsT (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hEv : LimEvT p χ F Y N) (hPos : LimPos p F Y N)
    (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N := by
  intro w hw hl
  have hE := hEv w hw hl
  have hP := hPos w hw hl
  have hB := hBd w hw hl
  have hN : 0 ≤ TBB.normC nn w := by
    unfold TBB.normC
    exact List.prod_nonneg (fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
      exact hnn _)
  by_cases hb : 0 < (B.beta p.T.base F F).re
  · refine ⟨(p.RR F 0 w [] []).re / (B.beta p.T.base F F).re, div_nonneg hP hb.le, (div_le_iff₀ hb).2 hB, ?_⟩
    rw [div_mul_cancel₀ _ hb.ne']
    exact hE
  · have hb' : (B.beta p.T.base F F).re ≤ 0 := not_lt.1 hb
    have hR0 : (p.RR F 0 w [] []).re = 0 :=
      le_antisymm (hB.trans (mul_nonpos_of_nonneg_of_nonpos hN hb')) hP
    refine ⟨0, le_refl 0, hN, ?_⟩
    rw [zero_mul]
    rw [hR0] at hE
    exact hE

end place


end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem np_top_two (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a a' : C.LPt)
    (ha : D.IsLocPt a P.r) (ha' : D.IsLocPt a' P.r) (w : List C.Letter) (c : ℂ) :
    ((√(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a) * √(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a') / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (P.r + 1) c : ℂ) * p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) =
      TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) := by
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a with hAdef
  set A' := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a' with hA'def
  have hA : 0 ≤ A := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a ha
  have hA' : 0 ≤ A' := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a' ha'
  have hn : ∀ (b : C.LPt), D.IsLocPt b P.r → TBB.nPt P.k P.r (TBB.TTp p) (b ++ [(1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 b *
        C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] := by
    intro b hb
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hb.2,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) b 1 le_rfl (by rw [hb.2]; omega)]
  unfold TBB.NP
  rw [hn a ha, hn a' ha']
  by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
  · have h0 : p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) = 0 :=
      Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w a (a' ++ [(1, c)]) c ha.2 hc2
    rw [h0]
    simp
  · push Not at hc2
    have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
    have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
    have hlast : ∀ b : C.LPt, D.ptGG (TBB.TTp p) (b ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
      intro b
      simp [D.ptGG, D.ptLast]
    have hTT : TBB.TTp p = P.T * P.T' := by
      unfold TBB.TTp
      rw [hT, hT']
    have hfac : ∀ b : C.LPt, C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
        KB.levW P (P.r + 1) c := by
      intro b
      rw [hlast, hTT]
      rw [hT, hT'] at hc2
      simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
      rw [if_pos ⟨by omega, trivial⟩]
      simp
    have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
      rw [← hfac a, hlast]
      simp only [C.nAux]
      rw [if_pos ⟨by omega, trivial⟩]
      have : 0 ≤ Complex.normSq c - TBB.TTp p := by
        unfold TBB.TTp; linarith
      simpa using pow_nonneg this _
    rw [hfac a, hfac a', Real.sqrt_mul hA, Real.sqrt_mul hA']
    have hs : √(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c) = KB.levW P (P.r + 1) c :=
      Real.mul_self_sqrt hlev
    have : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
        √A * √A' / TBB.normC nn w * KB.levW P (P.r + 1) c := by
      have e : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
          √A * √A' / TBB.normC nn w * (√(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c)) := by ring
      rw [e, hs]
    rw [this]
    push_cast
    ring

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

theorem nPt_append_one (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j + 1 ≤ P.r) (c : ℂ) :
    TBB.nPt P.k P.r TT (a ++ [(1, c)]) = TBB.nPt P.k P.r TT a * KB.levW P (j + 1) c := by
  let GG := D.ptGG TT (a ++ [(1, c)])
  let GG' := D.ptGG TT a
  have happend : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l = j + 1 →
      C.nAux P.k P.r GG (fun _ _ => 1) b (l ++ [(1, c)]) =
        C.nAux P.k P.r GG' (fun _ _ => 1) b l * KB.levW P (j + 1) c := by
    intro l
    induction l with
    | nil =>
      intro b hb
      change b + 0 = j + 1 at hb
      rw [Nat.add_zero] at hb
      subst b
      have htop : j + 1 ≠ P.r + 1 := by omega
      have hexp : C.Mlev P.k P.r (j + 1) + 1 - 3 = C.Mlev P.k P.r (j + 1) - 2 := by ring
      simp only [List.nil_append, C.nAux, KB.levW, Nat.add_sub_cancel, htop, false_and,
        if_false, Nat.cast_one, one_mul, mul_one, hexp]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) = j + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [List.cons_append, C.nAux, htop, false_and, if_false, ih (b + s) (by omega), mul_assoc]
  exact happend a 1 (by rw [ha.2, Nat.add_comm])

theorem nPt_nonneg_loc (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j ≤ P.r) :
    0 ≤ TBB.nPt P.k P.r TT a := by
  have hnonneg : ∀ (l : C.LPt) (b : ℕ), b + D.ptSize l ≤ P.r + 1 →
      0 ≤ C.nAux P.k P.r (D.ptGG TT a) (fun _ _ => 1) b l := by
    intro l
    induction l with
    | nil =>
      intro b _
      simp [C.nAux]
    | cons x l ih =>
      rcases x with ⟨s, t⟩
      intro b hb
      change b + (s + D.ptSize l) ≤ P.r + 1 at hb
      have htop : b + s - 1 ≠ P.r + 1 := by omega
      simp only [C.nAux, htop, false_and, if_false, one_mul]
      exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) (ih (b + s) (by omega))
  exact hnonneg a 1 (by rw [ha.2]; omega)

theorem levW_nonneg_low (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (c : ℂ) : 0 ≤ KB.levW P (j + 1) c := by
  simp only [KB.levW]
  rw [if_neg (by omega)]
  exact zpow_nonneg (norm_nonneg _) _

theorem glFibre : GLFibre := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn j hj w hw hN a b ha hb
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hjr : j ≤ P.r := by omega
  obtain ⟨φ, -, hφi, hφ, hφs⟩ := hPS hA Wp Wq P p F j hjr w a b ha hb Cb hCb hF hw.1
  set K : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
    TBB.normC nn w with hK
  have hae : (fun c => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) =ᵐ[volume]
      fun c => (K : ℂ) * φ c := by
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx1.ae_ne_zero] with c hc
    rw [hφ c hc]
    unfold TBB.NP
    rw [nPt_append_one P _ a j ha hj c, nPt_append_one P _ b j hb hj c,
      Real.sqrt_mul (nPt_nonneg_loc P _ a j ha hjr), Real.sqrt_mul (nPt_nonneg_loc P _ b j hb hjr)]
    have hl := Real.mul_self_sqrt (levW_nonneg_low P j hj c)
    rw [hK]
    have : Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (KB.levW P (j + 1) c) *
        (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) * Real.sqrt (KB.levW P (j + 1) c)) / TBB.normC nn w =
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w *
          KB.levW P (j + 1) c := by
      calc _ = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
              TBB.normC nn w * (Real.sqrt (KB.levW P (j + 1) c) * Real.sqrt (KB.levW P (j + 1) c)) := by ring
        _ = _ := by rw [hl]
    rw [this]
    push_cast
    ring
  refine ⟨(hφi.const_mul (K : ℂ)).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  have h0 := hφs 0
  simp only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul,
    Formalism.FourierDecayAlt.P.PBASM.waveG_zero_eq_self] at h0
  rw [h0]
  unfold TBB.NP
  congr 1
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨ha, hb⟩, dite_eq_left hjr]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGram
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem formC_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : PBL.CV (p.T.bs j) y) : p.form j hj w 0 y = 0 := by
  have h := PBL.form_slC p j hj w 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem formC_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : p.form j hj w x 0 = 0 := by
  have h := PBL.form_srC p j hj w x 0 0 1 hx PBL.cv_zero PBL.cv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem formC_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := PBL.form_slC p j hj w 0 x y c PBL.cv_zero hx hy
  rwa [zero_add, formC_zero_l p j hj w y hy, zero_add] at h

theorem formC_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := PBL.form_srC p j hj w x 0 y c hx PBL.cv_zero hy
  rwa [zero_add, formC_zero_r p j hj w x hx, zero_add] at h

end forms

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

abbrev HS (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

abbrev HT (I : Type) [Fintype I] (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : I => HS Wp Wq)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

def vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) : HT I Wp Wq :=
  WithLp.toLp 2 (fun i => ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q))

theorem vecT_apply (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) (i : I) :
    vecT p N c Fi L Q i = ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q) := rfl

theorem inner_vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q Q' : C.LPt) :
    ⟪vecT p N c Fi L Q, vecT p N c Fi L Q'⟫_ℂ =
      ∑ i, (c i : ℂ) * ⟪(omT p N Q : ℂ) • L i (p.V (Fi i) Q), (omT p N Q' : ℂ) • L i (p.V (Fi i) Q')⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ((√(c i) : ℝ) : ℂ) * ((√(c i) : ℝ) : ℂ) = (c i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc i)]
  rw [vecT_apply, vecT_apply, inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul, map_mul]
  rw [← hs]
  ring

def utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x D : ℂ) : HT I Wp Wq :=
  ((‖x‖ ^ (s - 1) : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])

def btT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  if u = 0 then 0 else ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

end place

structure VecHyp {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) : Prop where
  hc : ∀ i, 0 ≤ c i
  hFi : ∀ i, KB.CptCoef p.T.base (Fi i)
  gram : ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
    ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'), (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ
  int : ∀ a : C.LPt, D.IsLocPt a P.r →
    Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)]))
  fibre : ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
    TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])
  cont : ∀ i (m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
    ContinuousOn (fun c : ℂ => (omT p w.length (h ++ [(m, c)]) : ℂ) • p.V (Fi i) (h ++ [(m, c)])) {0}ᶜ

def FieldMemU : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → MemLp (utT p w.length c Fi L s h x) 2 volume

def FieldSup : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → ∫ D, ‖utT p w.length c Fi L s h x D‖ ^ 2 = TBB.Ew p nn F P.r w (h ++ [(s - 1, x⁻¹)])

def FieldMeas : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    StronglyMeasurable (btT p w.length c Fi L s h)

def FieldLoc : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖PBK.bz s (btT p w.length c Fi L s h) z‖ ^ 2) K

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
namespace Formalism.FourierDecayAlt.P.CutBP2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section hs

variable {Wp Wq Wq' Wq'' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  [NormedAddCommGroup Wq''] [InnerProductSpace ℂ Wq''] [FiniteDimensional ℂ Wq'']

lemma hs_le_of_adj_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) (A' : Wq'' →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A'), ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact h _

lemma hs_comp_le_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) :
    ‖B.hsVec (X.comp A)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A), Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  have h1 := (ContinuousLinearMap.adjoint A).le_opNorm
    ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))
  rw [LinearIsometryEquiv.norm_map] at h1
  calc ‖(ContinuousLinearMap.adjoint A) ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))‖ ^ 2
      ≤ (‖A‖ * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖) ^ 2 := by gcongr
    _ = ‖A‖ ^ 2 * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by ring

end hs

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

lemma ttp_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold TTp
  rw [hz, hz']
  rfl

lemma ew_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew q (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (q.V F γ)‖ ^ 2 := by
  have h := Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top q F hγ
  rw [ttp_sh p q hz hz'] at h
  exact h

lemma V_fpmSh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z') {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ)
    (hA : q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ)) :
    q.V (fpmSh (P := P) q f A p₀) γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (APt γ) := by
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  have h := Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow q (fun g => (f g).comp (A g)) p₀ hγ (hGq ▸ hG)
  rw [hA, hGq] at h
  exact h

lemma big_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (n₀ p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z')
    (hA : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ))
    (hn : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖APt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (c : Fin (P.r + 1) → ℂ) :
    Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c) := by
  set γ := bigPt P.r c with hγdef
  by_cases hloc : D.IsLocPt γ (P.r + 1)
  swap
  · have h0q : Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] γ = 0 :=
      Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc q _ hloc
    rw [h0q, Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc p _ hloc, mul_zero]
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  rw [ew_sh p q hz hz' _ hloc, Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hloc]
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  have hnn : 0 ≤ nn := mul_self_nonneg _
  by_cases hG : 0 < Gp p γ
  · rw [V_fpmSh p q f A APt p₀ hz hz' hloc hG (hA γ hloc hG), Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
    have h1 := hs_comp_le_sh (p.V f γ) (APt γ)
    have h2 := hn γ hloc hG
    set X2 := ‖B.hsVec (p.V f γ)‖ ^ 2 with hX2_def
    have hX2 : 0 ≤ X2 := sq_nonneg _
    have hTT : 0 ≤ TTp p := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt p.hP
    have hGd : Gp p γ ≤ ‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2 := by
      show D.ptG (TTp p) P.r γ ≤ _
      unfold D.ptG
      rw [Complex.normSq_eq_norm_sq]
      have := Complex.normSq_nonneg (D.ptMatN γ P.r).det
      nlinarith
    have hTq : 0 ≤ (Tq p)⁻¹ ^ n₀ := by
      have h3 : 0 ≤ (Gp p γ / Tq p) ^ n₀ := le_trans (sq_nonneg _) h2
      rw [div_pow, div_eq_mul_inv, ← inv_pow] at h3
      exact (mul_nonneg_iff_of_pos_left (pow_pos hG n₀)).mp h3
    calc nn * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (APt γ))‖ ^ 2)
        ≤ nn * ((Gp p γ ^ p₀) ^ 2 * (‖APt γ‖ ^ 2 * X2)) := by gcongr
      _ ≤ nn * ((Gp p γ ^ p₀) ^ 2 * ((Gp p γ / Tq p) ^ n₀ * X2)) := by gcongr
      _ = (Gp p γ) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) := by
        rw [div_pow]
        ring
      _ ≤ (‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG.le hGd _) hTq)
          (mul_nonneg hnn hX2)
      _ = _ := by rw [← pow_mul]
  · have hq0 : q.V (fpmSh (P := P) q f A p₀) γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      apply hG
      rw [← hGq]
      exact h
    have hp0 : p.V f γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      exact hG h
    have e1 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq' →L[ℂ] Wp)
    have e2 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq →L[ℂ] Wp)
    simp only [Complex.ofReal_zero, zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at e1 e2
    rw [hq0, hp0, e1, e2, mul_zero, mul_zero]

end sh

theorem normaliser_across_places : NormAtShOfAmaps := by
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hz hz' hzm hzm' hA
  obtain ⟨hAp, hAm, hadj, hnp, hnm⟩ := hA
  refine ⟨fun γ hγ hG => ?_, fun c => big_sh p pp f Ap ApPt n₀ p₀ hz hz' hAp hnp c,
    fun c => big_sh p pm f Am AmPt n₀ p₀ hzm hzm' hAm hnm c⟩
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hγ, ew_sh p pp hz hz' _ hγ, ew_sh p pm hzm hzm' _ hγ,
    V_fpmSh p pp f Ap ApPt p₀ hz hz' hγ hG (hAp γ hγ hG),
    V_fpmSh p pm f Am AmPt p₀ hzm hzm' hγ hG (hAm γ hγ hG),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  have hX := hs_le_of_adj_sh (p.V f γ) (ApPt γ) (AmPt γ)
    ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀) (hadj γ hγ hG)
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  set a1 := ‖B.hsVec ((p.V f γ).comp (ApPt γ))‖ ^ 2 with ha1
  set a2 := ‖B.hsVec ((p.V f γ).comp (AmPt γ))‖ ^ 2 with ha2
  have hnn : 0 ≤ nn := mul_self_nonneg _
  have hcanc : (Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm p₀ 2, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hG.ne')]
  have e : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
      (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
      nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) := by
    rw [show (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
        (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
        nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) *
          ((Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2) by ring, hcanc, mul_one]
  rw [e]
  exact mul_le_mul_of_nonneg_left hX hnn

end

end Formalism.FourierDecayAlt.P.CutBP2
end

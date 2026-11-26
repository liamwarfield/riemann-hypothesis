module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAdjDone
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjJComm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gAJComm_of_thetaJ (hT : LT.ThetaJ) : GAJComm := by
  refine ⟨12, 0, by norm_num, le_rfl, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d Bg hd hBg hΘ _hCoef η F _hη hFs hFg _hFsupp
    U J hU hJ hagree x hx hxU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hBg0 : 0 ≤ Bg := le_trans (by simp) hBg

  have hAg := LT.agreement_on_domain_holds S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base J F U hJ
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    (fun g => Gf S.G.k S.G.r (T v).base.z (T v).base.z' g) ⁻¹' U with hVdef
  have hVo : IsOpen V := (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _).inter
    (hU.preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))
  have hJV : ∀ y ∈ V, y ∈ B.GV S.G.k S.G.r → J y = B.JF (T v).base F y := fun y hy hyG =>
    hAg y ⟨hyG, hy.1⟩ hy.2
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base x ∈ V := ⟨hg0.2, hxU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hJ.1
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
  have hg0UU : B.gq (T v).base x ∈ UU := ⟨hg0, hg0V⟩

  have hThr : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold S.G.k S.G.r
      (B.AB S.G.k S.G.r + 12 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5) -
        Bg * ((B.opOrder Θ : ℕ) : ℝ)) (B.opOrder Θ) := by
    have hAB : (0 : ℝ) ≤ B.AB S.G.k S.G.r := by unfold B.AB; positivity
    have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have ho : (0 : ℝ) ≤ (B.opOrder Θ : ℝ) := Nat.cast_nonneg _
    apply Formalism.FourierDecayAlt.P.CutMP.jdc_thrW (B.opOrder Θ) _ (B.AB S.G.k S.G.r + 30 * (S.G.r : ℝ) + d +
      Bg * ((B.opOrder Θ : ℝ) + 10)) (by positivity)
    linarith
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU hThr hΘ.1 hΘ.2 hFs
    (hFg (B.opOrder Θ)) hUU hCkF

  have hg0G : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg0.1
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
      (f := fun y => Tm.coefAdj y (J y)) (f' := fun y => Tm.coefAdj y (B.JF (T v).base F y))
      (fun y hy hyG => by simp only [hJV y hy hyG]) _ hg0V hg0G]

theorem gAJComm_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : GAJComm :=
  gAJComm_of_thetaJ (LT.thetaJ_of_adjComm hAC)

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdjProof
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsOp
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section op

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem coefLeib {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ UU)
    {a : B.Mat k r → (E →L[ℂ] E')} {Φ : B.Mat k r → E} {d Bg A : ℝ} (hBg : 0 ≤ Bg)
    (ha : B.CkOn ⊤ UU a)
    (hab : ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O → ‖B.dLR u v a g‖ ≤ C * B.gN g ^ (d + Bg * m))
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ)
    (hz : ∀ g ∈ B.GV k r, g ∈ O → Φ g = 0) :
    B.CkOn ⊤ (B.GV k r) (ap a Φ) ∧ ∀ n : ℕ, B.InCC (A - d - Bg * n) n (ap a Φ) := by
  have hP : Pr O UU ⊤ a Φ := ⟨ha, hΦ, hz⟩
  refine ⟨hP.ck hO hcov, fun n => ?_⟩
  choose Ca hCa using hab
  choose cF hcF using hΦg
  set Ka : ℝ := ∑ j ∈ Finset.range (n + 1), |Ca j| with hKa
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKaj : ∀ j ≤ n, |Ca j| ≤ Ka := fun j hj =>
    Finset.single_le_sum (f := fun j => |Ca j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKa0 : 0 ≤ Ka := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCK : 0 ≤ Ka * K := mul_nonneg hKa0 hK0
  refine ⟨2 ^ n * (Ka * K), sCkOn_mono le_top (hP.ck hO hcov), fun u v hu hv hl g hg => ?_⟩
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hP' : Pr O UU ((wL u ++ wR v).length : ℕ) a Φ := hP.mono le_top
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hP'.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    exact mul_nonneg (by positivity) hCK
  · have hb := leib_bound hO hcov g hg (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))
      (wL u ++ wR v) a Φ hlie hP' (by
        intro w₁ w₂ hs₁ hs₂ hl₁₂
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
        rw [len_LR, len_LR] at hl₁₂
        have hl₁ : u₁.length + v₁.length ≤ n := by
          have := hu₁.length_le; have := hv₁.length_le; omega
        have hl₂ : u₂.length + v₂.length ≤ n := by
          have := hu₂.length_le; have := hv₂.length_le; omega
        have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
        have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
        have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
        have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
        set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
        set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
        have b1 : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Ka * B.gN g ^ (d + Bg * L₁) := by
          rw [← dLR_eq]
          have h1 := hCa (u₁.length + v₁.length) u₁ v₁ hu₁' hv₁' le_rfl g hg hgO
          calc _ ≤ Ca (u₁.length + v₁.length) * B.gN g ^ (d + Bg * L₁) := by rw [hL₁]; exact h1
            _ ≤ |Ca (u₁.length + v₁.length)| * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
            _ ≤ Ka * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (hKaj _ hl₁) (Real.rpow_nonneg hp.le _)
        have b2 : ‖Dw (wL u₂ ++ wR v₂) Φ g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
          rw [← dLR_eq]
          have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
          have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
            rw [← Real.rpow_add hp]; simp
          have h4 : ‖B.dLR u₂ v₂ Φ g‖ =
              B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖) := by
            rw [← mul_assoc, e, one_mul]
          rw [h4]
          have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖ ≤ K := by
            refine le_trans ?_ (hKj _ hl₂)
            refine le_trans ?_ (le_abs_self _)
            simpa [hL₂] using h1
          calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
            _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
        have hsum : (d + Bg * L₁) + (Bg * L₂ - A) = d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
          rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
        calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) Φ g‖
            ≤ (Ka * B.gN g ^ (d + Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
              mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hKa0 (Real.rpow_nonneg hp.le _))
          _ = Ka * K * (B.gN g ^ (d + Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
          _ = Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
              rw [← Real.rpow_add hp, hsum])
    have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
    have e2 : B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
      rw [← Real.rpow_add hp]
      refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
      have h6 : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
      nlinarith [mul_le_mul_of_nonneg_left h6 hBg]
    have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
    calc B.gN g ^ (A - d - Bg * n) * ‖Dw (wL u ++ wR v) (ap a Φ) g‖
        ≤ B.gN g ^ (A - d - Bg * n) * (2 ^ (wL u ++ wR v).length *
            (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
      _ = 2 ^ (wL u ++ wR v).length * (Ka * K) *
            (B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
      _ ≤ 2 ^ (wL u ++ wR v).length * (Ka * K) * 1 :=
          mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
      _ ≤ 2 ^ n * (Ka * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem rwG {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) {Φ : B.Mat k r → E} {A Bg : ℝ}
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ) :
    B.CkOn ⊤ (B.GV k r) (B.Rw w Φ) ∧ ∀ m : ℕ, B.InCC (A - Bg * w.length - Bg * m) m (B.Rw w Φ) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hw x (by simpa [wL] using hx))
    simpa using hΦ
  · have h := InCC_Rw (m := m) hw (hΦg (m + w.length))
    have e : A - Bg * ((m + w.length : ℕ) : ℝ) = A - Bg * w.length - Bg * m := by push_cast; ring
    rwa [e] at h

theorem listSumG {ι : Type*} (l : List ι) (f : ι → B.Mat k r → E) {A Bg : ℝ}
    (h : ∀ i ∈ l, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (A - Bg * m) m (f i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => (l.map fun i => f i g).sum) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => (l.map fun i => f i g).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨CkOn_zero, fun m => ⟨0, CCle_zero⟩⟩
  | cons i l ih =>
    have hi := h i (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨CkOn_add hi.1 hl.1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := hi.2 m
    obtain ⟨c', hc'⟩ := hl.2 m
    exact ⟨c + c', CCle_add hc hc'⟩

end op

theorem operator_in_class_holds : OpCCg := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ d Bg A η F hη hBg hSC hCG hF hFg hz
  set O : Set (B.Mat k r) := {g | Gf k r Bs.z Bs.z' g < η} with hOdef
  have hO : IsOpen O := isOpen_lt (Gf_cont _ _) continuous_const
  have hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ B.GPos Bs := by
    intro g hg
    by_cases h : Gf k r Bs.z Bs.z' g < η
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hη (not_lt.1 h)⟩
  have hzO : ∀ g ∈ B.GV k r, g ∈ O → F g = 0 := fun g hg h => hz g hg h
  have hoff : ∀ g, g ∉ O → η ≤ Gf k r Bs.z Bs.z' g := fun g h => not_lt.1 h
  have hab1 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coef g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).1⟩
  have hab2 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coefAdj g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).2⟩
  have hApp : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (ap T.coef (B.Rw T.word F)) := by
    intro T hT
    have hR := rwG T.word_lie hF hFg
    have hzR : ∀ g ∈ B.GV k r, g ∈ O → B.Rw T.word F g = 0 := Rw_vanish hO T.word_lie hzO
    have hc := coefLeib hO hcov hBg (hSC T hT).1 (hab1 T hT) hR.1 hR.2 hzR
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨hc.1, fun m => sInCC_mono ?_ le_rfl (hc.2 m)⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hBg]
  have hAdj : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r)
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) := by
    intro T hT
    have hc := coefLeib hO hcov hBg (hSC T hT).2 (hab2 T hT) hF hFg hzO
    have hR := rwG (w := T.word.reverse) (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hc.1 hc.2
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨CkOn_smul _ hR.1, fun m => ?_⟩
    have h2 := hR.2 m
    rw [List.length_reverse] at h2
    obtain ⟨c, hcc⟩ := sInCC_mono (A := A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) (by
      nlinarith [mul_le_mul_of_nonneg_left hlen hBg]) le_rfl h2
    exact ⟨_, CCle_smul _ hcc⟩
  exact ⟨listSumG Θ (fun T => ap T.coef (B.Rw T.word F)) hApp,
    listSumG Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) hAdj⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_operator_transfer_holds : JALocOp :=
  jALocOp_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds LT.theta_transfer_apply_holds

theorem jALocAdj_of_adjComm (h : FFS.AdjComm) : JALocAdj :=
  jALocAdj_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds (LT.thetaJ_of_adjComm h)

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocDone
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocPhi
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem lphi_log_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (m + 1) Real.log x‖ = (m.factorial : ℝ) * (x ^ (m + 1))⁻¹ := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  have e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]

theorem lphi_deriv_bdd {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {a : ℝ} (ha : 0 < a) (j : ℕ) : ∃ D : ℝ, ∀ x, a < x → ‖iteratedDeriv j φ x‖ ≤ D := by
  choose C hC using hld
  set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hφ
  set s : Set ℝ := Set.Ioi a with hs
  have hso : IsOpen s := isOpen_Ioi
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK
  have hKi : ∀ i ≤ j, |C i| ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set M : ℝ := max 1 a⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set Dd : ℝ := (j.factorial : ℝ) * M with hDd
  refine ⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩
  have hx0 : 0 < x := ha.trans hx
  have hxs : x ∈ s := hx
  have hlogc : ContDiffOn ℝ ∞ Real.log s :=
    Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ)
    hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs
    (C := K) (D := Dd) (fun i hi => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have := hC i x hx0
      unfold LE.ld at this
      rw [Real.norm_eq_abs]
      exact this.trans ((le_abs_self _).trans (hKi i hi)))
    (fun i hi1 hij => by
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [lphi_log_deriv m hx0]
      have hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1) := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hx0.le)
          ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _
      have hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hj1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1) := le_self_pow₀ hj1 (by omega)
      rw [hDd, mul_pow]
      exact mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))
  rw [iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFdB
  have heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    simp [hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]
  rw [← heq.iteratedDeriv_eq]
  exact hFdB

theorem lphi_cut {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) : ∃ (h : ℝ → ℝ) (ε' : ℝ), U.IsCutG ε' h ∧ ∀ x, δ ≤ x → h x = φ x := by
  set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀
  have hχ : C6.IsCut0 χ₀ := by
    refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
      ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩,
      fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩
  obtain ⟨δ₀, hδ₀, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ
  set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ
  have hε : 0 < δ₀ * δ := mul_pos hδ₀ hδ
  have hψ1 : ∀ x, δ ≤ x → ψ x = 1 := fun x hx =>
    hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)
  have hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0 := hcut.2.2
  have hφc := smoothLog_contDiffOn hφ
  refine ⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩,
    fun x hx => by simp [hψ1 x hx]⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < δ₀ * δ
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      simp [hψ0 y hy]
    · have hx0 : 0 < x := lt_of_lt_of_le hε (not_lt.1 hx)
      exact hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))
  · intro q
    set a : ℝ := δ₀ * δ / 2 with ha
    have ha0 : 0 < a := by positivity
    choose cψ hcψ using hcut.2.1
    choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hx : x < δ₀ * δ
    · have e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp [hψ0 y hy]
      rw [e.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simpa using hS0
    · have hxa : a < x := by linarith [not_lt.1 hx]
      set s : Set ℝ := Set.Ioi a with hs
      have hso : IsOpen s := isOpen_Ioi
      have hxs : x ∈ s := hxa
      have hφs : ContDiffOn ℝ ∞ φ s := hφc.mono fun y hy => ha0.trans (show a < y from hy)
      have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn
        hxs (n := q) (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
      refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i| := (hcψ i x).trans (le_abs_self _)
      have h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)| := (hD (q - i) x hxa).trans (le_abs_self _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)

theorem local_phi_transfer_holds : JALocPhi := by
  refine ⟨2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨h, ε', hcut, hhφ⟩ := lphi_cut hφ hld hδ
  obtain ⟨hck, hcc⟩ := gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2
  refine ⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩
  have e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1 := by
    funext g; simp [D.cutF, GfP]
  rw [e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]
  simp only [mulG]
  unfold GfP at hG
  rw [hhφ _ hG]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAdd
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAdd_thr (k r : ℕ) {A : ℝ} (hA : 10 * ((r : ℝ) + 1) * nDim k r ^ 2 ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A := by simpa [nDim] using hA
  have hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_pos hr (lt_of_lt_of_le one_pos hn2)]

theorem local_additivity_transfer : JALocAdd := by
  refine ⟨10, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hThr := locAdd_thr S.G.k S.G.r hA
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨F', hF1', hF2', hF3'⟩ := hJ'.2 δ hδ
  refine ⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c, hc⟩ := hF2 m
    obtain ⟨c', hc'⟩ := hF2' m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
    have hg := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have h0 : B.InCC A 0 F := by simpa using hF2 0
    have h0' : B.InCC A 0 F' := by simpa using hF2' 0
    have i1 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg
    have i2 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg
    have e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) =
        ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS := fun G => rfl
    rw [Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]
    congr 1
    funext p
    simp [JF.integrand, B.rho, smul_add]

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalSquareIntegrableTransfer
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem local_square_integrable_transfer : LocalSquareIntegrableTransfer := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A ε J e hFr hBg hε hA hJ π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  obtain ⟨F, -, hCC, hFJ⟩ := hJ.2 ε hε
  set A' := A - 5 * Bg with hA'
  have hC5 : ∀ m, m ≤ 5 → B.InCC A' m F := by
    intro m hm
    refine inCC_antiA ?_ (hCC m)
    have : (m : ℝ) ≤ 5 := by exact_mod_cast hm
    rw [hA']; nlinarith

  have hAB : B.AB S.G.k S.G.r ≤ A' := by
    have := jd_AB_le S.G.k S.G.r
    rw [hA']; linarith
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A' hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hC5 4 (by norm_num)
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hC5 5 le_rfl) (hC5 5 le_rfl) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ.1 π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  have hGm : Measurable (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT => MA.Gq (D.parOf S v) q) := by
    unfold MA.Gq; fun_prop
  have hs : MeasurableSet {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q} :=
    measurableSet_le measurable_const hGm
  refine ⟨(((jd_evQ_meas _ _).norm).pow 2).restrict, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q ∈ {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q},
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2) ≤ H q.1 := by
    intro q hqs
    refine ENNReal.ofReal_le_ofReal ?_
    have hGg : ε ≤ GfP S T v (B.gq (T v).base q.1) := by
      have h1 := Formalism.FourierDecayAlt.P.CutMP.cutTr_Gf_gq (T v).base q.2.1 (by rw [hTT]; exact q.2.2)
      have h2 : GfP S T v (B.gq (T v).base q.1) = MA.Gq (D.parOf S v) q := by
        unfold GfP MA.Gq; rw [h1, hTT]
      rw [h2]; exact hqs
    have hJF : J (B.gq Db q.1) = B.JF Db F (B.gq Db q.1) := hFJ q.1 q.2 hGg
    have hq : MA.evQ (D.parOf S v) (trJ S T v e J π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := by
      rw [← hJF]; exact congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          ∂(MA.mu0 (D.parOf S v).r (D.parOf S v).TT).restrict
            {q | ε ≤ MA.Gq (D.parOf S v) q}
        ≤ ∫⁻ q in {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q}, H q.1
            ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT := setLIntegral_mono' hs p1
      _ ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jALocCC_of_op (h2 : JALocOp) (h3 : JALocAdj) : JALocCC :=
  jALocCC_of_leaves h2 h3 local_phi_transfer_holds local_additivity_transfer local_square_integrable_transfer

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdj
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGACutGraded
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

theorem graded_truncation_action_holds : GACutGraded := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs χ₀ hχ ε A Bg F hε hBg hF hFg
  obtain ⟨δ, -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hε
  exact Formalism.FourierDecayAlt.P.CutMP.JA.gcut_graded Bs.z Bs.z' (fun x => χ₀ (x / ε)) (δ * ε) hcut
    (by linarith) hF hFg

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAGroupAdj_of_jComm (h : GA.GAJComm) : JAGroupAdj :=
  GA.jAGroupAdj_of_leaves GA.graded_truncation_action_holds h GA.group_action_pairing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_adjoint_transfer_holds : JALocAdj := jALocAdj_of_adjComm FFS.adjoint_commutation_holds

theorem local_class_transfer_holds : JALocCC := jALocCC_of_op local_operator_transfer_holds local_adjoint_transfer_holds

theorem group_action_commutation_holds : GA.GAJComm := GA.gAJComm_of_adjComm FFS.adjoint_commutation_holds

theorem group_adjoint_transfer_holds : JAGroupAdj := jAGroupAdj_of_jComm group_action_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQOpen
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

theorem jAdjTrQQ_of_open (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) (h12 : JAGroupAdj) (h13 : JALocCC) :
    JAdjTrQQ :=
  jAdjTrQQ_of_leaves quadratic_assembly_holds h1 h7 h11 h12 h13 smooth_forms_stability_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAdjTrQQ_of_three (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) : JAdjTrQQ :=
  jAdjTrQQ_of_open h1 h7 h11 group_adjoint_transfer_holds local_class_transfer_holds

end Formalism.FourierDecayAlt.P.CutMP.JA

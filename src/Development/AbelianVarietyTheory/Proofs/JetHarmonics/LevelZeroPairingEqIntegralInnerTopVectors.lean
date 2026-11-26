module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompact
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliFoldAddSmul
namespace GlobalTheory

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem capelliFold_good {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) :
    ∀ w : List (Bool × ℝ), Formalism.FourierDecayAlt.P.Qx2.Good k r 0 Set.univ
      (fun f : B.Mat k r → E => List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) f w)
  | [] => Formalism.FourierDecayAlt.P.Qx2.good_id
  | a :: w => (Formalism.FourierDecayAlt.P.Dx1.LZ.good_Tc (k := k) (r := r) (E := E) s (a.2 : ℂ)).comp (capelliFold_good s w)

theorem capelliFold_add_smul :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ))
      (a : ℂ) (X Z : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) Z →
      ∀ g ∈ B.GV k r,
        (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • Z) w) g =
          (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) g +
            a • (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (Z) w) g := by
  intro k r Wp Wq _ _ _ _ _ _ s w a X Z hX hZ g hg
  exact (capelliFold_good s w).lin X Z a (Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck hX)
    (Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck hZ) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinear
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_foldCapelli_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA a X X' Z Z' hX hX' hXc hX'c hZ hZ'
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  obtain ⟨c, hc⟩ := hXc
  obtain ⟨c', hc'⟩ := hX'c
  have h1 : B.InCC A 5 _ := ⟨_, hK A c X hX hc⟩
  have h2 : B.InCC A 5 _ := ⟨_, hK A c' X' hX' hc'⟩
  refine ⟨?_, (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA hZ hZ' h1 a).2⟩
  rw [← (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA h1 h2 hZ a).1]
  exact Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr Bs (fun g hg => GlobalTheory.capelliFold_add_smul k r Wp Wq s w a X X' hX hX' g hg)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinearStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  first | exact @GlobalTheory.beta_foldCapelli_sesquilinear | exact GlobalTheory.beta_foldCapelli_sesquilinear | (intros; apply GlobalTheory.beta_foldCapelli_sesquilinear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompactApproximantsConvergeDecayClass
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompactApproximantsConvergeDecayClass
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem cutF_approximants_ccle :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs χ f A₀ ε A mm hχ hε _ hfA hA
  obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hχ hfA hε (A + 1) mm hA
  generalize D.cutF Bs χ f ε = H at hb ⊢
  have hb0 : 0 ≤ b := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hb
  have hb' : B.CCle A mm H b := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := k) (r := r) (E := Wq →L[ℂ] Wp) mm
  have hψ : ∀ n : ℕ, B.CCle A mm (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g)
      (Kp * b / ((n : ℝ) + 1)) := fun n => by
    have h := hKp ((n : ℝ) + 1) (by positivity) (A + 1) H b hb
    rwa [add_sub_cancel_right] at h
  have hc : ∀ (n : ℕ) (g : B.Mat k r), ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)
        = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := fun n g =>
    Formalism.FourierDecayAlt.P.PBE.cut_eq (fun (n : ℕ) (g : B.Mat k r) => ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (fun _ _ => rfl) n g
  have hKb : 0 ≤ Kp * b := mul_nonneg hKp0 hb0
  refine ⟨b + Kp * b, by positivity, Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (by linarith), fun n => ⟨?_, ?_⟩⟩
  · have e : (fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g)
          = fun g => H g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [hc n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * b / ((n : ℝ) + 1) ≤ Kp * b := div_le_self hKb (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  · have e : ((fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) - H)
          = fun g => (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [Pi.sub_apply, hc n g, sub_smul, one_smul, neg_one_smul, sub_sub_cancel_left]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n)) ?_
    simp only [norm_neg, norm_one, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompactApproximantsConvergeDecayClassStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_compact_approximants_converge_decay_class : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  first | exact @GlobalTheory.cutF_approximants_ccle | exact GlobalTheory.cutF_approximants_ccle | (intros; apply GlobalTheory.cutF_approximants_ccle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLe
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_capelliFold_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA
  obtain ⟨_, _, _, ⟨C, hC⟩, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq Bs A hA
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  refine ⟨|C| * K, mul_nonneg (abs_nonneg _) hK0, ?_⟩
  intro X Z c c' hX hc hc'
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hc0' : 0 ≤ c' := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc'
  have hF := hK A c X hX hc
  have h := (hC _ _ _ _ ⟨_, hF⟩ ⟨_, hc'⟩ (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hF)
    (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hc')).2.2
  refine h.trans ?_
  rw [mul_assoc |C| K c]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hK0 hc0)) hc0'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLeStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  first | exact @GlobalTheory.beta_capelliFold_norm_le | exact GlobalTheory.beta_capelliFold_norm_le | (intros; apply GlobalTheory.beta_capelliFold_norm_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBound
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelZeroApprox

theorem ccle_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F F' : B.Mat k r → E} {c c' : ℝ} (h : B.CCle A m F c) (h' : B.CCle A m F' c') :
    B.CCle A m (F - F') (c + c') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rw [e] at h1
  simpa using h1

theorem ckOn_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U : Set (B.Mat k r)}
    {F F' : B.Mat k r → E} (h : B.CkOn m U F) (h' : B.CkOn m U F') : B.CkOn m U (F - F') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rwa [e] at h1

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_bump_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : B.Mat k r → E} (h : B.CkOn ⊤ (B.GV k r) H) (n : ℕ) :
    B.CkOn ⊤ (B.GV k r) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) := by
    have e : (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) = fun g => 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
      funext g
      rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
      rfl
    rw [e]
    exact contDiff_const.sub (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hcs h
end

theorem threshold (k r N l : ℕ) (hl : l ≤ N) :
    B.AB k r + 1 + 2 * ((r : ℝ) + 1) * ((5 + l * (2 * r + k + 1) : ℕ) : ℝ) ≤
      20 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  push_cast
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlN : (l : ℝ) ≤ N := by exact_mod_cast hl
  set ρ : ℝ := (r : ℝ) + 1 with hρ
  set ν : ℝ := 2 * (r : ℝ) + k + 1 with hν
  have hρ1 : 1 ≤ ρ := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hkr : (k : ℝ) + r ≤ ν := by linarith
  have h4 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have h2 : ν ≤ ν ^ 2 := le_self_pow₀ hν1 (by norm_num)
  have h3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hS : (l : ℝ) * ν + ν ≤ N * ν ^ 2 + ν ^ 3 :=
    add_le_add (mul_le_mul hlN h2 (by linarith) (by linarith)) h3
  have hlν : 0 ≤ (l : ℝ) * ν := by positivity
  have h5 : 20 * ρ * ((l : ℝ) * ν + ν) ≤ 20 * ρ ^ 4 * (N * ν ^ 2 + ν ^ 3) :=
    mul_le_mul (by linarith) hS (by linarith) (by positivity)
  refine le_trans ?_ h5
  have a1 : ((k : ℝ) + r) * ρ ≤ ν * ρ := mul_le_mul_of_nonneg_right hkr (by linarith)
  have a2 : ρ ≤ ν * ρ := le_mul_of_one_le_left (by linarith) hν1
  have a3 : 0 ≤ ρ * ((l : ℝ) * ν) := by positivity
  nlinarith

theorem beta_approx : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  refine ⟨20, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs s w χ f A N hχ hf hfA hA hw ε₁ ε₂ h₁ h₂
  have hth := (threshold k r N w.length hw).trans hA
  obtain ⟨K₁, hK₁, hH₁, hX₁⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₁ (B.AB k r) _ hχ h₁ hf hfA hth
  obtain ⟨K₂, hK₂, hH₂, hX₂⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₂ (B.AB k r) _ hχ h₂ hf hfA hth
  obtain ⟨C, hC, hbd⟩ := GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le k r Wp Wq Bs s w (B.AB k r) le_rfl
  have hsq := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear k r Wp Wq Bs s w (B.AB k r) le_rfl 1
  have hc₁ := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε₁
  have hx₁ := ckOn_bump_smul hc₁
  have lo : ∀ {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ},
      B.CCle (B.AB k r) (5 + w.length * (2 * r + k + 1)) F c → B.CCle (B.AB k r) 5 F c :=
    fun h => Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (Nat.le_add_right _ _) h
  generalize D.cutF Bs χ f ε₁ = H₁ at *
  generalize D.cutF Bs χ f ε₂ = H₂ at *
  set X₁ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₁ g with hX₁def
  set X₂ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₂ g with hX₂def
  set b : (B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp)) → ℂ := fun X Z =>
    B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) X w) Z with hb
  change ∀ n, B.CCle _ _ (X₁ n) K₁ ∧ B.CCle _ _ (X₁ n - H₁) _ at hX₁
  change ∀ n, B.CCle _ _ (X₂ n) K₂ ∧ B.CCle _ _ (X₂ n - H₂) _ at hX₂
  change ∀ n, B.CkOn _ _ (X₁ n) at hx₁
  change ∀ X Z c c', _ → _ → _ → ‖b X Z‖ ≤ _ at hbd
  change ∀ X X' Z Z', _ → _ → _ → _ → _ → _ → b (X + (1 : ℂ) • X') Z = b X Z + 1 * b X' Z ∧
    b X (Z + (1 : ℂ) • Z') = b X Z + (starRingEnd ℂ) 1 * b X Z' at hsq
  change Tendsto (fun n => b (X₁ n) (X₂ n)) atTop (𝓝 (b H₁ H₂)) ∧
    ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖b (X₁ n - X₁ m) (X₁ n - X₁ m)‖ ≤ K / ((n : ℝ) + 1)
  clear_value X₁ X₂ b
  constructor
  · have key : ∀ n : ℕ, ‖b (X₁ n) (X₂ n) - b H₁ H₂‖ ≤ 2 * C * K₁ * K₂ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hd := ckOn_sub (hx₁ n) hc₁
      have e1 := (hsq H₁ (X₁ n - H₁) (X₂ n) (X₂ n) hc₁ hd ⟨_, hH₁⟩ ⟨_, (hX₁ n).2⟩ ⟨_, lo (hX₂ n).1⟩
        ⟨_, lo (hX₂ n).1⟩).1
      have e2 := (hsq H₁ H₁ H₂ (X₂ n - H₂) hc₁ hc₁ ⟨_, hH₁⟩ ⟨_, hH₁⟩ ⟨_, lo hH₂⟩ ⟨_, lo (hX₂ n).2⟩).2
      simp only [one_smul, add_sub_cancel, one_mul, map_one] at e1 e2
      have b1 := hbd _ _ _ _ hd (hX₁ n).2 (lo (hX₂ n).1)
      have b2 := hbd _ _ _ _ hc₁ hH₁ (lo (hX₂ n).2)
      have e : b (X₁ n) (X₂ n) - b H₁ H₂ = b (X₁ n - H₁) (X₂ n) + b H₁ (X₂ n - H₂) := by
        rw [e1, e2]; ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) key ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C * K₁ * K₂)
  · refine ⟨4 * C * K₁ * K₁, fun n m hnm => ?_⟩
    have hd := ckOn_sub (hx₁ n) (hx₁ m)
    have c1 := ccle_sub (hX₁ n).2 (hX₁ m).2
    rw [sub_sub_sub_cancel_right] at c1
    have hle : K₁ / ((m : ℝ) + 1) ≤ K₁ / ((n : ℝ) + 1) := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact div_le_div_of_nonneg_left hK₁ (by positivity) (by linarith)
    have c2 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c c1 (add_le_add_right hle (K₁ / ((n : ℝ) + 1)))
    have c3 := ccle_sub (hX₁ n).1 (hX₁ m).1
    refine (hbd _ _ _ _ hd c2 (lo c3)).trans (le_of_eq ?_)
    ring

end GlobalTheory.LevelZeroApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBoundStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  first | exact @GlobalTheory.LevelZeroApprox.beta_approx | exact GlobalTheory.LevelZeroApprox.beta_approx | (intros; apply GlobalTheory.LevelZeroApprox.beta_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolarisationOnSubspace
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem polarisation_on_subspace : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : V → Prop) (B T : V → V → ℂ), (∀ (a : ℂ) x y, S x → S y → S (x + a • y)) → (∀ (a : ℂ) x y, S x → S y → B (x + a • y) (x + a • y) = B x x + a * B y x + (starRingEnd ℂ) a * B x y + a * (starRingEnd ℂ) a * B y y) → (∀ (a : ℂ) x y, S x → S y → T (x + a • y) (x + a • y) = T x x + a * T y x + (starRingEnd ℂ) a * T x y + a * (starRingEnd ℂ) a * T y y) → (∀ x, S x → B x x = T x x) → ∀ x y, S x → S y → B x y = T x y := by
  intro V _ _ S B T hS hB hT hd x y hx hy
  have key : ∀ a : ℂ, a * B y x + (starRingEnd ℂ) a * B x y = a * T y x + (starRingEnd ℂ) a * T x y := by
    intro a
    have h := hd _ (hS a x y hx hy)
    rw [hB a x y hx hy, hT a x y hx hy, hd x hx, hd y hy] at h
    linear_combination h
  have h1 := key 1
  have h2 := key Complex.I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2
    - ((B y x - T y x - B x y + T x y) / 2) * Complex.I_mul_I

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectors
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVecPol

theorem integrable_inner_of_memLp {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun c => inner ℂ (u c) (v c)) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with c h1 h2
  rw [h1, h2]

theorem integral_inner_expand {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (a : ℂ) :
    ∫ c, inner ℂ (u c + a • v c) (u c + a • v c) ∂μ =
      ∫ c, inner ℂ (u c) (u c) ∂μ + a * ∫ c, inner ℂ (u c) (v c) ∂μ +
        (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (u c) ∂μ +
        a * (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (v c) ∂μ := by
  have h1 := integrable_inner_of_memLp hu hu
  have h2 := (integrable_inner_of_memLp hu hv).const_mul a
  have h3 := (integrable_inner_of_memLp hv hu).const_mul ((starRingEnd ℂ) a)
  have h4 := (integrable_inner_of_memLp hv hv).const_mul (a * (starRingEnd ℂ) a)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  have h12 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c)) μ := h1.add h2
  have h123 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c) +
      (starRingEnd ℂ) a * inner ℂ (v c) (u c)) μ := h12.add h3
  rw [← integral_add h12 h3, ← integral_add h123 h4]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring

theorem beta_eq_integral_inner_tv : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H H' w hD hH hH' hw
  have hS : ∀ (a : ℂ) (x y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base x → KB.CptCoef p.T.base y →
      KB.CptCoef p.T.base (x + a • y) := fun a x y hx hy => Formalism.FourierDecayAlt.P.PBL.cpt_add hx (Formalism.FourierDecayAlt.P.PBL.cpt_smul a hy)
  have hcc : ∀ x : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base x → ∀ (A : ℝ) (m : ℕ), B.InCC A m x := by
    intro x hx
    obtain ⟨ε, -, h⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hx
    exact h.2.1
  refine GlobalTheory.polarisation_on_subspace (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (KB.CptCoef p.T.base)
    (fun x y => B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) x w) y)
    (fun x y => ∫ c, inner ℂ (tv p y w c) (tv p x w c)) hS ?_ ?_ ?_ H H' hH hH'
  · intro a x y hx hy
    have hs := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w (B.AB P.k P.r) le_rfl a
    have hz := hS a x y hx hy
    have e1 := (hs x y (x + a • y) x hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc _ hz _ _) (hcc x hx _ _)).1
    have e2 := (hs x y x y hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    have e3 := (hs y y x y hy.1 hy.1 (hcc y hy _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    beta_reduce
    rw [e1, e2, e3]
    ring
  · intro a x y hx hy
    have hx2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).1
    have hy2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb y w hD hy hw).1
    have e : ∀ c, tv p (x + a • y) w c = tv p x w c + a • tv p y w c := fun c =>
      GlobalTheory.TopVec.tv_add_smul Wp Wq P p Cb a x y w c hD hw hx hy
    beta_reduce
    simp only [e]
    exact integral_inner_expand hx2 hy2 a
  · intro x hx
    beta_reduce
    rw [(GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    simp

end GlobalTheory.TopVecPol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqBigCellIntegralTopVectorsStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  first | exact @GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | exact GlobalTheory.TopVecPol.beta_eq_integral_inner_tv | (intros; apply GlobalTheory.TopVecPol.beta_eq_integral_inner_tv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TvApproxTendstoL2Cutoff
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoTopVectorCompactApproximantsBigCell
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoTopVectorCompactApproximantsBigCell
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem vecV_theta_approx_tendsto (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ w, KB.CutWord P p.l0 w → w.length ≤ N → ∀ (e : Wd.Ix (Fin w.length)) (q : C.LPt), Tendsto
        (fun n => D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (fun g => cut n g • D.cutF p.T.base χ f ε g)) q) atTop
        (𝓝 (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (D.cutF p.T.base χ f ε)) q)) := by
  obtain ⟨c₂, hc₂⟩ := vecV_cut_op
  refine ⟨5 * max Cb 0 + max Cb 0 ^ 2 + 1 + |c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut w hw hwN e q
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb0 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  have hcut' : ∀ n g, cut n g = 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [hcut n g]
    simp [P.JCx2.pdPsi, P.JCx2.pdPhi, P.JCx2.pdChi, P.JCx2.pdSq]
  have hFck : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF p.T.base χ f ε) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  have hFv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < ε * δ → D.cutF p.T.base χ f ε g = 0 := by
    intro g hg
    show ((χ (Gf P0.k P0.r p.T.base.z p.T.base.z' g / ε) : ℝ) : ℂ) • f g = 0
    rw [hχ0 _ (by rw [div_lt_iff₀ hε]; linarith), Complex.ofReal_zero, zero_smul]
  obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
  have hcongr : ∀ G, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e G) q =
      D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) q :=
    fun G => vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
  simp only [hcongr]
  have ho' : (o : ℝ) ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
    calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
      _ ≤ max Cb 0 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
        rw [hXn]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
          (by linarith)
      _ ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hwN) hCb0) (by linarith)
  have hκ' : (κ : ℝ) ≤ max Cb 0 * ((P0.r : ℝ) + 1) * o :=
    hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      (Nat.cast_nonneg _))
  have hthr := thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 0) c₂ o κ A hr0 hrX hN0 hCb0
    (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
  obtain ⟨bF, hbF⟩ := cutF_inCC p.T.base hχ hfA hε (A - 2 * ((P0.r : ℝ) + 1) * o) o (by linarith)
  exact hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ q _ cut nf fib o κ Dop (ε * δ)
    (A - 2 * ((P0.r : ℝ) + 1) * o) bF hfib hIn (mul_pos hε hδ) hFv hFck hbF hcut'
    (by rw [hXn]; linarith [hthr])

theorem tv_approx_tendsto : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, Tendsto (fun n : ℕ => tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w c) atTop (𝓝 (tv p (D.cutF p.T.base χ f ε) w c)) := by
  intro Cb
  obtain ⟨Cc, hC⟩ := vecV_theta_approx_tendsto Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ A N w hDD hχ hf hfA hA hw hwN ε hε c
  have h := hC Wp Wq P0 p f χ ε A N _ hDD hχ hε hf hfA hA (fun _ _ => rfl) w hw hwN
  unfold tv
  refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  apply Tendsto.const_smul
  refine (P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_
  exact ((continuous_const.clm_comp continuous_id).tendsto _).comp (h x.1 (TBB.bigPt P0.r c))

end GlobalTheory.TopVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoTopVectorCompactApproximantsBigCellStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_topVector_compactApproximants_bigCell : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, Tendsto (fun n : ℕ => tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w c) atTop (𝓝 (tv p (D.cutF p.T.base χ f ε) w c)) := by
  first | exact @GlobalTheory.TopVec.tv_approx_tendsto | exact GlobalTheory.TopVec.tv_approx_tendsto | (intros; apply GlobalTheory.TopVec.tv_approx_tendsto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemLpTwoAndTendstoOfCauchyOfAeTendsto
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem eLpNorm_two_le_ofReal_sqrt_of_integral_le {X : Type} [MeasurableSpace X] {μ : Measure X} {E : Type}
    [NormedAddCommGroup E] {f : X → E} (hf : MemLp f 2 μ) {c : ℝ}
    (h : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c) : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt c) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  have h3 : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  rw [h3, Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h (by norm_num)

theorem memLp_two_and_tendsto_of_cauchy_of_ae_tendsto :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] (v : ℕ → X → E) (u : X → E) (K : ℝ), (∀ n, MemLp (v n) 2 μ) → (∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (u x))) → (∀ n m : ℕ, n ≤ m → ∫ x, ‖v n x - v m x‖ ^ 2 ∂μ ≤ K / ((n : ℝ) + 1)) → MemLp u 2 μ ∧ Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) := by
  intro X _ μ E _ v u K hv hlim hC
  have hu : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hv n).aestronglyMeasurable) hlim
  have hb : ∀ n, eLpNorm (v n - u) 2 μ ≤ ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1))) := by
    intro n
    have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := μ) (p := 2) (f := fun m => v n - v m)
      (fun m => ((hv n).sub (hv m)).aestronglyMeasurable) (v n - u)
      ((hv n).aestronglyMeasurable.sub hu)
      (by
        filter_upwards [hlim] with x hx
        exact tendsto_const_nhds.sub hx)
    refine hF.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact eLpNorm_two_le_ofReal_sqrt_of_integral_le ((hv n).sub (hv m)) (hC n m hm)
  refine ⟨?_, ?_⟩
  · have h0 : MemLp (v 0 - u) 2 μ :=
      memLp_iff.mpr ((hb 0).trans_lt ENNReal.ofReal_lt_top)
    have := (hv 0).sub h0
    simpa using this
  · have h1 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (h1.sqrt)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => bot_le) hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TvApproxTendstoL2Cutoff
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem tv_approx_tendsto_L2 : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (∀ n : ℕ, MemLp (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w) 2 volume) ∧ MemLp (tv p (D.cutF p.T.base χ f ε) w) 2 volume ∧ Tendsto (fun n : ℕ => eLpNorm (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w - tv p (D.cutF p.T.base χ f ε) w) 2 volume) atTop (𝓝 0) := by
  intro hP Cb
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.tendsto_topVector_compactApproximants_bigCell Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hCb hχ hf hA hthr hw hlen ε hε
  have hpos : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have hmono : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro C hC
    refine le_trans ?_ hthr
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hC hpos
  obtain ⟨-, K, hK⟩ := h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hA (hmono _ (le_max_left _ _)) hlen
    ε ε hε hε
  have hpt := h₂ Wp Wq P p f χ A N w hCb hχ hf hA (hmono _ (le_max_right _ _)) hw hlen ε hε
  have hcpt := Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P p.T.base hχ hf hε
  have hL : ∀ n : ℕ, MemLp (tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) 2 volume := fun n =>
    (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb _ w hCb (hcpt n) hw).1
  refine ⟨hL, ?_⟩
  refine GlobalTheory.memLp_two_and_tendsto_of_cauchy_of_ae_tendsto _ volume _
    (fun n => tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) _ K hL (Eventually.of_forall hpt) ?_
  intro n m hnm
  have hsub : KB.CptCoef p.T.base
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) :=
    Formalism.FourierDecayAlt.P.PBN.cpt_sub p.T.base (hcpt n) (hcpt m)
  have hlin : ∀ c, tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w c -
      tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c =
      tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c := by
    intro c
    have h := GlobalTheory.T.topVector_add_smul_compactCoefficients Wp Wq P p Cb (-1) _ _ w c hCb hw (hcpt n) (hcpt m)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    exact h.symm
  have hβ := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb _ w hCb hsub hw).2
  have hb : ‖B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G)
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w)
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m)‖ ≤
      K / ((n : ℝ) + 1) := hK n m hnm
  rw [hβ, Complex.norm_real] at hb
  simp only [hlin]
  exact (le_abs_self _).trans hb

end GlobalTheory.TopVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TvApproxTendstoL2CutoffStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tv_approx_tendsto_L2_cutoff : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (∀ n : ℕ, MemLp (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w) 2 volume) ∧ MemLp (tv p (D.cutF p.T.base χ f ε) w) 2 volume ∧ Tendsto (fun n : ℕ => eLpNorm (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w - tv p (D.cutF p.T.base χ f ε) w) 2 volume) atTop (𝓝 0) := by
  first | exact @GlobalTheory.TopVec.tv_approx_tendsto_L2 | exact GlobalTheory.TopVec.tv_approx_tendsto_L2 | (intros; apply GlobalTheory.TopVec.tv_approx_tendsto_L2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoIntegralInnerOfTendstoELpNormTwo
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by
  intro X _ μ E _ _ v v' u u' hv hv' hu hu' h h'
  have key : ∀ (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      ∫ x, inner ℂ (f x) (g x) ∂μ = inner ℂ (hf.toLp f) (hg.toLp g) := by
    intro f g hf hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have h1 : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).2 h
  have h2 : Tendsto (fun n => (hv' n).toLp (v' n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v' hv' u' hu').2 h'
  rw [key u' u hu' hu]
  simp_rw [fun n => key (v' n) (v n) (hv' n) (hv n)]
  exact h2.inner h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectors
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_word_cutF_eq_integral_inner_tv :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  intro hA Cb
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.tv_approx_tendsto_L2_cutoff hA Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hCC hth hw hlen ε₁ ε₂ hε₁ hε₂
  have hmono : ∀ Cc : ℝ, Cc ≤ max C₁ C₂ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro Cc hC
    refine le_trans ?_ hth
    gcongr
  have hL := (h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hCC (hmono _ (le_max_left _ _)) hlen
    ε₁ ε₂ hε₁ hε₂).1
  obtain ⟨a₁, b₁, c₁⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₁ hε₁
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₂ hε₂
  have hR := tendsto_integral_inner_of_tendsto_eLpNorm_two _ _ _ _ _ _ _ a₁ a₂ b₁ b₂ c₁ c₂
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have hc : ∀ ε : ℝ, 0 < ε → KB.CptCoef p.T.base (fun g : B.Mat P.k P.r =>
      ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) •
        D.cutF p.T.base χ f ε g) := fun ε hε =>
    Formalism.FourierDecayAlt.P.PBE.cutCpt P p.T.base f χ ε
      (fun (n : ℕ) (g : B.Mat P.k P.r) =>
        ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ))
      hχ hε hf (fun _ _ => rfl) n
  exact (GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors hA Wp Wq P p Cb _ _ w hD (hc ε₁ hε₁) (hc ε₂ hε₂) hw).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectorsStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  first | exact @GlobalTheory.beta_word_cutF_eq_integral_inner_tv | exact GlobalTheory.beta_word_cutF_eq_integral_inner_tv | (intros; apply GlobalTheory.beta_word_cutF_eq_integral_inner_tv <;> assumption)
end

module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2OfFourEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbedLoweringConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlusLetterFrameOfData
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussFormMinusLetter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteLevelZeroElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusLetterFrameOfData
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
namespace Formalism.FourierDecayAlt.P

theorem plus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.PlusStep :=
  plus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_plus
    rtt_relation_entries plus_letter_form plus_letter_tau plus_letter_l

theorem minus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.MinusStep :=
  minus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_minus
    rtt_relation_entries minus_letter_form minus_letter_tau minus_letter_l

theorem frame_of_admissible_word : Formalism.FourierDecayAlt.Fr.FrameAll :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).1

theorem frame_eq_word_module : Formalism.FourierDecayAlt.Fr.FrameWord :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).2

theorem frame_of_recursive_word : Formalism.FourierDecayAlt.Fr.FrameAllRec :=
  frame_rec_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

end Rep

theorem real_bound (u v c b : ℂ) (hc : c ≠ 0) (hu : u.im = 0) (hv : v.im = 0)
    (hb : ‖b‖ ^ 2 ≤ u.re * v.re) :
    (u * (c * v) / c).im = 0 ∧ ‖b‖ ^ 2 ≤ (u * (c * v) / c).re := by
  have h : u * (c * v) / c = u * v := by field_simp <;> ring
  rw [h]
  constructor
  · simp [Complex.mul_im, hu, hv]
  · simpa [Complex.mul_re, hu, hv] using hb

theorem qw_append_ne {S : Type} (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hq : qw q w Y ≠ 0) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ Y - l.pt ≠ 0 ∧ Y - l.pt + 1 ≠ 0) →
      qw q (L ++ w) Y ≠ 0 := by
  intro L hL
  induction L with
  | nil => simpa using hq
  | cons l L ih =>
    have hl := hL l (by simp)
    rw [List.cons_append]
    simp only [qw]
    rw [if_pos hl.1]
    exact mul_ne_zero (ih fun l' hl' => hL l' (by simp [hl'])) (div_ne_zero hl.2.2 hl.2.1)

theorem good_tail {S : Type} {l : Letter ℂ S} {w : List (Letter ℂ S)} (h : Good (l :: w)) : Good w := by
  unfold Good at *
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), (List.pairwise_cons.1 h3).2⟩
  simp only [List.map_cons, List.nodup_cons] at h1
  exact h1.2

theorem dkDualOK : DKDualOK := by
  intro S _ _ q w L hD
  induction L with
  | nil => trivial
  | cons l L ih =>
    obtain ⟨hP, hG, hGd, hPw, hq⟩ := hD
    have hl : l.plus = true := hP l (by simp)
    have hG' : Good (L ++ w) := good_tail hG
    have hGd' : Good (L.map dl ++ w) := good_tail (by simpa using hGd)
    have hpw := List.pairwise_cons.mp hPw
    refine ⟨?_, ?_, ih ⟨fun l' h => hP l' (by simp [h]), hG', hGd', hpw.2,
      fun l' h => hq l' (by simp [h])⟩⟩
    ·
      intro l' hl'
      have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hl]
      rw [hdl]
      rcases List.mem_append.mp hl' with h | h
      · have hpl : l'.plus = true := hP l' (by simp [h])
        have := (hpw.1 l' h).1
        simp only [RegL, hpl, if_true]
        intro h0; apply this; linear_combination h0
      · have hgd : Good (dl l :: (L.map dl ++ w)) := by simpa using hGd
        have := (List.pairwise_cons.mp hgd.2.2).1 l' (by simp [h])
        rw [hdl] at this
        exact this
    · simp only [ypt, hl, if_true]
      refine qw_append_ne q w l.pt (hq l (by simp)) L fun l' hl' => ⟨hP l' (by simp [hl']), ?_, ?_⟩
      · exact (hpw.1 l' hl').1
      · intro h0; exact (hpw.1 l' hl').2.2 (by linear_combination h0)

end Formalism.FourierDecayAlt.P.DualKernelLemmas
end

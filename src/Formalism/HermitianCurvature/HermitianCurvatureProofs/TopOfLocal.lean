module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopOfLocal
open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem top_of_local : KB.TopOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ' hpos _ hloc ε hε s hs2 hsr w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v =>
    le_trans (Nat.add_le_add_right (len_le_cnt S w.1 v) _) hcnt'
  choose U θ hUθ using fun v => hloc v s hs2 hsr (w.1 v) ⟨w, rfl⟩ (hlen v)
  have hU : ∀ v, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hUθ v).1.2 a ha).1,
      le_trans ((hUθ v).1.2 a ha).2 (Nat.add_le_add_right (len_le_cnt S w.1 v) _)⟩
  have hw : w.1.cnt ≤ w.1.cnt + C.Kst := Nat.le_add_right _ _
  refine ⟨fun B => pθ S B w θ, fun B => pθ_prob (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt', ?_⟩
  intro Y hY κ hκ t ht B
  let g : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, S.σ v t)]
  let G : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.gN S v ε (S.G.r + 1) (w.1 v) (g v h) (g v h')
  let M : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.mix S v ε (S.G.r + 1) (U v) (θ v) (g v h) (g v h')
  let c : Fin S.f → ℝ := fun v => (‖S.σ v t‖ * Λ' (S.G.r + 2 - s) s v) ^ (2 * C.Kst)
  let A : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    if v ∈ B then (c v : ℂ) * M v h h' else G v h h'
  have hG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (G v) := fun v _ =>
    psd_comp _ _ (gN_psd S hpos v hε le_rfl w (Y.image (g v))) Y (g v)
      (fun h hh => mem_image_of_mem _ hh)
  have hAG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (fun x y => A v x y - G v x y) := by
    intro v _
    by_cases hv : v ∈ B
    · have hσ : S.σ v t ≠ 0 := (map_ne_zero (S.σ v)).mpr ht
      have hY' : ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = S.G.r + 1 - s := by
        intro p hp
        obtain ⟨h, hh, rfl⟩ := mem_image.mp hp
        rw [ptSize_loc]
        exact hY h hh
      have h1 := psd_comp _ _ ((hUθ v).2 ε hε (S.σ v t) _ hσ hY') Y (C.loc (S.σ v))
        (fun h hh => mem_image_of_mem _ hh)
      refine Jx8.psd_congr ?_ h1
      intro x _ y _
      simp only [A, if_pos hv]
      rfl
    · refine Jx8.psd_congr ?_ (Jx8.zero_psd Y)
      intro x _ y _
      simp only [A, if_neg hv, sub_self]
  have hle := BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (Jx7.psd_prod_dom univ G A hG hAG)
  have hprod : ∀ h h', ∏ v, A v h h' =
      (∏ v ∈ B, (c v : ℂ)) * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    intro h h'
    calc ∏ v, A v h h'
        = ∏ v, ((if v ∈ B then (c v : ℂ) else 1) * (if v ∈ B then M v h h' else G v h h')) :=
          prod_congr rfl (fun v _ => by by_cases hv : v ∈ B <;> simp [A, hv])
      _ = (∏ v, (if v ∈ B then (c v : ℂ) else 1)) * ∏ v, (if v ∈ B then M v h h' else G v h h') :=
          prod_mul_distrib
      _ = _ := by rw [prod_ite_mem, univ_inter]
  have hexp : ∀ h h', ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h') =
      ∏ v, (if v ∈ B then M v h h' else G v h h') := fun h h' =>
    expand (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt'
      (fun v a => KB.gN S v ε (S.G.r + 1) a (g v h) (g v h'))
  have hR : ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    simp only [Nst_eq S (i := S.G.r + 1) le_rfl]
    have hm := mix_sum Y (S.base.Wb (w.1.cnt + C.Kst)) κ 1 (fun w' => (pθ S B w θ w' : ℂ))
      (fun w' h h' => ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h'))
    simp only [one_mul] at hm
    rw [← hm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
    rw [hexp h h']
  have hC : ∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K) = ∏ v ∈ B, c v :=
    prod_congr rfl fun v _ => by rw [av_eq]; rfl
  have hsum : ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K),
        pθ S B w θ w' * (S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re =
      (∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun w' _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [hC, hsum, hR, Nst_eq S (i := S.G.r + 1) le_rfl s w Y κ t t, ← Complex.re_ofReal_mul,
    Complex.ofReal_prod]
  have hA : (∏ v ∈ B, (c v : ℂ)) * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, A v h h' := by
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h' _ => ?_
    rw [hprod h h', mul_left_comm]
  rw [hA]
  simp only [mul_sub, sum_sub_distrib, Complex.sub_re] at hle
  linarith

end

end Formalism.FourierDecayAlt.P.PBA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfLocal
open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lpt (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (s : ℕ) (t : E) (h : TB.Pt E) : C.LPt :=
  C.loc (S.σ v) h ++ [(s, S.σ v t)]

theorem re_real_sum {W : Type} (c : ℝ) (Ws : Finset W) (p : W → ℝ) (N : W → ℂ) :
    ((c : ℂ) * ∑ w ∈ Ws, (p w : ℂ) * N w).re = c * ∑ w ∈ Ws, p w * (N w).re := by
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

theorem liftOfLoc_statement : KB.LiftOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ hpos _ _ hloc
  intro ε hε i s hs hsi hir w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by
    have := len_le_cnt S w.1 v; omega
  have hb1 : 1 ≤ i - s + 1 := by omega
  have hbs : i - s + 1 + s ≤ S.G.r + 1 := by omega
  have hlev : i - s + 1 + s - 1 = i := by omega
  have hi : i ≤ S.G.r + 1 := by omega
  have hwn : w.1.cnt ≤ w.1.cnt + C.Kst := by omega
  have hL := fun v => hloc v (i - s + 1) s hb1 hs hbs (w.1 v) ⟨w, rfl⟩ (hlen v)
  simp only [hlev] at hL
  choose Up θp Um θm hPp hPm hblk using hL
  have hUp : ∀ v, ∀ a ∈ Up v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPp v).2 a ha).1, ((hPp v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hUm : ∀ v, ∀ a ∈ Um v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPm v).2 a ha).1, ((hPm v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hprobP := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θp) (fun v _ => (hPp v).1) (fun v _ => hUp v) hwn hcnt'
  have hprobM := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θm) (fun v _ => (hPm v).1) (fun v _ => hUm v) hwn hcnt'
  refine ⟨fun A x => pθ S A w θp x.1 * pθ S A w θm x.2, fun A => pair_prob (hprobP A) (hprobM A), ?_⟩
  intro Y T κ hY hκ t ht t' ht' ht0 ht0' _ A
  have hσ : ∀ v, S.σ v t ≠ 0 := fun v => (map_ne_zero _).2 ht0
  have hσ' : ∀ v, S.σ v t' ≠ 0 := fun v => (map_ne_zero _).2 ht0'
  have hsz : ∀ v, ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = i - s + 1 - 1 := by
    intro v p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    rw [ptSize_loc, hY h hh]; omega
  have hU : ∀ v, ∃ u : ℂ, ‖u‖ = 1 ∧ (v ∈ A → KB.BlockPSD Y Y
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h'))
      (fun h h' => u * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst *
        KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h'))) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (S.σ v t) (S.σ v t') (Y.image (C.loc (S.σ v))) (hσ v) (hσ' v) (hsz v)
      exact ⟨u, hu, fun _ => blockPSD_comp _ _ _ _ hB Y (C.loc (S.σ v))
        (fun x hx => Finset.mem_image_of_mem _ hx)⟩
    · exact ⟨1, by simp, fun h => absurd h hv⟩
  choose u hu1 hu2 using hU
  have hprod := blockPSD_prod (Y₁ := Y) (Y₂ := Y) univ
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t h')))
    (fun v h h' => (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t' h) (lpt S v s t' h')))
    (by
      intro v _
      by_cases hv : v ∈ A
      · simp only [if_pos hv]; exact hu2 v hv
      · simp only [if_neg hv, one_mul]
        exact blockPSD_pull (Y.image (lpt S v s t) ∪ Y.image (lpt S v s t')) (KB.gN S v ε i (w.1 v))
          (gN_psd S hpos v hε hi w _) Y (lpt S v s t) (lpt S v s t')
          (fun h hh => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))
          (fun h hh => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh)))
  have hmem : ∀ τ ∈ T, ∀ h ∈ Y, TB.join h s τ ∈ TB.pts Y s T := by
    classical
    intro τ hτ h hh
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(h, τ), Finset.mem_product.2 ⟨hh, hτ⟩, rfl⟩
  have hκb : KB.BlockPSD Y Y (TB.blk κ s t t) (TB.blk κ s t t') (TB.blk κ s t' t') :=
    blockPSD_pull (TB.pts Y s T) κ hκ Y (fun h => TB.join h s t) (fun h => TB.join h s t')
      (hmem t ht) (hmem t' ht')
  have hmain := block_cross_le (blockPSD_mul hκb hprod)

  have eL : (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s t t' h h' * ∏ v, (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h')) =
      (∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t' := by
    rw [Nst_eq S hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    simp only [lpt]; ring

  have eD : ∀ (τ : E) (Uq : Fin S.f → Finset (List C.Letter)) (θq : Fin S.f → List C.Letter → ℝ),
      (∀ v, TB.IsProb (Uq v) (θq v)) → (∀ v, ∀ a ∈ Uq v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst) →
      (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s τ τ h h' * ∏ v,
        (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
      ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S A w θq w' : ℂ) * S.base.Nst ε i s w' Y (TB.blk κ s τ τ) τ τ := by
    intro τ Uq θq hP hUq
    have hx : ∀ h h', (∏ v, (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
        ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst),
          (pθ S A w θq w' : ℂ) * ∏ v, KB.gN S v ε i (w'.1 v) (lpt S v s τ h) (lpt S v s τ h') := by
      intro h h'
      have he := expand (A := A) (w := w) (θ := θq) (U := Uq) (fun v _ => hP v) (fun v _ => hUq v) hwn hcnt'
        (fun v a => KB.gN S v ε i a (lpt S v s τ h) (lpt S v s τ h'))
      rw [he, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Complex.ofReal_prod]
      rfl
    simp only [hx]
    rw [mix_sum]
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Nst_eq S hi]; rfl
  have hK : S.base.K = C.Kst := rfl
  have hcw : S.base.cnt w = w.1.cnt := rfl
  rw [eL, eD t Up θp (fun v => (hPp v).1) hUp, eD t' Um θm (fun v => (hPm v).1) hUm, re_real_sum, re_real_sum]
    at hmain
  have hsp := sum_pair (S.base.Wb (w.1.cnt + C.Kst)) (S.base.Wb (w.1.cnt + C.Kst)) (pθ S A w θp) (pθ S A w θm)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t t) t t).re)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t' t') t' t').re) (hprobM A).2.2 (hprobP A).2.2
  rw [hK, hcw, hsp]
  calc (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ C.Kst) * ‖S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ =
      ‖(∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ := by
        rw [norm_mul, norm_prod]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [norm_mul, hu1, one_mul, norm_pow, av_eq, map_sub, map_inv₀, map_inv₀]
    _ ≤ _ := hmain
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.PBA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminorWordSum (k r t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
      (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ t) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn (t : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          qminorOp (Q.EH k r) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin t))).toList.flatMap
      (fun σ => (expand k r (ts σ)).map fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨this.1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Loc ((ts σ).length : ℕ∞) f g := by
      intro σ
      obtain ⟨U, f', a, b, c, d⟩ := hf g hgU
      refine ⟨U, f', a, b, ?_, d⟩
      simpa [ts] using c
    have e1 : qminorOp (Q.EH k r) a b u f g = ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [foldT, ts, List.map_ofFn]
      rfl
    rw [e1, sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [expand_eq (ts σ) f g hg (hloc σ), List.map_map, ← sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp


open Classical in
def pTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [B.hsInner, _root_.smul_apply, ContinuousLinearMap.id_apply, hsv_smul,
      inner_smul_left, inner_smul_right]
    simp

theorem pTerm_word {P : B.Mat k r → ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word = w := by
  simp only [pTerm]
  rw [if_pos hw]

theorem pTerm_word_le (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word.length ≤ w.length := by
  simp only [pTerm]
  split_ifs
  · exact le_refl _
  · simp

theorem inLie_zero : B.inLie k r 0 := by
  unfold B.inLie
  simp

private theorem foldr_max_le_lemma (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → l.foldr max 0 ≤ t := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem le_foldr_max_lemma_2 : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih x hx) (le_max_right _ _)

theorem foldr_max_eq (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → t ∈ l → l.foldr max 0 = t := by
  intro l hl ht
  exact le_antisymm (foldr_max_le_lemma t l hl) (le_foldr_max_lemma_2 l t ht)

end terms

theorem qminOpRep {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) a (b j) u F g := by
  have h := fun j => qminorWordSum k r t a (b j) u
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
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
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
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
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

section basic₂

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem polyOp_mono {o o' κ κ' : ℕ} {Θ : B.DiffOp k r Wp Wq} (h : PolyOp o κ Θ) (ho : o ≤ o') (hκ : κ ≤ κ') :
    PolyOp o' κ' Θ := by
  unfold PolyOp at *
  intro Tm hTm
  obtain ⟨h1, P, hP, h2, h3⟩ := h Tm hTm
  obtain ⟨q, hq, hq'⟩ := hP
  exact ⟨h1.trans ho, P, ⟨q, hq.trans hκ, hq'⟩, h2, h3⟩

theorem polyOp_append {o κ : ℕ} {Θ₁ Θ₂ : B.DiffOp k r Wp Wq} (h₁ : PolyOp o κ Θ₁) (h₂ : PolyOp o κ Θ₂) :
    PolyOp o κ (Θ₁ ++ Θ₂) := by
  unfold PolyOp at *
  intro Tm hTm
  rcases List.mem_append.mp hTm with h | h
  · exact h₁ Tm h
  · exact h₂ Tm h

theorem opApply_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Θ₁ ++ Θ₂) F g = B.opApply Θ₁ F g + B.opApply Θ₂ F g := by
  unfold B.opApply
  rw [List.map_append, List.sum_append]

private theorem foldr_max_init_lemma_3 : ∀ (l : List ℕ) (b : ℕ), l.foldr max b = max (l.foldr max 0) b := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
    intro b
    simp only [List.foldr_cons]
    rw [ih b, max_assoc]

theorem opOrder_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) :
    B.opOrder (Θ₁ ++ Θ₂) = max (B.opOrder Θ₁) (B.opOrder Θ₂) := by
  unfold B.opOrder
  rw [List.map_append, List.foldr_append]
  exact foldr_max_init_lemma_3 _ _

end basic₂

end

end Formalism.FourierDecayAlt.P.CutMP.QMinOp
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mulRb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.mul_add]
      map_smul' := fun c X => by ext g : 1; simp }

def mulLb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.add_mul]
      map_smul' := fun c X => by ext g : 1; simp }

theorem vf_eq_b (b : Bool) (X g : Mat k r) :
    vf b X g = (if b then -(mulLb k r X g) else mulRb k r X g) := by
  cases b
  · first
    | rfl
    | simp [vf, mulLb, mulRb, mulL, mulR]
  · first
    | rfl
    | simp [vf, mulLb, mulRb, mulL, mulR]

theorem vf_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (b : Bool) {X g : P → Mat k r}
    (hX : ContDiff ℝ ∞ X) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun q => vf b (X q) (g q)) := by
  cases b
  · have h := ((mulRb k r).contDiff.comp hX).clm_apply hg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)
  · have h := (((mulLb k r).contDiff.comp hX).clm_apply hg).neg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)

def Phi (F' : Mat k r → E) : (j : ℕ) → (Fin j → Bool) → (Fin j → Mat k r) × Mat k r → E
  | 0, _, q => F' q.2
  | j + 1, bs, q => fderiv ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => q.1 i.succ), g)) q.2
      (vf (bs 0) (q.1 0) q.2)

theorem top_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  first
  | (rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  | simp
  | exact le_of_eq (by norm_cast)

theorem phi_contDiffAt (F' : Mat k r → E) {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (q : (Fin j → Mat k r) × Mat k r), q.2 ∈ U → ContDiffAt ℝ ∞ (Phi F' j bs) q := by
  intro j
  induction j with
  | zero =>
    intro bs q hq
    exact (hF.contDiffAt (hU.mem_nhds hq)).comp q contDiffAt_snd
  | succ j ih =>
    intro bs q hq
    have hsh : ContDiff ℝ ∞ (fun p : ((Fin (j + 1) → Mat k r) × Mat k r) × Mat k r =>
        ((fun i : Fin j => p.1.1 i.succ), p.2)) :=
      (contDiff_pi.2 fun (i : Fin j) => by
        simpa only [Function.comp_def] using
          (contDiff_apply ℝ (fun _ : Fin (j + 1) => Mat k r) i.succ).comp (contDiff_fst.comp contDiff_fst)).prodMk
        contDiff_snd
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (p : (Fin (j + 1) → Mat k r) × Mat k r) (g : Mat k r) =>
        Phi F' j (fun i => bs i.succ) ((fun i => p.1 i.succ), g)) (q, q.2) :=
      (ih (fun i => bs i.succ) ((fun i => q.1 i.succ), q.2) hq).comp (q, q.2) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 contDiffAt_snd top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun p : (Fin (j + 1) → Mat k r) × Mat k r => vf (bs 0) (p.1 0) p.2) :=
      vf_contDiff (bs 0) ((contDiff_apply ℝ (fun _ : Fin (j + 1) => Mat k r) 0).comp contDiff_fst) contDiff_snd
    exact h2.clm_apply h3.contDiffAt

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem W_eq_phi {F F' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U)
    (hff : ∀ x ∈ U, x ∈ GV k r → F x = F' x) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) →
      ∀ x ∈ U, x ∈ GV k r → W (List.ofFn fun i => (bs i, Xs i)) F x = Phi F' j bs (Xs, x) := by
  intro j
  induction j with
  | zero => intro bs Xs _ x hx hxG; exact hff x hx hxG
  | succ j ih =>
    intro bs Xs hXs x hx hxG
    rw [List.ofFn_succ, W_cons]
    have hd : DifferentiableAt ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => Xs i.succ), g)) x :=
      ((phi_contDiffAt F' hU hF j _ ((fun i => Xs i.succ), x) hx).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact (hasDerivAt_ext (bs 0) hU hx hxG hd (fun h hh hhG => ih _ _ (fun i => hXs i.succ) h hh hhG)
      (hXs 0)).deriv

theorem W_local_zero {F : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V) (h : ∀ x ∈ V, x ∈ GV k r → F x = 0) :
    ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ x ∈ V, x ∈ GV k r → W w F x = 0 := by
  intro w
  induction w with
  | nil => intro _ x hx hxG; exact h x hx hxG
  | cons a w ih =>
    intro hw x hx hxG
    rw [W_cons]
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hc := (cv_hasDerivAt a.1 a.2 x).continuousAt
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, cv a.1 a.2 t x ∈ V :=
      hc.preimage_mem_nhds (by rw [cv_zero]; exact hV.mem_nhds hx)
    have he : (fun t : ℝ => W w F (cv a.1 a.2 t x)) =ᶠ[𝓝 0] fun _ => (0 : E) := by
      filter_upwards [hmem] with t ht
      exact ih hw' _ ht (cv_mem (hw a List.mem_cons_self) hxG t)
    show deriv (fun t : ℝ => W w F (cv a.1 a.2 t x)) 0 = 0
    rw [he.deriv_eq, deriv_const]

def Box (k r : ℕ) : Set (Mat k r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1

theorem box_compact : IsCompact (Box k r) := by
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1

theorem mem_box {X : Mat k r} (h : ∀ i j, ‖X i j‖ ≤ 1) : X ∈ Box k r := by
  exact fun i _ j _ => mem_closedBall_zero_iff.mpr (h i j)

theorem local_bound {F : Mat k r → E} (hF : CkOn ⊤ (GV k r) F) (m : ℕ) {g₀ : Mat k r} (hg₀ : g₀ ∈ GV k r) :
    ∃ V ∈ 𝓝 g₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := by
  obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hgU
  have hsub : Metric.closedBall g₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hc' : ContDiffOn ℝ ∞ F' U := by exact_mod_cast hc
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ (Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ
      Metric.closedBall g₀ (ε / 2), ‖Phi F' j bs q‖ ≤ c := by
    intro j bs
    have hK : IsCompact ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall g₀ (ε / 2)) :=
      (isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall g₀ _)
    exact hK.exists_bound_of_continuousOn fun q hq =>
      (phi_contDiffAt F' hU hc' j bs q (hsub hq.2)).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall g₀ (ε / 2), Metric.closedBall_mem_nhds g₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro x hx hxG j hj bs Xs hL hB
  rw [W_eq_phi hU hc' hff j bs Xs hL x (hsub hx) hxG]
  calc ‖Phi F' j bs (Xs, x)‖ ≤ |c j bs| := (hcb j bs (Xs, x) ⟨fun i _ => hB i, hx⟩).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem compact_support_finite_class : Formalism.FourierDecayAlt.P.JFxG.CptInCC := by
  intro k r E _ _ F C hF hC hCF A m
  have hCG : IsCompact (C ∩ GV k r) := hC.inter_right B5.GV_closed
  have hloc : ∀ g₀ ∈ C ∩ GV k r, ∃ V, V ∈ 𝓝 g₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := fun g₀ hg₀ => by
    obtain ⟨V, hV, c, hc0, hc⟩ := local_bound hF m hg₀.2
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hloc
  obtain ⟨t, htC, hcov⟩ := hCG.elim_nhds_subcover V hV
  have hcW : ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F g‖ ≤ ∑ x ∈ t, c x := by
    intro g hg j hj bs Xs hL hB
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (hcov hg)
    exact (hc x (htC x hxt) g hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (htC y hy)) hxt)
  obtain ⟨cg, hcg⟩ := hCG.exists_bound_of_continuousOn (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  have hsum0 : 0 ≤ ∑ x ∈ t, c x := Finset.sum_nonneg fun y hy => hc0 y (htC y hy)
  refine ⟨|cg| * ∑ x ∈ t, c x, B5.ckOn_mono le_top hF, ?_⟩
  intro u v hu hv hl g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW g ⟨hgC, hg⟩ _ hlen (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl (fun x hx _ => hCF x hx) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity

end Formalism.FourierDecayAlt.P
end
end

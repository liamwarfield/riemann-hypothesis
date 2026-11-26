module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableBound
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.DvDegOtherMono

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EDelApply
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPbound
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPtrueHom
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EvensBeforePairwise
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem getElem_ge_of_many (D : List ℤ) (hD : D.Pairwise (· > ·)) (T : Finset ℤ) (b : ℤ)
    (hT : ∀ z ∈ T, z ∈ D ∧ b ≤ z) (l : ℕ) (hl : l < T.card) (hlen : l < D.length) : b ≤ D[l] := by
  by_contra hlt
  push_neg at hlt
  have hsub : T ⊆ (D.take l).toFinset := by
    intro z hz
    obtain ⟨hzD, hbz⟩ := hT z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzD
    have hil : i < l := by
      by_contra h
      push_neg at h
      rcases h.lt_or_eq with h | h
      · have := List.pairwise_iff_getElem.1 hD l i hlen hi h
        linarith
      · have e : D[l] = D[i] := by simp [h]
        linarith
    have hi' : i < (D.take l).length := by simp; omega
    have hm := List.getElem_mem hi'
    simp only [List.getElem_take] at hm
    exact List.mem_toFinset.2 hm
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (D.take l)
  simp only [List.length_take] at h2
  omega

section Fr

variable {n' r : ℕ} [NeZero n']

theorem fr_mono' {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))

theorem fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    ∀ k i, i < k → k < r → F.fr j i < F.fr j k := by
  intro k i hik hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k hk)
    · subst h
      exact hV.2.2.1 j i hk

theorem seg_of {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (s : ℤ) :
    ∃ j : ℤ, F.fr (j - 1) (r - 1) < s ∧ s ≤ F.fr j (r - 1) := by
  classical
  have hn : (1 : ℤ) ≤ (n' : ℤ) := by
    have : n' ≠ 0 := NeZero.ne n'
    omega
  have hstep : ∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) (r - 1) := by
    intro j
    exact lt_of_lt_of_le (hV.2.2.2.1 j) (fr_mono' hV (j + 1) (r - 1) (by omega))
  have hmono : StrictMono (fun j : ℤ => F.fr j (r - 1)) := strictMono_int_of_lt_succ hstep
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr ((m : ℤ) * F.J) (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 ((m : ℤ) * F.J) (r - 1)
      rw [show ((m + 1 : ℕ) : ℤ) * (F.J : ℤ) = (m : ℤ) * F.J + F.J by push_cast; ring, h]
      push_cast
      omega
  have hdown : ∀ m : ℕ, F.fr (-((m : ℤ) * F.J)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 (-(((m + 1 : ℕ) : ℤ) * F.J)) (r - 1)
      rw [show -(((m + 1 : ℕ) : ℤ) * (F.J : ℤ)) + F.J = -((m : ℤ) * F.J) by push_cast; ring] at h
      push_cast at h ⊢
      omega
  have hP : ∃ j : ℤ, s ≤ F.fr j (r - 1) := by
    refine ⟨((s - F.fr 0 (r - 1)).toNat : ℤ) * F.J, ?_⟩
    have := hup (s - F.fr 0 (r - 1)).toNat
    omega
  have hB : ∃ b : ℤ, ∀ j : ℤ, s ≤ F.fr j (r - 1) → b ≤ j := by
    refine ⟨-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J), fun j hj => ?_⟩
    have h1 := hdown (F.fr 0 (r - 1) - s + 1).toNat
    by_contra hlt
    push_neg at hlt
    have h2 : F.fr j (r - 1) < F.fr (-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J)) (r - 1) := hmono hlt
    omega
  obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd hB hP
  refine ⟨j, ?_, hj⟩
  by_contra h
  push_neg at h
  have := hmin (j - 1) h
  omega

theorem evensBefore_pairwise (F : Frames n' r) (s : ℤ) : (evensBefore F s).Pairwise (· > ·) := by
  unfold evensBefore
  rw [List.pairwise_reverse]
  exact (Finset.sortedLT_sort _).pairwise

theorem arow_near {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (s : ℤ) (l : ℕ) (hl : l < r) : (s - Arow F s l).toNat ≤ G' := by
  obtain ⟨-, hV, hG', -, -⟩ := hF
  obtain ⟨j, hj1, hj2⟩ := seg_of hV hr s
  unfold Arow
  by_cases hlen : l < (evensBefore F s).length
  · rw [List.getD_eq_getElem _ _ hlen]
    have hrn : (G' : ℤ) ≤ (r : ℤ) * (n' : ℤ) := by
      have : G' ≤ r * n' := le_trans hG (by nlinarith)
      exact_mod_cast this
    have key : s - (G' : ℤ) ≤ (evensBefore F s)[l] := by
      refine getElem_ge_of_many (evensBefore F s) (evensBefore_pairwise F s)
        ((Finset.range r).image (fun i => F.fr (j - 1) i)) (s - G') ?_ l ?_ hlen
      · intro z hz
        simp only [Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        have h0 := fr_mono' hV (j - 1) i hi
        have h1 : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := by
          rcases Nat.lt_or_ge i (r - 1) with h | h
          · exact le_of_lt (fr_lt hV (j - 1) (r - 1) i h (by omega))
          · have : i = r - 1 := by omega
            rw [this]
        have h2 := hG' j
        have h3 := hV.2.2.2.2.1 (j - 1) i hi
        refine ⟨?_, by omega⟩
        simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h3.1, h3.2⟩
      · rw [Finset.card_image_of_injOn]
        · simpa using hl
        · intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          simp only at hab
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := fr_lt hV (j - 1) b a h hb
            omega
          · have := fr_lt hV (j - 1) a b h ha
            omega
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem twist_of {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (p : ℕ) (hp : 1 ≤ p) : TwistBound p F (p ^ G') := by
  refine ⟨fun j => ?_, fun s _ l hl => Nat.pow_le_pow_right (by omega) (arow_near hF hr hG s.val l hl)⟩
  unfold Qj zF
  apply Nat.pow_le_pow_right (by omega)
  have h1 := hF.2.2.1 (j + 1)
  have h2 := fr_mono' hF.2.1 j (r - 1) (by omega)
  simp only [add_sub_cancel_right] at h1
  omega

end Fr

end Formalism.MainNotions.Pf14
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Hom

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] {n : ℕ}

theorem pol_prod {α : Type} (s : Finset α) (f : α → MvPolynomial (ι × Fin n) R) (e : α → ι → ℕ)
    (h : ∀ a ∈ s, f a ∈ Pol R n (e a)) : ∏ a ∈ s, f a ∈ Pol R n (∑ a ∈ s, e a) :=
  (dv_pol_iff _ _).2 (IsWeightedHomogeneous.prod s f e fun a ha => (dv_pol_iff _ _).1 (h a ha))

theorem pol_det {r : ℕ} (M : Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin n) R)) (e : Fin r → ι → ℕ)
    (h : ∀ l b, M l b ∈ Pol R n (e l)) : M.det ∈ Pol R n (∑ l, e l) := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h1 : ∏ i : Fin r, M (σ i) i ∈ Pol R n (∑ i : Fin r, e (σ i)) :=
    pol_prod Finset.univ _ _ fun i _ => h (σ i) i
  have h2 : (∑ i : Fin r, e (σ i)) = ∑ l, e l := Equiv.sum_comp σ e
  rw [h2] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact h1
  · rw [hs, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ h1

end Hom

section SP

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O]
variable {r k : ℕ} (F : Frames n' r)

theorem xg_hom (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) :
    xg p n' O n' g a b ∈ Pol (KK O) k (Pi.single (posOf n' a) 1 : Fin n' → ℕ) := by
  unfold xg
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [dv_pol_iff]
  have h1 := isWeightedHomogeneous_X (KK O) (letterWeight (ι := Fin n') (n := k)) (posOf n' a, c)
  have h2 := isWeightedHomogeneous_C (letterWeight (ι := Fin n') (n := k)) (sigMat p n' O g a c b)
  have := h1.mul h2
  rw [add_zero] at this
  have e : (letterWeight (ι := Fin n') (n := k) (posOf n' a, c)) = (Pi.single (posOf n' a) 1 : Fin n' → ℕ) := by
    funext i
    unfold letterWeight
    simp only [Pi.single_apply]
    congr
  rw [e] at this
  exact this

def eDel (j : ℤ) : Fin n' → ℕ :=
  ∑ l : Fin r, p ^ (zF F j - F.fr j l.val).toNat • (Pi.single (posOf n' (F.fr j l.val)) 1 : Fin n' → ℕ)

def eD (s : ℤ) : Fin n' → ℕ :=
  ∑ l : Fin r, p ^ (s - Arow F s l.val).toNat • (Pi.single (posOf n' (Arow F s l.val)) 1 : Fin n' → ℕ)

theorem Del_hom (g : Matrix (Fin k) (Fin k) (WF p n')) (j : ℤ) :
    Del p n' O F g j ∈ Pol (KK O) k (eDel p n' F j) := by
  unfold Del minorI
  split_ifs with h
  · refine pol_det _ _ fun l b => ?_
    simp only [Matrix.of_apply]
    unfold twRow
    exact dv_pol_pow _ _ (xg_hom p n' O g _ _) _
  · exact Submodule.zero_mem _

theorem Dtop_hom (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ) :
    Dtop p n' O F hrk g s ∈ Pol (KK O) k (eD p n' F s) := by
  unfold Dtop
  refine pol_det _ _ fun l b => ?_
  simp only [Matrix.of_apply]
  exact dv_pol_pow _ _ (xg_hom p n' O g _ _) _

def eSP (k c' Q : ℕ) : Fin n' → ℕ :=
  c' • (∑ j ∈ Finset.range F.J, alpha p F k (j : ℤ) • eDel p n' F (j : ℤ)) +
    (∑ j ∈ Finset.range F.J, c' • eDel p n' F (j : ℤ)) +
    ∑ s ∈ F.TT, ((2 * Q + 3) * c' + k * Q) • eD p n' F (s.val : ℤ)

theorem SPtrue_hom (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (c' Q : ℕ) :
    HasMultideg (SPtrue p n' O F hrk g c' Q) (eSP p n' F k c' Q) := by
  unfold HasMultideg SPtrue eSP R0 DtopProd
  refine dv_pol_mul _ _ _ _ (dv_pol_mul _ _ _ _ (dv_pol_pow _ _ ?_ _) ?_) ?_
  · exact pol_prod _ _ _ fun j _ => dv_pol_pow _ _ (Del_hom p n' O F g j) _
  · exact pol_prod _ _ _ fun j _ => dv_pol_pow _ _ (Del_hom p n' O F g j) _
  · exact pol_prod _ _ _ fun s _ => dv_pol_pow _ _ (Dtop_hom p n' O F hrk g s.val) _

end SP

end Formalism.MainNotions.Pf14
end
end

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Pos

variable {n' : ℕ} [NeZero n']

end Pos

section Fr

variable {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}

private theorem fr_lt_fr_of_lt (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l < l') (hl' : l' < r) :
    F.fr j l < F.fr j l' := by
  obtain ⟨-, -, hinc, -⟩ := hV
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hll
  induction m with
  | zero => exact hinc j l (by omega)
  | succ m ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hinc j (l + m + 1) (by omega)
    show F.fr j l < F.fr j (l + m + 1 + 1)
    exact lt_trans h1 h2

private theorem fr_le_fr_of_le (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l ≤ l') (hl' : l' < r) :
    F.fr j l ≤ F.fr j l' := by
  rcases Nat.lt_or_eq_of_le hll with h | rfl
  · exact le_of_lt (fr_lt_fr_of_lt hV j h hl')
  · exact le_rfl

theorem fr_le_last (hV : F.Valid L₁ N₁) (j : ℤ) {l : ℕ} (hl : l < r) : F.fr j l ≤ F.fr j (r - 1) := by
  exact fr_le_fr_of_le hV j (by omega) (by omega)

end Fr

end Formalism.MainNotions.Pf14
end
end

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Bound

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {r : ℕ} (F : Frames n' r)

theorem eDel_apply (j : ℤ) (t : Fin n') : eDel p n' F j t =
    ∑ l : Fin r, if t = posOf n' (F.fr j l.val) then p ^ (zF F j - F.fr j l.val).toNat else 0 := by
  simp only [eDel, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

theorem eD_apply (s : ℤ) (t : Fin n') : eD p n' F s t =
    ∑ l : Fin r, if t = posOf n' (Arow F s l.val) then p ^ (s - Arow F s l.val).toNat else 0 := by
  simp only [eD, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

variable {p n' F} {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ}

theorem del_bound (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n') (k c' : ℕ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t ≤
      (c' * (1 + r * k * p ^ G') + c') * p ^ G' := by
  classical
  have hV := hF.2.1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have rle : ∀ (j : ℤ) (i i' : ℕ), i ≤ i' → i' < r → F.fr j i ≤ F.fr j i' := by
    intro j i i' h h'
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      exact le_trans (ih (by omega) (by omega)) (le_of_lt (hV.2.2.1 j (i + d) (by omega)))
  have rlt : ∀ (j : ℤ) (d : ℕ) (i i' : ℕ), i < r → i' < r → F.fr j i < F.fr (j + 1 + d) i' := by
    intro j d
    induction d with
    | zero =>
      intro i i' hi hi'
      have h1 := rle j i (r - 1) (by omega) (by omega)
      have h2 := hV.2.2.2.1 j
      have h3 := rle (j + 1) 0 i' (Nat.zero_le _) hi'
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ d ih =>
      intro i i' hi hi'
      have h1 := ih i (r - 1) hi (by omega)
      have h2 := hV.2.2.2.1 (j + 1 + d)
      have h3 := rle (j + 1 + d + 1) 0 i' (Nat.zero_le _) hi'
      have e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1 := by push_cast; ring
      rw [e]
      linarith
  have hper := hV.2.1 0 0
  simp only [zero_add] at hper
  have hin : ∀ j : ℕ, j < F.J → ∀ l, l < r → F.fr 0 0 ≤ F.fr j l ∧ F.fr j l < F.fr 0 0 + n' := by
    intro j hj l hl
    constructor
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        simpa using rle 0 0 l (Nat.zero_le _) hl
      · have h1 := rlt 0 (j - 1) 0 l (by omega) hl
        have e : (0 : ℤ) + 1 + ((j - 1 : ℕ) : ℤ) = j := by omega
        rw [e] at h1
        linarith
    · have h1 := rlt j (F.J - j - 1) l 0 hl (by omega)
      have e : (j : ℤ) + 1 + ((F.J - j - 1 : ℕ) : ℤ) = F.J := by omega
      rw [e] at h1
      linarith
  have huniq : ∀ j j' : ℕ, j < F.J → j' < F.J → ∀ l l' : ℕ, l < r → l' < r →
      posOf n' (F.fr j l) = posOf n' (F.fr j' l') → j = j' ∧ l = l' := by
    intro j j' hj hj' l l' hl hl' h
    have he := residue_position_injective_window n' (F.fr 0 0) _ _ (hin j hj l hl) (hin j' hj' l' hl') h
    rcases lt_trichotomy j j' with h1 | h1 | h1
    · exfalso
      have h2 := rlt j (j' - j - 1) l l' hl hl'
      have e : (j : ℤ) + 1 + ((j' - j - 1 : ℕ) : ℤ) = j' := by omega
      rw [e] at h2
      linarith
    · subst h1
      refine ⟨rfl, ?_⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h2 | h2
      · have h3 := hV.2.2.1 j l (by omega)
        have h4 := rle j (l + 1) l' (by omega) hl'
        linarith
      · have h3 := hV.2.2.1 j l' (by omega)
        have h4 := rle j (l' + 1) l (by omega) hl
        linarith
    · exfalso
      have h2 := rlt j' (j - j' - 1) l' l hl' hl
      have e : (j' : ℤ) + 1 + ((j - j' - 1 : ℕ) : ℤ) = j := by omega
      rw [e] at h2
      linarith
  by_cases hex : ∃ j0 ∈ Finset.range F.J, ∃ l0 : Fin r, t = posOf n' (F.fr (j0 : ℤ) l0.val)
  · obtain ⟨j0, hj0, l0, ht0⟩ := hex
    have hj0' := Finset.mem_range.1 hj0
    have hz : ∀ j ∈ Finset.range F.J, j ≠ j0 →
        (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t = 0 := by
      intro j hj hne
      rw [eDel_apply, Finset.sum_eq_zero, mul_zero]
      intro l _
      refine if_neg ?_
      intro h
      exact hne (huniq j j0 (Finset.mem_range.1 hj) hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).1
    have h0 : eDel p n' F (j0 : ℤ) t = p ^ (zF F (j0 : ℤ) - F.fr j0 l0.val).toNat := by
      rw [eDel_apply, Finset.sum_eq_single l0]
      · exact if_pos ht0
      · intro l _ hne
        refine if_neg ?_
        intro h
        exact hne (Fin.ext (huniq j0 j0 hj0' hj0' l l0 l.isLt l0.isLt (h.symm.trans ht0)).2)
      · intro h
        exact absurd (Finset.mem_univ l0) h
    rw [Finset.sum_eq_single j0 hz (fun h => absurd hj0 h), h0]
    apply Nat.mul_le_mul
    · have hzz : (zF F ((j0 : ℤ) + 1) - zF F (j0 : ℤ)).toNat ≤ G' := by
        have g := hF.2.2.1 ((j0 : ℤ) + 1)
        simp only [add_sub_cancel_right] at g
        have m0 := rle (j0 : ℤ) 0 (r - 1) (Nat.zero_le _) (by omega)
        simp only [zF]
        omega
      have hα : alpha p F k (j0 : ℤ) ≤ 1 + r * k * p ^ G' := by
        simp only [alpha, Qj]
        have h1 : (if (j0 : ℤ) = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
        exact add_le_add h1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
          (le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hp hzz)))
      exact Nat.add_le_add_right (Nat.mul_le_mul_left c' hα) c'
    · apply Nat.pow_le_pow_right hp
      have g := hF.2.2.1 (j0 : ℤ)
      have m := rlt ((j0 : ℤ) - 1) 0 0 l0.val (by omega) l0.isLt
      simp only [Nat.cast_zero, add_zero, sub_add_cancel] at m
      simp only [zF]
      omega
  · push_neg at hex
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun j hj => ?_)) (Nat.zero_le _)
    rw [eDel_apply, Finset.sum_eq_zero (fun l _ => if_neg (hex j hj l)), mul_zero]

private theorem nuRow_le_Sc_add_wSz {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) {i i' : ℕ} (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hV.2.2.1 j (i + d) (by omega)
    exact le_trans h1 (le_of_lt h2)

private theorem fr_lt_fr_of_lt_index {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) {j j' : ℤ} (hjj : j < j') {i i' : ℕ}
    (hi : i < r) (hi' : i' < r) : F.fr j i < F.fr j' i' := by
  have key : ∀ d : ℕ, ∀ i', i' < r → F.fr j i < F.fr (j + 1 + d) i' := by
    intro d
    induction d with
    | zero =>
      intro i' hi'
      have h1 := nuRow_le_Sc_add_wSz hV j (show i ≤ r - 1 by omega) (by omega)
      have h2 := hV.2.2.2.1 j
      have h3 := nuRow_le_Sc_add_wSz hV (j + 1) (Nat.zero_le i') hi'
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ d ih =>
      intro i' hi'
      have h1 := ih (r - 1) (by omega)
      have h2 := hV.2.2.2.1 (j + 1 + d)
      have h3 := nuRow_le_Sc_add_wSz hV (j + 1 + d + 1) (Nat.zero_le i') hi'
      have e : j + 1 + ((d + 1 : ℕ) : ℤ) = j + 1 + d + 1 := by push_cast; ring
      rw [e]
      linarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j' = j + 1 + d := ⟨(j' - j - 1).toNat, by omega⟩
  subst hd
  exact key d i' hi'

private theorem arow_lt_self_and_sub_lt_of_framesOK (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (s : ℤ) (l : ℕ) (hl : l < r) : Arow F s l < s ∧ s - Arow F s l < G' := by
  classical
  have hV := hF.2.1
  have hstep : ∀ j : ℤ, F.fr j (r - 1) + 1 ≤ F.fr (j + 1) (r - 1) := fun j => by
    have := fr_lt_fr_of_lt_index hV (lt_add_one j) (i := r - 1) (i' := r - 1) (by omega) (by omega)
    omega
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr m (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep m
      push_cast
      linarith
  have hdown : ∀ m : ℕ, F.fr (-(m : ℤ)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep (-((m + 1 : ℕ) : ℤ))
      have e : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
      rw [e] at this
      push_cast at this ⊢
      linarith
  obtain ⟨j0, hj0, hmax⟩ := Int.exists_greatest_of_bdd (P := fun z => F.fr z (r - 1) < s)
    ⟨(s - F.fr 0 (r - 1)).toNat, fun z hz => by
      rcases le_or_gt 0 z with h0 | h0
      · have := hup z.toNat
        rw [Int.toNat_of_nonneg h0] at this
        omega
      · omega⟩
    ⟨-((F.fr 0 (r - 1) - s + 1).toNat : ℤ), by
      have := hdown (F.fr 0 (r - 1) - s + 1).toNat
      show F.fr _ (r - 1) < s
      omega⟩
  have hj1 : s ≤ F.fr (j0 + 1) (r - 1) := by
    by_contra h
    have := hmax (j0 + 1) (show F.fr (j0 + 1) (r - 1) < s by omega)
    omega
  have hgap := hF.2.2.1 (j0 + 1)
  simp only [add_sub_cancel_right] at hgap
  have hnr : (n' : ℤ) ≤ (r : ℤ) * n' := by
    have : n' ≤ r * n' := Nat.le_mul_of_pos_left n' hr
    exact_mod_cast this
  have hmemA : ∀ i < r, F.fr j0 i ∈ evensBefore F s := by
    intro i hi
    have h0 := nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi
    have h1 := nuRow_le_Sc_add_wSz hV j0 (show i ≤ r - 1 by omega) (by omega)
    have h2 := hV.2.2.2.2.1 j0 i hi
    rw [Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem]
    refine ⟨⟨?_, ?_⟩, h2.1, h2.2⟩
    · have : (G' : ℤ) ≤ n' := by exact_mod_cast hG
      linarith
    · linarith
  have hinj : Set.InjOn (fun i => F.fr j0 i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hV.2.2.1 j0 a (by omega)
      have h2 := nuRow_le_Sc_add_wSz hV j0 (show a + 1 ≤ b by omega) hb
      linarith
    · have h1 := hV.2.2.1 j0 b (by omega)
      have h2 := nuRow_le_Sc_add_wSz hV j0 (show b + 1 ≤ a by omega) ha
      linarith
  have hcardA : ((Finset.range r).image fun i => F.fr j0 i).card = r := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hpw : (evensBefore F s).Pairwise (· > ·) := evensBefore_pairwise F s
  have hlen : r ≤ (evensBefore F s).length := by
    calc r = ((Finset.range r).image fun i => F.fr j0 i).card := hcardA.symm
      _ ≤ (evensBefore F s).toFinset.card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
        exact List.mem_toFinset.2 (hmemA i (Finset.mem_range.1 hi))
      _ ≤ (evensBefore F s).length := List.toFinset_card_le _
  have hl' : l < (evensBefore F s).length := by omega
  have harow : Arow F s l = (evensBefore F s)[l] := by
    simp only [Arow]
    exact List.getD_eq_getElem _ _ hl'
  have hyl : (evensBefore F s)[l] < s := by
    have := (Formalism.MainNotions.G.symbolGeneratorData.dv_ev_mem (F := F) s _).1 (List.getElem_mem hl')
    exact this.1.2
  have hge : F.fr j0 0 ≤ (evensBefore F s)[l] := by
    by_contra hlt
    push_neg at hlt
    have hsub : ((Finset.range r).image fun i => F.fr j0 i) ⊆ ((evensBefore F s).take l).toFinset := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      have hi' := Finset.mem_range.1 hi
      have hm : F.fr j0 i ∈ (evensBefore F s).take l ++ (evensBefore F s).drop l := by
        rw [List.take_append_drop]
        exact hmemA i hi'
      rcases List.mem_append.1 hm with h | h
      · exact List.mem_toFinset.2 h
      · exfalso
        have hpw' := hpw.sublist (List.drop_sublist l (evensBefore F s))
        rw [List.drop_eq_getElem_cons hl'] at h hpw'
        have h0 := nuRow_le_Sc_add_wSz hV j0 (Nat.zero_le i) hi'
        rcases List.mem_cons.1 h with h | h
        · linarith
        · have := List.rel_of_pairwise_cons hpw' h
          linarith
    have := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le ((evensBefore F s).take l)
    have h3 := List.length_take_le l (evensBefore F s)
    omega
  rw [harow]
  constructor
  · exact hyl
  · linarith

theorem tops_near (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (t : Fin n') :
    (F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).card ≤ N₁ + 1 := by
  classical
  refine le_trans ?_ (Nat.le_succ N₁)
  have hsub : ((F.TT.filter fun s => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val)).map
      Fin.valEmbedding) ⊆ (F.TT.map Fin.valEmbedding) ∩ Formalism.G0.window n' t.val G' := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Fin.valEmbedding_apply] at hx
    obtain ⟨s, ⟨hs, l, hl⟩, rfl⟩ := hx
    refine Finset.mem_inter.2 ⟨Finset.mem_map_of_mem _ hs, ?_⟩
    obtain ⟨h1, h2⟩ := arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt
    have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have ht : (t.val : ℤ) = Arow F (s.val : ℤ) l.val % n' := by
      rw [hl]
      simp only [posOf]
      have e0 : 0 ≤ Arow F (s.val : ℤ) l.val % (n' : ℤ) := Int.emod_nonneg _ (ne_of_gt hn0)
      have e1 : Arow F (s.val : ℤ) l.val % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hs' : (s.val : ℤ) < n' := by exact_mod_cast s.isLt
    simp only [Formalism.G0.window, Finset.mem_image, Finset.mem_range]
    refine ⟨((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat, by omega, ?_⟩
    have key : (((t.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat : ℕ) : ℤ) % n') = s.val := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega), ht, Int.emod_add_emod]
      rw [show Arow F (s.val : ℤ) l.val + ((s.val : ℤ) - Arow F (s.val : ℤ) l.val) = s.val by ring]
      exact Int.emod_eq_of_lt (by positivity) hs'
    exact_mod_cast key
  calc _ = _ := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ N₁ := hI t.val t.isLt

theorem d_bound (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (mu : ℕ) (t : Fin n') :
    ∑ s ∈ F.TT, mu * eD p n' F (s.val : ℤ) t ≤ (N₁ + 1) * (mu * (r * p ^ G')) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← Finset.sum_filter_of_ne (p := fun s : Fin n' => ∃ l : Fin r, t = posOf n' (Arow F (s.val : ℤ) l.val))]
  · refine le_trans (Finset.sum_le_card_nsmul _ _ (mu * (r * p ^ G')) ?_) ?_
    · intro s _
      apply Nat.mul_le_mul_left
      rw [eD_apply]
      calc ∑ l : Fin r, (if t = posOf n' (Arow F (s.val : ℤ) l.val)
              then p ^ ((s.val : ℤ) - Arow F (s.val : ℤ) l.val).toNat else 0)
          ≤ ∑ _l : Fin r, p ^ G' := Finset.sum_le_sum fun l _ => by
            split_ifs
            · apply Nat.pow_le_pow_right hp
              have := (arow_lt_self_and_sub_lt_of_framesOK hF hr hG (s.val : ℤ) l.val l.isLt).2
              omega
            · exact Nat.zero_le _
        _ = r * p ^ G' := by simp
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (tops_near hF hr hG hI t)
  · intro s _ hne
    by_contra hno
    push_neg at hno
    apply hne
    rw [eD_apply, Finset.sum_eq_zero, mul_zero]
    intro l _
    exact if_neg (hno l)

theorem eSP_off (hF : FramesOK TT L₁ L₂ N₁ G' F) (k c' Q : ℕ) (t : Fin n') (ht : t ∉ F.TT) :
    eSP p n' F k c' Q t = 0 := by
  have hV := hF.2.1
  have h1 : ∀ j : ℤ, eDel p n' F j t = 0 := by
    intro j
    rw [eDel_apply]
    refine Finset.sum_eq_zero fun l _ => if_neg ?_
    rintro rfl
    exact ht (hV.2.2.2.2.1 j l.val l.isLt).1
  have h2 : ∀ s ∈ F.TT, eD p n' F (s.val : ℤ) t = 0 := by
    intro s hs
    rw [eD_apply]
    refine Finset.sum_eq_zero fun l _ => if_neg ?_
    rintro rfl
    exact ht (bs_top_Arow F s hs l.val)
  simp only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact Finset.sum_eq_zero fun s hs => by rw [h2 s hs, mul_zero]

theorem eSP_le (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r) (hG : G' ≤ n')
    (hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) G' N₁) (k c' : ℕ) (t : Fin n') :
    eSP p n' F k c' (p ^ G') t ≤ (c' * (1 + r * k * p ^ G') + c') * p ^ G' +
      (N₁ + 1) * (((2 * p ^ G' + 3) * c' + k * p ^ G') * (r * p ^ G')) := by
  have h1 := del_bound (p := p) hF hr hG k c' t
  have h2 := d_bound (p := p) hF hr hG hI ((2 * p ^ G' + 3) * c' + k * p ^ G') t
  have e : c' * ∑ j ∈ Finset.range F.J, alpha p F k (j : ℤ) * eDel p n' F (j : ℤ) t +
      ∑ j ∈ Finset.range F.J, c' * eDel p n' F (j : ℤ) t =
      ∑ j ∈ Finset.range F.J, (c' * alpha p F k (j : ℤ) + c') * eDel p n' F (j : ℤ) t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [eSP, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [e]
  exact add_le_add h1 h2

end Bound

end Formalism.MainNotions.Pf14
end
end

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem num_E (c' r k Q N₁ : ℕ) (hk : k ≤ c') (hN : N₁ ≤ k) (hN1 : 1 ≤ N₁) (hr : 2 ≤ r) (hQ : 3 ≤ Q) :
    (c' * (1 + r * k * Q) + c') * Q + (N₁ + 1) * (((2 * Q + 3) * c' + k * Q) * (r * Q)) ≤
      15 * c' * (N₁ + r * k) * Q ^ 2 := by
  have h1 : (2 * Q + 3) * c' + k * Q ≤ 4 * Q * c' := by
    nlinarith [Nat.mul_le_mul_right Q hk, Nat.mul_le_mul_right c' hQ]
  have h2 : N₁ + 1 ≤ 2 * k := by omega
  have h3 : (N₁ + 1) * (((2 * Q + 3) * c' + k * Q) * (r * Q)) ≤ (2 * k) * ((4 * Q * c') * (r * Q)) :=
    Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ h1)
  have h5 : 2 ≤ r * k * Q := by
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ r * k * Q := Nat.mul_le_mul (Nat.mul_le_mul hr (by omega)) (by omega)
  have h4 : (c' * (1 + r * k * Q) + c') * Q ≤ 2 * (c' * (r * k) * Q ^ 2) := by
    have e : (c' * (1 + r * k * Q) + c') * Q = c' * Q * 2 + c' * Q * (r * k * Q) := by ring
    have e2 : 2 * (c' * (r * k) * Q ^ 2) = c' * Q * (r * k * Q) + c' * Q * (r * k * Q) := by ring
    rw [e, e2]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h5) _
  have e3 : (2 * k) * ((4 * Q * c') * (r * Q)) = 8 * (c' * (r * k) * Q ^ 2) := by ring
  have e4 : 15 * c' * (N₁ + r * k) * Q ^ 2 = 15 * (c' * N₁ * Q ^ 2) + 15 * (c' * (r * k) * Q ^ 2) := by ring
  rw [e3] at h3
  rw [e4]
  omega

theorem multidegree_bound_le_a (C k r N Q c' Y a N₁ : ℝ) (hC : 30 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 1 ≤ Y) (hN1 : N₁ ≤ k) (h : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y ≤ a) :
    15 * c' * (N₁ + r * k) * Q ^ 2 ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr2 : r ≤ r ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hQ5 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
  have hQ2 : 0 ≤ Q ^ 2 := by positivity
  have h1 : N₁ + r * k ≤ 2 * (r * k) := by nlinarith
  have h2 : 15 * c' * (N₁ + r * k) * Q ^ 2 ≤ 15 * c' * (2 * (r * k)) * Q ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hQ2
  have a1 : 30 * k ≤ C * k ^ 3 := mul_le_mul hC hk3 (by linarith) (by linarith)
  have a2 : 30 * k * r ≤ C * k ^ 3 * r ^ 2 := mul_le_mul a1 hr2 (by linarith) (by positivity)
  have a3 : 30 * k * r ≤ C * k ^ 3 * r ^ 2 * N := le_trans a2 (le_mul_of_one_le_right (by positivity) hN)
  have a4 : 30 * k * r * Q ^ 2 ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := mul_le_mul a3 hQ5 hQ2 (by positivity)
  have a5 : 30 * k * r * Q ^ 2 * c' ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' := mul_le_mul_of_nonneg_right a4 hc
  have a6 : 30 * k * r * Q ^ 2 * c' ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y :=
    le_trans a5 (le_mul_of_one_le_right (by positivity) hY)
  have e : 15 * c' * (2 * (r * k)) * Q ^ 2 = 30 * k * r * Q ^ 2 * c' := by ring
  linarith

theorem spdeg {C : ℝ} (hC : 30 ≤ C) {p n' m r : ℕ} [Fact p.Prime] [NeZero n'] {TT : Finset (Fin n')} {L₁ L₂ : ℕ}
    {de h x : ℝ} {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar)
    {F : Frames n' r} (hF : FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F) (t : Fin n') (ht : t ∈ F.TT) :
    eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤
        E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
      eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤ flatDeg lam0 t := by
  have hB := hyps_basic (C := C) (by linarith) H
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := h3.2.2.2; omega
  have hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) (goodG' r de h x) (orbitWindowCount r de h x) := by
    rw [hTT]
    exact h3.1.2.2
  have hG1 : 1 ≤ goodG' r de h x := le_trans hB.one_le_depth_alt hB.depth_le_good_exponent
  have hpR : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
  have hkR : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h2
  have hNR : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hQR : (p : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := le_self_pow₀ (by linarith) (by omega)
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := by linarith
  have hcR : (8 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (8 : ℝ) ≤ (cStar : ℝ) := by
      have : 8 ≤ cStar := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  have sq_level_le_degree : orbitWindowCount r de h x ≤ m + 1 := by omega
  have hE0a : ((E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) : ℕ) : ℝ) ≤ a := by
    have := multidegree_bound_le_a C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x)
      ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y a (orbitWindowCount r de h x : ℝ) hC hkR hrR hNR hQ1
      (by linarith) (by linarith [hB.two_le_Y]) (by exact_mod_cast sq_level_le_degree) h12
    refine le_trans (le_of_eq ?_) this
    unfold E0 cPrime
    push_cast
    ring

  have hpa : (p : ℝ) ≤ a := by
    have hE : (p : ℝ) ≤ 15 * ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) *
        ((orbitWindowCount r de h x : ℝ) + r * ((m + 1 : ℕ) : ℝ)) * ((p : ℝ) ^ goodG' r de h x) ^ 2 := by
      have b1 : (1 : ℝ) ≤ 15 * ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) := by linarith
      have b2 : (1 : ℝ) ≤ (orbitWindowCount r de h x : ℝ) + r * ((m + 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ (orbitWindowCount r de h x : ℝ) := Nat.cast_nonneg _
        nlinarith
      have b3 : (p : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 2 := le_trans hQR (le_self_pow₀ hQ1 (by norm_num))
      have b4 := one_le_mul_of_one_le_of_one_le b1 b2
      calc (p : ℝ) = 1 * p := by ring
        _ ≤ _ := mul_le_mul b4 b3 (by linarith) (by linarith)
    refine le_trans hE (le_trans (le_of_eq ?_) hE0a)
    unfold E0 cPrime
    push_cast
    ring
  have hlog : 1 ≤ Real.logb p a := by
    rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_one]
    exact hpa
  have hkD : ((m + 1 : ℕ) : ℝ) ≤ Dp := by
    refine le_trans ?_ h10
    have c1 : (1 : ℝ) ≤ C * (TT.card : ℝ) := one_le_mul_of_one_le_of_one_le (by linarith) hNR
    have c2 : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := le_self_pow₀ hkR (by norm_num)
    have c3 : ((m + 1 : ℕ) : ℝ) ≤ C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 := by
      calc ((m + 1 : ℕ) : ℝ) = 1 * ((m + 1 : ℕ) : ℝ) := by ring
        _ ≤ _ := mul_le_mul c1 c2 (by linarith) (by linarith)
    exact le_trans c3 (le_mul_of_one_le_right (by positivity) hlog)
  have hkc : m + 1 ≤ cPrime n' r TT.card c0 cpp cStar := by
    have : m + 1 ≤ Dp := by exact_mod_cast hkD
    unfold cPrime
    omega
  have hQ3 : 3 ≤ p ^ goodG' r de h x := by
    calc 3 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ goodG' r de h x := Nat.pow_le_pow_right (by omega) hG1
  have hle := eSP_le (p := p) hF (by omega) hGn hI (m + 1) (cPrime n' r TT.card c0 cpp cStar) t
  have hnum := num_E (cPrime n' r TT.card c0 cpp cStar) r (m + 1) (p ^ goodG' r de h x) (orbitWindowCount r de h x) hkc sq_level_le_degree
    (one_le_orbitWindowCount r de h x) h2 hQ3
  have hfin : eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by
    unfold E0
    exact le_trans hle hnum
  refine ⟨hfin, ?_⟩
  have hfd := (flatDeg_bounds (by have := hB.m_ge; omega) (by linarith [hB.two_le_a]) h5 t (hTT ▸ ht)).1
  have : ((eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t : ℕ) : ℝ) ≤
      (flatDeg lam0 t : ℝ) := by
    have h0 : ((eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t : ℕ) : ℝ) ≤
        ((E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) : ℕ) : ℝ) := by
      exact_mod_cast hfin
    linarith
  exact_mod_cast this

end Formalism.MainNotions.Pf14

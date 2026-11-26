module

public import GroundTheory.AutomorphicForms.SatakeTriangular

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.MacdonaldRecursion
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open Finset

variable {n : ℕ}

theorem antitone_of_forall_succ_le {f : Fin n → ℤ}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j ≤ f i) : Antitone f := by
  have key : ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d → f b ≤ f a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      rw [show b = a from Fin.ext (by omega)]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < n := by omega
      exact (h ⟨a + d, hc⟩ b (by simp only; omega)).trans (ih a ⟨a + d, hc⟩ rfl)
  intro a b hab
  exact key (b - a) a b (by have := Fin.le_def.1 hab; omega)

theorem lamS_apply (S : Finset (Fin n)) (i : Fin n) : lamS S i = if i ∈ S then 1 else 0 := rfl

theorem exists_ascent {l : Fin n → ℤ} (hl : Antitone l) {S : Finset (Fin n)}
    (h : ¬ Antitone (l + lamS S)) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i = l j ∧ i ∉ S ∧ j ∈ S := by
  by_contra hne
  push Not at hne
  apply h
  refine antitone_of_forall_succ_le fun i j hij => ?_
  have hle : l j ≤ l i := hl (Fin.le_def.2 (by omega))
  simp only [Pi.add_apply, lamS_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp only [hi, hj, if_true, if_false]
  · omega
  · omega
  · rcases lt_or_eq_of_le hle with hlt | heq
    · omega
    · exact absurd hj (hne i j hij heq.symm hi)
  · omega

theorem add_lamS_comp_swap {l : Fin n → ℤ} {i j : Fin n} (hlij : l i = l j) (S : Finset (Fin n)) :
    (l + lamS S) ∘ Equiv.swap i j = l + lamS (S.map (Equiv.swap i j).toEmbedding) := by
  funext x
  simp only [Function.comp_apply, Pi.add_apply, lamS_apply, Finset.mem_map_equiv,
    Equiv.symm_swap]
  congr 1
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hlij]
  · rw [h2, hlij]
  · rfl

theorem sum_val_map_swap {S : Finset (Fin n)} {i j : Fin n} (hij : (j : ℕ) = i + 1) (hi : i ∉ S)
    (hj : j ∈ S) :
    ∑ x ∈ S.map (Equiv.swap i j).toEmbedding, (x : ℕ) + 1 = ∑ x ∈ S, (x : ℕ) := by
  rw [Finset.sum_map]
  rw [← Finset.insert_erase hj, Finset.sum_insert (Finset.notMem_erase j S),
    Finset.sum_insert (Finset.notMem_erase j S)]
  have hrest : ∑ x ∈ S.erase j, ((Equiv.swap i j).toEmbedding x : ℕ) = ∑ x ∈ S.erase j, (x : ℕ) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxj : x ≠ j := Finset.ne_of_mem_erase hx
    have hxi : x ≠ i := fun h => hi (h ▸ Finset.mem_of_mem_erase hx)
    simp [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  rw [hrest]
  simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_right]
  omega

theorem exists_perm_antitone {V : Type*} (H : (Fin n → ℤ) → V)
    (hH : ∀ (μ : Fin n → ℤ) (i j : Fin n), (j : ℕ) = i + 1 → μ j = μ i + 1 →
      H (μ ∘ Equiv.swap i j) = H μ)
    {l : Fin n → ℤ} (hl : Antitone l) (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), Antitone ((l + lamS S) ∘ σ) ∧
      H ((l + lamS S) ∘ σ) = H (l + lamS S) := by
  suffices key : ∀ k, ∀ S : Finset (Fin n), ∑ x ∈ S, (x : ℕ) = k →
      ∃ σ : Equiv.Perm (Fin n), Antitone ((l + lamS S) ∘ σ) ∧
        H ((l + lamS S) ∘ σ) = H (l + lamS S) from key _ S rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk
    by_cases ha : Antitone (l + lamS S)
    · exact ⟨1, by simpa using ha, by simp⟩
    obtain ⟨i, j, hij, hlij, hiS, hjS⟩ := exists_ascent hl ha
    have hcomp := add_lamS_comp_swap hlij S
    have hsum := sum_val_map_swap hij hiS hjS
    obtain ⟨σ, hσ, hHσ⟩ := ih _ (by omega) (S.map (Equiv.swap i j).toEmbedding) rfl
    refine ⟨Equiv.swap i j * σ, ?_, ?_⟩
    · rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hcomp]
      exact hσ
    · rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hcomp, hHσ, ← hcomp]
      refine hH _ i j hij ?_
      simp only [Pi.add_apply, lamS_apply, hiS, hjS, if_true, if_false, hlij]
      ring

def initSeg {r : ℕ} (hr : r ≤ n) : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hr)

theorem mem_initSeg {r : ℕ} (hr : r ≤ n) {i : Fin n} : i ∈ initSeg hr ↔ (i : ℕ) < r := by
  simp only [initSeg, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    simp
  · intro h
    exact ⟨⟨i, h⟩, Fin.ext (by simp)⟩

theorem card_initSeg {r : ℕ} (hr : r ≤ n) : (initSeg hr).card = r := by
  simp [initSeg]

def tailSet {m : ℕ} (hm : m ≤ n) : Finset (Fin n) :=
  Finset.univ.map ⟨tailEmb hm, tailEmb_injective hm⟩

theorem card_tailSet {m : ℕ} (hm : m ≤ n) : (tailSet hm).card = m := by
  simp [tailSet]

theorem mem_tailSet {m : ℕ} (hm : m ≤ n) {i : Fin n} : i ∈ tailSet hm ↔ n - m ≤ (i : ℕ) := by
  simp only [tailSet, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, rfl⟩
    simp [tailEmb]
  · intro h
    exact ⟨⟨i - (n - m), by omega⟩, Fin.ext (by simp [tailEmb]; omega)⟩

theorem tailSum_eq_sum_tailSet (f : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) :
    tailSum f hm = ∑ i ∈ tailSet hm, f i := by
  rw [tailSet, Finset.sum_map]
  rfl

theorem tailSum_add (f g : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) :
    tailSum (f + g) hm = tailSum f hm + tailSum g hm := by
  simp only [tailSum, Pi.add_apply, Finset.sum_add_distrib]

theorem sum_lamS_eq_card (S A : Finset (Fin n)) :
    ∑ i ∈ A, lamS S i = ((A.filter (· ∈ S)).card : ℤ) := by
  simp only [lamS_apply]
  rw [Finset.sum_boole]

theorem card_tailSet_inter_initSeg_le {m r : ℕ} (hm : m ≤ n) (hr : r ≤ n) {A S : Finset (Fin n)}
    (hA : A.card = m) (hS : S.card = r) :
    ((tailSet hm).filter (· ∈ initSeg hr)).card ≤ (A.filter (· ∈ S)).card := by
  have hAS : A.filter (· ∈ S) = A ∩ S := Finset.filter_mem_eq_inter
  have hBT : (tailSet hm).filter (· ∈ initSeg hr) = tailSet hm ∩ initSeg hr :=
    Finset.filter_mem_eq_inter
  rw [hAS, hBT]
  have h1 := Finset.card_union_add_card_inter A S
  have h2 : (A ∪ S).card ≤ n := by
    simpa using Finset.card_le_univ (A ∪ S)
  by_cases hmr : r + m ≤ n
  · have : tailSet hm ∩ initSeg hr = ∅ := by
      ext i
      simp only [Finset.mem_inter, mem_tailSet, mem_initSeg, Finset.notMem_empty, iff_false,
        not_and]
      omega
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  · have h3 := Finset.card_union_add_card_inter (tailSet hm) (initSeg hr)
    have h4 : tailSet hm ∪ initSeg hr = Finset.univ := by
      ext i
      simp only [Finset.mem_union, mem_tailSet, mem_initSeg, Finset.mem_univ, iff_true]
      omega
    rw [h4, Finset.card_univ, Fintype.card_fin, card_tailSet, card_initSeg] at h3
    omega

theorem domLE_rearrangement {l : Fin n → ℤ} (hl : Antitone l) {r : ℕ} (hr : r ≤ n)
    {S : Finset (Fin n)} (hS : S.card = r) (σ : Equiv.Perm (Fin n)) :
    DomLE ((l + lamS S) ∘ σ) (l + lamS (initSeg hr)) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [tailSum_add, tailSum_eq_sum_tailSet (lamS _), sum_lamS_eq_card,
      tailSum_eq_sum_tailSet ((l + lamS S) ∘ σ)]
    have hA : ((tailSet hm).map σ.toEmbedding).card = m := by
      rw [Finset.card_map, card_tailSet]
    have hsum : ∑ i ∈ tailSet hm, ((l + lamS S) ∘ σ) i =
        ∑ i ∈ (tailSet hm).map σ.toEmbedding, (l + lamS S) i := by
      rw [Finset.sum_map]
      rfl
    rw [hsum]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, sum_lamS_eq_card]
    have h1 := tailSum_le_sum hl hm _ hA
    have h2 := card_tailSet_inter_initSeg_le hm hr hA hS
    have h2' : (((tailSet hm).filter (· ∈ initSeg hr)).card : ℤ) ≤
        ((((tailSet hm).map σ.toEmbedding).filter (· ∈ S)).card : ℤ) := by exact_mod_cast h2
    linarith
  · show ∑ i, (l + lamS S) (σ i) = _
    rw [Equiv.sum_comp σ (l + lamS S)]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [sum_lamS_eq_card, sum_lamS_eq_card, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, hS, card_initSeg]

theorem defect_add (a b : Fin n → ℤ) : defect (a + b) = defect a + defect b := by
  rw [defect, defect, defect, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tailSum_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem antitone_lamS_initSeg {r : ℕ} (hr : r ≤ n) : Antitone (lamS (initSeg hr)) := by
  intro i j hij
  have := Fin.le_def.1 hij
  simp only [lamS_apply, mem_initSeg]
  split_ifs <;> omega

theorem defect_lamS_initSeg_pos {r : ℕ} (hr : r < n) (hr0 : 0 < r) :
    0 < defect (lamS (initSeg hr.le)) := by
  refine Finset.sum_pos' (fun m _ => ?_) ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
  · have := mul_tailSum_le (antitone_lamS_initSeg hr.le) (Nat.lt_succ_iff.1 m.2)
    linarith
  · have hsum : ∑ i, lamS (initSeg hr.le) i = r := by
      rw [sum_lamS_eq_card, Finset.filter_mem_eq_inter, Finset.univ_inter, card_initSeg]
    have htail : tailSum (lamS (initSeg hr.le)) (Nat.lt_succ_iff.1 (⟨1, by omega⟩ : Fin (n + 1)).2)
        = 0 := by
      rw [tailSum_eq_sum_tailSet, sum_lamS_eq_card]
      norm_cast
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi
      rw [mem_tailSet] at hi
      rw [mem_initSeg]
      simp only at hi
      omega
    rw [hsum, htail]
    simp only [Nat.cast_one, one_mul, mul_zero, sub_zero]
    exact_mod_cast hr0

theorem eq_zero_of_recursion (κ : Finset (Fin n) → ℝ) (hκ : ∀ S, 0 < κ S) (E : ℕ → ℂ)
    (hE : E n ≠ 0) (f : (Fin n → ℤ) → ℂ)
    (hrec : ∀ l : Fin n → ℤ, Antitone l → ∀ r ≤ n,
      E r * f l = ∑ S ∈ Finset.univ.powersetCard r, (κ S : ℂ) * f (l + lamS S))
    (hsort : ∀ l : Fin n → ℤ, Antitone l → ∀ S : Finset (Fin n),
      f (l + lamS S) = 0 ∨ ∃ σ : Equiv.Perm (Fin n), Antitone ((l + lamS S) ∘ σ) ∧
        f (l + lamS S) = f ((l + lamS S) ∘ σ))
    (h0 : f 0 = 0) : ∀ l : Fin n → ℤ, Antitone l → f l = 0 := by

  have hconst : ∀ c : ℤ, f (fun _ => c) = 0 := by
    have hstep : ∀ c : ℤ, E n * f (fun _ => c) = (κ Finset.univ : ℂ) * f (fun _ => c + 1) := by
      intro c
      have := hrec (fun _ => c) (fun _ _ _ => le_rfl) n le_rfl
      have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
        simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
      rw [this, hp, Finset.sum_singleton]
      congr 2
      funext i
      simp [lamS_apply]
    have hκu : (κ Finset.univ : ℂ) ≠ 0 := by exact_mod_cast (hκ _).ne'
    intro c
    induction c using Int.induction_on with
    | zero => exact h0
    | succ c ih =>
      have := hstep c
      rw [ih, mul_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hκu
    | pred c ih =>
      have := hstep (-(c : ℤ) - 1)
      rw [show -(c : ℤ) - 1 + 1 = -c by ring, ih, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hE

  suffices key : ∀ d : ℕ, ∀ ν : Fin n → ℤ, Antitone ν → (defect ν).toNat = d → f ν = 0 from
    fun ν hν => key _ ν hν rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro ν hν hd
    by_cases hc : ∀ i j, ν i = ν j
    · rcases n.eq_zero_or_pos with hn | hn
      · subst hn
        rw [show ν = 0 from funext fun i => i.elim0]
        exact h0
      · have : ν = fun _ => ν ⟨0, hn⟩ := funext fun i => hc i _
        rw [this]
        exact hconst _
    push Not at hc
    have hn : 0 < n := by
      obtain ⟨i, -, -⟩ := hc
      exact Fin.pos i
    set i0 : Fin n := ⟨0, hn⟩
    have hex : ∃ k, ∃ hk : k < n, ν ⟨k, hk⟩ ≠ ν i0 := by
      obtain ⟨i, j, hij⟩ := hc
      by_cases hi : ν i = ν i0
      · exact ⟨j, j.2, fun h => hij (hi.trans h.symm)⟩
      · exact ⟨i, i.2, hi⟩
    classical
    obtain ⟨r, hrn, hr0, hbefore, hrν⟩ : ∃ r, ∃ hrn : r < n, 0 < r ∧
        (∀ i : Fin n, (i : ℕ) < r → ν i = ν i0) ∧ ν ⟨r, hrn⟩ ≠ ν i0 := by
      obtain ⟨hrn, hrν⟩ := Nat.find_spec hex
      refine ⟨Nat.find hex, hrn, ?_, fun i hi => ?_, hrν⟩
      · by_contra h
        apply hrν
        congr 1
        exact Fin.ext (by simp only [i0]; omega)
      · have := Nat.find_min hex hi
        push Not at this
        exact this i.2
    obtain ⟨T, hT⟩ : ∃ T, T = initSeg hrn.le := ⟨_, rfl⟩
    obtain ⟨l, hl_def⟩ : ∃ l, l = ν - lamS T := ⟨_, rfl⟩
    have hνl : ν = l + lamS T := by rw [hl_def]; abel
    have hνr : ν ⟨r, hrn⟩ < ν i0 := lt_of_le_of_ne (hν (Fin.le_def.2 (Nat.zero_le _))) hrν
    have hl : Antitone l := by
      intro i j hij
      have hij' := Fin.le_def.1 hij
      rw [hl_def]
      simp only [Pi.sub_apply, lamS_apply, hT, mem_initSeg]
      have := hν hij
      by_cases hi : (i : ℕ) < r <;> by_cases hj : (j : ℕ) < r <;> simp only [hi, hj, if_true, if_false]
      · have := hbefore i hi
        have := hbefore j hj
        linarith
      · have hi' := hbefore i hi
        have hj' : ν j ≤ ν ⟨r, hrn⟩ := hν (Fin.le_def.2 (by simp only; omega))
        linarith
      · omega
      · linarith
    have hdef : defect ν = defect l + defect (lamS T) := by rw [hνl, defect_add]
    have hpos := defect_lamS_initSeg_pos hrn hr0
    rw [← hT] at hpos
    have hl0 : f l = 0 := by
      refine ih (defect l).toNat ?_ l hl rfl
      have := defect_nonneg hl
      omega
    have hterm : ∀ S ∈ Finset.univ.powersetCard r, f (l + lamS S) = 0 ∨ f (l + lamS S) = f ν := by
      intro S hS
      have hSr := (Finset.mem_powersetCard.1 hS).2
      rcases hsort l hl S with h | ⟨σ, hσ, hfσ⟩
      · exact Or.inl h
      · have hdom : DomLE ((l + lamS S) ∘ σ) ν := by
          rw [hνl, hT]
          exact domLE_rearrangement hl hrn.le hSr σ
        by_cases heq : (l + lamS S) ∘ σ = ν
        · exact Or.inr (hfσ.trans (by rw [heq]))
        · left
          rw [hfσ]
          have hlt := defect_lt hdom heq
          have hnn := defect_nonneg hσ
          exact ih _ (by omega) _ hσ rfl
    by_contra hfν
    have hsum := hrec l hl r hrn.le
    rw [hl0, mul_zero] at hsum
    have hsplit : ∑ S ∈ Finset.univ.powersetCard r, (κ S : ℂ) * f (l + lamS S) =
        (∑ S ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν), (κ S : ℂ)) *
          f ν := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun S hS => ?_
      split_ifs with h
      · rw [h]
      · rw [(hterm S hS).resolve_right h, mul_zero]
    have hTmem : T ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν) := by
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, by rw [hT, card_initSeg]⟩, by rw [← hνl]⟩
    have hκsum : (0 : ℝ) <
        ∑ S ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν), κ S :=
      Finset.sum_pos (fun S _ => hκ S) ⟨T, hTmem⟩
    rw [hsplit] at hsum
    have hne : (∑ S ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν),
        (κ S : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_sum]
      exact_mod_cast hκsum.ne'
    exact hfν ((mul_eq_zero.1 hsum.symm).resolve_left hne)

end Spherical

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra Finset

variable {n : ℕ}


variable (n) in
def antisymm : LaurentRing n →ₗ[ℂ] LaurentRing n where
  toFun p := ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • permAct σ p
  map_add' p q := by
    simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm]

theorem antisymm_apply (p : LaurentRing n) :
    antisymm n p = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • permAct σ p := rfl

theorem permAct_permAct (σ τ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    permAct σ (permAct τ p) = permAct (σ * τ) p := by
  rw [permAct_mul]
  rfl

theorem antisymm_permAct (τ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    antisymm n (permAct τ p) = Equiv.Perm.sign τ • antisymm n p := by
  rw [antisymm_apply, antisymm_apply, Finset.smul_sum]
  simp only [permAct_permAct]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulRight, smul_smul]
  congr 1
  rw [Equiv.Perm.sign_mul, mul_comm (Equiv.Perm.sign σ), ← mul_assoc, Int.units_mul_self, one_mul]

theorem antisymm_eq_zero_of_swap {i j : Fin n} (hij : i ≠ j) {p : LaurentRing n}
    (h : permAct (Equiv.swap i j) p = p) : antisymm n p = 0 := by
  have := antisymm_permAct (Equiv.swap i j) p
  rw [h, Equiv.Perm.sign_swap hij] at this
  simp only [Units.neg_smul, one_smul] at this
  set a := antisymm n p
  have h2 : (2 : ℂ) • a = 0 := by
    rw [two_smul]
    calc a + a = -a + a := by rw [← this]
      _ = 0 := neg_add_cancel a
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem antisymm_mul_of_symm {q : LaurentRing n} (hq : ∀ σ, permAct σ q = q) (p : LaurentRing n) :
    antisymm n (q * p) = q * antisymm n p := by
  rw [antisymm_apply, antisymm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, hq, mul_smul_comm]

def alternant (μ : Fin n → ℤ) : LaurentRing n := antisymm n (monomial μ)

theorem permAct_monomial (σ : Equiv.Perm (Fin n)) (μ : Fin n → ℤ) :
    permAct σ (monomial μ) = monomial (μ ∘ σ.symm) :=
  permAct_single σ μ 1

theorem alternant_eq_zero {μ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (h : μ i = μ j) :
    alternant μ = 0 := by
  refine antisymm_eq_zero_of_swap hij ?_
  rw [permAct_monomial, Equiv.symm_swap]
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem monomial_add (μ ν : Fin n → ℤ) : monomial (μ + ν) = monomial μ * monomial ν := by
  simp only [monomial, single_mul_single, mul_one]

theorem permAct_monomial_const (c : ℤ) (σ : Equiv.Perm (Fin n)) :
    permAct σ (monomial fun _ => c) = monomial fun _ => c := by
  rw [permAct_monomial]
  rfl

theorem alternant_add_const (μ : Fin n → ℤ) (c : ℤ) :
    alternant (μ + fun _ => c) = monomial (fun _ => c) * alternant μ := by
  rw [alternant, alternant, monomial_add, mul_comm, antisymm_mul_of_symm (permAct_monomial_const c)]

theorem alternant_eq_det (μ : Fin n → ℤ) :
    alternant μ = (Matrix.of fun a b : Fin n => monomial (Pi.single a (μ b))).det := by
  rw [alternant, antisymm_apply, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Matrix.of_apply, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, permAct_single]
  congr 1
  funext x
  rw [Finset.sum_apply, Finset.sum_eq_single (σ.symm x)]
  · simp
  · intro b _ hb
    simp only [Pi.single_apply]
    rw [if_neg]
    intro h
    exact hb (by rw [h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h


variable (n) in
def staircase : Fin n → ℤ := fun i => (n : ℤ) - 1 - i

theorem staircase_injective : Function.Injective (staircase n) := by
  intro i j h
  simp only [staircase] at h
  exact Fin.ext (by omega)

abbrev varL (a : Fin n) : LaurentRing n := monomial (Pi.single a 1)

theorem monomial_single_natCast (a : Fin n) (m : ℕ) :
    monomial (Pi.single a (m : ℤ)) = varL a ^ m := by
  simp only [varL, monomial, single_pow, one_pow]
  congr 1
  funext x
  simp [Pi.single_apply]


open Polynomial in
def rootPoly (n : ℕ) : (LaurentRing n)[X] := ∏ a : Fin n, (X - C (varL a))

open Polynomial in
theorem rootPoly_monic : (rootPoly n).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _

open Polynomial in
theorem natDegree_rootPoly : (rootPoly n).natDegree = n := by
  rw [rootPoly, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C _]
  simp

open Polynomial in
theorem eval_rootPoly (a : Fin n) : (rootPoly n).eval (varL a) = 0 := by
  rw [rootPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)


open Polynomial in
def remCoeff (m k : ℕ) : LaurentRing n := ((X ^ m : (LaurentRing n)[X]) %ₘ rootPoly n).coeff k


open Polynomial in
theorem pow_eq_sum_remCoeff (hn : 0 < n) (a : Fin n) (m : ℕ) :
    varL a ^ m = ∑ k : Fin n, remCoeff (n := n) m k * varL a ^ (k : ℕ) := by
  have hne : rootPoly n ≠ 1 := by
    intro h
    have := natDegree_rootPoly (n := n)
    rw [h, natDegree_one] at this
    omega
  have hdeg : ((X ^ m : (LaurentRing n)[X]) %ₘ rootPoly n).natDegree < n := by
    have := natDegree_modByMonic_lt (X ^ m : (LaurentRing n)[X]) rootPoly_monic hne
    rwa [natDegree_rootPoly] at this
  have h1 : (X ^ m : (LaurentRing n)[X]).eval (varL a) =
      ((X ^ m : (LaurentRing n)[X]) %ₘ rootPoly n).eval (varL a) := by
    conv_lhs => rw [← modByMonic_add_div (X ^ m : (LaurentRing n)[X]) (rootPoly n)]
    rw [eval_add, eval_mul, eval_rootPoly, zero_mul, add_zero]
  rw [eval_pow, eval_X, eval_eq_sum_range' hdeg, Finset.sum_range] at h1
  rw [h1]
  rfl

def vdm : Matrix (Fin n) (Fin n) (LaurentRing n) := Matrix.of fun a k => varL a ^ (k : ℕ)

def remMat (m : Fin n → ℕ) : Matrix (Fin n) (Fin n) (LaurentRing n) :=
  Matrix.of fun k b => remCoeff (m b) k

theorem alternant_natCast_eq (hn : 0 < n) (m : Fin n → ℕ) :
    alternant (fun b => (m b : ℤ)) = vdm.det * (remMat m).det := by
  rw [alternant_eq_det, ← Matrix.det_mul]
  congr 1
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, vdm, remMat]
  rw [monomial_single_natCast, pow_eq_sum_remCoeff hn a (m b)]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

open Polynomial in
theorem remMat_staircase (hn : 0 < n) :
    remMat (fun b : Fin n => n - 1 - (b : ℕ)) = Fin.revPerm.permMatrix (LaurentRing n) := by
  ext k b
  simp only [remMat, Matrix.of_apply, remCoeff, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
  have hlt : (X ^ (n - 1 - (b : ℕ)) : (LaurentRing n)[X]).degree < (rootPoly n).degree := by
    rw [degree_X_pow, degree_eq_natDegree rootPoly_monic.ne_zero, natDegree_rootPoly]
    exact_mod_cast (show n - 1 - (b : ℕ) < n by omega)
  rw [(modByMonic_eq_self_iff rootPoly_monic).2 hlt, coeff_X_pow]
  by_cases h : (k : ℕ) = n - 1 - (b : ℕ)
  · rw [if_pos h, if_pos]
    exact Fin.ext (by simp [Fin.val_rev]; omega)
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [← h']
    simp [Fin.val_rev]
    omega

theorem staircase_eq_natCast :
    staircase n = fun b : Fin n => ((n - 1 - (b : ℕ) : ℕ) : ℤ) := by
  funext b
  simp only [staircase]
  have := b.2
  omega

theorem exists_alternant_eq_mul (μ : Fin n → ℤ) :
    ∃ q, alternant μ = alternant (staircase n) * q := by
  rcases n.eq_zero_or_pos with hn | hn
  · subst hn
    exact ⟨1, by rw [mul_one]; congr 1; funext i; exact i.elim0⟩

  set s : LaurentRing n := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : LaurentRing n)
  have hs : s * s = 1 := by
    simp only [s]
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hδ : alternant (staircase n) = vdm.det * s := by
    rw [staircase_eq_natCast, alternant_natCast_eq hn, remMat_staircase hn, Matrix.det_permutation]
  have hV : vdm.det = alternant (staircase n) * s := by
    rw [hδ, mul_assoc, hs, mul_one]

  set c : ℤ := ∑ i, |μ i|
  have hc : ∀ i, 0 ≤ μ i + c := by
    intro i
    have := Finset.single_le_sum (f := fun i => |μ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have := neg_abs_le (μ i)
    simp only [c]
    linarith
  have hshift : (μ + fun _ => c) = fun b => (((μ b + c).toNat : ℕ) : ℤ) := by
    funext b
    simp only [Pi.add_apply]
    rw [Int.toNat_of_nonneg (hc b)]
  have h1 := alternant_add_const μ c
  rw [hshift, alternant_natCast_eq hn, hV] at h1
  refine ⟨monomial (fun _ => -c) * s * (remMat fun b => (μ b + c).toNat).det, ?_⟩
  have hinv : monomial (fun _ : Fin n => -c) * monomial (fun _ => c) = 1 := by
    rw [← monomial_add]
    simp only [Pi.add_def, neg_add_cancel]
    rfl
  calc alternant μ = monomial (fun _ : Fin n => -c) * (monomial (fun _ => c) * alternant μ) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [← h1]; ring

theorem exists_antisymm_eq_mul (p : LaurentRing n) :
    ∃ q, antisymm n p = alternant (staircase n) * q := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨qx, hqx⟩ := hx
    obtain ⟨qy, hqy⟩ := hy
    exact ⟨qx + qy, by rw [map_add (f := _), hqx, hqy, mul_add]⟩
  | single μ c =>
    obtain ⟨q, hq⟩ := exists_alternant_eq_mul μ
    refine ⟨c • q, ?_⟩
    have : (single μ c : LaurentRing n) = c • monomial μ := by
      simp [monomial, smul_single']
    rw [this, map_smul, ← alternant, hq, mul_smul_comm]

theorem coeff_alternant_staircase :
    (alternant (staircase n)).coeff (staircase n) = 1 := by
  rw [alternant, antisymm_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [permAct_monomial]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [show (Equiv.symm (1 : Equiv.Perm (Fin n))) = 1 from rfl]
    simp [monomial, AddMonoidAlgebra.coeff_single]
  · intro σ _ hσ
    rw [Units.smul_def, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, monomial,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg, smul_zero]
    intro h
    apply hσ
    refine Equiv.ext fun x => ?_
    have := congrFun h x
    simp only [Function.comp_apply] at this
    have := staircase_injective this
    rw [Equiv.symm_apply_eq] at this
    exact this.symm
  · simp

theorem alternant_staircase_ne_zero : alternant (staircase n) ≠ 0 := by
  intro h
  have := coeff_alternant_staircase (n := n)
  rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  exact zero_ne_one this

def altQuot (p : LaurentRing n) : LaurentRing n := (exists_antisymm_eq_mul p).choose

theorem alternant_mul_altQuot (p : LaurentRing n) :
    alternant (staircase n) * altQuot p = antisymm n p :=
  (exists_antisymm_eq_mul p).choose_spec.symm

theorem altQuot_eq_of_mul {p q : LaurentRing n} (h : alternant (staircase n) * q = antisymm n p) :
    altQuot p = q :=
  mul_left_cancel₀ alternant_staircase_ne_zero ((alternant_mul_altQuot p).trans h.symm)

theorem altQuot_add (p q : LaurentRing n) : altQuot (p + q) = altQuot p + altQuot q :=
  altQuot_eq_of_mul (by rw [mul_add, alternant_mul_altQuot, alternant_mul_altQuot, map_add (f := _)])

theorem altQuot_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentRing n) :
    altQuot (∑ i ∈ s, f i) = ∑ i ∈ s, altQuot (f i) :=
  altQuot_eq_of_mul (by rw [Finset.mul_sum, map_sum]; simp only [alternant_mul_altQuot])

theorem altQuot_smul (c : ℂ) (p : LaurentRing n) : altQuot (c • p) = c • altQuot p :=
  altQuot_eq_of_mul (by rw [mul_smul_comm, alternant_mul_altQuot, map_smul])

theorem altQuot_mul_of_symm {q : LaurentRing n} (hq : ∀ σ, permAct σ q = q) (p : LaurentRing n) :
    altQuot (q * p) = q * altQuot p :=
  altQuot_eq_of_mul (by
    rw [antisymm_mul_of_symm hq, ← alternant_mul_altQuot p]
    ring)

theorem altQuot_eq_zero_of_swap {i j : Fin n} (hij : i ≠ j) {p : LaurentRing n}
    (h : permAct (Equiv.swap i j) p = p) : altQuot p = 0 :=
  altQuot_eq_of_mul (by rw [mul_zero, antisymm_eq_zero_of_swap hij h])

def esymmL (n r : ℕ) : LaurentRing n := ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, monomial (lamS S)

theorem lamS_comp_symm (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    lamS S ∘ σ.symm = lamS (S.map σ.toEmbedding) := by
  funext x
  simp only [Function.comp_apply, lamS_apply, Finset.mem_map_equiv]

theorem permAct_esymmL (r : ℕ) (σ : Equiv.Perm (Fin n)) : permAct σ (esymmL n r) = esymmL n r := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [esymmL, map_sum]
  simp only [permAct_monomial, lamS_comp_symm]
  refine Finset.sum_nbij' (fun S => S.map σ.toEmbedding) (fun S => S.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro S hS
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at hS ⊢
    exact hS
  · intro S hS
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at hS ⊢
    exact hS
  · intro S _
    ext x
    simp [Finset.mem_map_equiv]
  · intro S _
    ext x
    simp [Finset.mem_map_equiv]

theorem esymmL_mul_monomial (r : ℕ) (l : Fin n → ℤ) :
    esymmL n r * monomial l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      monomial (l + lamS S) := by
  rw [esymmL, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [add_comm, monomial_add]

theorem esymmL_mul_altQuot (r : ℕ) (l : Fin n → ℤ) (g : LaurentRing n) :
    esymmL n r * altQuot (monomial l * g) = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      altQuot (monomial (l + lamS S) * g) := by
  rw [← altQuot_mul_of_symm (permAct_esymmL r), ← mul_assoc, esymmL_mul_monomial, Finset.sum_mul,
    altQuot_sum]

def schur (l : Fin n → ℤ) : LaurentRing n := altQuot (monomial (l + staircase n))

theorem alternant_mul_schur (l : Fin n → ℤ) :
    alternant (staircase n) * schur l = alternant (l + staircase n) :=
  alternant_mul_altQuot _

theorem esymmL_mul_schur (r : ℕ) (l : Fin n → ℤ) :
    esymmL n r * schur l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, schur (l + lamS S) := by
  have h := esymmL_mul_altQuot r l (monomial (staircase n))
  simp only [← monomial_add] at h
  rw [schur, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [schur, add_right_comm]

theorem schur_eq_zero_of_ascent {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : schur μ = 0 := by
  refine mul_left_cancel₀ (alternant_staircase_ne_zero (n := n)) ?_
  rw [alternant_mul_schur, mul_zero]
  refine alternant_eq_zero (i := i) (j := j) (fun h => by rw [h] at hij; omega) ?_
  simp only [Pi.add_apply, staircase, hμ]
  push_cast [hij]
  ring

def hlFactor (n : ℕ) (t : ℂ) : LaurentRing n :=
  ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), (varL p.1 - t • varL p.2)

def hlR (t : ℂ) (l : Fin n → ℤ) : LaurentRing n := altQuot (monomial l * hlFactor n t)

theorem esymmL_mul_hlR (t : ℂ) (r : ℕ) (l : Fin n → ℤ) :
    esymmL n r * hlR t l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, hlR t (l + lamS S) :=
  esymmL_mul_altQuot r l _

theorem altQuot_sub_smul (t : ℂ) (p q : LaurentRing n) :
    altQuot (p - t • q) = altQuot p - t • altQuot q := by
  rw [sub_eq_add_neg, ← neg_smul, altQuot_add, altQuot_smul, neg_smul, ← sub_eq_add_neg]

theorem permAct_varL (σ : Equiv.Perm (Fin n)) (a : Fin n) : permAct σ (varL a) = varL (σ a) := by
  rw [varL, permAct_monomial]
  congr 1
  funext x
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem swap_lt_swap {i j a b : Fin n} (hij : (j : ℕ) = i + 1) (hab : a < b)
    (hne : ¬(a = i ∧ b = j)) : Equiv.swap i j a < Equiv.swap i j b := by
  have hv : ∀ x : Fin n, ((Equiv.swap i j x : Fin n) : ℕ) =
      if (x : ℕ) = i then (j : ℕ) else if (x : ℕ) = j then (i : ℕ) else (x : ℕ) := by
    intro x
    rw [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]
  rw [Fin.lt_def, hv, hv]
  rw [Fin.lt_def] at hab
  have : ¬((a : ℕ) = i ∧ (b : ℕ) = j) := fun h => hne ⟨Fin.ext h.1, Fin.ext h.2⟩
  split_ifs <;> omega

theorem hlR_swap (t : ℂ) {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : hlR t μ = t • hlR t (μ ∘ Equiv.swap i j) := by
  classical
  set s := Equiv.swap i j with hs
  have hij' : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt : i < j := Fin.lt_def.2 (by omega)
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) with hP
  set fac : Fin n × Fin n → LaurentRing n := fun p => varL p.1 - t • varL p.2 with hfac
  have hmem : (i, j) ∈ P := by simp [hP, hlt]
  set D' := ∏ p ∈ P.erase (i, j), fac p with hD'
  have hD : hlFactor n t = fac (i, j) * D' := by
    rw [hD', Finset.mul_prod_erase P fac hmem]
    rfl

  have hsD' : permAct s D' = D' := by
    rw [hD', map_prod]
    refine Finset.prod_nbij' (fun p => (s p.1, s p.2)) (fun p => (s p.1, s p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_erase] at hp ⊢
      obtain ⟨hne, hpP⟩ := hp
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hpP ⊢
      have hne' : ¬(p.1 = i ∧ p.2 = j) := fun h => hne (Prod.ext h.1 h.2)
      refine ⟨fun h => ?_, swap_lt_swap hij hpP hne'⟩
      simp only [Prod.mk.injEq] at h
      have h1 : p.1 = j := by
        have := congrArg s h.1
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have h2 : p.2 = i := by
        have := congrArg s h.2
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      rw [h1, h2] at hpP
      exact absurd hlt (not_lt.2 hpP.le)
    · intro p hp
      rw [Finset.mem_erase] at hp ⊢
      obtain ⟨hne, hpP⟩ := hp
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hpP ⊢
      have hne' : ¬(p.1 = i ∧ p.2 = j) := fun h => hne (Prod.ext h.1 h.2)
      refine ⟨fun h => ?_, swap_lt_swap hij hpP hne'⟩
      simp only [Prod.mk.injEq] at h
      have h1 : p.1 = j := by
        have := congrArg s h.1
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have h2 : p.2 = i := by
        have := congrArg s h.2
        rwa [hs, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      rw [h1, h2] at hpP
      exact absurd hlt (not_lt.2 hpP.le)
    · intro p _
      simp [hs, Equiv.swap_apply_self]
    · intro p _
      simp [hs, Equiv.swap_apply_self]
    · intro p _
      simp only [hfac, map_sub, map_smul, permAct_varL]

  have hkey : monomial (μ ∘ s) * varL j = monomial μ * varL i := by
    rw [varL, varL, ← monomial_add, ← monomial_add]
    congr 1
    funext x
    simp only [Pi.add_apply, Function.comp_apply, hs, Equiv.swap_apply_def, Pi.single_apply]
    split_ifs <;> simp_all
  have hss : μ ∘ s ∘ s = μ := by
    funext x
    simp [hs, Equiv.swap_apply_self]
  have hY : permAct s ((monomial μ - t • monomial (μ ∘ s)) * fac (i, j)) =
      (monomial μ - t • monomial (μ ∘ s)) * fac (i, j) := by
    simp only [hfac, map_mul, map_sub, map_smul, permAct_varL]
    rw [permAct_monomial, permAct_monomial,
      show (s.symm : Equiv.Perm (Fin n)) = s from Equiv.symm_swap i j, Function.comp_assoc, hss,
      hs, Equiv.swap_apply_left, Equiv.swap_apply_right, ← hs]
    simp only [Algebra.smul_def]
    linear_combination (1 - algebraMap ℂ (LaurentRing n) t ^ 2) * hkey
  have hzero : altQuot ((monomial μ - t • monomial (μ ∘ s)) * hlFactor n t) = 0 := by
    rw [hD, ← mul_assoc]
    refine altQuot_eq_zero_of_swap hij' ?_
    rw [map_mul, hY, hsD']
  rw [sub_mul, smul_mul_assoc, altQuot_sub_smul] at hzero
  rw [hlR, hlR]
  exact sub_eq_zero.1 hzero

end Spherical

end GroundTheory.Automorphic

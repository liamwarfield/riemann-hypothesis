module

public import Formalism.PieriBlockIdeals.LemmaWAssembled

@[expose] public section

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.WeightExchangeChainHolds
section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.ContentLinkageHolds
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical

theorem comb_roots_prod {K : Type} [Field K] {N : ℕ} (f : Fin N → K) :
    (∏ a, (X + C (f a))).roots = Multiset.map (fun a => -f a) Finset.univ.val := by
  have h : (∏ a, (X + C (f a))) =
      ((Multiset.map (fun a => -f a) Finset.univ.val).map fun x => X - C x).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [sub_eq_add_neg]
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]

theorem contentLinkage_holds : Linkage := by
  intro l K _ _ N U U' c hl hprod
  haveI : Fact l.Prime := ⟨hl⟩
  have hr := congrArg Polynomial.roots hprod
  have hU := comb_roots_prod (fun a => (((U a + c : ℤ)) : K))
  have hU' := comb_roots_prod (fun a => (((U' a + c : ℤ)) : K))
  rw [hU, hU'] at hr
  let ψ : ZMod l →+* K := ZMod.castHom (dvd_refl l) K
  have hψ : Function.Injective ψ := ψ.injective
  have key : ∀ V : Fin N → ℤ, Multiset.map (fun a => -(((V a + c : ℤ)) : K)) Finset.univ.val =
      Multiset.map ψ (Multiset.map (fun a => -(((V a + c : ℤ)) : ZMod l)) Finset.univ.val) := by
    intro V
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp [ψ, map_intCast]
  rw [key U, key U'] at hr
  have h2 := Multiset.map_injective hψ hr
  have h3 := congrArg (Multiset.map fun z : ZMod l => -z - (c : ZMod l)) h2
  simp only [Multiset.map_map] at h3
  convert h3 using 2 <;> (try simp only [Function.comp_apply]; push_cast; ring)

end Formalism.CohomologicalDescent
end
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.WeightExchangeBoundHolds
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

theorem we_msum (Y A Bm X : Multiset ℤ) (lo hi : ℤ) (hYA : Y ≤ A) (hA : A = Bm + X)
    (hc : Multiset.card Y = Multiset.card Bm) (hin : ∀ a ∈ A, lo ≤ a ∧ a ≤ hi) :
    |Bm.sum - Y.sum| ≤ (Multiset.card X : ℤ) * (hi - lo) := by
  subst hA
  have noMem : hi < lo → ∀ S : Multiset ℤ, (∀ a ∈ S, lo ≤ a ∧ a ≤ hi) → Multiset.card S = 0 := by
    intro hlt S hS
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne)
    have := hS a ha
    omega
  have hP : Y - Bm ≤ X := Multiset.sub_le_iff_le_add.2 (by rw [add_comm]; exact hYA)
  have hYs : Y.sum = (Y - Bm).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.sum_add]
  have hBs : Bm.sum = (Bm - Y).sum + (Y ∩ Bm).sum := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.sum_add, Multiset.inter_comm]
  have hYc : Multiset.card Y = Multiset.card (Y - Bm) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Y Bm]
    rw [Multiset.card_add]
  have hBc : Multiset.card Bm = Multiset.card (Bm - Y) + Multiset.card (Y ∩ Bm) := by
    conv_lhs => rw [← Multiset.sub_add_inter Bm Y]
    rw [Multiset.card_add, Multiset.inter_comm]
  have hPQ : Multiset.card (Y - Bm) = Multiset.card (Bm - Y) := by omega
  have memP : ∀ a ∈ Y - Bm, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_of_le hYA (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha))
  have memQ : ∀ a ∈ Bm - Y, lo ≤ a ∧ a ≤ hi := fun a ha =>
    hin a (Multiset.mem_add.2 (Or.inl (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)))
  have memX : ∀ a ∈ X, lo ≤ a ∧ a ≤ hi := fun a ha => hin a (Multiset.mem_add.2 (Or.inr ha))
  have P1 := Multiset.sum_le_card_nsmul (Y - Bm) hi (fun a ha => (memP a ha).2)
  have P2 : Multiset.card (Y - Bm) • lo ≤ (Y - Bm).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memP a ha).1)
  have Q1 := Multiset.sum_le_card_nsmul (Bm - Y) hi (fun a ha => (memQ a ha).2)
  have Q2 : Multiset.card (Bm - Y) • lo ≤ (Bm - Y).sum :=
    Multiset.card_nsmul_le_sum (fun a ha => (memQ a ha).1)
  rw [hPQ] at P1 P2
  simp only [nsmul_eq_mul] at P1 P2 Q1 Q2
  have hm : (Multiset.card (Bm - Y) : ℤ) * (hi - lo) ≤ (Multiset.card X : ℤ) * (hi - lo) := by
    by_cases h : lo ≤ hi
    · apply mul_le_mul_of_nonneg_right _ (by linarith)
      have := Multiset.card_le_card hP
      rw [hPQ] at this
      exact_mod_cast this
    · push_neg at h
      rw [noMem h _ memQ, noMem h X memX]
  rw [hYs, hBs, abs_le]
  constructor <;> linarith

theorem shiftSumBound_holds : KapSum := by
  intro l b t κ U kap hl htl hU hkap hle
  have : NeZero l := ⟨by omega⟩
  have hlpos : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  obtain ⟨lo, hlo⟩ : ∃ lo : ℤ, lo = b - (κ : ℤ) := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : ℤ, hi = b + (t : ℤ) - 1 + (κ : ℤ) := ⟨_, rfl⟩
  have hwin : hi < lo + l := by omega
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ u, g u = lo + (u - lo) % (l : ℤ) := ⟨_, fun _ => rfl⟩
  have g_ge : ∀ u, lo ≤ g u := fun u => by
    rw [hg]
    have := Int.emod_nonneg (u - lo) hlpos.ne'
    linarith
  have g_fix : ∀ v, lo ≤ v → v ≤ hi → g v = v := fun v h1 h2 => by
    rw [hg, Int.emod_eq_of_lt (by linarith) (by linarith)]
    ring
  have g_mod : ∀ u, g u ≡ u [ZMOD (l : ℤ)] := fun u => by
    have h := (Int.mod_modEq (u - lo) (l : ℤ)).add_left lo
    rw [hg]
    rwa [show lo + (u - lo) = u by ring] at h
  have g_cong : ∀ u v, u ≡ v [ZMOD (l : ℤ)] → g u = g v := fun u v h => by
    have e : (u - lo) % (l : ℤ) = (v - lo) % (l : ℤ) := Int.ModEq.sub_right lo h
    rw [hg, hg, e]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ZMod l → ℤ, ∀ u : ℤ, ρ (u : ZMod l) = g u :=
    ⟨fun z => lo + ((z - (lo : ZMod l)).val : ℤ), fun u => by
      show lo + ((((u : ZMod l) - (lo : ZMod l))).val : ℤ) = g u
      rw [← Int.cast_sub, ZMod.val_intCast, hg]⟩
  have hvW : ∀ s : Fin t, lo ≤ b + ((s : ℕ) : ℤ) - kap s ∧ b + ((s : ℕ) : ℤ) - kap s ≤ hi :=
    fun s => by
      have h1 := s.isLt
      have h2 := abs_le.1 (hkap s)
      omega
  have hY : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.map g U.val := by
    have h1 := Multiset.map_le_map (f := ρ) hle
    rw [Multiset.map_map, Multiset.map_map] at h1
    refine Eq.trans_le (Multiset.map_congr rfl fun s _ => ?_)
      (h1.trans_eq (Multiset.map_congr rfl fun u _ => ?_))
    · simp only [Function.comp_apply]
      rw [hρ, g_fix _ (hvW s).1 (hvW s).2]
    · simp only [Function.comp_apply]
      rw [hρ]
  have hYA : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) := by
    have hself : Multiset.filter (fun x => x ≤ hi)
        (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val) =
        Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val :=
      Multiset.filter_eq_self.2 (fun a ha => by
        rw [Multiset.mem_map] at ha
        obtain ⟨s, -, rfl⟩ := ha
        exact (hvW s).2)
    rw [← hself]
    exact Multiset.filter_le_filter (p := fun x => x ≤ hi) hY
  have hin : ∀ a ∈ Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val), lo ≤ a ∧ a ≤ hi := by
    intro a ha
    rw [Multiset.mem_filter, Multiset.mem_map] at ha
    obtain ⟨⟨u, -, rfl⟩, h⟩ := ha
    exact ⟨g_ge u, h⟩
  have hF : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map g (Multiset.filter (fun u => g u ≤ hi) U.val) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map g) (Multiset.filter_congr fun _ _ => Iff.rfl)
  have hfirst : Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val := by
    have hinj : Function.Injective (fun s : Fin t => b + ((s : ℕ) : ℤ)) := by
      intro s1 s2 h
      have h' : b + ((s1 : ℕ) : ℤ) = b + ((s2 : ℕ) : ℤ) := h
      exact Fin.ext (by omega)
    have hnd1 : (Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)).Nodup := by
      apply Multiset.Nodup.filter
      apply Multiset.Nodup.filter
      exact U.nodup
    rw [Multiset.Nodup.ext hnd1 (Multiset.Nodup.map hinj (Finset.nodup _))]
    intro a
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_Icc, Multiset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, -⟩, h1, h2⟩
      have hn := Int.toNat_of_nonneg (show 0 ≤ a - b by omega)
      refine ⟨⟨(a - b).toNat, by omega⟩, ?_⟩
      show b + (((a - b).toNat : ℕ) : ℤ) = a
      omega
    · rintro ⟨s, rfl⟩
      have hs := s.isLt
      refine ⟨⟨hU s, ?_⟩, by omega, by omega⟩
      rw [g_fix _ (by omega) (by omega)]
      omega
  have hA : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val +
      Multiset.map g (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)) := by
    rw [hF]
    conv_lhs => rw [← Multiset.filter_add_not (p := fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (s := Multiset.filter (fun u => g u ≤ hi) U.val)]
    rw [Multiset.map_add (f := _), hfirst, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun s _ => by
      have hs := s.isLt
      simp only [Function.comp_apply]
      exact g_fix _ (by omega) (by omega)
  have hR : ∀ u, (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
      x ≡ u [ZMOD (l : ℤ)]) ↔ g u ≤ hi := by
    intro u
    constructor
    · rintro ⟨x, hx, hxu⟩
      rw [Finset.mem_Icc] at hx
      rw [← g_cong x u hxu, g_fix x (by omega) (by omega)]
      omega
    · intro hu
      exact ⟨g u, Finset.mem_Icc.2 ⟨by have := g_ge u; omega, by omega⟩, g_mod u⟩
  have hcard : Multiset.card (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val)) = mwCount l b t κ U := by
    unfold mwCount
    rw [← Finset.card_val, Finset.filter_val, Finset.filter_val,
      Multiset.filter_filter, Multiset.filter_filter]
    congr 1
    have e : Multiset.filter (fun a => a ∉ Finset.Icc b (b + (t : ℤ) - 1) ∧ g a ≤ hi) U.val =
        Multiset.filter (fun a => (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
          x ≡ a [ZMOD (l : ℤ)]) ∧ a ∉ Finset.Icc b (b + (t : ℤ) - 1)) U.val :=
      Multiset.filter_congr (fun u _ => by rw [hR u]; exact and_comm)
    convert e using 2
  have key := we_msum _ _ _ _ lo hi hYA hA
    (by rw [Multiset.card_map, Multiset.card_map]) hin
  rw [Multiset.card_map, hcard] at key
  have hBs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := (Finset.sum_eq_multiset_sum _ _).symm
  have hYs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) - kap s) := (Finset.sum_eq_multiset_sum _ _).symm
  rw [hBs, hYs, Finset.sum_sub_distrib, sub_sub_cancel] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  omega

theorem weightExchangeBound_holds : WEArith := by
  intro k j t q l h κ mw mwp U U' kc kp _ _ hU0 hU'h hsum htop hkc hkp
  have hlkp : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self kp).trans hkp) (by positivity)
  have hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) := (neg_le_abs kc).trans hkc
  have hq : ∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q), (h : ℤ) ≤
      (q : ℤ) * h := by
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc : (Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q)).card ≤ q := by
      refine le_trans (Finset.card_le_card_of_injOn (fun a => (a : ℕ) - (k + j)) ?_ ?_)
        (Finset.card_range q).le
      · intro a ha
        simp at ha ⊢
        omega
      · intro a ha a' ha' hab
        simp at ha ha'
        have hab' : (a : ℕ) - (k + j) = (a' : ℕ) - (k + j) := hab
        exact Fin.ext (by omega)
    exact_mod_cast hc
  rw [Finset.sum_filter] at hq
  have hpt : ∀ a ∈ (Finset.univ : Finset (Fin (k + j + t + q))),
      (if (a : ℕ) < k + j then U a - U' a else 0) +
        (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t then U a else 0) ≤
      (if k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + q then (h : ℤ) else 0) +
        (if k + j + q ≤ (a : ℕ) then U' a else 0) + (U a - U' a) := by
    intro a _
    have h1 := hU0 a
    have h2 := hU'h a
    split_ifs <;> omega
  have hsumle := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsumle
  simp only [Finset.sum_filter] at htop ⊢
  nlinarith

end Formalism.CohomologicalDescent
end
end

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

theorem map_cast_image_val_eq (l N : ℕ) (W : Fin N → ℤ) (hW : StrictAnti W) :
    Multiset.map (fun u : ℤ => (u : ZMod l)) (Finset.univ.image W).val =
      Multiset.map (fun a => ((W a : ℤ) : ZMod l)) Finset.univ.val := by
  rw [Finset.image_val_of_injOn hW.injective.injOn, Multiset.map_map]
  rfl

theorem sum_filter_block_eq (k j t q : ℕ) (U : Fin (k + j + t + q) → ℤ) (b : ℤ)
    (hblock : ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) :
    ∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := by
  refine Finset.sum_bij'
    (fun a ha => (⟨k + j + t - 1 - (a : ℕ), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      omega⟩ : Fin t))
    (fun s _ => (⟨k + j + t - 1 - (s : ℕ), by
      have := s.isLt
      omega⟩ : Fin (k + j + t + q))) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro s _
    have := s.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    ext
    simp only
    omega
  · intro s _
    have := s.isLt
    ext
    simp only
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [hblock a ha.1 ha.2]

theorem weightExchangeChain_holds : WEChain := by
  intro k j t q l h κ K _ _ U U' V V' b b' c c' kc kp hl htl hU hU' hV hV' hU0 hU'h hsum hblock hVb
    hprodU hprodV hkc hkp hmU hmV hfilt
  have hlink := contentLinkage_holds l K _ U U' c hl hprodU
  have hlinkV := contentLinkage_holds l K _ V V' c' hl hprodV
  have hmemU : ∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ Finset.univ.image U := by
    intro s
    have hs := s.isLt
    refine Finset.mem_image.mpr ⟨⟨k + j + t - 1 - (s : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    have h1 : k + j + t - 1 - (k + j + t - 1 - (s : ℕ)) = (s : ℕ) := by omega
    rw [hblock _ (by simp only; omega) (by simp only; omega)]
    simp only [h1]
  have hmemV : ∀ s : Fin t, b' + ((s : ℕ) : ℤ) ∈ Finset.univ.image V := by
    intro s
    obtain ⟨a, ha⟩ := hVb s
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
  have hKU : |∑ s, kc s| ≤ (mwCount l b t κ (Finset.univ.image U) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b t κ (Finset.univ.image U) kc hl.pos htl hmemU hkc ?_
    rw [map_cast_image_val_eq l _ U hU, hlink]
    exact hmU
  have hKV : |∑ s, kp s| ≤ (mwCount l b' t κ (Finset.univ.image V) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b' t κ (Finset.univ.image V) kp hl.pos htl hmemV hkp ?_
    rw [map_cast_image_val_eq l _ V hV, hlinkV]
    exact hmV
  have hfilt' : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * (∑ s, kp s) - ∑ s, kc s := by
    rw [sum_filter_block_eq k j t q U b hblock]
    refine hfilt.trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact weightExchangeBound_holds k j t q l h κ _ _ U U' (∑ s, kc s) (∑ s, kp s) hU hU' hU0 hU'h hsum hfilt'
    hKU hKV

end Formalism.CohomologicalDescent
end
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.MinorValuationBoundHolds
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

theorem lw_det_block {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (s : m) (hs : ∀ j, b j = b s → j = s) :
    (M.toSquareBlock b (b s)).det = M s s := by
  let _ : Unique {a // b a = b s} :=
    { default := ⟨s, rfl⟩
      uniq := fun j => Subtype.ext (hs j.1 j.2) }
  rw [Matrix.det_unique]
  rfl

theorem lw_det_inj {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (hM : M.BlockTriangular b) (hb : Function.Injective b) :
    M.det = ∏ i, M i i := by
  rw [Matrix.BlockTriangular.det hM, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun i _ => lw_det_block M b i (fun j hj => hb hj))
  · intro x _ y _ hxy
    exact hb hxy

end Formalism.CohomologicalDescent
end
end

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

theorem le_sum_of_dvd_det_submatrix {R : Type*} [CommRing R] [IsDomain R] (π : R) (hπ : Prime π) {t n : ℕ}
    (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (pos : Fin t → Fin n)
    (hinj : Function.Injective pos) (hpos : ∀ s j, b j = b (pos s) → j = pos s)
    (hΦ : Φ.BlockTriangular b) (al : Fin t → ℕ)
    (hdiag : ∀ s, ∃ u : Rˣ, Φ (pos s) (pos s) = (u : R) * π ^ al s) (c : ℕ)
    (hdvd : π ^ c ∣ (Φ.submatrix pos pos).det) : c ≤ ∑ s, al s := by
  have hbp : Function.Injective (b ∘ pos) := fun s s' hs => hinj (hpos s' (pos s) hs)
  have hdet := lw_det_inj (Φ.submatrix pos pos) (b ∘ pos) hΦ.submatrix hbp
  simp only [Matrix.submatrix_apply] at hdet
  choose u hu using hdiag
  rw [hdet, Finset.prod_congr rfl (fun s _ => hu s), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Units.coe_prod, Units.dvd_mul_left] at hdvd
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_unit).1 hdvd

theorem map_cast_le_of_map_neg_mul_le (l : ℕ) (hl : l.Prime) (F : Type) [Field F] [CharP F l] (a : F) (ha : a ≠ 0)
    {α β : Type} (A : Multiset α) (B : Multiset β) (f : α → ℤ) (g : β → ℤ)
    (h : Multiset.map (fun x => -a * ((f x : ℤ) : F)) A ≤
      Multiset.map (fun y => -a * ((g y : ℤ) : F)) B) :
    Multiset.map (fun x => ((f x : ℤ) : ZMod l)) A ≤ Multiset.map (fun y => ((g y : ℤ) : ZMod l)) B := by
  haveI := Fact.mk hl
  let φ : ZMod l →+* F := ZMod.castHom (dvd_refl l) F
  have hφ : Function.Injective φ := φ.injective
  have hψ : Function.Injective (fun z : ZMod l => -a * φ z) := fun z w hzw =>
    hφ (mul_left_cancel₀ (neg_ne_zero.2 ha) hzw)
  rw [← Multiset.map_le_map_iff hψ, Multiset.map_map, Multiset.map_map]
  simpa [Function.comp_def, φ, map_intCast] using h

private lemma sub_one_mul_abs_kap_le {ι : Type} [Fintype ι] (σ : Equiv.Perm ι) (l h : ℕ) (hl : 2 ≤ l)
    (w kap : ι → ℤ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ (h : ℤ))
    (hd : ∀ i, 0 ≤ (l : ℤ) * kap (σ i) + w i - kap i ∧ (l : ℤ) * kap (σ i) + w i - kap i ≤ (h : ℤ))
    (i : ι) : ((l : ℤ) - 1) * |kap i| ≤ (h : ℤ) := by
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => |kap i|)
  have hσ : σ (σ.symm i₀) = i₀ := σ.apply_symm_apply i₀
  have h1 := hd (σ.symm i₀)
  rw [hσ] at h1
  have h2 := hw (σ.symm i₀)
  have hm : |kap (σ.symm i₀)| ≤ |kap i₀| := hi₀ (σ.symm i₀)
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast hl
  have hl' : (0 : ℤ) ≤ (l : ℤ) - 1 := by linarith
  have key : (l : ℤ) * |kap i₀| ≤ |kap (σ.symm i₀)| + h := by
    rcases abs_cases (kap i₀) with ⟨e0, _⟩ | ⟨e0, _⟩ <;>
      rcases abs_cases (kap (σ.symm i₀)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rw [e0, e1] <;> nlinarith
  have h3 : ((l : ℤ) - 1) * |kap i₀| ≤ h := by nlinarith
  calc ((l : ℤ) - 1) * |kap i| ≤ ((l : ℤ) - 1) * |kap i₀| := mul_le_mul_of_nonneg_left (hi₀ i) hl'
    _ ≤ h := h3

theorem twisted_block_bounds : LemmaWAssembled := by
  intro ι _ σ l h t n F _ _ W U' bot kap c hl hW hb hd
  obtain ⟨ha, hinj, hpos, hΘ, hchar, hdiag, hΦ, hΦd, hc⟩ := hW
  have hbp : Function.Injective (W.b ∘ W.pos) := fun s s' hs => hinj (hpos s' (W.pos s) hs)
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact sub_one_mul_abs_kap_le σ l h hl.two_le (fun i => bot i + ((s : ℕ) : ℤ)) (fun i => kap i s)
      (fun i => hb i s) (fun i => hd i s) i
  · intro i
    have hdvd : ∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s))) ∣
        (W.Θ i).charpoly := by
      show _ ∣ (Matrix.charmatrix (W.Θ i)).det
      rw [(hΘ i).charmatrix.det]
      have e : ∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s))) =
          ∏ k ∈ Finset.univ.image (W.b ∘ W.pos),
            ((Matrix.charmatrix (W.Θ i)).toSquareBlock W.b k).det := by
        rw [Finset.prod_image (fun s _ s' _ hs => hbp hs)]
        refine Finset.prod_congr rfl fun s _ => ?_
        simp only [Function.comp_apply]
        rw [lw_det_block _ W.b (W.pos s) (hpos s), Matrix.charmatrix_apply_eq]
      rw [e]
      apply Finset.prod_dvd_prod_of_subset
      intro k hk
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
      obtain ⟨s, rfl⟩ := hk
      exact ⟨W.pos s, rfl⟩
    have hne : (W.Θ i).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hr := Polynomial.roots.le_of_dvd hne hdvd
    rw [hchar i] at hr
    have r1 : (∏ s, (Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s)))).roots =
        Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val := by
      rw [Finset.prod_eq_multiset_prod]
      rw [show Multiset.map (fun s => Polynomial.X - Polynomial.C (W.Θ i (W.pos s) (W.pos s)))
          Finset.univ.val = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    have r2 : (∏ u, (Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))).roots =
        Multiset.map (fun u => -W.a * ((U' i u : ℤ) : F)) Finset.univ.val := by
      rw [Finset.prod_eq_multiset_prod]
      rw [show Multiset.map (fun u => Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))
          Finset.univ.val = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun u => -W.a * ((U' i u : ℤ) : F)) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    rw [r1, r2] at hr
    have e2 : Multiset.map (fun s => W.Θ i (W.pos s) (W.pos s)) Finset.univ.val =
        Multiset.map (fun s : Fin t => -W.a * (((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ)) : F))
          Finset.univ.val := Multiset.map_congr rfl (fun s _ => hdiag i s)
    rw [e2] at hr
    exact map_cast_le_of_map_neg_mul_le l hl F W.a ha Finset.univ.val Finset.univ.val
      (fun s : Fin t => bot i + ((s : ℕ) : ℤ) - kap i s) (U' i) hr
  · intro i
    have hm := le_sum_of_dvd_det_submatrix (PowerSeries.X : PowerSeries F) PowerSeries.X_prime (W.Φ i) W.b W.pos hinj
      hpos (hΦ i) (fun s => ((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat)
      (hΦd i) (c i) (hc i)
    have hm' : ((c i : ℕ) : ℤ) ≤ ∑ s : Fin t,
        ((((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat : ℕ) : ℤ) := by
      exact_mod_cast hm
    calc (c i : ℤ) ≤ _ := hm'
      _ = ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Int.toNat_of_nonneg (hd i s).1]
        ring

theorem weightExchangeFull_holds : WEFull := by
  intro ι _ σ k j t q l h F _ _ W U U' bot cst kap c τ hl hlt hW hb hd hU hU' hUb hprod hU0 hU'h
    hsum hblock hcτ
  obtain ⟨h1, h2, h3⟩ := twisted_block_bounds ι σ l h t (k + j + t + q) F W U' bot kap c hl hW hb hd
  have hκ : ∀ i s, |kap i s| ≤ ((h / (l - 1) : ℕ) : ℤ) := by
    intro i s
    have hl2 := hl.two_le
    have hpos : (0 : ℤ) < ((l - 1 : ℕ) : ℤ) := by omega
    have e : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
    rw [Int.natCast_div, Int.le_ediv_iff_mul_le hpos, e, mul_comm]
    exact h1 i s
  exact weightExchangeChain_holds k j t q l h (h / (l - 1)) F (U τ) (U' τ) (U (σ τ)) (U' (σ τ)) (bot τ)
    (bot (σ τ)) (cst τ) (cst (σ τ)) (kap τ) (kap (σ τ)) hl hlt (hU τ) (hU' τ) (hU (σ τ))
    (hU' (σ τ)) hU0 (fun a => (hU'h a).2) hsum hblock (hUb (σ τ)) (hprod τ) (hprod (σ τ))
    (hκ τ) (hκ (σ τ)) (h2 τ) (h2 (σ τ)) (by rw [← hcτ]; exact h3 τ)

end Formalism.CohomologicalDescent

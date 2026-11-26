module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasympAll
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MultAtEqCount
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_colon_chain {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) (j : Fin N) : J ≤ q j := by

  have mono : ∀ k : ℕ, ∀ hk : k ≤ N, J ≤ F ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have e : (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
      rw [e, h0]
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have step := (hj ⟨k, hk'⟩).1
      calc J ≤ F (Fin.castSucc ⟨k, hk'⟩) := ih hk'.le
        _ ≤ F (Fin.castSucc ⟨k, hk'⟩) ⊔ Ideal.span {f ⟨k, hk'⟩} := le_sup_left
        _ = F (Fin.succ ⟨k, hk'⟩) := step.symm
  intro g hg
  exact ((hj j).2 g).2 (Ideal.mul_mem_right _ _ (mono j.val j.isLt.le hg))

theorem multAt_eq_count {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J) (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    {W' : Ideal (MRing ι)} (hW' : W' ∈ J.minimalPrimes) :
    multAt J W' = ∑ j, if q j = W' then 1 else 0 := by
  classical
  have hp : W'.IsPrime := hW'.1.1
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).1, (hj j).2.2⟩
  have hmin : ∀ j, q j ≤ W' → q j = W' := fun j h => le_antisymm h (hW'.2 ⟨(hj j).2.1, hJq j⟩ h)
  have := length_loc_chain W' N F f q hlast hj hmin
  rw [h0] at this
  unfold multAt
  rw [dite_eq_left hp, this]
  simp

theorem block_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W')
    (b : K) :
    ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| ≤
        C * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  classical
  obtain ⟨hWp, hWm, hWr⟩ := hW
  obtain ⟨i, hi⟩ := hWr b
  set s : MRing ι := X ⟨b, i⟩ with hsdef
  have hs : IsMultiHomog s (Pi.single b 1) := isMultiHomog_X' b i
  set J := W ⊔ Ideal.span {s} with hJdef
  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span hWm hs
  obtain ⟨N, F, f, c, q, h0, hlast, hj⟩ := exists_primeFiltration_of_isMultiHomogIdeal J hJ
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).2.1, (hj j).2.2.2.2⟩
  have hFm : IsMultiHomogIdeal (F 0) := h0 ▸ hJ
  choose a0 C hC hb using fun j => per_factor (L := L) hp hWm hpW hdim hs hi IH (hj j).2.2.1
    (hj j).2.2.2.1 (hJq j) (c j)
  refine ⟨1 + ∑ j, a0 j + ∑ j, tdeg (c j), ∑ j, C j, Finset.sum_nonneg fun j _ => hC j,
    fun a ha => ?_⟩
  have ha0 : ∀ j k, a0 j ≤ a k := fun j k => by
    have h1 : a0 j ≤ ∑ j, a0 j := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have := ha k
    omega
  have hca : ∀ j k, c j k ≤ a k := fun j k => by
    have h1 : c j k ≤ tdeg (c j) := Finset.single_le_sum (f := c j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    have h2 : tdeg (c j) ≤ ∑ j, tdeg (c j) := Finset.single_le_sum (f := fun j => tdeg (c j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have := ha k
    omega
  have hb1 : ∀ k, (Pi.single b 1 : K → ℕ) k ≤ a k := fun k => by
    have := ha k
    by_cases hk : k = b
    · subst hk; simp; omega
    · simp [Pi.single_apply, hk]
  have hstep := lg_step hWm hs (q := W)
    (fun g => ⟨fun h => W.mul_mem_right _ h, fun h => (hWp.mem_or_mem h).resolve_right hi⟩)
    hb1 hp.pos hpW
  have hch := lg_chain a hFm hlast (fun j => ⟨(hj j).1, (hj j).2.1, (hj j).2.2.2.2⟩) hca hp.pos
    (fun j => hJq j (Ideal.mem_sup_left hpW))
  rw [h0] at hch
  have hfin := divSupp_finite W s
  have hsum : L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial =
      ∑ j, (if q j ∈ divSupp W s then appr L m (q j) a else 0) := by
    rw [hR4W _ b i hi (by funext k'; simp [uv, Pi.single_apply]), Fin.init_snoc,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hcount : ∀ W' ∈ hfin.toFinset, multAt J W' = ∑ j, if q j = W' then 1 else 0 :=
      fun W' hW' => multAt_eq_count h0 hlast (fun j => ⟨(hj j).2.1, (hj j).2.2.1, (hj j).2.2.2.2⟩)
        ((Set.Finite.mem_toFinset hfin).mp hW').1
    rw [Finset.sum_congr rfl fun W' hW' => by rw [hcount W' hW']]
    push_cast
    simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Set.Finite.mem_toFinset, appr]
    split_ifs <;> simp
  rw [hsum, hstep, hch, add_sub_cancel_right, ← Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb j a fun k => ha0 j k)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem main_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (hSW : SymmAt (m + 1) W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W') :
    HAsymp L (m + 1) W := by
  have hblock (b : K) := block_step (L := L) hp hW hpW hdim hR4W IH b
  choose a0 C hC hb using hblock
  set a₁ := 1 + ∑ b, a0 b
  set Δ : (K → ℕ) → ℝ := fun a => lg W a - appr L (m + 1) W a with hΔ
  set B := coefB (m + 1) W
  have hB : 0 ≤ B := coefB_nonneg _ _
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  set Kst := ∑ b, C b + |L| * B * 2 ^ (m - 1) / m.factorial
  have hKst : 0 ≤ Kst := by
    have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => hC b
    positivity
  have hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
    intro a b ha hab
    have ha0 : ∀ k, a0 b ≤ a k := fun k => by
      have h1 : a0 b ≤ ∑ b, a0 b := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
      have := ha k
      omega
    have h1 := hb b a ha0
    set x : K → ℤ := fun k => (a k : ℤ)
    have hx : (fun _ : Fin (m + 1) => fun k => ((a - (Pi.single b 1 : K → ℕ)) k : ℤ)) =
        fun _ => x - uv b := by
      funext _ k
      by_cases hk : k = b
      · subst hk
        have : 1 ≤ a k := by omega
        simp [x, uv, Nat.cast_sub this]
      · simp [x, uv, Pi.single_apply, hk]
    have h2 := geoNum_diff_est m W hSW x b
    rw [show nrm x = tdeg a from nrm_natCast a] at h2
    have hfs : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hid : Δ a - Δ (a - Pi.single b 1) =
        (lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial) -
        L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))) := by
      simp only [hΔ, appr]
      rw [hx, hfs]
      field_simp
      ring
    have h3 : |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| ≤
        |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m + 1).factorial : ℝ)), hfs]
      have hN : (0 : ℝ) ≤ tdeg a := by positivity
      have h4 : ((tdeg a : ℝ) + 2) ^ (m + 1 - 2) ≤ 2 ^ (m - 1) * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
        rw [show m + 1 - 2 = m - 1 by omega, ← mul_pow]
        gcongr
        linarith
      calc |L| / ((m + 1) * m.factorial) * |(geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))|
          ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * ((tdeg a : ℝ) + 2) ^ (m + 1 - 2))) := by
            gcongr
        _ ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * (2 ^ (m - 1) *
              ((tdeg a : ℝ) + 1) ^ (m - 1)))) := by
            gcongr
        _ = |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
            field_simp
    have hCb : C b ≤ ∑ b, C b := Finset.single_le_sum (f := C) (fun b _ => hC b) (Finset.mem_univ b)
    rw [hid]
    calc _ ≤ |lg W a - lg W (a - Pi.single b 1) -
            L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| +
          |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| := abs_sub _ _
      _ ≤ C b * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := add_le_add h1 h3
      _ ≤ (∑ b, C b) * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by gcongr
      _ = Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by ring
  have hw := walk_bound Δ a₁ m hKst hstep
  refine ⟨a₁, |Δ (fun _ => a₁)| + Kst * m, by positivity, fun a ha => ?_⟩
  have h := hw a ha
  have hN : (0 : ℝ) ≤ tdeg a := by positivity
  have hp1 : (1 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ m := one_le_pow₀ (by linarith)
  have hkey : Kst * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have : ((tdeg a : ℝ) + 1) ^ m = ((tdeg a : ℝ) + 1) ^ (m - 1) * ((tdeg a : ℝ) + 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [this]
      have : (0 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ (m - 1) := by positivity
      have : (0 : ℝ) ≤ Kst * m := by positivity
      nlinarith
  simp only [Nat.add_sub_cancel]
  push_cast
  have hΔc := abs_nonneg (Δ (fun _ => a₁))
  have hKm : (0 : ℝ) ≤ Kst * m := by positivity
  change |Δ a| ≤ _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hA : (1 : ℝ) ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by nlinarith
  have hB1 : |Δ (fun _ => a₁)| ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) :=
    le_mul_of_one_le_right hΔc hA
  have hB2 : Kst * m * ((tdeg a : ℝ) + 1) ^ m ≤
      Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by
    have : ((tdeg a : ℝ) + 1) ^ m ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left this hKm
  calc |Δ a| ≤ |Δ (fun _ => a₁)| + Kst * m * ((tdeg a : ℝ) + 1) ^ m := by linarith
    _ ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) +
        Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by linarith
    _ = (|Δ (fun _ => a₁)| + Kst * m) * ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by ring

theorem hasymp_all {L : ℝ} {p : ℕ} (hp : p.Prime)
    (hR4 : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K) (i : ι k),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
      (X ⟨k, i⟩ : MRing ι) ∉ V →
      (a (Fin.last n) = fun k' => if k' = k then 1 else 0) →
      geoNum (n + 1) V a = ∑ᶠ W' ∈ divSupp V (X ⟨k, i⟩),
        (multAt (V ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum n W' (Fin.init a))
    (hSymm : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
      geoNum n V (a ∘ σ) = geoNum n V a)
    (hbase : ∀ W : Ideal (MRing ι), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) → HAsymp L 0 W) :
    ∀ (d : ℕ) (W : Ideal (MRing ι)), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L d W ∧ SymmAt d W := by
  intro d
  induction d with
  | zero =>
    intro W hW hpW hdim
    exact ⟨hbase W hW hpW hdim,
      fun a σ => hSymm 0 W a σ hW (charOf_ne_zero_of_mem hp.ne_zero hpW) hdim⟩
  | succ m ih =>
    intro W hW hpW hdim
    have hc := charOf_ne_zero_of_mem hp.ne_zero hpW
    have hS : SymmAt (m + 1) W := fun a σ => hSymm (m + 1) W a σ hW hc hdim
    exact ⟨main_step hp hW hpW hdim (fun a k i hX ha => hR4 m W a k i hW hc hdim hX ha) hS
      (fun W' hW' hpW' hdim' => ih W' hW' hpW' hdim'), hS⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def killB (T : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval (fun p => if p.1 ∈ T then 0 else X p)

theorem killB_X (T : Finset K) (p : Σ k, ι k) :
    killB T (X p : MRing ι) = if p.1 ∈ T then 0 else X p := by
  unfold killB
  rw [MvPolynomial.aeval_X]

open Classical in
theorem killB_monomial (T : Finset K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    killB T (monomial m c : MRing ι) = if (∃ p, p.1 ∈ T ∧ m p ≠ 0) then 0 else monomial m c := by
  unfold killB
  rw [MvPolynomial.aeval_monomial]
  split_ifs with h
  · obtain ⟨p, hpT, hp⟩ := h
    apply mul_eq_zero_of_right
    rw [Finsupp.prod]
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
    simp [hpT, hp]
  · push_neg at h
    rw [Finsupp.prod]
    have hc : ∀ p ∈ m.support, (if p.1 ∈ T then (0 : MRing ι) else X p) ^ m p = X p ^ m p := by
      intro p hp
      rw [if_neg]
      intro hT
      exact (Finsupp.mem_support_iff.mp hp) (h p hT)
    rw [Finset.prod_congr rfl hc, ← Finsupp.prod, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]

theorem killB_multiHomog (T : Finset K) {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) :
    killB T s = 0 ∨ killB T s = s := by
  classical
  by_cases hT : ∃ k ∈ T, c k ≠ 0
  · left
    obtain ⟨k, hkT, hck⟩ := hT
    set_option synthInstance.maxHeartbeats 100000 in
      rw [s.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    have h := hs m hm k
    rw [← h] at hck
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hck
    rw [killB_monomial, if_pos ⟨⟨k, i⟩, hkT, hi⟩]
  · right
    push_neg at hT
    have key : ∀ m ∈ s.support, killB T (monomial m (AddMonoidAlgebra.coeff s m)) = monomial m (AddMonoidAlgebra.coeff s m) := by
      intro m hm
      rw [killB_monomial, if_neg]
      rintro ⟨p, hpT, hp⟩
      have h := hs m hm p.1
      rw [hT p.1 hpT] at h
      exact hp ((Finset.sum_eq_zero_iff.mp h) p.2 (Finset.mem_univ _))
    calc killB T s = killB T (∑ m ∈ s.support, monomial m (AddMonoidAlgebra.coeff s m)) := by rw [← s.as_sum]
      _ = ∑ m ∈ s.support, killB T (monomial m (AddMonoidAlgebra.coeff s m)) := map_sum _ _ _
      _ = ∑ m ∈ s.support, monomial m (AddMonoidAlgebra.coeff s m) := Finset.sum_congr rfl key
      _ = s := s.as_sum.symm

theorem le_comap_killB {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (T : Finset K) :
    P ≤ P.comap (killB T) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killB_multiHomog T ha with h | h
  · rw [h]; exact Ideal.zero_mem _
  · rw [h]; exact Ideal.subset_span hf

theorem killB_comp {T T' : Finset K} (h : T ⊆ T') :
    (killB T' : MRing ι →ₐ[ℤ] MRing ι).comp (killB T) = killB T' := by
  apply MvPolynomial.algHom_ext
  intro p
  rw [AlgHom.comp_apply, killB_X]
  split_ifs with hp
  · rw [map_zero, killB_X, if_pos (h hp)]
  · rfl

theorem comap_killB_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {T T' : Finset K}
    (h : T ⊆ T') : P.comap (killB T) ≤ P.comap (killB T') := by
  intro x hx
  rw [Ideal.mem_comap] at hx ⊢
  rw [← killB_comp h, AlgHom.comp_apply]
  exact Ideal.mem_comap.mp (le_comap_killB hP T' hx)

theorem card_le_dim {P : Ideal (MRing ι)} (hPp : P.IsPrime) (hPm : IsMultiHomogIdeal P)
    (hrel : IsRelevant P) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ P) := by
  classical
  haveI := hPp
  let T : ℕ → Finset K := fun j => Finset.univ.filter fun k => ((Fintype.equivFin K k : ℕ) < j)
  let Q : ℕ → Ideal (MRing ι) := fun j => P.comap (killB (T j))
  have hQp : ∀ j, (Q j).IsPrime := fun j => Ideal.comap_isPrime _ _
  have hPQ : ∀ j, P ≤ Q j := fun j => le_comap_killB hPm (T j)
  have hT : ∀ j, T j ⊆ T (j + 1) := by
    intro j k hk
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  have hlt : ∀ j < Fintype.card K, Q j < Q (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (comap_killB_mono hPm (hT j)) ?_
    intro heq
    set k := (Fintype.equivFin K).symm ⟨j, hj⟩ with hk
    have hkv : ((Fintype.equivFin K k : Fin _) : ℕ) = j := by simp [hk]
    obtain ⟨i, hi⟩ := hrel k
    have hin : k ∈ T (j + 1) := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hout : k ∉ T j := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h1 : (X ⟨k, i⟩ : MRing ι) ∈ Q (j + 1) := by
      rw [Ideal.mem_comap, killB_X, if_pos hin]
      exact P.zero_mem
    have h2 : (X ⟨k, i⟩ : MRing ι) ∉ Q j := by
      rw [Ideal.mem_comap, killB_X, if_neg hout]
      exact hi
    exact h2 (heq ▸ h1)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (P : Set (MRing ι)) :=
    fun j => ⟨⟨Q j, hQp j⟩, fun x hx => hPQ j hx⟩
  let s : LTSeries (PrimeSpectrum.zeroLocus (P : Set (MRing ι))) :=
    ⟨Fintype.card K, f, fun j => by
      first
      | exact Subtype.mk_lt_mk.mpr (PrimeSpectrum.asIdeal_lt_asIdeal.mp (hlt j j.isLt))
      | exact (hlt j j.isLt)⟩
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim s

theorem not_relevant_of_dim_zero {W : Ideal (MRing ι)} [W.IsPrime] (hWm : IsMultiHomogIdeal W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) (hsW : s ∉ W) {W' : Ideal (MRing ι)}
    (hW' : W' ∈ (W ⊔ Ideal.span {s}).minimalPrimes) : ¬ IsRelevant W' := by
  classical
  intro hrel
  have hW'p : W'.IsPrime := hW'.1.1
  have hJ : IsMultiHomogIdeal (W ⊔ Ideal.span {s}) := isMultiHomogIdeal_sup_span hWm hs
  have hW'm : IsMultiHomogIdeal W' := by
    let e := Fintype.equivFin K
    letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := lexDecEq (Fintype.card K)
    letI : GradedAlgebra (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
      MvPolynomial.weightedGradedAlgebra ℤ (lexW (ι := ι) e)
    rw [← isHomogeneous_lex_iff e] at hJ ⊢
    have hcore := hW'p.homogeneousCore (𝒜 := weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))
    have hle : W ⊔ Ideal.span {s} ≤
        (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).toIdeal := by
      rw [← hJ.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hW'.1.2
    have hge := hW'.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    have heq : (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).toIdeal = W' :=
      le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) hge
    rw [← heq]
    exact (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).isHomogeneous
  have h1 := card_le_dim hW'p hW'm hrel
  have hWW' : W ≤ W' := le_trans le_sup_left hW'.1.2
  have hsW' : s ∈ W' :=
    hW'.1.2 ((le_sup_right : Ideal.span {s} ≤ W ⊔ Ideal.span {s}) (Ideal.mem_span_singleton_self s))
  let g : MRing ι ⧸ W →+* MRing ι ⧸ W' := Ideal.Quotient.factor hWW'
  have hg : ∀ a ∈ Ideal.span {Ideal.Quotient.mk W s}, g a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : g (Ideal.Quotient.mk W s) = 0 := by
      simp only [g, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hsW'
    rw [this, mul_zero]
  let f : (MRing ι ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W s} →+* MRing ι ⧸ W' :=
    Ideal.Quotient.lift _ g hg
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk W x), rfl⟩
  have hnz : Ideal.Quotient.mk W s ∈ nonZeroDivisors (MRing ι ⧸ W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    exact hsW (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have h2 : ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (MRing ι ⧸ W') + 1 := by
          gcongr
      _ ≤ ringKrullDim ((MRing ι ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W s}) + 1 := by
          gcongr
          exact ringKrullDim_le_of_surjective f hf
      _ ≤ ringKrullDim (MRing ι ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      _ = _ := hd
  rw [zero_add] at h2
  have h3 : (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h2
  have h4 := WithBot.coe_le_coe.mp h3
  have h5 : ((Fintype.card K + 1 : ℕ) : ℕ∞) ≤ ((Fintype.card K : ℕ) : ℕ∞) := h4
  exact absurd (Nat.cast_le.mp h5) (by omega)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

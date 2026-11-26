module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori.UpInv

variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]

def low (wt : ι → ℕ) (P : ι → Module.End L V) (m : ℕ) : Submodule L V where
  carrier := {x | ∀ i, m ≤ wt i → P i x = 0}
  add_mem' {x y} hx hy i hi := by rw [map_add (f := _), hx i hi, hy i hi, add_zero]
  zero_mem' i _ := map_zero _
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi, smul_zero]

theorem sum_pieces {P : ι → Module.End L V} (hP : IsPieces P) (x : V) :
    ∑ j, P j x = x := by
  have h := congrArg (fun T : Module.End L V => T x) hP.sum
  simpa [LinearMap.sum_apply] using h

theorem map_low_le {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P)
    {a : Module.End L V} (ha : IsUpper wt P a) (m : ℕ) :
    (low wt P m).map a ≤ low wt P m := by
  rintro _ ⟨x, hx, rfl⟩ i hi
  have hx' : x ∈ low wt P m := hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_pieces hP x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : m ≤ wt j
  · rw [hx' j hj, map_zero, map_zero]
  · have h := congrArg (fun T : Module.End L V => T x) (ha i j (by omega))
    simpa using h

theorem map_low_eq [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) (m : ℕ) : (low wt P m).map a = low wt P m := by
  let e : V ≃ₗ[L] V := LinearEquiv.ofLinear a a' h1 h2
  exact Submodule.eq_of_le_of_finrank_eq (map_low_le hP ha m)
    (LinearEquiv.finrank_map_eq e (low wt P m))

theorem inv_mem_low [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) {m : ℕ} {x : V} (hx : x ∈ low wt P m) : a' x ∈ low wt P m := by
  rw [← map_low_eq hP h1 h2 ha m] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h := congrArg (fun T : Module.End L V => T y) h2
  have h' : a' (a y) = y := by simpa using h
  rwa [h']

theorem piece_mem_low {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P) (j : ι) (x : V) :
    P j x ∈ low wt P (wt j + 1) := by
  intro i hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  have h := congrArg (fun T : Module.End L V => T x) (hP.orth i j hij)
  simpa using h

theorem isUpper_inv : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V),
    GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 →
      GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  intro L V ι _ _ _ _ _ wt P hP a a' h1 h2 ha i j hij
  refine LinearMap.ext fun x => ?_
  have h := inv_mem_low hP h1 h2 ha (piece_mem_low (wt := wt) hP j x) i (by omega)
  simpa using h

end GlobalTheory.CompanionTheory.Iwahori.UpInv

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpperStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upper_triangular_inverse_is_upper : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | exact GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | (intros; apply GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Gauss

open GlobalTheory.CompanionTheory.Iwahori

variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}

theorem eq_zero_of_mul_pieces (hP : IsPieces P) {y : E} (h : ∀ j, y * P j = 0) : y = 0 := by
  have : y * ∑ j, P j = 0 := by
    rw [Finset.mul_sum]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, mul_one] at this

theorem eq_zero_of_pieces_mul (hP : IsPieces P) {y : E} (h : ∀ j, P j * y = 0) : y = 0 := by
  have : (∑ j, P j) * y = 0 := by
    rw [Finset.sum_mul]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, one_mul] at this

theorem block_mul (hP : IsPieces P) (u x y v : E) :
    u * (x * y) * v = ∑ l, (u * x * P l) * (P l * y * v) := by
  have h : ∀ l, (u * x * P l) * (P l * y * v) = u * x * (P l) * y * v := by
    intro l
    calc (u * x * P l) * (P l * y * v) = u * x * (P l * P l) * y * v := by
          simp only [mul_assoc]
      _ = _ := by rw [hP.idem]
  simp_rw [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hP.sum]
  simp only [mul_one, mul_assoc]

theorem isUpper_mul (hP : IsPieces P) {a b : E} (ha : IsUpper wt P a) (hb : IsUpper wt P b) :
    IsUpper wt P (a * b) := by
  intro i j hij
  rw [block_mul hP]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (wt l) (wt i) with h | h
  · rw [ha i l h, zero_mul]
  · rw [hb l j (lt_of_lt_of_le hij h), mul_zero]

theorem isLowerUni_mul (hwt : Function.Injective wt) (hP : IsPieces P) {a b : E}
    (ha : IsLowerUni wt P a) (hb : IsLowerUni wt P b) : IsLowerUni wt P (a * b) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [block_mul hP]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge (wt i) (wt l) with h | h
    · rw [ha.1 i l h, zero_mul]
    · rw [hb.1 l j (lt_of_le_of_lt h hij), mul_zero]
  · rw [block_mul hP, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, hP.idem]
    · intro l _ hl
      rcases lt_trichotomy (wt i) (wt l) with h | h | h
      · rw [ha.1 i l h, zero_mul]
      · exact absurd (hwt h).symm hl
      · rw [hb.1 l i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem isUpper_one (hP : IsPieces P) : IsUpper wt P 1 := fun i j h => by
  rw [mul_one]
  exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)

theorem isLowerUni_one (hP : IsPieces P) : IsLowerUni wt P 1 := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_one]
    exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)
  · rw [mul_one, hP.idem]

theorem sub_one_mul_mem {J : AddSubgroup E} (hJ : IsCongIdeal J P) {a b : E}
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) : a * b - 1 ∈ J := by
  have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  rw [this]
  exact J.add_mem (J.add_mem (hJ.mul_mem _ ha _ hb) ha) hb

theorem step (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ)
    (ih : ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b)
    (q : ι) (hq : wt q = m) (x : E) (hx : x ∈ J)
    (hH : ∀ i j, (m + 1 ≤ wt i ∨ m + 1 ≤ wt j) → P i * x * P j = 0) :
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ 1 + x = a * b := by
  have hl : ∀ i, m + 1 ≤ wt i → P i * x = 0 := fun i hi =>
    eq_zero_of_mul_pieces hP fun j => hH i j (Or.inl hi)
  have hr : ∀ j, m + 1 ≤ wt j → x * P j = 0 := fun j hj =>
    eq_zero_of_pieces_mul hP fun i => by rw [← mul_assoc]; exact hH i j (Or.inr hj)
  have hne : ∀ j, m + 1 ≤ wt j → P q * P j = 0 := fun j hj =>
    hP.orth q j (fun e => by subst e; omega)
  have hne' : ∀ j, m + 1 ≤ wt j → P j * P q = 0 := fun j hj =>
    hP.orth j q (fun e => by subst e; omega)
  have hQQ := hP.idem q
  obtain ⟨y, hy, h1, h2⟩ := hJ.inv (x * P q) (hJ.right_mem q x hx)
  obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ J, 1 + z = (1 + y) * (1 + x) :=
    ⟨(1 + y) * (1 + x) - 1,
      sub_one_mul_mem hJ (by rwa [add_sub_cancel_left]) (by rwa [add_sub_cancel_left]),
      by abel⟩
  have hAB : 1 + x = (1 + x * P q) * (1 + z) := by
    rw [hzdef, ← mul_assoc, h1, one_mul]
  have hzQ : z * P q = 0 := by
    have e : (1 + x) * P q = (1 + x * P q) * P q := by
      simp only [add_mul, one_mul, mul_assoc, hQQ]
    have : (1 + z) * P q = P q := by
      calc (1 + z) * P q = (1 + y) * ((1 + x) * P q) := by rw [hzdef, mul_assoc]
        _ = (1 + y) * ((1 + x * P q) * P q) := by rw [e]
        _ = ((1 + y) * (1 + x * P q)) * P q := by rw [mul_assoc]
        _ = P q := by rw [h2, one_mul]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzr : ∀ j, m + 1 ≤ wt j → z * P j = 0 := by
    intro j hj
    have e1 : (1 + x) * P j = P j := by rw [add_mul, one_mul, hr j hj, add_zero]
    have e2 : (1 + x * P q) * P j = P j := by
      rw [add_mul, one_mul, mul_assoc, hne j hj, mul_zero, add_zero]
    have e3 : (1 + y) * P j = P j := by
      calc (1 + y) * P j = (1 + y) * ((1 + x * P q) * P j) := by rw [e2]
        _ = ((1 + y) * (1 + x * P q)) * P j := by rw [mul_assoc]
        _ = P j := by rw [h2, one_mul]
    have : (1 + z) * P j = P j := by
      rw [hzdef, mul_assoc, e1, e3]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzl : ∀ i, m + 1 ≤ wt i → P i * z = 0 := by
    intro i hi
    have e1 : P i * (1 + x) = P i := by rw [mul_add, mul_one, hl i hi, add_zero]
    have e2 : P i * (1 + x * P q) = P i := by
      rw [mul_add, mul_one, ← mul_assoc, hl i hi, zero_mul, add_zero]
    have e3 : P i * (1 + y) = P i := by
      calc P i * (1 + y) = (P i * (1 + x * P q)) * (1 + y) := by rw [e2]
        _ = P i * ((1 + x * P q) * (1 + y)) := by rw [mul_assoc]
        _ = P i := by rw [h1, mul_one]
    have : P i * (1 + z) = P i := by
      rw [hzdef, ← mul_assoc, e3, e1]
    rw [mul_add, mul_one] at this
    simpa using this
  have hsJ : z - P q * z ∈ J := J.sub_mem hz (hJ.left_mem q z hz)
  have hsr : ∀ j, m ≤ wt j → (z - P q * z) * P j = 0 := by
    intro j hj
    rcases hj.eq_or_lt with h | h
    · have : j = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [sub_mul, hzQ, mul_assoc, hzQ, mul_zero, sub_zero]
    · rw [sub_mul, hzr j h, mul_assoc, hzr j h, mul_zero, sub_zero]
  have hsl : ∀ i, m ≤ wt i → P i * (z - P q * z) = 0 := by
    intro i hi
    rcases hi.eq_or_lt with h | h
    · have : i = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [mul_sub, ← mul_assoc, hQQ, sub_self]
    · rw [mul_sub, hzl i h, ← mul_assoc, hne' i h, zero_mul, sub_zero]
  have hS : ∀ i j, (m ≤ wt i ∨ m ≤ wt j) →
      P i * ((1 + (z - P q * z)) - 1) * P j = 0 := by
    intro i j hij
    rw [add_sub_cancel_left]
    rcases hij with h | h
    · rw [hsl i h, zero_mul]
    · rw [mul_assoc, hsr j h, mul_zero]
  obtain ⟨a', b', ha, hb, hau, hbl, hk⟩ :=
    ih (1 + (z - P q * z)) (by rwa [add_sub_cancel_left]) hS
  have hSC : (1 + (z - P q * z)) * (1 + P q * z) = 1 + z := by
    have : (1 + (z - P q * z)) * (1 + P q * z)
        = 1 + z + (z * P q) * z - P q * (z * P q) * z := by noncomm_ring
    rw [this, hzQ]
    simp
  have hA : IsUpper wt P (1 + x * P q) := by
    intro i j hij
    have hm : P i * (1 + x * P q) * P j = P i * P j + P i * x * (P q * P j) := by
      simp only [mul_add, add_mul, mul_one, mul_assoc]
    rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
    by_cases hjq : j = q
    · subst hjq
      rw [hl i (by omega), zero_mul]
    · rw [hP.orth q j (Ne.symm hjq), mul_zero]
  have hC : IsLowerUni wt P (1 + P q * z) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hm : P i * (1 + P q * z) * P j = P i * P j + (P i * P q) * (z * P j) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
      by_cases hiq : i = q
      · subst hiq
        rw [hzr j (by omega), mul_zero]
      · rw [hP.orth i q hiq, zero_mul]
    · have hm : P i * (1 + P q * z) * P i = P i * P i + (P i * P q) * (z * P i) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.idem]
      by_cases hiq : i = q
      · subst hiq
        rw [hzQ, mul_zero, add_zero]
      · rw [hP.orth i q hiq, zero_mul, add_zero]
  refine ⟨(1 + x * P q) * a', b' * (1 + P q * z), ?_, ?_, isUpper_mul hP hA hau,
    isLowerUni_mul hwt hP hbl hC, ?_⟩
  · exact sub_one_mul_mem hJ (by rw [add_sub_cancel_left]; exact hJ.right_mem q x hx) ha
  · exact sub_one_mul_mem hJ hb (by rw [add_sub_cancel_left]; exact hJ.left_mem q z hz)
  · rw [hAB, ← hSC, hk]
    simp only [mul_assoc]

theorem exists_of_support (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ) :
    ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b := by
  induction m with
  | zero =>
    intro k _ h
    have h0 : k - 1 = 0 := eq_zero_of_mul_pieces hP fun j => eq_zero_of_pieces_mul hP fun i => by
      rw [← mul_assoc]; exact h i j (Or.inl (Nat.zero_le _))
    have hk : k = 1 := sub_eq_zero.mp h0
    exact ⟨1, 1, by simp, by simp, isUpper_one hP, isLowerUni_one hP, by simp [hk]⟩
  | succ m ih =>
    intro k hk h
    by_cases hq : ∃ q, wt q = m
    · obtain ⟨q, hq⟩ := hq
      have := step hwt hP hJ m ih q hq (k - 1) hk h
      simpa using this
    · have hq' : ∀ i, m ≤ wt i → m + 1 ≤ wt i := fun i hi => by
        rcases hi.eq_or_lt with e | e
        · exact absurd ⟨i, e.symm⟩ hq
        · exact e
      refine ih k hk fun i j hij => h i j ?_
      rcases hij with e | e
      · exact Or.inl (hq' i e)
      · exact Or.inr (hq' j e)

theorem block_gauss : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt →
    ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E,
    GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J →
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧
      GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  intro E ι _ _ wt hwt P hP J hJ k hk
  refine exists_of_support hwt hP hJ (Finset.univ.sup wt + 1) k hk ?_
  intro i j h
  have h1 := Finset.le_sup (f := wt) (Finset.mem_univ i)
  have h2 := Finset.le_sup (f := wt) (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.Iwahori.Gauss
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorizationStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_upper_lower_factorization : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt → ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J → ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧ GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss | exact GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss | (intros; apply GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit

variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]

theorem norm_one_add_of_lt {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by
  have hne : ‖(1 : L)‖ ≠ ‖t‖ := by rw [norm_one]; exact ht.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
  exact max_eq_left ht.le

theorem exists_coord {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hx : x ≠ 0) :
    ∃ i, (∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖) ∧ b.repr x i ≠ 0 ∧
      ‖b.repr ((1 + g) x) i‖ = ‖b.repr x i‖ := by
  have hne : ∃ j, b.repr x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have : b.repr x = 0 := by
      ext j
      simpa using hcon j
    simpa using this
  obtain ⟨j₀, hj₀⟩ := hne
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr x j‖)
    ⟨j₀, Finset.mem_univ _⟩
  have hmax : ∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖ := fun j => hi j (Finset.mem_univ _)
  have hc : b.repr x i ≠ 0 := by
    intro h0
    have := hmax j₀
    rw [h0, norm_zero] at this
    exact hj₀ (norm_le_zero_iff.mp this)
  refine ⟨i, hmax, hc, ?_⟩
  set c := b.repr x i with hcdef
  have hy : c⁻¹ • x ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hmax j) (norm_nonneg _)
  obtain ⟨z, hz, hgz⟩ := hg _ hy
  have hzi : ‖b.repr z i‖ ≤ 1 := (hb z).1 hz i
  have hval : g x = c • π • z := by
    have h1 : g (c⁻¹ • x) = c⁻¹ • g x := map_smul g _ _
    rw [h1] at hgz
    rw [← hgz, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hGx : b.repr ((1 + g) x) i = c * (1 + π * b.repr z i) := by
    have : (1 + g) x = x + c • π • z := by
      rw [LinearMap.add_apply, Module.End.one_apply, hval]
    rw [this, map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← hcdef]
    ring
  have ht : ‖π * b.repr z i‖ < 1 := by
    rw [norm_mul]
    calc ‖π‖ * ‖b.repr z i‖ ≤ ‖π‖ * 1 := by gcongr
      _ < 1 := by simpa using hπ
  rw [hGx, norm_mul, norm_one_add_of_lt ht, mul_one]

theorem eq_zero_of_apply {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (h0 : (1 + g) x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨i, -, hc, hn⟩ := exists_coord b hb hπ hg hx
  rw [h0, map_zero, Finsupp.zero_apply, norm_zero] at hn
  exact hc (norm_eq_zero.mp hn.symm)

theorem mem_of_apply_mem {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hG : (1 + g) x ∈ Λ) : x ∈ Λ := by
  by_cases hx : x = 0
  · rw [hx]; exact Λ.zero_mem
  obtain ⟨i, hmax, -, hn⟩ := exists_coord b hb hπ hg hx
  rw [hb]
  intro j
  exact (hmax j).trans (hn ▸ (hb _).1 hG i)

theorem main : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 →
    ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π,
      (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  intro L V _ _ _ _ _ Λ hΛ π hπ g hg
  obtain ⟨m, b, hb⟩ := hΛ
  have hker : LinearMap.ker (1 + g) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_apply b hb hπ hg hx
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_ker_eq_bot (1 + g)).2 hker
  have hGH : (1 + g) * (↑u⁻¹ : Module.End L V) = 1 := by rw [← hu]; exact u.mul_inv
  have hHG : (↑u⁻¹ : Module.End L V) * (1 + g) = 1 := by rw [← hu]; exact u.inv_mul
  set H : Module.End L V := ↑u⁻¹ with hH
  have hGHx : ∀ x, (1 + g) (H x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hGH
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHGx : ∀ x, H ((1 + g) x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hHG
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHmem : ∀ x ∈ Λ, H x ∈ Λ := fun x hx =>
    mem_of_apply_mem b hb hπ hg (by rw [hGHx]; exact hx)
  refine ⟨H - 1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hgy⟩ := hg x hx
    refine ⟨-H y, Λ.neg_mem (hHmem y hy), ?_⟩
    have h1 : H x + H (g x) = x := by
      have := hHGx x
      rwa [LinearMap.add_apply, Module.End.one_apply, map_add] at this
    have h2 : (H - 1) x = H x - x := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [h2, smul_neg, ← map_smul, ← hgy]
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, h1, sub_self]
  · rw [add_sub_cancel]; exact hGH
  · rw [add_sub_cancel]; exact hHG

end GlobalTheory.CompanionTheory.Iwahori.CongUnit
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExistsStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_endomorphism_inverse_exists : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 → ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.CongUnit.main | exact GlobalTheory.CompanionTheory.Iwahori.CongUnit.main | (intros; apply GlobalTheory.CompanionTheory.Iwahori.CongUnit.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem hLin_apply (hh : IsHerm s h) (x y : V) : hLin hh x y = h x y := rfl

theorem h_sub_right (hh : IsHerm s h) (x y z : V) : h x (y - z) = h x y - h x z :=
  map_sub (hLin hh x) y z

theorem h_zero_right (hh : IsHerm s h) (x : V) : h x 0 = 0 := map_zero (hLin hh x)

theorem eq_of_pair (hh : IsHerm s h) {z z' : V} (H : ∀ x, h x z = h x z') : z = z' := by
  have : z - z' = 0 := by
    apply hh.2.2.2
    intro y
    rw [hh.2.2.1 y (z - z'), h_sub_right hh, H, sub_self, map_zero]
  exact sub_eq_zero.1 this

theorem s_ne (hδ : δ ≠ 0) : s δ ≠ 0 := by
  simpa using (map_ne_zero s).2 hδ

theorem projE_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projE hh δ e f i x = ((s δ)⁻¹ * h (f i) x) • e i := by
  simp [projE, hLin_apply, mul_smul]

theorem projF_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projF hh δ e f i x = (δ⁻¹ * h (e i) x) • f i := by
  simp [projF, hLin_apply, mul_smul]

theorem h_f_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if j = i then s δ else 0 := by
  rw [hh.2.2.1 (e j) (f i), hF.2.2.1 j i]
  split_ifs <;> simp

theorem projE_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (e j) = if j = i then e i else 0 := by
  rw [projE_apply, h_f_e hh hF]
  split_ifs
  · simp [s_ne hδ]
  · simp

theorem projE_f (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (f j) = 0 := by
  rw [projE_apply, hF.2.1]; simp

theorem projE_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projE hh δ e f i w = 0 := by
  rw [projE_apply, (hF.2.2.2.1 w hw i).2]; simp

theorem projF_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (e j) = 0 := by
  rw [projF_apply, hF.1]; simp

theorem projF_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (f j) = if j = i then f i else 0 := by
  rw [projF_apply, hF.2.2.1 i j]
  by_cases hij : j = i
  · subst hij; simp [hδ]
  · simp [hij, Ne.symm hij]

theorem projF_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projF hh δ e f i w = 0 := by
  rw [projF_apply, (hF.2.2.2.1 w hw i).1]; simp

theorem piece_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (e j) = if i = some (Sum.inl j) then e j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_e hh hδ hF, projF_e hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projE_e hh hδ hF]
    · simp [piece, projE_e hh hδ hF, hij, Ne.symm hij]
  · simp [piece, projF_e hh hF]

theorem piece_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (f j) = if i = some (Sum.inr j) then f j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_f hh hF, projF_f hh hδ hF]
  · simp [piece, projE_f hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projF_f hh hδ hF]
    · simp [piece, projF_f hh hδ hF, hij, Ne.symm hij]

theorem piece_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Idx l) {w : V} (hw : w ∈ W) :
    piece hh δ e f i w = if i = none then w else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_w hh hF _ hw, projF_w hh hF _ hw]
  · simp [piece, projE_w hh hF _ hw]
  · simp [piece, projF_w hh hF _ hw]

theorem end_ext (hF : IsFrame h δ e f W) {A B : Module.End L V} (he : ∀ i, A (e i) = B (e i))
    (hf : ∀ i, A (f i) = B (f i)) (hw : ∀ w ∈ W, A w = B w) : A = B := by
  ext x
  obtain ⟨a, b, w, hwW, rfl⟩ := hF.2.2.2.2.2 x
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_add (f := _), map_sum, he, hf, hw w hwW]

theorem isPieces_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) :
    IsPieces (piece hh δ e f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_w hh hF _ hw]
  · intro i
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw]
      split_ifs with h1 <;> simp_all [piece_w hh hF _ hw]
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp [LinearMap.sum_apply, piece_e hh hδ hF]
    · simp [LinearMap.sum_apply, piece_f hh hδ hF]
    · simp [LinearMap.sum_apply, piece_w hh hF _ hw]

theorem lat_smul {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {c : L} (hc : ‖c‖ ≤ 1) {x : V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hx i)

theorem e_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    e j ∈ Λ := by
  have := (hA (Pi.single j 1) 0 0 W.zero_mem).2 ⟨fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], fun i => by simp, by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

theorem f_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    f j ∈ Λ := by
  have := (hA 0 (Pi.single j 1) 0 W.zero_mem).2 ⟨fun i => by simp, fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

theorem piece_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (hA : IsAdapted h e f W (fun _ => 1) Λ)
    (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) {x : V} (hx : x ∈ Λ) :
    piece hh δ e f i x ∈ Λ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  obtain ⟨ha, hb, hww⟩ := (hA a b w hw).1 hx
  rcases i with _ | i | i
  · have : piece hh δ e f none (∑ i, a i • e i + ∑ i, b i • f i + w) = w := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_add (f := _), map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    have := (hA 0 0 w hw).2 ⟨fun i => by simp, fun i => by simp, hww⟩
    simpa using this
  · have : piece hh δ e f (some (Sum.inl i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = a i • e i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_add (f := _), map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using ha i) (e_mem hA hh i)
  · have : piece hh δ e f (some (Sum.inr i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = b i • f i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_add (f := _), map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using hb i) (f_mem hA hh i)

theorem tor_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) {u : Fin l → L}
    {t : V ≃ₗ[L] V} (ht : IsTor s e f W u t) (i : Idx l) :
    (t.toLinearMap : Module.End L V) * piece hh δ e f i = tau s u i • piece hh δ e f i ∧
      piece hh δ e f i * (t.toLinearMap : Module.End L V) = tau s u i • piece hh δ e f i := by
  obtain ⟨t1, t2, t3⟩ := ht
  constructor
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_e hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t1]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_f hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t2]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_w hh hF _ hw, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t3 w hw]
      · simp
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t1, map_smul,
        piece_e hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t2, map_smul,
        piece_f hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t3 w hw,
        piece_w hh hF _ hw]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp

theorem wt_le {l : ℕ} (i : Idx l) : wt i ≤ 2 * l := by
  rcases i with _ | i | i <;> simp only [wt] <;> omega

theorem wt_injective {l : ℕ} : Function.Injective (wt : Idx l → ℕ) := by
  rintro (_ | i | i) (_ | j | j) hij <;> simp only [wt] at hij <;>
    first
    | rfl
    | (exfalso; have := i.2; omega)
    | (exfalso; have := j.2; omega)
    | (exfalso; have := i.2; have := j.2; omega)
    | (congr 2; apply Fin.ext; have := i.2; have := j.2; omega)

theorem wt_rev {l : ℕ} (i : Idx l) : wt (rev i) + wt i = 2 * l := by
  rcases i with _ | i | i
  · simp only [wt, rev]; omega
  · simp only [wt, rev]; have := i.2; omega
  · simp only [wt, rev]; have := i.2; omega

theorem rev_rev {l : ℕ} (i : Idx l) : rev (rev i) = i := by
  rcases i with _ | i | i <;> rfl

theorem tau_mono (hs : IsInv s) {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (hm : Monotone fun i => ‖u i‖)
    (h1 : ∀ i, ‖u i‖ ≤ 1) (i j : Idx l) (hij : wt i ≤ wt j) : ‖tau s u i‖ ≤ ‖tau s u j‖ := by
  have hinv : ∀ m, 1 ≤ ‖(s (u m))⁻¹‖ := fun m => by
    rw [norm_inv, hs.2.1]
    exact (one_le_inv₀ (norm_pos_iff.2 (hu0 m))).2 (h1 m)
  rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp only [wt] at hij <;> simp only [tau]
  · simp
  · have := j.2; omega
  · simpa using hinv j
  · simpa using h1 i
  · have hij' : i ≤ j := by rw [Fin.le_def]; exact hij
    exact hm hij'
  · exact (h1 i).trans (hinv j)
  · have := i.2; omega
  · have := i.2; have := j.2; omega
  · rw [norm_inv, norm_inv, hs.2.1, hs.2.1]
    refine inv_anti₀ (norm_pos_iff.2 (hu0 j)) (hm ?_)
    have := i.2; have := j.2
    rw [Fin.le_def]; omega

theorem tau_ne {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (i : Idx l) : tau s u i ≠ 0 := by
  rcases i with _ | i | i
  · simp [tau]
  · simpa [tau] using hu0 i
  · simpa [tau] using hu0 i

theorem h_smul_left (hh : IsHerm s h) (c : L) (x y : V) : h (c • x) y = s c * h x y := by
  rw [hh.2.2.1 y (c • x), hh.2.1, map_mul, ← hh.2.2.1 y x]

theorem h_add_left (hh : IsHerm s h) (x x' y : V) : h (x + x') y = h x y + h x' y := by
  rw [hh.2.2.1 y (x + x'), hh.1, map_add (f := _), ← hh.2.2.1 y x, ← hh.2.2.1 y x']

theorem h_zero_left (hh : IsHerm s h) (y : V) : h 0 y = 0 := by
  rw [hh.2.2.1 y 0, h_zero_right hh, map_zero]

theorem h_sum_left (hh : IsHerm s h) {ι : Type} (A : Finset ι) (v : ι → V) (y : V) :
    h (∑ m ∈ A, v m) y = ∑ m ∈ A, h (v m) y :=
  map_sum (⟨⟨fun x => h x y, h_zero_left hh y⟩, fun x x' => h_add_left hh x x' y⟩ : V →+ L) v A

theorem h_sub_left (hh : IsHerm s h) (x x' y : V) : h (x - x') y = h x y - h x' y := by
  rw [hh.2.2.1 y (x - x'), h_sub_right hh, map_sub, ← hh.2.2.1 y x, ← hh.2.2.1 y x']

theorem projE_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projE hh δ e f i x) y = h x (projF hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, hs.1, ← hh.2.2.1 (f i) x]
  ring

theorem projF_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projF hh δ e f i x) y = h x (projE hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, ← hh.2.2.1 (e i) x]
  ring

theorem piece_adj (hs : IsInv s) (hh : IsHerm s h) (i : Idx l) (x y : V) :
    h (piece hh δ e f i x) y = h x (piece hh δ e f (rev i) y) := by
  rcases i with _ | i | i
  · have hx := map_sum (hLin hh x) (fun m => projE hh δ e f m y + projF hh δ e f m y) Finset.univ
    simp only [hLin_apply] at hx
    simp only [piece, rev, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      LinearMap.add_apply, h_sub_left hh, h_sub_right hh, h_sum_left hh, hx, h_add_left hh, hh.1,
      projE_adj hs hh, projF_adj hs hh]
    congr 1
    exact Finset.sum_congr rfl fun m _ => add_comm _ _
  · exact projE_adj hs hh i x y
  · exact projF_adj hs hh i x y

theorem exists_star (hs : IsInv s) (hh : IsHerm s h)
    (hadj : ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y)) :
    ∃ st : Module.End L V → Module.End L V, (∀ g x y, h (g x) y = h x (st g y)) ∧
      (∀ a b, st (a * b) = st b * st a) ∧ st 1 = 1 ∧ st 0 = 0 ∧
      ∀ i : Idx l, st (piece hh δ e f i) = piece hh δ e f (rev i) := by
  choose st hst using hadj
  refine ⟨st, hst, fun a b => ?_, ?_, ?_, fun i => ?_⟩
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, Module.End.mul_apply, Module.End.mul_apply, ← hst, ← hst]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; rfl
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; simp [h_zero_left hh, h_zero_right hh]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, piece_adj hs hh]

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem isCongIdeal_congJ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    {π : L} (hπ : ‖π‖ < 1) {ι : Type} (P : ι → Module.End L V)
    (hP : ∀ i, ∀ x ∈ Λ, P i x ∈ Λ) : IsCongIdeal (congJ Λ π) P := by
  refine ⟨?_, ?_, ?_, GlobalTheory.T.congruence_endomorphism_inverse_exists Λ hΛ π hπ⟩
  · intro x hx y hy v hv
    obtain ⟨z, hz, e1⟩ := hy v hv
    obtain ⟨w, hw, e2⟩ := hx z hz
    refine ⟨π • w, lat_smul hΛ hπ.le hw, ?_⟩
    simp [Module.End.mul_apply, e1, e2]
  · intro i x hx v hv
    obtain ⟨z, hz, e1⟩ := hx v hv
    exact ⟨P i z, hP i z hz, by simp [Module.End.mul_apply, e1]⟩
  · intro i x hx v hv
    exact hx _ (hP i v hv)

theorem congJ_smul {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (π : L) (c : L) (hc : ‖c‖ ≤ 1) (x : Module.End L V)
    (hx : x ∈ congJ Λ π) : c • x ∈ congJ Λ π := by
  intro v hv
  obtain ⟨z, hz, e1⟩ := hx v hv
  refine ⟨c • z, lat_smul hΛ hc hz, ?_⟩
  simp [e1, smul_comm c π z]

theorem isUpper_rev_iff {E : Type} [Ring E] {l : ℕ} (P : Idx l → E) (b : E) :
    IsUpper (fun i => 2 * l - wt i) P b ↔ IsLower wt P b := by
  constructor
  · intro H i j hij
    exact H i j (by have := wt_le i; have := wt_le j; simp only; omega)
  · intro H i j hij
    refine H i j ?_
    have := wt_le i; have := wt_le j
    simp only at hij
    omega

theorem stIwahori : StIwahori := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc
  have hδ0 : δ ≠ 0 := hδ.1
  set P := piece hh δ e f with hPdef
  have hP : IsPieces P := isPieces_piece hh hδ0 hF
  have hJ : IsCongIdeal (congJ Λ π) P :=
    isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx
  obtain ⟨st, hst, st_mul, st_one, st_zero, st_P⟩ :=
    exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (GlobalTheory.T.hermitian_adjoint_exists s hs h hh)
  have hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π := fun x hx => by
    obtain ⟨y, hy, e1⟩ := hc x hx
    exact ⟨y, hy, by simpa using e1⟩
  obtain ⟨a, b, ha, hb, hup, hlo, hab⟩ := GlobalTheory.T.iwahori_upper_lower_factorization wt wt_injective P hP _ hJ _ hk1

  obtain ⟨ya, hya, ia1, ia2⟩ := hJ.inv _ ha
  obtain ⟨yb, hyb, ib1, ib2⟩ := hJ.inv _ hb
  rw [add_sub_cancel] at ia1 ia2 ib1 ib2
  have hkk : ∀ y, st (k.toLinearMap) (k y) = y := fun y => by
    refine eq_of_pair hh fun x => ?_
    have := hst k.toLinearMap x (k y)
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hk x y]
  have hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1 := by
    ext y; exact hkk y
  have hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := k.surjective y
    simp [Module.End.mul_apply, hkk z]
  rw [hab] at hk2 hk3
  obtain ⟨ua, ub⟩ := GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni wt P hP rev rev_rev
    (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P
    (fun a a' h1 h2 h3 => GlobalTheory.T.upper_triangular_inverse_is_upper wt P hP a a' h1 h2 h3)
    (fun a a' h1 h2 h3 => (isUpper_rev_iff P a').1 (GlobalTheory.T.upper_triangular_inverse_is_upper _ P hP a a' h1 h2 ((isUpper_rev_iff P a).2 h3)))
    a (1 + ya) b (1 + yb) ia1 ia2 ib1 ib2 hup hlo hk2 hk3
  let A : V ≃ₗ[L] V := LinearEquiv.ofLinear a (1 + ya) ia1 ia2
  let B : V ≃ₗ[L] V := LinearEquiv.ofLinear b (1 + yb) ib1 ib2
  have isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g := fun g hg x y => by
    have := hst g.toLinearMap x (g y)
    simp only [LinearEquiv.coe_coe] at this
    rw [this]
    have h2 : st g.toLinearMap (g y) = y := by
      have := congrArg (fun m : Module.End L V => m y) hg
      simpa [Module.End.mul_apply] using this
    rw [h2]
  refine ⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩
  · ext x
    have := congrArg (fun m : Module.End L V => m x) hab
    simpa [A, B, Module.End.mul_apply] using this
  · intro u t hu0 hm h1 ht
    have hT := fun i => tor_piece (δ := δ) hh hδ0 hF ht i
    have key := GlobalTheory.T.torus_conjugation_preserves_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u)
      (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply])
      (fun i => (hT i).1) (fun i => (hT i).2)
      (tau_mono hs hu0 hm h1) a b ha hb hup hlo.1
    constructor
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.1 x hx
      exact ⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.2 x hx
      exact ⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩

end GlobalTheory.CompanionTheory.Iwahori

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IwahoriStatement : StIwahori := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.stIwahori | exact GlobalTheory.CompanionTheory.Iwahori.stIwahori | (intros; apply GlobalTheory.CompanionTheory.Iwahori.stIwahori <;> assumption)
end

module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowersDiagonalAtTBlock

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationQuotientSeparatedDvd
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SymmetricIndexRegularity

theorem orderEmb_rev {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key : (fun j : Fin m => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro i j hij
      exact Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij))
  have := congrFun key j
  rw [← this, Fin.rev_rev]

theorem diff_injective {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun i : Fin n => x i - x i.rev := by
  have : StrictAnti fun i : Fin n => x i - x i.rev := by
    intro i j hij
    have h1 := hx hij
    have h2 := hx (Fin.rev_lt_rev.mpr hij)
    show x j - x j.rev < x i - x i.rev
    omega
  exact this.injective

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S)
    (j : Fin m) : nv (restr x S h) j = x (S.orderEmbOfFin h j) - x (S.orderEmbOfFin h j).rev := by
  simp only [nv, restr, orderEmb_rev S h hS]

theorem restr_strictAnti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) :=
  fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n} :
    i ∈ symIdx n mid s ↔ (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
  simp [symIdx]

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    ∀ i ∈ symIdx n mid s, i.rev ∈ symIdx n mid s := by
  intro i hi
  have hv : i.rev.val = n - 1 - i.val := by
    have := i.isLt
    rw [Fin.val_rev]; omega
  have hv' : n - 1 - i.rev.val = i.val := by
    have := i.isLt
    omega
  rw [mem_symIdx] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    simpa only [hv'] using hs
  · left
    refine ⟨by omega, ?_⟩
    simpa only [hv] using hs
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_disj (n : ℕ) (m₁ m₂ : Prop) [Decidable m₁] [Decidable m₂] (s : Finset (Fin (n / 2)))
    (hm : n % 2 = 1 → ¬ (m₁ ∧ m₂)) (i : Fin n) (h₁ : i ∈ symIdx n m₁ s) (h₂ : i ∈ symIdx n m₂ sᶜ) : False := by
  have hi := i.isLt
  rw [mem_symIdx] at h₁ h₂
  rcases h₁ with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm₁, ho, he⟩ <;> rcases h₂ with ⟨h', hs'⟩ | ⟨h', hs'⟩ | ⟨hm₂, ho', he'⟩
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact hm ho ⟨hm₁, hm₂⟩

theorem localization_quotient_separated_dvd {F : Type} [Field F] (ord : F → ℤ) {n a b : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x)
    (S₁ S₂ : Finset (Fin n)) (h₁ : S₁.card = a) (h₂ : S₂.card = b) (y₁ : ∀ i ∈ S₁, i.rev ∈ S₁)
    (y₂ : ∀ i ∈ S₂, i.rev ∈ S₂) (hd : ∀ i, i ∈ S₁ → i ∈ S₂ → False) (u₁ : Fin a → F) (u₂ : Fin b → F)
    (hu₁ : ∀ j, ord (u₁ j) = nv (restr x S₁ h₁) j) (hu₂ : ∀ j, ord (u₂ j) = nv (restr x S₂ h₂) j) :
    ((∏ i, (X - C (u₁ i))) * ∏ i, (X - C (u₂ i))).Separable := by
  have hprod : (∏ i, (X - C (u₁ i))) * (∏ i, (X - C (u₂ i))) = ∏ i, (X - C (Sum.elim u₁ u₂ i)) := by
    rw [Fintype.prod_sum_type]; simp
  rw [hprod, separable_prod_X_sub_C_iff]
  have hinj := diff_injective hx
  have e₁ : ∀ i j, u₁ i = u₁ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₁, nv_restr x S₁ h₁ y₁, nv_restr x S₁ h₁ y₁] at this
    exact (S₁.orderEmbOfFin h₁).injective (hinj this)
  have e₂ : ∀ i j, u₂ i = u₂ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₂, hu₂, nv_restr x S₂ h₂ y₂, nv_restr x S₂ h₂ y₂] at this
    exact (S₂.orderEmbOfFin h₂).injective (hinj this)
  have e₃ : ∀ i j, u₁ i = u₂ j → False := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₂, nv_restr x S₁ h₁ y₁, nv_restr x S₂ h₂ y₂] at this
    have h := hinj this
    refine hd _ (Finset.orderEmbOfFin_mem S₁ h₁ i) ?_
    rw [show S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ j from h]
    exact Finset.orderEmbOfFin_mem S₂ h₂ j
  rintro (i | i) (j | j) hij
  · exact congrArg _ (e₁ _ _ hij)
  · exact (e₃ _ _ hij).elim
  · exact (e₃ _ _ hij.symm).elim
  · exact congrArg _ (e₂ _ _ hij)

end GlobalTheory.CompanionTheory.SymmetricIndexRegularity
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaGLMemIwGL
open Matrix ValuativeRel
open GlobalTheory.CompanionTheory.TwContraction

namespace GlobalTheory.CompanionTheory.ThetaContraction

section Step

variable {F : Type} [Field F] {n : ℕ}

def sg (F : Type) [Field F] {n : ℕ} (i l : Fin n) : F := (-1) ^ ((i : ℕ) + l)

theorem sg_mul_self (i l : Fin n) : sg F i l * sg F i l = 1 := by
  rw [sg, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

theorem sg_self (i : Fin n) : sg F i i = 1 := by
  rw [sg]
  exact Even.neg_one_pow ⟨_, rfl⟩

theorem map_sg (c : F →+* F) (i l : Fin n) : c (sg F i l) = sg F i l := by
  simp [sg]

theorem theta_expand (c : F →+* F) (p : GL (Fin n) F) (T : Matrix (Fin n) (Fin n) F)
    (hP : (p : Matrix (Fin n) (Fin n) F) = 1 + T) (i l : Fin n) :
    (GlobalTheory.CuspRep.thetaGL n c p).val i l = (1 : Matrix (Fin n) (Fin n) F) i l -
      sg F i l * c (T l.rev i.rev) +
      sg F i l * c ((T * T * ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) l.rev i.rev) := by
  set P' : Matrix (Fin n) (Fin n) F := ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hP'
  have h1 : (1 + T) * P' = 1 := by
    rw [← hP, hP', ← Units.val_mul, mul_inv_cancel]
    rfl
  have h2 : P' = 1 - T * P' := by
    rw [add_mul, one_mul] at h1
    exact eq_sub_of_add_eq h1
  have h3 : P' = 1 - T + T * T * P' := by
    calc P' = 1 - T * P' := h2
      _ = 1 - T * (1 - T * P') := by rw [← h2]; exact h2
      _ = 1 - T + T * T * P' := by noncomm_ring
  have hent : P' l.rev i.rev = (1 - T + T * T * P') l.rev i.rev := congrFun (congrFun h3 _) _
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← hP', hent, Matrix.add_apply, Matrix.sub_apply, map_add (f := _), map_sub,
    mul_add, mul_sub]
  congr 2
  · by_cases h : i = l
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, mul_one]
      exact sg_self i
    · have h' : l.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h', map_zero, mul_zero]

variable [ValuativeRel F]

theorem step (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F)
    (c : F →+* F) (hcv : ∀ a, valuation F (c a) = valuation F a) (hcc : ∀ a, c (c a) = a)
    (hθU : ∀ g ∈ U, GlobalTheory.CuspRep.thetaGL n c g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (j : ℕ) (g : GL (Fin n) F) (hgU : g ∈ U)
    (hgD : ∀ i l, i ≠ l → valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j) :
    ∃ p ∈ U, x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p ∈ U ∧
      ∀ i l, i ≠ l → valuation F (((x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ (j + 1) := by
  have hI : g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by rw [← hU]; exact hgU
  have hρ1' : ρ ≤ 1 := hρ1.le
  set C : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) with hCdef
  let d : Fin n → F := fun i => C i i
  have hd : ∀ i, valuation F (d i) = 1 := fun i => val_diag_of_mem_iwahori hI i
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hsgv : ∀ i l : Fin n, valuation F (sg F i l) = 1 := fun i l => by
    rw [sg, map_pow, Valuation.map_neg, map_one, one_pow]
  have hev : ∀ i, valuation F (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).2 (he i)
  have hq : ∀ i l, i < l → valuation F (e i / e l) ≤ ρ := fun i l h => by
    rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 (hev l))]
    exact hc i l h
  set s : ℕ := max j 1 with hs
  have hs1 : 1 ≤ s := le_max_right _ _
  have hjs : j ≤ s := le_max_left _ _
  have hsj : s ≤ j + 1 := max_le (Nat.le_succ j) (Nat.le_add_left 1 j)
  have hlow : ∀ i l, l < i → valuation F (C i l) ≤ ρ ^ s := fun i l h => by
    rcases max_choice j 1 with h' | h'
    · rw [hs, h']; exact hgD i l h.ne'
    · rw [hs, h', pow_one]; exact hunif _ (hI.2 i l h)
  let T : Matrix (Fin n) (Fin n) F := fun i l =>
    if l < i then sg F l.rev i.rev * c (C l.rev i.rev / d l.rev)
    else if i < l then (e i / e l) * (C i l / d l) else 0
  have hTlo : ∀ i l, l < i → T i l = sg F l.rev i.rev * c (C l.rev i.rev / d l.rev) :=
    fun i l h => if_pos h
  have hTup : ∀ i l, i < l → T i l = (e i / e l) * (C i l / d l) := fun i l h => by
    show (if l < i then _ else _) = _
    rw [if_neg (not_lt.2 h.le), if_pos h]
  have hTd : ∀ i, T i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hTlov : ∀ i l, l < i → valuation F (T i l) ≤ ρ ^ s := fun i l h => by
    rw [hTlo i l h, map_mul, hsgv, one_mul, hcv, map_div₀, hd, div_one]
    exact hlow _ _ (Fin.rev_lt_rev.2 h)
  have hTupv : ∀ i l, i < l → valuation F (T i l) ≤ ρ ^ (j + 1) := fun i l h => by
    rw [hTup i l h, map_mul, map_div₀ _ (C i l), hd, div_one, pow_succ']
    exact mul_le_mul' (hq i l h) (hgD i l h.ne)
  have hT : Dp ρ s T := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · exact (hTupv i l h).trans (pow_le_pow_right_of_le_one' hρ1' hsj)
    · subst h; rw [hTd, map_zero]; exact zero_le'
    · exact hTlov i l h
  have hρs : ρ ^ s ≤ ρ := by
    calc ρ ^ s ≤ ρ ^ 1 := pow_le_pow_right_of_le_one' hρ1' hs1
      _ = ρ := pow_one ρ
  set P : Matrix (Fin n) (Fin n) F := 1 + T with hP
  have hPd : ∀ i, P i i = 1 := fun i => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_eq, hTd, add_zero]
  have hPo : ∀ i l, i ≠ l → P i l = T i l := fun i l h => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_ne h, zero_add]
  have hPint : ∀ i l, valuation F (P i l) ≤ 1 := fun i l => by
    by_cases h : i = l
    · subst h; rw [hPd, map_one]
    · rw [hPo i l h]; exact (hT i l).trans (hρs.trans hρ1')
  have hPlow : ∀ i l, l < i → valuation F (P i l) < 1 := fun i l h => by
    rw [hPo i l h.ne']
    exact lt_of_le_of_lt ((hT i l).trans hρs) hρ1
  have hPdet : valuation F P.det = 1 := by
    have h1 := val_det_sub_prod_lt P hPint hPlow
    rw [Finset.prod_congr rfl fun i _ => hPd i, Finset.prod_const_one] at h1
    have := Valuation.map_eq_of_sub_lt (valuation F) (x := (1 : F)) (y := P.det) (by rwa [map_one])
    rwa [map_one] at this
  have hPne : P.det ≠ 0 := fun h => by
    rw [h, map_zero] at hPdet
    exact zero_ne_one hPdet
  let p : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPne
  have hpv : (p : Matrix (Fin n) (Fin n) F) = P := rfl
  have hpI : p ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := ⟨mem_unitGL_of p hPint hPdet, hPlow⟩
  have hpU : p ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact hpI
  have hxinv : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (e i)⁻¹ := by
    rw [Matrix.coe_units_inv, hx]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he i)
  let q : GL (Fin n) F := x⁻¹ * p * x
  set Q : Matrix (Fin n) (Fin n) F := (q : Matrix (Fin n) (Fin n) F) with hQdef
  have hQ : ∀ i l, Q i l = (e i)⁻¹ * P i l * e l := fun i l => by
    show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l = _
    rw [Units.val_mul, Units.val_mul, hxinv, hx, hpv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hQd : ∀ i, Q i i = 1 := fun i => by
    rw [hQ, hPd, mul_one, inv_mul_cancel₀ (he i)]
  have hQup : ∀ i l, i < l → Q i l = C i l / d l := fun i l h => by
    rw [hQ, hPo i l h.ne, hTup i l h]
    have h1 := he i
    have h2 := he l
    field_simp
  have hQlow : ∀ i l, l < i → valuation F (Q i l) ≤ ρ * ρ ^ s := fun i l h => by
    rw [hQ, hPo i l h.ne', show (e i)⁻¹ * T i l * e l = (e l / e i) * T i l by
      rw [div_eq_mul_inv]; ring, map_mul]
    exact mul_le_mul' (hq l i h) (hTlov i l h)
  have hQint : ∀ i l, valuation F (Q i l) ≤ 1 := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, map_div₀, hd, div_one]
      exact mem_unitGL_entries hI.1 i l
    · subst h; rw [hQd, map_one]
    · refine (hQlow i l h).trans ?_
      calc ρ * ρ ^ s ≤ 1 * 1 := mul_le_mul' hρ1' (hρs.trans hρ1')
        _ = 1 := one_mul 1
  have hQdet : valuation F Q.det = 1 := by
    have : Q.det = P.det := by
      show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = _
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hpv]
      have h3 : (x : Matrix (Fin n) (Fin n) F).det * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
        simp
      calc _ = P.det * ((x : Matrix (Fin n) (Fin n) F).det *
            ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) := by ring
        _ = P.det := by rw [h3, mul_one]
    rw [this]; exact hPdet
  have hqU : q ∈ U := by
    have : q ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := ⟨mem_unitGL_of q hQint hQdet, fun i l h =>
      lt_of_le_of_lt (hQlow i l h) (lt_of_le_of_lt (mul_le_mul' le_rfl hρs) (by
        calc ρ * ρ ≤ ρ * 1 := mul_le_mul' le_rfl hρ1'
          _ = ρ := mul_one ρ
          _ < 1 := hρ1 |>.trans_le le_rfl))⟩
    rw [← SetLike.mem_coe, hU]
    exact this

  let T' : Matrix (Fin n) (Fin n) F := fun i l => - (sg F i l * c (T l.rev i.rev))
  have hT'v : ∀ i l, valuation F (T' i l) = valuation F (T l.rev i.rev) := fun i l => by
    show valuation F (- (sg F i l * c (T l.rev i.rev))) = _
    rw [Valuation.map_neg, map_mul, hsgv, one_mul, hcv]
  have hT' : Dp ρ s T' := fun i l => by
    rw [hT'v]; exact hT _ _
  have hT'd : ∀ i, T' i i = 0 := fun i => by
    show - (sg F i i * c (T i.rev i.rev)) = 0
    rw [hTd, map_zero, mul_zero, neg_zero]
  have hT'lo : ∀ i l, l < i → T' i l = - (C i l / d i) := fun i l h => by
    show - (sg F i l * c (T l.rev i.rev)) = _
    rw [hTlo _ _ (Fin.rev_lt_rev.2 h), Fin.rev_rev, Fin.rev_rev, map_mul, map_sg, hcc, ← mul_assoc,
      sg_mul_self, one_mul]
  have hT'up : ∀ i l, i < l → valuation F (T' i l) ≤ ρ ^ (j + 1) := fun i l h => by
    rw [hT'v]
    exact hTupv _ _ (Fin.rev_lt_rev.2 h)
  have hp0 : Dp ρ 0 ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := fun a b => by
    rw [pow_zero]
    have : p⁻¹ ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by
      rw [← hU]; exact U.inv_mem hpU
    exact mem_unitGL_entries this.1 a b
  let W : Matrix (Fin n) (Fin n) F := T * T * ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hW : Dp ρ (s + s + 0) W := (hT.mul hT).mul hp0
  let D : Matrix (Fin n) (Fin n) F := fun i l => sg F i l * c (W l.rev i.rev)
  have hD : Dp ρ (s + s + 0) D := fun i l => by
    show valuation F (sg F i l * c (W l.rev i.rev)) ≤ _
    rw [map_mul, hsgv, one_mul, hcv]
    exact hW _ _
  have hθ : ((GlobalTheory.CuspRep.thetaGL n c p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + T' + D := by
    ext i l
    rw [theta_expand c p T hpv i l, Matrix.add_apply, Matrix.add_apply]
    show _ = (1 : Matrix (Fin n) (Fin n) F) i l + - (sg F i l * c (T l.rev i.rev)) +
      sg F i l * c (W l.rev i.rev)
    rw [sub_eq_add_neg]
  let Dg : Matrix (Fin n) (Fin n) F := Matrix.diagonal d
  let Co : Matrix (Fin n) (Fin n) F := C - Dg
  have hC0 : Dp ρ 0 C := fun a b => by
    rw [pow_zero]
    exact mem_unitGL_entries hI.1 a b
  have hCo : Dp ρ j Co := fun i l => by
    by_cases h : i = l
    · subst h
      show valuation F (C i i - Dg i i) ≤ _
      rw [show Dg i i = C i i from Matrix.diagonal_apply_eq _ _, sub_self, map_zero]
      exact zero_le'
    · show valuation F (C i l - Dg i l) ≤ _
      rw [show Dg i l = 0 from Matrix.diagonal_apply_ne _ h, sub_zero]
      exact hgD i l h
  let B : Matrix (Fin n) (Fin n) F := C + Dg * T' - Q * Dg
  have hBe : ∀ i l, B i l = C i l + d i * T' i l - Q i l * d l := fun i l => by
    show (C + Dg * T' - Q * Dg) i l = _
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hB : Dp ρ (j + 1) B := fun i l => by
    rw [hBe]
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, div_mul_cancel₀ _ (hd0 l), add_sub_cancel_left, map_mul, hd, one_mul]
      exact hT'up i l h
    · subst h
      rw [hT'd, hQd, mul_zero, add_zero, one_mul]
      show valuation F (C i i - C i i) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    · rw [hT'lo i l h, mul_neg, mul_div_cancel₀ _ (hd0 i),
        add_neg_cancel, zero_sub, Valuation.map_neg, map_mul, hd, mul_one]
      refine (hQlow i l h).trans ?_
      rw [← pow_succ']
      exact pow_le_pow_right_of_le_one' hρ1' (Nat.succ_le_succ hjs)
  let R : Matrix (Fin n) (Fin n) F := B + Co * T' + C * D
  have hR : Dp ρ (j + 1) R :=
    (hB.add ((hCo.mul hT').mono hρ1' (Nat.add_le_add_left hs1 j))).add
      ((hC0.mul hD).mono hρ1' (by omega))
  have hid : C * (1 + T' + D) = Q * Dg + R := by
    show C * (1 + T' + D) = Q * Dg + (C + Dg * T' - Q * Dg + (C - Dg) * T' + C * D)
    noncomm_ring
  have hw : x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p =
      q⁻¹ * (g * GlobalTheory.CuspRep.thetaGL n c p) := by
    show _ = (x⁻¹ * p * x)⁻¹ * _
    group
  refine ⟨p, hpU, ?_, ?_⟩
  · rw [hw]
    exact U.mul_mem (U.inv_mem hqU) (U.mul_mem hgU (hθU p hpU))
  · intro i l hil
    rw [hw]
    have hval : ((q⁻¹ * (g * GlobalTheory.CuspRep.thetaGL n c p) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = Dg + ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * R := by
      rw [Units.val_mul, Units.val_mul, hθ]
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (C * (1 + T' + D)) = _
      rw [hid, mul_add, ← mul_assoc]
      congr 1
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (q : Matrix (Fin n) (Fin n) F) * Dg = Dg
      rw [← Units.val_mul, inv_mul_cancel]
      simp
    rw [hval, Matrix.add_apply, show Dg i l = 0 from Matrix.diagonal_apply_ne _ hil, zero_add]
    have hq0 : Dp ρ 0 ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [pow_zero]
      have : q⁻¹ ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by
        rw [← hU]; exact U.inv_mem hqU
      exact mem_unitGL_entries this.1 a b
    have := (hq0.mul hR) i l
    rwa [zero_add] at this

end Step

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem contraction (U : Subgroup (GL (Fin n) F))
    (hU : (U : Set (GL (Fin n) F)) = PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F)
    (hcpt : IsCompact (PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F))
    (c : F →+* F) (hcc : ∀ a, c (c a) = a) (hcv : ∀ a, valuation F (c a) = valuation F a)
    (hcont : Continuous c) (hθU : ∀ g ∈ U, GlobalTheory.CuspRep.thetaGL n c g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (δ : GL (Fin n) F) (hδ : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble F x) :
    ∃ m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F, ∃ t ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F,
      (∀ i l, i ≠ l → (t : Matrix (Fin n) (Fin n) F) i l = 0) ∧
      m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m = x * t := by
  have hUI : ∀ g, g ∈ U ↔ g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := fun g => by
    rw [← hU]; rfl
  let f : GL (Fin n) F → GL (Fin n) F := fun m =>
    x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m
  have hf : Continuous f :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul
      (GlobalTheory.ThetaPull.continuous_thetaGL c hcont)
  let S : ℕ → Set (GL (Fin n) F) := fun j =>
    {m | m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ∧ f m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ∧
      ∀ i l, i ≠ l → valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j}
  have hclosedI : IsClosed (PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F) := hcpt.isClosed
  have hSc : ∀ j, IsClosed (S j) := fun j => by
    have h1 : IsClosed {m : GL (Fin n) F | ∀ i l, i ≠ l →
        valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun l => isClosed_iInter fun _ => ?_
      have hcont : Continuous fun m : GL (Fin n) F => (f m : Matrix (Fin n) (Fin n) F) i l :=
        (Units.continuous_val.comp hf).matrix_elem i l
      exact (IsNonarchimedeanLocalField.isCompact_closedBall F (ρ ^ j)).isClosed.preimage hcont
    exact hclosedI.inter ((hclosedI.preimage hf).inter h1)
  have hSn : ∀ j, (S j).Nonempty := by
    intro j
    induction j with
    | zero =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hδ
      have hfa : f a = b * GlobalTheory.CuspRep.thetaGL n c a := by
        show x⁻¹ * a⁻¹ * (a * x * b) * _ = _
        group
      have hfaI : f a ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by
        rw [hfa, ← hUI]
        exact U.mul_mem ((hUI _).2 hb) (hθU _ ((hUI _).2 ha))
      refine ⟨a, ha, hfaI, fun i l _ => ?_⟩
      rw [pow_zero]
      exact mem_unitGL_entries hfaI.1 i l
    | succ j ih =>
      obtain ⟨m, hm, hfm, hD⟩ := ih
      obtain ⟨p, hp, hcU, hcD⟩ := step U hU c hcv hcc hθU ρ hρ1 hunif e he hc x hx j (f m)
        ((hUI _).2 hfm) hD
      have hfmp : f (m * p) = x⁻¹ * p⁻¹ * x * f m * GlobalTheory.CuspRep.thetaGL n c p := by
        show x⁻¹ * (m * p)⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c (m * p) =
          x⁻¹ * p⁻¹ * x * (x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m) * _
        rw [map_mul]
        group
      refine ⟨m * p, (hUI _).1 (U.mul_mem ((hUI _).2 hm) hp), ?_, ?_⟩
      · rw [hfmp]; exact (hUI _).1 hcU
      · rw [hfmp]; exact hcD
  have hSd : ∀ j, S (j + 1) ⊆ S j := fun j m hm => ⟨hm.1, hm.2.1, fun i l h =>
    (hm.2.2 i l h).trans (pow_le_pow_right_of_le_one' hρ1.le (Nat.le_succ j))⟩
  have hS0 : IsCompact (S 0) := hcpt.of_isClosed_subset (hSc 0) fun m hm => hm.1
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSn hS0 hSc
  have hm' : ∀ j, m ∈ S j := Set.mem_iInter.1 hm
  have : MulArchimedean (ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨m, (hm' 0).1, f m, (hm' 0).2.1, fun i l hil => ?_, ?_⟩
  · by_contra h0
    have hv : valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hρ1 (Units.mk0 _ hv)
    exact absurd ((hm' j).2.2 i l hil) (not_le.2 hj)
  · show _ = x * (x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m)
    group

end Main

section Local

open NumberField IsDedekindDomain GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem thetaGL_mem_iwGL {w : Pl E} (c : w.adicCompletion E →+* w.adicCompletion E)
    (hcv : ∀ x, Valued.v (c x) = Valued.v x) (n : ℕ) (g : GLw n w) (hg : g ∈ iwGL n w) :
    GlobalTheory.CuspRep.thetaGL n c g ∈ iwGL n w := by
  have hsg : ∀ i l : Fin n, Valued.v ((-1 : w.adicCompletion E) ^ ((i : ℕ) + l)) = 1 := fun i l => by
    rw [map_pow, Valuation.map_neg, map_one, one_pow]
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg
  obtain ⟨-, -, h4⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g⁻¹).1.1 (inv_mem hg)
  refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨fun i l => ?_, fun i l => ?_, fun i l h => ?_⟩
  · rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv]
    exact h2 _ _
  · rw [← map_inv, GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv, inv_inv]
    exact h1 _ _
  · rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv]
    exact h4 _ _ (Fin.rev_lt_rev.2 h)

theorem contr_tw : PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw.P_contr_tw := by
  intro E _ _ _ hU w hw ϖ hϖ n y hy δ hδ
  obtain ⟨hcont, hcc, hcv, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  have hθ : GlobalTheory.BCT.thL n w = GlobalTheory.CuspRep.thetaGL n (GlobalTheory.BCT.cj w) := if_neg hw
  have hEq : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
    have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ValuativeRel.isEquiv _ _
  have hvF : ∀ a, valuation (w.adicCompletion E) (GlobalTheory.BCT.cj w a) = valuation (w.adicCompletion E) a :=
    fun a => le_antisymm ((hEq _ _).2 (hcv a).le) ((hEq _ _).2 (hcv a).ge)
  have hIU : ((GlobalTheory.BCT.iwGL n w : Subgroup _) : Set (GlobalTheory.BCT.GLw n w)) =
      PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E) := by
    ext g
    exact (GlobalTheory.CompanionTheory.IwContract.mem_iwahori_iff).symm
  have hcpt : IsCompact (PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E)) := by
    rw [← hIU]
    exact GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1
    ((Valuation.ne_zero_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).2 ϖ.ne_zero)
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := hϖ.1
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm] at this
    omega
  have hρ1 : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 := by
    refine (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 ?_
    rw [← hu, ← WithZero.coe_one, WithZero.coe_lt_coe]
    change Multiplicative.toAdd u < 0
    omega
  have hunif : ∀ a : w.adicCompletion E, valuation (w.adicCompletion E) a < 1 →
      valuation (w.adicCompletion E) a ≤ valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := by
    intro a ha
    have ha' := (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w a).1 ha
    refine (hEq _ _).2 ?_
    by_cases h0 : Valued.v a = 0
    · rw [h0]; exact zero_le'
    · obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 h0
      rw [← hb, ← WithZero.coe_one, WithZero.coe_lt_coe] at ha'
      rw [← hb, ← hu, WithZero.coe_le_coe]
      change Multiplicative.toAdd b < 0 at ha'
      change Multiplicative.toAdd b ≤ Multiplicative.toAdd u
      omega
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have he : ∀ i, e i ≠ 0 := fun i => Units.ne_zero _
  have hc : ∀ i l, i < l → valuation (w.adicCompletion E) (e i) ≤
      valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) * valuation (w.adicCompletion E) (e l) := by
    intro i l h
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((b + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (b + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (b + 1)
        ≤ valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hρ1.le (Nat.succ_le_succ (Nat.zero_le b))
      _ = _ := pow_one _
  have hx : ((GlobalTheory.BCT.tdiag ϖ y : GlobalTheory.BCT.GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal e := by
    rw [GlobalTheory.BCT.tdiag, GlobalTheory.SmGL.val_diagT]
  have hδ' : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (GlobalTheory.BCT.tdiag ϖ y) := by
    have h : ∃ x ∈ GlobalTheory.BCT.iwGL n w, ∃ z ∈ GlobalTheory.BCT.iwGL n w, δ = x * GlobalTheory.BCT.tdiag ϖ y * z := by
      by_contra h
      exact hδ (if_neg h)
    obtain ⟨a, ha, b, hb, e'⟩ := h
    exact ⟨a, by rw [← hIU]; exact ha, b, by rw [← hIU]; exact hb, e'⟩
  obtain ⟨m, hm, t, ht, hoff, h⟩ := contraction (GlobalTheory.BCT.iwGL n w) hIU hcpt (GlobalTheory.BCT.cj w) hcc hvF hcont
    (fun g hg => thetaGL_mem_iwGL _ hcv n g hg) _ hρ1 hunif e he hc _ hx δ hδ'
  refine ⟨m, by rw [← SetLike.mem_coe, hIU]; exact hm, t, ⟨hoff, fun i => ?_⟩, by rw [hθ]; exact h⟩
  exact hEq.eq_one_iff_eq_one.1 (val_diag_of_mem_iwahori ht i)

end Local

end GlobalTheory.CompanionTheory.ThetaContraction
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactClosureZpowersMap
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.TwSide

section Generic

variable {G : Type} [Group G]

end Generic

section Diag

variable {L : Type} [Field L]

theorem thetaGL_diagT (c : L →+* L) {n : ℕ} (u : Fin n → Lˣ) :
    thetaGL n c (GlobalTheory.SmGL.diagT L (Fin n) u) =
      GlobalTheory.SmGL.diagT L (Fin n) fun i => Units.map (c : L →* L) (u i.rev)⁻¹ := by
  apply Units.ext
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero,
      mul_zero]

theorem exists_diagT {n : ℕ} (g : GL (Fin n) L) (h : ∀ i j : Fin n, i ≠ j → g.val i j = 0) :
    ∃ s : Fin n → Lˣ, g = GlobalTheory.SmGL.diagT L (Fin n) s := by
  have hne : ∀ i, g.val i i ≠ 0 := by
    intro i h0
    have h1 : (g.val * (g⁻¹).val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [h i k hk, zero_mul]
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

end Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_diagT_of_mem_TO {n : ℕ} {w : Pl E} {τ : GLw n w} (hτ : τ ∈ TO n w) :
    ∃ v : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (v i : w.adicCompletion E) = 1) ∧
      τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
  obtain ⟨v, hv⟩ := exists_diagT τ hτ.1
  refine ⟨v, fun i => ?_, hv⟩
  have h := hτ.2 i
  rw [hv, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq] at h
  exact h

theorem nrmL_diagT {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (u : Fin n → (w.adicCompletion E)ˣ) :
    nrmL n w (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n)
        fun i => u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ := by
  rw [nrmL, if_neg hw, thetaGL_diagT, ← map_mul]
  rfl

theorem ordL_norm_entry (hU : Unr E) {n : ℕ} {w : Pl E} (u : Fin n → (w.adicCompletion E)ˣ) (y : Fin n → ℤ)
    (hu : ∀ i, ordL (u i : w.adicCompletion E) = y i) (i : Fin n) :
    ordL ((u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = nv y i := by
  obtain ⟨-, -, hcv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hinv : ordL (((u i.rev)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    have h1 := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i.rev).ne_zero ((u i.rev)⁻¹).ne_zero
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one, hu] at h1
    omega
  have hmap : ordL ((Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    rw [← hinv]
    exact GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (hcv _)
  rw [Units.val_mul, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i).ne_zero (Units.ne_zero _), hu, hmap]
  simp only [nv]
  omega

end GlobalTheory.CompanionTheory.TwSide
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorus
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MT PositivityTheory.Rg.BcB.F.MLM
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RegPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open GlobalTheory.CompanionTheory.MatchPow in
theorem hasVals_nrm (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a : ℕ}
    {y : Fin a → ℤ} (hy : StrictAnti y) {δ : GLw a w} (hδ : dcos a w (tdiag ϖ y) δ ≠ 0) :
    HasVals (nrmL a w δ).val.charpoly (nv y) := by
  obtain ⟨m, -, τ, hτ, e⟩ := GlobalTheory.CompanionTheory.ThetaContraction.contr_tw hU w hw ϖ hϖ a y hy δ hδ
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.CompanionTheory.TwSide.exists_diagT_of_mem_TO hτ
  have hdu : m⁻¹ * δ * thL a w m = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) fun i => ϖ ^ y i * v i := by
    rw [e, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (((ϖ ^ y i * v i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y i := by
    intro i
    simp only [Units.val_mul]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ.1,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  rw [← GlobalTheory.CompanionTheory.MatchLinear.charpoly_nrmL_twConj hU a w δ m, hdu, GlobalTheory.CompanionTheory.TwSide.nrmL_diagT hw, GlobalTheory.SmGL.val_diagT,
    Matrix.charpoly_diagonal]
  exact ⟨fun i => _, rfl, fun i => ⟨Units.ne_zero _, GlobalTheory.CompanionTheory.TwSide.ordL_norm_entry hU _ y hord i⟩⟩


open GlobalTheory.CompanionTheory.MatchPow in
theorem mpow_entT {w : Pl E} {n : ℕ} (a : ℕ) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J : Type} [Fintype J]
    (c : J → ℂ) (x : J → Fin n → ℤ) (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (k : ℕ) :
    ∃ (J' : Type) (_ : Fintype J') (c' : J' → ℂ) (x' : J' → Fin n → ℤ),
      (∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) ∧
      ∀ s, mpow w (entT n w ϖ a c x s) (k + 1) = fun y => beta a (n - a) w ^ k * entT n w ϖ a c' x' s y := by
  induction k with
  | zero =>
    refine ⟨J, inferInstance, c, x, hx, fun s => ?_⟩
    funext y
    have := conv_unit (iwahori_pair_le_maximal a (n - a) w) (iwahori_pair_index_ne_zero a (n - a) w)
      (fun k hk z => ((entT_hecke n w ϖ a c x s).2 k hk z).2) y
    rw [pow_zero, one_mul]
    exact this
  | succ k ih =>
    obtain ⟨J', _, c', x', hx', e⟩ := ih
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => x p.1 + x' p.2, fun p => ⟨?_, ?_⟩, fun s => ?_⟩
    · exact fun i j hij => add_lt_add ((hx p.1).1 hij) ((hx' p.2).1 hij)
    · rw [lOf_add]
      exact cone_add (hx p.1).2 (hx' p.2).2
    · show mconv _ (mpow w _ (k + 1)) = _
      rw [e, mconv_entT GlobalTheory.CompanionTheory.DcosProduct.dcosMul n ϖ hϖ a c x c' x' hx hx', pow_succ]

theorem regPowT : RegPowT := by
  intro E _ _ _ hU n d _ hm a ha m w hT y hy
  obtain ⟨hw, -, hϖ, hc⟩ := hm.T w hT
  rw [GlobalTheory.CompanionTheory.MatchLMB2.trace_test_function_eq d ha hT m] at hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  obtain ⟨J', _, c', x', hx', e⟩ := mpow_entT a hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w)
    (fun j => hc j.1 j.2) m
  rw [GlobalTheory.CompanionTheory.MatchLMPlaces.qT_eq d s, GlobalTheory.CompanionTheory.MatchLMPlaces.mpow_scale, e s] at hs
  have h1 : entT n w (d.ϖ w) a c' x' s y ≠ 0 := fun h => hs (by simp [h])
  by_cases hA : MT.admitted n a s
  swap
  · exact absurd (dif_neg hA) h1
  unfold entT at h1
  rw [dite_eq_left hA] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hd2 : dcos (n - a) w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.2)) y.2 ≠ 0 := right_ne_zero_of_mul hj
  have hd1 : dcos a w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.1)) y.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hj)
  obtain ⟨u₁, hQ₁, hu₁⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.1) hd1
  obtain ⟨u₂, hQ₂, hu₂⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.2) hd2
  rw [hQ₁, hQ₂]
  exact GlobalTheory.CompanionTheory.SymmetricIndexRegularity.localization_quotient_separated_dvd (fun z => ordL z) (hx' j).1 _ _ hA.2.2.2.1 hA.2.2.2.2 (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ s)
    (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ sᶜ) (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_disj n _ _ s (by have := hA.2.2.1; omega)) u₁ u₂
    (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.RegPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorusStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_power_torus : PositivityTheory.Rg.BcB.F.MLM.RegPowT := by
  first | exact @GlobalTheory.CompanionTheory.RegPow.regPowT | exact GlobalTheory.CompanionTheory.RegPow.regPowT | (intros; apply GlobalTheory.CompanionTheory.RegPow.regPowT <;> assumption)
end

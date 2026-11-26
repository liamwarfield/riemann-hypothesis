module

public import Formalism.TruncatedSeriesCounting.StatementX
public import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
public import Formalism.WindowSums.PowerSeriesRelationList
public import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt

@[expose] public section

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColTwoStep
noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

private lemma comap_subtype_span_sup_eq_span_range_sup {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (Z J : Submodule O M) (s : Finset M) (hs : ∀ x ∈ s, x ∈ Z) :
    (Submodule.span O (s : Set M) ⊔ J).comap Z.subtype =
      Submodule.span O (Set.range fun x : s => (⟨x, hs x x.2⟩ : Z)) ⊔ J.comap Z.subtype := by
  apply Submodule.map_injective_of_injective Z.injective_subtype
  have hle : Submodule.span O (s : Set M) ≤ Z := Submodule.span_le.2 fun x hx => hs x hx
  have hr : Set.range (⇑Z.subtype ∘ fun x : s => (⟨x, hs x x.2⟩ : Z)) = (s : Set M) := by
    ext y
    simp
  rw [Submodule.map_sup, Submodule.map_span, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    ← Set.range_comp, hr, inf_comm Z, sup_inf_assoc_of_le J hle, inf_comm J Z]

theorem length_quotient_le_of_two_step : ColTwoStep := by
  unfold ColTwoStep
  intro O M _ _ _ ℓ g g₀ e e' Z I s s₀ hIZ hs hs₀ hs₀Z hspan hZ hI
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => by
    rw [← hspan]
    exact Submodule.mem_sup_left (Submodule.subset_span hx)
  have hs₀Z' : ∀ x ∈ s₀, x ∈ Z := fun x hx => hs₀Z hx
  have hIT : I.comap Z.subtype ≤ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    Submodule.comap_mono le_sup_right
  let N := ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ
  have hsplit : Module.length O (Z ⧸ I.comap Z.subtype) =
      Module.length O N + Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) :=
    Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hQN : Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) =
      Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) :=
    (Submodule.quotientQuotientEquivQuotient _ _ hIT).length_eq
  let q : s₀ → Z ⧸ I.comap Z.subtype := fun x => (I.comap Z.subtype).mkQ ⟨x, hs₀Z' x x.2⟩
  have hNq : N = Submodule.span O (Set.range q) := by
    show ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ = _
    rw [comap_subtype_span_sup_eq_span_range_sup Z I s₀ hs₀Z', Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
      Submodule.map_span, ← Set.range_comp]
    rfl
  let v : s₀ → N := fun x => ⟨q x, by rw [hNq]; exact Submodule.subset_span ⟨x, rfl⟩⟩
  have hv_top : Submodule.span O (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hNq.symm
  have hv_kill : ∀ x, ((ℓ : O) ^ e') • v x = 0 := by
    intro x
    apply Subtype.ext
    show ((ℓ : O) ^ e') • q x = 0
    simp only [q, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e') • (x : M) ∈ I
    have h := hI x (Submodule.subset_span x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hN : Module.length O N ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span v ((ℓ : O) ^ e') hv_top hv_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e'
    calc Module.length O N ≤ (Fintype.card s₀ : ℕ∞) *
          Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e'}) := h1
      _ ≤ (g₀ : ℕ∞) * ((e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs₀) h2
      _ = _ := by ring
  let w : s → Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    fun x => ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⟨x, hsZ x x.2⟩
  have hw_top : Submodule.span O (Set.range w) = ⊤ := by
    have htop : (⊤ : Submodule O Z) = Submodule.span O (Set.range fun x : s => (⟨x, hsZ x x.2⟩ : Z)) ⊔
        I.comap Z.subtype := by
      rw [← comap_subtype_span_sup_eq_span_range_sup Z I s hsZ, hspan, Submodule.comap_subtype_self]
    have hmt : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⊤ = ⊤ := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    have hbot : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ
        (I.comap Z.subtype) = ⊥ :=
      le_bot_iff.1 ((Submodule.map_mono hIT).trans (Submodule.mkQ_map_self _).le)
    rw [← hmt, htop, Submodule.map_sup, hbot, sup_bot_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  have hw_kill : ∀ x, ((ℓ : O) ^ e) • w x = 0 := by
    intro x
    simp only [w, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e) • (x : M) ∈ Submodule.span O (s₀ : Set M) ⊔ I
    have h := hZ x (hsZ x x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hZT : Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) ≤
      (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span w ((ℓ : O) ^ e) hw_top hw_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e
    calc _ ≤ (Fintype.card s : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e}) := h1
      _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs) h2
      _ = _ := by ring
  rw [hsplit, hQN]
  calc _ ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add hN hZT
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ArcExp
namespace Formalism.TruncatedSeriesCounting.X

theorem arc_exponential_identity : ArcExp := by
  intro r σ κ G j' ell hr hσ hκ hG hj
  have hj' : (j' : ℝ) ≤ ell := by exact_mod_cast hj
  have hjG : (j' : ℝ) * G ≤ ell * G := mul_le_mul_of_nonneg_right hj' hG
  have hell : 0 ≤ (ell : ℝ) * G := mul_nonneg (Nat.cast_nonneg _) hG
  rcases le_total (r + κ) (2 * σ + 2 * j' * G + 1) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end Formalism.TruncatedSeriesCounting.X
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.AprimeArith
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma log_nat_le (h : ℕ) : Real.log h ≤ (h : ℝ) / 1000 + 998 := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · have hx : (0 : ℝ) < h := by exact_mod_cast hpos
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < h / 1000 by positivity)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1000 by norm_num)
    rw [Real.log_div hx.ne' (by norm_num)] at h1
    linarith

private lemma mpar_le (ℓ g h : ℕ) (hℓ : 11 ≤ ℓ) :
    (Mpar ℓ g h : ℝ) ≤ ((h:ℝ) + 2 * g) / 10 + 1 := by
  have hk : (10 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ ℓ - 1)
  have h1 : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h + 2 * g : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) := Nat.cast_div_le
  have h2 : ((h + 2 * g : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) ≤ ((h + 2 * g : ℕ) : ℝ) / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hk
  have h3 := h1.trans h2
  rw [Mpar, Nat.cast_add, Nat.cast_one]
  push_cast at h3 ⊢
  linarith

private lemma sig_lt (ℓ g h j : ℕ) (hℓ : 11 ≤ ℓ) :
    (sigE ℓ g h j : ℝ) < 11 / 100 * (3 * (g:ℝ) + ((h:ℝ) + 2 * g) / 10 + 1) + 2 := by
  unfold sigE
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hM := mpar_le ℓ g h hℓ
  have hM0 : (0 : ℝ) ≤ Mpar ℓ g h := Nat.cast_nonneg _
  have hpow : (1 : ℝ) ≤ (ℓ : ℝ) ^ (j - 1) := one_le_pow₀ (by linarith)
  have hq : (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ Mpar ℓ g h := div_le_self hM0 hpow
  have hfrac : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 11 / 100 := by
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (by linarith : (0 : ℝ) ≤ 11 * ℓ - 1)]
  set A := 3 * (g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hx0 : 0 ≤ A * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc := Nat.ceil_lt_add_one hx0
  have hAl : A * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ A * (11 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hfrac hA0
  have hA : A ≤ 3 * g + ((h : ℝ) + 2 * g) / 10 + 1 := by rw [hAdef]; linarith
  linarith

private lemma rr_le (ℓ G h j : ℕ) (rr : ℝ) (hℓ : 11 ≤ ℓ) (hj : 1 ≤ j)
    (hrr : rr ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1)) :
    rr ≤ 20 * ((G : ℝ) / 11 + (h : ℝ) / 100 + ((h : ℝ) / 1000 + 998) + 1) := by
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : (G : ℝ) / ℓ ≤ G / 11 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl
  have hp : (100 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have h10 : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
    calc (100 : ℝ) = 10 ^ 2 := by norm_num
      _ ≤ ((ℓ : ℝ) - 1) ^ 2 := by gcongr
      _ ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ h / 100 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
  have hlog0 : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hlogl : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h3 : Real.logb ℓ h ≤ Real.log h := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h4 := log_nat_le h
  linarith

theorem exists_constant_exponent_inequalities : AprimeArith := by
  refine ⟨100000, by norm_num, ?_⟩
  intro ℓ hℓ b w S η j ell b₀ b₁ rr hj hC hell hb0 hb0' hb1 hb1' hrr
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hG0 : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := Nat.cast_nonneg _
  have hjG : (0 : ℝ) ≤ (j : ℝ) * ((w + S + η : ℕ) : ℝ) := by positivity
  have hbig : (200000 : ℝ) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b := by nlinarith
  have hbG : w + S + η + 1 < b := by
    have : (((w + S + η + 1 : ℕ)) : ℝ) < b := by push_cast at hbig ⊢; linarith
    exact_mod_cast this
  have hb1r : (b : ℝ) ≤ b₁ := by exact_mod_cast hb1
  have hb0r : (b₀ : ℝ) ≤ b + η := by exact_mod_cast hb0'
  have hηG : (η : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by exact_mod_cast (by omega : η ≤ w + S + η)
  have hlb : (11 : ℝ) * b₁ ≤ ℓ * b₁ := mul_le_mul_of_nonneg_right hl (by positivity)
  refine ⟨by omega, by omega, by linarith, by linarith, ?_⟩
  have hs := sig_lt ℓ (max (w + S + η) 1) (b + η + S) j hℓ
  have hr := rr_le ℓ (w + S + η) (b + η + S) j rr hℓ hj hrr
  have hg : ((max (w + S + η) 1 : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : max (w + S + η) 1 ≤ w + S + η + 1)
  have hg0 : (0 : ℝ) ≤ ((max (w + S + η) 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hellr : (ell : ℝ) ≤ 3 * j + 1 := by exact_mod_cast hell
  have hge : ((max (w + S + η) 1 : ℕ) : ℝ) * ell ≤ (((w + S + η : ℕ) : ℝ) + 1) * (3 * j + 1) :=
    mul_le_mul hg hellr (Nat.cast_nonneg _) (by positivity)
  have hH : ((b + η + S : ℕ) : ℝ) ≤ b + ((w + S + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b + η + S ≤ b + (w + S + η))
  unfold a0E
  nlinarith
end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SaturationCriterion
namespace Formalism.TruncatedSeriesCounting.X

private theorem iter_nzd {A : Type} [CommRing A] (ℓ g : A)
    (h : ∀ a : A, ℓ * a ∈ Ideal.span {g} → a ∈ Ideal.span {g}) :
    ∀ (n : ℕ) (z : A), ℓ ^ n * z ∈ Ideal.span {g} → z ∈ Ideal.span {g} := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    apply ih
    apply h
    have e : ℓ * (ℓ ^ n * z) = ℓ ^ (n + 1) * z := by ring
    rw [e]; exact hz

theorem saturation_criterion : SatA := by
  intro A _ _ ℓ f f' hf' hℓf hℓf' x k ⟨b, hb⟩ ⟨a, ha⟩
  have inj : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A (FractionRing A)
  have h1 : ℓ ^ k * b = f' * (f * a) := by
    apply inj
    rw [map_mul, map_pow, hb, map_mul (algebraMap A (FractionRing A)) f', ha]
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f' hℓf' k b (by
    rw [h1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f')))
  have hf'0 : algebraMap A (FractionRing A) f' ≠ 0 := (map_ne_zero_iff _ inj).mpr hf'
  have hx : x = algebraMap A (FractionRing A) c := by
    apply mul_left_cancel₀ hf'0
    rw [← hb, hc, map_mul]
  have h2 : ℓ ^ k * c = f * a := by
    apply inj
    rw [map_mul, map_pow, ← hx, ha]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f hℓf k c (by
    rw [h2]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
  exact ⟨d, by rw [hx, hd]⟩

end Formalism.TruncatedSeriesCounting.X
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncSig
namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_signature_bound : TruncSig := by
  unfold TruncSig
  intro ℓ hℓ y X M η
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1) := by
    intro T hT
    rw [sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]
    rcases le_total ((ℓ : ℝ) * y - T) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1 := by
    intro T
    have h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
    rw [add_div]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (gen X (Nat.cast_nonneg _)).trans (mono _)
  · have e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M) := by ring
    rw [e]
    have := gen ((η : ℝ) + M) (by positivity)
    have h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1 := by
      rw [add_comm (η : ℝ)]
      have h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
      linarith
    linarith
  · have hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := pow_pos ha 2
    have e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2 := by
      field_simp
    have key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2 := by
      rw [e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
      have hX : (X : ℝ) = X / ℓ * ℓ := (div_mul_cancel₀ _ hlpos.ne').symm
      rcases le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h
      · rw [max_eq_left h]
        have h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X := by
          have h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ := by linarith
          have := mul_le_mul_of_nonneg_right h5 hlpos.le
          linarith
        nlinarith
      · rw [max_eq_right h]
        have hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ := by nlinarith
        nlinarith [mul_nonneg h hs2]
    have h6 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

end Formalism.TruncatedSeriesCounting.X
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncationRemainderBound
namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LengthQuotientLeOfPowSMul
noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

theorem length_quotient_le_of_pow_smul : LengthQuotientLeOfPowSMul := by
  intro O _ _ _ M _ _ _ _ ℓ e e' FFs J h1 h2
  set A := FFs ⊔ Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M) with hA
  have hx : ∀ x ∈ A, ℓ ^ e • x ∈ J := by
    intro x hxA
    obtain ⟨f, hf, m, hm, rfl⟩ := Submodule.mem_sup.1 hxA
    rw [smul_add]
    exact J.add_mem (h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hf))
      (J.smul_mem _ (h2 hm))
  have hS := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.submodule_generator_count O M ℓ e A J hx
  let f : (A ⧸ J.comap A.subtype) →ₗ[O] M ⧸ J := (J.comap A.subtype).mapQ J A.subtype le_rfl
  let g : (M ⧸ J) →ₗ[O] M ⧸ (A ⊔ J) :=
    J.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_right hx)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm
      obtain ⟨a, ha, j, hj, rfl⟩ := Submodule.mem_sup.1 hm
      refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype]
      rw [Submodule.Quotient.eq]
      simpa using J.neg_mem hj
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype, Submodule.Quotient.eq] at hx
      have e1 : m = (a : M) - ((a : M) - m) := by abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left a.2) (Submodule.mem_sup_right hx)
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hq : Module.length O (M ⧸ (A ⊔ J)) ≤ Module.length O (M ⧸ A) := by
    refine Module.length_le_of_surjective (A.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_left hx)) ?_
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  rw [hlen, add_comm]
  exact add_le_add hq hS

end Formalism.TruncatedSeriesCounting.R9
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KapWin
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open Finset

private lemma sum_le_sum_cover {K : ℕ} (W : Fin K → Finset ℤ) (S : Finset ℤ)
    (hS : ∀ i ∈ S, ∃ k, i ∈ W k) (g : ℤ → ℕ) :
    ∑ i ∈ S, g i ≤ ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
  calc ∑ i ∈ S, g i ≤ ∑ i ∈ S, ∑ k, if i ∈ W k then g i else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨k, hk⟩ := hS i hi
        calc g i = (fun k' => if i ∈ W k' then g i else 0) k := by simp [hk]
          _ ≤ ∑ k', if i ∈ W k' then g i else 0 :=
            Finset.single_le_sum (f := fun k' => if i ∈ W k' then g i else 0) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
    _ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]

theorem kappa_window_bound : KapWin := by
  intro ℓ _ hℓ χ hχ ell K D a L JJ hJJ hD
  obtain ⟨hne, hv⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩
  rw [hv]
  set S := JJ.erase 0 with hSdef
  set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (L k : ℤ)) with hWdef
  have hcov : ∀ i ∈ S, ∃ k, i ∈ W k := by
    intro i hi
    have := hJJ (Finset.mem_of_mem_erase hi)
    simpa [Finset.mem_biUnion, hWdef] using this
  have hcard : S.card ≤ ∑ k, L k := by
    have h := sum_le_sum_cover W S hcov (fun _ => 1)
    rw [Finset.card_eq_sum_ones]
    refine h.trans (Finset.sum_le_sum fun k _ => ?_)
    rw [← Finset.card_eq_sum_ones]
    calc (S.filter (fun i => i ∈ W k)).card ≤ (W k).card := by
          apply Finset.card_le_card
          intro i hi
          exact (Finset.mem_filter.mp hi).2
      _ = L k := by simp [hWdef]
  have hsumv : ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤
      ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
    calc ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast sum_le_sum_cover W S hcov (fun i => padicValInt ℓ i)
      _ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine Formalism.WindowSums.arc_WindowSum ℓ (a k) (L k) D _ ?_ ?_ ?_
          · intro i hi
            exact (Finset.mem_filter.mp hi).2
          · intro h0
            have := (Finset.mem_filter.mp h0).1
            simp [hSdef] at this
          · intro i hi
            exact hD i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)
  have hsplit : ∑ i ∈ S, (1 + ell + padicValInt ℓ i) =
      S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [hsplit]
  have hcardR : (S.card : ℝ) ≤ ((∑ k, L k : ℕ) : ℝ) := by exact_mod_cast hcard
  have hmul : (S.card : ℝ) * (1 + ell) ≤ ((∑ k, L k : ℕ) : ℝ) * (1 + ell) :=
    mul_le_mul_of_nonneg_right hcardR (by positivity)
  have hgoal : ((S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i + ell : ℕ) : ℝ) =
      (S.card : ℝ) * (1 + ell) + ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) + ell := by
    push_cast; ring
  rw [hgoal]
  linarith

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ThmEExp
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma sigma_exponent_le_real (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (g h j : ℕ) (hj : 1 ≤ j) :
    (sigE ℓ g h j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hjm : m + 1 - 1 = m := by omega
  unfold sigE
  rw [hjm]
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hA0 : (0 : ℝ) ≤ (h : ℝ) + 2 * g := by positivity
  have hP1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hPq : ((ℓ : ℝ) - 1) ^ m ≤ (ℓ : ℝ) ^ m := pow_le_pow_left₀ hq0.le (by linarith) m
  have hP0 : (0 : ℝ) < (ℓ : ℝ) ^ m := by linarith
  have hM : (Mpar ℓ g h : ℝ) ≤ ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1 := by
    unfold Mpar
    push_cast
    have hc : (((ℓ - 1 : ℕ)) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    rw [hc] at this
    push_cast at this
    linarith
  have hM0 : (0 : ℝ) ≤ (Mpar ℓ g h : ℝ) := by positivity
  have hr : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ hq2]
    nlinarith
  have hr0 : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hX0 : (0 : ℝ) ≤ ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    positivity
  have hceil := Nat.ceil_lt_add_one hX0
  have e1 : ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
      3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) +
        (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
    field_simp
  have t1 : 3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) ≤ 9 / 4 * g := by nlinarith
  have t2 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) + 3 / 4 := by
    have hB : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by positivity
    have s1 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
        (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      gcongr
    have s2 : (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m =
        ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) +
          ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      field_simp
    have s3 : ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) ≤
        3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) hB]
      have k1 : (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m := by
        have : (ℓ : ℝ) ≤ 3 / 2 * ((ℓ : ℝ) - 1) := by linarith
        calc (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) ^ m :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left hPq (by positivity)
      have k2 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hA0 hq2.le)
      have e2 : ((ℓ : ℝ) - 1) ^ (m + 1 + 1) = ((ℓ : ℝ) - 1) ^ m * ((ℓ : ℝ) - 1) ^ 2 := by ring
      rw [e2]
      nlinarith [k2]
    have s4 : ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤ 3 / 4 := by
      rw [div_le_iff₀ hP0]
      nlinarith
    linarith
  rw [e1] at hceil ⊢
  linarith

theorem total_exponent_le_eight_hundred : ExponentBoundOfRankAndKappaBounds := by
  intro ℓ hℓ G g h j ell rr kap hj hG hg hgh hell hrr hkap
  have hσ := sigma_exponent_le_real ℓ hℓ g h j hj
  unfold eE a0E
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hB4 : (4 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (ℓ : ℝ) - 1) (by omega : 2 ≤ j + 1)
    nlinarith
  have hB0 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (j + 1) := by linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGg : (G : ℝ) ≤ g := by exact_mod_cast hG
  have hgh' : (g : ℝ) ≤ h := by exact_mod_cast hgh
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hT : (0 : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) := by positivity
  have hΛ : (0 : ℝ) ≤ Real.logb ℓ h := Real.logb_nonneg (by linarith) hh1
  have hlog2 : Real.logb ℓ (2 * h) = Real.logb ℓ 2 + Real.logb ℓ h :=
    Real.logb_mul (by norm_num) (by positivity)
  have hl2 : Real.logb ℓ 2 ≤ 1 := by
    have := Real.logb_le_logb_of_le (by linarith : (1 : ℝ) < ℓ) (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ ℓ)
    rwa [Real.logb_self_eq_one (by linarith)] at this
  have hGL : (G : ℝ) / ℓ ≤ g / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hgB : (g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ g / 4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hB4
  have h4g : 4 * (g : ℝ) / ((ℓ : ℝ) - 1) ≤ 2 * g := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have eσ : 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) =
      3 / 2 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) + 3 * ((g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) := by
    ring
  rw [eσ] at hσ
  rw [hlog2] at hkap
  have hge : (g : ℝ) ≤ g * ell := by nlinarith
  have hee : (ell : ℝ) ≤ g * ell := by nlinarith
  have h1e : (1 : ℝ) ≤ g * ell := by nlinarith
  nlinarith

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Polynomial

private theorem winDiff (ℓ : ℕ) [Fact ℓ.Prime] (j₀ lo : ℤ) (L D : ℕ) (T : Finset ℤ)
    (hT : ∀ j ∈ T, lo ≤ j₀ - j ∧ j₀ - j < lo + L) (h0 : j₀ ∉ T)
    (hD : ∀ j ∈ T, |j₀ - j| ≤ (D : ℤ)) :
    ((∑ j ∈ T, padicValInt ℓ (j₀ - j) : ℕ) : ℝ) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb (ℓ : ℝ) (D : ℝ) := by
  have hinj : Set.InjOn (fun j : ℤ => j₀ - j) (T : Set ℤ) := by
    intro x _ y _ h
    simp only at h
    omega
  have hre : ∑ j ∈ T, padicValInt ℓ (j₀ - j) =
      ∑ i ∈ T.image (fun j : ℤ => j₀ - j), padicValInt ℓ i :=
    (Finset.sum_image hinj).symm
  rw [hre]
  apply Formalism.WindowSums.arc_WindowSum ℓ lo L D
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have := hT j hj
    rw [Finset.mem_Ico]
    omega
  · intro hi
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.1 hi
    have : j = j₀ := by omega
    exact h0 (this ▸ hj)
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact hD j hj

theorem g_ideal_valuation_statement : LemmaGIdeal := by
  intro ℓ _ R _ _ c hc h η S b a S₂ hb hbS hS₂
  have hℓ2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  set S₁ := Finset.Icc ((b : ℤ) - a + 1) (b : ℤ) with hS₁def
  have m2 : ∀ r ∈ S₂, ((b : ℤ) + 1 ≤ r ∧ r ≤ b + S + a) ∨ (1 - (η : ℤ) ≤ r ∧ r ≤ η + a) := by
    intro r hr
    simpa only [Finset.mem_union, Finset.mem_Icc] using hS₂ hr
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    rw [hS₁def, Finset.mem_Icc] at hr1
    have := m2 r hr2
    omega
  have hlag := Formalism.LIFT.lift_LagrangeIdealInt ℓ R S₁ S₂ c hdisj
    (fun x _ y _ hxy => hc x y hxy)
  refine ⟨S₁.sup fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j), ?_, hlag⟩

  have hH1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    have : 1 ≤ h + η := by omega
    exact_mod_cast this
  have hlog : Real.logb (ℓ : ℝ) ((h + η : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_le_logb_of_le (b := (ℓ : ℝ)) (by linarith) (by linarith)
      (show ((h + η : ℕ) : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    have := Real.logb_nonneg (b := (ℓ : ℝ)) (by linarith)
      (show (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) by linarith)
    linarith
  have hden : 0 < (ℓ : ℝ) - 1 := by linarith
  have key : ∀ j₀ ∈ S₁, ((((∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j) : ℕ)) : ℝ) ≤
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) + 3 * lam ℓ (h + η) := by
    intro j₀ hj₀
    rw [hS₁def, Finset.mem_Icc] at hj₀
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) + 1 ≤ j)]
    push_cast
    have w1 := winDiff ℓ j₀ (j₀ - b) a (h + η) (S₁.erase j₀)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        omega)
      (by simp)
      (by
        intro j hj
        rw [Finset.mem_erase, hS₁def, Finset.mem_Icc] at hj
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w2 := winDiff ℓ j₀ (j₀ - b - S - a) (S + a) (h + η)
      (S₂.filter (fun j => (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    have w3 := winDiff ℓ j₀ (j₀ - η - a) (2 * η + a) (h + η)
      (S₂.filter (fun j => ¬ (b : ℤ) + 1 ≤ j))
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        push_cast
        omega)
      (by
        rw [Finset.mem_filter]
        intro hh
        have := m2 j₀ hh.1
        omega)
      (by
        intro j hj
        rw [Finset.mem_filter] at hj
        have := m2 j hj.1
        rw [abs_le]
        push_cast
        constructor <;> omega)
    push_cast at w1 w2 w3
    have hsum : (a : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) +
        (2 * (η : ℝ) + (a : ℝ)) / ((ℓ : ℝ) - 1) =
        (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by ring
    push_cast at hlog
    linarith
  rcases S₁.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty]
    simp only [Nat.bot_eq_zero, Nat.cast_zero]
    have : 0 ≤ (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by positivity
    linarith
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup S₁ hne
      (fun j₀ => (∑ j ∈ S₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ S₁.erase j₀, padicValInt ℓ (j₀ - j))
    rw [hjeq]
    exact key j hj

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

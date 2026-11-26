module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfTNatCastUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.IsAdicCompleteMax
noncomputable section

namespace Formalism.MainNotions.N.Ln34.AdicCompletionMax

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_eq_max_pow {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.span {p} = IsLocalRing.maximalIdeal O ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (mt Ideal.span_singleton_eq_bot.mp hp0) hϖ
  refine ⟨n, Nat.one_le_iff_ne_zero.mpr ?_, ?_⟩
  · rintro rfl
    rw [pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at hn
    exact absurd hn ((IsLocalRing.mem_maximalIdeal _).1 hpm)
  · rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

private theorem isAdicComplete_of_isAdicComplete_pow {J : Ideal O} {k : ℕ} (hk : 1 ≤ k)
    (h : IsAdicComplete (J ^ k) O) : IsAdicComplete J O := by
  have key : ∀ n : ℕ, (J ^ k) ^ n = J ^ (k * n) := fun n => (pow_mul J k n).symm
  have hkn : ∀ n : ℕ, n ≤ k * n := fun n => by simpa using Nat.mul_le_mul hk (le_refl n)
  have hle : ∀ {a b : ℕ}, a ≤ b → J ^ b • (⊤ : Submodule O O) ≤ J ^ a • ⊤ :=
    fun hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [key]
    exact hx (k * n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => f (k * n))
      (fun {a b} hab => by
        rw [key]
        exact hf (Nat.mul_le_mul (le_refl k) hab))
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (k * n) [SMOD (J ^ n • ⊤ : Submodule O O)] := hf (hkn n)
    have h2 : f (k * n) ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := by
      have h3 := hL n
      rw [key] at h3
      exact SModEq.mono (hle (hkn n)) h3
    exact h1.trans h2

theorem isAdicComplete_max {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O)
    [h : IsAdicComplete (Ideal.span {p}) O] : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  obtain ⟨k, hk, hkeq⟩ := span_eq_max_pow hp0 hpm
  rw [hkeq] at h
  exact isAdicComplete_of_isAdicComplete_pow hk h

end Formalism.MainNotions.N.Ln34.AdicCompletionMax
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem u2ringPf_zetaO {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) {ζ : ↥LL.1}
    (hζ : IsPrimitiveRoot ζ l) : ∃ z : ↥(OL LL), IsPrimitiveRoot z l := by
  have hv : 0 ≤ P.v LL ζ := by
    have h1 : P.v LL (ζ ^ l) = 0 := by rw [hζ.pow_eq_one, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    cases hq : P.v LL ζ using WithTop.recTopCoe with
    | top =>
      exfalso
      rw [hq] at h1
      obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Fact.out : l.Prime).pos; omega⟩
      rw [hk, succ_nsmul, WithTop.add_top] at h1
      exact WithTop.top_ne_zero h1
    | coe q =>
      rw [hq] at h1
      have h2 : ((l • q : ℚ) : WithTop ℚ) = 0 := by rw [WithTop.coe_nsmul]; exact h1
      have h3 : l • q = 0 := by exact_mod_cast h2
      rw [nsmul_eq_mul, mul_eq_zero] at h3
      rcases h3 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : l = 0) (Fact.out : l.Prime).ne_zero
      · rw [h3]; exact le_refl _
  refine ⟨⟨ζ, (P.v_O LL ζ).1 hv⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) hζ Subtype.val_injective

theorem u2ring_pf : SecondRingHypothesis := by
  intro D HW F Cm CA CB CK _ l _ hl K LL hG π' E hR h' hh' c
  have hlp : l.Prime := Fact.out
  have : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) :=
    (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (by rw [hpl]; exact hlp.ne_zero)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := AdicCompletionMax.isAdicComplete_max hp0 hpm
  have hs : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hd := DvdPf.dvdCondition l hl K LL hG
  have hes : eK K * sK l K = ((D.loc l).PD K).p - 1 := by rw [hpl]; exact Nat.mul_div_cancel' hd
  obtain ⟨ζL, hζL⟩ := Formalism.MainNotions.N.zeta_of_good (D.loc l) hG
  obtain ⟨ζ, hζ⟩ := u2ringPf_zetaO (D.loc l) LL hζL
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hpl]; exact hζ
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  obtain ⟨a, r, ha, hrm, hE, hnr⟩ := u2ringPfT_split ((HW l).W K 1 LL hG) hR hs hes hpm c ζ hζ' hp2 hι hRv
  exact u2ringPfD_main ((HW l).W K 1 LL hG) hR hs (((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2) le_rfl c a ha r
    hrm hE hnr h' hh'

end Formalism.MainNotions.N.Ln34

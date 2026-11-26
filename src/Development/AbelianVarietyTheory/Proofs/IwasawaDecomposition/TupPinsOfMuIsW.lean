module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.Mem.HD.RamBoth

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simpa using h

theorem exists_intCast_cong {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (z : w.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ k : ℤ, Valued.v (algebraMap E (w.adicCompletion E) (k : E) - z) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨b, hb⟩ := GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong w z hz
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Fact (Nat.card (𝓞 E ⧸ w.asIdeal)).Prime := ⟨hc ▸ hp⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal)) with h | h
    · exfalso
      have : (1 : 𝓞 E ⧸ w.asIdeal) ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := AddSubgroup.mem_zmultiples 1
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this
    · exact h
  obtain ⟨k, hk⟩ : Ideal.Quotient.mk w.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := htop ▸ AddSubgroup.mem_top _
  have hk' : ((k : 𝓞 E ⧸ w.asIdeal)) = Ideal.Quotient.mk w.asIdeal b := by simpa using hk
  have hmem : b - (k : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hk', map_intCast, sub_self]
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((b : E) - (k : E))) ≤ WithZero.exp (-1 : ℤ) := by
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval]
    refine le_exp_neg_one_of_lt_one ?_
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (b - (k : 𝓞 E))).2 hmem
    simpa using this
  have hb' : Valued.v (algebraMap E (w.adicCompletion E) (b : E) - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hb
  refine ⟨k, ?_⟩
  have := Valuation.map_sub_le _ (hb'.trans (by simp)) h1
  rw [map_sub (algebraMap E (w.adicCompletion E)), sub_sub_sub_cancel_left] at this
  exact this

theorem mem_aboveF_iff (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {R : HeightOneSpectrum (𝓞 D.host.E)} :
    R ∈ aboveF (L := D.host.E) D.host.F v ↔ R.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl


open Classical in
theorem aboveF_eq_pair (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w P : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (hne : w ≠ P) :
    aboveF (L := D.host.E) D.host.F v = {w, P} := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 D.host.F) (𝓞 D.host.E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 D.host.E) D.host.F D.host.E v.ne_bot
  rw [D.sp.cm.deg2] at h1
  have h2 : (aboveF (L := D.host.E) D.host.F v).card ≤ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 D.host.E)).card := by
    refine Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (fun R hR => ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rw [Finset.mem_coe, mem_aboveF_iff] at hR
    rw [IsDedekindDomain.coe_primesOverFinset v.ne_bot]
    exact ⟨R.isPrime, ⟨hR ▸ rfl⟩⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; omega

theorem unrAt_of_pair {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    [DecidableEq (HeightOneSpectrum (𝓞 E))] (χ : HChar E) {v : HeightOneSpectrum (𝓞 F)} {w P : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (hP : P.under (𝓞 F) = v) (hne : w ≠ P) (hS : aboveF (L := E) F v = {w, P})
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hF : χ.TrivOn F) (ht : χ.TameAt w) (hun : χ.UnrAt P) : χ.UnrAt w := by
  intro u hu
  have hu1 : Valued.v (u : w.adicCompletion E) = 1 := hu
  obtain ⟨k, hk⟩ := exists_intCast_cong w hp u hu1.le
  have hval : ∀ (R : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = 1 ↔
      (k : 𝓞 E) ∉ R.asIdeal := fun R => by
    have h1 : Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = R.valuation E (k : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (k : E)
    have h2 : R.valuation E (k : E) = R.intValuation (k : 𝓞 E) := by
      rw [← map_intCast (algebraMap (𝓞 E) E) k]
      exact HeightOneSpectrum.valuation_of_algebraMap (K := E) R (k : 𝓞 E)
    rw [h1, h2, HeightOneSpectrum.intValuation_eq_one_iff]
  have hmem : ∀ (R : HeightOneSpectrum (𝓞 E)), R.under (𝓞 F) = v → ((k : 𝓞 E) ∈ R.asIdeal ↔ (k : 𝓞 F) ∈ v.asIdeal) :=
    fun R hR => by
      rw [← hR, ← map_intCast (algebraMap (𝓞 F) (𝓞 E)) k]
      exact Iff.rfl
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (algebraMap E (w.adicCompletion E) (k : E)) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ hk.trans_lt hlt), hu1]
  have hkw := (hval w).1 h5
  have hkP : (k : 𝓞 E) ∉ P.asIdeal := fun h => hkw ((hmem w hw).2 ((hmem P hP).1 h))
  have hk0 : (k : F) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    exact hkw (by simp [this])
  have hco : ∀ R : HeightOneSpectrum (𝓞 E), ((atFin R (upF F (Units.mk0 (k : F) hk0)) : (R.adicCompletion E)ˣ) :
      R.adicCompletion E) = algebraMap E (R.adicCompletion E) (k : E) := fun R => by
    rw [← map_intCast (algebraMap F E) k]
    rfl
  have h7 := hF.1 v (Units.mk0 (k : F) hk0)
  unfold HChar.resFin at h7
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h7
  have h6 : χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 := hun _ (by
    unfold IsUnitAt
    rw [hco, (hval P).2 hkP])
  change χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0))) * χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 at h7
  rw [h6, mul_one] at h7
  have h8 : χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0)) / u) = 1 := by
    refine ht _ ?_ ?_
    · unfold IsUnitAt
      rw [Units.val_div_eq_div_val, map_div₀, hco, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, hco]
      exact hk
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

theorem ram_both : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp →
    ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v →
    ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  classical
  intro D C nch Tp hT μ v w P hw hP hr hun
  by_cases hne : w = P
  · exact hr (hne ▸ hun)
  · exact hr (unrAt_of_pair _ ((mem_aboveF_iff D).1 hw) ((mem_aboveF_iff D).1 hP) hne
      (by convert aboveF_eq_pair D hw hP hne) (hT.ram μ w hr).2.1 (Tp.xi_triv μ) (Tp.xi_tame μ w) hun)

end GlobalTheory.Mem.HD.RamBoth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlaceStatement
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  first | exact @GlobalTheory.Mem.HD.RamBoth.ram_both | exact GlobalTheory.Mem.HD.RamBoth.ram_both | (intros; apply GlobalTheory.Mem.HD.RamBoth.ram_both <;> assumption)
end
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem absNorm_eq_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
  rw [mem_aboveF_iff] at hP
  subst hP
  have hd : Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.card_dvd_of_injective
      (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) le_rfl).toAddMonoidHom
      Ideal.quotientMap_injective
  exact ((Nat.dvd_prime h).1 hd).resolve_left fun h1 =>
    (P.under (𝓞 D.host.F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m)
    (h' : ¬ x ≤ WithZero.exp (m - 1)) : x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem degreeOne_of_prime_absNorm_not_mem_sq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (h1 : (Ideal.absNorm P.asIdeal).Prime) (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∉ P.asIdeal ^ 2) : Deg1 P := by
  refine ⟨h1, ?_⟩
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qP P : ℕ) : P.adicCompletion L) =
      algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L)) := by
    simp [qP]
  have hv : ∀ y : L, Valued.v (algebraMap L (P.adicCompletion L) y) = P.valuation L y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P y
  rw [e, hv, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hmem)
  have a2 : ¬ P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem _ 2).1 h)
  refine eq_exp_of_le (by simpa using a1) fun h => a2 ?_
  convert h using 2
  norm_num

theorem ramTransfer : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place

theorem finite_inQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | Tp.InQ' μ v}.Finite := by
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).image fun w => w.under (𝓞 D.host.F)).subset ?_
  rintro v ⟨w, hw, hr⟩
  exact ⟨w, hr, mem_aboveF_iff.1 hw⟩

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

theorem qpSet_g (Tp : TupTied D C nch) (hp : TupPins Tp) (μ : D.what₂.Tup) (i : Fin 2) :
    D.host.g i ∉ qpSet Tp μ := fun h => by
  obtain ⟨-, w, hw, hr⟩ := (mem_qpSet Tp _ _).1 h
  exact (hp.ram μ w hr).2.2.2 i hw

theorem one_lt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)


include hp hPv in
theorem ram_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ¬ (Tp.xi μ).UnrAt (Pv v.1) := by
  obtain ⟨w, hw, hr⟩ := v.2
  exact ramTransfer D C nch Tp hp μ v.1 w (Pv v.1) hw (hPv v.1) hr

include hp hPv in
theorem chosenPrimeAbove_ramifiedPlace_degreeOne (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : Deg1 (Pv v.1) :=
  degreeOne_of_prime_absNorm_not_mem_sq _ (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1 (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.1

include hp hPv in
theorem offg_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ∀ k, ¬ OverP D.host (D.host.g k) (Pv v.1) :=
  (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.2

include hp hPv in
theorem absNorm_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    Ideal.absNorm v.1.asIdeal = qP (Pv v.1) :=
  absNorm_eq_of_mem (hPv v.1) (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1

theorem one_le_letterBlockLength : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega


include hp hPv in
theorem stepEx (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) (j : ℕ) :
    (∃ n, TypeDimAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j n) ∧
      ∃ z, StepAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j z :=
  GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _ (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v))
    (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v)) D.R.r D.R.t j one_le_letterBlockLength

def zq (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (stepEx Tp hp Pv hPv μ v j).2.choose

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}
variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

def reQ (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    Qp_g := fun μ _ i => qpSet_g Tp hp μ i
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    finQ := fun μ => by
      haveI : Finite {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := (finite_inQ Tp μ).to_subtype
      exact Fintype.ofFinite _
    qv := fun _ v => Ideal.absNorm v.1.asIdeal
    qv_gt := fun _ v => one_lt_absNorm v.1
    qv_char := fun μ _ v => by
      obtain ⟨w, hw, hr⟩ := v.2
      have hpr := (hp.ram μ w hr).2.1
      refine ⟨Ideal.absNorm v.1.asIdeal, (mem_qpSet Tp μ _).2 ⟨?_, w, ?_, hr⟩, ?_, rfl⟩
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
      · rw [absNorm_eq_of_mem hw hpr]; exact Ideal.absNorm_mem _
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
    nu := fun _ v i => ((nuP C (Pv v.1) i (piP (Pv v.1)) : ℂˣ) : ℂ)
    nu_ne := fun _ _ _ => Units.ne_zero _
    nu_abs := fun μ v i => (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) i).unitary _
    ZQ := zq Tp hp Pv hPv
    quotientLocalValueFirst := fun _ v => (zVal1 (qP (Pv v.1)) D.R.r D.R.t : ℂ)
    typeDim := fun μ v j => (stepEx Tp hp Pv hPv μ v j).1.choose }

def reducedDivisorCharacter (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv hPv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

theorem reLoc (Z₀ : DivX D) : QLocTiedC (reducedDivisorCharacter Tp hp Pv hPv Z₀) Pv := by
  refine ⟨fun μ v => hPv _, ?_⟩
  refine
    { qv_eq := fun μ v => absNorm_Pv Tp hp Pv hPv μ v
      deg1 := fun μ v => chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v
      ram := fun μ v => ram_Pv Tp hp Pv hPv μ v
      off_g := fun μ v => offg_Pv Tp hp Pv hPv μ v
      nu_eq := fun μ v i => ?_
      typeDim_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).1.choose_spec
      ZQ_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).2.choose_spec
      quotientLocalValueFirst_eq := fun μ v j _ _ => GlobalTheory.T.singleBlock_doublingIntegral_value D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _
        (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v)) (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) j) D.R.r D.R.t one_le_letterBlockLength }
  show ((nuP C (Pv v.1) (i.1 + 1) (piP (Pv v.1)) : ℂˣ) : ℂ) = _
  rw [nuP_succ]
  rfl

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.HD.ReQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.PinPlace

theorem mem_mul_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (y : K) :
    (∃ a : R, y = algebraMap R K (ϖ * a)) ↔ y = 0 ∨ y⁻¹ ∉ (algebraMap R K).range := by
  have hinj := IsFractionRing.injective R K
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, b, hb⟩ := hc
    have h1 : ϖ * a * b = 1 := hinj (by rw [map_mul, hb, mul_inv_cancel₀ h0, map_one])
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a * b) (by rw [← mul_assoc, h1]))
  · rintro (rfl | h)
    · exact ⟨0, by simp⟩
    · rcases ValuationRing.isInteger_or_isInteger R y with ⟨b, rfl⟩ | hb
      · have hb : ¬ IsUnit b := by
          rintro ⟨u, rfl⟩
          refine h ⟨(u⁻¹ : Rˣ), ?_⟩
          exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        have hm : b ∈ IsLocalRing.maximalIdeal R := hb
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨a, rfl⟩ := hm
        exact ⟨a, rfl⟩
      · exact absurd hb h

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem mem_range_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    y ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ↔
      la.1.valuation D.what₂.LL z ≤ 1 := by
  obtain ⟨W, h1, h2⟩ := h
  rw [← h2, hyz, h1]

theorem mem_pW_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    (∃ a : WittVector p (AlgebraicClosure (ZMod p)),
        y = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
      la.1.valuation D.what₂.LL z < 1 := by
  rw [mem_mul_iff (WittVector.irreducible p) y,
    mem_range_iff h (y := y⁻¹) (z := z⁻¹) (by rw [map_inv₀, map_inv₀, hyz])]
  have h0 : y = 0 ↔ z = 0 := by
    rw [← map_eq_zero_iff jc jc.injective, hyz, map_eq_zero_iff _ D.what₂.embLL.injective]
  rw [h0, map_inv₀, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hv : 0 < la.1.valuation D.what₂.LL z := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz)
    rw [one_lt_inv₀ hv]
    simp [hz]

theorem pinned_reads_place : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) →
    ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
      (jC p la).comp τ = D.what₂.embLL.comp e → ∀ x : 𝓞 D.host.E,
        τ x ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ∧
        ((∃ a : WittVector p (AlgebraicClosure (ZMod p)),
            τ x = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
          la.1.valuation D.what₂.LL (e x) < 1) ∧
        (la.1.valuation D.what₂.LL (e x) < 1 ↔ RingOfIntegers.mapRingHom e x ∈ la.1.asIdeal) := by
  intro D jC h p _ la τ e hτ x
  have hx : jC p la (τ x) = D.what₂.embLL (e x) := RingHom.congr_fun hτ (x : D.host.E)
  have he : e x = algebraMap (𝓞 D.what₂.LL) D.what₂.LL (RingOfIntegers.mapRingHom e x) := rfl
  refine ⟨(mem_range_iff (h p la) hx).2 ?_, mem_pW_iff (h p la) hx, ?_⟩
  · rw [he]; exact la.1.valuation_le_one _
  · rw [he]; exact la.1.valuation_lt_one_iff_mem _

theorem coeff_zero_eq_zero_iff {k : Type} [Field k] [CharP k p] [PerfectRing k p] (b : WittVector p k) :
    b.coeff 0 = 0 ↔ ∃ a : WittVector p k, b = p * a := by
  constructor
  · intro h0
    have hb : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      have h1 := congrArg (fun w : WittVector p k => w.coeff 0) u.mul_inv
      simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hm : b ∈ IsLocalRing.maximalIdeal (WittVector p k) := hb
    rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [WittVector.mul_coeff_zero]
    have : ((p : WittVector p k)).coeff 0 = 0 := by simp
    rw [this, zero_mul]

theorem pinned_tiedFor : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) → Formalism.L2.Geo.ComplexEmbeddingsCompatible jC := by
  intro D jC h p _ la τ e hτ x
  obtain ⟨-, h2, -⟩ := pinned_reads_place D jC h p la τ e hτ x
  rw [← h2]
  constructor
  · rintro ⟨b, hb, h0⟩
    obtain ⟨a, rfl⟩ := (coeff_zero_eq_zero_iff b).1 h0
    exact ⟨a, hb.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨p * a, ha.symm, (coeff_zero_eq_zero_iff _).2 ⟨a, rfl⟩⟩

end GlobalTheory.ShFam.PinPlace
end
end

noncomputable section

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft NumberField

namespace GlobalTheory.GeoModel

variable (D : D7)

def fracO : IntermediateField ℚ D.what₂.LL := IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

theorem otoLL_mem (y : D.what₂.O) : D.what₂.OtoLL y ∈ fracO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

variable {D} {T : HostTied D} {C : CharFrame D}

def toInt (h : OTied D T C) : D.what₂.O →+* 𝓞 (fracO D) where
  toFun y := ⟨⟨D.what₂.OtoLL y, otoLL_mem D y⟩, by
    have hq : IsIntegral ℤ (T.jLL (D.what₂.OtoLL y)) := ((h.range _).1 ⟨y, rfl⟩).2
    let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
    have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
    exact (isIntegral_algHom_iff f hf).1 hq⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; exact map_mul D.what₂.OtoLL a b
  map_zero' := by ext; simp
  map_add' a b := by ext; exact map_add D.what₂.OtoLL a b

theorem toInt_val (h : OTied D T C) (y : D.what₂.O) : ((toInt h y : fracO D) : D.what₂.LL) = D.what₂.OtoLL y := rfl

theorem toInt_bijective (h : OTied D T C) : Function.Bijective (toInt h) := by
  refine ⟨fun a b hab => h.inj ?_, fun z => ?_⟩
  · have := congrArg (fun w : 𝓞 (fracO D) => ((w : fracO D) : D.what₂.LL)) hab
    simpa [toInt_val] using this
  · set x : D.what₂.LL := ((z : fracO D) : D.what₂.LL) with hx
    have hint : IsIntegral ℤ (T.jLL x) := by
      let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
      have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
      exact (isIntegral_algHom_iff f hf).2 z.2
    have hmem : T.jLL x ∈ KsQ D T C h.pieces := by
      have hx' : x ∈ fracO D := (z : fracO D).2
      have h1 : T.jLL x ∈ (fracO D).map T.jLL.toRatAlgHom := ⟨x, hx', rfl⟩
      rw [fracO, IntermediateField.adjoin_map] at h1
      refine (IntermediateField.adjoin_le_iff.2 ?_) h1
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ((h.range _).1 ⟨y, rfl⟩).1
    obtain ⟨y, hy⟩ := (h.range _).2 ⟨hmem, hint⟩
    refine ⟨y, ?_⟩
    ext
    exact T.jLL.injective hy

def eO (h : OTied D T C) : 𝓞 (fracO D) ≃+* D.what₂.O := (RingEquiv.ofBijective _ (toInt_bijective h)).symm

end GlobalTheory.GeoModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.QpIsOf

theorem qpIs_qpSet : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), ColPin w → ∀ (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch), tp.xi = w.I.xi → GlobalTheory.Mem.HD.TupPins tp →
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := by
  intro B f T w _ Z nch tp hxi _ a p
  classical
  have hr := w.ok.xi_reads a
  have hsel : Formalism.L2.Col.IsSel B.fields w.I.sel := w.ok.sel_ok
  have hf := GlobalTheory.OpenChrRam.qprime_finite B.fields.F B.fields.E B.fields.K ((w.I.tup a : Formalism.L2.DIV.Chr _ _ _))
    (w.I.tup a).2.1.1.1.1.2
  have hpm : ∀ (v : HeightOneSpectrum (𝓞 B.fields.F)) (P : HeightOneSpectrum (𝓞 B.fields.E)),
      Ideal.under (𝓞 B.fields.F) P.asIdeal = v.asIdeal → ((p : 𝓞 B.fields.E) ∈ P.asIdeal ↔ (p : 𝓞 B.fields.F) ∈ v.asIdeal) := by
    intro v P h
    rw [← h, Ideal.under, Ideal.mem_comap, map_natCast]
  have hx : ∀ P, (tp.xi a).UnrAt P ↔ (w.I.xi a).UnrAt P := fun P => by rw [congrFun hxi a]; exact Iff.rfl
  refine (GlobalTheory.Mem.HD.ReQ.mem_qpSet tp a p).trans ?_
  refine Iff.trans (and_congr_right fun _ => exists_congr fun P => and_congr_right fun _ => not_congr (hx P)) ?_
  show (p.Prime ∧ ∃ P, (p : 𝓞 B.fields.E) ∈ P.asIdeal ∧ ¬ (w.I.xi a).UnrAt P) ↔
    p.Prime ∧ ∃ P ∈ Formalism.L2.Col.QE w.I.sel (w.I.tup a : Formalism.L2.DIV.Chr _ _ _), (p : 𝓞 B.fields.E) ∈ P.asIdeal
  rw [Formalism.L2.Col.QE, dite_eq_left hf]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨P, hp, hP⟩
    refine ⟨w.I.sel (P.under (𝓞 B.fields.F)),
      Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr _).2 ⟨P, rfl, hP⟩)), ?_⟩
    rw [hpm _ _ (hsel _), ← hpm _ P rfl]
    exact hp
  · rintro ⟨P, hP, hp⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨P', hP', hr'⟩ := (GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr v).1 (hf.mem_toFinset.1 hv)
    refine ⟨P', ?_, hr'⟩
    rw [hpm v P' (by rw [← hP']; rfl), ← hpm v _ (hsel v)]
    exact hp

end GlobalTheory.Mem.Top.Bl.QpIsOf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) ⟨f.isDel.fin, f.isDel.triv, f.isDel.tame, f.isDel.unr, f.isDel.ine⟩
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) ⟨f.isDel'.fin, f.isDel'.triv, f.isDel'.tame, f.isDel'.unr, f.isDel'.ine⟩
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

end GlobalTheory.Mem.HD.TupPin
end

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.fam3.base3.Ix :=
  GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)


open Classical in
def labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) : A3.fam3.base3.Ix :=
  if h : ∃ c, Bl.OverIx Z σ c then h.choose else (nonempty_ix hH).some

theorem overIx_labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) (h : ∃ c, Bl.OverIx Z σ c) :
    Bl.OverIx Z σ (labOf Z hH σ) := by
  rw [labOf, dite_eq_left h]
  exact h.choose_spec


open Classical in
def logLamOf (Z : ReadL R F X0 Y) (hH : Holds R F) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  else if h : j - 1 < D.R.m then
    if D.what₂.isot j σ = ⊥ then 0 else Real.log ((s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (labOf Z hH σ) (InfinitePlace.mk e))
  else 0

theorem lamAre_of_eq (Z : ReadL R F X0 Y) (hH : Holds R F) (Xd : DivX D) (hX : Xd.logLam = logLamOf Z hH) : Bl.LamAre Z Xd := by
  refine ⟨labOf Z hH, overIx_labOf Z hH, fun i σ e he => ?_⟩
  have h : (i : ℕ) + 1 - 1 < D.R.m := i.2
  rw [hX, logLamOf, if_neg he, dite_eq_left h]
  exact ⟨fun h0 => if_neg h0, fun h0 => if_pos h0⟩

def x0 (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : DivX D where
  geo := Formalism.BasicNotions.Examples₂.geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => Formalism.L2.Geo.PlL D p
  plpFin := fun p _ => Formalism.L2.Geo.finPl D p
  plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
  wtP := fun p _ => Formalism.L2.Geo.wtL D p
  divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
  divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
  plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
  divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
  jC := fun p _ _ => (Formalism.BasicNotions.Examples₂.teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (Formalism.BasicNotions.Examples₂.TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  phiFr_unram := fun _ κ => κ.elim
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := mjH Z
  MjH_good := mjH_good Z hH
  jM := jM Z
  jM_basis := jM_basis Z hH
  jM_lat := jM_lat Z hP hH
  MjLat_sub := mjLat_sub Z hP hH
  jM_metric := jM_metric Z hH
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := logLamOf Z hH
  logLam_base := fun _ _ => if_pos rfl
  kapR := fun _ => kapSharp D
  kapR_pos := fun _ => RowSide.kapOf_pos _ _
  kapR_conj := fun _ => rfl
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

end GlobalTheory.Mem.Top.DivRec

end

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupPins_of_muIsW (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl)
    (xi : X.C.Tup → HChar X.B.host.E) (h : V4.MuIsW X f T Wt xi) {C : CharFrame X.toD7} {nch : NChoice X.toD7}
    (tp : TupTied X.toD7 C nch) (hxi : tp.xi = xi) : GlobalTheory.Mem.HD.TupPins tp := by
  refine ⟨fun μ v hv => ?_, fun w v hv => ?_⟩
  · rw [hxi] at hv
    obtain ⟨h1, h2, h3, h4⟩ :=
      (GlobalTheory.Mem.HD.TupPin.isTwist_types X.B f T (xi μ) (h.range ▸ Set.mem_range_self μ)).2.2.2 v hv
    exact ⟨h1, h2, h3, fun k hk => h4
      ⟨k, Examples₂.PlacesToy.prime_mem_unique v (X.B.host.g_prime k) h2 hk (Ideal.absNorm_mem _)⟩⟩
  · rw [hxi]
    show (xi (X.W.muAt w)).UnrAt v
    by_cases hw : w ∈ Wt
    · rw [h.on w hw, h.tw w]
      exact GlobalTheory.Mem.HD.TupPin.xiTw_unr X.B f T w v hv
    · rw [h.off w hw, h.mu0]
      exact fun _ _ => rfl


open _root_.Formalism.L2.Rows _root_.Formalism.L2.Geo GlobalTheory.GeoGraft GlobalTheory.GeoModel in
theorem geoOver_stages (X : Stages) (X₀ : DivX X.toD7) : GeoOver (fun _ => True) X₀ := by
  let D := X.toD7
  let eO : 𝓞 X.B.Ks ≃+* D.what₂.O := RingEquiv.refl _
  let kL : X.B.Ks →+* D.what₂.LL := X.B.Ks.val.toRingHom
  have hk : ∀ x : 𝓞 X.B.Ks, kL (x : X.B.Ks) = D.what₂.OtoLL (eO x) := fun _ => rfl
  let jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ) :=
    fun p _ la => Classical.choose (GlobalTheory.WittFracPlace.exists_jcPin D p la)
  have hjc : ComplexEmbeddingsCompatible jc := GlobalTheory.ShFam.PinPlace.pinned_tiedFor D jc
    (fun p _ la => Classical.choose_spec (GlobalTheory.WittFracPlace.exists_jcPin D p la))
  refine ⟨divXFl D jc X₀, fun _ _ => True, ⟨divXFl D jc X₀, (divXFl D jc X₀).iMj, (divXFl D jc X₀).iMj_mem, rfl⟩,
    ⟨famFlJ D jc X.B.Ks eO kL hk, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X₀, hjc,
      fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc X.B.Ks eO kL hk, levInTie_famFlJ D jc X.B.Ks eO kL hk⟩, trivial⟩

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem qpIs_qpSet (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch) (hxi : tp.xi = w.I.xi) (hp : GlobalTheory.Mem.HD.TupPins tp) :
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := GlobalTheory.Mem.Top.Bl.QpIsOf.qpIs_qpSet w pin Z tp hxi hp

theorem exists_divT {𝒮 : Slots} {K : Ctx} (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) (l : Lv4 𝒮 K w Z) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
      LamAre l.what₂.r.Z Y := by
  have hp : GlobalTheory.Mem.HD.TupPins l.n.tp := tupPins_of_muIsW (w.st Z) f T l.Wt w.I.xi l.what₂.mu l.n.tp l.n.xi
  let X₁ := x0 l.what₂.r.Z l.what₂.r.z.pins l.what₂.r.intersectionNumber_baseChange
  let X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨X, inK, ⟨Xg, iM, hiM, rfl⟩, hG, -⟩ := geoOver_stages (w.st Z) X₂
  let c := GlobalTheory.Mem.HD.ReQ.reducedDivisorCharacter l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.HD.ReQ.reLoc l.n.tp hp w.I.sel pin.above X₁
  let chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) _ l.n.tp (GlobalTheory.GeoGraft.graft Xg X₂ iM hiM) := ⟨c.Qp_iff, c.eQPl, c.qv_eq⟩
  refine ⟨GlobalTheory.GeoGraft.graft Xg X₂ iM hiM,
    ⟨{ Qp := qpIs_qpSet w pin Z l.n.tp l.n.xi hp, chr := chr, loc := ⟨h1, ?_⟩, inK := inK, geo := hG }⟩,
    GlobalTheory.Mem.R3.exists_mjHTie l.what₂.r.Z _ rfl HEq.rfl, fun _ => rfl,
    lamAre_of_eq l.what₂.r.Z l.what₂.r.intersectionNumber_baseChange _ rfl⟩
  exact ⟨h2.qv_eq, h2.deg1, h2.ram, h2.off_g, h2.nu_eq, h2.typeDim_eq, h2.ZQ_eq, h2.quotientLocalValueFirst_eq⟩

theorem lamAre_heq {K : Ctx} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 p0' : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}
    {t' : RowsT K w Z Wt p0'} (e : p0 = p0') (h : HEq t t') {X : DivX (w.D Z)} (hX : LamAre t'.r.Z X) : LamAre t.r.Z X := by
  subst e
  obtain rfl := eq_of_heq h
  exact hX

theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
    let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
    ⟨Y, h1, h2, h3, fun O t hX hp ht => by
      rw [hOx]
      exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩

theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
    𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=
  fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx

end GlobalTheory.Mem.Top.DivRec

end

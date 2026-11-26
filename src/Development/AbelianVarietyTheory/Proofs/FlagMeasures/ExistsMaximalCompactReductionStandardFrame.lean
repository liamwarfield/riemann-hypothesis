module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFixedPlaceConjugatorLiftsActByReductions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsIdentificationFstEqOneOfFiniteAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsIdentificationFstEqOneOfFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.RealTrivIota

theorem iotaX_fst_eq_one_of_mem_GfC : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : Formalism.L2.Theta.GA D (D.sp.Y 0)), g ∈ GfC (D.sp.Y 0) → (Formalism.L2.SG.RowsJoinPinned.iotaX X h g).1 = 1 := by
  intro D X h g hg
  exact (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h g).2 hg

end GlobalTheory.RealTrivIota
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsIdentificationFstEqOneOfFiniteAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsIdentification_fst_eq_one_of_finiteAdelic : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : Formalism.L2.Theta.GA D (D.sp.Y 0)), g ∈ GfC (D.sp.Y 0) → (Formalism.L2.SG.RowsJoinPinned.iotaX X h g).1 = 1 := by
  first | exact @GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC | exact GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC | (intros; apply GlobalTheory.RealTrivIota.iotaX_fst_eq_one_of_mem_GfC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReducedMatrixOfActsAsDegreeOnePrimeFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReducedMatrixOfActsAsDegreeOnePrimeFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct Matrix

namespace GlobalTheory.RowLev

open Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin IsDedekindDomain

theorem redMat0_of_actsAs : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  intro I N p w fr x hx M hM
  have hp : p.Prime := fr.prime
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p :=
    (Nat.card_congr fr.residueEquiv.toEquiv).trans (Nat.card_zmod p)
  have h1 : ∀ u ∈ lamAf (F := I.F) (wLat0 I w), u ∈ extId I w.asIdeal • I.Lf := by
    refine fun u hu => lamAf_w_le I w _ (fun a ha y hy => ?_) hu
    rw [DictLat.iv_smulE]
    exact Submodule.smul_mem_smul (r := Inhab.psi I.F I.E a) (Ideal.subset_span ⟨a, ha, rfl⟩) (DictLat.iv_mem I hy)
  have h2 : ∀ u ∈ extId I w.asIdeal • I.Lf, u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun _ _ h h' => add_mem h h')
    refine Submodule.span_induction (p := fun a _ => a • v ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ ha
    · rintro z ⟨b, hb, e⟩
      show (z : I.E ⊗[I.F] Af I.F) • v ∈ _
      rw [e]
      exact smul_mem I w hb hv
    · simp
    · intro a b _ _ ha hb
      rw [add_smul]; exact add_mem ha hb
    · intro s a _ ha
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ s ha
  have hz : ∀ u : I.Lf, fr.c u = 0 ↔ (u : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ lamAf (F := I.F) (wLat0 I w) :=
    fun u => (fr.c_ker u).trans ⟨h2 _, h1 _⟩
  choose y hy using fun i : Fin N => fr.c_surj (Pi.single i 1)
  choose b hbL hb using fun i => dense I w hp hcard (y i).2
  let B : Fin N → I.Lf := fun i => ⟨iv I (b i), DictLat.iv_mem I (hbL i)⟩
  have hB : ∀ i, fr.c (B i) = Pi.single i 1 := by
    intro i
    have e : fr.c (y i - B i) = 0 := (hz _).2 (hb i)
    rw [map_sub, sub_eq_zero] at e
    rw [← e, hy]
  have hci : ∀ (n : ℤ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_intCast]
  have hcn : ∀ (n : ℕ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_natCast]
  refine ⟨b, ⟨hbL, fun z hz' => ?_⟩, fun i => ?_⟩
  · let Z : I.Lf := ⟨iv I z, DictLat.iv_mem I hz'⟩
    let c : Fin N → ℤ := fun j => ((fr.c Z j).val : ℤ)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e0 : fr.c (Z - ∑ j, ((c j : ℤ) : IntAf I.F I.E) • B j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero]
      simp only [hci, hB]
      funext k
      simp [c, Finset.sum_apply, Pi.single_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    simp [Z, B, Submodule.coe_sum]
    rfl
  · let V : I.Lf := ⟨I.fmat x *ᵥ iv I (b i), Inhab.mulVec_mem hx (B i).2⟩
    have hV : fr.c V = M *ᵥ Pi.single i 1 := by rw [← hB i]; exact hM (B i) V.2
    have e0 : fr.c (V - ∑ j, (((M j i).val : ℕ) : IntAf I.F I.E) • B j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero, hV]
      simp only [hcn, hB, ZMod.natCast_zmod_val]
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    show _ = ((((M j i).val : ℕ) : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) • iv I (b j)
    rw [SubringClass.coe_natCast]
    rfl

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReducedMatrixOfActsAsDegreeOnePrimeFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedMatrix_of_actsAs_degree_one_prime_frame : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  first | exact @GlobalTheory.RowLev.redMat0_of_actsAs | exact GlobalTheory.RowLev.redMat0_of_actsAs | (intros; apply GlobalTheory.RowLev.redMat0_of_actsAs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedTypePrimePlacesChoiceOnePerConjugatePair
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsChoiceAndIsChoiceOfCard
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSubMemPow
namespace GlobalTheory.IntSubMemPow

theorem exists_int_sub_mem {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (P : Ideal R)
    (hP : P ≠ ⊤) (hc : Nat.card (R ⧸ P) = p) (a : R) : ∃ m : ℤ, a - (m : R) ∈ P := by
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  have : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)

  have hord : addOrderOf (1 : R ⧸ P) = p := by
    have hdvd : addOrderOf (1 : R ⧸ P) ∣ p := hc ▸ addOrderOf_dvd_natCard 1
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) one_ne_zero
    · exact h1

  have htop : AddSubgroup.zmultiples (1 : R ⧸ P) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hc]
  have hmem : Ideal.Quotient.mk P a ∈ AddSubgroup.zmultiples (1 : R ⧸ P) := by
    rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hm, zsmul_one, sub_self]

theorem span_sup_sq_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R)
    (hP : P.IsMaximal) (h0 : P ≠ ⊥) (x : R) (hx : x ∈ P) (hx2 : x ∉ P ^ 2) :
    Ideal.span {x} ⊔ P ^ 2 = P := by
  have hprime : Prime P := Ideal.prime_of_isPrime h0 hP.isPrime
  have hle : Ideal.span {x} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hx) (Ideal.pow_le_self two_ne_zero)

  have hdvd : Ideal.span {x} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime 2).mp hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · exfalso
    rw [pow_zero, Ideal.one_eq_top] at hassoc
    exact hP.ne_top (top_le_iff.mp (hassoc ▸ hle))
  · simpa using hassoc
  · exfalso
    exact hx2 (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))

private lemma pow_le_span_pow_sup_pow_succ {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    P ^ k ≤ Ideal.span {x ^ k} ⊔ P ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (ih hr)
    have hs' := hs
    rw [← h] at hs'
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hs'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hd
    have hsplit : (c * x ^ k + b) * (c' * x + e) =
        (c * c') * x ^ (k + 1) + (c * (x ^ k * e) + b * (c' * x + e)) := by ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) ?_
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
    · have : x ^ k * e ∈ P ^ k * P ^ 2 := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx k) he
      rwa [← pow_add] at this
    · have : b * (c' * x + e) ∈ P ^ (k + 1) * P := Ideal.mul_mem_mul hb hs
      rwa [← pow_succ] at this

theorem exists_sub_mul_pow_mem {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    ∀ y ∈ P ^ k, ∃ c : R, y - c * x ^ k ∈ P ^ (k + 1) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (pow_le_span_pow_sup_pow_succ P x hx h k hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  exact ⟨c, by simpa using hb⟩

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p)
    (P : Ideal (NumberField.RingOfIntegers E)) (hP : Ideal.IsMaximal P)
    (hpP : (p : NumberField.RingOfIntegers E) ∈ P) (hN : Ideal.absNorm P = p)
    (hp2 : (p : NumberField.RingOfIntegers E) ∉ P ^ (2 : ℕ)) (k : ℕ)
    (a : NumberField.RingOfIntegers E) :
    ∃ m : ℤ, a - (m : NumberField.RingOfIntegers E) ∈ P ^ k := by
  have h0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  have hcard : Nat.card (NumberField.RingOfIntegers E ⧸ P) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hgen : Ideal.span {(p : NumberField.RingOfIntegers E)} ⊔ P ^ 2 = P := span_sup_sq_eq P hP h0 _ hpP hp2
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih

    obtain ⟨c, hc⟩ := exists_sub_mul_pow_mem P _ hpP hgen k _ hm
    obtain ⟨n, hn⟩ := exists_int_sub_mem hp P hP.ne_top hcard c
    refine ⟨m + n * (p : ℤ) ^ k, ?_⟩
    have hrest : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P ^ (k + 1) := by
      have : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P * P ^ k :=
        Ideal.mul_mem_mul hn (Ideal.pow_mem_pow hpP k)
      rwa [← pow_succ'] at this
    have heq : a - ((m + n * (p : ℤ) ^ k : ℤ) : NumberField.RingOfIntegers E) =
        (a - (m : NumberField.RingOfIntegers E) - c * (p : NumberField.RingOfIntegers E) ^ k) + (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k := by
      push_cast; ring
    rw [heq]
    exact Ideal.add_mem _ hc hrest

end GlobalTheory.IntSubMemPow
end

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitChoice

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) (hm : (p : 𝓞 E) ∈ P) (hN : Ideal.absNorm P = p) (h2 : (p : 𝓞 E) ∉ P ^ 2) (k : ℕ)
    (a : 𝓞 E) : ∃ m : ℤ, a - m ∈ P ^ k := by
  first
  | exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | (apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)

theorem not_isConj_self (I : AutInst) {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 I.E))
    (hm : (p : 𝓞 I.E) ∈ v.asIdeal) (hN : Ideal.absNorm v.asIdeal = p) (h2 : (p : 𝓞 I.E) ∉ v.asIdeal ^ 2) :
    ¬ IsConj I v v := by
  intro h
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hmap : v.asIdeal.map st ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha
  have hfix : ∀ a, st a = a := fun a => by
    have hall : ∀ k, st a - a ∈ v.asIdeal ^ k := fun k => by
      obtain ⟨m, hm'⟩ := exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a
      have h3 : st (a - m) ∈ v.asIdeal ^ k := by
        have := Ideal.mem_map_of_mem st hm'
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono hmap k this
      rw [map_sub, map_intCast] at h3
      simpa using sub_mem h3 hm'
    have := Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top
    have h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E)) := this ▸ Ideal.mem_iInf.2 hall
    exact sub_eq_zero.1 h4
  have hfixE : ∀ x : I.E, star x = x := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) x
    have ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a := by
      rw [← hst a, hfix]
    have hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b := by
      rw [← hst b, hfix]
    rw [star_div₀, ha, hb]
  have hsurj : Function.Surjective (algebraMap I.F I.E) := fun x => (I.cm.fixed x).1 (hfixE x)
  have h1 : Module.finrank I.F I.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩
  have := I.cm.deg2
  omega

theorem ncard_places_eq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  rw [← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
    have : (p : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at this
    exact this

theorem exists_isChoice_and_isChoice_of_card : ∀ (I : AutInst) (g : Fin 2 → ℕ), (∀ k, (g k).Prime) → g 0 ≠ g 1 → (∀ k (P : Ideal (𝓞 I.E)), P.IsMaximal → ((g k : ℕ) : 𝓞 I.E) ∈ P → Ideal.absNorm P = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ P ^ 2) → (∃ w : ∀ _ : Fin 2, Fin I.f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin I.f) w) ∧ ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Fintype.card (Pl k) = I.f) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) → (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  intro I g hg hne h
  have hdeg : Module.finrank ℚ I.E = 2 * I.f := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]
  refine GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_
  · obtain ⟨h1, h2⟩ := h k v.asIdeal v.isMaximal hv
    exact ⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩
  · rw [ncard_places_eq (hg k),
      GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]

end GlobalTheory.SplitChoice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedTypePrimePlacesChoiceOnePerConjugatePair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open Formalism.MainNotions.BridgeLemma IsDedekindDomain

namespace GlobalTheory.RowLev.FixedChoice

theorem isChoice_wB_plGw : ∀ (D : D7) (X : HidaSetting D), GlobalTheory.RowLev.IsChoice X.B.I D.host.g D.nd.PlG (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) := by
  intro D X
  let e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have he : ∀ a : 𝓞 X.B.I.E, ((e a : 𝓞 D.host.E) : D.host.E) = X.ιE (a : X.B.I.E) := fun a => rfl
  have hnat : ∀ m : ℕ, e (m : 𝓞 X.B.I.E) = (m : 𝓞 D.host.E) := fun m => map_natCast e m
  have hmemB : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E),
      a ∈ (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ↔ e a ∈ w.asIdeal := fun w a => Iff.rfl

  have hspl : ∀ k, SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := span_isMaximal hp
    apply splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  have hsp : ∀ k (P : Ideal (𝓞 X.B.I.E)), P.IsMaximal → ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P →
      Ideal.absNorm P = D.host.g k ∧ ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
    intro k P hP hg
    have hQ : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
      rw [← hnat]; exact Ideal.mem_map_of_mem _ hg
    obtain ⟨h1, h2⟩ := hspl k _ hQ hgQ
    refine ⟨?_, fun h => h2 ?_⟩
    · rw [← h1, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv P (P.map e) e rfl).toEquiv
    · rw [← hnat, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ h
  have hf : X.B.I.f = D.R.f := Formalism.L2.SG.Pf.RowDictPf.f_eq X
  refine (GlobalTheory.SplitChoice.exists_isChoice_and_isChoice_of_card X.B.I D.host.g D.host.g_prime D.host.g_ne hsp).2
    D.nd.PlG _ (fun k => by rw [hf]; convert D.nd.card_PlG k) (fun k v => ?_) (fun k => ?_) (fun k v v' hc => ?_)
  · rw [hmemB, hnat]; exact D.naut.plGw_over k v
  · intro v v' h
    simp only at h
    apply D.naut.plGw_inj k
    apply HeightOneSpectrum.ext
    have h1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal.map e = w.asIdeal :=
      fun w => Ideal.map_comap_of_surjective _ e.surjective w.asIdeal
    rw [← h1, ← h1 (D.naut.plGw k v'), h]
  · apply D.naut.plGw_nconj k v v'
    intro x y hxy
    have hst : ((e.symm y : 𝓞 X.B.I.E) : X.B.I.E) = star ((e.symm x : 𝓞 X.B.I.E) : X.B.I.E) := by
      apply X.ιE.injective
      rw [X.ιE_conj, ← he, ← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hxy]
    have := hc (e.symm x) (e.symm y) hst
    rwa [hmemB, hmemB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at this

end GlobalTheory.RowLev.FixedChoice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedTypePrimePlacesChoiceOnePerConjugatePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedTypePrimePlaces_choice_one_per_conjugate_pair : ∀ (D : D7) (X : HidaSetting D), GlobalTheory.RowLev.IsChoice X.B.I D.host.g D.nd.PlG (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) := by
  first | exact @GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw | exact GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw | (intros; apply GlobalTheory.RowLev.FixedChoice.isChoice_wB_plGw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin

theorem frameRed_exists : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ c red, FrameRed X h t PY c red := by
  intro D X h t PY hF hstd hι
  obtain ⟨c, fr, hB⟩ := GlobalTheory.T.exists_fixed_place_conjugator_lifts_act_by_reductions D X h t PY hF hstd hι (GlobalTheory.T.cmField_splitPlace_eq_of_place_eq D.host.E)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.RowLev.exists_red_actsBy X.B.I D.R.r D.host.g D.nd.PlG
    (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) fr X.n_eq (GlobalTheory.T.fixedTypePrimePlaces_choice_one_per_conjugate_pair D X)
  have hg : X.B.g = D.host.g 0 * D.host.g 1 := X.g_eq
  refine ⟨c, ρ.toFun, ⟨?_, ?_, ?_, ?_⟩, fun kv => GlobalTheory.T.exists_splitPlace_eq_fixedTypePrimePlace D kv, ?_⟩
  · intro k hk kv
    exact (Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ k _).2
      (GlobalTheory.T.reducedMatrix_of_actsAs_degree_one_prime_frame X.B.I D.R.r (D.host.g kv.1) _ (fr kv.1 kv.2) k hk _ (hρ k hk kv.1 kv.2))
  · exact ρ.map_mul
  · exact ρ.surj
  · intro k hk
    rw [hg]
    exact ρ.ker k hk
  · intro kv s hs x γ hx
    obtain ⟨hK, hact, hoth⟩ := hB kv s hs x γ hx
    set k := (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 with hk
    have hfin : (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).1 = 1 := by
      apply GlobalTheory.T.rowsIdentification_fst_eq_one_of_finiteAdelic D X h
      have hn : (GfC (D.sp.Y 0)).Normal := by unfold GfC; infer_instance
      exact hn.conj_mem _ (PY.into _) t
    refine ⟨k, hK, ?_, ?_, ?_⟩
    · obtain ⟨g, hg'⟩ : ∃ g : Formalism.L2.Theta.GA D (D.sp.Y 0), g = PY.ψ (c * x * c⁻¹) := ⟨_, rfl⟩
      have e : (Formalism.L2.SG.RowsJoinPinned.iotaX X h).symm (1, k) = MulAut.conj t g := by
        rw [ContinuousMulEquiv.symm_apply_eq, hg']
        exact Prod.ext hfin.symm rfl
      show PY.ψ (c * x * c⁻¹) = (t⁻¹ * (Formalism.L2.SG.RowsJoinPinned.iotaX X h).symm (1, k) * t : Formalism.L2.Theta.GA D (D.sp.Y 0))
      rw [e, MulAut.conj_apply, ← hg']
      exact (by group : g = t⁻¹ * (t * g * t⁻¹) * t)
    · exact Units.ext (GlobalTheory.RowLev.PlFrame.ActsAs.unique (fr kv.1 kv.2) hK (hρ k hK kv.1 kv.2) hact)
    · intro kv' hne
      exact Units.ext (GlobalTheory.RowLev.PlFrame.ActsAs.unique (fr kv'.1 kv'.2) hK (hρ k hK kv'.1 kv'.2) (hoth kv' hne))

end GlobalTheory.LabPin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximalCompact_reduction_standardFrame : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ c red, FrameRed X h t PY c red := by
  first | exact @GlobalTheory.LabPin.frameRed_exists | exact GlobalTheory.LabPin.frameRed_exists | (intros; apply GlobalTheory.LabPin.frameRed_exists <;> assumption)
end

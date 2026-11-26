module

public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SplitColumnClasses
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
end

noncomputable section

namespace GlobalTheory.ColClassCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

section Descent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p : ℕ}

theorem unram_card_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : Ideal (𝓞 F)) [hv : v.IsPrime] (hpv : (p : 𝓞 F) ∈ v) :
    (p : 𝓞 F) ∉ v ^ 2 ∧ Nat.card (𝓞 F ⧸ v) = p := by
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (v.primesOver (𝓞 E)))
  have hgP : (p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P v (p : 𝓞 F)).1 hpv
  obtain ⟨hP2, hP3⟩ := GlobalTheory.LocSplit.split_prime hp h P hgP
  refine ⟨fun h2 => hP2 ?_, ?_⟩
  · have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 F ⧸ v) := Ideal.Quotient.nontrivial_iff.2 hv.ne_top
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v), Ideal.Quotient.eq_zero_iff_mem]
      exact hpv
    haveI : CharP (𝓞 F ⧸ v) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    have hb : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 F ⧸ v)) := by
      refine ⟨RingHom.injective _, fun x => ?_⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨m, hm⟩ := hP3 (algebraMap (𝓞 F) (𝓞 E) x)
      refine ⟨(m : ZMod p), ?_⟩
      rw [map_intCast, ← map_intCast (Ideal.Quotient.mk v), eq_comm, Ideal.Quotient.eq,
        Ideal.mem_of_liesOver P v]
      simpa using hm
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_zmod]

theorem ncard_primesOver_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard = Module.finrank ℚ F := by
  classical
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).mpr hp'
  have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hs := Ideal.sum_ramification_inertia (𝓞 F) ℚ F (p := Ideal.span {(p : ℤ)}) hne
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 F) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
  obtain ⟨h2, hc⟩ := unram_card_of_split (E := E) hp h q hpq
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' q = 1 := by
    by_contra hne1
    refine h2 ?_
    have := (Ideal.ramificationIdx'_ne_one_iff (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hpq)).1 hne1
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at this
    simpa using this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' q = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' q hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hc] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end Descent

theorem finrank_F (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.sp.cm.deg2, finrank_host D] at h1
  omega

theorem splitsF_of_splitsCompletely (D : D7) {p : ℕ} (h : SplitsCompletely D.host.E p) : SplitsF D p := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 := ncard_primesOver_of_split (F := D.host.F) hp h
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp, finrank_F] at h1
    rw [← h1, ← Nat.card_coe_set_eq]
    rfl
  · haveI := v.isPrime
    exact (unram_card_of_split hp h v.asIdeal hv).2

theorem levelPrime_mod (D : D7) (u : D.what₂.Word) :
    (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 := by
  obtain ⟨π, -, hn, hm⟩ := D.T_norm u
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hm
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hn0 : 1 ≤ D.host.QS := D.host.QS_pos
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = D.host.QS * D.host.q * D.host.d := ⟨_, rfl⟩
  have hM1 : 1 < M := by
    have h1 : 1 * 3 * 7 ≤ D.host.QS * D.host.q * D.host.d :=
      Nat.mul_le_mul (Nat.mul_le_mul hn0 (by omega)) (by omega)
    omega
  rw [← hM] at ha ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (D.host.g 0 * D.host.g 1) ^ 2 := ⟨_, rfl⟩
  rw [← hG] at ha
  set y : D.host.E := (a : D.host.E) * G with hy
  have hyi : IsIntegral ℤ y := (RingOfIntegers.isIntegral_coe a).mul (isIntegral_natCast G)
  have hπ : (π : D.host.E) = 1 + M * y := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    rw [hy]
    push_cast at this ⊢
    linear_combination -this
  have hci : IsIntegral ℤ (D.conjF y) := hyi.map (D.conjF.toRingHom.toIntAlgHom)
  rw [← D.conjF_eq, hπ, map_add (f := _), map_mul, map_one, map_natCast] at hn
  set z : D.host.E := y + D.conjF y + M * (y * D.conjF y) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := D.host.E) M).mul (hyi.mul hci))
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have h4 : z = algebraMap ℚ D.host.E ((((D.mem u).A.T : ℚ) - 1) / M) := by
    have hM0' : (M : D.host.E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff ] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((D.mem u).A.T : ℤ) : ℚ) = ((1 + M * n : ℤ) : ℚ) := by
    have : (n : ℚ) = (((D.mem u).A.T : ℚ) - 1) / M := by simpa using hn'
    push_cast
    rw [this]
    field_simp
    ring
  have h6 : ((D.mem u).A.T : ℤ) = 1 + M * n := by exact_mod_cast h5
  have h7 : (((D.mem u).A.T % M : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, h6, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hM1)
  exact_mod_cast h7

theorem levelPrime_splitsCompletely_in_cmField (D : D7) (u : D.what₂.Word) : SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨(D.mem u).A.T_prime,
    (GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (levelPrime_mod D u)).1⟩

theorem split_g_iff (D : D7) (i : Fin 2) :
    SplitsF D (D.host.g i) ↔ SplitsCompletely D.host.E (D.host.g i) :=
  ⟨fun _ => splitsCompletely_g D i, splitsF_of_splitsCompletely D⟩

end GlobalTheory.ColClassCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_genericDet (R : Type) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (lpMinor R n le_rfl le_rfl) = C g.det * lpMinor R n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 p q
  simp [rowAct, Matrix.mul_apply]

theorem genericDet_pow_mem (R : Type) [CommRing R] (n c : ℕ) :
    lpMinor R n le_rfl le_rfl ^ c ∈ dualWeyl R n n (fun _ => c) := by
  have h := bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)
  have e : shapeDeg (n := n) (fun _ : Fin c => n) = fun _ => c := by
    funext t
    simp [shapeDeg]
  rw [e] at h
  simpa [bideterminant, initMinor, lpMinor] using h

theorem genericDet_pow_mul_hw (R : Type) [CommRing R] (n c : ℕ) (ν : Fin n → ℕ) :
    lpMinor R n le_rfl le_rfl ^ c * hw R le_rfl ν = hw R (le_refl n) (fun i => ν i + c) := by
  cases n with
  | zero => simp [hw, lpMinor]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have hs : (Fin.castSucc s).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_pos hs]
      omega
    · have hs : ¬ (Fin.last m).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_neg hs, Nat.sub_zero]
      rw [pow_add, mul_comm]
      rfl

theorem genericDet_pow_mul :
    ∀ (n c : ℕ) (ν : Fin n → ℕ), (∀ f ∈ dualWeyl ℂ n n ν, lpMinor ℂ n le_rfl le_rfl ^ c * f ∈ dualWeyl ℂ n n (fun i => ν i + c)) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ), rowAct ℂ g (lpMinor ℂ n le_rfl le_rfl ^ c * f) = g.det ^ c • (lpMinor ℂ n le_rfl le_rfl ^ c * rowAct ℂ g f)) ∧ (Antitone ν → lpMinor ℂ n le_rfl le_rfl ^ c * hw ℂ le_rfl ν = hw ℂ (le_refl n) (fun i => ν i + c)) := by
  intro n c ν
  refine ⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩
  · rw [mul_comm]
    exact (dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)
  · rw [map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]

end GlobalTheory.Branching
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem exists_poly_rowAct_coef (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P := by
  induction f using MvPolynomial.induction_on generalizing l with
  | C a => exact ⟨C (l (C a)), fun g => by simp [rowAct]⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp l
    obtain ⟨Q, hQ⟩ := hq l
    exact ⟨P + Q, fun g => by simp only [map_add (f := _), hP, hQ]⟩
  | mul_X p v hp =>
    choose P hP using fun b : Fin n => hp (l ∘ₗ LinearMap.mulRight ℂ (X (b, v.2)))
    refine ⟨∑ b, X (v.1, b) * P b, fun g => ?_⟩
    have e : rowAct ℂ g (X v) = ∑ b, g v.1 b • X (b, v.2) := by
      simp [rowAct, smul_eq_C_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, e, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
    rfl

theorem eq_zero_of_vanish_unitaryGroup (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) : P = 0 := by
  have hinj : Function.Injective (fun x : Fin n × Fin n => ((), x) : Fin n × Fin n → Unit × Fin n × Fin n) :=
    fun x y e => congrArg Prod.snd e
  apply rename_injective _ hinj
  rw [map_zero]
  refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := Unit) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
  rw [eval_rename]
  have := h (u ()) (Matrix.mem_unitaryGroup_iff'.2 (hu ()))
  simpa [Function.comp_def] using this

theorem rowAct_coef_poly_and_unitary_dense :
    (∀ (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ) (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)),
      ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
        l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P) ∧
    ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
      (∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) → P = 0 :=
  ⟨exists_poly_rowAct_coef, eq_zero_of_vanish_unitaryGroup⟩

end GlobalTheory.Branching
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory

theorem directSum_eq_zero_of_toModule_eq_zero {k G ι W : Type} [Field k] [Group G] [DecidableEq ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (σ : Representation k G W)
    (hirr : ∀ i, (ρ i).IsIrreducible)
    (hdis : ∀ i j, i ≠ j → ∀ φ : (ρ i).IntertwiningMap (ρ j), φ = 0)
    (Φ : (Representation.directSum ρ).IntertwiningMap σ)
    (hΦ : ∀ i (v : V i), Φ (DirectSum.lof k ι V i v) = 0 → v = 0) (s : Finset ι) :
    ∀ x : ⨁ i, V i, (∀ j, j ∉ s → x j = 0) → Φ x = 0 → x = 0 := by
  have hρ : ∀ g (x : ⨁ i, V i) j, (Representation.directSum ρ g x) j = ρ j g (x j) := by
    intro g x j
    rfl
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    ext j
    exact hx j (Finset.notMem_empty j)
  | insert i t hi ih =>
    let K : Submodule k (⨁ i, V i) :=
      { carrier := {x | (∀ j, j ∉ insert i t → x j = 0) ∧ Φ x = 0}
        add_mem' := fun {a b} ha hb => ⟨fun j hj => by
          rw [DirectSum.add_apply, ha.1 j hj, hb.1 j hj, add_zero],
          by rw [map_add (f := _), ha.2, hb.2, add_zero]⟩
        zero_mem' := ⟨fun j _ => rfl, map_zero Φ⟩
        smul_mem' := fun c a ha => ⟨fun j hj => by
          rw [DirectSum.smul_apply, ha.1 j hj, smul_zero],
          by rw [map_smul, ha.2, smul_zero]⟩ }
    have hK : ∀ g x, x ∈ K → Representation.directSum ρ g x ∈ K := by
      intro g x hx
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [hρ, hx.1 j hj, map_zero]
      · rw [Φ.isIntertwining, hx.2, map_zero]
    have hz : ∀ x ∈ K, x i = 0 → x = 0 := by
      intro x hx h0
      refine ih x (fun j hj => ?_) hx.2
      by_cases hji : j = i
      · subst hji; exact h0
      · exact hx.1 j (by simp [hji, hj])
    let p : K →ₗ[k] V i := DirectSum.component k ι V i ∘ₗ K.subtype
    have hp : ∀ x : K, p x = x.1 i := fun x => rfl
    have hinj : Function.Injective p := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      exact Subtype.ext (hz x.1 x.2 hx)
    let R : Subrepresentation (ρ i) :=
      { toSubmodule := LinearMap.range p
        apply_mem_toSubmodule := by
          rintro g _ ⟨x, rfl⟩
          exact ⟨⟨_, hK g x.1 x.2⟩, rfl⟩ }
    intro x hx1 hx2
    have hx : x ∈ K := ⟨hx1, hx2⟩
    have := hirr i
    rcases eq_bot_or_eq_top R with hR | hR
    · apply hz x hx
      have : x i ∈ R.toSubmodule := ⟨⟨x, hx⟩, rfl⟩
      rw [hR] at this
      exact this
    · have hsurj : Function.Surjective p := by
        intro v
        have : v ∈ R.toSubmodule := by rw [hR]; trivial
        exact this
      let e := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩
      have he : ∀ y : K, e.symm (y.1 i) = y := fun y => e.symm_apply_apply y
      have hoff : ∀ j, j ≠ i → x j = 0 := by
        intro j hj
        let ψ : (ρ i).IntertwiningMap (ρ j) :=
          LinearMap.intertwiningMap_of_isIntertwiningMap (ρ i) (ρ j)
            (DirectSum.component k ι V j ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap) (by
              intro g v
              obtain ⟨y, rfl⟩ := hsurj v
              have h1 := he ⟨_, hK g y.1 y.2⟩
              have h2 := he y
              change ((e.symm (ρ i g (y.1 i)) : K) : ⨁ i, V i) j
                = ρ j g (((e.symm (y.1 i) : K) : ⨁ i, V i) j)
              rw [h2, ← hρ, h1]
              rfl)
        have h0 : ψ = 0 := hdis i j (Ne.symm hj) ψ
        have h3 : ψ (x i) = x j := by
          change ((e.symm (x i) : K) : ⨁ i, V i) j = x j
          rw [he ⟨x, hx⟩]
        rw [← h3, h0]
        rfl
      have hxe : x = DirectSum.lof k ι V i (x i) := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp [DirectSum.lof_eq_of]
        · rw [hoff j hj, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      apply hz x hx
      apply hΦ
      rw [← hxe]
      exact hx2

theorem nonempty_directSum_equiv_of_finrank_le : ∀ (k G ι W : Type) [Field k] [Group G] [Finite ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : ∀ i, Representation k G (V i)) (σ : Representation k G W), (∀ i, (ρ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ φ : (ρ i).IntertwiningMap (ρ j), φ = 0) → (∀ i, ∃ φ : (ρ i).IntertwiningMap σ, φ ≠ 0) → Module.finrank k W ≤ Module.finrank k (⨁ i, V i) → Nonempty ((Representation.directSum ρ).Equiv σ) := by
  intro k G ι W _ _ _ V _ _ _ _ _ _ ρ σ hirr hdis hex hle
  classical
  have := Fintype.ofFinite ι
  choose φ hφ using hex
  let Φ : (Representation.directSum ρ).IntertwiningMap σ :=
    ⟨DirectSum.toModule k ι W (fun i => (φ i).toLinearMap), fun g => by
      ext i v
      simp [(φ i).isIntertwining]⟩
  have hinj : Function.Injective Φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine directSum_eq_zero_of_toModule_eq_zero ρ σ hirr hdis Φ ?_ Finset.univ x
      (fun j hj => absurd (Finset.mem_univ j) hj) hx
    intro i v hv
    have := hirr i
    have hi := (Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right (hφ i)
    have h1 : Φ (DirectSum.lof k ι V i v) = φ i v :=
      DirectSum.toModule_lof k (φ := fun i => (φ i).toLinearMap) i v
    apply hi
    rw [← h1, hv, map_zero]
  have heq : Module.finrank k (⨁ i, V i) = Module.finrank k W :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hle
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩)
    Φ.isIntertwining'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator
section -- merged from Development.AutomorphicArithmetic.WeightCongruences.ProdCMTypeEmbeddingsRootOfUnityEqOne
open NumberField Formalism.BasicNotions

theorem UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one :
    ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ),
      (∀ σ : H.E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) → (∀ i j, φ i H.sqd = φ j H.sqd) →
      ∀ z : H.E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z = 1 := by
  intro R H I _ φ hu hs z hz
  haveI : IsGalois ℚ H.E := H.galois
  obtain ⟨i₀, -, -⟩ := hu H.φ₀
  have hfix : ∀ g : R.Psi, H.sigmaOf (g : R.GG) H.sqd = H.sqd := fun g => by
    refine (H.galE_mem_Psi_iff _).1 ?_
    have h : H.galE (H.sigmaOf (g : R.GG)) = g := H.gal.apply_symm_apply _
    rw [h]; exact g.2
  have hex : ∀ i, ∃ g : R.Psi, ∀ x, φ i₀ (H.sigmaOf (g : R.GG) x) = φ i x := fun i => by
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) (K := H.E) (φ i₀) (φ i)
      (Subsingleton.elim _ _)
    have h1 : ∀ x, φ i₀ (σ.symm x) = φ i x := fun x => RingHom.congr_fun hσ x
    have h2 : σ.symm H.sqd = H.sqd := (φ i₀).injective ((h1 _).trans (hs i i₀))
    refine ⟨⟨H.galE σ.symm, (H.galE_mem_Psi_iff _).2 h2⟩, fun x => ?_⟩
    have h : H.sigmaOf (H.galE σ.symm) = σ.symm := H.gal.symm_apply_apply _
    show φ i₀ (H.sigmaOf (H.galE σ.symm) x) = _
    rw [h, h1]
  choose f hf using hex
  have hinj : Function.Injective f := fun i j hij => by
    have h : φ i = φ j := RingHom.ext fun x => by rw [← hf i, ← hf j, hij]
    exact (hu (φ i)).unique (Or.inl rfl) (Or.inl h)
  have hsurj : Function.Surjective f := fun g => by
    obtain ⟨i, hi, -⟩ := hu ((φ i₀).comp (H.sigmaOf (g : R.GG) : H.E →+* H.E))
    rcases hi with hi | hi
    · refine ⟨i, Subtype.ext (H.gal.symm.injective ?_)⟩
      refine AlgEquiv.ext fun x => (φ i₀).injective ?_
      exact (hf i x).trans (RingHom.congr_fun hi x).symm
    · exfalso
      have h1 : φ i₀ (H.sigmaOf (g : R.GG) H.sqd) = (starRingEnd ℂ) (φ i H.sqd) := RingHom.congr_fun hi H.sqd
      have hc : H.conj H.sqd = -H.sqd := H.conj_sqd
      have h2 : φ i (H.conj H.sqd) = (starRingEnd ℂ) (φ i H.sqd) := H.conjE_apply (φ i) H.sqd
      rw [hfix, ← h2, hc, map_neg, hs i₀ i] at h1
      have h3 : φ i H.sqd = 0 := by linear_combination h1 / 2
      exact H.sqd_ne_zero ((map_eq_zero (φ i)).1 h3)
  have h1 := UpperTheory.Mu.prod_emb H (Equiv.ofBijective f ⟨hinj, hsurj⟩) hz
  have h2 : H.φ₀ (∏ i, H.sigmaOf (f i : R.GG) z) = H.φ₀ 1 := by
    rw [map_prod, map_one]; exact h1
  have h3 := congrArg (φ i₀) (H.φ₀.injective h2)
  rw [map_prod, map_one] at h3
  rw [← h3]
  exact Finset.prod_congr rfl fun i _ => (hf i z).symm
end

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomBridge

theorem exists_int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff ).1 h')

theorem isIntLattice_of {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) {Λ : PeriodPair} (h1 : Λ.ω₁ = 1)
    (h2 : Λ.ω₂ = (1 + Complex.I * (Real.sqrt d : ℝ)) / 2) : IsIntLattice d Λ := by
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hZ : ∀ n : ℤ, IsIntegral ℤ (n : ℂ) := fun n => isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
  have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  intro x
  rw [PeriodPair.mem_lattice, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨((hZ m).mul isIntegral_one).add ((hZ n).mul ?_), m + n / 2, n / 2, by push_cast; ring⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
  · rintro ⟨hx, a, b, rfl⟩
    have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
      have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
      simpa [hwc, sub_eq_add_neg] using this
    obtain ⟨t, ht⟩ := exists_int_of_isIntegral (r := 2 * a) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
      push_cast; ring)
    obtain ⟨n, hn⟩ := exists_int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
      push_cast
      linear_combination (b : ℂ) ^ 2 * hw2)
    have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [hn, ht]; ring
    obtain ⟨m, hm⟩ := exists_int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
      rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
      exact hZ _))
    have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
      rw [← hm] at hm2
      exact_mod_cast hm2
    obtain ⟨u, rfl⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow ⟨_, hm3⟩
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
    have hu : (u : ℚ) = 2 * b := by
      push_cast at hm
      exact mul_left_cancel₀ hd0 hm
    have hn4 : 4 * n = t ^ 2 + d * u ^ 2 := by
      have : (4 : ℚ) * n = t ^ 2 + d * u ^ 2 := by rw [hn, ht, hu]; ring
      exact_mod_cast this
    have hcZ : (d : ℤ) = 4 * c - 1 := by omega
    have hpar : Even (t - u) := by
      have h5 : Even ((t - u) * (t - u)) :=
        ⟨2 * n - 2 * c * u ^ 2 + u ^ 2 - t * u, by rw [hcZ] at hn4; linear_combination -hn4⟩
      exact (Int.even_mul.1 h5).elim id id
    obtain ⟨k, hk⟩ := hpar
    refine ⟨k, u, ?_⟩
    have e1 : (t : ℂ) = 2 * a := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) ht
    have e2 : (u : ℂ) = 2 * b := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hu
    have e3 : (t : ℂ) - u = k + k := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hk
    linear_combination (-1 / 2 : ℂ) * e3 + (1 / 2 : ℂ) * e1 + (w / 2) * e2

variable {R : Ranks} (H : Host R)

theorem host_isAbelianGalois : IsAbelianGalois ℚ H.E := by
  have := H.hostE_isGalois
  have : IsMulCommutative Gal(H.E/ℚ) :=
    ⟨⟨fun σ τ => (H.gal).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  exact {}

theorem host_unramFin : UnramFin H.E := by
  have : IsCMField H.E := H.isCMField_hostE
  have h : discr H.E = discr (maximalRealSubfield H.E) ^ 2 := H.der.discr_sq
  have h2 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (maximalRealSubfield H.E) (OF H.E) H.E (𝓞 H.E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two, h, Int.natAbs_pow] at h2
  have h0 : (discr (maximalRealSubfield H.E)).natAbs ^ 2 ≠ 0 := pow_ne_zero _ (Int.natAbs_ne_zero.2 (discr_ne_zero _))
  exact Ideal.absNorm_eq_one_iff.1 (mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm))

theorem two_dvd_discr_host : (2 : ℤ) ∣ discr H.E := H.der.discr_primes.2.1

theorem finrank_le_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Module.finrank ℚ E ≤ 2 * Fintype.card I := by
  have := Fintype.card_le_of_surjective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) fun σ => by
    obtain ⟨i, hi | hi, -⟩ := h σ
    · exact ⟨Sum.inl i, hi.symm⟩
    · exact ⟨Sum.inr i, hi.symm⟩
  rwa [Embeddings.card, Fintype.card_sum, ← two_mul] at this

theorem isFieldData_host {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} (h : IsCMType φ)
    (h' : ∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) : IsFieldData H.d φ := by
  have hcard : 2 ≤ Fintype.card I := by
    have h1 := finrank_le_of_isCMType h
    have h2 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
    have h3 : 0 < R.ord := R.ord_pos
    rw [h2] at h1
    omega
  refine ⟨H.hyp.2.1, by have := H.hyp.2.2.2.1; omega, host_unramFin H, fun x hx => ?_, two_dvd_discr_host H, hcard, h, ?_⟩
  · exact UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one R H I φ h h' x (isOfFinOrder_iff_pow_eq_one.1 hx)
  · obtain ⟨i⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqrtMinusD_sq
    have hsq : φ i H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℝ)) ^ 2 := by
      rw [← map_pow, hb, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · exact ⟨_, hb, fun j => (h' j i).trans e⟩
    · exact ⟨-H.sqrtMinusD, by rw [neg_sq, hb], fun j => by rw [map_neg, h' j i, e, neg_neg]⟩

theorem classTermBoundBeta_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBoundBeta := by
  intro R H I _ φ s κ 𝔣 χ hD Λ h1 h2 l hl
  have : IsCMField H.E := H.isCMField_hostE
  have := host_isAbelianGalois H
  obtain ⟨z, -, hz⟩ := h H.E I H.d φ s (isFieldData_host H hD.1 hD.2.1) hD.2.2.1
  have hΛ := isIntLattice_of H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) h1 h2
  refine ⟨⌈betaBound_vp H.d s κ 𝔣 z l⌉₊, fun Q hQ hQl y T hT => ?_⟩
  have := (hz κ 𝔣 Λ χ hD.2.2.2.2.1 hΛ hD.2.2.2.2.2 l hl Q hQ hQl).1 y T hT (⌈betaBound_vp H.d s κ 𝔣 z l⌉₊ : ℕ) 1 one_pos
    (by simpa using Nat.le_ceil _)
  simpa using this

theorem classTermBound_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBound :=
  GlobalTheory.ToricDenom.classTermBound_of_beta (classTermBoundBeta_of_toricDenominator h)

end GlobalTheory.ToricDenomBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHost
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHost
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalConjugacy
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

noncomputable def coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V) : Submodule (𝓞 E) (Fin V.rank → E) :=
  L.map (V.frame.equivFun.restrictScalars (𝓞 E)).toLinearMap

theorem span_eq_top_of_unimodular (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    Submodule.span E (L : Set V.V) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis V.hT V.nondeg V.frame
  let μ := ∑ j, star (φ (V.frame j)) • bs j
  have hμ : ∀ v, V.hT μ v = φ v := by
    have key : V.hT μ = φ := by
      apply V.frame.ext
      intro i
      dsimp only [μ]
      rw [map_sum, LinearMap.sum_apply]
      have hs : ∀ j, V.hT (star (φ (V.frame j)) • bs j) (V.frame i) =
          φ (V.frame j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
        congr 1
        rw [← V.herm.eq (V.frame i) (bs j), hbs]
        split_ifs <;> simp
      simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact fun v => congrArg (fun f : V.V →ₗ[E] E => f v) key
  have hμ₀ : μ ≠ 0 := by
    intro hz
    apply hφ₀
    ext y
    simpa [hz] using (hμ y).symm
  have hline (a : E) : a • μ ∈ L := by
    rw [← hu]
    change a • μ ∈ Formalism.E.hdual V.hT L
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← V.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  let i : E →ₗ[𝓞 E] L :=
    ((LinearMap.toSpanSingleton E _ μ).restrictScalars (𝓞 E)).codRestrict L hline
  let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr h.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E hμ₀ (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem isLattice_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by exact V.baseLattice_isUnimodular) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (coordLat V L) := by
  refine ⟨h.fg.map _, ?_⟩
  have : (coordLat V L : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (L : Set V.V) := rfl
  rw [this, ← Submodule.map_span, span_eq_top_of_unimodular V L h hu, Submodule.map_top, LinearEquiv.range]

theorem herm_coord (V : Formalism.BasicNotions.HSpace E) (x y : V.V) :
    herm V.gramᵀ (V.frame.equivFun x) (V.frame.equivFun y) = V.hT y x := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change V.frame.repr x j * V.gram i j * star (V.frame.repr y i) = _
  ring

theorem selfDual_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (x : Fin V.rank → E) :
    x ∈ coordLat V L ↔ ∀ y ∈ coordLat V L, IsIntegral ℤ (herm V.gramᵀ x y) := by
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
  have h1 : V.frame.equivFun x ∈ coordLat V L ↔ x ∈ L :=
    ⟨fun ⟨z, hz, e⟩ => V.frame.equivFun.injective e ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
  have h2 : x ∈ L ↔ ∀ y ∈ L, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual V.hT L = L from h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  have h3 : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  rw [h1, h2]
  constructor
  · rintro H _ ⟨y, hy, rfl⟩
    have := (h3 _).1 (H y hy)
    rwa [← herm_coord] at this
  · intro H y hy
    rw [h3, ← herm_coord]
    exact H _ ⟨y, hy, rfl⟩

theorem mem_latLoc_iff (V : Formalism.BasicNotions.HSpace E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (y : Fin V.rank → LocAlg v) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔ y ∈ locLattice v (coordLat V V.L0) := by
  have key : ∀ (a : v.adicCompletionIntegers (maximalRealSubfield E)) (b : v.adicCompletion (maximalRealSubfield E)) (z : E),
      a • (b ⊗ₜ[maximalRealSubfield E] z : LocAlg v) = ((a : v.adicCompletion (maximalRealSubfield E)) * b) ⊗ₜ z := by
    intro a b z
    rw [TensorProduct.smul_tmul']
    rfl
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have := Submodule.smul_mem (locLattice v (coordLat V V.L0)) (⟨a, ha⟩ : v.adicCompletionIntegers (maximalRealSubfield E))
        (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      convert this using 1
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hy
    suffices H : ∀ a : v.adicCompletionIntegers (maximalRealSubfield E),
        a • y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v by
      simpa using H 1
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
      intro a
      refine AddSubgroup.subset_closure ⟨a, a.2, x, hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => intro a; rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
    | smul c x _ hx => intro a; rw [smul_smul]; exact hx _

theorem exists_conj (hc : CMData (maximalRealSubfield E) E) (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), HA (Fv (maximalRealSubfield E) v) hc.sig V.gram,
      {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
        (y : Fin V.rank → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
        y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
          (HA.mat (Fv (maximalRealSubfield E) v) hc.sig V.gram (γ v)).1.mulVec y ∈
            GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
    Formalism.L2.Pj.unramBridge_holds E fun P hP => by
      obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
        RingOfIntegers.ext e1.symm
      rwa [this]
  have hG : ∀ a b, cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨γ, hγ, hfin⟩ := (GlobalTheory.selfDual_lattices_one_genus hG hG hd hd (isLattice_coordLat V L h1 h2)
    (isLattice_coordLat V V.L0 V.standardTuple_isLattice V.baseLattice_isUnimodular)
    (Or.inl ⟨selfDual_coordLat V L h2, selfDual_coordLat V V.L0 V.baseLattice_isUnimodular⟩)).2.1 rfl
  have hmem : ∀ v, γ v ∈ HR (Fv (maximalRealSubfield E) v) hc.sig V.gram := fun v => by
    have h := congrArg Matrix.transpose (hγ v).1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
    exact h.symm
  refine ⟨fun v => ⟨γ v, hmem v⟩, hfin.subset fun v hv h => hv (Subtype.ext h), fun v y => ?_⟩
  rw [mem_latLoc_iff]
  exact ((hγ v).2 y).trans (mem_latLoc_iff (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v _).symm

end

theorem exists_local_conjugation : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v :=
  fun D V L h1 h2 =>
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    exists_conj (E := D.host.E) D.sp.cm V L h1 h2

end GlobalTheory.LocalConjugacy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHostStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  first | exact @GlobalTheory.LocalConjugacy.exists_local_conjugation | exact GlobalTheory.LocalConjugacy.exists_local_conjugation | (intros; apply GlobalTheory.LocalConjugacy.exists_local_conjugation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColAddGenRenameCastSucc
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching.AddColumn

theorem weight_mapDomain (r n : ℕ) (u : Fin r × Fin n →₀ ℕ) :
    (∀ i : Fin n, Finsupp.weight (colW r (n + 1))
        (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) i.castSucc = Finsupp.weight (colW r n) u i) ∧
      Finsupp.weight (colW r (n + 1)) (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) (Fin.last n) = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, ha.1, hb.1]
    · rw [Finsupp.mapDomain_add, map_add (f := _), Pi.add_apply, ha.2, hb.2]
  | single v k =>
    refine ⟨fun i => ?_, ?_⟩
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply]
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply,
        (Fin.castSucc_lt_last v.2).ne']

theorem colAddGen_rename_castSucc (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l.castSucc j.castSucc
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename (Option.map (Prod.map id Fin.castSucc)) (colAddGen R l j f) := by
  have e : (colAddGen R (r := r) l.castSucc j.castSucc).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename (Option.map (Prod.map id Fin.castSucc))).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hv : s = j
    · simp [colAddGen, hv]
    · simp [colAddGen, hv]
  exact DFunLike.congr_fun e f

theorem colAddGen_rename_last (R : Type*) [CommRing R] {r n : ℕ} (l : Fin (n + 1))
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l (Fin.last n)
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename some (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) := by
  have e : (colAddGen R (r := r) l (Fin.last n)).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename some).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [colAddGen, (Fin.castSucc_lt_last s).ne]
  exact DFunLike.congr_fun e f

theorem add_column : ∀ (r n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → (∀ f ∈ dualWeyl ℂ r n (fun i => ν i.castSucc), rename (Prod.map id Fin.castSucc) f ∈ dualWeyl ℂ r (n + 1) ν) ∧ ∀ (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ), rowAct ℂ g (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) = rename (Prod.map id Fin.castSucc) (rowAct ℂ g f) := by
  intro r n ν hν
  refine ⟨fun f hf => ?_, fun g f => ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
    refine ⟨fun d hd => ?_, fun l j hlj => ?_⟩
    · obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
      have h := hf.1 hu
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [(weight_mapDomain r n u).2, hν]
      · rw [(weight_mapDomain r n u).1, h]
    · induction j using Fin.lastCases with
      | last => exact colAddGen_rename_last ℂ l f
      | cast j =>
        induction l using Fin.lastCases with
        | last => exact absurd hlj (not_lt.2 (Fin.le_last _))
        | cast l =>
          rw [colAddGen_rename_castSucc, hf.2 l j (Fin.castSucc_lt_castSucc_iff.1 hlj), rename_rename,
            rename_rename]
          rfl
  · have e : (rowAct ℂ g).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
        (rename (Prod.map id Fin.castSucc)).comp (rowAct ℂ g) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, s⟩
      simp [rowAct]
    exact DFunLike.congr_fun e f

end GlobalTheory.Branching.AddColumn
end

module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.PeriodIdealUnit

theorem not_dvd_different {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ} (hl : l.Prime)
    (v : Ideal (𝓞 E)) [hvp : v.IsPrime] (hv : ((l : ℕ) : 𝓞 E) ∈ v) (h2 : ((l : ℕ) : 𝓞 E) ∉ v ^ 2) :
    ¬ v ∣ differentIdeal (𝓞 K) (𝓞 E) := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : v.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hvp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have he : v.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact h2 (by simpa using hne)
  have : Algebra.IsUnramifiedAt ℤ v := Ideal.ramificationIdx_eq_one_iff.1 he
  exact not_dvd_differentIdeal_iff.2 (Algebra.IsUnramifiedAt.of_restrictScalars ℤ v)

theorem locP_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E)
    (h1 : I ≤ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h2 : ∃ n, n ∉ P.asIdeal ∧ n • (1 : E) ∈ I) :
    localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
  le_antisymm ((ThetaMove.localization_mono P h1).trans (localization_localization₂ P _).le)
    ((ThetaMove.localization_mono P (Submodule.one_le.2 h2 : (1 : Submodule (𝓞 E) E) ≤ localization₂ P.asIdeal I)).trans (localization_localization₂ P _).le)

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem one_mem_inv_b (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  refine (FractionalIdeal.mem_inv_iff (b_ne_zero D)).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem locP_AA_eq_one : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)), (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal) → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  intro X D s cc δ B χ cD P hp h2 hc
  let e : 𝓞 D.host.E ≃+* 𝓞 X.E := RingOfIntegers.mapRingEquiv s.iE.symm
  have he : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 X.E) X.E (e x) = s.iE.symm (algebraMap _ D.host.E x) := fun x => rfl
  have := P.isPrime
  let v : Ideal (𝓞 D.host.E) := P.asIdeal.comap (e : 𝓞 D.host.E →+* 𝓞 X.E)
  have hvp : v.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hv1 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v := by
    rw [Ideal.mem_comap, map_natCast]; exact hmem
  have hv2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v ^ 2 := fun h => by
    have h3 := Ideal.le_comap_pow (e : 𝓞 D.host.E →+* 𝓞 X.E) 2 h
    rw [Ideal.mem_comap, map_natCast] at h3
    exact h2 h3
  have hnd := not_dvd_different (K := D.host.K) hp v hv1 hv2
  have hnot : ¬ D.host.𝔟 ≤ v := fun hle => hnd (by
    rw [D.host.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hN : ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => by
    have h3 : IsCoprime ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) := hc.cast
    obtain ⟨a, b, hab⟩ := h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hmem)))
  refine locP_eq_one P _ ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine ⟨e z, hzP, Submodule.mem_one.2 ⟨e (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def, he, he, ← map_mul, map_mul (algebraMap _ D.host.E), hw]
    congr 1
    have : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) = ((c : D.host.K) : D.host.E) := rfl
    rw [this]
    ring
  · refine ⟨_, hN, Submodule.subset_span ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, 1, one_mem_inv_b D, ?_⟩⟩
    have h1 : (((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K)) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) :=
      map_natCast ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)) _
    rw [h1, mul_one, map_natCast, Algebra.smul_def, map_natCast, mul_one]

end GlobalTheory.PeriodIdealUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.TamePow

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem locK_eq_one_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (y : Lˣ)
    (h2 : v.valuation L (y : L) = 1) (h1 : v.valuation L ((y : L) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    χ.locK v y = 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  refine h (atFin v y) ((hval _).trans h2) ?_
  have : ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
      algebraMap L (v.adicCompletion L) ((y : L) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this, hval]
  simpa using h1

theorem exists_pow_sub_one_mem (v : HeightOneSpectrum (𝓞 L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 L, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal := by
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hmax := v.isMaximal
  refine ⟨Nat.card (𝓞 L ⧸ v.asIdeal)ˣ, Nat.card_pos, fun r hr => ?_⟩
  let _ := Ideal.Quotient.field v.asIdeal
  have h0 : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := Units.mk0 _ h0))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h1

theorem exists_pow_locK (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Lˣ, v.valuation L (u : L) = 1 → χ.locK v u ^ m = 1 := by
  obtain ⟨m, hm, H⟩ := exists_pow_sub_one_mem v
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := (intAt_iff (P := v) (u : L)).2 hu.le
  have hs1 : v.valuation L (algebraMap (𝓞 L) L s) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hr1 : v.valuation L (algebraMap (𝓞 L) L r) = 1 := by
    rw [← hrs, map_mul, hs1, hu, one_mul]
  have hr : r ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).1 hr1
  have hmem : r ^ m - s ^ m ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem (H r hr) (H s hs)
    rwa [sub_sub_sub_cancel_right] at this
  have hle : v.valuation L (algebraMap (𝓞 L) L (r ^ m - s ^ m)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    simpa using (v.intValuation_le_pow_iff_mem (r ^ m - s ^ m) 1).2 (by simpa using hmem)
  rw [← map_pow]
  refine locK_eq_one_of_tame χ h _ (by simp [hu]) ?_
  have e : algebraMap (𝓞 L) L (r ^ m - s ^ m) = (algebraMap (𝓞 L) L s) ^ m * (((u ^ m : Lˣ) : L) - 1) := by
    rw [map_sub, map_pow, map_pow, ← hrs, Units.val_pow_eq_pow_val]; ring
  rwa [e, map_mul, map_pow, hs1, one_pow, one_mul] at hle

theorem exists_gen (P : HeightOneSpectrum (𝓞 L)) : ∃ (h : ℕ) (a : Lˣ), 0 < h ∧
    P.valuation L (a : L) = WithZero.exp (-(h : ℤ)) ∧
    ∀ Q : HeightOneSpectrum (𝓞 L), Q ≠ P → Q.valuation L (a : L) = 1 := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have h1 : ClassGroup.mk0 (⟨P.asIdeal, hP⟩ ^ Nat.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one']
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (pow_mem hP _)).1 h1
  have ha' : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) = Ideal.span {a} := ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ P.ne_bot (by simpa using ha')
  refine ⟨Nat.card (ClassGroup (𝓞 L)), Units.mk0 (algebraMap (𝓞 L) L a) (by simpa using ha0), Nat.card_pos, ?_, ?_⟩
  · rw [Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap, P.intValuation_if_neg ha0, ← ha',
      Associates.mk_pow, Associates.count_pow (by simpa using P.ne_bot) P.associates_irreducible,
      Associates.count_self P.associates_irreducible, mul_one]
  · intro Q hQ
    rw [Units.val_mk0, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hm
    have h2 : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) ≤ Q.asIdeal := by
      rw [ha', Ideal.span_singleton_le_iff_mem]; exact hm
    have h3 := Q.isPrime.le_of_pow_le h2
    exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h3).symm)

theorem exists_pow_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))), χ.ProductRule → (∀ v, v ∉ S → χ.UnrAt v) → (∀ v, χ.TameAt v) → ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), ∃ (M : ℕ) (z : Eˣ), 0 < M ∧ P.valuation E (z : E) = P.valuation E (k : E) ^ M ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) ∧ χ.locK P k ^ M * χ.inf z = 1 := by
  intro E _ _ χ S hpr hunr htame P k
  classical
  obtain ⟨h, a, hh, haP, haQ⟩ := exists_gen P
  choose m hm hmu using fun v => exists_pow_locK χ (htame v)
  set M' := ∏ v ∈ insert P S, m v with hM'
  have hkill : ∀ v ∈ insert P S, ∀ u : Eˣ, v.valuation E (u : E) = 1 → χ.locK v (u ^ M') = 1 := by
    intro v hv u hu
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hv
    rw [map_pow, hM', hc, pow_mul, hmu v u hu, one_pow]
  have hk0 : P.valuation E (k : E) ≠ 0 := by simp
  set z0 : Eˣ := a ^ ordF P k with hz0
  have hz0P : P.valuation E (z0 : E) = P.valuation E (k : E) ^ h := by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haP, ← WithZero.exp_log hk0, ← WithZero.exp_zsmul,
      ← WithZero.exp_nsmul, ordF]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have hz0Q : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z0 : E) = 1 := fun Q hQ => by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]
  have hzQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E ((z0 ^ M' : Eˣ) : E) = 1 := fun Q hQ => by
    rw [Units.val_pow_eq_pow_val, map_pow, hz0Q Q hQ, one_pow]
  refine ⟨h * M', z0 ^ M', Nat.mul_pos hh (Finset.prod_pos fun v _ => hm v), ?_, hzQ, ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, hz0P, pow_mul]
  · have H := hpr (insert P S) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (z0 ^ M')
    have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P S), χ.val v ^ ordF v (z0 ^ M')) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      by_cases hv : v ∈ insert P S
      · rw [finprod_eq_if, if_neg (not_not.2 hv)]
      rw [finprod_eq_if, if_pos hv]
      have : v ≠ P := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      rw [ordF, hzQ v this, WithZero.log_one, neg_zero, zpow_zero]
    have e2 : ∏ v ∈ insert P S, χ.locK v (z0 ^ M') = χ.locK P (z0 ^ M') :=
      Finset.prod_eq_single P (fun v hv hne => hkill v hv z0 (hz0Q v hne))
        (fun h => absurd (Finset.mem_insert_self _ _) h)
    have e3 : χ.locK P (z0 ^ M') = χ.locK P k ^ (h * M') := by
      have := hkill P (Finset.mem_insert_self _ _) (z0 / k ^ h) (by
        rw [Units.val_div_eq_div_val, map_div₀, hz0P, Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hk0)])
      rwa [div_pow, map_div, div_eq_one, ← pow_mul, map_pow (χ.locK P) k] at this
    rw [e1, e2, e3, mul_one, mul_comm] at H
    exact H

end GlobalTheory.TamePow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDual
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CocInt

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem hv_apply {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem emb_apply (x : HomE X.E a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    emb A x τ i j = A.δ * X.embC A.σ₀ τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (hX : X.Ok) (r : X.E) (x y : HomE X.E a b) :
    HV A.sc (emb A (r • x)) (emb A y) = HV A.sc (emb A x) (emb A (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [emb_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hX.conjE, Complex.conj_conj]
  ring

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add (embH _ _) x y

theorem coc_add_left (x y z : HomE X.E a b) : coc A (x + y) z = coc A x z + coc A y z := by
  simp only [coc, imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem coc_zero_left (z : HomE X.E a b) : coc A 0 z = 0 := by
  have := coc_add_left A 0 0 z
  rw [add_zero] at this
  linarith

theorem emb_injective (hX : X.Ok) (hδ : A.δ ≠ 0) : Function.Injective (emb A : HomE X.E a b → _) := by
  intro x y h
  obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [emb_apply, emb_apply] at this
  simpa using (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ this)

variable {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem emb_mem {x : HomE X.E a b} (hx : x ∈ per A N N') : emb A x ∈ LamC (X.embC A.σ₀) A.δ A.AA N N' :=
  ⟨x, hx, rfl⟩

theorem mem_per_iff (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') (x : HomE X.E a b) :
    x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n := by
  constructor
  · intro hx y hy
    have h1 := emb_mem A hx
    rw [← hL.1] at h1
    exact h1 _ (emb_mem A hy)
  · intro h
    have h1 : emb A x ∈ dualLat (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    rw [hL.1] at h1
    obtain ⟨x', hx', e⟩ := h1
    rwa [← emb_injective A hX hδ (a₁ := x') e]

theorem coc_int (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') {x y : HomE X.E a b}
    (hx : x ∈ per A N N') (hy : y ∈ per A N N') : ∃ n : ℤ, coc A x y = n := by
  obtain ⟨m, hm⟩ := (mem_per_iff A hX hδ hL x).1 hx y hy
  have h := hL.2.2 _ (emb_mem A hx) _ (emb_mem A hy)
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n + m, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (HV A.sc (emb A y) (emb A x)).re = (HV A.sc (emb A x) (emb A y)).re := by
    rw [hv_swap]; simp
  simp only [imH] at hm
  simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, h3, hm] at h2
  simp at h2
  simp only [coc, imH, hm]
  push_cast
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

theorem cocycle_integral : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  intro X A a b N N' hX hδ hL
  have h1 : ∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y) := by
    intro r x y
    simp only [coc, imH, altE, hv_smul A hX, and_self]
  refine ⟨h1, mem_per_iff A hX hδ hL, fun x y h => ?_⟩
  let I : Ideal (𝓞 X.E) :=
    { carrier := {r | ∀ s : 𝓞 X.E, ∃ n : ℤ, coc A ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [coc_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, coc_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 X.E) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField X.E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨v, hv, hy⟩ := (mem_locP _ _ _).1 hy
    have hmem : u * cO X.E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := coc_int A hX hδ hL (Submodule.smul_mem _ s hx) hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO X.E v)) • x = (star (algebraMap (𝓞 X.E) X.E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul X.E s, ← algebraMap_smul X.E u, ← algebraMap_smul X.E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, (h1 _ _ _).1, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hM.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 X.E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.MomT.CocInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDualStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCocycleForm_integral_selfDual : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  first | exact @GlobalTheory.MomT.CocInt.cocycle_integral | exact GlobalTheory.MomT.CocInt.cocycle_integral | (intros; apply GlobalTheory.MomT.CocInt.cocycle_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSum
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.RepsMod

variable {H : Type} [AddCommGroup H]

theorem sum_eq_of_family {M ι : Type} [AddCommMonoid M] {Λ B : AddSubgroup H} {R : Finset H}
    (hR : IsReps Λ B R) (s : Finset ι) (f : ι → H) (hf : ∀ i ∈ s, f i ∈ B)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i - f j ∈ Λ → i = j) (hsurj : ∀ y ∈ B, ∃ i ∈ s, y - f i ∈ Λ)
    (F : H → M) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ i ∈ s, F (f i) := by
  obtain ⟨h1, h2, h3⟩ := hR
  symm
  choose r hr hrl using fun i (hi : i ∈ s) => h3 (f i) (hf i hi)
  refine Finset.sum_bij r hr ?_ ?_ ?_
  · intro i hi j hj hij
    apply hinj i hi j hj
    have := Λ.sub_mem (hrl i hi) (hrl j hj)
    rw [hij] at this
    simpa using this
  · intro y hy
    obtain ⟨i, hi, hl⟩ := hsurj y (h1 y hy)
    refine ⟨i, hi, ?_⟩
    symm
    apply h2 y hy _ (hr i hi)
    have := Λ.add_mem hl (hrl i hi)
    simpa using this
  · intro i hi
    have := hF (r i hi) (h1 _ (hr i hi)) _ (hrl i hi) (B.sub_mem (hf i hi) (h1 _ (hr i hi)))
    simpa using this

theorem out_sub_mem_iff (Λ B : AddSubgroup H) (x y : B) :
    ((x : H) - y ∈ Λ) ↔ (QuotientAddGroup.mk x : B ⧸ Λ.addSubgroupOf B) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  simp

theorem out_inj (Λ B : AddSubgroup H) (c d : B ⧸ Λ.addSubgroupOf B)
    (h : ((c.out : B) : H) - (d.out : B) ∈ Λ) : c = d := by
  rw [out_sub_mem_iff] at h
  simpa using h

theorem out_surj (Λ B : AddSubgroup H) (y : H) (hy : y ∈ B) :
    ∃ c : B ⧸ Λ.addSubgroupOf B, y - ((c.out : B) : H) ∈ Λ := by
  refine ⟨QuotientAddGroup.mk ⟨y, hy⟩, ?_⟩
  have := (out_sub_mem_iff Λ B ⟨y, hy⟩ (Quotient.out (QuotientAddGroup.mk ⟨y, hy⟩ : B ⧸ Λ.addSubgroupOf B))).2 (by simp)
  exact this

theorem exists_reps (Λ B : AddSubgroup H) (h : Λ.relIndex B ≠ 0) : ∃ R : Finset H, IsReps Λ B R := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  refine ⟨Finset.univ.image (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (c.out).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    rw [out_inj Λ B c d hxy]
  · intro y hy
    obtain ⟨c, hc⟩ := out_surj Λ B y hy
    exact ⟨_, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, hc⟩

theorem card_reps (Λ B : AddSubgroup H) (R : Finset H) (hR : IsReps Λ B R) :
    R.card = Λ.relIndex B := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := by
    refine Finite.of_surjective (fun x : R => (QuotientAddGroup.mk ⟨x.1, hR.1 _ x.2⟩ : B ⧸ Λ.addSubgroupOf B)) ?_
    intro c
    obtain ⟨x, hx, hl⟩ := hR.2.2 _ (c.out).2
    refine ⟨⟨x, hx⟩, ?_⟩
    have := (out_sub_mem_iff Λ B c.out ⟨x, hR.1 _ hx⟩).1 hl
    simpa using this.symm
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  have h := sum_eq_of_family hR Finset.univ (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H))
    (fun c _ => (c.out).2) (fun c _ d _ h => out_inj Λ B c d h)
    (fun y hy => by
      obtain ⟨c, hc⟩ := out_surj Λ B y hy
      exact ⟨c, Finset.mem_univ _, hc⟩) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h, ← Nat.card_eq_fintype_card]
  rfl

theorem sum_prod_reps (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H)
    (F : H → M) (h1 : B₁ ≤ B) (h2 : B₂ ≤ B) (hs : ∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ)
    (hi : ∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) (hR : IsReps Λ B R) (hR₁ : IsReps Λ B₁ R₁)
    (hR₂ : IsReps Λ B₂ R₂) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂) := by
  rw [← Finset.sum_product']
  refine sum_eq_of_family hR (R₂ ×ˢ R₁) (fun p => p.2 + p.1) ?_ ?_ ?_ F hF
  · intro p hp
    rw [Finset.mem_product] at hp
    exact B.add_mem (h1 (hR₁.1 _ hp.2)) (h2 (hR₂.1 _ hp.1))
  · intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    have e : p.2 + p.1 - (q.2 + q.1) = (p.2 - q.2) + (p.1 - q.1) := by abel
    simp only [e] at hpq
    have a1 := hi _ (B₁.sub_mem (hR₁.1 _ hp.2) (hR₁.1 _ hq.2)) _
      (B₂.sub_mem (hR₂.1 _ hp.1) (hR₂.1 _ hq.1)) hpq
    have a2 : p.1 - q.1 ∈ Λ := by
      have := Λ.sub_mem hpq a1
      simpa using this
    exact Prod.ext (hR₂.2.1 _ hp.1 _ hq.1 a2) (hR₁.2.1 _ hp.2 _ hq.2 a1)
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hl⟩ := hs y hy
    obtain ⟨r₁, hr₁, hl₁⟩ := hR₁.2.2 _ hy₁
    obtain ⟨r₂, hr₂, hl₂⟩ := hR₂.2.2 _ hy₂
    refine ⟨(r₂, r₁), Finset.mem_product.2 ⟨hr₂, hr₁⟩, ?_⟩
    have e : y - (r₁ + r₂) = (y - (y₁ + y₂)) + (y₁ - r₁) + (y₂ - r₂) := by abel
    simp only [e]
    exact Λ.add_mem (Λ.add_mem hl hl₁) hl₂

theorem sum_char_reps (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K)
    (hR : IsReps Λ B R) (hm : ∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y)
    (h1 : ∀ x ∈ B, x ∈ Λ → φ x = 1) :
    ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧
      ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0) := by
  constructor
  · intro h
    rw [Finset.sum_congr rfl (fun y hy => h y (hR.1 y hy))]
    simp
  · intro h
    push Not at h
    obtain ⟨y₀, hy₀, hne⟩ := h
    have key := sum_eq_of_family hR R (fun y => y₀ + y) (fun y hy => B.add_mem hy₀ (hR.1 y hy))
      (fun x hx y hy hxy => hR.2.1 x hx y hy (by simpa using hxy))
      (fun y hy => by
        obtain ⟨x, hx, hl⟩ := hR.2.2 _ (B.sub_mem hy hy₀)
        exact ⟨x, hx, by rwa [← sub_sub]⟩) φ
      (fun y hy l hl hlB => by rw [hm y hy l hlB, h1 l hlB hl, mul_one])
    rw [Finset.sum_congr rfl (fun y hy => hm y₀ hy₀ y (hR.1 y hy)), ← Finset.mul_sum] at key
    have : (φ y₀ - 1) * ∑ y ∈ R, φ y = 0 := by rw [_root_.sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem not_dvd_relIndex (Λ B : AddSubgroup H) (g p : ℕ) (hp : p.Prime) (hc : Nat.Coprime g p)
    (h : Λ.relIndex B ≠ 0) (hg : ∀ x ∈ B, g • x ∈ Λ) : ¬ p ∣ Λ.relIndex B := by
  intro hd
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fact.mk hp
  obtain ⟨c, hcc⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ Λ.addSubgroupOf B) p hd
  have h0 : g • c = 0 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hg x x.2
  have hdg : p ∣ g := hcc ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  exact (hp.coprime_iff_not_dvd.1 hc.symm) hdg

theorem reps_facts : ∀ (H : Type) [AddCommGroup H], (∀ Λ B : AddSubgroup H, Λ.relIndex B ≠ 0 → ∃ R : Finset H, IsReps Λ B R) ∧ (∀ (Λ B : AddSubgroup H) (R : Finset H), IsReps Λ B R → R.card = Λ.relIndex B) ∧ (∀ (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H) (F : H → M), B₁ ≤ B → B₂ ≤ B → (∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ) → (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) → IsReps Λ B R → IsReps Λ B₁ R₁ → IsReps Λ B₂ R₂ → (∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) → ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂)) ∧ (∀ (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K), IsReps Λ B R → (∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y) → (∀ x ∈ B, x ∈ Λ → φ x = 1) → ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧ ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0)) ∧ ∀ (Λ B : AddSubgroup H) (g p : ℕ), p.Prime → Nat.Coprime g p → Λ.relIndex B ≠ 0 → (∀ x ∈ B, g • x ∈ Λ) → ¬ p ∣ Λ.relIndex B :=
  fun _ _ => ⟨exists_reps, card_reps, sum_prod_reps, sum_char_reps, not_dvd_relIndex⟩

end GlobalTheory.RepsMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addSubgroup_reps_existence_card_sum : ∀ (H : Type) [AddCommGroup H], (∀ Λ B : AddSubgroup H, Λ.relIndex B ≠ 0 → ∃ R : Finset H, IsReps Λ B R) ∧ (∀ (Λ B : AddSubgroup H) (R : Finset H), IsReps Λ B R → R.card = Λ.relIndex B) ∧ (∀ (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H) (F : H → M), B₁ ≤ B → B₂ ≤ B → (∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ) → (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) → IsReps Λ B R → IsReps Λ B₁ R₁ → IsReps Λ B₂ R₂ → (∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) → ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂)) ∧ (∀ (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K), IsReps Λ B R → (∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y) → (∀ x ∈ B, x ∈ Λ → φ x = 1) → ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧ ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0)) ∧ ∀ (Λ B : AddSubgroup H) (g p : ℕ), p.Prime → Nat.Coprime g p → Λ.relIndex B ≠ 0 → (∀ x ∈ B, g • x ∈ Λ) → ¬ p ∣ Λ.relIndex B := by
  first | exact @GlobalTheory.RepsMod.reps_facts | exact GlobalTheory.RepsMod.reps_facts | (intros; apply GlobalTheory.RepsMod.reps_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
noncomputable section

namespace GlobalTheory.LvT.BuiltChain

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] (emb : ι → E →+* K)


omit [Fintype ι] in
theorem mem_dualFr_tauLat {n : ℕ} (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (φ : Fin n → K) :
    φ ∈ dualFr (tauLat emb τ L) ↔ ∀ y ∈ L, φ ⬝ᵥ (fun a => emb τ (y a)) ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h y hy
    exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [dotProduct_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy


omit [Fintype ι] in
theorem dualFr_tauLat_sum {N n : ℕ} (hN : N = n + 1) (τ : ι) {t : E} (ht : t ≠ 0) (L : Submodule (𝓞 E) (Fin N → E))
    (L' : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) :
    dualFr (tauLat emb τ L) = Br.sumLat hN (dualFr (tauLat emb τ L')) (emb τ t) := by
  subst hN
  ext φ
  rw [mem_dualFr_tauLat]
  change _ ↔ (fun a : Fin n => φ a.castSucc) ∈ dualFr (tauLat emb τ L') ∧ ∃ c : 𝓞 K, φ (Fin.last n) = (c : K) * emb τ t
  replace hL : ∀ x, x ∈ L ↔ (fun a : Fin n => x a.castSucc) ∈ L' ∧ t * x (Fin.last n) ∈ (1 : Submodule (𝓞 E) E) := hL
  rw [mem_dualFr_tauLat]
  have e : ∀ y : Fin (n + 1) → E, φ ⬝ᵥ (fun a => emb τ (y a)) =
      (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun a => emb τ (y a.castSucc)) + φ (Fin.last n) * emb τ (y (Fin.last n)) := by
    intro y
    simp only [dotProduct, Fin.sum_univ_castSucc]
  have ht' : emb τ t ≠ 0 := (map_ne_zero _).2 ht
  constructor
  · intro h
    refine ⟨fun y hy => ?_, ?_⟩
    · have := h (Fin.snoc y 0) ((hL _).2 ⟨by simpa using hy, by simp⟩)
      rw [e] at this
      simpa using this
    · have := h (Fin.snoc (0 : Fin n → E) t⁻¹) ((hL _).2 ⟨by simp only [Fin.snoc_castSucc]; exact L'.zero_mem, by
        rw [Fin.snoc_last, mul_inv_cancel₀ ht]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩)
      rw [e] at this
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, map_zero] at this
      have h0 : (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun _ => (0 : K)) = 0 := dotProduct_zero _
      rw [h0, zero_add, map_inv₀] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      change _ = algebraMap (𝓞 K) K c * _
      rw [hc, inv_mul_cancel_right₀ ht']
  · rintro ⟨h1, c, hc⟩ y hy
    obtain ⟨h2, h3⟩ := (hL y).1 hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
    rw [e]
    refine Submodule.add_mem _ (h1 _ h2) ?_
    rw [hc, mul_assoc, ← map_mul, ← hr]
    exact Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) r, by rw [map_mul]; rfl⟩


omit [NumberField E] [NumberField K] [Fintype ι] in
theorem invTrK_embGL_apply {n : ℕ} (γ : GL (Fin n) E) (τ : ι) (a b : Fin n) :
    ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      emb τ (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b a) := by
  simp only [invTrK, inside₂, embGL, Formalism.UG.bc, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.pi_apply,
    transpose_apply, ← map_inv]
  rfl


omit [NumberField E] in
theorem brAt_rhoVr {N n : ℕ} (hN : N = n + 1) {lam : ι → DomWeight N} {sg : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (t : ι → K)
    (γ : GL (Fin n) E) (γ' : GL (Fin N) E)
    (h1 : ∀ x, iniH hN (((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) =
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x)
    (h2 : ∀ x, (((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) (G : Formalism.L2.DIV.VV K lam) :
    Br.brAt hN lam sg t (rhoVr emb lam γ' G) = rhoVr emb sg γ (Br.brAt hN lam sg t G) := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have key := GlobalTheory.BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL emb γ)) (invTrK (embGL emb γ'))
    (fun τ => by
      simp only [invTrK_embGL_apply]
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
      · have h := congrFun (h1 (Pi.single (Br.iC hN a) 1)) b
        have e : iniH hN (Pi.single (Br.iC hN a) (1 : E)) = Pi.single a 1 := by
          funext i
          simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
        rw [e, mulVec_single_one, mulVec_single_one] at h
        exact congrArg _ h
      · have h := h2 (Pi.single (Br.iC hN a) 1)
        rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
        exact (congrArg _ h).trans (map_zero _)
      · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
        have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
        rw [e, mulVec_zero, mulVec_single_one] at h
        exact (congrArg _ h).trans (map_zero _)
      · have h := h2 (Pi.single (Br.iL hN) 1)
        rw [mulVec_single_one, Pi.single_eq_same] at h
        exact (congrArg _ h).trans (map_one _)) G
  rw [Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg _ key

variable [StarRing E] [StarRing K] (σ : K →+* ℂ)

theorem evV_rho {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (b : S.β) (g : S.G b) (v : Formalism.L2.DIV.VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm


omit [NumberField E] [NumberField K] [StarRing E] [StarRing K] in
theorem polOf_evV {n : ℕ} (lam : ι → DomWeight n) (v : Formalism.L2.DIV.VV K lam) :
    polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) =
      MvPolynomial.map σ v.1 := by
  have h := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (MvPolynomial.map σ v.1)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  rwa [e] at h

variable {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hc : ι → HCParam R)


omit [StarRing E] [StarRing K] in
theorem br_map (v : Formalism.L2.DIV.VV K (lamT hc R.m)) :
    Q.br emb σ hc (MvPolynomial.map σ v.1) =
      MvPolynomial.map σ (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) v).1 := by
  simp only [PerIn.br, Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem rho_mv_mem {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (x : S.FormsK emb lam h)
    (hx : x ∈ (S.hlat emb lam h).L) (b : S.β) (d : S.D b) :
    S.rho emb lam b (S.mv b d) (x.1 (S.cl b d)) ∈ delAtr emb lam (S.Lsh b d) := by
  have h1 : delAtr emb lam (S.Lsh b (S.mv b d • S.rep (S.cl b d))) =
      (delAtr emb lam (S.Lsh b (S.rep (S.cl b d)))).map ((S.rho emb lam b (S.mv b d)).restrictScalars (𝓞 K)) :=
    (h b).del_smul (S.mv b d) (S.rep (S.cl b d))
  rw [S.mv_smul] at h1
  rw [h1]
  exact Submodule.mem_map_of_mem (hx (S.cl b d))

theorem exists_image (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) (hI : I.Ok) (hQ : Q.Ok)
    (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ)) (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ))
    (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) (hx : x ∈ ((I.S R.m).hlat emb (lamT hc R.m) hF).L) :
    ∃ y ∈ (Q.S'.hlat emb Q.sgT hP).L, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → Formalism.L2.DIV.VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, fun c => ?_, funext fun c => ?_⟩
  · have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
        (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
    have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
      have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
      exact h3
    show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
    rw [← brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
      (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
      (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
    exact congrArg B h2
  · have h2 : v c ∈ delAtr emb (lamT hc R.m) ((I.S R.m).Lsh Q.b0 (Q.til c.1 (Q.S'.rep c))) :=
      rho_mv_mem emb (I.S R.m) (lamT hc R.m) hF x hx Q.b0 (Q.tilPt c)
    refine GlobalTheory.BranchFormula.integrality h6 K ι _ _ (N_m_succ R) _ _ hW hS _ _ (fun τ => (map_ne_zero _).2 hQ.tz_ne) _ ?_
    unfold delAtr at h2
    rwa [funext fun τ => dualFr_tauLat_sum emb (N_m_succ R) τ hQ.tz_ne _ _ (hQ.Lsh_til c.1 (Q.S'.rep c))] at h2
  · show _ = fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x.1 (Q.tilC c))))))
    rw [← evV_rho, polOf_evV, br_map]
    rfl


omit [StarRing K] in
theorem weights_ok (emb : ι → E →+* K) [StarRing K] (h : ∀ τ, Q.sg τ = (RowPar.of (hc τ)).sg) (τ : ι) :
    Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ) ∧ Br.SameShift (lamT hc R.m τ) (Q.sgT τ) := by
  classical
  let X : Fields := { F := ℚ, E := E, K := K, Tau := ι, emb := emb }
  let W : Wts X Unit R := ⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩
  have := GlobalTheory.BranchMembers.members X Unit R W
    ⟨fun τ => ⟨hc τ, rfl⟩, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩ () τ
  unfold PerIn.sgT
  rw [h τ]
  exact this

end General

variable {D : D7} {u : D.what₂.Word}

end GlobalTheory.LvT.BuiltChain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.SplitUnram

variable {E : Type} [Field E] [NumberField E]

theorem absNorm_span_invol (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) (a : 𝓞 E) :
    Ideal.absNorm (Ideal.span {s a}) = Ideal.absNorm (Ideal.span {a}) := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom s s (RingHom.ext hs) (RingHom.ext hs)
  let e' : 𝓞 E ≃ₐ[ℤ] 𝓞 E := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  exact congrArg Int.natAbs (Algebra.norm_eq_of_algEquiv e' a)

theorem natCast_notMem_sq : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E →+* 𝓞 E) (a : 𝓞 E) (p : ℕ),
    (∀ x, s (s x) = x) → p.Prime → a * s a = (p : 𝓞 E) → IsCoprime a (s a) →
    2 * (divs a).card = Module.finrank ℚ E → (∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) →
    ∀ P ∈ divs a, ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro E _ _ s a p hs hp ha hcop hcard hN P hP hmem
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hnorm : Ideal.absNorm (Ideal.span {a}) = p ^ (divs a).card := by
    have h1 : Ideal.absNorm (Ideal.span {a}) ^ 2 = (p ^ (divs a).card) ^ 2 := by
      rw [← pow_mul, mul_comm, hcard, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast, ← ha,
        ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_invol s hs, sq]
    exact Nat.pow_left_injective two_ne_zero h1
  have haP : a ∈ P.asIdeal := (mem_divs ha0 P).1 hP
  have ha2 : a ∈ P.asIdeal ^ 2 := by
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : a = u * a ^ 2 + v * (p : 𝓞 E) := by
      rw [← ha]
      linear_combination (-a) * huv
    rw [h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haP 2)) (Ideal.mul_mem_left _ _ hmem)
  have hd1 : P.asIdeal ^ 2 ∣ Ideal.span {a} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha2
  have hd2 : ∏ Q ∈ (divs a).erase P, Q.asIdeal ∣ Ideal.span {a} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
    · intro Q hQ
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (mem_divs ha0 Q).1 (Finset.mem_of_mem_erase hQ)
  have hc : IsCoprime (P.asIdeal ^ 2) (∏ Q ∈ (divs a).erase P, Q.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun Q hQ => ?_)
    exact HeightOneSpectrum.isCoprime_of_ne P Q (Finset.ne_of_mem_erase hQ).symm
  have hd := map_dvd Ideal.absNorm (hc.mul_dvd hd1 hd2)
  rw [hnorm, map_mul, map_pow, map_prod, hN P hP,
    Finset.prod_congr rfl (fun Q hQ => hN Q (Finset.mem_of_mem_erase hQ)), Finset.prod_const, ← pow_add,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have h3 := Finset.card_erase_add_one hP
  omega

end GlobalTheory.SplitUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem split_of_conj_ne₂ : ∀ (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (v : HeightOneSpectrum (𝓞 X.F)),
    X.Ok → conjPrime₂ P ≠ P → P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal = P.asIdeal * (conjPrime₂ P).asIdeal ∧
    ∀ Q : HeightOneSpectrum (𝓞 X.E), Q.asIdeal.under (𝓞 X.F) = v.asIdeal ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  intro X P v hX hP hv
  obtain rfl : P.under (𝓞 X.F) = v := HeightOneSpectrum.ext hv
  have key := GlobalTheory.MuConj.mem_above_iff hX.star_F hX.rankE P hP
  refine ⟨GlobalTheory.Mem.GoodPlace.map_eq_mul hX.rankE hP.symm ((key _).2 (Or.inr rfl)), fun Q => ?_⟩
  rw [← key Q]
  exact ⟨fun h => HeightOneSpectrum.ext h, fun h => congrArg HeightOneSpectrum.asIdeal h⟩

end GlobalTheory.ThetaMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubAddLeSpread
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT

theorem sub_add_le_spread {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    lam.w a - lam.w b + (N : ℤ) ≤ lam.spread := by
  have hN : 0 < N := a.pos
  have h1 : lam.w a ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.2 (Nat.zero_le _))
  have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b := lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  linarith

theorem alcoveAt_of_ok : ∀ (Z : Dat), Z.Ok → ∀ (u : Z.Pr.Word) (j : ℕ), j ≤ Z.R.m → AlcoveAt Z.W u j := by
  intro Z hZ u j hj τ a b
  have h1 := hZ.sizes.two_spread_lt u j hj τ
  have h2 := sub_add_le_spread (Z.W.lamTrue u j τ) a b
  linarith

end GlobalTheory.KerT
end

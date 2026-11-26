module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QInertHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ThetaSpanHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfSpan
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfTheta
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QSplitHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdemCases
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def QProd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal),
      ∀ c, e (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = (c, c)

theorem sq_mem (h : IsCMExt F E σ) (x : QE (E := E) v) (hx : sigQ σ v x = x) :
    ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
    rw [← sigQ_mk]; exact hx
  have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ h _)
  obtain ⟨b, hb⟩ := fix_int σ h (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]

theorem idem_cases {k : Type} [Field k] {a : k} (ha : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, ha, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

theorem qSplit_of (hP : QProd σ J ψ v) : QSplit σ J ψ v := by
  intro hstd hun hp
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨e, he⟩ := hP hstd hun hp
  refine ⟨e, ?_⟩
  set z : QE (E := E) v := e.symm (1, 0) with hz
  have hez : e z = (1, 0) := by rw [hz, RingEquiv.apply_symm_apply]
  have hinv : ∀ x, sigQ σ v (sigQ σ v x) = x := sigQ_sigQ σ v hstd.1
  have hw : e (sigQ σ v z) = (0, 1) := by
    have hzz : z * z = z := e.injective (by rw [map_mul, hez]; simp)
    have hid : e (sigQ σ v z) * e (sigQ σ v z) = e (sigQ σ v z) := by rw [← map_mul, ← map_mul, hzz]
    have h1 := idem_cases ((Prod.fst_mul _ _).symm.trans (congrArg Prod.fst hid))
    have h2 := idem_cases ((Prod.snd_mul _ _).symm.trans (congrArg Prod.snd hid))
    have h10 : ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).1 ≠ ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).2 :=
      one_ne_zero
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      have h0 : sigQ σ v z = 0 := (map_eq_zero_iff e e.injective).1 (Prod.ext h1 h2)
      have : e z = 0 := by rw [← hinv z, h0, map_zero, map_zero]
      rw [hez] at this
      exact one_ne_zero (congrArg Prod.fst this)
    · exact Prod.ext h1 h2
    · exfalso
      have hf : sigQ σ v z = z := e.injective (by rw [hez]; exact Prod.ext h1 h2)
      obtain ⟨c, hc⟩ := sq_mem σ v hstd.1 z hf
      rw [hzz] at hc
      have := he c
      rw [hc, hez] at this
      apply h10
      rw [this]
    · exfalso
      have h0 : sigQ σ v z = 1 := e.injective (by rw [map_one]; exact Prod.ext h1 h2)
      have : e z = 1 := by rw [← hinv z, h0, map_one, map_one]
      rw [hez] at this
      exact zero_ne_one (congrArg Prod.snd this)
  intro x
  have hx : x = algebraMap _ (QE (E := E) v) (e x).1 * z + algebraMap _ (QE (E := E) v) (e x).2 * (1 - z) := by
    apply e.injective
    rw [map_add (f := _), map_mul, map_mul, he, he, map_sub, map_one, hez]
    ext <;> simp
  have key : e (sigQ σ v x) = ((e x).2, (e x).1) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, map_mul, sigQ_alg, sigQ_alg, map_sub, map_one, map_add (f := _), map_mul, map_mul, he, he,
      map_sub, map_one, hw]
    ext <;> simp
  rw [key]
  rfl

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

set_option linter.deprecated false

theorem card_QE (h : IsCMExt F E σ) [Finite (𝓞 F ⧸ v.asIdeal)] :
    Nat.card (QE (E := E) v) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ 2 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
    rw [← h.2.2.1]
    exact Ideal.finrank_quotient_map v.asIdeal F E
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (QE (E := E) v)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := QE (E := E) v), hr]

def gP (P : Ideal (𝓞 E)) (hP : IE (E := E) v ≤ P) : 𝓞 F ⧸ v.asIdeal →+* 𝓞 E ⧸ P :=
  Ideal.quotientMap P (algebraMap (𝓞 F) (𝓞 E)) (Ideal.map_le_iff_le_comap.1 hP)

theorem bij_of_card {A B : Type} [Finite A] [Finite B] (f : A → B) (hf : Function.Injective f)
    (hc : Nat.card A = Nat.card B) : Function.Bijective f := by
  exact hf.bijective_of_nat_card_le hc.ge

theorem qProd_holds : QProd σ J ψ v := by
  intro hS hU hnp
  have hcm : IsCMExt F E σ := hS.1
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hI : IE (E := E) v ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  set ι := (UniqueFactorizationMonoid.factors (IE (E := E) v)).toFinset with hι
  have hmem : ∀ P : ι, (P : Ideal (𝓞 E)) ∈ UniqueFactorizationMonoid.factors (IE (E := E) v) :=
    fun P => Multiset.mem_toFinset.mp P.2
  have hprime : ∀ P : ι, (P : Ideal (𝓞 E)).IsPrime :=
    fun P => Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor _ (hmem P))
  have hne : ∀ P : ι, (P : Ideal (𝓞 E)) ≠ ⊥ :=
    fun P => (UniqueFactorizationMonoid.prime_of_factor _ (hmem P)).ne_zero
  have hle : ∀ P : ι, IE (E := E) v ≤ (P : Ideal (𝓞 E)) :=
    fun P => Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors (hmem P))
  have hcomap : ∀ P : ι,
      Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (P : Ideal (𝓞 E)) = v.asIdeal := by
    intro P
    haveI := hprime P
    exact (v.isMaximal.eq_of_le (Ideal.IsPrime.comap _).ne_top
      (Ideal.map_le_iff_le_comap.mp (hle P))).symm
  have hcount : ∀ P : ι, (P : Ideal (𝓞 E)) ^ Multiset.count (P : Ideal (𝓞 E))
      (UniqueFactorizationMonoid.factors (IE (E := E) v)) = P := by
    intro P
    haveI := hprime P
    haveI : (P : Ideal (𝓞 E)).LiesOver v.asIdeal := ⟨(hcomap P).symm⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count v.asIdeal (P : Ideal (𝓞 E)) hI,
      hU P (hprime P) (hne P) (hcomap P), pow_one]
  let eqv : QE (E := E) v ≃+* ∀ P : ι, 𝓞 E ⧸ (P : Ideal (𝓞 E)) :=
    (IsDedekindDomain.quotientEquivPiFactors hI).trans
      (RingEquiv.piCongrRight fun P => Ideal.quotEquivOfEq (hcount P))
  have heqv : ∀ (y : 𝓞 E) (P : ι), eqv (Ideal.Quotient.mk _ y) P = Ideal.Quotient.mk _ y :=
    fun y P => rfl
  haveI hfinE : ∀ P : ι, Finite (𝓞 E ⧸ (P : Ideal (𝓞 E))) :=
    fun P => Ideal.finiteQuotientOfFreeOfNeBot _ (hne P)
  haveI : Finite (QE (E := E) v) := Finite.of_equiv _ eqv.symm.toEquiv
  have hinj : ∀ P : ι, Function.Injective (gP v (P : Ideal (𝓞 E)) (hle P)) := by
    intro P
    haveI := hprime P
    exact (gP v _ (hle P)).injective
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hq2 : 1 < q := Finite.one_lt_card
  have hcardP : ∀ P : ι, q ≤ Nat.card (𝓞 E ⧸ (P : Ideal (𝓞 E))) :=
    fun P => Nat.card_le_card_of_injective _ (hinj P)
  have hprod : ∏ P : ι, Nat.card (𝓞 E ⧸ (P : Ideal (𝓞 E))) = q ^ 2 := by
    rw [← Nat.card_pi, ← Nat.card_congr eqv.toEquiv, card_QE σ v hcm]
  have hn : Fintype.card ι = 2 := by
    have hpow : q ^ Fintype.card ι ≤ q ^ 2 := by
      rw [← hprod]
      calc q ^ Fintype.card ι = ∏ _P : ι, q := by rw [Finset.prod_const, Finset.card_univ]
        _ ≤ _ := Finset.prod_le_prod' fun P _ => hcardP P
    rcases Nat.lt_or_ge (Fintype.card ι) 2 with hlt | hge
    · exfalso
      interval_cases hc : Fintype.card ι
      · haveI := Fintype.card_eq_zero_iff.mp hc
        rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
        nlinarith
      · obtain ⟨P0, hP0⟩ := Fintype.card_eq_one_iff.mp hc
        apply hnp
        haveI := hprime P0
        have h0 : ∀ z : 𝓞 E, z ∈ IE (E := E) v ↔
            Ideal.Quotient.mk (P0 : Ideal (𝓞 E)) z = 0 := by
          intro z
          rw [← Ideal.Quotient.eq_zero_iff_mem (I := IE (E := E) v)]
          constructor
          · intro hz
            have := congrArg (fun w => eqv w P0) hz
            simpa only [heqv, map_zero, Pi.zero_apply] using this
          · intro hz
            apply eqv.injective
            rw [map_zero]
            funext P
            obtain rfl := hP0 P
            rw [heqv, hz, Pi.zero_apply]
        rw [Ideal.isPrime_iff]
        refine ⟨fun h => (hprime P0).ne_top (top_le_iff.mp (h ▸ hle P0)), ?_⟩
        intro x y hxy
        rw [h0, map_mul] at hxy
        rw [h0, h0]
        exact mul_eq_zero.mp hxy
    · by_contra hne2
      have h3 : 3 ≤ Fintype.card ι := by omega
      have h4 : q ^ 3 ≤ q ^ Fintype.card ι := Nat.pow_le_pow_right (by omega) h3
      have h5 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hq2 (by norm_num)
      linarith
  let eι := Fintype.equivFinOfCardEq hn
  have hfin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  have hall : ∀ P : ι, P = eι.symm 0 ∨ P = eι.symm 1 := by
    intro P
    rcases hfin2 (eι P) with h | h
    · left; rw [← h, Equiv.symm_apply_apply]
    · right; rw [← h, Equiv.symm_apply_apply]
  have hprod2 : Nat.card (𝓞 E ⧸ ((eι.symm 0 : ι) : Ideal (𝓞 E))) *
      Nat.card (𝓞 E ⧸ ((eι.symm 1 : ι) : Ideal (𝓞 E))) = q ^ 2 := by
    rw [← hprod, ← eι.symm.prod_comp, Fin.prod_univ_two]
  have hc0 := hcardP (eι.symm 0)
  have hc1 := hcardP (eι.symm 1)
  have hcq : ∀ P : ι, Nat.card (𝓞 E ⧸ (P : Ideal (𝓞 E))) = q := by
    intro P
    rcases hall P with rfl | rfl
    · nlinarith
    · nlinarith
  let eP : ∀ P : ι, (𝓞 F ⧸ v.asIdeal) ≃+* 𝓞 E ⧸ (P : Ideal (𝓞 E)) := fun P =>
    RingEquiv.ofBijective (gP v _ (hle P)) (bij_of_card _ (hinj P) (hcq P).symm)
  let φ : QE (E := E) v →+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) :=
    RingHom.prod
      (((eP (eι.symm 0)).symm : _ →+* _).comp
        ((Pi.evalRingHom (fun P : ι => 𝓞 E ⧸ (P : Ideal (𝓞 E))) (eι.symm 0)).comp
          (eqv : QE (E := E) v →+* _)))
      (((eP (eι.symm 1)).symm : _ →+* _).comp
        ((Pi.evalRingHom (fun P : ι => 𝓞 E ⧸ (P : Ideal (𝓞 E))) (eι.symm 1)).comp
          (eqv : QE (E := E) v →+* _)))
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h0 : eqv a (eι.symm 0) = eqv b (eι.symm 0) :=
      (eP (eι.symm 0)).symm.injective (congrArg Prod.fst hab)
    have h1 : eqv a (eι.symm 1) = eqv b (eι.symm 1) :=
      (eP (eι.symm 1)).symm.injective (congrArg Prod.snd hab)
    apply eqv.injective
    funext P
    rcases hall P with rfl | rfl
    · exact h0
    · exact h1
  have hbij : Function.Bijective φ :=
    bij_of_card φ hφinj (by rw [Nat.card_prod, card_QE σ v hcm, sq])
  refine ⟨RingEquiv.ofBijective φ hbij, fun c => ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h1 := Ideal.Quotient.algebraMap_quotient_map_quotient (S := 𝓞 E) (p := v.asIdeal) f
  rw [RingEquiv.ofBijective_apply]
  refine Prod.ext ?_ ?_
  · show (eP (eι.symm 0)).symm (eqv (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)
      (Ideal.Quotient.mk v.asIdeal f)) (eι.symm 0)) = _
    rw [RingEquiv.symm_apply_eq]
    rw [show algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk v.asIdeal f) =
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f) from h1, heqv]
    rfl
  · show (eP (eι.symm 1)).symm (eqv (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)
      (Ideal.Quotient.mk v.asIdeal f)) (eι.symm 1)) = _
    rw [RingEquiv.symm_apply_eq]
    rw [show algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk v.asIdeal f) =
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f) from h1, heqv]
    rfl

theorem qSplit_holds : QSplit σ J ψ v := qSplit_of σ J ψ v (qProd_holds σ J ψ v)

private theorem sigma_sigma_eq_of_isCMExt (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hc⟩ := h
  let τ : E →+* ℂ := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
  apply τ.injective
  rw [hc, hc, star_star]

theorem resAlg_of' (hQ : ResQ σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v := by
  intro hS hU ϖ hϖ
  have hcm : IsCMExt F E σ := hS.1
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨ρ, hρ⟩ := hQ hS hU ϖ hϖ
  have hη : etaV (E := E) v = 1 ∨ etaV (E := E) v = -1 := by
    unfold etaV
    split_ifs <;> simp
  have hlink := hE hS hU
  have hcardk : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨𝓞 F ⧸ v.asIdeal, inferInstance, inferInstance, hcardk, ?_⟩
  by_cases hp : (IE (E := E) v).IsPrime
  · left
    have hm1 : etaV (E := E) v = -1 := by
      rcases hη with h | h
      · exact absurd hp (hlink.mp h)
      · exact h
    refine ⟨hm1, ?_⟩
    haveI : (IE (E := E) v).IsMaximal := hp.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
    letI : Field (QE (E := E) v) := Ideal.Quotient.field _
    have hinv : ∀ z, sigQ σ v (sigQ σ v z) = z := by
      intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [sigQ, Ideal.quotientMap_mk]
      congr 1
      apply RingOfIntegers.ext
      exact sigma_sigma_eq_of_isCMExt σ hcm (y : E)
    have hfixc : ∀ c, sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) =
        algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c := by
      intro c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
      have h1 := Ideal.Quotient.algebraMap_quotient_map_quotient (S := 𝓞 E) (p := v.asIdeal) f
      have h2 : sigO σ (algebraMap (𝓞 F) (𝓞 E) f) = algebraMap (𝓞 F) (𝓞 E) f := by
        apply RingOfIntegers.ext
        exact σ.commutes (f : F)
      calc sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk v.asIdeal f))
          = sigQ σ v (Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f)) := congrArg _ h1
        _ = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) f) := by
            simp only [sigQ, Ideal.quotientMap_mk, h2]
        _ = _ := h1.symm
    let s : QE (E := E) v ≃ₐ[𝓞 F ⧸ v.asIdeal] QE (E := E) v :=
      { sigQ σ v with
        invFun := sigQ σ v
        left_inv := hinv
        right_inv := hinv
        commutes' := hfixc }
    have hr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
      rw [← hcm.2.2.1]
      exact Ideal.finrank_quotient_map v.asIdeal F E
    refine ⟨QE (E := E) v, inferInstance, inferInstance, s, ρ, fun x => hinv x, hr, ?_, hρ⟩
    intro hs
    have hfix : ∀ x, sigQ σ v x = x := fun x => AlgEquiv.ext_iff.mp hs x
    have hsq : ∀ x : QE (E := E) v, ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x :=
      fun x => sq_mem σ v hcm x (hfix x)
    have hall : ∀ x : QE (E := E) v, ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x := by
      by_cases h2 : (2 : QE (E := E) v) = 0
      · haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) :=
          Module.finite_of_finrank_pos (by rw [hr]; norm_num)
        haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
        have hinjsq : Function.Injective (fun y : QE (E := E) v => y * y) := by
          intro a b hab
          have hab' : a * a = b * b := hab
          have h3 : (a - b) * (a - b) = 0 := by
            have e1 : (a - b) * (a - b) = a * a - b * b - 2 * b * (a - b) := by ring
            rw [e1, hab', h2]
            ring
          exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
        intro x
        obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinjsq x
        obtain ⟨c, hc⟩ := hsq y
        exact ⟨c, hc.trans hy⟩
      · intro x
        obtain ⟨c0, hc0⟩ := hsq x
        obtain ⟨c1, hc1⟩ := hsq (x + 1)
        refine ⟨(c1 - c0 - 1) * 2⁻¹, ?_⟩
        have hx2 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (c1 - c0 - 1) = 2 * x := by
          rw [map_sub, map_sub, map_one, hc0, hc1]
          ring
        rw [map_mul, map_inv₀, hx2, map_ofNat, mul_comm]
        exact inv_mul_cancel_left₀ h2 x
    have hle1 : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) ≤ 1 :=
      finrank_le_one (1 : QE (E := E) v) (fun w => by
        obtain ⟨c, hc⟩ := hall w
        exact ⟨c, by rw [← Algebra.algebraMap_eq_smul_one, hc]⟩)
    omega
  · right
    refine ⟨hlink.mpr hp, ?_⟩
    obtain ⟨e, he⟩ := qSplit_holds σ J ψ v hS hU hp
    refine ⟨(e : QE (E := E) v →+* _).comp ρ, ?_, ?_, ?_⟩
    · exact e.surjective.comp hρ.1
    · intro x
      rw [← hρ.2.1 x]
      show e (ρ x) = 0 ↔ ρ x = 0
      exact map_eq_zero_iff _ e.injective
    · intro x y hxy
      show e (ρ y) = RingEquiv.prodComm (e (ρ x))
      rw [hρ.2.2 x y hxy, he]
      rfl

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def redR : v.adicCompletionIntegers F →+* 𝓞 F ⧸ v.asIdeal where
  toFun x := red v (x : Fv F v)
  map_one' := red_one v
  map_mul' x y := red_mul v x.2 y.2
  map_zero' := red_zero v
  map_add' x y := red_add v x.2 y.2

theorem redR_surj : Function.Surjective (redR v) := fun t => by
  obtain ⟨x, hx, h⟩ := red_surj v t
  exact ⟨⟨x, hx⟩, h⟩

theorem sc_eq' (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem inclR_alg' (a : F) :
    inclR (F := F) (Fv F v) (algebraMap F E a) = sc (E := E) v (algebraMap F (Fv F v) a) := by
  rw [sc_eq', ← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes a

theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (c ⊗ₜ (1 : E)) = c ⊗ₜ (1 : E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem sigR_incl (e : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ e) = (1 : Fv F v) ⊗ₜ σ e
  rw [Algebra.TensorProduct.map_tmul]
  rfl

def ThetaBas : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∃ θ : 𝓞 E,
    (∀ x ∈ OEv (E := E) v, ∃ a0 a1 : v.adicCompletionIntegers F,
      x = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * inclR (F := F) (Fv F v) (θ : E)) ∧
    (∀ a0 a1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * inclR (F := F) (Fv F v) (θ : E) = 0 →
      a0 = 0 ∧ a1 = 0) ∧
    (∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) ∧
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ)

theorem resQ_of (hT : ThetaBas σ J ψ v) : ResQ σ J ψ v := by
  intro hstd hun ϖ hϖ
  obtain ⟨θ, h1, h2, h3, h4⟩ := hT hstd hun
  set iθ : Fv F v ⊗[F] E := inclR (F := F) (Fv F v) (θ : E) with hiθ
  have hss : sigO σ (sigO σ θ) = θ := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
  obtain ⟨t, ht⟩ := fix_int σ hstd.1 (θ + sigO σ θ) (by rw [map_add (f := _), hss, add_comm])
  obtain ⟨m, hm⟩ := fix_int σ hstd.1 (θ * sigO σ θ) (by rw [map_mul, hss, mul_comm])
  have hθ2 : θ * θ = algebraMap (𝓞 F) (𝓞 E) t * θ - algebraMap (𝓞 F) (𝓞 E) m := by
    rw [ht, hm]; ring
  have hσθ : sigO σ θ = algebraMap (𝓞 F) (𝓞 E) t - θ := by rw [ht]; ring
  have hinc : ∀ a : 𝓞 F, inclR (F := F) (Fv F v) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) =
      sc (E := E) v (iO v a) := fun a => inclR_alg' v (a : F)
  have hiθ2 : iθ * iθ = sc (E := E) v (iO v t) * iθ - sc (E := E) v (iO v m) := by
    have e1 := congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hθ2
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, map_mul, map_sub, hinc] at e1
    exact e1
  have hsiθ : sigR (Fv F v) σ iθ = sc (E := E) v (iO v t) - iθ := by
    have e1 := congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hσθ
    simp only [AddSubgroupClass.coe_sub, map_sub, hinc, sigO_coe] at e1
    rw [hiθ, sigR_incl]
    exact e1
  let T0 : v.adicCompletionIntegers F := ⟨iO v t, mem_O_iO v t⟩
  let M0 : v.adicCompletionIntegers F := ⟨iO v m, mem_O_iO v m⟩
  have huniq : ∀ a0 a1 b0 b1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * iθ =
      sc (E := E) v b0 + sc (E := E) v b1 * iθ → a0 = b0 ∧ a1 = b1 := by
    intro a0 a1 b0 b1 h
    have := h2 (a0 - b0) (a1 - b1) (by simp only [sc_eq', map_sub] at h ⊢; linear_combination h)
    exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩
  choose c0 c1 hc using fun x : OR (E := E) v => h1 (x : Fv F v ⊗[F] E) x.2
  have hco : ∀ (x : OR (E := E) v) (a0 a1 : v.adicCompletionIntegers F),
      (x : Fv F v ⊗[F] E) = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * iθ →
      c0 x = a0 ∧ c1 x = a1 := by
    intro x a0 a1 h
    have := huniq _ _ _ _ ((hc x).symm.trans h)
    exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  let g : 𝓞 F ⧸ v.asIdeal →+* QE (E := E) v := algebraMap _ _
  let θb : QE (E := E) v := Ideal.Quotient.mk (IE (E := E) v) θ
  let ρf : OR (E := E) v → QE (E := E) v := fun x => g (redR v (c0 x)) + g (redR v (c1 x)) * θb
  have hρ : ∀ (x : OR (E := E) v) (a0 a1 : v.adicCompletionIntegers F),
      (x : Fv F v ⊗[F] E) = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * iθ →
      ρf x = g (redR v a0) + g (redR v a1) * θb := by
    intro x a0 a1 h
    obtain ⟨e0, e1⟩ := hco x a0 a1 h
    simp only [ρf, e0, e1]
  have hgt : ∀ a : 𝓞 F, g (redR v ⟨iO v a, mem_O_iO v a⟩) =
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) a) := by
    intro a
    show algebraMap _ _ (red v (iO v a)) = _
    rw [red_iO, Ideal.Quotient.algebraMap_quotient_map_quotient]
  have hQθ : θb * θb = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) * θb -
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) m) := by
    simp only [θb]
    rw [← map_mul, ← map_mul, ← map_sub, hθ2]
  let ρ : OR (E := E) v →+* QE (E := E) v :=
    { toFun := ρf
      map_one' := by
        rw [hρ 1 1 0 (by simp only [sc_eq', OneMemClass.coe_one, ZeroMemClass.coe_zero, map_one, map_zero,
          zero_mul, add_zero])]
        simp
      map_mul' := fun x y => by
        rw [hρ (x * y) (c0 x * c0 y - c1 x * c1 y * M0) (c0 x * c1 y + c1 x * c0 y + c1 x * c1 y * T0) ?_]
        · show _ = ρf x * ρf y
          simp only [ρf, map_add (f := _), map_sub, map_mul, T0, M0, hgt]
          linear_combination (-(g (redR v (c1 x)) * g (redR v (c1 y)))) * hQθ
        · show (x : Fv F v ⊗[F] E) * (y : Fv F v ⊗[F] E) = _
          rw [hc x, hc y]
          simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, AddMemClass.coe_add, sc_eq', map_mul, map_sub,
            map_add, T0, M0] at hiθ2 ⊢
          linear_combination (algebraMap (Fv F v) (Fv F v ⊗[F] E) (c1 x) *
            algebraMap (Fv F v) (Fv F v ⊗[F] E) (c1 y)) * hiθ2
      map_zero' := by
        rw [hρ 0 0 0 (by simp only [sc_eq', ZeroMemClass.coe_zero, map_zero, zero_mul, add_zero])]
        simp
      map_add' := fun x y => by
        rw [hρ (x + y) (c0 x + c0 y) (c1 x + c1 y) ?_]
        · show _ = ρf x + ρf y
          simp only [ρf, map_add (f := _)]
          ring
        · show (x : Fv F v ⊗[F] E) + (y : Fv F v ⊗[F] E) = _
          rw [hc x, hc y]
          simp only [AddMemClass.coe_add, sc_eq', map_add (f := _)]
          ring }
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨a0, a1, rfl⟩ := h4 q
    obtain ⟨b0, rfl⟩ := redR_surj v a0
    obtain ⟨b1, rfl⟩ := redR_surj v a1
    have m0 : sc (E := E) v (b0 : Fv F v) ∈ OEv (E := E) v := by
      simpa using sc_mul_mem_oEv v b0.2 (Orb.oSub (E := E) v).1
    have m1 : sc (E := E) v (b1 : Fv F v) * iθ ∈ OEv (E := E) v := sc_mul_mem_oEv v b1.2 (Orb.gen_mem v θ)
    exact ⟨⟨_, Orb.oev_add v m0 m1⟩, hρ _ b0 b1 rfl⟩
  · intro x
    have hρx : ρ x = g (redR v (c0 x)) + g (redR v (c1 x)) * θb := rfl
    have hz : ∀ c : v.adicCompletionIntegers F, redR v c = 0 ↔ ∃ d : v.adicCompletionIntegers F,
        (c : Fv F v) = ϖ * d := by
      intro c
      show red v (c : Fv F v) = 0 ↔ _
      rw [red_eq_zero_iff v c.2, ← mem_unifO_iff v hϖ c]
      rfl
    have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
      show Valued.v ϖ ≤ 1
      rw [show Valued.v ϖ = _ from hϖ]
      exact le_of_lt (by decide)
    rw [hρx]
    constructor
    · intro h0
      obtain ⟨z0, z1⟩ := h3 _ _ h0
      obtain ⟨d0, hd0⟩ := (hz _).1 z0
      obtain ⟨d1, hd1⟩ := (hz _).1 z1
      refine ⟨sc (E := E) v (d0 : Fv F v) + sc (E := E) v (d1 : Fv F v) * iθ,
        Orb.oev_add v (by simpa using sc_mul_mem_oEv v d0.2 (Orb.oSub (E := E) v).1)
          (sc_mul_mem_oEv v d1.2 (Orb.gen_mem v θ)), ?_⟩
      rw [hc x, hd0, hd1]
      simp only [sc_eq', map_mul]
      ring
    · rintro ⟨o, ho, hxo⟩
      obtain ⟨d0, d1, hd⟩ := h1 o ho
      have hx' : (x : Fv F v ⊗[F] E) = sc (E := E) v (ϖ * d0) + sc (E := E) v (ϖ * d1) * iθ := by
        rw [hxo, hd]; simp only [sc_eq', map_mul]; ring
      obtain ⟨e0, e1⟩ := huniq _ _ _ _ ((hc x).symm.trans hx')
      rw [(hz _).2 ⟨d0, e0⟩, (hz _).2 ⟨d1, e1⟩]
      simp
  · intro x y hxy
    have hy : (y : Fv F v ⊗[F] E) = sc (E := E) v ((c0 x + c1 x * T0 : v.adicCompletionIntegers F) : Fv F v) +
        sc (E := E) v ((-c1 x : v.adicCompletionIntegers F) : Fv F v) * iθ := by
      rw [hxy, hc x, map_add (f := _), map_mul, sigR_sc, sigR_sc, hsiθ]
      simp only [AddMemClass.coe_add, MulMemClass.coe_mul, NegMemClass.coe_neg, sc_eq', map_add (f := _), map_mul, map_neg, T0]
      ring
    show ρf y = sigQ σ v (ρf x)
    rw [hρ y _ _ hy]
    simp only [ρf, map_add (f := _), map_mul, map_neg, hgt, sigQ_alg]
    have hsq : sigQ σ v θb = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) - θb := by
      simp only [θb]
      rw [sigQ_mk, hσθ, map_sub]
    rw [hsq]
    have hsg : ∀ c, sigQ σ v (g c) = g c := fun c => sigQ_alg σ v c
    simp only [hsg]
    rw [show g (redR v T0) = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) from hgt t]
    ring

theorem resAlg_of_theta (hT : ThetaBas σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of' σ J ψ v (resQ_of σ J ψ v hT) hE

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

set_option linter.deprecated false

def ThetaSpan : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ θ : 𝓞 E,
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ) →
    ∀ x ∈ OEv (E := E) v, ∃ a0 a1 : v.adicCompletionIntegers F,
      x = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * inclR (F := F) (Fv F v) (θ : E)

theorem theta_exists (h : IsCMExt F E σ) : ∃ θ : 𝓞 E,
    (∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) ∧
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ) := by
  classical
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finite_res v
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hcard : Nat.card (QE (E := E) v) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ 2 := card_QE σ v h
  have hk : 1 < Nat.card (𝓞 F ⧸ v.asIdeal) := Finite.one_lt_card
  have hpos : Nat.card (QE (E := E) v) ≠ 0 := by
    rw [hcard]
    positivity
  haveI : Finite (QE (E := E) v) := Nat.finite_of_card_ne_zero hpos
  haveI : Nontrivial (QE (E := E) v) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    nlinarith
  have hx : ∃ x : QE (E := E) v, x ∉ Set.range (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)) := by
    by_contra hne
    push_neg at hne
    have hs : Function.Surjective (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)) := fun y => hne y
    have hle := Nat.card_le_card_of_surjective _ hs
    rw [hcard] at hle
    nlinarith
  obtain ⟨x, hx⟩ := hx
  obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hind : ∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0 := by
    intro a0 a1 h0
    by_cases ha1 : a1 = 0
    · subst ha1
      simp only [map_zero, zero_mul, add_zero] at h0
      exact ⟨(algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)).injective (by rw [h0, map_zero]), rfl⟩
    · exfalso
      apply hx
      refine ⟨-(a0 * a1⁻¹), ?_⟩
      have hinv : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1⁻¹ *
          algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ha1, map_one]
      rw [map_neg, map_mul]
      linear_combination (-(algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1⁻¹)) * h0 +
        (Ideal.Quotient.mk (IE (E := E) v) θ) * hinv
  refine ⟨θ, hind, ?_⟩
  let f : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) → QE (E := E) v := fun p =>
    algebraMap _ (QE (E := E) v) p.1 + algebraMap _ (QE (E := E) v) p.2 * Ideal.Quotient.mk (IE (E := E) v) θ
  have hinj : Function.Injective f := by
    intro p p' hpp
    have h0 := hind (p.1 - p'.1) (p.2 - p'.2) (by
      simp only [f] at hpp
      rw [map_sub, map_sub]
      linear_combination hpp)
    exact Prod.ext (sub_eq_zero.mp h0.1) (sub_eq_zero.mp h0.2)
  have hbij := bij_of_card f hinj (by rw [Nat.card_prod, hcard, sq])
  intro q
  obtain ⟨p, hp⟩ := hbij.2 q
  exact ⟨p.1, p.2, hp.symm⟩

theorem theta_indep (h : IsCMExt F E σ) (θ : 𝓞 E)
    (h3 : ∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) :
    ∀ a0 a1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * inclR (F := F) (Fv F v) (θ : E) = 0 →
      a0 = 0 ∧ a1 = 0 := by
  classical
  intro a0 a1 h0
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hθ : ∀ f : F, algebraMap F E f ≠ (θ : E) := by
    intro f hf
    have hint : IsIntegral ℤ f := (isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom)
        (algebraMap F E).injective).mp (by
      show IsIntegral ℤ (algebraMap F E f)
      rw [hf]
      exact RingOfIntegers.isIntegral_coe θ)
    have hg : θ = algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩ := by
      apply RingOfIntegers.ext
      rw [← hf]
      rfl
    have hz := h3 (-(Ideal.Quotient.mk _ ⟨f, hint⟩)) 1 (by
      rw [map_neg, map_one, one_mul, hg]
      show -Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩) +
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩) = 0
      exact neg_add_cancel _)
    exact one_ne_zero hz.2
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
      exact ⟨(algebraMap F E).injective (by rw [hst, map_zero]), rfl⟩
    · exfalso
      apply hθ (-(s * t⁻¹))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have hinv : algebraMap F E t⁻¹ * algebraMap F E t = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ht, map_one]
      rw [map_neg, map_mul]
      linear_combination (-(algebraMap F E t⁻¹)) * hst + (θ : E) * hinv
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h.2.2.1])
  let b' := Algebra.TensorProduct.basis (Fv F v) b
  have hb : ![(1 : Fv F v) ⊗ₜ[F] (1 : E), (1 : Fv F v) ⊗ₜ[F] (θ : E)] = ⇑b' := by
    ext i
    fin_cases i <;>
      simp [b', b, Algebra.TensorProduct.basis_apply, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hli' : LinearIndependent (Fv F v) ![(1 : Fv F v) ⊗ₜ[F] (1 : E), (1 : Fv F v) ⊗ₜ[F] (θ : E)] := by
    rw [hb]
    exact b'.linearIndependent
  apply LinearIndependent.pair_iff.mp hli' a0 a1
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [← h0]
  simp [sc, inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem thetaBas_of (hS : ThetaSpan σ J ψ v) : ThetaBas σ J ψ v := fun hstd hun => by
  obtain ⟨θ, h3, h4⟩ := theta_exists σ v hstd.1
  exact ⟨θ, hS hstd hun θ h4, theta_indep σ v hstd.1 θ h3, h3, h4⟩

theorem resAlg_of_span (hS : ThetaSpan σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_theta σ J ψ v (thetaBas_of σ J ψ v hS) hE

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem ov_smul (a : v.adicCompletionIntegers F) (y : Fv F v ⊗[F] E) :
    a • y = sc (E := E) v (a : Fv F v) * y := by
  rw [← smul_eq_sc]; rfl

theorem iO_max (p : 𝓞 F) (hp : p ∈ v.asIdeal) :
    (⟨iO v p, mem_O_iO v p⟩ : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v p).mpr hp
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at h1
  exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))).mpr h1

theorem thetaSpan_holds : ThetaSpan σ J ψ v := by
  intro _ _ θ hsp x hx
  classical
  let ι : 𝓞 E →+* Fv F v ⊗[F] E := (inclR (F := F) (Fv F v)).comp (algebraMap (𝓞 E) E)
  let Nt : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span _ (ι '' Set.range (RingOfIntegers.basis E))
  let M : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span _ {(1 : Fv F v ⊗[F] E), inclR (F := F) (Fv F v) (θ : E)}
  have halg : ∀ b : 𝓞 F, ι (algebraMap (𝓞 F) (𝓞 E) b) = sc (E := E) v (iO v b) := by
    intro b
    show inclR (F := F) (Fv F v) (algebraMap F E (b : F)) = _
    rw [inclR_alg']
  have hN : ∀ y : 𝓞 E, ι y ∈ Nt := by
    intro y
    have hy : y ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by
      rw [(RingOfIntegers.basis E).span_eq]
      trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => rw [map_zero]; exact Nt.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Nt.add_mem ha hb
    | smul n a _ ha => rw [map_zsmul]; exact zsmul_mem ha n
  have hI : ∀ w ∈ IE (E := E) v, ∀ c : 𝓞 E,
      ι (c * w) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • Nt := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, hp, rfl⟩ := hz
      intro c
      have hs := (ov_smul (E := E) v (⟨iO v p, mem_O_iO v p⟩ : v.adicCompletionIntegers F) (ι c)).symm
      rw [map_mul, halg, mul_comm]
      rw [hs]
      exact Submodule.smul_mem_smul (iO_max v p hp) (hN c)
    | zero => intro c; rw [mul_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => intro c; rw [mul_add, map_add (f := _)]; exact Submodule.add_mem _ (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact ha (c * d)
  have hNM : Nt ≤ M ⊔ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • Nt := by
    rw [Submodule.span_le]
    rintro _ ⟨y, _, rfl⟩
    obtain ⟨a0, a1, hq⟩ := hsp (Ideal.Quotient.mk (IE (E := E) v) y)
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective a0
    obtain ⟨b1, rfl⟩ := Ideal.Quotient.mk_surjective a1
    have e0 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk _ b0) =
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) b0) := rfl
    have e1 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk _ b1) =
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) b1) := rfl
    have hw : y - algebraMap (𝓞 F) (𝓞 E) b0 - algebraMap (𝓞 F) (𝓞 E) b1 * θ ∈ IE (E := E) v := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, map_mul, hq, e0, e1]
      ring
    have hy : ι y = ((⟨iO v b0, mem_O_iO v b0⟩ : v.adicCompletionIntegers F) • (1 : Fv F v ⊗[F] E) +
        (⟨iO v b1, mem_O_iO v b1⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (θ : E)) +
        ι (1 * (y - algebraMap (𝓞 F) (𝓞 E) b0 - algebraMap (𝓞 F) (𝓞 E) b1 * θ)) := by
      rw [ov_smul, ov_smul, mul_one]
      show _ = sc (E := E) v (iO v b0) + sc (E := E) v (iO v b1) * ι θ + _
      rw [← halg, ← halg, ← map_mul, ← map_add (f := _), ← map_add (f := _)]
      congr 1
      ring
    rw [hy]
    exact Submodule.add_mem_sup (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩) (hI _ hw 1)
  have hle : Nt ≤ M := Submodule.le_of_le_smul_of_le_jacobson_bot
    (Submodule.fg_span ((Set.finite_range _).image _)) (IsLocalRing.maximalIdeal_le_jacobson ⊥) hNM
  have hx' : x ∈ Submodule.span (v.adicCompletionIntegers F) (ι '' Set.univ) := hx
  have hxM : x ∈ M := by
    apply hle
    refine (Submodule.span_le.mpr ?_) hx'
    rintro _ ⟨y, _, rfl⟩
    exact hN y
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxM
  refine ⟨a, b, ?_⟩
  rw [← hab, ov_smul, ov_smul, mul_one]

theorem resAlg_of_eta (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_span σ J ψ v (thetaSpan_holds σ J ψ v) hE

end PI.OmLocU.Red
end
end

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def EtaIn : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime →
    ∀ x : Fv F v ⊗[F] E, x * x = x → x = 0 ∨ x = 1

def EtaSp : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1

theorem etaLink_of (hI : EtaIn σ J ψ v) (hS : EtaSp σ J ψ v) : EtaLink σ J ψ v := by
  intro hstd hun
  unfold etaV
  constructor
  · intro h hp
    split_ifs at h with hx
    · obtain ⟨x, h1, h2, h3⟩ := hx
      rcases hI hstd hun hp x h1 with h0 | h0
      · exact h2 h0
      · exact h3 h0
  · intro hp
    rw [if_pos (hS hstd hun hp)]

theorem resAlg_of_etaSp (hI : EtaIn σ J ψ v) (hS : EtaSp σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_eta σ J ψ v (etaLink_of σ J ψ v hI hS)

end PI.OmLocU.Red

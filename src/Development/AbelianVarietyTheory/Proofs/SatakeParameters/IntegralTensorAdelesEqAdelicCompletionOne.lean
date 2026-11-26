module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDual

theorem lamHat_eq_hat {D : D7} (V : HSp D) :
    LamHat V = GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  have : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    rw [SetLike.mem_coe, GlobalTheory.Member.mem_latC, Module.Basis.equivFun_symm_apply]
    rfl
  rw [this]
  rfl

theorem integralTensorAdeles_eq_adelicCompletion_one (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    exact ⟨a, ha, x, rfl⟩

theorem hR_eq_hermA {D : D7} (V : HSp D)
    (z y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y =
      GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y z := by
  unfold hR Formalism.UG.hform GlobalTheory.AdLat.hermA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, mul_comm (sigR _ _ _), ← mul_assoc]
  rfl

theorem smul_mem_lamHat {D : D7} (V : HSp D) :
    ∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V := by
  intro a ha y hy
  rw [lamHat_eq_hat] at hy ⊢
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        (GlobalTheory.Member.latC V).smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

theorem lamHat_selfDual_and_module : ∀ {D : D7} (V : HSp D), (∀ y, y ∈ LamHat V ↔ ∀ z ∈ LamHat V, hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D) ∧ (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) := by
  intro D V
  refine ⟨fun y => ?_, smul_mem_lamHat V⟩
  obtain ⟨-, -, hfg, hspan, hcc, -, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D)
    V.gram.transpose 1 hfg hspan hcc hG hdet one_ne_zero hL
  rw [← integralTensorAdeles_eq_adelicCompletion_one, ← lamHat_eq_hat] at key
  simp only [hR_eq_hermA]
  constructor
  · intro hy z hz
    rw [lamHat_eq_hat] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_lamHat V _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    rw [lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

end GlobalTheory.LatDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitUnif

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)


omit [NumberField E] [Algebra F E] in
theorem map_mem (x : 𝓞 E) : φ x ∈ v.adicCompletionIntegers F := by
  have h2 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem lt_one_iff (x : WithZero (Multiplicative ℤ)) : x < 1 ↔ x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem mem_max (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))

theorem irreducible_of_valued (p : v.adicCompletionIntegers F)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-1)) : Irreducible p := by
  have hp0 : (p : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  rw [mem_max, lt_one_iff, Ideal.mem_span_singleton', ← hp]
  constructor
  · intro h
    refine ⟨⟨(x : v.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    show Valued.v ((x : v.adicCompletion F) / p) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ h zero_le
  · rintro ⟨a, rfl⟩
    show Valued.v ((a : v.adicCompletion F) * p) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' a.2

variable (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in
theorem valued_unif (ϖ : 𝓞 E) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    Valued.v (φ ϖ) = WithZero.exp (-1) := by
  refine le_antisymm ((lt_one_iff _).1 ((hP ϖ).1 h1)) ?_
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  let s : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) t
  have hs : Valued.v (φ s) = WithZero.exp (-1) := by
    have e1 : (s : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F t)) =
        v.valuation F (algebraMap (𝓞 F) F t) := v.valuedAdicCompletion_eq_valuation' _
    rw [e1, hφ, e2, HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hsP : s ∈ P.asIdeal := by rw [hP, lt_one_iff, hs]
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply h2
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _
  have hle : P.intValuation s ≤ P.intValuation ϖ := by
    have a1 := (P.intValuation_le_pow_iff_mem s 1).2 (by simpa using hsP)
    have a2 := mt (P.intValuation_le_pow_iff_mem ϖ 2).1 h2
    have a3 : P.intValuation ϖ ≠ 0 := P.intValuation_ne_zero ϖ (fun h => hϖ0 (by rw [h]; rfl))
    refine a1.trans ?_
    rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a2 ⊢
    push_cast at a2 ⊢
    omega
  have hx : P.valuation E ((s : E) / ϖ) ≤ 1 := by
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact hle
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
  have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
    le_antisymm (map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
  have h3 : (s : E) * ((d : 𝓞 E) : E) = (n : E) * ϖ := by
    have h' : (s : E) / ϖ * ((d : 𝓞 E) : E) = (n : E) := h
    rw [← h']
    field_simp
  have h4 := congrArg (fun z => Valued.v (φ z)) h3
  simp only [map_mul] at h4
  rw [hd, mul_one, hs] at h4
  rw [h4]
  exact mul_le_of_le_one_left' (map_mem v φ n)

include hφ hP in
theorem card_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm P.asIdeal := by
  let ψ : 𝓞 E →+* v.adicCompletionIntegers F :=
    (φ.comp (algebraMap (𝓞 E) E)).codRestrict _ (map_mem v φ)
  let χ : 𝓞 E →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp ψ
  have hker : RingHom.ker χ = P.asIdeal := by
    ext x
    rw [RingHom.mem_ker, hP]
    show IsLocalRing.residue _ (ψ x) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, mem_max]
    rfl
  have hsurj : Function.Surjective χ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := Formalism.UG.P.glint_exists_approx v x
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
    show IsLocalRing.residue _ (ψ _) = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max]
    have e1 : ((ψ (algebraMap (𝓞 F) (𝓞 E) r) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (𝓞 F) (v.adicCompletion F) r := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← hφ]
      rfl
    rw [AddSubgroupClass.coe_sub, e1]
    exact hr
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

end General

theorem unif_chart : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  intro D e P v π he hc ϖ h1 h2
  let φ : D.host.E →+* v.adicCompletion D.host.F := π.comp (incA D)
  have hφ : ∀ t : D.host.F, φ (algebraMap D.host.F D.host.E t) =
      algebraMap D.host.F (v.adicCompletion D.host.F) t := by
    intro t
    have e1 : incA D (algebraMap D.host.F D.host.E t) =
        algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
    show π (incA D _) = _
    rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, hc.2.2.2, isInt_Ov]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  exact ⟨⟨⟨φ ϖ, map_mem v φ ϖ⟩, rfl, irreducible_of_valued v _ (valued_unif v φ P hφ hP ϖ h1 h2)⟩,
    card_residueField v φ P hφ hP⟩

end GlobalTheory.SplitUnif

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCardStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitChart_uniformiser_and_residueCard : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  first | exact @GlobalTheory.SplitUnif.unif_chart | exact GlobalTheory.SplitUnif.unif_chart | (intros; apply GlobalTheory.SplitUnif.unif_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def intA : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

variable {F}

def evF (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom

def ordAt (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def sgT (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] Af F ⊗[F] E :=
  TensorProduct.map (GlobalTheory.AutFunCompare.sgV v) LinearMap.id

def IsIdemOf (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) : Prop :=
  infP F E e = 0 ∧ evF E v (finP F E e) = 1 ∧ ∀ w, w ≠ v → evF E w (finP F E e) = 0

variable {E}

omit [NumberField E] in
theorem evF_sgT_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) : evF E v (sgT E v y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_same]

omit [NumberField E] in
theorem evF_sgT_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v ⊗[F] E) : evF E w (sgT E v y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

omit [NumberField E] in
theorem evF_ext {z z' : Af F ⊗[F] E} (h : ∀ v, evF E v z = evF E v z') : z = z' :=
  GlobalTheory.LatticeLocalGlobal.ext_components z z' h

omit [NumberField E] in
theorem evF_finP_incl (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    evF E v (finP F E (inclR (AF F) x)) = inclR (Fv F v) x := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F 1) ⊗ₜ x = (1 : Fv F v) ⊗ₜ x
  rw [map_one, map_one]


omit [NumberField E] in
theorem isIdemOf_algebraMap {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α = 0) :
    IsIdemOf E v (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α)) := by
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · show (0 : Ainf F) ⊗ₜ (1 : E) = 0
    exact TensorProduct.zero_tmul _ _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α ⊗ₜ (1 : E) = 1
    rw [h1]; rfl
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α ⊗ₜ (1 : E) = 0
    rw [h2 w hw]; exact TensorProduct.zero_tmul _ _

variable [StarRing E] (hc : CMData F E) (V : HSpace E)

abbrev lamHat (F : Type) [Field F] [NumberField F] [Algebra F E] (V : HSpace E) :
    AddSubgroup (Fin V.rank → Af F ⊗[F] E) :=
  latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0}

def locMat (v : HeightOneSpectrum (𝓞 F)) : HA (AF F) hc.sig V.gram →* GL (Fin V.rank) (Fv F v ⊗[F] E) :=
  (Formalism.UG.bc (evF E v)).comp ((Formalism.UG.bc (finP F E)).comp (HR (AF F) hc.sig V.gram).subtype)

def Supp (f : AF F ⊗[F] E) (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ i j, f * ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j = ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j

def IsFin (g : HA (AF F) hc.sig V.gram) : Prop :=
  Formalism.UG.bc (infP F E) (HA.mat (AF F) hc.sig V.gram g) = 1

def Stab (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ y, y ∈ lamHat F V ↔ (finMat hc.sig V.gram g).mulVec y ∈ lamHat F V

def DivG (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (α : HA (AF F) hc.sig V.gram) : Prop :=
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E),
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → (fun a => finP F E e * B.mulVec z a) ∈ lamHat F V) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * y a) = fun a => finP F E e * B.mulVec z a) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) ∧
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∃ y ∈ lamHat F V,
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a)

theorem locMat_val (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    (locMat hc V v g).1 = (finMat hc.sig V.gram g).map (evF E v) := rfl

theorem locMat_mem (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    locMat hc V v g ∈ HR (Fv F v) hc.sig V.gram :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V v (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g)).2

theorem mem_lamHat_iff (y : Fin V.rank → Af F ⊗[F] E) :
    y ∈ lamHat F V ↔ ∀ v, (fun i => evF E v (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v :=
  GlobalTheory.LatticeLocalGlobal.mem_latHat_iff F E V y

def IsFrameAt (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) : Prop :=
  ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ ∀ i, (h⁻¹).1.mulVec x i ∈ ordAt E v

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

theorem mem_ordAt_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (z : LocAlg v) :
    z ∈ ordAt E v ↔ z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le (t := (locOrder v).toSubring)).2 ?_ hz
    rintro _ ⟨a, ha, x, rfl⟩
    have := mul_mem ((locOrder v).algebraMap_mem ⟨a, ha⟩) (locEmb_mem_locOrder v x)
    have e : algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) ⟨a, ha⟩ * locEmb v (x : E) =
        a ⊗ₜ (x : E) := by
      show (a ⊗ₜ 1 : LocAlg v) * (1 ⊗ₜ (x : E)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e] at this
    exact this
  · intro hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Subring.subset_closure ⟨1, one_mem _, a, rfl⟩
    | algebraMap r => exact Subring.subset_closure ⟨r, r.2, 1, rfl⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_orthonormal (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), IsFrameAt V v h ∧
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 * JR (Fv (maximalRealSubfield E) v) V.gram * h.1 = 1 := by
  haveI := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (V.gramᵀ a b) = V.gramᵀ b a :=
    fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd
    (GlobalTheory.LocalConjugacy.isLattice_coordLat V V.L0 V.standardTuple_isLattice)
    (GlobalTheory.LocalConjugacy.selfDual_coordLat V V.L0 V.baseLattice_isUnimodular) v
  refine ⟨h, fun x => (GlobalTheory.LocalConjugacy.mem_latLoc_iff V v x).trans ((h2 x).trans
    (forall_congr' fun i => (mem_ordAt_iff v _).symm)), ?_⟩
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  exact h3

end CM

end GlobalTheory.PlaceComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitOnto

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

def adj (c : A →+* A) (G H X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := H * (X.map c)ᵀ * G

variable {c : A →+* A} {G H : Matrix (Fin n) (Fin n) A}

theorem adj_add (X Y : Matrix (Fin n) (Fin n) A) : adj c G H (X + Y) = adj c G H X + adj c G H Y := by
  simp only [adj, Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : adj c G H (a • X) = c a • adj c G H X := by
  have : (a • X).map c = c a • X.map c := by
    ext i j
    simp
  simp only [adj, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (h : G * H = 1) : adj c G H 1 = 1 := by
  rw [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, mul_eq_one_comm.1 h]

theorem adj_mul (h : G * H = 1) (X Y : Matrix (Fin n) (Fin n) A) :
    adj c G H (X * Y) = adj c G H Y * adj c G H X := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G H, h, Matrix.one_mul]

theorem adj_adj (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) (X : Matrix (Fin n) (Fin n) A) :
    adj c G H (adj c G H X) = X := by
  have h' : H * G = 1 := mul_eq_one_comm.1 h
  have h1 : (H.map c)ᵀ * G = 1 := by
    conv_lhs => rw [← hG]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have h2 : (((X.map c)ᵀ).map c)ᵀ = X := by
    ext i j
    exact hc _
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, h2, hG, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [← Matrix.mul_assoc, h', Matrix.one_mul]

theorem exists_unitary (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) {e : A} (he : e * e = e)
    (he' : e * c e = 0) (M M' : Matrix (Fin n) (Fin n) A) (hM : e • (M' * M) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ g : GL (Fin n) A, (g.1.map c)ᵀ * G * g.1 = G ∧ (e + c e) • (g.1 - 1) = g.1 - 1 ∧ e • g.1 = e • M := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  set g := e • M + c e • adj c G H M' + f • (1 : Matrix (Fin n) (Fin n) A) with hg
  have hadj : adj c G H g = e • M' + c e • adj c G H M + f • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [hg, adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_adj hc h hG, adj_one h, hc, hcf, add_comm (c e • _)]
  have hM' : c e • (adj c G H M * adj c G H M') = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← adj_mul h, ← adj_smul, hM, adj_smul, adj_one h]
  have hinv : adj c G H g * g = 1 := by
    rw [hadj, hg]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, hM, hM']
    rw [← add_smul, ← add_smul, hf]
    simp
  refine ⟨⟨g, adj c G H g, mul_eq_one_comm.1 hinv, hinv⟩, ?_, ?_, ?_⟩
  · change (g.map c)ᵀ * G * g = G
    have := congrArg (G * ·) hinv
    simpa only [adj, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_one] using this
  · change (e + c e) • (g - 1) = g - 1
    have h6 : f • g = f • (1 : Matrix (Fin n) (Fin n) A) := by
      simp only [hg, smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]
    have h7 : e + c e = 1 - f := by rw [hf]; ring
    rw [h7, sub_smul, one_smul, smul_sub, h6, sub_self, sub_zero]
  · change e • g = e • M
    simp only [hg, smul_add, smul_smul, he, he', h1, zero_smul, add_zero]

end Generic

variable {D : D7}

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  have h : star (V.gram j i) = V.gram i j := LinearMap.isSymm_def.1 V.herm _ _
  exact congrArg (incA D) h

theorem exists_suppAt_rho_eq : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  intro D e v π he hπ V β x
  obtain ⟨he1, he2, -⟩ := he
  obtain ⟨hs, hk, -, -⟩ := hπ
  have key : ∀ a b, π a = π b ↔ e * a = e * b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, hk, mul_sub, sub_eq_zero]
  have keyM : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Y.map π ↔ e • X = e • Y := fun X Y => by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, key]
  have lift : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v),
      ∃ X : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Z := fun Z => by
    choose X hX using fun i j => hs (Z i j)
    exact ⟨Matrix.of X, Matrix.ext hX⟩
  obtain ⟨M, hM⟩ := lift (β * x * β⁻¹).1
  obtain ⟨M', hM'⟩ := lift ((β * x * β⁻¹)⁻¹).1
  obtain ⟨g, h1, h2, h3⟩ := exists_unitary (c := cA D) cA_cA (gram_mul_inv V) (gram_conj V) he1 he2 M M' (by
    rw [← keyM, Matrix.map_mul, hM, hM', Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨g, h1⟩
  refine ⟨g', fun i j => congrFun (congrFun h2 i) j, Units.ext ?_⟩
  refine (rho_val V π β g').trans ?_
  change (β⁻¹).1 * g.1.map π * β.1 = x.1
  rw [(keyM _ _).2 h3, hM, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.SplitOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitSupported_unitary_component : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  first | exact @GlobalTheory.SplitOnto.exists_suppAt_rho_eq | exact GlobalTheory.SplitOnto.exists_suppAt_rho_eq | (intros; apply GlobalTheory.SplitOnto.exists_suppAt_rho_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
noncomputable section

namespace GlobalTheory.UnUnitCmp.Val

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt IsUnifAt exists_unif ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

variable {L : Type} [Field L] [NumberField L]

def intFin (L : Type) [Field L] [NumberField L] : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers L}
  one_mem' := fun _ => one_mem _
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (intFin L ⧸ Ideal.span {(N : intFin L)}) := by
  let ι : 𝓞 L →+* intFin L :=
    ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap (𝓞 L) L)).codRestrict _
      fun x v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v x
  have : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 L)})
    (Ideal.span {(N : intFin L)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : intFin L)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).2 z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : FiniteAdeleRing (𝓞 L) L) - algebraMap L _ (x : L) = ((N : intFin L) : FiniteAdeleRing (𝓞 L) L) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

theorem finUnit_pow (χ : HChar L) (hχ : χ.IsUnitary) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ((χ.1 u : ℂˣ) : ℂ) ^ m = 1 := by
  let ψ : Ideles L →* Circle :=
    { toFun := fun x => ⟨(χ.1 x : ℂˣ), by simpa [Submonoid.unitSphere] using hχ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => Subtype.ext (congrArg Units.val (map_mul χ.1 x y)) }
  have hψ : Continuous ψ := (Units.continuous_val.comp χ.2.1).subtype_mk _
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl) (intFin L)
    (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW) finite_quot ψ hψ
  refine ⟨m, hm, fun u h1 h2 => ?_⟩
  have := h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩
  exact congrArg (fun z : Circle => (z : ℂ)) this

theorem infDiag_mul_finPartI (k : Lˣ) : infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  classical
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem exists_pow_eq (x : Ideles L) (hx : IsFinIdele x) :
    ∃ h : ℕ, 0 < h ∧ ∃ (u : Ideles L) (k : Lˣ), IsFinIdele u ∧ u ∈ unitIdl L ∧ x ^ h * infDiag k = u * diagUnits L k := by
  have : (unitIdl L ⊔ (diagUnits L).range).FiniteIndex := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero this.index_ne_zero, ?_⟩
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
  have hf : finPartI L x = x := Units.ext (Prod.ext (funext hx).symm rfl)
  refine ⟨finPartI L u, k, fun _ => rfl, hu, ?_⟩
  rw [← hf, ← map_pow, ← e, map_mul, mul_assoc, mul_comm _ (infDiag k), infDiag_mul_finPartI]

end GlobalTheory.UnUnitCmp.Val
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
open NumberField IsDedekindDomain

theorem GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  intro E _ _ _
  obtain ⟨d, s, hs, hsn, -⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hsn
    have : s = 0 := by simpa using hs
    rw [this]
    exact zero_mem _
  have h2d : (2 * d : 𝓞 (maximalRealSubfield E)) ≠ 0 := mul_ne_zero two_ne_zero hd0
  refine ⟨Ideal.absNorm (Ideal.span {2 * d}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h2d
  intro K _ _ _ _ w hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {2 * d}))
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  have hint : ∀ x : 𝓞 (maximalRealSubfield E),
      IsIntegral ℤ (algebraMap E K ((x : maximalRealSubfield E) : E)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map
      ((algebraMap E K).comp (maximalRealSubfield E).subtype).toIntAlgHom
  have hmem : algebraMap E K ((d : maximalRealSubfield E) : E) ∈ maximalRealSubfield K :=
    (GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).2 (d : maximalRealSubfield E).2
  have hai : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield K) :=
    (isIntegral_algHom_iff (maximalRealSubfield K).subtype.toIntAlgHom Subtype.val_injective).1 (hint d)
  let a : 𝓞 (maximalRealSubfield K) := ⟨_, hai⟩
  refine GlobalTheory.unramified_adjoin_sqrt_of_not_mem K a (algebraMap E K s) ?_ ?_ w ?_
  · rw [← map_pow, hs]; rfl
  · exact fun h => hsn ((GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).1 h)
  · intro h
    apply hw
    have h1 : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) ∈ w.asIdeal := h
    let c' : 𝓞 K := ⟨_, hint c⟩
    have h2 : ((Ideal.absNorm (Ideal.span {2 * d}) : ℕ) : 𝓞 K)
        = c' * algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      let f : 𝓞 (maximalRealSubfield E) →+* K :=
        ((algebraMap E K).comp (maximalRealSubfield E).subtype).comp (algebraMap _ _)
      have h3 := congrArg f hc
      rw [map_natCast, map_mul, map_mul, map_ofNat] at h3
      rw [map_natCast, ← h3, map_mul, map_mul, map_mul, map_ofNat, map_ofNat]
      rfl
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfieldStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_unramified_over_maximalRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  first | exact @GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield | exact GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield | (intros; apply GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
open Matrix

namespace GlobalTheory.SplitHecke

theorem finrank_range_reduction (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (p : O) (hp : Irreducible p) (n j : ℕ) (a : GL (Fin n) K)
    (A : Matrix (Fin n) (Fin n) O) (hj : j ≤ n) (h : Hk O p j a) (hA : A.map (algebraMap O K) = a.1) :
    Module.finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  classical
  obtain ⟨-, h2, u, hu⟩ := h
  obtain ⟨B, hB⟩ := intM_iff.1 h2
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hAB : A * B = p • (1 : Matrix (Fin n) (Fin n) O) := by
    apply Matrix.map_injective inj
    change (A * B).map (algebraMap O K) = (p • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O K)
    rw [Matrix.map_mul, hA, hB, Matrix.mul_smul, Units.mul_inv]
    ext i k
    by_cases e : i = k <;> simp [e]
  have hdet : Associated A.det (p ^ j) := by
    have : A.det = p ^ j * u := by
      apply inj
      rw [← hu, ← hA, RingHom.map_det]
      rfl
    rw [this]
    exact (associated_mul_unit_left _ _ u.isUnit)
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := GlobalTheory.SmithBetween.smith_between O p hp n j hj A B hAB hdet
  set r := IsLocalRing.residue O with hr
  have hP' : IsUnit (P.map r).det := by
    have := hP.map r
    rwa [RingHom.map_det] at this
  have hQ' : IsUnit (Q.map r).det := by
    have := hQ.map r
    rwa [RingHom.map_det] at this
  have hp0 : r p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hp.not_isUnit
  have h3 : A.map r * Q.map r = P.map r *
      Matrix.diagonal (fun i : Fin n => if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_mul, Matrix.diagonal_map (map_zero r)]
    congr 2
    funext i
    split_ifs <;> simp [hp0]
  have h4 := congrArg Matrix.rank h3
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP',
    Matrix.rank_diagonal] at h4
  have h5 : Fintype.card {i : Fin n // (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0}
      = n - j := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n =>
        (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0)
        = Finset.univ.filter fun i : Fin n => i.1 < n - j := by
      ext i
      by_cases e : i.1 < n - j <;> simp only [Finset.mem_filter, Finset.mem_univ, e, if_true, if_false, true_and, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
    rw [this, Fin.card_filter_val_lt]
    omega
  have h6 : (A.map r).rank = n - j := by
    rw [h4]
    convert h5
  change (A.map r).rank + j = n
  omega

end GlobalTheory.SplitHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_reduction_range_add_corank : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (n j : ℕ) (a : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) O), j ≤ n → Hk O p j a → A.map (algebraMap O K) = a.1 → Module.finrank (IsLocalRing.ResidueField O) (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  first | exact @GlobalTheory.SplitHecke.finrank_range_reduction | exact GlobalTheory.SplitHecke.finrank_range_reduction | (intros; apply GlobalTheory.SplitHecke.finrank_range_reduction <;> assumption)
end
end

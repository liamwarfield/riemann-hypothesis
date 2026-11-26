module

public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.HalfNorm
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbChart

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

def atPlace : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem atPlace_apply (a : Fv F v) : atPlace v a = pairA F 0 (singleFin v a) := rfl

theorem atPlace_mul_right (a : Fv F v) (y : AF F) : atPlace v a * y = atPlace v (a * evFin F v y) := by
  refine Prod.ext (zero_mul _) ?_
  change singleFin v a * sndA F y = singleFin v (a * evalV F v (sndA F y))
  refine FiniteAdeleRing.ext _ fun u => ?_
  change evalV F u (singleFin v a * sndA F y) = evalV F u (singleFin v (a * evalV F v (sndA F y)))
  rw [map_mul]
  by_cases e : u = v
  · subst e; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]

theorem evFin_atPlace (a : Fv F v) : evFin F v (atPlace v a) = a := evalV_singleFin_self v a


variable (E) in
def tensAt : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (atPlace v) LinearMap.id

theorem tensAt_tmul (a : Fv F v) (x : E) : tensAt E v (a ⊗ₜ[F] x) = atPlace v a ⊗ₜ[F] x := rfl

theorem compFin_tensAt (y : Fv F v ⊗[F] E) : compFin F E v (tensAt E v y) = y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (evFin_atPlace v a)

theorem tensAt_eq_zero {y : Fv F v ⊗[F] E} : tensAt E v y = 0 ↔ y = 0 :=
  ⟨fun h => by rw [← compFin_tensAt v y, h, map_zero], fun h => by rw [h, map_zero]⟩

theorem tensAt_mul_right (y : Fv F v ⊗[F] E) (z : AF F ⊗[F] E) :
    tensAt E v y * z = tensAt E v (y * compFin F E v z) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  | tmul a x =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), mul_add, hx, hy]
    | tmul b x' =>
      change _ = tensAt E v (a ⊗ₜ[F] x * evFin F v b ⊗ₜ[F] x')
      rw [tensAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, tensAt_tmul,
        atPlace_mul_right]

theorem sigR_tensAt (σ : E →ₐ[F] E) (y : Fv F v ⊗[F] E) :
    sigR (AF F) σ (tensAt E v y) = tensAt E v (sigR _ σ y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_evalV_map_sndA (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E v z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_evalV_mem {z : Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact tmul_mem_intLoc (hα v) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem map_sndA_tensAt_mem {y : Fv F v ⊗[F] E} (h : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) h
  · refine AddSubgroup.subset_closure ⟨singleFin v a, fun u => ?_, x, rfl⟩
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

end General

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem finPart_tensAt_mem_iff (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    finPart D (tensAt D.host.E v y) ∈ intAE D ↔ y ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => ?_, map_sndA_tensAt_mem v⟩
  have h3 := map_evalV_mem v h
  rwa [show finPart D (tensAt D.host.E v y) = _ from rfl, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_evalV_map_sndA, compFin_tensAt] at h3

def idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D := tensAt D.host.E v (splitIdem (isCMExt_host D) τ)

theorem idem_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    idem τ * a = tensAt D.host.E v (splitIdem (isCMExt_host D) τ * compFin D.host.F D.host.E v a) :=
  tensAt_mul_right v _ a

theorem compFin_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    compFin D.host.F D.host.E v (idem τ) = splitIdem (isCMExt_host D) τ := compFin_tensAt v _

theorem cA_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    cA D (idem τ) = tensAt D.host.E v (1 - splitIdem (isCMExt_host D) τ) :=
  (sigR_tensAt v _ _).trans (congrArg _ (sigR_splitIdem _ τ))

theorem isSplitIdem_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsSplitIdem D (idem τ) := by
  refine ⟨?_, ?_, v, atPlace v 1, ⟨singleFin v 1, rfl, evalV_singleFin_self v 1, fun u hu => evalV_singleFin_ne hu 1⟩,
    ?_⟩
  · rw [idem_mul, compFin_idem, splitIdem_mul_self]; rfl
  · rw [idem_mul, cA_idem, compFin_tensAt, mul_sub, mul_one, splitIdem_mul_self, sub_self, LinearMap.map_zero]
  · rw [cA_idem, idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

theorem finPart_idem_mul_mem_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    finPart D (idem τ * a) ∈ intAE D ↔
      splitProj τ (compFin D.host.F D.host.E v a) ∈ v.adicCompletionIntegers D.host.F := by
  rw [idem_mul, finPart_tensAt_mem_iff, mem_intLoc_iff_split (isCMExt_host D) τ, map_mul, map_mul,
    splitProj_splitIdem, splitProj_comp_splitIdem, one_mul, zero_mul]
  exact and_iff_left (zero_mem _)

theorem chart_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Chart (idem τ) v
    ((splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)) := by
  refine ⟨fun a => ⟨tensAt D.host.E v (a ⊗ₜ 1), ?_⟩, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · change splitProj τ (compFin D.host.F D.host.E v (tensAt D.host.E v (a ⊗ₜ[D.host.F] 1))) = a
    rw [compFin_tensAt, splitProj_tmul, map_one, mul_one]
  · rw [idem_mul, tensAt_eq_zero]
    exact splitProj_eq_zero_iff _ τ _
  · change splitProj τ (evFin D.host.F v y ⊗ₜ 1) = _
    rw [splitProj_tmul, map_one, mul_one]; rfl
  · rw [finPart_idem_mul_mem_iff, isInt_Ov]; rfl

theorem isIdemAt_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsIdemAt (idem τ) (splitPrime τ) := by
  refine ⟨isSplitIdem_idem τ, fun x hx => ?_⟩
  have h0 : Valued.v (τ x) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero τ).2 (RingOfIntegers.coe_ne_zero_iff.2 hx))
  have h1 : splitProj τ (compFin D.host.F D.host.E v (incA D (x : D.host.E)⁻¹)) = τ (x : D.host.E)⁻¹ := by
    change splitProj τ (evFin D.host.F v 1 ⊗ₜ _) = _
    rw [splitProj_tmul, map_one, one_mul]; rfl
  rw [finPart_idem_mul_mem_iff, h1, mem_splitPrime, HeightOneSpectrum.mem_adicCompletionIntegers,
    map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem exists_isIdemAt_chart : ∀ {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ e : AE D, IsIdemAt e (GlobalTheory.AdelicU.splitPrime τ) ∧ Chart e v ((GlobalTheory.AdelicU.splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)) :=
  fun τ => ⟨idem τ, isIdemAt_idem τ, chart_idem τ⟩

end GlobalTheory.EmbChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)

variable {D : D7}

abbrev Place (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev ModHost (D : D7) : Type := ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E

def PrimeToAA (D : D7) (P : Place D) : Prop := FractionalIdeal.count D.host.E P D.host.AA = 0

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro hz
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · rw [FractionalIdeal.coeIdeal_eq_zero] at h1
    unfold Formalism.BasicNotions.Host.ccE at h1
    rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h1
    exact D.host.ccK_ne_bot h1
  · rw [inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero] at h1
    have h2 := D.host.𝔟_spec.2
    rw [h1] at h2
    simp at h2

end GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
end
end

noncomputable section

namespace GlobalTheory.HalfCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level Coeff Moduli)

variable {D : D7}

abbrev badInt (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ∀ N : ℕ, (N : 𝓞 K) ∈ P.asIdeal ↔ p ∣ N := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, fun N => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem mem_of_dvd {R : Type} [CommRing R] {J : Ideal R} {p N : ℕ} (hp : (p : R) ∈ J) (h : p ∣ N) : (N : R) ∈ J := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  exact J.mul_mem_right _ hp

theorem not_mem_of_coprime {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {a b : ℕ}
    (h : Nat.Coprime a b) (hb : (b : 𝓞 K) ∈ P.asIdeal) : (a : 𝓞 K) ∉ P.asIdeal := by
  intro ha
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h ((hP a).1 ha) ((hP b).1 hb))

theorem exists_place_of_dvd_absNorm {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 K))
    (h : p ∣ Ideal.absNorm J) : ∃ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal ∧ P.asIdeal ∣ J := by
  obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h
  have hm : (p : 𝓞 K) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hu]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨P, hP.isPrime, ?_⟩, hm, hd⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hm)

theorem prime_dvd_absNorm_halfDifferent (D : D7) {p : ℕ} (hp : p.Prime) :
    p ∣ Ideal.absNorm D.host.𝔟 ↔ p ∣ D.host.QS * D.host.q :=
  D.host.prime_dvd_absNorm_half_iff hp

theorem coprime_ccK (D : D7) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.QS * D.host.q) :=
  Nat.Coprime.mul_right D.host.ccK_coprimeS (D.host.ccK_coprime _ (by simp))

theorem ccE_ne_bot (D : D7) : D.host.ccE ≠ ⊥ := fun h =>
  D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)

theorem absNorm_ccK_mem {P : Place D} (h : P.asIdeal ∣ D.host.ccE) :
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
  rw [map_natCast] at this
  exact Ideal.le_of_dvd h this

theorem two_q_mem {P : Place D} (h : P.asIdeal ∣ D.host.𝔟) : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  obtain ⟨p, hp, hP⟩ := exists_prime_under P
  exact (hP _).2 ((prime_dvd_absNorm_halfDifferent D hp).1 ((hP _).1 (Ideal.le_of_dvd h (Ideal.absNorm_mem _))))

theorem primeToAA_iff (P : Place D) : PrimeToAA D P ↔ ¬ P.asIdeal ∣ D.host.ccE ∧ ¬ P.asIdeal ∣ D.host.𝔟 := by
  classical
  have hb := D.host.half_ne_bot
  have hc := ccE_ne_bot D
  have hnot : ¬ (P.asIdeal ∣ D.host.ccE ∧ P.asIdeal ∣ D.host.𝔟) := fun h =>
    not_mem_of_coprime P (coprime_ccK D) (two_q_mem h.2) (absNorm_ccK_mem h.1)
  unfold PrimeToAA Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [FractionalIdeal.count_mul _ _ (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe _ _ hc, FractionalIdeal.count_coe _ _ hb]
  rw [← Associates.count_ne_zero_iff_dvd hc P.irreducible, ← Associates.count_ne_zero_iff_dvd hb P.irreducible] at hnot ⊢
  omega

theorem primeToAA_of_not_mem {P : Place D} (h : ((badInt D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : PrimeToAA D P :=
  (primeToAA_iff P).2 ⟨fun hc => h (mem_of_dvd (absNorm_ccK_mem hc) (Dvd.intro_left _ rfl)),
    fun hb => h (mem_of_dvd (two_q_mem hb) (Dvd.intro _ rfl))⟩

section Lev

variable {H : ModHost D}

end Lev

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

end GlobalTheory.HalfCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ENNReal

namespace GlobalTheory.RestrMeas

section Pi

theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod_eq_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod fun i => hf _

end Pi

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v}
  {K : ∀ v, Set (Yf v)}

theorem finprod_eq_prod_of_mem {M : Type} [CommMonoid M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) {x : X} (hx : ∀ v ∉ S, pf v x ∈ K v) :
    ∏ᶠ v, ff v (pf v x) = ∏ v ∈ S, ff v (pf v x) :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h' => hv (h1 v h' _ (hx v h'))

theorem finprod_eq_zero_of_notMem {M : Type} [CommMonoidWithZero M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ff v = (K v).indicator 1) {x : X} (hx : ∀ᶠ v in cofinite, pf v x ∈ K v)
    (hx' : ¬ ∀ v ∉ S, pf v x ∈ K v) : ∏ᶠ v, ff v (pf v x) = 0 := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_of_eventually hx
  push Not at hx'
  obtain ⟨u, hu, hu'⟩ := hx'
  rw [finprod_eq_prod_of_mem (K := K) (S := S ∪ T)
    (fun v hv y hy => by rw [h1 v fun h' => hv (Finset.mem_union_left _ h'), indicator_of_mem hy, Pi.one_apply])
    fun v hv => hT v fun h' => hv (Finset.mem_union_right _ h')]
  exact Finset.prod_eq_zero (Finset.mem_union_right _ (by_contra fun h' => hu' (hT u h')))
    (by rw [h1 u hu, indicator_of_notMem hu'])

variable [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)] [Countable V]

theorem measurableSet_level (hf : ∀ v, Measurable (pf v)) (hK : ∀ v, MeasurableSet (K v)) (S : Finset V) :
    MeasurableSet {x | ∀ v ∉ S, pf v x ∈ K v} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hf v (hK v)

variable [Fintype W] {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
  [∀ w, SigmaFinite (μa w)] [∀ v, SigmaFinite (μf v)]


omit [Countable V] in
theorem IsCylProd.measurePreserving_level (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w))
    (hf : ∀ v, Measurable (pf v)) {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1) :
    MeasurePreserving (fun x => (fun w => pa w x, fun v : S => pf v x)) (μ.restrict {x | ∀ v ∉ S, pf v x ∈ K v})
      ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)) := by
  classical
  have hπ : Measurable fun x => (fun w => pa w x, fun v : S => pf v x) :=
    (Measurable.of_eval ha).prodMk (Measurable.of_eval fun v => hf v)
  refine ⟨hπ, (prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (FiniteSpanningSetsIn.pi fun w => (μa w).toFiniteSpanningSetsIn)
    (FiniteSpanningSetsIn.pi fun v : S => (μf v).toFiniteSpanningSetsIn) ?_).symm⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hm := (MeasurableSet.univ_pi fun w => hA w (mem_univ _)).prod (MeasurableSet.univ_pi fun v => hB v (mem_univ _))
  have e := h.2 S hS A (fun v => if hv : v ∈ S then B ⟨v, hv⟩ else univ) (fun w => hA w (mem_univ _))
    fun v hv => by simp only [dif_pos hv]; exact hB ⟨v, hv⟩ (mem_univ _)
  rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm), Measure.pi_pi, Measure.pi_pi]
  convert e using 2
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, mem_setOf_eq, and_assoc, Subtype.forall]
    exact and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun v hv => by rw [dif_pos hv]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]

variable (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w)) (hf : ∀ v, Measurable (pf v))
  (hK : ∀ v, MeasurableSet (K v))

include h ha hf hK

section Nonneg

variable {fa : ∀ w, Ya w → ℝ≥0∞} {ff : ∀ v, Yf v → ℝ≥0∞}

end Nonneg

variable {𝕜 : Type} [RCLike 𝕜] {fa : ∀ w, Ya w → 𝕜} {ff : ∀ v, Yf v → 𝕜}

theorem IsCylProd.setIntegral_tensor {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1)
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) (hfa : ∀ w, Integrable (fa w) (μa w))
    (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    IntegrableOn (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} μ ∧
    ∫ x in {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  have hp := h.measurePreserving_level ha hf hS
  have hi := (Integrable.fintype_prod_dep hfa).mul_prod
    (Integrable.fintype_prod_dep (μ := fun v : S => μf v) fun v : S => hff v v.2)
  have e : EqOn (fun x => (∏ w, fa w (pa w x)) * ∏ v : S, ff v (pf v x))
      (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} := fun x hx => by
    simp only [finprod_eq_prod_of_mem h1 hx, ← Finset.prod_coe_sort S]
  refine ⟨IntegrableOn.congr_fun (hp.integrable_comp_of_integrable hi) e (measurableSet_level hf hK S), ?_⟩
  rw [← setIntegral_congr_fun (measurableSet_level hf hK S) e, ← Finset.prod_coe_sort S,
    ← integral_fintype_prod_eq_prod, ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← hp.map_eq,
    integral_map hp.aemeasurable (hp.map_eq ▸ hi.aestronglyMeasurable)]

theorem IsCylProd.integral_tensor_indicator (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S : Finset V}
    (hS : ∀ v ∉ S, μf v (K v) = 1) (h1 : ∀ v ∉ S, ff v = (K v).indicator 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ ∧
    ∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  obtain ⟨hi, e⟩ := h.setIntegral_tensor ha hf hK hS
    (fun v hv y hy => by rw [h1 v hv, indicator_of_mem hy, Pi.one_apply]) hfa hff
  have h0 : ∀ x ∉ {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) = 0 := fun x hx => by
    rw [finprod_eq_zero_of_notMem h1 (hX x) hx, mul_zero]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero h0, by rw [← e, setIntegral_eq_integral_of_forall_compl_eq_zero h0]⟩


end GlobalTheory.RestrMeas

namespace GlobalTheory.AdelicU

open NumberField IsDedekindDomain GlobalTheory.RestrMeas

end GlobalTheory.AdelicU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLatHatIffOfSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicU.SplitFrame

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem map_map_sndA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (u : HeightOneSpectrum (𝓞 F))
    (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem vecLoc_finPart {n : ℕ} (u : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (y : Fin n → AE D) :
    vecLoc u (fun i => finPart D (e * y i)) =
      compFin D.host.F D.host.E u e • fun i => compFin D.host.F D.host.E u (y i) :=
  funext fun i => (map_map_sndA u (e * y i)).trans ((compFin D.host.F D.host.E u).map_mul e (y i))

theorem compFin_eq_zero (he : IsSplitIdem D e) (hπ : Chart e v π) {u : HeightOneSpectrum (𝓞 D.host.F)}
    (hu : u ≠ v) : compFin D.host.F D.host.E u e = 0 := by
  obtain ⟨h1, h2, v', ε, ⟨α, rfl, -, ha⟩, hε⟩ := he
  have p1 : π e = 1 := by
    have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, h1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have p2 : π (cA D e) = 0 := (hπ.2.1 _).2 h2
  have p3 : evalV D.host.F v α = 1 := by
    have := hπ.2.2.1 (pairA D.host.F 0 α)
    rw [← hε, map_add (f := _), p1, p2, add_zero] at this
    exact this.symm
  have hv : v = v' := by
    by_contra hne
    rw [ha v hne] at p3
    exact zero_ne_one p3
  subst hv
  have p4 : compFin D.host.F D.host.E u (e + cA D e) = 0 := by
    rw [hε]
    change (evalV D.host.F u α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [ha u hu, TensorProduct.zero_tmul]
  have p5 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [p5, map_mul, p4, mul_zero]

theorem mem_latHat_iff_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) {y : Fin n → Af F ⊗[F] E} {z : Fin n → Fv F v}
    (hv : vecLoc v y = splitIncl h τ z) (hu : ∀ u, u ≠ v → vecLoc u y = 0) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ z ∈ splitLat τ L := by
  rw [mem_latHat_iff hL, ← splitIncl_mem_latLoc_iff h, ← hv]
  refine ⟨fun h => h v, fun h u => ?_⟩
  by_cases huv : u = v
  · subst huv; exact h
  · rw [hu u huv]; exact zero_mem _

theorem vecLoc_self (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D) :
    vecLoc v (fun i => finPart D (e * y i)) = splitIncl (isCMExt_host D) (chartEmb hπ) (fun k => π (y k)) := by
  have : (fun k => π (y k)) = splitVec (chartEmb hπ) (fun k => compFin D.host.F D.host.E v (y k)) :=
    funext fun k => chart_eq_splitProj hπ _
  rw [this, splitIncl_splitVec, vecLoc_finPart, compFin_eq_splitIdem he hπ]

theorem vecLoc_ne (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D)
    (u : HeightOneSpectrum (𝓞 D.host.F)) (hu : u ≠ v) : vecLoc u (fun i => finPart D (e * y i)) = 0 := by
  rw [vecLoc_finPart, compFin_eq_zero he hπ hu]
  exact funext fun i => zero_mul _

theorem lamHat_eq (V : HSp D) :
    LamHat V = Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) :=
  congrArg (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E) (hermitianSpaceBaseLattice_eq_frameLattice V)

theorem mem_lamHat_iff (he : IsSplitIdem D e) (hπ : Chart e v π) (V : HSp D) (y : Fin V.rank → AE D) :
    (fun i => finPart D (e * y i)) ∈ LamHat V ↔ (fun k => π (y k)) ∈ splitLat (chartEmb hπ) (frameLat V) := by
  rw [lamHat_eq]
  exact mem_latHat_iff_of_support (isCMExt_host D) _ (frameLat_fg V) (vecLoc_self he hπ y) (vecLoc_ne he hπ y)

theorem frame_iff_isSplitBasis : ∀ {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v}, IsSplitIdem D e → ∀ (hπ : Chart e v π) (V : HSp D)
    (β : GL (Fin V.rank) (Fv D.host.F v)),
    Frame V e π β ↔ GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.AdelicU.chartEmb hπ) (GlobalTheory.AdelicU.frameLat V) β := by
  intro D e v π he hπ V β
  refine ⟨fun h u => ?_, fun h y => ?_⟩
  · choose y hy using fun k => hπ.1 ((β.1 *ᵥ u) k)
    have h1 := h y
    rw [mem_lamHat_iff he hπ, show (fun k => π (y k)) = β.1 *ᵥ u from funext hy, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec] at h1
    simpa only [isInt_Ov] using h1.symm
  · rw [mem_lamHat_iff he hπ, h.mem_iff]
    simp only [isInt_Ov]

end GlobalTheory.AdelicU.SplitFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMul
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem theta_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  intro k _ _ _ _ n ψ hψ a ha b hb
  have P := GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k
  obtain ⟨-, -, -, -, -, -, hevmul, hevcong, hevtriv⟩ := P
  unfold theta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  by_cases ht : Triv (ψ m / nxt ψ m) 1
  · rw [hevtriv _ _ ht, hevtriv _ _ ht, hevtriv _ _ ht, one_mul]
  · obtain ⟨hv, hc⟩ := GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k n ψ hψ m ht
    have hab := GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hψ a ha b hb
    have va := hv a ha
    have vb := hv b hb
    have vab := hv (a * b) hab
    have vprod : valuation k (minor a m * minor b m) = 1 := by rw [map_mul, va, vb, one_mul]
    rw [hevcong _ _ _ vab vprod (hc a ha b hb), hevmul _ _ _ va vb]

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMulStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  first | exact @GlobalTheory.PsType.theta_mul | exact GlobalTheory.PsType.theta_mul | (intros; apply GlobalTheory.PsType.theta_mul <;> assumption)
end
end

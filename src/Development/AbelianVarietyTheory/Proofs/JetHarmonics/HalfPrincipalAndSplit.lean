module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartFormalBiextensionBaseChange
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueGermsIndependentOfChart
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.HalfGen

theorem factors_of_ncard_places (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have h1 : s.card ≤ Module.finrank ℚ E := by
    have := Multiset.pow_card_le_prod hle
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map] at this
    exact (Nat.pow_le_pow_iff_right hg.one_lt).1 this
  have h2 : Module.finrank ℚ E ≤ s.toFinset.card := by
    rw [← h, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun v => v.asIdeal) (fun v hv => ?_)
      (fun v _ w _ e => HeightOneSpectrum.ext e) (Finset.finite_toSet _)
    rw [Finset.mem_coe, Multiset.mem_toFinset, hs, Ideal.mem_normalizedFactors_iff hI0]
    exact ⟨v.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hv⟩
  have h3 := Multiset.toFinset_card_le s
  exact ⟨by omega, Multiset.toFinset_card_eq_card_iff_nodup.1 (by omega)⟩

theorem barE_piG {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D _

theorem half_principal_and_split : ∀ (D : D7) (T : Core D), LawsM T → ∀ EX : ErrX D,
 letI := T.Q.H.starRing
 (∃ α : 𝓞 D.host.E, α * star α = ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {star α}) ∧ (∀ i, star (EX.piG i) = piBarO EX i ∧ piBarO EX i * star (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E)) ∧ ((∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) → T.Q.l.Mb = Ideal.span {piBarO EX 0 * piBarO EX 1}) ∧ ∀ (L : SizeData₂ D), ParameterChoice' D L → ∀ i, (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup := by
  intro D T h EX
  have hb : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => by rw [bar_core, barE_piG]
  have hbb : ∀ a, T.Q.H.bar (T.Q.H.bar a) = a := fun a => by rw [bar_core, bar_core, barE_barE]
  have hn : ∀ i, piBarO EX i * T.Q.H.bar (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [← hb, hbb, mul_comm, hb]
    exact RPfVal.piG_mul_bar EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hpp : (piOf T EX 0 * piOf T EX 1) * T.Q.H.bar (piOf T EX 0 * piOf T EX 1) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [map_mul, ← hp 0, ← hp 1]; ring
  refine ⟨⟨T.Q.H.bar (piOf T EX 0 * piOf T EX 1), ?_, ?_⟩, fun i => ⟨hb i, hn i⟩, fun ho => ?_, fun _ _ i => ?_⟩
  · show T.Q.H.bar _ * T.Q.H.bar (T.Q.H.bar _) = _
    rw [hbb, mul_comm, hpp, level_M T h, Nat.cast_mul]
  · show _ = Ideal.span {T.Q.H.bar (T.Q.H.bar _)}
    rw [hbb, hM]
  · have hcg : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    rw [← hn 0, ← hn 1] at hcg
    have hc : IsCoprime (piBarO EX 0) (piBarO EX 1) := hcg.of_mul_left_left.of_mul_right_left
    have hd : ∀ i, piBarO EX i ∣ piOf T EX 0 * piOf T EX 1 := fun i =>
      Ideal.mem_span_singleton.1 (ho i (hM ▸ Ideal.mem_span_singleton_self _))
    obtain ⟨c, hcc⟩ := hc.mul_dvd (hd 0) (hd 1)
    have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)
    have hu : c * T.Q.H.bar c = 1 := by
      apply mul_left_cancel₀ hg
      rw [_root_.mul_one]
      conv_rhs => rw [← hpp, hcc, map_mul, map_mul]
      rw [← hn 0, ← hn 1]
      ring
    rw [hM, hcc]
    exact Ideal.span_singleton_mul_right_unit (IsUnit.of_mul_eq_one _ hu) _
  · exact factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.HalfGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate

namespace GlobalTheory.HatNF.MinorPoly

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminor_words (k r m : ℕ) (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ⊤ UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        qminorOp (EabH (Hpk k r)) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin m) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin m => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin m))).toList.flatMap
      (fun σ => (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map
        fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨fun X hX => (this.1 X hX).1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((ts σ).length : ℕ∞) f g := fun σ =>
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top (hf g hgU)
    have e1 : qminorOp (EabH (Hpk k r)) a b u f g =
        ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT, ts, List.map_ofFn]
      rfl
    rw [e1, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq (ts σ) f g hg (hloc σ), List.map_map,
      ← Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def scalarTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := w
  word_lie := hw
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right]
    simp

theorem isPolyDeg_mul_const {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) (c : ℂ) :
    U.IsPolyDeg κ fun g => P g * c := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [he g]⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simpa using hq

theorem exists_polyOp_words (m κ : ℕ) (P : B.Mat k r → ℂ) (hP : U.IsPolyDeg κ P)
    (L : List (ℂ × List (B.Mat k r))) (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) :
    ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F g,
      B.opApply Θ F g = P g • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction L with
  | nil => exact ⟨[], fun T hT => by simp at hT, fun F g => by simp [B.opApply]⟩
  | cons cw L ih =>
    obtain ⟨Θ, hΘ, he⟩ := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    have h0 := hL cw List.mem_cons_self
    refine ⟨scalarTerm (fun g => P g * cw.1) cw.2 h0.1 :: Θ, ?_, fun F g => ?_⟩
    · intro T hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact ⟨h0.2, fun g => P g * cw.1, isPolyDeg_mul_const hP _, fun _ => rfl, fun _ => rfl⟩
      · exact hΘ T hT
    · have h1 := he F g
      simp only [B.opApply, List.map_cons, List.sum_cons] at h1 ⊢
      rw [h1, smul_add, smul_smul]
      rfl

end terms

theorem minor_polyOp : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  intro Wp Wq _ _ _ _ _ _ k r m κ ι _ a b u co hco
  choose L hL hE using fun i => qminor_words k r m (a i) (b i) u
  choose Θ hΘ hA using fun i => exists_polyOp_words (Wp := Wp) (Wq := Wq) m κ (co i) (hco i) (L i) (hL i)
  refine ⟨(Finset.univ : Finset ι).toList.flatMap Θ, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 hT
    exact hΘ i T hi
  · intro F g hg V _ hgV hF
    unfold B.opApply
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE i _ _ F hF g ⟨hg, hgV⟩ hg, ← hA i F g]
    rfl

end

end GlobalTheory.HatNF.MinorPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperatorStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantumMinor_sum_polynomialOperator : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  first | exact @GlobalTheory.HatNF.MinorPoly.minor_polyOp | exact GlobalTheory.HatNF.MinorPoly.minor_polyOp | (intros; apply GlobalTheory.HatNF.MinorPoly.minor_polyOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeField
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeField
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HarmonicValueToField


set_option maxHeartbeats 1000000 in
theorem sum_map_of_harmA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    [Field S'] [Algebra c.F S'] [Algebra ℚ S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S')
    (hm : FrMap ψ y y') (h : ptO Xo y'.x ⟶ ptO Xo y.x) (hh : h.left = spMap ψ.toRingHom)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) (K : ℤ) (k : ℕ)
    (hK : K = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y'.x)))
    (hF' : ∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L K (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) :
    ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' K (F' b) (colOf m b) := by
  subst hK
  obtain ⟨hx, hu, -⟩ := hm
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  dsimp only at hx hu h hh F' hF'
  have hu' : u' = fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ y.u τ i := funext fun τ => funext fun i => hu τ i
  have hx' : x' = spMap (ψ : S →+* S') ≫ y.x := hx
  subst hx'
  subst hu'
  have hh' : h = ptBC (ψ : S →+* S') y.x := Over.OverMorphism.ext hh
  subst hh'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  choose f hf using fun b => hex k (F b)
  obtain ⟨B', x2, e2, -, hF, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩ :=
    GlobalTheory.rawChart_baseChange E H Dw l Xo c S S' ψ y.x y.u (ChartAt.toRaw C)
  let z : FrPt Xo c S' := ⟨_, xo', _, tan', eig', basis', s', gen'⟩
  set_option backward.isDefEq.respectTransparency false in
  let C2 : ChartAt Xo c z :=
    ⟨C.d, B', fun ℓ j => ψ (C.uvec ℓ j), x2, e2, C.wP, MvPowerSeries.map (ψ : S →+* S') C.h,
      ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩,
      ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, C.prim, hga, hrig⟩
  have hg2 : ∀ b, IsGerm z C2.d C2.x C2.B.A.act C2.e C2.wP k (F' b)
      (MvPowerSeries.map (ψ : S →+* S') (f b)) := fun b => hgerm k (F b) (F' b) (f b) (hF' b) (hf b)
  obtain ⟨C3, hex3, hpin3⟩ := hnab.2 S' z
  choose f3 hf3 using fun b => hex3 k (F' b)
  have hI := GlobalTheory.T.harmonicValue_germs_independent_of_chart E H Dw l Xo c hnab.1 S' z C2 C3 k n F' _ f3 hg2 hf3 a P hP
  have e3 : (∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab z k (F' b) (colOf m b)) =
      chartVal C3 k f3 P := by
    unfold chartVal
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun b _ => hpin3 k (F' b) (f3 b) (hf3 b) (colOf m b)
  refine Eq.trans ?_ (hI.trans e3.symm)
  unfold chartVal
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, AlgHom.commutes, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hN := nabMap_holds S S' (ψ : S →+* S') C.d (𝓞 E) C.B B' hF hA C.h C.gauge H.w0 k (f b) (Lt1 Dw) C.uvec
    (MvPolynomial.monomial (colOf m b) 1)
  rw [MvPolynomial.map_monomial, map_one] at hN
  exact (congrArg ψ (hpin k (F b) (f b) (hf b) (colOf m b))).trans hN.symm

end GlobalTheory.HarmonicValueToField

namespace GlobalTheory

theorem harmonicValue_baseChange_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Field S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S S' _ _ _ _ ψ y y' hm h hh a n P hP N F F' hF'
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  letI : Algebra ℚ S' := ((algebraMap c.F S').comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨M, hM, hMP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key := HarmonicValueToField.sum_map_of_harmA nab hnab ψ y y' hm h hh a n _ hMP _ (N ^ 2)
    (by push_cast; rfl) F F' hF'
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S), map_mul (algebraMap c.F S'),
    _root_.mul_assoc, ← Finset.mul_sum] at key
  rw [map_mul, AlgHom.commutes] at key
  have hu : IsUnit (algebraMap c.F S' (M : c.F)) :=
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _
  exact hu.mul_left_cancel key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicConnectionValue_baseChange_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Field S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  first | exact @GlobalTheory.harmonicValue_baseChange_field | exact GlobalTheory.harmonicValue_baseChange_field | (intros; apply GlobalTheory.harmonicValue_baseChange_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

noncomputable section

namespace GlobalTheory.DepthLink

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

end GlobalTheory.DepthLink
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombination
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem capelli_eigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A ι S co Fs F h hF
  classical
  have h' : ∀ x : S, _ := fun x => h x.1 x.2
  choose d' A' hd hA N Fi ν hν hC hE hS using h'
  let e := (Fintype.equivFin (Σ x : S, Fin (N x))).symm
  refine ⟨_, fun j g => co (e j).1 • Fi (e j).1 (e j).2 g, fun j => ν (e j).1 (e j).2, ?_, ?_, ?_, ?_⟩
  · intro j s
    exact (hν _ _ s).trans (by exact_mod_cast hd _)
  · intro j
    refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul _ (hC _ _).1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono (hA (e j).1) le_rfl ((hC _ (e j).2).2 m)
    exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ hc⟩
  · intro j Y g hg
    have h1 := Formalism.FourierDecayAlt.P.CutMP.En.cV_smul (k := k) (r := r) (Y : ℂ) (co (e j).1) (Fi (e j).1 (e j).2)
    have h2 := congrFun h1 g
    have h3 : (fun g => co (e j).1 • Fi (e j).1 (e j).2 g) = co (e j).1 • Fi (e j).1 (e j).2 := rfl
    beta_reduce
    rw [h3, h2, Pi.smul_apply, hE _ _ Y g hg, smul_comm]
  · intro g hg
    rw [hF g hg, Equiv.sum_comp e (fun y : (Σ x : S, Fin (N x)) => co y.1 • Fi y.1 y.2 g),
      Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hS x g hg, Finset.smul_sum]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombinationStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliEigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  first | exact @GlobalTheory.capelli_eigenSum_linearCombination | exact GlobalTheory.capelli_eigenSum_linearCombination | (intros; apply GlobalTheory.capelli_eigenSum_linearCombination <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ErealLeMulOfForallLe
set_option autoImplicit false

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GoodDepth

theorem ramOverZ_ne_zero' {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ramOverZ la ≠ 0 := by
  have hl := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hne0 : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact Formalism.L2.Pj.Crude.crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  have : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := ⟨hmax.eq_of_le hne hle⟩
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal hne0

theorem ereal_le_mul_of_forall_le {x : EReal} {e B : ℝ} (he : 0 < e)
    (h : ∀ ν : ℝ, ((e * ν : ℝ) : EReal) ≤ x → ν ≤ B) : x ≤ ((e * B : ℝ) : EReal) := by
  by_contra hx
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  have h1 : r / e ≤ B := h (r / e) (by rw [mul_div_cancel₀ _ he.ne']; exact hr2.le)
  have h2 : e * B < r := by exact_mod_cast hr1
  rw [div_le_iff₀ he] at h1
  linarith [mul_comm e B]

theorem nuW_bound_of_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], IntChartEx Xo c →
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (B : ℝ), 0 ≤ B →
  (∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e k a n → ν ≤ B) →
  nuW Xo c la k a n ≠ ⊤ ∧ (nuW Xo c la k a n).toReal / (ramOverZ la : ℝ) ≤ B ∧ (B = 0 → nuW Xo c la k a n = 0) := by
  intro E _ _ _ H Dw lv Xo c _ hEx la k a n B hB h
  have he : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (ramOverZ_ne_zero' la)
  have hsup : nuSup Xo c la k a n ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal) := by
    unfold nuSup
    refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun hO => iSup_le fun y =>
      iSup_le fun hy => ?_
    obtain ⟨C⟩ := hEx T io y hy
    exact (iInf_le (fun C : IntChart T io y => nuLocC C e k a n) C).trans
      (ereal_le_mul_of_forall_le he (h T io e hO y hy C))
  have h0 : (0 : ℝ) ≤ (ramOverZ la : ℝ) * B := mul_nonneg he.le hB
  have hW : nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal) :=
    max_le (by exact_mod_cast h0) hsup
  have hW0 : 0 ≤ nuW Xo c la k a n := le_max_left _ _
  refine ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hW, ?_, fun hB0 => ?_⟩
  · rw [div_le_iff₀ he, mul_comm]
    have := EReal.toReal_le_toReal hW (ne_bot_of_le_ne_bot EReal.zero_ne_bot hW0) (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  · rw [hB0, mul_zero, EReal.coe_zero] at hW
    exact le_antisymm hW hW0

end GlobalTheory.GoodDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLattice
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open scoped Matrix nonZeroDivisors
open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_marked_of_component : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  intro D V H Dw l Xo σ' g ty F hty r hr X k φ io hW hef hemb hform
  subst hr
  obtain ⟨hinj, hrange⟩ := hemb
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (gmW V rfl) (io x) (io y)) := by
    intro x y
    have h := trace_herm_gmW V rfl (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [hform, neg_neg, ← h]
    rfl
  obtain ⟨-, P, hP⟩ := (PeriodExists.typeFn_period_exist _ H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨f, h1, h2, h3, h4⟩ := familyUnif_lattice_genus _ H Dw l Xo σ' g ty F k P hP
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← hW.2]
    exact neg_ne_zero.2 X.ξ0_ne
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    (-(-D.host.xi0)) hξ Dw.La (F.Di k).La (fun x y => Dw.EF x y) (fun x y => (F.Di k).EF x y) io hinj
    X.Λ φ hfg hsp X.Λ_fg X.Λ_span hEF
    (fun x y => by
      have := hef x y
      rw [hW.1, hW.2] at this
      exact this) f h1 h2 h3
  obtain ⟨u, hu, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank X.Λ X.Λ_fg
    X.Λ_span).1
  refine ⟨u, ?_, fun a ha => ?_⟩
  · rw [(hlat u).1, hug]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    rw [AdLat.latOf, hg1]
    exact (hc v).symm
  · obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hgw⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    have hmem : ∀ z, z ∈ latGHat V u ↔ z ∈ AdLat.hat D.host.F (X.Λ : Set (Fin V.rank → D.host.E)) := by
      intro z
      rw [← SetLike.mem_coe, (hlat u).2, hug, hg1, SetLike.mem_coe]
    rw [hug]
    refine ⟨-(AdLat.fv D.host.F (φ e : Fin V.rank → D.host.E) + w),
      (hmem _).2 (neg_mem (add_mem ((hc _).2 (φ e).2) hw)), ?_⟩
    change AdLat.fv D.host.F (φ (F.t k a) : Fin V.rank → D.host.E) - gf.1 *ᵥ AdLat.fv D.host.F (io a) = _
    rw [hgw, he, map_add (f := _), map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, AdLat.cap_fv_add,
      AdLat.cap_fv_nsmul]
    exact comp_sub_eq _ _ _ _

end GlobalTheory.ShortMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLatticeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_element_of_marked_component_lattice : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  first | exact @GlobalTheory.ShortMove.exists_marked_of_component | exact GlobalTheory.ShortMove.exists_marked_of_component | (intros; apply GlobalTheory.ShortMove.exists_marked_of_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometries
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_adelic_of_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  intro D V H Dw io hio hEF s hν
  obtain ⟨hinj, hrange⟩ := hio
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : D.host.xi0 ≠ 0 := by
    have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
    have h2 : D.host.sqrtMinusD ≠ 0 := by
      intro h
      have := D.host.sqrtMinusD_sq
      rw [h] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := by
        have := D.host.qd_big.2
        exact_mod_cast (by omega : D.host.d ≠ 0)
      apply hd
      linear_combination this
    exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hA : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 *
      ∑ a, ∑ b, io x a * (-V.gram.transpose) a b * c (io y b)) := by
    intro x y
    rw [hEF, ← trace_herm_gmW V rfl, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    D.host.xi0 hξ Dw.La Dw.La (fun x y => Dw.EF x y) (fun x y => Dw.EF x y) io hinj
    (LinearMap.range io) (LinearEquiv.ofInjective io hinj) hfg hsp hfg hsp hA hA s.f
    (fun n m hn hm a => by
      obtain ⟨e, he⟩ := s.tower n m hn hm a
      exact ⟨e, by rw [← he, add_sub_cancel]⟩)
    (fun n hn => by
      obtain ⟨g, hg⟩ := s.inv n hn
      refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
      · rintro ⟨e, he⟩
        obtain ⟨b, hb⟩ := (hg a).1
        exact ⟨g e - b, by rw [smul_sub, ← hb, he, map_nsmul, sub_sub_cancel]⟩
      · rintro ⟨e, he⟩
        exact ⟨s.f n e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, hb⟩ := (hg a').2
        exact ⟨g a', -b, by rw [smul_neg, ← hb, neg_sub, add_sub_cancel]⟩)
    (fun n hn a a' => by
      have := s.mult n hn a a'
      rwa [hν, one_mul] at this)
  obtain ⟨u, -, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have h1 : (latGHat V 1 : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
      AdLat.hat D.host.F (LinearMap.range io : Set (Fin V.rank → D.host.E)) := by
    rw [(hlat 1).2, map_one, Units.val_one]
    ext z
    simp
  refine ⟨u, SetLike.coe_injective ?_, fun N hN a => ?_⟩
  · rw [(hlat u).2, hug, hg1, h1]
  · obtain ⟨w, hw, hgw⟩ := hg2 N hN a
    refine ⟨w, ?_, ?_⟩
    · rw [← SetLike.mem_coe, h1]
      exact hw
    · rw [hug]
      exact hgw

end GlobalTheory.ShortMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometriesStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_of_lattice_isometries : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  first | exact @GlobalTheory.ShortMove.exists_adelic_of_isometry | exact GlobalTheory.ShortMove.exists_adelic_of_isometry | (intros; apply GlobalTheory.ShortMove.exists_adelic_of_isometry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientElliptic
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientElliptic
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ScaledQuot

theorem not_inOK_neg_half (d : ℕ) (hd : 0 < d) : ¬ InOK d ((0 : ℂ) - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have h2 : (2 * u : ℝ) = -1 := by
    simp at hre
    linarith
  have h3 : (2 * u : ℤ) = -1 := by exact_mod_cast h2
  omega

theorem inOK_nat_mul (d s : ℕ) {l : ℂ} (hl : InOK d l) : InOK d ((s : ℂ) * l) := by
  obtain ⟨u, v, rfl⟩ := hl
  exact ⟨s * u, s * v, by push_cast; ring⟩

theorem inOK_nat (d s : ℕ) : InOK d (s : ℂ) := ⟨s, 0, by simp⟩

theorem zero_iff_of_fixed {d : ℕ} {θ : ℂ → ℂ} {x : ℂ} (h : W1 d x θ = θ) (z : ℂ) :
    θ (z + x) = 0 ↔ θ z = 0 := by
  have := congrFun h z
  rw [← this]
  simp [W1, U1, Complex.exp_ne_zero]

theorem scaled_quotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  intro d q _ M ω θ hd hd7 hsp hL hch hθ t s hs hsq hst φ
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  obtain ⟨-, -, hUd, -, -, hper, -, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  obtain ⟨-, -, -, -, -, hint, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hsp
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hsp hL hch
  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hN : ∀ p, AnalyticAt ℂ (fun z => U1 d t θ ((s : ℂ) * z)) p := fun p =>
    ((hUd t θ hdiff).1.comp hlin).analyticAt p
  have hD : ∀ p, AnalyticAt ℂ (fun z => θ ((s : ℂ) * z)) p := fun p =>
    (hdiff.comp hlin).analyticAt p
  have han : ∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    (hN p).div (hD p) hp
  have hE : Ell M.L φ := by
    refine ⟨fun p => (hN p).meromorphicAt.div (hD p).meromorphicAt, ?_⟩
    intro l hl z
    have hl' : InOK d l := (hL l).1 hl
    have hWl := hW _ (inOK_nat_mul d s hl')
    have hk : kap1 d ((s : ℂ) * l) t = 1 := by
      obtain ⟨k, hk⟩ := hint l _ hl' hst
      have e : h1 d ((s : ℂ) * l) t = h1 d l ((s : ℂ) * t) := by
        simp only [h1, map_mul, Complex.conj_natCast]; ring
      rw [kap1, e, hk]
      have := Complex.exp_int_mul_two_pi_mul_I (-k)
      rw [← this]
      congr 1
      push_cast; ring
    have hp := hper θ t ((s : ℂ) * l) ((s : ℂ) * z) hWl
    rw [hk, one_mul] at hp
    show U1 d t θ ((s : ℂ) * (z + l)) / θ ((s : ℂ) * (z + l)) = U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)
    rw [mul_add]
    by_cases hz0 : θ ((s : ℂ) * z) = 0
    · rw [hz0, (zero_iff_of_fixed hWl _).2 hz0, div_zero, div_zero]
    · have hz1 : θ ((s : ℂ) * z + (s : ℂ) * l) ≠ 0 := fun h => hz0 ((zero_iff_of_fixed hWl _).1 h)
      rw [div_eq_div_iff hz1 hz0]
      exact hp
  have hA0 : AnalyticAt ℂ φ 0 := han 0 (by rw [mul_zero, h0]; exact one_ne_zero)
  have hpole : ∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p := by
    intro p r hr hr2 hθ0 hsmall
    exact hr2 (hsm p s r (inOK_nat d s) (by exact_mod_cast hs.ne') hr (hz _ hθ0) hsmall).2
  refine ⟨hE, hA0, han, hpole, GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ φ hch hE hA0 ?_⟩
  intro p hp
  have hθp : θ ((s : ℂ) * p) = 0 := by
    by_contra hne
    exact absurd hp (not_lt.mpr (han p hne).meromorphicOrderAt_nonneg)
  exact hpole p 0 ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (not_inOK_neg_half d hd.pos) (by rw [add_zero]; exact hθp)

end GlobalTheory.MomOne.ScaledQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientEllipticStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledThetaTranslationQuotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic | exact GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic | (intros; apply GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic <;> assumption)
end
end

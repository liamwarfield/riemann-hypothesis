module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SwapAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.RigidF
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem normV_eq_absNorm {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : Formalism.ConjugateSelfDual.normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

private theorem normV_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (h : GM.Split M (w.under (𝓞 K))) :
    Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
  have hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
    ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w,
      ← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  simp only [normV_eq_absNorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, Nat.eq_one_of_mul_eq_one_left h1, pow_one]

private theorem summand_of_irr {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {τ : Submodule ℂ (L2 μ)} (h : CuspIrr μ τ) : IsSummand μ τ :=
  ⟨h.le, h.closed, h.inv, h.ne, h.irr⟩

private theorem sat_single {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ι : Type} {κ : ι → Type}
    [∀ i, Fintype (κ i)] {m : (Σ i, κ i) → ℕ} (Q : ∀ a, CG E (m a))
    (hinj : Function.Injective (Sigma.fst : (Σ i, κ i) → ι)) (a : Σ i, κ i) {w : HeightOneSpectrum (𝓞 E)}
    {C : Multiset ℂˣ} (h : R.sumSat (m := fun k : κ a.1 => m ⟨a.1, k⟩) (fun k => Q ⟨a.1, k⟩) w C) : (Q a).HasSat w C := by
  obtain ⟨i, k₀⟩ := a
  obtain ⟨D, hD, rfl⟩ := h
  have hu : ∀ k : κ i, k = k₀ := fun k => by
    have : (⟨i, k⟩ : Σ i, κ i) = ⟨i, k₀⟩ := hinj rfl
    simpa using this
  rw [Fintype.sum_eq_single k₀ fun k hk => absurd (hu k) hk]
  exact hD k₀

private theorem sat_of_sigma {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n n' : ℕ} {p : CG E n} {q : CG E n'}
    (h : (⟨n, p⟩ : Σ a, CG E a) = ⟨n', q⟩) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (hq : q.HasSat w B) :
    p.HasSat w B := by
  cases h
  exact hq

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.rigidF :
    T.LiftAll → RigidF := by
  intro hL
  unfold RigidF ForSwap
  intro F E _ _ _ _ _ _ _ _ σ h2 hgen τ₁ τ₂ θ₂ hP hgal h12 h21 SE SF hSE hSF m₁ m₂ B₁ B₂ hA₁ hA₂ b Λ' t' hb hbc
  have hp : (Module.finrank F E).Prime := h2 ▸ Nat.prime_two
  obtain ⟨-, hsw⟩ := swapAt F E σ h2 hgen τ₁ τ₂ θ₂ hP hgal h12 h21
  have s₁ := summand_of_irr hP.irr₁
  have s₂ := summand_of_irr hP.irr₂
  obtain ⟨π₁, c₁, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ₁ s₁
  obtain ⟨π₂, c₂, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ₂ s₂
  obtain ⟨P, hPt⟩ := T.famSat F (2 + 2) b SF hSF Λ' t' hb
  choose κ fκ m Q hm hne hQ using fun i => hL F E σ hgen hp (b.d i) (b.pos i) (P i)
  have hsum := R.liftSum F E hp (Fin b.r) κ b.d (fun a => m a.1 a.2) P (fun a => Q a.1 a.2) hQ
  have hN := (T.places F E hp).2.2.2.2.1
  have hund := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ (B : Fin 2 → Multiset ℂˣ) (B' : (Σ i, κ i) → Multiset ℂˣ),
      (∀ i, ((![CG.mk π₁, CG.mk π₂] : Fin 2 → CG E 2) i).HasSat w (B i)) ∧ (∀ a, (Q a.1 a.2).HasSat w (B' a)) ∧
        ∑ i, B i = ∑ a, B' a := by
    filter_upwards [hsum, hSE.eventually_cofinite_notMem, hund.eventually hSF.eventually_cofinite_notMem] with w hw hwE hwF
    obtain ⟨B, ⟨B1, hB1, e1⟩, D, hD, eD⟩ := hw (UpperTheory.ConvolutionTheory.resDeg F w) (by
      simpa only [normV_eq_absNorm] using hN w)
    obtain ⟨C, ⟨C1, hC1, e2⟩, e⟩ := hPt _ hwF
    obtain ⟨A₁, a₁, h₁⟩ := (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w _).1 (hA₁.2 w hwE)
    obtain ⟨A₂, a₂, h₂⟩ := (Dp.sSatIff E 2 _ π₂ τ₂ c₂ w _).1 (hA₂.2 w hwE)
    have e3 : B = C := by
      rw [e1, e2]
      exact Finset.sum_congr rfl fun i _ => (hB1 i).unique (hC1 i)
    refine ⟨![A₁, A₂], D, fun i => ?_, hD, ?_⟩
    · fin_cases i
      exacts [h₁, h₂]
    · have hb := hbc w hwE
      rw [bcSat, e, a₁, a₂, Multiset.map_map] at hb
      refine Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) (fun a b e => Units.ext e) ?_
      rw [← eD, e3, Fin.sum_univ_two, Multiset.map_map]
      simpa using hb
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E (Fin 2) (Σ i, κ i) (fun _ => 2) (fun a => m a.1 a.2)
    ![CG.mk π₁, CG.mk π₂] (fun a => Q a.1 a.2) (fun _ => by norm_num) (fun a => hm a.1 a.2) hev
  have hcard : Fintype.card (Σ i, κ i) = 2 := by simpa using (Fintype.card_congr s).symm
  have hsurj : Function.Surjective (Sigma.fst : (Σ i, κ i) → Fin b.r) := fun i => ⟨⟨i, (hne i).some⟩, rfl⟩
  have hinj : Function.Injective (Sigma.fst : (Σ i, κ i) → Fin b.r) := by
    refine ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, ?_⟩).1
    have h1 := Fintype.card_le_of_surjective _ hsurj
    have h3 := b.two
    simp only [Fintype.card_fin] at h1 ⊢
    omega
  have hl0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ f : ℕ,
      Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f →
        ∃ B, (P (s 0).1).HasSat (w.under (𝓞 F)) B ∧ (CG.mk π₁).HasSat w (B.map (· ^ f)) :=
    (hQ (s 0).1).mono fun w hw f hf => by
      obtain ⟨B, hB, hC⟩ := hw f hf
      exact ⟨B, hB, sat_of_sigma (hs 0) (sat_single (fun a => Q a.1 a.2) hinj (s 0) hC)⟩
  obtain ⟨X, hX, hlift⟩ : ∃ X : Set (HeightOneSpectrum (𝓞 E)), X.Finite ∧ ∀ w ∉ X, ∀ f : ℕ,
      Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f →
        ∃ B, (P (s 0).1).HasSat (w.under (𝓞 F)) B ∧ (CG.mk π₁).HasSat w (B.map (· ^ f)) :=
    ⟨_, Filter.eventually_cofinite.1 hl0, fun w hw => not_not.1 hw⟩
  have hev2 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w ∉ SE ∧ SSat (BW.mu1 E 2) τ₁ w (B₂ w) := by
    filter_upwards [hund.eventually (R.decomp F E hp), hund.eventually (hX.image fun w => w.under (𝓞 F)).eventually_cofinite_notMem,
      hSE.eventually_cofinite_notMem] with w hd hy hwE
    refine ⟨hwE, ?_⟩
    have hg : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → w' ∉ X :=
      fun w' hu hc => hy ⟨w', hc, hu⟩
    have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) := by
      rw [normV_eq_absNorm]
      exact NumberField.HeightOneSpectrum.one_lt_absNorm _
    rcases hd with ⟨hc, hn⟩ | ⟨-, hn⟩
    · obtain ⟨⟨w', hu⟩, hne', -⟩ := (Nat.card_eq_two_iff' (⟨w, rfl⟩ : {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 F) = w.under (𝓞 F)})).1
        (hc.trans h2)
      have hne : w ≠ w' := fun e => hne' (Subtype.ext e.symm)
      obtain ⟨B, hB, hw1⟩ := hlift w (hg w rfl) 1 (by rw [pow_one]; exact hn w rfl)
      obtain ⟨B', hB', hw2⟩ := hlift w' (hg w' hu) 1 (by rw [pow_one, hu]; exact hn w' hu)
      rw [hu] at hB'
      obtain rfl := hB.unique hB'
      obtain ⟨Y, eY, hY⟩ := (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w' _).1 ((hsw w w' hu.symm (Or.inl hne) _).1 (hA₂.2 w hwE))
      have hY' : (CG.mk π₁).HasSat w' Y := hY
      obtain rfl : Y = B.map (· ^ 1) := hY'.unique hw2
      exact (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w _).2 ⟨_, eY, hw1⟩
    · have hns : ¬ GM.Split E (w.under (𝓞 F)) := fun h => by
        have e := (hn w rfl).symm.trans (normV_split w h)
        rw [h2] at e
        have : (2 : ℕ) = 1 := Nat.pow_right_injective hq (e.trans (pow_one _).symm)
        omega
      exact (hsw w w rfl (Or.inr hns) _).1 (hA₂.2 w hwE)
  have hτ : τ₁ = τ₂ := Dp.atInj E 2 _ τ₁ τ₂ s₁ s₂ _ (Filter.eventually_cofinite.1 hev2) B₂
    (fun w hw => (not_not.1 hw).2) (fun w hw => hA₂.2 w (not_not.1 hw).1)
  have ho := hP.orth
  rw [← hτ] at ho
  exact hP.irr₁.ne (Submodule.isOrtho_self.1 ho)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.NotConjIso
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section Pow

open Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem pow_val {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-s) := by
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · have hx' : Valued.v (x : v.adicCompletion K) = 1 := hx
    rw [pow_loc h, FinitePlace.norm_def, hx']
    simp
  · have hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      unif_spec v
    refine (pow_loc h v (atFin v (unif v))).trans ?_
    rw [FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have e' : normV v = Ideal.absNorm v.asIdeal := by
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [WithZero.log_exp, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

private theorem exists_place (E : Type) [Field E] [NumberField E] : Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩

private theorem absC_pow (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℂ) : IsPow (GlobalTheory.CuspRep.Model.absC E s) s := by
  obtain ⟨b, hb⟩ := GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E)
    (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E)
    (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)
  have hgen : ∀ z : ℂ, IsPow (GlobalTheory.CuspRep.Model.absC E z) (z * b) := fun z y => by
    change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E y).2
    rw [hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
    congr 1
    push_cast
    ring
  have hb1 : b = 1 := by
    obtain ⟨w⟩ := exists_place E
    have h1 := (pow_val (hgen 1) w).2
    have e' : normV w = Ideal.absNorm w.asIdeal := by
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [PositivityTheory.Rg.Rs.StrStepB.absC_val, e'] at h1
    have h0 : 1 < (Ideal.absNorm w.asIdeal : ℕ) := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h2 := congrArg norm h1
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_natCast_cpow_of_pos (by omega),
      show (-(1 : ℂ)).re = -1 by simp, show (-(1 * (b : ℂ))).re = -b by simp] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ))),
      Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ)))] at h3
    have h4 : Real.log (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast h0)).ne'
    linarith [mul_right_cancel₀ h4 h3]
  simpa [hb1] using hgen s

private theorem pow_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {s : ℂ} (h : IsPow χ s) :
    χ = GlobalTheory.CuspRep.Model.absC E s :=
  Subtype.ext (MonoidHom.ext fun x => Units.ext ((h x).trans (absC_pow E s x).symm))

private theorem pow_expo {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {s : ℂ} (h : IsPow χ s)
    (τ : E →+* ℂ) : expo χ τ = s := by
  rw [pow_eq h, GlobalTheory.CuspRep.Model.expo_absC]

end Pow

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Formalism.L2.Host Formalism.ConjugateSelfDual

private theorem norm_deg (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm

private theorem deg_sum (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 F) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_split (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 F) = w.under (𝓞 F)) : normV w = normV (w.under (𝓞 F)) := by
  classical
  have := w.isPrime
  have := w'.isPrime
  have hu' : (w.under (𝓞 F)).asIdeal = w'.asIdeal.under (𝓞 F) := (congrArg HeightOneSpectrum.asIdeal hu).symm
  have hs := deg_sum h2 (w.under (𝓞 F)) {⟨w'.asIdeal, w'.isPrime, ⟨hu'⟩⟩, ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_pair fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h))] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have h4 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  rw [norm_deg (F := F) w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by dsimp only at hs; omega, pow_one]

private theorem gal_two (h2 : Module.finrank F E = 2) : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 ∧ ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ := by
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact ⟨y, hy, fun τ => (em (τ = 1)).imp_right (hy' τ)⟩

end Places

section Conj

open Formalism.L2.Host UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Bc

private theorem infOf_ne {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) : infOf m ≠ infOf m' := by
  intro e
  have h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m := Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩
  rw [e] at h1
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h1
  have h2 : m' i = m 0 := Int.cast_injective (add_left_cancel hi)
  fin_cases i
  · exact absurd (@h 2 0 h2) (by decide)
  · exact absurd (@h 3 0 h2) (by decide)

open UpperTheory.CBC UpperTheory.CBC.SConjSpaceCAux in
private theorem not_conjIso {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    (h2 : Module.finrank K M = 2) (π : CuspSub M 2) (hm : MixWtC K π) (σ : M ≃ₐ[K] M) (h1σ : σ ≠ 1) :
    ¬ (Cusp.cx π).ConjIso σ.toRingEquiv := by
  intro h
  have : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨m, m', τ, τ', hne, h1, h2', k1, k2, hinj⟩ := hm φ
  obtain ⟨σ₀, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2'.symm)
  obtain ⟨y, -, hy⟩ := gal_two (F := K) (E := M) h2
  have h0 : σ₀ ≠ 1 := by
    rintro rfl
    exact hne (RingHom.ext fun x => (RingHom.congr_fun hσ x))
  obtain rfl : σ₀ = σ := ((hy σ₀).resolve_left h0).trans ((hy σ).resolve_left h1σ).symm
  obtain ⟨s, hs⟩ := SGalAdEx_holds M σ₀.toRingEquiv
  obtain ⟨P', hsp, hiso⟩ := h s hs
  obtain ⟨d, hd, hd'⟩ := exists_GD _ s hs
  cases P' with
  | re π' => exact hiso.elim
  | cx π' =>
    have e : τ.comp (d.σ.symm : M →+* M) = τ' := by
      rw [hd']
      exact hσ
    have k3 : π'.HasInfChar τ (infOf m') := by
      refine ⟨k2.1, fun u x hx => ?_⟩
      have hx' : x.1 ∈ (Cusp.cx π').space := ⟨x, hx, rfl⟩
      rw [hsp] at hx'
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx'
      obtain rfl : x = pull d 2 y := Subtype.ext (by rw [← hxy, ← hd]; rfl)
      rw [cap_pull, e, k2.2 u y hy, map_smul]
    exact infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))

end Conj

section Main

open Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T

private theorem satTw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {π : CuspSub E a}
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) {χ : HChar E}
    (hu : χ.UnrAt w) : (CG.mk (π.twist χ)).HasSat w (B.map (· * χ.val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist E a π χ w B hu h

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs :
    IndNorm → IndCs := by
  intro hN K M _ _ hK _ _ hM _ h2 π hm hS
  have hq : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  have hn : 1 ≤ (2 : ℕ) := by decide
  let μ : Measure (normOneGL (K := M) (n := 2)) := Measure.haar
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ :
      ∃ χ : HChar M, (∃ s : ℂ, IsPow χ s) ∧ ∃ V, Dp.Carries μ (π.twist χ) V :=
    Dp.exTwist M 2 μ π hn
  obtain ⟨hex, hpw⟩ := powTwist K M
  obtain ⟨χ₀, hχ₀⟩ := (hex s).1
  obtain ⟨hi₀, hi, htw⟩ := hpw s χ₀ χ hχ₀ hχ
  have hback := (htw 2 hn).2.1 π
  have hCj := ((hpw (-s) χ₀⁻¹ χ⁻¹ hi₀ hi).2.2 2 hn).2.2.2.1
  have hnorm : GlobalTheory.DiscSpec.IsNormalised (π.twist χ) :=
    (Dp.normIff M 2 _).2 ((Dp.exSummand M 2 μ _ V).1 hV).1
  have hnc : ∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ¬ (UpperTheory.CBC.Cusp.cx (π.twist χ)).ConjIso σ.toRingEquiv := fun σ h1 hc =>
    not_conjIso h2 π hm σ h1 (by simpa only [hback] using hCj _ _ hc)
  have hsb : SplitBad K (π.twist χ) := fun v hv => ⟨(hS v hv).1, fun w hw =>
    let ⟨_, hB⟩ := (hS v hv).2 w hw
    ⟨_, satTw hB (pow_val hχ w).1⟩⟩
  obtain ⟨P, hP, hI⟩ := hN K M h2 (π.twist χ) hnorm hnc hsb
  have hun : ∀ {w : HeightOneSpectrum (𝓞 M)} {B : Multiset ℂˣ}, (CG.mk (π.twist χ)).HasSat w B →
      (CG.mk π).HasSat w (B.map (· * χ⁻¹.val w)) := fun {w B} h => by
    have h1 := satTw h (pow_val hi w).1
    rwa [hback] at h1
  have hv : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f →
      χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) ^ f := fun w f hf => by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (pow_val hi _).2, (pow_val hi₀ _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul]
  refine ⟨P.twist χ₀⁻¹, hP.mono fun w hw => ⟨fun w' hne e => ?_, fun hq2 => ?_⟩, fun τ τ' m m' hne hc k1 k2 => ?_⟩
  · obtain ⟨B, B', k1, k2, k3⟩ := hw.1 w' hne e
    have e1 : χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) :=
      (hv w 1 ((norm_split h2 hne e).trans (pow_one _).symm)).trans (pow_one _)
    have e2 : χ⁻¹.val w' = χ₀⁻¹.val (w.under (𝓞 K)) := by
      rw [← e]
      exact (hv w' 1 ((norm_split h2 hne.symm e.symm).trans (by rw [e, pow_one]))).trans (pow_one _)
    refine ⟨_, _, hun k1, hun k2, ?_⟩
    rw [e1, e2, ← Multiset.map_add (f := _)]
    exact satTw k3 (pow_val hi₀ _).1
  · obtain ⟨_, B', k1, rfl, k3⟩ := hw.2 hq2
    refine ⟨_, B'.map (· * χ₀⁻¹.val (w.under (𝓞 K))), ?_, ?_, satTw k3 (pow_val hi₀ _).1⟩
    · have k4 := hun k1
      rw [hv w 2 hq2] at k4
      simpa only [Multiset.map_map, Function.comp_def, mul_pow] using k4
    · simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, neg_mul]
  · have k := (hI τ τ' _ _ hne hc (k1.twist χ) (k2.twist χ)).twist χ₀⁻¹
    rw [pow_expo hχ, pow_expo hχ, pow_expo hi₀, ← Multiset.map_add (f := _), Multiset.map_map] at k
    simpa using k

end Main
end

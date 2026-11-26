module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LaHatMod

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

theorem valued_algebraMap (w : HeightOneSpectrum ℤ) (q : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) = w.valuation ℚ q :=
  valuedAdicCompletion_eq_valuation' w q

theorem exists_int_valued_sub_le (w : HeightOneSpectrum ℤ) {x : w.adicCompletion ℚ} (hx : Valued.v x ≤ 1)
    {c : ℚ} (hc0 : c ≠ 0) (hc : w.valuation ℚ c ≤ 1) :
    ∃ r : ℤ, Valued.v (x - (r : w.adicCompletion ℚ)) ≤ w.valuation ℚ c := by
  set c' : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) c
  have hc' : c' ≠ 0 := by
    simp only [c', ne_eq, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact hc0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v c' := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc')
  have hU : IsOpen ((fun y => (y - x) / c') ⁻¹' (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) :=
    (Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).div_const c')
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := ℚ) w).exists_mem_open hU
    ⟨x, by simp [SetLike.mem_coe, sub_self, zero_div]⟩
  have hk' : Valued.v (x - algebraMap ℚ (w.adicCompletion ℚ) k) ≤ w.valuation ℚ c := by
    have h : Valued.v ((algebraMap ℚ (w.adicCompletion ℚ) k - x) / c') ≤ 1 := hk
    rw [map_div₀, div_le_one₀ hpos] at h
    rw [Valuation.map_sub_swap, ← valued_algebraMap]; exact h
  have hk1 : w.valuation ℚ k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap ℚ (w.adicCompletion ℚ) k = x - (x - algebraMap ℚ (w.adicCompletion ℚ) k) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hk'.trans hc))
  have hne : w.valuation ℚ c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hk1 (Units.mk0 _ hne)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r)) ≤ w.valuation ℚ c := by
    rw [valued_algebraMap, Valuation.map_sub_swap]; exact hr.le
  have e : x - (r : w.adicCompletion ℚ) =
      (x - algebraMap ℚ (w.adicCompletion ℚ) k) + algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r) := by
    rw [map_sub, algebraMap_int_eq, eq_intCast, map_intCast]; ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le hk' hr')

variable {p : ℕ} [Fact p.Prime]

theorem valued_intCast (w : HeightOneSpectrum ℤ) (z : ℤ) :
    Valued.v ((z : w.adicCompletion ℚ)) ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ (w.adicCompletion ℚ)), valued_algebraMap]
  have := w.valuation_le_one (K := ℚ) z
  simpa using this

theorem exists_int_add_prime_mul (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (l : AfP p) * a' := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  let w0 : HeightOneSpectrum ℤ := ⟨Ideal.span {(l : ℤ)}, hmax.isPrime, by simpa using hl0⟩
  have hw0 : w0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have hp : (p : ℤ) ∈ Ideal.span {(l : ℤ)} := by
      change (p : ℤ) ∈ w0.asIdeal; rw [h]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hp
    have hd : l ∣ p := by exact_mod_cast hp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) l hd) with h1 | h1
    · exact hl.ne_one h1
    · exact hlp h1
  let v0 : AwayP p := ⟨w0, hw0⟩
  have hlq0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlv : ∀ w : HeightOneSpectrum ℤ, w.valuation ℚ (l : ℚ) ≤ 1 := fun w => by
    have := w.valuation_le_one (K := ℚ) (l : ℤ); simpa using this
  obtain ⟨z, hz⟩ := exists_int_valued_sub_le w0 (ha v0) hlq0 (hlv w0)
  refine ⟨z, (a - (z : AfP p)) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹, ?_, ?_⟩
  · intro v
    rw [mem_adicCompletionIntegers, map_mul, map_sub, map_intCast, AlgHom.commutes, Valuation.map_mul,
      valued_algebraMap, map_inv₀]
    have hne : v.1.valuation ℚ (l : ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 hlq0
    by_cases hv : v = v0
    · subst hv
      rw [mul_inv_le_iff₀ (zero_lt_iff.2 hne), _root_.one_mul]
      exact hz
    · have hnot : (l : ℤ) ∉ v.1.asIdeal := by
        intro hm
        apply hv
        have hle : Ideal.span {(l : ℤ)} ≤ v.1.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hm
        have heq := hmax.eq_of_le v.1.isPrime.ne_top hle
        exact Subtype.ext (HeightOneSpectrum.ext heq.symm)
      have h1 : v.1.valuation ℚ (l : ℚ) = 1 := by
        have := (valuation_eq_one_iff_notMem (v := v.1) (K := ℚ) (r := (l : ℤ))).2 hnot
        simpa using this
      rw [h1, inv_one, _root_.mul_one]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha v) (valued_intCast v.1 z))
  · have e : (l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hlq0, map_one]
    calc a = (z : AfP p) + (a - (z : AfP p)) * ((l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹) := by
          rw [e, _root_.mul_one]; ring
      _ = _ := by ring

theorem exists_int_add_mul (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (n : AfP p) * a' := by
  induction n using Nat.recOnMul generalizing a with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact ⟨0, a, ha, by simp⟩
  | prime l hl =>
    exact exists_int_add_prime_mul l hl (fun h => by
      subst h; exact hl.ne_one ((Nat.coprime_self _).1 hnp)) a ha
  | mul m k ihm ihk =>
    have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    obtain ⟨hmp, hkp⟩ := Nat.coprime_mul_iff_left.1 hnp
    obtain ⟨z1, a1, h1, e1⟩ := ihm hm hmp a ha
    obtain ⟨z2, a2, h2, e2⟩ := ihk hk hkp a1 h1
    exact ⟨z1 + m * z2, a2, h2, by rw [e1, e2]; push_cast; ring⟩

end GlobalTheory.LKGeo.LaHatMod

namespace GlobalTheory.LKGeo

theorem exists_inAf_add_nsmul_of_mem_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p →
    ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  intro p _ D n hn hnp v hv
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    obtain ⟨z, a', ha', e⟩ := LaHatMod.exists_int_add_mul n hn hnp a ha
    refine ⟨z • x, a' ⊗ₜ ((1 : ℚ) ⊗ₜ x), AddSubgroup.subset_closure ⟨a', x, ha', rfl⟩, ?_⟩
    have h1 : ((z : AfP p)) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] (z • x)) := by
      rw [show (z : AfP p) = (z : ℚ) • (1 : AfP p) by rw [← Algebra.algebraMap_eq_smul_one, map_intCast],
        TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        show (z : ℚ) • (1 : ℚ) = z • (1 : ℚ) by simp, TensorProduct.smul_tmul]
    have h2 : ((n : AfP p) * a') ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = n • (a' ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [e, TensorProduct.add_tmul, h1, h2, inAf]
  | zero => exact ⟨0, 0, zero_mem _, by simp [inAf]⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨x, w, hw, e⟩ := ih
    obtain ⟨x', w', hw', e'⟩ := ih'
    refine ⟨x + x', w + w', add_mem hw hw', ?_⟩
    rw [e, e', inAf, inAf, inAf, TensorProduct.tmul_add, TensorProduct.tmul_add, smul_add]
    abel
  | neg u _ ih =>
    obtain ⟨x, w, hw, e⟩ := ih
    refine ⟨-x, -w, neg_mem hw, ?_⟩
    rw [e, inAf, inAf, TensorProduct.tmul_neg, TensorProduct.tmul_neg, smul_neg, neg_add]

end GlobalTheory.LKGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p → ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  first | (exact @GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat) | (exact GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat) | (intros; apply GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem gBig_both {P Q S : GP} (hP : GBig P) (hQ : GBig Q)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ
    (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G)
    (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩

private theorem fst_fin {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW) (hA : ∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ)
    (hW : ∀ τ, FW.cart τ = X.rW.s τ) (hX : X.Is ψ θ α β νH S) (t : T) : GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hA τ, hW τ]
  exact hF

private theorem snd_fin {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (hA' : ∀ τ, (GlobalTheory.SquareComm.frSgn false FA').cart τ = X.rA'.s τ)
    (hW : ∀ τ, FW.cart τ = X.rW.s τ) (hI : X.Is ψ θ α β νH S) (t : T) : GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t) := by
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [hA' τ, hW τ]
  exact hF

open GlobalTheory.StageDict in
theorem _root_.GlobalTheory.T.towerStage_seesawDictionary_framesSignatures : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
  GlobalTheory.SqTower.IsStageC W i j p q X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) (A.rank - p) p) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) (A'.rank - q) q) ∧
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) (WW.rank - (p + q)) (p + q)) ∧
    ∀ t : T, GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_both GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_
  intro D T Lc sc G μ₀ C x b _ hinf hram W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hsz := stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  have e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ := cart_frSgn_true_rigFr X.rA hXi.rigA
  have e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ := cart_frSgn_false_rigFr X.rA' hXi.rigA'
  have e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ := cart_rigFr X.rW hXi.rigW
  refine ⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, hnA, hnA', hnW, fun t => ⟨?_,
    fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    fst_fin X _ _ _ _ _ _ _ _ e1 e2 hXi t, snd_fin X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩
  · refine
      { hecA := (hXi.weil' t).hecS
        hecB := (hXi.weil t).hecS
        resA := (hXi.weil' t).resS
        resB := (hXi.weil t).resS
        rank := hrk
        even := by rw [hrk]; exact hsz.1
        sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩
        ram := hram W i j p q A A' WW X ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ t }
    have h1 := (hab t τ).2.2
    have h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast (hrk ▸ hsz.2.2.2)
    linarith
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ := funext e1
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B := funext (onb_rigFr X.rA hXi.rigA)
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [f1, f2, f3, f4]
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s := funext e1'
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B := funext (onb_rigFr X.rA' hXi.rigA')
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [f1, f2, f3, f4]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArith
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArith
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem enat_add_natCast_eq_natCast_exists {c : ℕ∞} {a b : ℕ} (h : c + (a : ℕ∞) = (b : ℕ∞)) : ∃ n : ℕ, c = n ∧ n + a = b := by
  induction c using ENat.recTopCoe with
  | top => simp at h
  | coe n => exact ⟨n, rfl, by exact_mod_cast h⟩

theorem dimOne : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ,
    topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧
    ∀ (z : Y) (w : clo z), Order.coheight z = 1 →
      (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  intro k _ Y _ q hq e hY
  have hB := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  have hC := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq (e + 1) hY
  have h1 : ∀ z : Y, Order.coheight z = 1 ↔ HasDim z e := by
    intro z
    obtain ⟨m, hm⟩ := hB.1
    obtain ⟨d, -, hd⟩ := hm z
    obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (hC z d hd)
    constructor
    · intro hz
      rw [hz] at hn
      have : n = 1 := by exact_mod_cast hn.symm
      subst this
      have : d = e := by omega
      exact this ▸ hd
    · intro hz
      have := hB.2.1 z d e hd hz
      subst this
      rw [hn]
      have : n = 1 := by omega
      simp [this]
  refine ⟨h1, fun z w hz => ?_⟩
  have hze : HasDim z e := (h1 z).1 hz
  have hgen : HasDim (genericPoint (clo z)) e := by
    rw [← hB.2.2.2.2.1 (clo z) (cloι z) (genericPoint (clo z)) e, cloι_genericPoint]
    exact hze
  have hdim : topologicalKrullDim (clo z) = e := (hB.2.2.2.2.2 (clo z) e).1 hgen
  refine ⟨hdim, ?_⟩
  have hq' : IsAmb (cloι z ≫ q) := hq.sub (cloι z)
  have hB' := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k (clo z) (cloι z ≫ q) hq'
  obtain ⟨m, hm⟩ := hB'.1
  obtain ⟨d, -, hd⟩ := hm w
  have hd' : HasDim (cloι z w) d := (hB.2.2.2.2.1 (clo z) (cloι z) w d).2 hd
  obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k (clo z) (cloι z ≫ q) hq' e hdim w d hd)
  obtain ⟨n', hn', hnd'⟩ := enat_add_natCast_eq_natCast_exists (hC (cloι z w) d hd')
  have : n' = n + 1 := by omega
  rw [hn, hn', this]
  constructor
  · intro h
    have : n = 1 := by exact_mod_cast h
    simp [this]
  · intro h
    have : n + 1 = 2 := by exact_mod_cast h
    have : n = 1 := by omega
    simp [this]

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧ ∀ (z : Y) (w : clo z), Order.coheight z = 1 → (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  first | exact @GlobalTheory.MixHt.dimOne | exact GlobalTheory.MixHt.dimOne | (intros; apply GlobalTheory.MixHt.dimOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChart
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem functions_are_series : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ n f, G.res n (c.ev (n + 1) f) = c.ev n f) ∧
    (∀ n s, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s) ∧
    ∀ b : ∀ n, G.A n, (∀ n, G.res n (b (n + 1)) = b n) → ∃! f, ∀ n, c.ev n f = b n := by
  intro p k _ d G c
  refine ⟨fun n f => ?_, fun n s => ?_, fun b hb => ?_⟩
  · exact (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A (n + 1))).2 (G.A n) (G.res n : G.A (n + 1) →ₐ[k] G.A n)
      (c.x (n + 1)) (c.nil (n + 1)) (c.x n) (c.nil n) (fun i => c.res n i) f
  · let g : G.A (n + 1) →ₐ[k] G.A n := G.res n
    have h := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A (n + 1) ⊗[k] G.A (n + 1))).2
      (G.A n ⊗[k] G.A n) (Algebra.TensorProduct.map g g)
      (c.x₂ (n + 1)) (c.nil₂ (n + 1)) (c.x₂ n) (c.nil₂ n) (fun i => by
        cases i with
        | inl i => simp [x₂, g, c.res n i]
        | inr i => simp [x₂, g, c.res n i]) s
    refine Eq.trans ?_ h
    rfl
  · exact GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d) G.A c.x c.nil (fun n => (G.res n : G.A (n + 1) →ₐ[k] G.A n))
      (fun n i => c.res n i) c.presents b hb

end GlobalTheory.Katz.Chart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functions_eq_series_in_chart : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n f, G.res n (c.ev (n + 1) f) = c.ev n f) ∧ (∀ n s, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s) ∧ ∀ b : ∀ n, G.A n, (∀ n, G.res n (b (n + 1)) = b n) → ∃! f, ∀ n, c.ev n f = b n := by
  first | exact @GlobalTheory.Katz.Chart.functions_are_series | exact GlobalTheory.Katz.Chart.functions_are_series | (intros; apply GlobalTheory.Katz.Chart.functions_are_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.inRange {X : Node} (h : DefNode D.R.m X) : X.InRange D.R.m := by
  rcases X with ⟨i, j⟩ | i | j
  · exact ⟨h.1, h.2.le⟩
  · exact h.elim
  · exact h

theorem DefNode.sigOK (G : GridData L sc) {X : Node} (h : DefNode D.R.m X) : (G.V X).SigOK := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := h.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact D.sp.X'_sig
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sigOK
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sigOK

theorem vac_exists_of_defPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (p : Pair T), GlobalTheory.FunObj.DefPair D.R.m p → ∃ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f := by
  intro D T L sc G W U N p hp
  obtain ⟨h1, h2⟩ := hp.nodes
  rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
  · exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _
      (GlobalTheory.ChiGrid.WeilOver.sigOK_negSp (h2.sigOK G)) (h1.sigOK G)
      (fun τ => isCartanInv_neg (W.cart_is _ h2.inRange τ)) (fun τ => W.cart_is _ h1.inRange τ) _ _
      (isSelfDualC_neg (N.selfDual h2)) (N.selfDual h1)
  · exact hp.elim
  · exact hp.elim
  · exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (h1.sigOK G) (h2.sigOK G)
      (fun τ => W.cart_is _ h1.inRange τ) (fun τ => W.cart_is _ h2.inRange τ) _ _ (N.selfDual h1) (N.selfDual h2)

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitVacuum_standardLattices_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (p : Pair T), GlobalTheory.FunObj.DefPair D.R.m p → ∃ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f := by
  first | exact @GlobalTheory.FunObj.vac_exists_of_defPair | exact GlobalTheory.FunObj.vac_exists_of_defPair | (intros; apply GlobalTheory.FunObj.vac_exists_of_defPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Base

variable {p : ℕ} [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop}
  (B : GlobalTheory.Dieu.Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' {G : PDivGroup p k} (hG : P k G) : B.map hG hG (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun m => B.smap_id G hG m

theorem map_comp' {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H) (g : H ⟶ K) :
    B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g :=
  LinearMap.ext fun m => B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g))
    (fun _ _ => rfl) m

theorem map_add' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f g : G ⟶ H) :
    B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g :=
  LinearMap.ext fun m => B.smap_add hG hH f g m

def mapAdd {G H : PDivGroup p k} (hG : P k G) (hH : P k H) :
    (G ⟶ H) →+ (B.M H hH →ₗ[WittVector p k] B.M G hG) :=
  AddMonoidHom.mk' (B.map hG hH) (B.map_add' hG hH)

theorem map_zero' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) : B.map hG hH (0 : G ⟶ H) = 0 :=
  map_zero (B.mapAdd hG hH)

theorem map_pow_smul {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (n : ℕ) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m := by
  have e : (p : ℤ_[p]) ^ n • f = (p ^ n) • f := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have e2 : B.map hG hH ((p ^ n) • f) = (p ^ n) • B.map hG hH f := map_nsmul (B.mapAdd hG hH) _ _
  rw [e, e2, LinearMap.smul_apply]

theorem red_map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m) := by
  have := B.red_smap hG hH (SemiHom.ofHom f) m
  rw [SemiHom.ofHom_rig] at this
  exact this

theorem map_F {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m) := by
  let u := (SemiHom.ofHom f).comp (absFrob (p_eq_zero p k) H)
  have e1 : B.smap hG hH u m = B.map hG hH f (B.F H hH m) :=
    B.smap_comp hG hH hH (absFrob (p_eq_zero p k) H) (SemiHom.ofHom f) u (fun _ _ => rfl) m
  have e2 : B.smap hG hH u m = B.F G hG (B.map hG hH f m) :=
    B.smap_comp hG hG hH (SemiHom.ofHom f) (absFrob (p_eq_zero p k) G) u
      (fun n a => by simp only [u, SemiHom.comp_app, SemiHom.ofHom_app, absFrob_app, map_pow]) m
  exact e1.symm.trans e2

theorem finrank_M (G : PDivGroup p k) (hG : P k G) :
    Module.finrank (WittVector p k) (B.M G hG) = G.height := by
  haveI := B.free G hG
  haveI := B.finite G hG
  obtain ⟨_, h5⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p)
    (p_eq_zero p k) (B.red G hG) (B.red_surjective G hG) fun m => (B.red_eq_zero G hG m).1
  exact h5.symm.trans (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p k (p_eq_zero p k) G).2.2.1

theorem eq_zero_of_pow_smul {G : PDivGroup p k} (hG : P k G) (n : ℕ) (m : B.M G hG) (h : p ^ n • m = 0) :
    m = 0 := by
  haveI := B.free G hG
  rw [← Nat.cast_smul_eq_nsmul (WittVector p k)] at h
  refine (smul_eq_zero.1 h).resolve_left ?_
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (WittVector.p_ne_zero p k)

end GlobalTheory.Dieu.Base

namespace GlobalTheory.Dieu

theorem base_functor_props : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  intro p _ P B k _ _ _ G H K hG hH hK
  exact ⟨B.map_id' hG, fun f g => B.map_comp' hG hH hK f g, B.map_add' hG hH, B.map_zero' hG hH,
    B.map_pow_smul hG hH, B.red_map hG hH, B.map_F hG hH, B.finrank_M G hG, B.eq_zero_of_pow_smul hG⟩

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonneFunctorBase_functor_properties : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : GlobalTheory.Dieu.Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 :=
  @GlobalTheory.Dieu.base_functor_props
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem chart_square_presents : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n,
      (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  intro p k _ d G c
  have ht := fun n => GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n)
    (c.nil n) (c.nil₂ n) (c.presents.1 n) (c.presents.1 n)
  refine ⟨⟨fun n => (ht n).1, fun N => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨n, hn⟩ := c.presents.2 N
    exact ⟨n, (ht n).2 N hn hn⟩
  · let r : ∀ n, G.A n.succ ⊗[k] G.A n.succ →ₐ[k] G.A n ⊗[k] G.A n := fun n =>
      Algebra.TensorProduct.map (G.res n : G.A (n + 1) →ₐ[k] G.A n)
        (G.res n : G.A (n + 1) →ₐ[k] G.A n)
    have hr : ∀ n t, r n t = pullbackTwo (G.res n) t := fun n t => by
      induction t with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => rfl
    refine GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d ⊕ Fin d) (fun n => G.A n ⊗[k] G.A n) c.x₂ c.nil₂ r
      (fun n i => ?_) ⟨fun n => (ht n).1, fun N => ?_⟩ z (fun n => by rw [hr]; exact hz n)
    · rw [hr]
      cases i with
      | inl i => simp [Chart.x₂, c.res]
      | inr i => simp [Chart.x₂, c.res]
    · obtain ⟨n, hn⟩ := c.presents.2 N
      exact ⟨n, (ht n).2 N hn hn⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_square_coordinates_present_levels : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n, (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  first | exact @GlobalTheory.chart_square_presents | exact GlobalTheory.chart_square_presents | (intros; apply GlobalTheory.chart_square_presents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.IntDvd

open IsDedekindDomain HeightOneSpectrum

theorem int_dvd_of_local (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) (c : ℤ)
    (h : ∀ v : AwayP p, ∃ y ∈ v.1.adicCompletionIntegers ℚ,
      algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ) = algebraMap ℚ (v.1.adicCompletion ℚ) ((n : ℤ) : ℚ) * y) :
    (n : ℤ) ∣ c := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp
  · obtain ⟨ℓ, hℓ, n₁, hn₁⟩ : ∃ ℓ, ℓ.Prime ∧ ∃ n₁, n = ℓ * n₁ :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have hℓp : ℓ ≠ p := by
      intro he
      have h3 : ℓ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n₁, hn₁⟩ hc
      rw [he, Nat.coprime_self] at h3
      exact (Fact.out : p.Prime).one_lt.ne' h3
    let w : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ),
      by simp [hℓ.ne_zero]⟩
    have hw : w.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro he
      rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at he
      simp only [Int.natAbs_natCast] at he
      exact hℓp he
    let v : AwayP p := ⟨w, hw⟩
    have hval : ∀ c : ℤ, Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ)) = v.1.intValuation c := by
      intro c
      rw [← valuation_of_algebraMap (K := ℚ), ← valuedAdicCompletion_eq_valuation]
      rfl
    have hℓc : (ℓ : ℤ) ∣ c := by
      obtain ⟨y, hy, e⟩ := h v
      have hy' : Valued.v y ≤ 1 := (mem_adicCompletionIntegers ℤ ℚ v.1).1 hy
      have h1 : v.1.intValuation c ≤ v.1.intValuation (n : ℤ) := by
        rw [← hval, ← hval, e, map_mul]
        exact mul_le_of_le_one_right' hy'
      have h2 : v.1.intValuation (n : ℤ) < 1 :=
        (intValuation_lt_one_iff_mem _ _).2 (Ideal.mem_span_singleton.2 ⟨n₁, by rw [hn₁]; push_cast; ring⟩)
      exact Ideal.mem_span_singleton.1 ((intValuation_lt_one_iff_mem _ _).1 (lt_of_le_of_lt h1 h2))
    obtain ⟨c₁, rfl⟩ := hℓc
    have hn₁pos : 0 < n₁ := by
      rcases Nat.eq_zero_or_pos n₁ with h0 | h0
      · rw [h0, mul_zero] at hn₁; omega
      · exact h0
    have hlt : n₁ < n := by
      rw [hn₁]; exact lt_mul_left hn₁pos hℓ.one_lt
    have hc₁ : n₁.Coprime p := Nat.Coprime.coprime_dvd_left ⟨ℓ, by rw [hn₁, Nat.mul_comm]⟩ hc
    have hd : (n₁ : ℤ) ∣ c₁ := ih n₁ hlt hn₁pos hc₁ c₁ fun v' => by
      obtain ⟨y, hy, e⟩ := h v'
      refine ⟨y, hy, ?_⟩
      have hne : algebraMap ℚ (v'.1.adicCompletion ℚ) ((ℓ : ℤ) : ℚ) ≠ 0 :=
        (map_ne_zero _).2 (by exact_mod_cast hℓ.ne_zero)
      apply mul_left_cancel₀ hne
      rw [← map_mul, ← _root_.mul_assoc, ← map_mul, ← Int.cast_mul, ← Int.cast_mul, e, hn₁]
      push_cast
      ring
    rw [hn₁]
    push_cast
    exact mul_dvd_mul_left _ hd

theorem int_dvd_of_eq_mul_isIntAf : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p),
    IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  intro p _ n hn hc c a ha e
  refine int_dvd_of_local p n hn hc c fun v => ⟨AfP.eval v a, ha v, ?_⟩
  have e' := congrArg (AfP.eval v) e
  rw [(AfP.eval v).commutes, map_mul, map_natCast] at e'
  rw [e']
  simp

end GlobalTheory.LKGeo.IntDvd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  first | (exact @GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (exact GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (intros; apply GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames _root_.Formalism.L2.Host _root_.Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure IsSBArgs (G : Grid k) (ϖ : kˣ) (n : ℕ) (F : ColArgs G → RowArgs G → ℂ) : Prop where
  dep : ∀ x x' y y', (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → F x y = F x' y'
  per : ∀ x y a b, (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) →
    (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → F (x + a) (y + b) = F x y
  supp : ∀ x y, F x y ≠ 0 → (∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧
    ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)

end Local

section Half

variable {D : D7} {a b : ℕ}

def frAt (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x : Mx D b a) :
    Matrix (Fin b) (Fin a) (Kw w) :=
  (Comparison₂.fr β' β (x.map (toEAf D))).map (cpt (D := D) w)

def IsSmall (P : Finset (Pl D.host.E)) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (n : ℤ) (t : Mx D b a) : Prop :=
  ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w β' β t r s) ≤ valuation (Kw w) ((unifAt w ^ n : (Kw w)ˣ) : Kw w)


open Classical in
def cosLoc (P : Finset (Pl D.host.E)) (e : AE D) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (n : ℤ)
    (r t : Mx D b a) : ℂ :=
  if IsHalf e t ∧ IsSmall P β' β n (t - r) then 1 else 0

end Half

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDvd

variable {p : ℕ} [Fact p.Prime]

def adBasis {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem adBasis_repr_inAf {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (z : D.La) (i : J) :
    (adBasis b).repr (inAf D z) i = algebraMap ℚ (AfP p) ((b.repr z i : ℤ) : ℚ) := by
  simp only [adBasis, inAf, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

theorem isIntAf_adBasis_repr {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {w : AfP p ⊗[ℚ] VQ D}
    (hw : w ∈ LaHat D) : IsIntAf ((adBasis b).repr w i) := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (adBasis b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [adBasis, Algebra.smul_def]
    rw [e]
    intro v
    rw [map_mul, map_intCast]
    exact mul_mem (intCast_mem _ _) (hc v)
  | zero =>
    intro v
    rw [map_zero, Finsupp.zero_apply, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro v
    rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem exists_eq_nsmul_of_inAf (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ) (_hn : 0 < n) (_hc : n.Coprime p)
    (h : ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c)
    (z : D.La) (hz : ∃ w ∈ LaHat D, inAf D z = n • w) : ∃ u : D.La, z = n • u := by
  obtain ⟨w, hw, e⟩ := hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.repr z i := by
    intro i
    refine h _ _ (isIntAf_adBasis_repr b i hw) ?_
    rw [← adBasis_repr_inAf, e, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  choose d hd using hd
  refine ⟨∑ i, d i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr z]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.LKGeo.LatDvd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p → (∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c) → ∀ z : D.La, (∃ w ∈ LaHat D, inAf D z = n • w) → ∃ u : D.La, z = n • u := by
  first | (exact @GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf) | (exact GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf) | (intros; apply GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf <;> assumption)
end
end

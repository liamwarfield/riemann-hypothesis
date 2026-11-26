module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_max_iff_val_lt_one (x : 𝒪[k]) : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem pr_incA_int_mem (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] :=
  (q.pr_mem_iff _).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1
    (Formalism.L2.DIV.oToS D.host.F D.host.E x).2)

theorem exists_int_approx (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {u : k} (hu : u ∈ 𝒪[k]) : ∃ z : 𝓞 D.host.E, valuation k (u - q.pr (incA D (z : D.host.E))) < 1 := by
  have h1 : toEAf D (q.e * q.sec u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [map_mul]
    exact (q.pr_mem_iff (q.sec u)).1 (by rw [q.pr_sec]; exact hu)
  have h2 : q.pr (q.e * q.sec u) = u := by rw [← q.sec_pr, q.pr_sec, q.pr_sec]
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot
    (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
  have ha : (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈
    Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h3 := q.val_lt_of_mem_idS he ha
  have e2 : (((⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (q.e * q.sec u) - toEAf D (incA D (a : D.host.E)) := rfl
  rw [e2, RingHom.map_sub, prF_toEAf, prF_toEAf, h2] at h3
  exact ⟨a, h3⟩

theorem hasVal_of_int_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  intro D k _ _ _ _ p PP he m b b' hb _ P hlat c₀ hval u hu r0 hr0
  classical
  choose z hz using fun r => p.exists_int_approx he (hu r)
  obtain ⟨s, hs, hv⟩ := hval (fun r => (z r : D.host.E)) (fun r => (z r).isIntegral_coe) r0 hr0
  have hw : ∀ r, p.pr (incA D (z r : D.host.E)) ∈ 𝒪[k] := fun r => p.pr_incA_int_mem he (z r)
  let d : Fin m → 𝒪[k] := fun r => ⟨u r - p.pr (incA D (z r : D.host.E)), sub_mem (hu r) (hw r)⟩
  have hd : ∀ r, d r ∈ maximalIdeal 𝒪[k] := fun r => (mem_max_iff_val_lt_one (d r)).2 (hz r)
  have hcol : ∀ r, b' *ᵥ (Pi.single r 1 : Fin m → k) ∈ P.lat := fun r => (hlat _).2 fun r' => by
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hker : ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) ∈ P.ker :=
    Submodule.sum_mem _ fun r _ => Pair.smul_mem_ker (hd r) (hcol r)
  have hsum : b' *ᵥ u = (b' *ᵥ fun r' => p.pr (incA D (z r' : D.host.E))) +
      ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) := by
    have : ∀ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = b' *ᵥ (Pi.single r (d r : k) : Fin m → k) := fun r => by
      change (d r : k) • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = _
      rw [← Matrix.mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun r _ => this r, ← Matrix.mulVec_sum, ← Matrix.mulVec_add, Finset.univ_sum_single]
    congr 1
    funext r
    simp [d]
  let c : 𝒪[k] := ⟨_, p.pr_incA_int_mem he c₀⟩
  refine ⟨s + c * d r0, ?_, ?_⟩
  · change (s : k) + p.pr (incA D (c₀ : D.host.E)) * (u r0 - p.pr (incA D (z r0 : D.host.E))) = _
    rw [hs, map_mul, map_mul]
    ring
  · rw [hsum, map_add (f := _), (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_left _ c (hd r0))]
    exact hv.add (Pair.mem_ker.1 hker)

end GlobalTheory.FinPl.SplitPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_values_integral_vectors_of_integer_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  first | exact @GlobalTheory.FinPl.SplitPt.hasVal_of_int_vectors | exact GlobalTheory.FinPl.SplitPt.hasVal_of_int_vectors | (intros; apply GlobalTheory.FinPl.SplitPt.hasVal_of_int_vectors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ChiStd

variable {D : D7}

theorem prV_toEAf_idem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (hv : v' ≠ v) (a : AE D) :
    Formalism.UG.prV (E := D.host.E) v' (Formalism.IndefR.Datum.toEAf D (algebraMap (AF D.host.F) (AE D) ε * a)) = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  have h0' : (Formalism.UG.evalV D.host.F v') ((sndA D.host.F) (pairA D.host.F 0 α)) = 0 := h0 v' hv
  induction a using TensorProduct.induction_on with
  | zero => rw [mul_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
    rw [h0', zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => rw [mul_add, RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

end GlobalTheory.AdForm.ChiStd

namespace GlobalTheory.AdForm.ChiStd

variable {D : D7}

theorem finM_gl_map_prV {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {m : Type} [Fintype m] [DecidableEq m] (β : Frame p S m)
    (g : GL m k) {v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v' ≠ p.v) :
    (finM S hn (β.gl g)).map (Formalism.UG.prV (E := D.host.E) v') = 1 := by
  obtain ⟨ε, hε, he⟩ := p.above
  have hs := β.gl_supp g
  subst hn
  ext r s
  have key : Formalism.UG.prV (E := D.host.E) v' (Formalism.IndefR.Datum.toEAf D ((mt S (β.gl g) - 1) r s)) = 0 := by
    rw [← hs r s, he]; exact prV_toEAf_idem_mul hε hv _
  have e1 : mt S (β.gl g) r s = (mt S (β.gl g) - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s := by
    rw [Matrix.sub_apply, sub_add_cancel]
  simp only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [e1, RingHom.map_add (f := _), RingHom.map_add (f := _), key, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.AdForm.ChiStd

theorem GlobalTheory.AdForm.ChiStd.not_both_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a c : ℕ}
    (ha : a.Prime) (hc : c.Prime) (hne : a ≠ c) (h1 : ((a : ℕ) : 𝓞 F) ∈ v.asIdeal) (h2 : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime a c := (Nat.coprime_primes ha hc).2 hne
  have hg : ((Nat.gcd a c : ℕ) : ℤ) = a * Nat.gcdA a c + c * Nat.gcdB a c := Nat.gcd_eq_gcd_ab a c
  rw [hcop, Nat.cast_one] at hg
  have h3 : ((1 : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hg]; push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h1) (v.asIdeal.mul_mem_right _ h2)
  rw [Int.cast_one] at h3
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.AdForm.chi_std_trivial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → ∀ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1 := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg h
  obtain ⟨κ, hκ⟩ := ((hA.U j hj b _).1 h).2
  rw [hA.chi j hj b ⟨_, h⟩ κ hκ]
  apply hA.lev_chi_eq_one j hj b κ
  intro v' hv'
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ (p i).v.asIdeal := by
    obtain ⟨⟨e, he⟩, -⟩ := hS
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    have hmem : X.piT u ∈ (e i).1.asIdeal := (Formalism.L2.Col.mem_divs hne _).1 (e i).2
    obtain ⟨ε, hε, hε'⟩ := (p i).above
    have hund := GlobalTheory.IdemUnder.under_eq_of_isIdemAt (I.rec7 l Z) (p i).e (e i).1 (p i).v ε (he i) hε hε'
    have hTE : ((B.T u : ℕ) : 𝓞 B.host.E) ∈ (e i).1.asIdeal := by
      have := hPr.piT_norm u
      rw [← this]
      exact Ideal.mul_mem_right _ _ hmem
    rw [← hund]
    show _ ∈ Ideal.comap _ _
    refine Ideal.mem_comap.2 ?_
    have h2 : (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E)) ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) =
        ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.E) := map_natCast _ _
    first | (erw [h2]; exact hTE) | exact h2 ▸ hTE | simpa using hTE
  have hne : v' ≠ (p i).v := by
    rintro rfl
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    rcases hv' with hbad | hq
    · rcases hbad with h0 | h1
      · exact GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 0) (hPr.T_ne_g u 0) hT h0
      · exact GlobalTheory.AdForm.ChiStd.not_both_mem _ (hPr.T_prime u) (hPr.g_prime 1) (hPr.T_ne_g u 1) hT h1
    · exact (GlobalTheory.Mem.Col2.TC.underQ_notMem I hOk l u a _ hq).1 hT
  apply Units.ext
  show (κ.1.1).map (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v') = 1
  rw [hκ]
  exact GlobalTheory.AdForm.ChiStd.finM_gl_map_prV (p i) _ _ (β j i) g hne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → ∀ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.AdForm.chi_std_trivial | exact GlobalTheory.AdForm.chi_std_trivial | (intros; apply GlobalTheory.AdForm.chi_std_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG

namespace GlobalTheory.Mem.Col2.AdT.SplitChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_conjP_eq_one (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) (r s : Fin n) :
    adAt F (conjPrime₂ P) (u.1 r s) = (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
  subst J
  have hunit : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) * u.1 = 1 := by
    have h := hu
    change cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) u.1 * (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * u.1 = _ at h
    simpa only [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] using h
  have h1 : (u : Matrix (Fin n) (Fin n) (AfE F E)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    have hcT : 1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) = cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) u.1 := by
      ext i j
      by_cases h : i = j <;> simp [cT, Matrix.one_apply, map_sub, h, eq_comm]
    rw [hcT]
    exact (mul_eq_one_comm).1 hunit
  have hC : (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P)) = 0 := by
    refine Matrix.ext fun i j => ?_
    show adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)) = 0
    have e2 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) j i := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hX : adAt F P (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i) = 0 := by
      rw [Matrix.sub_apply, map_sub, hP, e2, sub_self]
    have e := GlobalTheory.Mem.Col2.valued_sigR hc (conjPrime₂ P) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)
    rw [GlobalTheory.CharValCompare.conjP_conjP, hX, Valuation.map_zero] at e
    exact (Valuation.zero_iff _).1 e
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add (f := _), map_one] at h2
  change _ * (1 + (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P))) = 1 at h2
  rw [hC, add_zero, mul_one] at h2
  exact congrFun (congrFun h2 r) s

theorem bc_prV_eq_one_of_split (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hover : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) :
    bc (prV (E := E) v) u = 1 := by
  refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt F E n v u fun w hw r s => ?_
  rcases hover w hw with rfl | rfl
  · rw [hP, Matrix.one_apply]
  · rw [adAt_conjP_eq_one hc hJ hu P hP r s, Matrix.one_apply]

end Gen

section Root

theorem exists_root_GL {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n : ℕ) (hn : 0 < n)
    (c : P.adicCompletion E) (hc : Valued.v c < 1) (A : GL (Fin m) (P.adicCompletion E))
    (hA : ∀ r s, Valued.v (A.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤
      Valued.v ((n : P.adicCompletion E) ^ 2 * c)) :
    ∃ M : GL (Fin m) (P.adicCompletion E), M ^ n = A ∧
      ∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ Valued.v ((n : P.adicCompletion E) * c) := by
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n c A.1 hn hc
    (fun r s => by rw [Matrix.sub_apply]; exact hA r s)
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ A.isUnit)
  obtain ⟨M, rfl⟩ := hu
  exact ⟨M, Units.ext (by rw [Units.val_pow_eq_pow_val, hM2]), fun r s => by rw [← Matrix.sub_apply]; exact hM1 r s⟩

end Root

section Fin

theorem chi_eq_one_of_pow {G : Type} [Group G] {U : Subgroup G} (χ : U →* ℂˣ) (x z : U) (n : ℕ) (hz : χ z ^ n = 1)
    (hy : χ ((z ^ n)⁻¹ * x) = 1) : χ x = 1 := by
  rw [map_mul, map_inv, map_pow, hz, inv_one, one_mul] at hy
  exact hy

theorem map_inv_pow_mul_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {x z : G} (n : ℕ) (hz : f z = 1) (hx : f x = 1) :
    f ((z ^ n)⁻¹ * x) = 1 := by
  rw [map_mul, map_inv, map_pow, hz, hx, one_pow, inv_one, one_mul]

end Fin


set_option maxHeartbeats 8000000 in
theorem chi_eq_one_of_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  intro B X I hI hPin l Z a T i hi bad S n hn hchi P v hv
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  have hu : P.1.under (𝓞 B.host.F) = v := by
    rw [hs] at hv
    exact HeightOneSpectrum.ext (Eq.symm hv)
  haveI : CharZero (P.1.adicCompletion B.fields.E) := algebraRat.charZero _
  set c : P.1.adicCompletion B.fields.E := ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) ^ (N₀ + 1) with hcdef
  have hc : Valued.v c = WithZero.exp (-((N₀ : ℤ) + 1)) := by
    rw [hcdef, map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc1 : Valued.v c < 1 := by
    rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hn1 : Valued.v (n : P.1.adicCompletion B.fields.E) ≤ 1 := GlobalTheory.MatNthRoot.v_natCast_le_one n
  have hε : Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  set e := WithZero.log (Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c)) with he
  refine ⟨(-e).toNat, fun x hxv w hw hxw => ?_⟩

  have hxP : ∀ r s, adAt B.host.F P.1 (x.1.1 r s) = adAt B.host.F P.1 (w.1 r s) := fun r s => by
    have h := congrArg (fun g : GL (Fin ((I.rec7 l Z).R.N i)) _ => g.1 r s) hxw
    refine GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 ?_
    rw [hu]
    exact h
  have hwP := ((hd _ w).2.2).1 hw
  have hwP := ((hd (-e).toNat w).2.2).1 hw
  have hA : ∀ r s, Valued.v (adAt B.host.F P.1 (x.1.1 r s) - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s) ≤
      Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) := fun r s => by
    rw [hxP]
    refine (hwP r s).trans ?_
    rw [← WithZero.exp_log hε, ← he]
    exact WithZero.exp_le_exp.2 (by omega)
  let x' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := x.1
  obtain ⟨Mu, hMun, hMu1⟩ := exists_root_GL P.1 (B.R.N i) n hn c hc1
    (Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) x') hA
  obtain ⟨z, hzU, hzv, hzP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv Mu
  have hz : z ∈ S.U := hN₀ z hzU hzv (((hd N₀ z).2.2).2 fun r s => by
    rw [hzP]
    refine (hMu1 r s).trans ?_
    rw [map_mul, hc]
    exact (mul_le_of_le_one_left' hn1).trans (WithZero.exp_le_exp.2 (by omega)))
  have hgU : (z ^ n)⁻¹ * x.1 ∈ S.U := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hz n)) x.2
  have hyU := ((S.U_eq _).1 hgU).1
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPin l Z).2.2.2 i hi).1
  let z' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := z
  have hzmap : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) z' = Mu := Units.ext (Matrix.ext hzP)
  have key : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) ((z' ^ n)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, map_pow, hzmap, hMun, inv_mul_cancel]
  have hyP : ∀ r s, adAt B.host.F P.1 (((z ^ n)⁻¹ * x.1).1 r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s :=
    fun r s => congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) key
  have hover : ∀ w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), w.under (𝓞 (I.rec7 l Z).host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 :=
    fun w hw => (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 w).1 (hw.trans hu.symm)
  have hyv : ∀ v', bc (prV (E := (I.rec7 l Z).host.E) v') ((z ^ n)⁻¹ * x.1) = 1 := by
    intro v'
    by_cases hv' : v' = v
    · rw [hv']
      exact bc_prV_eq_one_of_split (I.rec7 l Z).sp.cm hgram hyU P.1 v hover hyP
    · exact map_inv_pow_mul_eq_one _ n (hzv v' hv') (hxv v' hv')
  exact chi_eq_one_of_pow S.chi x ⟨z, hz⟩ n (hchi _) (S.chi_triv _ fun v' _ => hyv v')

end GlobalTheory.Mem.Col2.AdT.SplitChi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep | exact GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep | (intros; apply GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenomNotMemOfPrInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem mem_prime_iff_pr_inv_notMem {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt p.e P) (x : 𝓞 D.host.E) (hx : x ≠ 0) :
    x ∈ P.asIdeal ↔ p.pr (incA D ((x : D.host.E)⁻¹)) ∉ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr]
  exact h.2 x hx

theorem exists_denom_notMem_of_pr_int : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ a : D.host.E, p.pr (incA D a) ∈ 𝒪[k] →
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 D.host.E,
      algebraMap (𝓞 D.host.E) D.host.E c = algebraMap (𝓞 D.host.E) D.host.E s * a := by
  intro D k _ _ _ _ p P h a ha
  obtain ⟨n, ⟨d, hd⟩, hnd | hnd⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := D.host.E) a
  · exact ⟨d, hd, n, by rw [← hnd, mul_comm]⟩
  · have hd' : d ∉ P.asIdeal := hd
    have hd0 : d ≠ 0 := fun h0 => hd' (h0 ▸ P.asIdeal.zero_mem)
    have hnd' : a * (n : D.host.E) = (d : D.host.E) := hnd
    have hdE : (d : D.host.E) ≠ 0 := fun h0 => hd0 (RingOfIntegers.coe_eq_zero_iff.mp h0)
    have hnE : (n : D.host.E) ≠ 0 := fun h0 => hdE (by rw [← hnd', h0, mul_zero])
    have hn0 : n ≠ 0 := fun h0 => hnE (by rw [h0]; rfl)
    refine ⟨n, fun hn => ?_, d, by rw [mul_comm]; exact hnd.symm⟩
    have h1 := (mem_prime_iff_pr_inv_notMem p P h n hn0).1 hn
    have h2 := not_not.1 (mt (mem_prime_iff_pr_inv_notMem p P h d hd0).2 hd')
    apply h1
    have h3 : (n : D.host.E)⁻¹ = a * (d : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hdE, ← hnd', mul_comm a, inv_mul_cancel_left₀ hnE]
    rw [h3, map_mul, map_mul]
    exact mul_mem ha h2

end GlobalTheory.PhiOneVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem residue_pr_int_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  intro D k _ _ _ _ p P hP c
  have h : p.pr (incA D (c : D.host.E)) ∈ 𝒪[k] := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p c
  refine ⟨h, ?_⟩
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hc : c = 0
  · subst hc
    have h0 : (⟨_, h⟩ : 𝒪[k]) = 0 := by
      apply Subtype.ext
      simp
    refine ⟨fun _ => zero_mem _, fun _ hu => ?_⟩
    exact not_isUnit_zero (h0 ▸ hu)
  have hc' : (c : D.host.E) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hinv : p.pr (incA D (c : D.host.E)) * p.pr (incA D (c : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, ← map_mul (incA D), mul_inv_cancel₀ hc', map_one, map_one]
  rw [hP.2 c hc, ← p.sec_pr, ← p.int_iff]
  apply not_congr
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : p.pr (incA D (c : D.host.E)) * (y : k) = 1 := congrArg Subtype.val hy
    have hne : p.pr (incA D (c : D.host.E)) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have : p.pr (incA D (c : D.host.E)⁻¹) = y := mul_left_cancel₀ hne (hinv.trans hy'.symm)
    rw [this]; exact y.2
  · intro hi
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝒪[k]) (Subtype.ext hinv)

end GlobalTheory.PhiOneVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_component_integer_residue_zero_iff_mem_prime : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  first | exact @GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff | exact GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff | (intros; apply GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.CommIs

open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi

theorem isKFin_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

theorem itSpans_of (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hθ : IsInfFam θ) (hw : IsWeilExp ψ V W aS aT ω)
    (hv : IsVacVec ψ θ M M' f) (hi : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : GlobalTheory.Core.Mi.ItSpans M M' It := by
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D V W S S' M M' θ ψ aS aT ω f It hθ hw hv hi
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap (It P) (Submodule.span ℂ
      {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => isKFin_of_mem _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Fam.CommIs


open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt in
theorem GlobalTheory.Fam.commOf_is : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ g : GlobalTheory.Fam.Geo D, GeoMeas (pk W) g → (∀ j, j ≤ D.R.m → (g.x j).Is) → (commOf (pk W) u g).Is := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hp g hm hx
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  have hS : StepsOK (pk W) := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ (pk W) hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX
    hC.chain.vY hC.chain.vX
  have hθ : IsInfFam (pk W).θ := hC.models.inf
  have hm1 : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hY : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((pk W).MY j) ((pk W).MY (j + 1)) ((pk W).ItY j) := by
    intro j hj
    have h := hS.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItY W.P.A3.A.μ0 j hj)
  have hX : GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
    have h := hS.2 W.P.A3.A.μ0 ⟨D.R.m - 1, hm1⟩ rfl
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItX W.P.A3.A.μ0)
  have hXc : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((pk W).MY n) (pk W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n))
        (pk W).ItX e) := by
    intro n e
    subst e
    exact hX
  refine ⟨W.Q.stdChar, hθ, hx, GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite D.sp.X'_sig fun τ => Or.inl (D.X'_posDef τ), hm.μf, hm.ρJ,
    hm.ρB, fun j hj => hY j hj, fun j h => hXc (j + 1) (idx_top h)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.OffPlace

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_of_idOff (p : SplitPt D k) {a : Formalism.L2.Theta.AE D} (ha : a ∈ idOff D (· = p.v)) : p.pr a = 0 := by

  have hv : compAt D p.v a = 0 := by
    rw [idOff, Submodule.mem_iInf] at ha
    exact ha ⟨p.v, rfl⟩
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  obtain ⟨α, hα, hαv, hαw⟩ := hε
  have hparts := placeIdempotent_infinite_and_finite_components D p.v ε α hα

  have hεa : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [map_mul, hparts.1, zero_mul]
    · intro w
      rw [map_mul, hparts.2 w]
      by_cases hw : w = p.v
      · subst hw
        rw [hv, mul_zero]
      · rw [hαw w hw, TensorProduct.zero_tmul, zero_mul]

  have hea : p.e * a = 0 := by
    have : p.e * algebraMap (AF D.host.F) (AE D) ε = p.e := by
      rw [← hsum, mul_add, hee, hec, add_zero]
    rw [← this, mul_assoc, hεa, mul_zero]
  rw [← p.pr_sec (p.pr a), p.sec_pr, hea, map_zero]

theorem map_pr_of_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  intro D k _ _ _ _ p S n _ _ β κ g h
  set γ := κ * (β.gl g)⁻¹ with hγ

  have hq : (mt S γ).map (Ideal.Quotient.mk (idOff D (· = p.v))) = 1 := by
    rw [grpOff, congGrp, MonoidHom.mem_ker] at h
    have := congrArg (fun M : GL (Fin S.rank) (AE D ⧸ idOff D (· = p.v)) => M.val) h
    simpa [Formalism.L2.Theta.mt] using this

  have hγ1 : (mt S γ).map p.pr = 1 := by
    ext i j
    have hij := congrFun (congrFun hq i) j
    have hmem : mt S γ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D (· = p.v) := by
      rw [← Ideal.Quotient.eq]
      rw [Matrix.map_apply] at hij
      rw [hij, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := pr_of_idOff p hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hκ : κ = γ * β.gl g := by rw [hγ, inv_mul_cancel_right]
  have hmt : mt S κ = mt S γ * mt S (β.gl g) := by
    rw [hκ]
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  rw [hmt, Matrix.map_mul, hγ1, one_mul, β.gl_mat g]

end GlobalTheory.AdForm.OffPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  first | exact @GlobalTheory.AdForm.OffPlace.map_pr_of_off | exact GlobalTheory.AdForm.OffPlace.map_pr_of_off | (intros; apply GlobalTheory.AdForm.OffPlace.map_pr_of_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotents
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.PutIn

theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := by
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_smul_idem {D : D7} {m n : ℕ} {b : AE D} (hbb : b * b = b) (x : Mx D m n) : IsHalf b (b • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hbb]

theorem isHalf_sub_smul {D : D7} {m n : ℕ} {a b : AE D} (hab : a * b = 0) {u : Mx D m n} (hu : IsHalf (a + b) u) :
    IsHalf a (u - b • u) := by
  intro i j
  have h := hu i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
  rw [add_mul] at h
  linear_combination h

theorem isSBHalf_tens : ∀ (D : D7) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (Φ Ψ : WO S T → ℂ),
    a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsSBHalf a Λ Φ → IsSBHalf b Λ Ψ →
    IsSBHalf (a + b) Λ (GlobalTheory.FinPl.PutIn.tens b Φ Ψ) := by
  intro D S T a b Λ Φ Ψ hab hbb hΛ ⟨hΦs, kΦ, hkΦ, hΦi, hΦb⟩ ⟨hΨs, kΨ, hkΨ, hΨi, hΨb⟩
  refine ⟨?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, ?_, ?_⟩
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦs _ (left_ne_zero_of_mul ht)
    have h2 := hΨs _ (right_ne_zero_of_mul ht)
    intro i j
    have e1 := h1 i j
    have e2 := h2 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at e1
    rw [add_mul, e1]
    ring
  · intro u hu hhu t
    have hu1 : u - b • u ∈ Λ := Λ.sub_mem hu (hΛ u hu)
    have hu2 : b • u ∈ Λ := hΛ u hu
    have e1 : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    have e2 : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [tens_apply, tens_apply, e1, e2,
      hΦi _ (Λ.nsmul_mem hu1 kΨ) (isHalf_nsmul (isHalf_sub_smul hab hhu) kΨ),
      hΨi _ (Λ.nsmul_mem hu2 kΦ) (isHalf_nsmul (isHalf_smul_idem hbb u) kΦ)]
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦb _ (left_ne_zero_of_mul ht)
    have h2 := hΨb _ (right_ne_zero_of_mul ht)
    have e : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem h1 kΨ) (Λ.nsmul_mem h2 kΦ)

end GlobalTheory.FinPl.PutIn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents : ∀ (D : D7) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (Φ Ψ : WO S T → ℂ), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsSBHalf a Λ Φ → IsSBHalf b Λ Ψ → IsSBHalf (a + b) Λ (GlobalTheory.FinPl.PutIn.tens b Φ Ψ) := by
  first | exact @GlobalTheory.FinPl.PutIn.isSBHalf_tens | exact GlobalTheory.FinPl.PutIn.isSBHalf_tens | (intros; apply GlobalTheory.FinPl.PutIn.isSBHalf_tens <;> assumption)
end
end

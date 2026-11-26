module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelColumnSubOneMemBaseLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelColumnSubOneMemBaseLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.AdForm.level_col_sub_one_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  set_option maxHeartbeats 10000000 in
    next =>
      intro B X I hI hP l Z u a Ch A hA j hj b κ hκ v hv s
      obtain ⟨-, κ', hκ'⟩ := (hA.U j hj b κ).1 hκ
      have hgram : gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
      haveI : NeZero ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) := ⟨by
        have := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_add_three_le_k
        simp only [Ranks.N]; omega⟩
      obtain ⟨At, -, hpi, -⟩ := GlobalTheory.Mem.AtLevel.exists_atTTied I hI hP l Z u
      let sg : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E := RingOfIntegers.mapRingHom (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)
      have hsc : ∀ x, (sg x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.conj (x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
      have hpq : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) * (sg At.piU : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) = (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hsc]; exact At.piU_norm
      have hTp := ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T_prime
      have hp0 : ((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
      have hL : (A.K j hj b).lev.Lb = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) (((At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)⁻¹) := by
        refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ At.piU hp0 _ ?_
        rw [hpi]; exact (hA.reads j hj).lb b
      have hx := (((A.K j hj b).lev.U_eq κ'.1).1 κ'.2).2 v
      have hT := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.fixed x).1 hx)
          (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.cm.cmUnram.2.2 hgram (A.K j hj b).lev At.piU (sg At.piU) rfl hpq hTp hL v hv (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u At v hv) _).1 hx
      have hsp : Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb) = Formalism.L2.Col.rll_dLat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) ((sg At.piU : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) := by
        rw [hL, hgram]; exact GlobalTheory.uLocDual_eq (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (fun x => star_star x) _ At.piU (sg At.piU) hp0 rfl
      have hy : (fun r => Formalism.UG.inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((Pi.single s 1 : Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) r)) ∈ Formalism.UG.latS (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (intV (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E v) (Submodule.span (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (dualSet ((sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →ₐ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E →+* (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) j hj) (A.K j hj b).lev.Lb)) := by
        simp only [hsp]
        refine Submodule.subset_span ⟨Pi.single s 1, ?_, rfl⟩
        rw [SetLike.mem_coe, Formalism.L2.Col.rll_mem_dLat]
        refine ⟨fun i _ => ?_, ?_⟩
        · by_cases h : i = s
          · subst h; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _
        · by_cases h : Formalism.L2.Col.lastIdx ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N j) = s
          · rw [h, Pi.single_eq_same, mul_one]; exact ⟨sg At.piU, rfl⟩
          · rw [Pi.single_eq_of_ne h, mul_zero]; exact zero_mem _
      have key := hT.2 _ hy
      convert key using 1
      funext r
      have hm : ((Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) κ'.1 : GL _ _) : Matrix _ _ _) = (κ'.1.1).map (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) := rfl
      rw [Pi.sub_apply, hm, hκ']
      congr 1
      · simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply]
      · simp [Pi.single_apply, Matrix.one_apply]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelColumnSubOneMemBaseLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  first | exact @GlobalTheory.AdForm.level_col_sub_one_mem | exact GlobalTheory.AdForm.level_col_sub_one_mem | (intros; apply GlobalTheory.AdForm.level_col_sub_one_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GeneratorMemSplitPrimeLevelPrimeMemPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GeneratorMemSplitPrimeLevelPrimeMemPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.GenOver


open GlobalTheory.AdForm.PlacesDistinct in
theorem mem_place_of_mem_prime {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w)
    (x : 𝓞 D.host.F) (y : 𝓞 D.host.E) (hxy : (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F))
    (hy : y ∈ w.asIdeal) : x ∈ p.v.asIdeal := by
  by_contra hxv
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ p.v.asIdeal.zero_mem)
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    have : algebraMap D.host.F D.host.E (x : D.host.F) = 0 := by rw [← hxy, h]; rfl
    rw [map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective] at this
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  apply (hI.2 y hy0).1 hy
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.e = p.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hsum, mul_add, p.split.1, p.split.2.1, add_zero]
  set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) ((x : D.host.F)⁻¹) with hc
  have hinc : incA D ((y : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) c := by
    rw [hxy, ← map_inv₀, hc]
    show Algebra.TensorProduct.includeRight _ = _
    exact (Algebra.TensorProduct.includeRight.commutes _).trans (IsScalarTower.algebraMap_apply _ _ _ _)
  have h2 : finPart D (algebraMap (AF D.host.F) (AE D) (ε * c)) ∈ intAE D := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hf : finPart D ((ε * c) ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F (ε * c) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hf]
    refine AddSubgroup.subset_closure ⟨sndA D.host.F (ε * c), ?_, 1, by simp⟩
    intro v'
    obtain ⟨α, rfl, h1, h0⟩ := hε
    have hs : sndA D.host.F (pairA D.host.F 0 α * c) = α * algebraMap D.host.F (Af D.host.F) ((x : D.host.F)⁻¹) := by
      rw [map_mul, hc, AlgHom.commutes]; rfl
    rw [hs, map_mul, AlgHom.commutes]
    by_cases hv : v' = p.v
    · subst hv
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
      have hv1 : Valued.v (algebraMap D.host.F (Fv D.host.F p.v) (x : D.host.F)) = 1 := by
        have := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.F) p.v x
        refine this.trans ?_
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hxv
      rw [hv1, inv_one]
    · rw [h0 v' hv, zero_mul]
      exact zero_mem _
  rw [hinc, he, mul_assoc, ← map_mul, map_mul]
  exact FrameLat.mul_mem_intAE (finPart_idem_int hI) h2

theorem natCast_mem_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w) (n : ℕ)
    (hn : (n : 𝓞 D.host.E) ∈ w.asIdeal) : (n : 𝓞 D.host.F) ∈ p.v.asIdeal :=
  mem_place_of_mem_prime p hI (n : 𝓞 D.host.F) (n : 𝓞 D.host.E) (by simp) hn

end GlobalTheory.AdForm.GenOver


open GlobalTheory.AdForm.GenOver in
theorem GlobalTheory.AdForm.piT_mem_and_T_mem_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k) (P : (B.primes X).vT u), Formalism.L2.NTheta.IsIdemAt p.e P.1 → X.piT u ∈ P.1.asIdeal ∧ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal := by
  intro B X I _ l Z u k _ _ _ _ p P hI
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h1 : X.piT u ∈ P.1.asIdeal := (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).1 P.2
  have hT : ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ P.1.asIdeal := by
    have : X.piT u * B.fields.conjO (X.piT u) = ((B.T u : ℕ) : 𝓞 B.fields.E) := hPr.piT_norm u
    rw [← this]
    exact Ideal.mul_mem_right _ _ h1
  exact ⟨h1, natCast_mem_place p hI (B.T u) hT⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GeneratorMemSplitPrimeLevelPrimeMemPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_mem_split_prime_level_prime_mem_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k) (P : (B.primes X).vT u), Formalism.L2.NTheta.IsIdemAt p.e P.1 → X.piT u ∈ P.1.asIdeal ∧ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal := by
  first | exact @GlobalTheory.AdForm.piT_mem_and_T_mem_place | exact GlobalTheory.AdForm.piT_mem_and_T_mem_place | (intros; apply GlobalTheory.AdForm.piT_mem_and_T_mem_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.AdForm.CompFix.intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s) ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 :=
          mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.AdForm.comp_fixes_stdPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b κ hκ i g hg

  let e := Classical.choose hS.1
  have he := Classical.choose_spec hS.1
  obtain ⟨hpi, hT⟩ := GlobalTheory.T.generator_mem_split_prime_level_prime_mem_place I hOk l Z u k (p i) (e i) (he i)
  have key : ∀ κ₀ ∈ A.U j b, ∀ r s : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank,
      ((mt _ κ₀).map (p i).pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank →
        valuation k (((mt _ κ₀).map (p i).pr) r s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s) < 1) := by
    intro κ₀ hκ₀ r s
    have hn := rankN (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) j hj
    have h3 := GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice I hOk hPins l Z u a Ch A hA j hj b κ₀ hκ₀ (p i).v hT (Fin.cast hn s)
    let y : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j) → AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) := fun r' =>
      mt _ κ₀ (Fin.cast hn.symm r') s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) (Fin.cast hn.symm r') s
    have hy : (fun r' => Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) (p i).v (toEAf (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (y r'))) =
        (fun r' => Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) (p i).v (GlobalTheory.AdForm.finM _ hn κ₀ r' (Fin.cast hn s)) -
          (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j)) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j)) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.F] (p i).v.adicCompletion (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.F)) r' (Fin.cast hn s)) := by
      funext r'
      simp only [y]
      rw [RingHom.map_sub, RingHom.map_sub]
      congr 1
      by_cases h : r' = Fin.cast hn s
      · subst h
        have : Fin.cast hn.symm (Fin.cast hn s) = s := Fin.ext rfl
        rw [this, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
      · have h' : Fin.cast hn.symm r' ≠ s := fun h2 => h (Fin.ext (by rw [← h2]; rfl))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
    have hLb : ∀ x, x ∈ (A.K j hj b).lev.Lb ↔ ∀ j' : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j), ∃ r : 𝓞 (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E, x j' = (r : (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) ∧ (j'.1 + 1 = (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j → X.piT u ∣ r) :=
      fun x => (hA.reads j hj).lb b x
    rw [← hy] at h3
    have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) k (p i) (e i).1 (he i) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j) (X.piT u) hpi (A.K j hj b).lev.Lb hLb y h3 (Fin.cast hn r)
    have hyr : y (Fin.cast hn r) = mt _ κ₀ r s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) r s := rfl
    rw [hyr] at h4
    have h1 : (p i).pr ((1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) r s) =
        (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [map_sub, h1] at h4
    refine ⟨?_, fun hr => ?_⟩
    · have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s ∈ 𝒪[k] by
        simp only [Matrix.one_apply]; split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      rwa [sub_add_cancel] at this
    · exact h4.2 (by rw [Fin.coe_cast, ← hn]; exact hr)

  set M := (mt _ κ).map (p i).pr with hMdef
  set M' := (mt _ κ⁻¹).map (p i).pr with hM'def
  have hmt : ∀ x y : GA (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j), mt _ (x * y) = mt _ x * mt _ y := fun x y => by
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, mul_inv_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, inv_mul_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM := GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) k (p i) _ _ (β j i) κ g hg
  rw [← hMdef] at hM
  rcases Nat.eq_zero_or_pos ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank with h0 | hpos
  · have : g = 1 := by
      apply Units.ext
      apply Matrix.ext
      intro a b
      have ha : a.val < ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := a.isLt
      omega
    rw [this, one_smul]
  let r₀ : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := ⟨((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := by simp only [r₀]; omega
  have hK := GlobalTheory.AdForm.CompFix.intMat_keeps M M' hMM (fun r s => (key κ hκ r s).1) (fun r s => (key κ⁻¹ (inv_mem hκ) r s).1) r₀
    (fun s => (key κ⁻¹ (inv_mem hκ) r₀ s).2 hr₀)

  have hbg : ∀ x : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank → k, (β j i).b *ᵥ (g⁻¹ • x) = M' *ᵥ ((β j i).b *ᵥ x) := by
    intro x
    have e1 : (β j i).b * g.val = M * (β j i).b := by
      rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, (β j i).b'b, Matrix.mul_one]
    have e2 : (β j i).b *ᵥ x = M *ᵥ ((β j i).b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine Pair.ext fun x a' => ?_
  rw [Pair.smul_hasVal, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK ((β j i).b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_component_fixes_standardPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  first | exact @GlobalTheory.AdForm.comp_fixes_stdPair | exact GlobalTheory.AdForm.comp_fixes_stdPair | (intros; apply GlobalTheory.AdForm.comp_fixes_stdPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProof
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.twLev_prime : GlobalTheory.AdForm.TwLev' := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ hJall j hj b
  refine ⟨fun i g hg => ⟨GlobalTheory.T.standardPair_stabiliser_mem_chartLevel I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg,
    GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg _⟩, fun κ hκ => ?_⟩
  obtain ⟨g, hg1, κ', hκ', heq⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off (I.rec7 l Z) ((I.rec7 l Z).sp.X j) k ι p _ (β j)
    (GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hS) J hJ hJall κ
  exact ⟨g, fun i => GlobalTheory.T.chartLevel_component_fixes_standardPair I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b κ hκ i (g i) (hg1 i), κ', hκ', heq⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  first | exact @GlobalTheory.AdForm.twLev_prime | exact GlobalTheory.AdForm.twLev_prime | (intros; apply GlobalTheory.AdForm.twLev_prime <;> assumption)
end

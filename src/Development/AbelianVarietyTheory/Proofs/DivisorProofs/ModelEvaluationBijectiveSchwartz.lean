module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ModelAdm

open Filter
open scoped Classical

theorem model_admissible_iff_evaluation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij l
  constructor
  · intro hl
    exact GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE l hl
  · intro hl g hg
    obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
    obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
    have hbi : Function.Bijective ei :=
      ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
        GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
    obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
    have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
      intro j v
      by_cases h : φ j v = M₁.vac v
      · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
      · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
        obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
        exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
    choose ψ hψSB hψev hψvac using hpre
    have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
      ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
    have hψstd : ∀ j, ∀ᶠ v in cofinite,
        ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
      ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
    have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → Af F) := fun j =>
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
    choose Tj hTj using fun j => hl _ (hG j)
    refine ⟨∑ j, c j • (Tj j).comp S, fun f => ?_⟩
    have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
        ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      rfl
    have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
        e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
      intro j
      have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
      rw [hS] at h1
      have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
      rw [h2] at h1
      exact h1.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφe j]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [← hTj j (S f)]
    rfl

end GlobalTheory.ModelAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_evaluation_bijective_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ModelAdm.model_admissible_iff_evaluation | exact GlobalTheory.ModelAdm.model_admissible_iff_evaluation | (intros; apply GlobalTheory.ModelAdm.model_admissible_iff_evaluation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedInertKillsUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedInertKillsUnits
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.UnrKill

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 K) ∈ P.asIdeal := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem vl_nat_eq_one {D : D7} {q m : ℕ} (hm : Nat.Coprime m q) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v (m : AE D) = 1 := by
  refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have hab' := congrArg (Int.cast : ℤ → AE D) hab
  push_cast at hab'
  have h2 : vl D v ((a : AE D) * m) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
  have h3 : vl D v ((b : AE D) * q) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [hab', map_one] at h4
  exact lt_irrefl _ h4

theorem vl_eq_zero_of_zeroAt {D : D7} {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v x = 0 := by
  have hk : ∀ k : ℕ, vl D v x ≤ vl D v (q : AE D) ^ k := fun k => by
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have h1 := vl_nat_eq_one hm hv
    rw [← one_mul (vl D v x), ← h1, ← map_mul, e, map_mul, map_pow]
    exact mul_le_of_le_one_right' (vl_le hs v)
  by_contra h0
  obtain ⟨k, hk'⟩ := exists_pow_lt₀ (val_nat_lt hv) (Units.mk0 _ h0)
  exact lt_irrefl _ ((hk k).trans_lt hk')

theorem unr_kill : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), (∀ P : HeightOneSpectrum (𝓞 D.host.E), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → χ.UnrAt P) → ∀ u : (AE D)ˣ, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D u) = 1 := by
  intro D χ hχ u hu hz
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) ?_
  intro P x hx
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P
  by_cases hI : InertQ D q
  · have hunr := hχ P ⟨q, hq, hI, hqP⟩
    refine hunr x ?_
    show Valued.v (x : P.adicCompletion D.host.E) = 1
    rw [hx]
    exact finIdl_unit hu P
  · have h0 := vl_eq_zero_of_zeroAt (hz q hq hI) (v := P) hqP
    rw [← vl_sub_one, map_eq_zero, sub_eq_zero, ← hx] at h0
    have hx1 : x = 1 := Units.ext h0
    rw [hx1, map_one]
    exact map_one _

end GlobalTheory.UnrKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedInertKillsUnitsStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_unramified_inert_kills_units : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), (∀ P : HeightOneSpectrum (𝓞 D.host.E), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → χ.UnrAt P) → ∀ u : (AE D)ˣ, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D u) = 1 := by
  first | exact @GlobalTheory.UnrKill.unr_kill | exact GlobalTheory.UnrKill.unr_kill | (intros; apply GlobalTheory.UnrKill.unr_kill <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacF

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem mem_conjHalf_conj {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : ∀ i j, e * x i j = x i j) :
    x ∈ conjHalf σ (cAF σ e) nS nT := fun i j => by rw [cAF_cAF he]; exact hx i j

theorem fin_of_mem {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT) :
    u.map (infPartF F E) = 0 := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  have hs := congrArg (infPartF F E) hsum
  rw [map_add (f := _), GlobalTheory.WeilPartsF.infPartF_placeIdem hpl] at hs
  have hc : infPartF F E (cAF σ e) = 0 := by
    have a1 : infPartF F E (cAF σ e) * infPartF F E (cAF σ e) = infPartF F E (cAF σ e) := by
      rw [← map_mul, ← map_mul, h1]
    have a2 : infPartF F E (cAF σ e) * infPartF F E e = 0 := by rw [← map_mul, mul_comm, h2, map_zero]
    linear_combination -a1 - a2 + infPartF F E (cAF σ e) * hs
  ext i j
  show infPartF F E (u i j) = 0
  rw [← hu i j, map_mul, hc, zero_mul]

theorem commF_add_left (u u' y : WOF F E nS nT) :
    commF σ JS JT xi0 ψ (u + u') y = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u' y := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_add_right (u y y' : WOF F E nS nT) :
    commF σ JS JT xi0 ψ u (y + y') = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u y' := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_zero_left (y : WOF F E nS nT) : commF σ JS JT xi0 ψ 0 y = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_zero_right (u : WOF F E nS nT) : commF σ JS JT xi0 ψ u 0 = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_neg_right (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ u (-y) * commF σ JS JT xi0 ψ u y = 1 := by
  rw [← commF_add_right, neg_add_cancel, commF_zero_right]

theorem commF_swap (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ y (-u) = commF σ JS JT xi0 ψ u y := by
  unfold commF
  have h1 := GlobalTheory.HeisThetaF.symplOHF_add_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) y (-u) u
  have h2 := GlobalTheory.HeisThetaF.symplOHF_add_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (-u) u y
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_right] at h1
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_left] at h2
  congr 1
  linear_combination -h1 + h2

theorem commF_nsmul_left (u y : WOF F E nS nT) (n : ℕ) :
    commF σ JS JT xi0 ψ (n • u) y = commF σ JS JT xi0 ψ u y ^ n := by
  induction n with
  | zero => rw [zero_smul, commF_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, commF_add_left, ih, pow_succ]

theorem commF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : commF σ JS JT xi0 ψ x y = 1 := by
  unfold commF
  rw [symplOHF_half he hx hy, symplOHF_half he hy hx, sub_zero, AddChar.map_zero_eq_one]

theorem heisOF_add_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ (x + y) f = heisOF σ JS JT xi0 ψ x (heisOF σ JS JT xi0 ψ y f) := by
  rw [heisOF_heisOF, symplOHF_half he hx hy, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

end GlobalTheory.SplitVacF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParameters
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis.TrivParFun

variable {D : D7}

theorem isParamFun_one_trivPar : ∀ {D : D7} (A : HSp D) (LA : Lat A) (Sf : Finset (FinPl D)), IsSelfDualC A LA →
    (∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) (fun _ : GA D A => (1 : ℂ))
      (GlobalTheory.BottomRallis.trivPar A.rank) := by
  intro D V L Sf hLd _ v _ w h
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hL := hLd.1
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  haveI : Submodule.IsFullLattice D.host.E L := hfull V L hLd
  have hd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hLd v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    have := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h0 : (fun _ : GA D V => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg Submodule.IsFullLattice.span_eq_top h hs hd
    exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w V.rank).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map (LinearMap.pi fun _ : GA D V => LinearMap.id) (fun _ _ => rfl) h0⟩
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hw' w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, -, hconj⟩ := (LFun.exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram L hH hL.fg Submodule.IsFullLattice.span_eq_top hd
    refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero v) V.rank).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ : GA D V => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩
    rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
    exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero v) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

end GlobalTheory.BottomRallis.TrivParFun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParametersStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantFunction_has_trivialRep_satakeParameters : ∀ {D : D7} (A : HSp D) (LA : Lat A) (Sf : Finset (FinPl D)), IsSelfDualC A LA → (∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) (fun _ : GA D A => (1 : ℂ)) (GlobalTheory.BottomRallis.trivPar A.rank) := by
  first | exact @GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar | exact GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar | (intros; apply GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterTrivialSubfieldKillsIdeleNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterTrivialSubfieldKillsIdeleNorms
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.NuCharNorm

open Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.LocTriv
open GlobalTheory.Mem.Chr (finPartI unitIdl locF)
open GlobalTheory.NormSum.UnramHecke GlobalTheory.Mem.Col2.SplitChar

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem inf_upF (χ : HChar L) (k : Fˣ) : χ.inf (upF F k) = ∏ w : InfinitePlace F, χ.resInf w k := by
  classical
  rw [HChar.inf, MonoidHom.comp_apply, infDiag, MonoidHom.finsetProd_apply, map_prod,
    ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap F L)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [HChar.resInf_apply]
  exact Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl

end General

theorem norm_killed (D : D7) (χ : HChar D.host.E) (ht : χ.TrivOn D.host.F) (M : ℕ) (hM : 0 < M)
    (hker : ∀ a : Ideles D.host.E, a ∈ unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) →
      (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤
        Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1)
    (x : (AE D)ˣ) : χ.1 (finIdl D (x * sgU D x)) = 1 := by
  have hfin : ∀ k : (D.host.F)ˣ, χ.1 (finIdl D (incU D (upF D.host.F k))) = 1 := fun k => by
    have h1 := χ.2.2 (upF D.host.F k)
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
    have h2 : χ.inf (upF D.host.F k) = 1 := by
      rw [inf_upF]
      exact Finset.prod_eq_one fun w _ => ht.2 w k
    rw [HChar.inf, MonoidHom.comp_apply] at h2
    rw [h2, one_mul] at h1
    exact h1
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (Nat.mul_pos prod_g_pos hM) hn)
  have hs : -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) ∈ OhE D := neg_mem (mul_mem hr hx)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 =
      ((∏ i, D.host.g i : ℕ) : AE D) * ((M : AE D) * -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul, Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  generalize -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) = s at hs h1
  generalize hG : ((∏ i, D.host.g i : ℕ) : AE D) = G at h1
  have hGm : G ∈ OhE D := hG ▸ natCast_mem _ _
  have hGs : sgA D G = G := hG ▸ map_natCast _ _
  have hMs : sgA D (M : AE D) = M := map_natCast _ _
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime 0)
    have := vl_cong (mul_mem (natCast_mem _ M) hs) 0 v hv
    rw [hG, ← h1, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this
  let z : (AE D)ˣ := incU D (Units.mk0 a ha) * x⁻¹
  have hz : (z : AE D) = 1 + G * ((M : AE D) * s) := eq_add_of_sub_eq' h1
  let w : (AE D)ˣ := z * sgU D z
  have hw : (w : AE D) - 1 = (M : AE D) * (G * (s + sgA D s + G * M * s * sgA D s)) := by
    have e1 : (w : AE D) = (z : AE D) * sgA D z := rfl
    rw [e1, hz, map_add (f := _), map_one, map_mul, map_mul, hGs, hMs]
    ring
  have hwM : ∀ P, vl D P ((w : AE D) - 1) ≤ vl D P (M : AE D) := fun P => by
    rw [hw, map_mul]
    exact mul_le_of_le_one_right' (vl_le (mul_mem hGm (add_mem (add_mem hs (sgA_mem D hs))
      (mul_mem (mul_mem (mul_mem hGm (natCast_mem _ _)) hs) (sgA_mem D hs)))) P)
  have hvM : ∀ P, vl D P (M : AE D) = Valued.v (((M : D.host.E) : P.adicCompletion D.host.E)) := fun P => by
    rw [vl_nat]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu ((χ.1.comp (finPartI D.host.E)).ker)
    (fun v k => (MonoidHom.mem_ker).2 (GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k)) (finIdl D w) (norm_balanced z)
  have hb' : χ.1 (finPartI D.host.E b) = 1 := (MonoidHom.mem_ker).1 hb
  have hc1 : χ.1 (finPartI D.host.E (b⁻¹ * finIdl D w)) = 1 := by
    refine hker _ hun (fun _ => rfl) fun P => ?_
    change Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ _
    rw [← hvM]
    by_cases hP : vl D P ((w : AE D) - 1) < 1
    · have h2 : valAt P (finIdl D w) = 1 := by
        rw [valAt_apply, ← sub_add_cancel ((finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P) 1, add_comm]
        exact Valuation.map_one_add_of_lt _ (by rw [vl_sub_one]; exact hP)
      have h3 : Units.map (ev P) (b⁻¹ * finIdl D w) = Units.map (ev P) (finIdl D w) := by
        rw [map_mul, map_inv, hc P h2, inv_one, one_mul]
      have h4 : ((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P =
          (finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P := congrArg Units.val h3
      rw [h4, vl_sub_one]
      exact hwM P
    · have hM1 : vl D P (M : AE D) = 1 := le_antisymm (vl_le (natCast_mem _ _) P) ((not_lt.1 hP).trans (hwM P))
      rw [hM1]
      refine (Valuation.map_sub _ _ _).trans ?_
      have hP1 : Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P) = 1 := hun P
      rw [hP1, map_one, max_self]
  have e2 : finPartI D.host.E (b⁻¹ * finIdl D w) = (finPartI D.host.E b)⁻¹ * finIdl D w := by
    rw [map_mul, map_inv, finPartI_finIdl]
  rw [e2, map_mul, map_inv, hb', inv_one, one_mul] at hc1
  obtain ⟨k, hk⟩ := exists_real_norm (Units.mk0 a ha)
  have h5 : χ.1 (finIdl D (incU D (Units.mk0 a ha) * sgU D (incU D (Units.mk0 a ha)))) = 1 := by
    rw [hk]
    exact hfin k
  have h6 : χ.1 (finIdl D ((incU D (Units.mk0 a ha) * x⁻¹) * sgU D (incU D (Units.mk0 a ha) * x⁻¹))) = 1 := hc1
  rw [map_mul (sgU D), mul_mul_mul_comm, map_inv, ← mul_inv, map_mul, map_mul, h5, one_mul, map_inv, map_inv,
    inv_eq_one] at h6
  exact h6

end GlobalTheory.NuCharNorm

theorem GlobalTheory.NuCharNorm.chi_norm_one : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.TrivOn D.host.F → (∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles D.host.E, a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1) → ∀ x : (AE D)ˣ, χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D (x * sgU D x)) = 1 :=
  fun D χ ht ⟨M, hM, h⟩ x => GlobalTheory.NuCharNorm.norm_killed D χ ht M hM h x
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterTrivialSubfieldKillsIdeleNormsStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_trivial_subfield_kills_idele_norms : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.TrivOn D.host.F → (∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles D.host.E, a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1) → ∀ x : (AE D)ˣ, χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.NuCharNorm.chi_norm_one | exact GlobalTheory.NuCharNorm.chi_norm_one | (intros; apply GlobalTheory.NuCharNorm.chi_norm_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

theorem nsmul_mem_of_mem_halfCoset {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {r x : Mx D m n}
    (hr : K • r ∈ Λ) (h : x ∈ halfCoset e Λ K r) : K • x ∈ Λ := by
  obtain ⟨u, hu, -, rfl⟩ := h
  rw [nsmul_add]
  exact add_mem hr (nsmul_mem (nsmul_mem hu K) K)

theorem eq_of_mem_halfCoset_reps {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {R : Finset (Mx D m n)}
    (hR3 : ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r') {r r₀ x : Mx D m n} (hr : r ∈ R) (hr₀ : r₀ ∈ R)
    (hm : x ∈ halfCoset e Λ K r) (hm₀ : x ∈ halfCoset e Λ K r₀) : r = r₀ := by
  refine hR3 r hr r₀ hr₀ ?_
  rw [← halfCoset_eq hm, halfCoset_eq hm₀]
  exact mem_halfCoset_self _ _ _ _

theorem exists_cosetExpansion_of_depthOK : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  classical
  intro D T L sc G W U μ₀ hL S t Φ β e τ K hK he hexp hdep
  by_cases hτ : τ = 0
  · subst hτ
    exact ⟨0, hK, ⟨e, he, hexp⟩, fun d hd => by simp at hd⟩
  obtain ⟨d₀, hd₀⟩ := Finsupp.support_nonempty_iff.2 hτ
  have hP0 := hexp.1 d₀ hd₀
  have hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.top t j)) K r → r = r' := fun j =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg
      (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hK hK))
  have hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r → r = r' := fun i =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg
      (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hK hK))
  choose R1 hR1 using hR1
  choose R2 hR2 using hR2
  let dat : (∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) →
      (∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) → PureDat G t :=
    fun ρ ρ' => ((fun j => cosetDatum (d₀.1 j) K (ρ j)), fun i => cosetDatum (d₀.2 i) K (ρ' i))
  set τ' : PureDat G t →₀ ℂ := ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2,
      Finsupp.single (dat ρ ρ') (flatProd S t Φ β ρ ρ') with hτ'
  have hsupp : ∀ d' ∈ τ'.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2, d' = dat ρ ρ' := by
    intro d' hd'
    rw [hτ'] at hd'
    obtain ⟨ρ, hρ, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨ρ', hρ', h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)
    exact ⟨ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩
  refine ⟨τ', hK, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩
  · obtain ⟨ρ, -, ρ', -, rfl⟩ := hsupp d' hd'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · obtain ⟨a, b, c⟩ := hP0.1 j
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
    · obtain ⟨a, b, c⟩ := hP0.2 i
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
  · let g : PureDat G t → ℂ → ℂ := fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)
    have h0 : ∀ d, g d 0 = 0 := fun d => by simp [g]
    have hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂ := fun d b₁ b₂ => by simp only [g]; ring
    change Finsupp.sum τ' g = _
    rw [hτ', ← Finsupp.sum_finsetSum_index h0 hadd]
    simp_rw [← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]
    have hfn1 : ∀ ρ ∈ Fintype.piFinset R1, ∀ j, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j) =
        (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) := fun ρ hρ j =>
      congrFun (cosetDatum_fn (d₀.1 j) (hP0.1 j).2.1 hK ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).1
        ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).2) (x j)
    have hfn2 : ∀ ρ' ∈ Fintype.piFinset R2, ∀ i, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ' hρ' i =>
      congrFun (cosetDatum_fn (d₀.2 i) (hP0.2 i).2.1 hK ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).1
        ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).2) (y i)
    simp only [g, dat]
    have hsum : ∀ ρ ∈ Fintype.piFinset R1, ∀ ρ' ∈ Fintype.piFinset R2,
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j)) * ∏ i : Fin D.R.m, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j)) *
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ hρ ρ' hρ' => by
      rw [Finset.prod_congr rfl fun j _ => hfn1 ρ hρ j, Finset.prod_congr rfl fun i _ => hfn2 ρ' hρ' i]
    rw [Finset.sum_congr rfl fun ρ hρ => Finset.sum_congr rfl fun ρ' hρ' => hsum ρ hρ ρ' hρ']
    show _ = flatProd S t Φ β x y
    by_cases hin : (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)
    · have h1 := fun j => (hR1 j).2.1 (x j) (hx j) (hin.1 j)
      have h2 := fun i => (hR2 i).2.1 (y i) (hy i) (hin.2 i)
      choose ρ0 hρ0 hxρ0 using h1
      choose ρ0' hρ0' hyρ0' using h2
      have hmem : ρ0 ∈ Fintype.piFinset R1 := Fintype.mem_piFinset.2 hρ0
      have hmem' : ρ0' ∈ Fintype.piFinset R2 := Fintype.mem_piFinset.2 hρ0'
      have hz1 : ∀ ρ ∈ Fintype.piFinset R1, ρ ≠ ρ0 →
          ∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) = (0 : ℂ) := by
        intro ρ hρ hne
        obtain ⟨j, hj⟩ : ∃ j, ρ j ≠ ρ0 j := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj ?_) _)
        exact eq_of_mem_halfCoset_reps (hR1 j).2.2 (Fintype.mem_piFinset.1 hρ j) (hρ0 j) hm (hxρ0 j)
      have hz2 : ∀ ρ' ∈ Fintype.piFinset R2, ρ' ≠ ρ0' →
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) = (0 : ℂ) := by
        intro ρ' hρ' hne
        obtain ⟨i, hi⟩ : ∃ i, ρ' i ≠ ρ0' i := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi ?_) _)
        exact eq_of_mem_halfCoset_reps (hR2 i).2.2 (Fintype.mem_piFinset.1 hρ' i) (hρ0' i) hm (hyρ0' i)
      rw [Finset.sum_eq_single_of_mem ρ0 hmem ?s1, Finset.sum_eq_single_of_mem ρ0' hmem' ?s2]
      case s1 =>
        intro ρ hρ hne
        exact Finset.sum_eq_zero fun ρ' _ => mul_eq_zero_of_left (mul_eq_zero_of_right _ (hz1 ρ hρ hne)) _
      case s2 =>
        intro ρ' hρ' hne
        exact mul_eq_zero_of_right _ (hz2 ρ' hρ' hne)
      refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun j _ => ?_))
        (Finset.prod_eq_one fun i _ => ?_)).trans ?_
      · exact Set.indicator_of_mem (hxρ0 j) _
      · exact Set.indicator_of_mem (hyρ0' i) _
      rw [mul_one, mul_one]
      choose u hu hu' hxu using hxρ0
      choose v hv hv' hyv using hyρ0'
      have hx' : x = ρ0 + K • u := funext fun j => by rw [Pi.add_apply, Pi.smul_apply]; exact hxu j
      have hy' : y = ρ0' + K • v := funext fun i => by rw [Pi.add_apply, Pi.smul_apply]; exact hyv i
      rw [hx', hy']
      exact (hdep.2 ρ0 u ρ0' v (fun j => ((hR1 j).1 _ (hρ0 j)).1) (fun i => ((hR2 i).1 _ (hρ0' i)).1)
        (fun j => ⟨hu' j, hu j⟩) (fun i => ⟨hv' i, hv i⟩)).symm
    · have hzero : flatProd S t Φ β x y = 0 := by
        by_contra h
        exact hin (hdep.1 x y hx hy h)
      rw [hzero]
      refine Finset.sum_eq_zero fun ρ hρ => Finset.sum_eq_zero fun ρ' hρ' => ?_
      rw [Fintype.mem_piFinset] at hρ hρ'
      rcases not_and_or.1 hin with h | h
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem
          (fun hm => hj (nsmul_mem_of_mem_halfCoset ((hR1 j).1 _ (hρ j)).2 hm)) _))) _
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem
          (fun hm => hi (nsmul_mem_of_mem_halfCoset ((hR2 i).1 _ (hρ' i)).2 hm)) _))
  · obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := hsupp d' hd'
    rw [Fintype.mem_piFinset] at hρ hρ'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h := (hR1 j).1 _ (hρ j)
      exact isCosetDatum_cosetDatum _ hK ((hP0.1 j).2.1 ▸ h.1) h.2
    · have h := (hR2 i).1 _ (hρ' i)
      exact isCosetDatum_cosetDatum _ hK ((hP0.2 i).2.1 ▸ h.1) h.2

end GlobalTheory.DepthUnf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  first | exact @GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK | exact GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK | (intros; apply GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.LatMove

open scoped Matrix

theorem mem_hat_stdLat_iff {D : D7} {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ IntVec z := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem mem_hat_colLat_iff {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E)
    (w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) ↔
      IntVec (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) := by
  have ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]
  have h1 := GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)
  rw [ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
  exact h1.trans (mem_hat_stdLat_iff _)

theorem swap_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔
      u ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  rw [GlobalTheory.GenusTranslate.hatL_iff]
  simp only [AlgEquiv.symm_apply_apply]

theorem exists_move {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) :
    ∃ x ∈ GfC V, ∀ w, w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin V.rank → D.host.E)) ↔
      (finHom V x).1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨x, hx, h⟩ := GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
  refine ⟨x, hx, fun w => ?_⟩
  have h1 := h fun i => Formalism.IndefR.Lev.swapAE D (w i)
  have h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) =
      fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm
  rw [h2] at h1
  exact (swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))

theorem exists_finite_point : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  intro D _ V M hM
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)
  obtain ⟨B, rfl⟩ := hu
  obtain ⟨x, hx, h⟩ := exists_move V B hM
  refine ⟨x⁻¹, inv_mem hx, fun y => ?_⟩
  have hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) :=
    Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm
  have h1 := h ((finHom V x⁻¹).1 *ᵥ y)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec,
    mem_hat_colLat_iff, Matrix.coe_units_inv] at h1
  rw [hL]
  exact h1.symm

end GlobalTheory.DefTransfer.LatMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  first | exact @GlobalTheory.DefTransfer.LatMove.exists_finite_point | exact GlobalTheory.DefTransfer.LatMove.exists_finite_point | (intros; apply GlobalTheory.DefTransfer.LatMove.exists_finite_point <;> assumption)
end
end

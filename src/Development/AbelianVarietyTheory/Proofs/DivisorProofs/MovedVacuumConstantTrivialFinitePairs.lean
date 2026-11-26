module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInert

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorNormalisingVectorNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorNormalisingVectorNeZero
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem om_normalising_ne_zero : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0),
  Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ → oddE0 D cc δ t0 a d e0 →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d), W.Om x y e0 ≠ 0 := by
  intro D cc δ t0 a d e0 W hC hodd x y h0
  have he0 := hodd.1
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hWL, -, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC a d
    (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) v e0 = e0 := by
    intro v hv
    rw [hWL v hv]; funext w; exact he0.2 v hv w
  have heT : e0 ∈ TT D (tor0 D cc δ) a d :=
    ⟨he0.1, 1, one_pos, fun v hv => by rw [one_nsmul]; exact hfix v hv⟩
  have h1 := W.mul x⁻¹ x y⁻¹ y e0 heT
  rw [inv_mul_cancel, inv_mul_cancel, W.one _ heT, h0] at h1
  have h2 := W.smul x⁻¹ y⁻¹ 0 e0 heT
  rw [zero_smul, zero_smul] at h2
  exact W.nz (h1.trans h2)

end GlobalTheory.NormExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorNormalisingVectorNeZeroStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_normalisingVector_ne_zero : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0),
  Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ → oddE0 D cc δ t0 a d e0 →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d), W.Om x y e0 ≠ 0 := by
  first | exact @GlobalTheory.NormExact.om_normalising_ne_zero | exact GlobalTheory.NormExact.om_normalising_ne_zero | (intros; apply GlobalTheory.NormExact.om_normalising_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupOne
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFormula

theorem isFinPt_one : ∀ {D : D7} (V : HSp D) {n : ℕ}, V.rank = n → IsFinPt V (1 : GA D V) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  intro D V n hn
  subst hn
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  have hL : (finHom V (1 : GA D V)).val = 1 := by
    rw [map_one]; rfl
  rw [hL, Fin.cast_eq_self, Fin.cast_eq_self]
  show _ = toFinE D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end GlobalTheory.BotFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupOneStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one : ∀ {D : D7} (V : HSp D) {n : ℕ}, V.rank = n → IsFinPt V (1 : GA D V) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  first | exact @GlobalTheory.BotFormula.isFinPt_one | exact GlobalTheory.BotFormula.isFinPt_one | (intros; apply GlobalTheory.BotFormula.isFinPt_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsGaussianSmulConstUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsGaussianSmulConstUnique
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact

theorem reads_smul_const_unique : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (G : VC D a d → ℂ) (f : WO S T → ℂ) (c c' : ℂ), G ≠ 0 →
  Reads ψ θ hS hT cc δ r (c • G) f → Reads ψ θ hS hT cc δ r (c' • G) f → c = c' := by
  intro D ψ θ S T a d hS hT cc δ r hs G f c c' hG h1 h2
  subst hS hT
  obtain ⟨Y, hY⟩ : ∃ Y, G Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hG (funext hc)
  have hδ : δ ≠ 0 := delta_ne_zero hs.crv
  have hr : r ≠ 0 := IsScale.ne_zero hs.crv.1.1 hs.scale
  have hm : ∀ τ, δ * embT D τ r ≠ 0 := fun τ => mul_ne_zero hδ ((map_ne_zero _).2 hr)
  obtain ⟨x, ⟨hx, hx0⟩, -⟩ := GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hs.inf T.rank S.rank
    (fun τ => Matrix.of fun i j => Y τ i j / (δ * embT D τ r)) 0
  replace hx0 : x.map (finPart D) = 0 := by rw [hx0]; exact Matrix.map_zero _ (map_zero _)
  have hxY : coordY θ rfl rfl δ r x = Y := by
    funext τ i j
    simp only [coordY, Fin.cast_eq_self, hx, Matrix.of_apply]
    have hE : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    field_simp [hm τ, hE, hδ]
  have e1 := h1.2 x hx0
  have e2 := h2.2 x hx0
  rw [hxY] at e1 e2
  rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e2
  have he := Complex.exp_ne_zero (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) Y Y)
  have := mul_left_cancel₀ he e2
  exact mul_right_cancel₀ hY this

end GlobalTheory.NormExact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsGaussianSmulConstUniqueStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readsGaussian_smul_const_unique : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (G : VC D a d → ℂ) (f : WO S T → ℂ) (c c' : ℂ), G ≠ 0 →
  Reads ψ θ hS hT cc δ r (c • G) f → Reads ψ θ hS hT cc δ r (c' • G) f → c = c' := by
  first | exact @GlobalTheory.NormExact.reads_smul_const_unique | exact GlobalTheory.NormExact.reads_smul_const_unique | (intros; apply GlobalTheory.NormExact.reads_smul_const_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsFiniteAdelicPointSame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsFiniteAdelicPointSame
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPtUnique

theorem eq_of_isFinPt : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
    IsFinPt V g x → IsFinPt V g' x → g = g' := by
  intro D V n g g' x ⟨hg, e, he⟩ ⟨hg', e', he'⟩
  apply GlobalTheory.FinRealComm.GA_ext_inf_fin V
  · have h1 : infHom V g = 1 := hg
    have h2 : infHom V g' = 1 := hg'
    rw [h1, h2]
  · apply Units.ext
    apply Matrix.ext
    intro i j
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [he i j, he' i j]

end GlobalTheory.FinPtUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsFiniteAdelicPointSameStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isFiniteAdelicPoint_same : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  IsFinPt V g x → IsFinPt V g' x → g = g' := by
  first | exact @GlobalTheory.FinPtUnique.eq_of_isFinPt | exact GlobalTheory.FinPtUnique.eq_of_isFinPt | (intros; apply GlobalTheory.FinPtUnique.eq_of_isFinPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupMul
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPtMul

theorem isFinPt_mul : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x x' : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  IsFinPt V g x → IsFinPt V g' x' → IsFinPt V (g * g') (x * x') := by
  intro D V n g g' x x' hx hx'
  obtain ⟨hg, e, h⟩ := hx
  obtain ⟨hg', e', h'⟩ := hx'
  subst e
  refine ⟨mul_mem hg hg', rfl, fun i j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, Fin.cast_eq_self]
  refine Finset.sum_congr rfl fun k _ => ?_
  have a := h i k
  have b := h' k j
  simp only [Fin.cast_eq_self] at a b
  rw [a, b]

end GlobalTheory.FinPtMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupMulStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x x' : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  IsFinPt V g x → IsFinPt V g' x' → IsFinPt V (g * g') (x * x') := by
  first | exact @GlobalTheory.FinPtMul.isFinPt_mul | exact GlobalTheory.FinPtMul.isFinPt_mul | (intros; apply GlobalTheory.FinPtMul.isFinPt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumConstantTrivialFinitePairs
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacTriv

theorem one_suppSplit {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_suppInert {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_intG {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.IntG D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro i j
  simp only [inv_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨one_mem _, one_mem _⟩
  · exact ⟨zero_mem _, zero_mem _⟩

theorem vacuum_const_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hW hInp t0 ht0 hev hodd hχS hχT f₀ hf₀ hline hmul hsplit hinert
  subst hS
  subst hT
  have hnz : ∀ x y, W.Om x y e0 ≠ 0 := GlobalTheory.T.weilOperator_normalisingVector_ne_zero cc δ t0 e0 W hset.crv hodd
  have huniq : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T) (c c' : ℂ),
      Reads ψ θ rfl rfl cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r (c' • W.Om x y e0) (om (g, h) f₀) → c = c' :=
    fun x y g h c c' h1 h2 => GlobalTheory.T.readsGaussian_smul_const_unique ψ θ S T rfl rfl cc δ r hset _ _ c c' (hnz x y) h1 h2
  have hone : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T),
      Reads ψ θ rfl rfl cc δ r (W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r ((1 : ℂ) • W.Om x y e0) (om (g, h) f₀) := fun x y g h hr => by rwa [one_smul]
  have p1S : IsFinPt S (1 : GA D S) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one S rfl
  have p1T : IsFinPt T (1 : GA D T) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one T rfl
  have exS : ∀ x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank, ∃ g, IsFinPt S g x :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one S hset.gS x rfl
  have exT : ∀ y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank, ∃ h, IsFinPt T h y :=
    fun y => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one T hset.gT y rfl
  choose gx hgx using exS
  choose hy hhy using exT
  have gx1 : gx 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ 1 (hgx 1) p1S
  have hy1 : hy 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ 1 (hhy 1) p1T
  have gxm : ∀ x₁ x₂, gx x₁ * gx x₂ = gx (x₁ * x₂) :=
    fun x₁ x₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul S _ _ _ _ (hgx x₁) (hgx x₂)) (hgx (x₁ * x₂))
  have hym : ∀ y₁ y₂, hy y₁ * hy y₂ = hy (y₁ * y₂) :=
    fun y₁ y₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul T _ _ _ _ (hhy y₁) (hhy y₂)) (hhy (y₁ * y₂))
  choose cS hcS using fun x => hline x 1 (gx x) 1 (hgx x) p1T
  choose cT hcT using fun y => hline 1 y 1 (hy y) p1S (hhy y)

  have cS1 : cS 1 = 1 := by
    have h1 := hcS 1
    rw [gx1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cSm : ∀ x₁ x₂, cS (x₁ * x₂) = cS x₁ * cS x₂ := by
    intro x₁ x₂
    have h1 := hmul x₁ 1 (gx x₁) 1 x₂ 1 (gx x₂) 1 (cS x₁) (cS x₂) (hgx _) p1T (hgx _) p1T (hcS x₁) (hcS x₂)
    rw [mul_one, mul_one, gxm] at h1
    exact huniq _ _ _ _ _ _ (hcS (x₁ * x₂)) h1
  have cT1 : cT 1 = 1 := by
    have h1 := hcT 1
    rw [hy1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cTm : ∀ y₁ y₂, cT (y₁ * y₂) = cT y₁ * cT y₂ := by
    intro y₁ y₂
    have h1 := hmul 1 y₁ 1 (hy y₁) 1 y₂ 1 (hy y₂) (cT y₁) (cT y₂) p1S (hhy _) p1S (hhy _) (hcT y₁) (hcT y₂)
    rw [mul_one, mul_one, hym] at h1
    exact huniq _ _ _ _ _ _ (hcT (y₁ * y₂)) h1
  let νS : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank →* ℂ := { toFun := cS, map_one' := cS1, map_mul' := cSm }
  let νT : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank →* ℂ := { toFun := cT, map_one' := cT1, map_mul' := cTm }
  have tS : ∀ x, cS x = 1 := by
    intro x
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert S hset.gS νS.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hsplit k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppSplit)))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hinert k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppInert)
          hki (by simpa using one_intG))))) x
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  have tT : ∀ y, cT y = 1 := by
    intro y
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert T hset.gT νT.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hsplit 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppSplit) hk))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hinert 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppInert) hk
          (by simpa using one_intG) hki)))) y
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  intro x y g h hg hh
  have eg : g = gx x := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ x hg (hgx x)
  have eh : h = hy y := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ y hh (hhy y)
  subst eg eh
  have h1 := hmul x 1 (gx x) 1 1 y 1 (hy y) (cS x) (cT y) (hgx x) p1T p1S (hhy y) (hcS x) (hcT y)
  rw [tS, tT] at h1
  simp only [mul_one, one_mul, one_smul] at h1
  exact h1

end GlobalTheory.VacTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumConstantTrivialFinitePairsStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_constant_trivial_finite_pairs : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  first | exact @GlobalTheory.VacTriv.vacuum_const_trivial | exact GlobalTheory.VacTriv.vacuum_const_trivial | (intros; apply GlobalTheory.VacTriv.vacuum_const_trivial <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7}

theorem GQ_negGA_mem (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_GQ (p : Pair T) {γ : GA D (G.V p.small)} {γ' : GA D (G.V p.big)} (hγ : γ ∈ GQ (G.V p.small))
    (hγ' : γ' ∈ GQ (G.V p.big)) : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
  cases p with
  | chi i j => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | mu t i j => exact ⟨hγ, hγ'⟩
  | core i => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | top t j => exact ⟨hγ, hγ'⟩

theorem ker_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T),
    p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  intro D T L sc G W p hp f hf γ hγ γ' hγ' g h
  have hw := W.om_is p hp
  obtain ⟨h1, h2⟩ := toPair_GQ p hγ hγ'
  have e : W.ker p f (γ * g) (γ' * h) =
      W.om p (G.toPair p γ γ') (W.om p (G.toPair p g h) f) 0 := by
    simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.mk.eta, map_mul, Module.End.mul_apply]
  rw [e]
  have := hw.om_aut _ h1 _ h2 (W.om p (G.toPair p g h) f) (hw.om_pres (G.toPair p g h) f hf)
  rw [Prod.mk.eta] at this
  rw [this]
  simp only [GridData.Weil.ker, thetaKO, Prod.mk.eta]

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_grid_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  first | exact @GlobalTheory.RowReal.ker_rat_left | exact GlobalTheory.RowReal.ker_rat_left | (intros; apply GlobalTheory.RowReal.ker_rat_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAl
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAl
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblIdent

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Matrix in
theorem fromRows_add_fromRows {R : Type} [Add R] {m₁ m₂ n : Type} (A B : Matrix m₁ n R) (C D : Matrix m₂ n R) :
    fromRows A C + fromRows B D = fromRows (A + B) (C + D) := by
  ext (i | i) j <;> rfl

open Matrix in
theorem smul_fromRows {R S : Type} [SMul S R] {m₁ m₂ n : Type} (s : S) (A : Matrix m₁ n R) (C : Matrix m₂ n R) :
    s • fromRows A C = fromRows (s • A) (s • C) := by
  ext (i | i) j <;> rfl

theorem nT_eq {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (X Y : Matrix (Fin d) (Fin d) R)
    (h2 : (Y + 1) * (X + 1) = 1) (hc : (c * c) • X = X) :
    ((h * h * h) • ((1 - c) • X - (1 + c) • Y)) * (1 + (h * (1 + c)) • X) = (h * h) • X := by
  have hYX : Y * X = -X - Y := by
    have e : Y * X + X + Y = 0 := by
      have := h2; rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul] at this
      rw [← sub_eq_zero] at this; rw [← this]; abel
    rw [← sub_eq_zero, ← e]; abel
  have hY : (c * c) • Y = Y := by
    have e : Y = -((Y + 1) * X) := by
      rw [add_mul, one_mul, hYX]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hc]
  have hXX : (c * c) • (X * X) = X * X := by rw [← Matrix.smul_mul, hc]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
    smul_sub, smul_add, smul_smul, Matrix.mul_sub]
  linear_combination (norm := module) (-(h ^ 4 * (1 + c) ^ 2)) • hYX - h ^ 4 • hXX + h ^ 4 • hc + h ^ 4 • hY +
    hh • ((h ^ 3 * (1 + c) + h ^ 2) • X + (h ^ 3 * (1 + c)) • Y)

theorem blocks {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (K N T : Matrix (Fin d) (Fin d) R)
    (hT : T = 1 + (h * (1 + c)) • (K - 1)) (hNT : N * T = (h * h) • (K - 1)) :
    (1 + (h * c) • (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R))ᵀ)) *
        Matrix.fromBlocks K 0 0 (1 : Matrix (Fin d) (Fin d) R) * Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) =
      (1 + Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R) * N * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R))ᵀ) *
        Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * T := by
  simp only [Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg, Matrix.add_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_add, smul_fromRows,
    fromRows_add_fromRows, hNT]
  rw [Matrix.fromRows_inj.eq_iff]
  subst hT
  constructor
  · linear_combination (norm := module) hh • (-(h + 1) • (K - 1))
  · linear_combination (norm := module) hh • (h • (K - 1))

end GlobalTheory.SplitDblIdent

namespace GlobalTheory.SplitDblGen

theorem half_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    (half : AE F E) * 2 = 1 := by
  rw [half, show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem diagonalFixingDoubling_mul_firstFactor_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := AE F E) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := AE F E) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  intro F E _ _ _ _ _ d c K K' _ h2 hc
  have hNT := GlobalTheory.SplitDblIdent.nT_eq half c half_mul_two (K - 1) (K' - 1) (by simpa using h2) hc
  exact GlobalTheory.SplitDblIdent.blocks half c half_mul_two K (splitDoublingNBlock c K K') (tMat c K) rfl hNT

end GlobalTheory.SplitDblGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAlStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  first | exact @GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian | exact GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian | (intros; apply GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : ι → Type} (T : ∀ i, (X i → ℂ) →ₗ[ℂ] (Y i → ℂ)) {δ : Type}

theorem sum_prod_partial_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (A : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ Aᶜ, F d i (x i)) = 0 := by
  induction A using Finset.induction_on generalizing x with
  | empty => simpa using h x
  | @insert b A hb ih =>
    set c : δ → ℂ := fun d => a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ (insert b A)ᶜ, F d i (x i)) with hc
    have hbA : b ∈ Aᶜ := Finset.mem_compl.2 hb
    have hcompl : (insert b A)ᶜ = (Aᶜ).erase b := by
      ext i; simp [Finset.mem_erase, and_comm]
    have hφ : (∑ d ∈ s, c d • F d b) = 0 := by
      funext z
      have := ih (Function.update x b z)
      rw [Finset.sum_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hc, ← Finset.mul_prod_erase _ _ hbA, Function.update_self, hcompl]
      have : ∏ i ∈ (Aᶜ).erase b, F d i (Function.update x b z i) = ∏ i ∈ (Aᶜ).erase b, F d i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [this]; ring
    have h2 := congrArg (fun f => T b f (y b)) hφ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.prod_insert hb, hc]; ring

theorem sum_prod_map_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) = 0 := by
  by_cases hX : Nonempty (∀ i, X i)
  · obtain ⟨x⟩ := hX
    simpa using sum_prod_partial_eq_zero T s a F h Finset.univ x y
  · have hi : ∃ i, IsEmpty (X i) := by
      by_contra hn
      push_neg at hn
      exact hX ⟨fun i => Classical.choice (hn i)⟩
    obtain ⟨i, hi⟩ := hi
    have h0 : ∀ f : X i → ℂ, f = 0 := fun f => funext fun z => hi.elim z
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0 (F d i), map_zero]; rfl), mul_zero]

theorem sum_prod_map_congr {δ' : Type} (s : Finset δ) (s' : Finset δ') (a : δ → ℂ) (a' : δ' → ℂ) (F : δ → ∀ i, X i → ℂ)
    (F' : δ' → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s', a' d * ∏ i, F' d i (x i) = ∑ d ∈ s, a d * ∏ i, F d i (x i)) (y : ∀ i, Y i) :
    ∑ d ∈ s', a' d * ∏ i, T i (F' d i) (y i) = ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) := by
  have key := sum_prod_map_eq_zero T (s'.disjSum s) (Sum.elim a' fun d => -a d) (Sum.elim F' F) (fun x => by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, h x, add_neg_cancel]) y
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact key)

end Tensor

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def stdLatO (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E))
    fun _ => True

def movedFn (_S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => (d.1 j').fn) ⟨j, by omega⟩
      fun x => (d.1 ⟨j, by omega⟩).fn (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ x))
    ⟨j + 1, hj⟩ fun x => (d.1 ⟨j + 1, hj⟩).fn (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (hz : d.z = 1) (hv : S.Z.HasVec d)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hTm : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLatO S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := hv
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, ← hf.2 Tm hTm]
  rw [show ((1 : GA D (G.pS p)), (1 : GA D (G.pT p))) = 1 from rfl, map_one]
  rfl

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelPar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelPar
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblPar

section Gen
variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def shear (ι : Type) [DecidableEq ι] (s : A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A :=
  Matrix.fromBlocks ((1 + s) • 1) ((-s) • 1) (s • 1) ((1 - s) • 1)

theorem shear_mul (s t : A) : shear ι s * shear ι t = shear ι (s + t) := by
  simp only [shear, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

omit [Fintype ι] in
theorem shear_zero : shear ι (0 : A) = 1 := by
  simp [shear, Matrix.fromBlocks_one]

omit [Fintype ι] in
theorem shear_map (f : A →+* A) (s : A) : (shear ι s).map f = shear ι (f s) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [shear, Matrix.one_apply, h]

theorem shear_unitary (J : Matrix ι ι A) (s : A) : (shear ι s)ᵀ * dbl J * shear ι (-s) = dbl J := by
  simp only [shear, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    zero_add, smul_smul, smul_neg, Matrix.neg_mul, smul_zero]
  congr 1 <;> module

theorem shear_mulVec_inl (s : A) (z : ι ⊕ ι → A) :
    (fun i => (shear ι s *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + s • (fun i => z (Sum.inl i)) - s • (fun i => z (Sum.inr i)) := by
  funext i
  simp [shear, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  ring

theorem shear_mulVec_inr (s : A) (z : ι ⊕ ι → A) :
    (fun i => (shear ι s *ᵥ z) (Sum.inr i)) =
      (fun i => z (Sum.inr i)) + s • (fun i => z (Sum.inl i)) - s • (fun i => z (Sum.inr i)) := by
  funext i
  simp [shear, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  ring

theorem shear_diagCols (s : A) : shear ι s * (diagCols ι : Matrix (ι ⊕ ι) ι A) = (diagCols ι : Matrix (ι ⊕ ι) ι A) * (1 : Matrix ι ι A) := by
  rw [Matrix.mul_one]
  ext (i | i) j <;> by_cases h : i = j <;>
    simp [shear, diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h]

theorem shear_eq (s : A) : shear ι s = 1 + s • ((diagCols ι : Matrix (ι ⊕ ι) ι A) * (Matrix.fromRows (1 : Matrix ι ι A) (-1))ᵀ) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [shear, diagCols, Matrix.mul_apply, Matrix.one_apply, h, sub_eq_add_neg]
  all_goals (intro h'; exact absurd h'.symm h)

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem diagonalFixingDoublingMatrix_eq_shear (c : AE F E) (d : ℕ) : GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d = shear (Fin d) (GlobalTheory.SplitDblGen.half * c) :=
  (shear_eq _).symm

theorem shear_mem_latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (s : AE F E)
    (hs : ∀ z ∈ GlobalTheory.InertSph.latAt W v, s • z ∈ GlobalTheory.InertSph.latAt W v) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertDbl.latAtD W v) : shear (Fin d) s *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  refine ⟨?_, ?_⟩
  · rw [shear_mulVec_inl]; exact sub_mem (add_mem hz.1 (hs _ hz.1)) (hs _ hz.2)
  · rw [shear_mulVec_inr]; exact sub_mem (add_mem hz.2 (hs _ hz.1)) (hs _ hz.2)

theorem diagonalFixingDoublingMatrix_mem_integralSiegelParabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → At (evFin F v) c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ p ∈ GlobalTheory.InertDbl.ParD σ W v, GlobalTheory.InertDbl.matD p = GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hat hlat
  set s : AE F E := GlobalTheory.SplitDblGen.half * c with hsdef
  have hσ : cA σ s = -s := by
    rw [hsdef, map_mul, hc, GlobalTheory.SplitDblGen.half, AlgHom.commutes, mul_neg]
  have hs : ∀ z ∈ GlobalTheory.InertSph.latAt W v, s • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hsdef, mul_smul, GlobalTheory.SplitDblGen.half, algebraMap_smul]
    exact GlobalTheory.InertSph.invTwo_smul_mem_latAt F E d W v h2 _ (hlat z hz)
  have hs' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-s) • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [neg_smul]; exact neg_mem (hs z hz)
  have hu : (shear (Fin d) s)ᵀ * dbl (incM F W.J) * (shear (Fin d) s).map (cA σ) = dbl (incM F W.J) := by
    have h := shear_map (ι := Fin d) (cA σ : AE F E →+* AE F E) s
    have h' : (shear (Fin d) s).map (cA σ) = shear (Fin d) (-s) := by rw [← hσ]; exact h
    rw [h', shear_unitary]
  let p : GlobalTheory.InertDbl.UD σ W :=
    ⟨⟨shear (Fin d) s, shear (Fin d) (-s), by rw [shear_mul, add_neg_cancel, shear_zero],
      by rw [shear_mul, neg_add_cancel, shear_zero]⟩, hu⟩
  have hp : GlobalTheory.InertDbl.matD p = shear (Fin d) s := rfl
  have hpi : GlobalTheory.InertDbl.matD p⁻¹ = shear (Fin d) (-s) := rfl
  refine ⟨p, ⟨⟨fun u hu => ?_, fun z hz => ?_⟩, 1, ?_⟩, (diagonalFixingDoublingMatrix_eq_shear c d).symm⟩
  · have h0 : u • s = 0 := by rw [hsdef, ← mul_smul_comm, hat u hu, mul_zero]
    rw [hp, shear_eq, add_sub_cancel_left, ← smul_assoc, h0, zero_smul]
  · rw [hp, hpi]
    exact ⟨shear_mem_latAtD W v s hs hz, shear_mem_latAtD W v (-s) hs' hz⟩
  · exact shear_diagCols s

end GlobalTheory.SplitDblPar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelParStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c → At (evFin F v) c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ p ∈ GlobalTheory.InertDbl.ParD σ W v, GlobalTheory.InertDbl.matD p = GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d := by
  first | exact @GlobalTheory.SplitDblPar.diagonalFixingDoublingMatrix_mem_integralSiegelParabolic | exact GlobalTheory.SplitDblPar.diagonalFixingDoublingMatrix_mem_integralSiegelParabolic | (intros; apply GlobalTheory.SplitDblPar.diagonalFixingDoublingMatrix_mem_integralSiegelParabolic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hc.2.2.2 τ, hc.2.2.2 τ, star_star]

theorem exists_anti_unit {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {v : Pl (F := F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    ∃ (τ : E →ₐ[F] Fv F v) (δ : 𝓞 E), σ (δ : E) = -(δ : E) ∧ Valued.v (τ (δ : E)) = 1 := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have hPv : P.under (𝓞 F) = v := HeightOneSpectrum.ext hP
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc ⟨P, Q, hPQ, hP, hQ⟩ hPv
  obtain ⟨w', hne, -, -, -, hw'⟩ := SplitChart.exists_conj_place hc (splitPrime_under τ) ⟨P, Q, hPQ, hP, hQ⟩
  have hmax : (splitPrime τ).asIdeal.IsMaximal := (splitPrime τ).isMaximal
  have hmax' : w'.asIdeal.IsMaximal := w'.isMaximal
  have hnle : ¬ (splitPrime τ).asIdeal ≤ w'.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (hmax.eq_of_le hmax'.ne_top hle))
  obtain ⟨θ, hθP, hθw⟩ := Set.not_subset.1 hnle
  set σθ : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) θ with hσθ
  have hσθP : σθ ∉ (splitPrime τ).asIdeal := by
    intro h
    apply hθw
    rw [hw']
    exact h
  refine ⟨τ, θ - σθ, ?_, ?_⟩
  · have e : ((σθ : 𝓞 E) : E) = σ (θ : E) := rfl
    push_cast
    rw [map_sub]
    change σ (θ : E) - σ (σ (θ : E)) = -((θ : E) - σ (θ : E))
    rw [conj_conj hc]
    ring
  · have hnot : θ - σθ ∉ (splitPrime τ).asIdeal := by
      intro h
      apply hσθP
      have := (splitPrime τ).asIdeal.sub_mem hθP h
      simpa using this
    rw [mem_splitPrime] at hnot
    exact le_antisymm (apply_coe_mem τ _) (not_lt.1 hnot)

theorem smul_eq_self_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M}
    (hz : At (evFin F v) z) : GlobalTheory.LatVac.liftV v 1 • z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem liftV_mul_liftV (v : Pl (F := F)) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = GlobalTheory.LatVac.liftV v (a * b) := by
  rw [show GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = _ from GlobalTheory.EmbChart.atPlace_mul_right v a _]
  show GlobalTheory.LatVac.liftV v (a * evFin F v (GlobalTheory.LatVac.liftV v b)) = _
  rw [GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.SplitSign


open GlobalTheory.SplitSign in
theorem GlobalTheory.SplitSign.exists_split_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : AE F E, cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : AE F E, At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨τ, δ, hσδ, hδv⟩ := exists_anti_unit hB.cm hv
  set s : Fv F v := τ (δ : E) with hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hδv
    exact zero_ne_one hδv
  have hsinv : s⁻¹ ∈ v.adicCompletionIntegers F := by
    show Valued.v s⁻¹ ≤ 1
    rw [map_inv₀, hδv, inv_one]
  obtain ⟨f, hf⟩ := SnMass.SkewVol.mem_range_of_cm_fixed hB.cm (x := (δ : E) * δ)
    (by rw [map_mul, hσδ, neg_mul_neg])
  refine ⟨GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E), ?_, ?_, ?_, ?_⟩
  · rw [cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσδ, TensorProduct.tmul_neg]
  · intro u hu
    rw [TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v s⁻¹ u hu, TensorProduct.zero_tmul]
  · intro z hz
    have hcc : (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) * (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) =
        GlobalTheory.LatVac.liftV v 1 • (1 : AE F E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', liftV_mul_liftV, ← map_smul]
      have h1 : f • (s⁻¹ * s⁻¹) = (1 : Fv F v) := by
        rw [Algebra.smul_def, ← AlgHom.commutes τ f, hf, map_mul, ← hs]
        field_simp
      rw [h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcc, smul_mul_assoc, one_mul, smul_eq_self_of_at hz]
  · intro d W z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v s⁻¹ * a, ?_, ?_, δ • y, W.L.smul_mem δ hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem hsinv hav
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', mul_one,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitSign.exists_split_sign | exact GlobalTheory.SplitSign.exists_split_sign | (intros; apply GlobalTheory.SplitSign.exists_split_sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem triIs_congr {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ ψ' : AddChar (AF D.host.F) ℂ} {θ θ' : InfFam D}
    {α α' β β' : T → ((AE D)ˣ →* Circle)} {ν ν' : T → Formalism.L2.Host.HChar D.host.E} {S S' : T → Finset (Pl D.host.E)}
    (h : X.Is ψ θ α β ν S) (e1 : ψ' = ψ) (e2 : θ' = θ) (e3 : ∀ t, α' t = α t) (e4 : ∀ t, β' t = β t) (e5 : ∀ t, ν' t = ν t)
    (e6 : ∀ t, S' t = S t) : X.Is ψ' θ' α' β' ν' S' := by
  obtain rfl := e1
  obtain rfl := e2
  obtain rfl := funext e3
  obtain rfl := funext e4
  obtain rfl := funext e5
  obtain rfl := funext e6
  exact h


set_option maxHeartbeats 1000000 in
theorem trBot_holds : TrBot := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hB
  obtain ⟨hl, hg, hw, -⟩ := hA
  have pre := hl.pre
  cases X with | mk B C Wr V Sg N Gj =>
  cases X' with | mk B' C' Wr' V' Sg' N' Gj' =>
  cases B
  cases B'
  dsimp only at pre
  subst pre
  let DX := GlobalTheory.Mem.Stages.toD7 ⟨_, C, Wr, V, Sg, N, Gj⟩
  let DX' := GlobalTheory.Mem.Stages.toD7 ⟨_, C', Wr', V', Sg', N', Gj'⟩
  obtain ⟨f, f', hff, hC, hC'⟩ := hl.C
  obtain rfl : f' = f := eq_of_heq hff
  have hψ : W'.ψ = (by with_unfolding_all exact (W.ψ :)) := eq_of_heq hw.ψ
  have hθ : W'.θ = (by with_unfolding_all exact (W.θ :)) := eq_of_heq hw.θ
  have hxiH : ∀ t, L'.xiH t = (by with_unfolding_all exact ((L.xiH (ι t)) :)) := fun t => eq_of_heq (hl.xi t)
  have hQ : ∀ t, L'.Q t = (by with_unfolding_all exact ((L.Q (ι t)) :)) := fun t => eq_of_heq (hl.Q t)
  have hchi : G'.ch.chi = (by with_unfolding_all exact (G.ch.chi :)) := eq_of_heq hg.chi
  have hchiH : G'.ch.chiH = (by with_unfolding_all exact (G.ch.chiH :)) := eq_of_heq hg.chiH
  have hv0 : G'.pl.v0 = (by with_unfolding_all exact (G.pl.v0 :)) := eq_of_heq hg.v0
  have hwp : G'.pl.w = (by with_unfolding_all exact (G.pl.w :)) := eq_of_heq hg.w
  have hCmu : ∀ j, L'.C.mu0 j = (by with_unfolding_all exact ((L.C.mu0 j) :)) := fun j => by
    have a : L.C.mu0 j = f'.mu0 j := by rw [hC]; rfl
    have b : L'.C.mu0 j = f'.mu0 j := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hCeta : L'.C.eta = (by with_unfolding_all exact (L.C.eta :)) := by
    have a : L.C.eta = f'.eta := by rw [hC]; rfl
    have b : L'.C.eta = f'.eta := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hmu0 : ∀ j : Fin DX'.R.m, L'.mu0 (↑j + 1) = (by with_unfolding_all exact ((L.mu0 (↑j + 1)) :)) := fun j => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.mu0 (↑j + 1)) :))) (L'.C.mu0 j) := by rw [hCmu j]; exact (by with_unfolding_all exact ((hl.is.mu0 j) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.mu0 j) h1
  have heta : L'.eta = (by with_unfolding_all exact (L.eta :)) := by
    have h1 : ChrEq ((by with_unfolding_all exact (L.eta :))) L'.C.eta := by rw [hCeta]; exact (by with_unfolding_all exact (hl.is.eta :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ hl.is'.eta h1
  have hxi : ∀ t, L'.xi t = (by with_unfolding_all exact ((L.xi (ι t)) :)) := fun t => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.xi (ι t)) :))) (L'.xiH t) := by rw [hxiH t]; exact (by with_unfolding_all exact ((hl.is.xi (ι t)) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.xi t) h1

  have thImp : ∀ ψ S T f, @IsThetaFunO DX ψ S T f → @IsThetaFunO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thImp' : ∀ ψ S T f, @IsThetaFunO DX' ψ S T f → @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thEq : @IsThetaFunO DX' = fun ψ S T f => @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := by
    funext ψ S T f
    exact propext ⟨fun h => (by with_unfolding_all exact ((thImp' _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((thImp _ _ _ _ h) :))⟩
  have wImp : ∀ ψ S T x1 x2 ω, @IsWeilDatumO DX ψ S T x1 x2 ω →
      @IsWeilDatumO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (ω :))) := fun ψ S T x1 x2 ω h =>
    { std := (by with_unfolding_all exact (h.std :))
      hecS := (by with_unfolding_all exact (h.hecS :))
      hecT := (by with_unfolding_all exact (h.hecT :))
      resS := (by with_unfolding_all exact (h.resS :))
      resT := (by with_unfolding_all exact (h.resT :))
      om_pres := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_pres :))
      om_heis := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_heis :))
      om_aut := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_aut :))
      om_cont := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_cont :))
      om_unit := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_unit :))
      om_split := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_split :)) }
  have vacImp : ∀ ψ θ S T sS sT LS LT f, @IsVacO DX ψ θ S T sS sT LS LT f →
      @IsVacO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (θ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (sS :))) ((by with_unfolding_all exact (sT :))) ((by with_unfolding_all exact (LS :))) ((by with_unfolding_all exact (LT :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ θ S T sS sT LS LT f h => by
      unfold IsVacO
      rewrite [thEq]
      exact ⟨(by with_unfolding_all exact (h.1 :)), (by with_unfolding_all exact (h.2.inf :)), (by with_unfolding_all exact (h.2.theta :)), (by with_unfolding_all exact (h.2.lat :)), (by with_unfolding_all exact (h.2.fock :)), (by with_unfolding_all exact (h.2.norm :))⟩
  have pmImp : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX' m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmImp' : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX' m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmEq : @IsPlaceModel DX' = fun m n ψ B hs e Λ c f₀ T =>
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) := by
    funext m n ψ B hs e Λ c f₀ T
    exact propext ⟨fun h => (by with_unfolding_all exact ((pmImp' _ _ _ _ _ _ _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((pmImp _ _ _ _ _ _ _ _ _ _ h) :))⟩
  intro i j
  obtain ⟨A, A', WW, Y, hb, hsum⟩ := hB i j
  have hmu : ∀ t, L'.mu t (↑j + 1) = (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1)) :)) := fun t => by
    show L'.mu0 (↑j + 1) * L'.xi t = _
    rw [hmu0 j, hxi t]
    exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1))) :))
  have hnu : ∀ t, SqNum.nuH G' t i j = (by with_unfolding_all exact ((SqNum.nuH G (ι t) i j) :)) := fun t => by
    show L'.C.mu0 j * L'.xiH t / G'.ch.chiH (DX'.R.m - ↑i) = _
    rw [hCmu j, hxiH t, hchiH]
    exact (by with_unfolding_all exact ((Eq.refl (SqNum.nuH G (ι t) i j)) :))
  have hloc : ∀ t, locPl G' t = (by with_unfolding_all exact ((locPl G (ι t)) :)) := fun t => by
    unfold locPl GlobalTheory.ChiGrid.Places.W0 GlobalTheory.ChiGrid.Places.S0
    rw [hQ t, hv0, hwp]
    exact (by with_unfolding_all exact ((Eq.refl (locPl G (ι t))) :))
  refine ⟨A, A', WW,
    ⟨⟨(by with_unfolding_all exact (Y.rA.Λ :)), (by with_unfolding_all exact (Y.rA.β :)), (by with_unfolding_all exact (Y.rA.s :)), (by with_unfolding_all exact (Y.rA.B :))⟩, ⟨(by with_unfolding_all exact (Y.rA'.Λ :)), (by with_unfolding_all exact (Y.rA'.β :)), (by with_unfolding_all exact (Y.rA'.s :)), (by with_unfolding_all exact (Y.rA'.B :))⟩,
      ⟨(by with_unfolding_all exact (Y.rW.Λ :)), (by with_unfolding_all exact (Y.rW.β :)), (by with_unfolding_all exact (Y.rW.s :)), (by with_unfolding_all exact (Y.rW.B :))⟩, fun t => (by with_unfolding_all exact ((Y.ω (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.ω' (ι t)) :)), (by with_unfolding_all exact (Y.vac :)),
      (by with_unfolding_all exact (Y.vac' :)), fun t => (by with_unfolding_all exact ((Y.e (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.c (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f' (ι t)) :)),
      (by with_unfolding_all exact (Y.m :)), (by with_unfolding_all exact (Y.fd :)), (by with_unfolding_all exact (Y.m' :)), (by with_unfolding_all exact (Y.fd' :))⟩, ⟨(by with_unfolding_all exact (hb.rank :)), (by with_unfolding_all exact (hb.rank' :)), (by with_unfolding_all exact (hb.std :)), (by with_unfolding_all exact (hb.std' :)), (by with_unfolding_all exact (hb.stdW :)), ?_⟩, ?_⟩
  · have e3 : ∀ t, L'.mu t (↑j + 1) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2)) :)) := fun t => by
      rw [hmu t, heta]
      exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2))) :))
    have e4 : ∀ _ : T', G'.ch.chi (DX'.R.m - ↑i) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2)) :)) := fun _ => by
      rw [hchi, heta]
      exact (by with_unfolding_all exact ((Eq.refl (G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2))) :))
    refine triIs_congr ?_ hψ hθ e3 e4 hnu hloc
    exact ⟨(by with_unfolding_all exact (hb.is.rank :)), (by with_unfolding_all exact (hb.is.rigA :)), (by with_unfolding_all exact (hb.is.rigA' :)), (by with_unfolding_all exact (hb.is.rigW :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil (ι t))) :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil' (ι t))) :)),
      (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac) :)), (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac') :)),
      fun t => (by with_unfolding_all exact ((hb.is.idem (ι t)) :)), fun t => (by with_unfolding_all exact ((hb.is.expo (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.fst (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.snd (ι t)) :)),
      (by with_unfolding_all exact (hb.is.meas :)), (by with_unfolding_all exact (hb.is.meas' :))⟩
  · obtain ⟨Ω, Ω', h0, h0', H⟩ := hsum
    refine ⟨Ω, Ω', h0, h0', fun t h hh => ?_⟩
    rw [hψ, hθ]
    have H3 := H (ι t) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (hh :)))
    exact (by with_unfolding_all exact (H3 :))

end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotent
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblNab

open Matrix

section Generic

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def blkN (N : Matrix ι ι A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A := fromBlocks (1 + N) N (-N) (1 - N)

theorem blkN_mul_neg (N : Matrix ι ι A) : blkN N * blkN (-N) = 1 := by
  rw [blkN, blkN, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> noncomm_ring

theorem neg_mul_blkN (N : Matrix ι ι A) : blkN (-N) * blkN N = 1 := by
  have h := blkN_mul_neg (-N)
  rwa [neg_neg] at h

theorem blkN_eq (N : Matrix ι ι A) :
    1 + (fromRows (1 : Matrix ι ι A) (-1) * N) * (fromRows (1 : Matrix ι ι A) 1)ᵀ = blkN N := by
  rw [fromRows_mul, transpose_fromRows, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_add, blkN]
  simp [sub_eq_add_neg]

-- Select matrix multiplication explicitly to avoid the `CStarMatrix` default instance.
local infixl:70 " ⬝ₘ " => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem blkN_anti (N : Matrix ι ι A) : blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) (-1) = fromRows 1 (-1) := by
  rw [blkN, fromBlocks_mul_fromRows]
  congr 1 <;> noncomm_ring

theorem blkN_diag (N : Matrix ι ι A) :
    blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) 1 = fromRows 1 1 + fromRows (1 : Matrix ι ι A) (-1) ⬝ₘ (N + N) := by
  rw [blkN, fromBlocks_mul_fromRows, fromRows_mul]
  ext (i | i) j <;> simp <;> ring

theorem blkN_unitary (s : A →+* A) (J N : Matrix ι ι A) (h : Nᵀ * J + J * N.map s = 0) :
    (blkN N)ᵀ * dbl J * (blkN N).map s = dbl J := by
  have h1 : (1 + N).map s = 1 + N.map s := by
    rw [Matrix.map_add _ (map_add s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h2 : (1 - N).map s = 1 - N.map s := by
    rw [Matrix.map_sub _ (map_sub s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h3 : (-N).map s = - N.map s := by ext i j; simp
  rw [blkN, fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3,
    transpose_add, transpose_sub, transpose_neg, transpose_one]
  generalize Nᵀ = P at h ⊢
  generalize N.map s = Q at h ⊢
  congr 1
  · calc _ = J + (P * J + J * Q) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = -J + (P * J + J * Q) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem skew_block (s : A →+* A) (J K K' : Matrix ι ι A) (a c : A) (ha : s a = a) (hc : s c = -c)
    (hKK : K * K' = 1) (hKK' : K' * K = 1) (hK : Kᵀ * J * K.map s = J) (hK' : K'ᵀ * J * K'.map s = J) :
    (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1)))ᵀ * J +
      J * (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s = 0 := by
  have e1 : J * K.map s = K'ᵀ * J := by
    calc J * K.map s = (K * K')ᵀ * J * K.map s := by rw [hKK, transpose_one, Matrix.one_mul]
      _ = K'ᵀ * (Kᵀ * J * K.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK]
  have e2 : J * K'.map s = Kᵀ * J := by
    calc J * K'.map s = (K' * K)ᵀ * J * K'.map s := by rw [hKK', transpose_one, Matrix.one_mul]
      _ = Kᵀ * (K'ᵀ * J * K'.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK']
  have e3 : (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s =
      a • ((1 + c) • (K.map s - 1) - (1 - c) • (K'.map s - 1)) := by
    ext i j
    have h1 : s ((1 : Matrix ι ι A) i j) = (1 : Matrix ι ι A) i j :=
      congrFun (congrFun (Matrix.map_one s (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub, map_add (f := _), map_one,
      ha, hc, h1]
    ring
  rw [e3]
  simp only [transpose_smul, transpose_sub, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
  rw [← smul_add]
  simp

theorem blkN_mulVec_inl (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inr i)) := by
  rw [blkN, fromBlocks_mulVec, add_mulVec, one_mulVec]
  rfl

theorem blkN_mulVec_inr (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inr i)) =
      -(N *ᵥ (fun i => z (Sum.inl i))) + ((fun i => z (Sum.inr i)) - N *ᵥ (fun i => z (Sum.inr i))) := by
  rw [blkN, fromBlocks_mulVec, sub_mulVec, one_mulVec, neg_mulVec]
  rfl

theorem blkN_sub_one (N : Matrix ι ι A) : blkN N - 1 = fromBlocks N N (-N) (-N) := by
  ext (i | i) (j | j) <;> simp [blkN, Matrix.one_apply]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mem_latAt_of_int {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {x : AF F}
    (hx : evFin F v x ∈ v.adicCompletionIntegers F) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : x • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨x * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hx hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem evFin_invTwo_mem (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

theorem half_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.SplitDblGen.half : AE F E) • y ∈ GlobalTheory.InertSph.latAt W v := by
  rw [GlobalTheory.SplitDblGen.half, algebraMap_smul]
  exact smul_mem_latAt_of_int W v (evFin_invTwo_mem v h2) hy

theorem nMat_mem_NabD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ n ∈ GlobalTheory.InertDbl.NabD σ W v,
      GlobalTheory.InertDbl.matD n = GlobalTheory.SplitDblGen.nMat c (mat k) (mat k⁻¹) := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hcL k hk
  set N := GlobalTheory.SplitDblGen.splitDoublingNBlock c (mat k) (mat k⁻¹) with hN
  have hKK : mat k * mat k⁻¹ = 1 := congrArg Units.val (mul_inv_cancel (k : GL (Fin d) (AE F E)))
  have hKK' : mat k⁻¹ * mat k = 1 := congrArg Units.val (inv_mul_cancel (k : GL (Fin d) (AE F E)))
  have hhalf : (cA σ) (GlobalTheory.SplitDblGen.half : AE F E) = GlobalTheory.SplitDblGen.half := (cA σ).commutes _
  have hsk : Nᵀ * incM F W.J + incM F W.J * N.map (cA σ : AE F E →+* AE F E) = 0 :=
    skew_block (cA σ : AE F E →+* AE F E) (incM F W.J) (mat k) (mat k⁻¹) _ c
      (by simp only [RingHom.coe_coe, map_mul, hhalf]) hc hKK hKK' k.2 (k⁻¹).2
  have hNL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, N *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    have a1 : (mat k - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).1 hz
    have a2 : (mat k⁻¹ - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).2 hz
    rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_mulVec, mul_smul, mul_smul, sub_mulVec, smul_mulVec, smul_mulVec, sub_smul,
      add_smul, one_smul, one_smul]
    exact half_smul_mem W v h2 (half_smul_mem W v h2 (half_smul_mem W v h2
      (sub_mem (sub_mem a1 (hcL _ a1)) (add_mem a2 (hcL _ a2)))))
  have hblk : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertDbl.latAtD W v, blkN M *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
    intro M hM z hz
    refine ⟨?_, ?_⟩
    · rw [blkN_mulVec_inl]; exact add_mem (add_mem hz.1 (hM _ hz.1)) (hM _ hz.2)
    · rw [blkN_mulVec_inr]; exact add_mem (neg_mem (hM _ hz.1)) (sub_mem hz.2 (hM _ hz.2))
  refine ⟨⟨⟨blkN N, blkN (-N), blkN_mul_neg N, neg_mul_blkN N⟩,
    blkN_unitary (cA σ : AE F E →+* AE F E) _ N hsk⟩, ⟨⟨fun u hu => ?_, fun z hz => ⟨hblk N hNL z hz, ?_⟩⟩,
      blkN_anti N, N + N, blkN_diag N⟩, (blkN_eq N).symm⟩
  · have b1 : u • (mat k - 1) = 0 := hk.1 u hu
    have b2 : u • (mat k⁻¹ - 1) = 0 := by
      have e1 : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
        rw [Matrix.mul_sub, hKK', Matrix.mul_one, neg_sub]
      rw [e1, smul_neg, ← Matrix.mul_smul, b1, Matrix.mul_zero, neg_zero]
    have b3 : u • N = 0 := by
      rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_comm u, smul_sub u, smul_comm u, smul_comm u (1 + c), b1, b2, smul_zero,
        smul_zero, sub_zero, smul_zero]
    show u • (blkN N - 1) = 0
    rw [blkN_sub_one, fromBlocks_smul, smul_neg, b3, neg_zero, fromBlocks_zero]
  · exact hblk (-N) (fun y hy => by rw [neg_mulVec]; exact neg_mem (hNL y hy)) z hz

end GlobalTheory.SplitDblNab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotentStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ n ∈ GlobalTheory.InertDbl.NabD σ W v,
      GlobalTheory.InertDbl.matD n = GlobalTheory.SplitDblGen.nMat c (mat k) (mat k⁻¹) := by
  first | exact @GlobalTheory.SplitDblNab.nMat_mem_NabD | exact GlobalTheory.SplitDblNab.nMat_mem_NabD | (intros; apply GlobalTheory.SplitDblNab.nMat_mem_NabD <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * y i) ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {u : Fin T₀.rank → AE D} (hu : u ∈ latV T₀ L₀ (· = v)) :
    d.j0 *ᵥ u ∈ latV T L (· = v) := by
  refine (hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h0 : (d.pX *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jX i ((d.pX *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · have h0 : (d.pY *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jY i ((d.pY *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec]; exact hu

theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin T₀.rank → AE D} (hz : z ∈ latA T₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA T L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin T₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV T₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.j0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.j0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact smul_mem_latA ha (wittCoreInclusion_mem_latticeCompletionAtPlace d hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

theorem wittExt_wittInc_mem_completed_hom_lattice {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
    {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T₀}
    (hw : w ∈ latO S₀ T₀ (LS₀ : Set _) (LT₀ : Set _) (· = v)) :
    dS.ext0 T (dT.inc0 S₀ w) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · change (dT.j0 * w * dS.p0) *ᵥ y ∈ latA T LT (· = v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

theorem wittExt_wittInc_isHalf {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {e : AE D}
    {w : WO S₀ T₀} (hw : IsHalf e w) : IsHalf e (dS.ext0 T (dT.inc0 S₀ w)) := by
  intro i j
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hw k l]
  ring

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

theorem flat_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf
  obtain ⟨hθ, h2, hh⟩ := hf
  have hmem : ∀ w ∈ latO B.V₀ J.W₀ (LV₀ : Set _) (LW₀ : Set _) (· = v),
      B.d.ext0 J.W (J.d.inc0 B.V₀ w) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) := fun w hw =>
    wittExt_wittInc_mem_completed_hom_lattice B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hw
  refine ⟨h𝔉.Heisenberg₂.theta f hθ, fun w hw => ?_, fun e he w hw hwe => ?_⟩
  · have hx : MxAt (· = v) (2 • w) := fun i j => by
      rw [Matrix.smul_apply]
      exact nsmul_mem (GlobalTheory.FinPl.LatMem.latO_mxAt hw i j) 2
    rw [← h𝔉.Heisenberg₂.core f hθ (2 • w) hx, map_nsmul, map_nsmul, h2 _ (hmem w hw)]
  · rw [← h𝔉.Heisenberg₂.core f hθ w (GlobalTheory.FinPl.LatMem.latO_mxAt hw),
      hh e he _ (hmem w hw) (wittExt_wittInc_isHalf B.d J.d hwe)]

end GlobalTheory.FinPl.VacFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  first | exact @GlobalTheory.FinPl.VacFlat.flat_vac | exact GlobalTheory.FinPl.VacFlat.flat_vac | (intros; apply GlobalTheory.FinPl.VacFlat.flat_vac <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
noncomputable section
namespace GlobalTheory.GLGen
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

theorem single_neg' (x y : Fin n) (a : R) : single x y (-a) = -single x y a := by
  ext p q; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp

theorem diag_transv_diag (a b : Fin n → R) (hab : ∀ k, a k * b k = 1) {i j : Fin n} (hij : i ≠ j) (c : R) :
    diagonal a * transvection i j c * diagonal b = transvection i j (a i * c * b j) := by
  have h1 : diagonal a * diagonal b = (1 : Matrix (Fin n) (Fin n) R) := by
    rw [diagonal_mul_diagonal]; simp [hab]
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  congr 1
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h <;> simp_all

theorem w_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-((u⁻¹ : Rˣ) : R)) * transvection i j (u : R) =
      1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1 := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, z1, z2, z3, z4]
  simp only [mul_neg, neg_mul, Units.mul_inv, Units.inv_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, single_neg', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]
  abel

theorem ww_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    (1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) *
      (1 + single i j ((-1 : Rˣ) : R) + single j i (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) =
      diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1) := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, z1, z2, z3, z4]
  clear z1 z2 z3 z4
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hji : j ≠ i := Ne.symm hij
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi; simp [hij, hji]
    · by_cases hpj : p = j
      · subst hpj; simp [hij, hji]
      · simp [hpi, hpj, Ne.symm hpi, Ne.symm hpj]
  · by_cases hpi : p = i <;> by_cases hqi : q = i <;> by_cases hpj : p = j <;> by_cases hqj : q = j <;>
      simp_all [eq_comm]

def diagU (u : Fin n → Rˣ) : GL (Fin n) R :=
  ⟨diagonal (fun k => (u k : R)), diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem diagU_val (u : Fin n → Rˣ) : ((diagU u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (u k : R)) := rfl

theorem diagU_inv_val (u : Fin n → Rˣ) :
    (((diagU u)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)) := rfl

theorem diagU_mul (u v : Fin n → Rˣ) : diagU (u * v) = diagU u * diagU v := by
  ext : 1
  simp only [Units.val_mul, diagU_val, diagonal_mul_diagonal, Pi.mul_apply]

theorem diagU_one : diagU (1 : Fin n → Rˣ) = 1 := by
  ext : 1
  simp [diagU_val]

def transvGL {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]⟩

def transvSet (R : Type) [CommRing R] (n : ℕ) : Set (GL (Fin n) R) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin n) (Fin n) R) = transvection i j c}

def elem (R : Type) [CommRing R] (n : ℕ) : Subgroup (GL (Fin n) R) := Subgroup.closure (transvSet R n)

theorem transvGL_mem {i j : Fin n} (hij : i ≠ j) (c : R) : transvGL hij c ∈ elem R n :=
  Subgroup.subset_closure ⟨i, j, c, hij, rfl⟩

theorem conj_mem (u : Fin n → Rˣ) {e : GL (Fin n) R} (he : e ∈ elem R n) :
    diagU u * e * (diagU u)⁻¹ ∈ elem R n := by
  have hle : elem R n ≤ (elem R n).comap (MulAut.conj (diagU u)).toMonoidHom := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨i, j, (u i : R) * c * ((u j)⁻¹ : Rˣ), hij, ?_⟩
    rw [Units.val_mul, Units.val_mul, hg, diagU_val, diagU_inv_val]
    exact diag_transv_diag _ _ (fun k => Units.mul_inv (u k)) hij c
  simpa using hle he

theorem whitehead_mem {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) ∈ elem R n := by
  have e : diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) =
      transvGL hij (u : R) * transvGL hij.symm (-((u⁻¹ : Rˣ) : R)) * transvGL hij (u : R) *
      (transvGL hij ((-1 : Rˣ) : R) * transvGL hij.symm (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) *
        transvGL hij ((-1 : Rˣ) : R)) := by
    ext : 1
    simp only [Units.val_mul, transvGL, diagU_val]
    rw [w_eq hij u, w_eq hij (-1), ww_eq hij u]
    congr 1
    funext k
    split_ifs <;> rfl
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) <;> exact transvGL_mem _ _

theorem diagU_inv (u : Fin n → Rˣ) : diagU u⁻¹ = (diagU u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagU_mul, inv_mul_cancel, diagU_one])

def diagHomU : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun := diagU
  map_one' := diagU_one
  map_mul' := diagU_mul

theorem pair_mem_elem (i j : Fin n) (a : Rˣ) :
    diagU (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) ∈ elem R n := by
  by_cases hij : i = j
  · subst hij
    have : (Pi.mulSingle i a * Pi.mulSingle i a⁻¹ : Fin n → Rˣ) = 1 := by
      rw [← Pi.mulSingle_mul]; simp
    rw [this, diagU_one]
    exact one_mem _
  · have hji : j ≠ i := fun h => hij h.symm
    have : (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) =
        fun k => if k = i then a else if k = j then a⁻¹ else 1 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    rw [this]
    exact whitehead_mem hij a

theorem diag_mem_of_prod (u : Fin n → Rˣ) (hu : ∏ k, u k = 1) : diagU u ∈ elem R n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : diagU u = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
    exact one_mem _
  · let j : Fin n := ⟨0, hpos⟩
    have key : u = ∏ k, (Pi.mulSingle k (u k) * Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ) := by
      rw [Finset.prod_mul_distrib, Finset.univ_prod_mulSingle]
      have : (∏ k, (Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)) = 1 := by
        have h := map_prod (MonoidHom.mulSingle (fun _ : Fin n => Rˣ) j) (fun k => (u k)⁻¹)
          Finset.univ
        rw [Finset.prod_inv_distrib, hu, inv_one, map_one] at h
        exact h.symm
      rw [this, mul_one]
    have : u ∈ (elem R n).comap (diagHomU (R := R) (n := n)) := by
      rw [key]
      exact Subgroup.prod_mem _ (fun k _ => pair_mem_elem k j (u k))
    exact this

theorem det_eq_one_of_mem {e : GL (Fin n) R} (he : e ∈ elem R n) : GeneralLinearGroup.det e = 1 := by
  have hle : elem R n ≤ (GeneralLinearGroup.det : GL (Fin n) R →* Rˣ).ker := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ hij]
    rfl
  exact hle he

theorem mem_of_det_eq_one : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) →
    ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R),
      u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  intro R _ hsr n H hH a ha
  have hEH : elem R n ≤ H := Subgroup.closure_le _ |>.2 (by
    rintro g ⟨i, j, c, hij, hg⟩; exact hH i j hij c g hg)
  have hSR : PI.VolSemiDirect.W.Cj.HasStableRangeOne R := fun a b x y h =>
    hsr a b ⟨x, y, by rw [← h]; ring⟩
  have hmem := PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag R hSR n a
  have key : ∀ g ∈ Subgroup.closure ({g : GL (Fin n) R | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin n → R, (g : Matrix (Fin n) (Fin n) R) = Matrix.diagonal d}),
      ∃ u : Fin n → Rˣ, g * diagU u ∈ elem R n := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨i, j, c, hij, hg⟩ | ⟨d, hd⟩
      · exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.subset_closure ⟨i, j, c, hij, hg⟩⟩
      · have hu : ∀ k, IsUnit (d k) := fun k => by
          have h : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          have h' := congrFun (congrFun h k) k
          rw [hd, Matrix.mul_diagonal, one_apply_eq] at h'
          exact ⟨⟨d k, _, by rw [mul_comm]; exact h', h'⟩, rfl⟩
        refine ⟨fun k => (hu k).unit⁻¹, ?_⟩
        have e : g * diagU (fun k => (hu k).unit⁻¹) = 1 := by
          ext : 1
          rw [Units.val_mul, hd, diagU_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
          congr 1
          funext k
          exact (hu k).mul_val_inv
        rw [e]; exact Subgroup.one_mem _
    | one => exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨v * u, ?_⟩
      have h := Subgroup.mul_mem _ hu (conj_mem u⁻¹ hv)
      rw [diagU_inv, inv_inv] at h
      convert h using 1
      rw [diagU_mul]
      group
    | inv x _ hx =>
      obtain ⟨u, hu⟩ := hx
      refine ⟨u⁻¹, ?_⟩
      have h := conj_mem u (Subgroup.inv_mem _ hu)
      rw [diagU_inv]
      convert h using 1
      group
  obtain ⟨u, hu⟩ := key a hmem
  have h1 := det_eq_one_of_mem hu
  rw [map_mul, ha, one_mul] at h1
  have hprod : ∏ k, u k = 1 := by
    have h2 := congrArg Units.val h1
    rw [GeneralLinearGroup.val_det_apply, diagU_val, det_diagonal] at h2
    ext
    rw [Units.coe_prod]
    simpa using h2
  have hd := diag_mem_of_prod u hprod
  have e : a = (a * diagU u) * (diagU u)⁻¹ := by group
  rw [e]
  exact hEH (Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hd))

end GlobalTheory.GLGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvectionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_linear_generated_by_transvections : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) → ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R), u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  first | exact @GlobalTheory.GLGen.mem_of_det_eq_one | exact GlobalTheory.GLGen.mem_of_det_eq_one | (intros; apply GlobalTheory.GLGen.mem_of_det_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf

theorem vol_fund_lt_top {D : D7} {V : HSp D} (hc : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨_, _, _, _, _, _, hΓc⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  obtain ⟨K, hKc, hKcov⟩ := hc
  have hcover : v.𝓕 ⊆ ⋃ g : GQ V, (g • K) := by
    intro h _
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
    simp [Subgroup.smul_def]
  have hle : v.μ v.𝓕 ≤ v.μ K := by
    calc v.μ v.𝓕 = v.μ ((⋃ g : GQ V, (g • K)) ∩ v.𝓕) := by rw [Set.inter_eq_right.2 hcover]
      _ = v.μ (⋃ g : GQ V, (g • K ∩ v.𝓕)) := by rw [Set.iUnion_inter]
      _ ≤ ∑' g : GQ V, v.μ (g • K ∩ v.𝓕) := measure_iUnion_le _
      _ = v.μ K := (v.fund.measure_eq_tsum K).symm
  exact hle.trans_lt hKc.measure_lt_top

theorem jac_bound (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) (h : GA D J.W) :
    ∃ C, ∀ (n : flagN J.d) (h' : GA D J.W₀), ‖K (n.1 * J.d.emb0 h' * h)‖ ≤ C := by
  have hcont := J.d.continuous_embed
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  obtain ⟨⟨Kn, hKn, hcov⟩, -⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)
  obtain ⟨K₀, hK₀, hcov₀⟩ := J.cpt
  obtain ⟨-, -, -, -, htop, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  let f : flagN J.d × GA D J.W₀ → GA D J.W := fun p => p.1.1 * J.d.emb0 p.2 * h
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).mul (hcont.comp continuous_snd)).mul continuous_const
  have hS : IsCompact (f '' (Kn ×ˢ K₀)) := (hKn.prod hK₀).image hf
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hK.continuousOn
  refine ⟨C, fun n h' => ?_⟩
  obtain ⟨γ₀, hγ₀, hk₀⟩ := hcov₀ h'
  have hemb : J.d.emb0 γ₀ ∈ GQ J.W := J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ₀
  let n' : flagN J.d := ⟨J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹, hnorm n.1 n.2 γ₀⟩
  obtain ⟨γ, hγ, k, hk, hn'⟩ := hcov n'
  have hδ : (J.d.emb0 γ₀)⁻¹ * γ.1 ∈ GQ J.W ⊓ jacGrp J.d :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hemb) (Subgroup.mem_subgroupOf.1 hγ),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨γ₀, rfl⟩)))
        (Subgroup.mem_sup_left γ.2)⟩
  have h1 : γ.1 * k.1 = J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹ := (congrArg Subtype.val hn').symm
  have heq : n.1 * J.d.emb0 h' * h = ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * J.d.emb0 (γ₀ * h') * h) := by
    rw [map_mul, show ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * (J.d.emb0 γ₀ * J.d.emb0 h') * h) =
      (J.d.emb0 γ₀)⁻¹ * (γ.1 * k.1) * J.d.emb0 γ₀ * J.d.emb0 h' * h by simp only [mul_assoc], h1]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [heq, hinv _ hδ]
  exact hC _ ⟨(k, γ₀ * h'), ⟨hk, hk₀⟩, rfl⟩

theorem jac_absConv : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
    (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h,
      AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  intro D ρ J K hK hinv h
  obtain ⟨C, hC⟩ := jac_bound D ρ J K hK hinv h
  have hcont := J.d.continuous_embed
  obtain ⟨-, h2W, -, hbW, htW, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨-, h20, -, hb0, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  have hμ : J.v0.μ J.v0.𝓕 < ⊤ := vol_fund_lt_top J.cpt J.v0
  have hν : J.vN.ν J.vN.𝓝 < ⊤ := by rw [J.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hμ.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  unfold AbsConv
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hC p.2 p.1)
  exact (hK.comp (((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul
    continuous_const)).aestronglyMeasurable

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_invariant_function_integrable : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K → (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  first | exact @GlobalTheory.Unf.jac_absConv | exact GlobalTheory.Unf.jac_absConv | (intros; apply GlobalTheory.Unf.jac_absConv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.JacMeas

open GlobalTheory.SemiHaar

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def lv : UX D ρ →* GA D S := d.levi.comp (UX D ρ).subtype

theorem lv_mem (u : UX D ρ) : lv d u ∈ flagN d := d.levi_mem_NFlag u.2

theorem radX_le : radX d ≤ flagN d := inf_le_left

theorem lv_conj (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : lv d u * n * (lv d u)⁻¹ ∈ radX d := by
  refine ⟨(flagN d).mul_mem ((flagN d).mul_mem (lv_mem d u) hn.1) ((flagN d).inv_mem (lv_mem d u)), ?_⟩
  change mt S (d.levi u.1 * n * (d.levi u.1)⁻¹) ⬝ d.jX = d.jX
  rw [← map_inv, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n),
    mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem anisotropicEmbedding_conj_wittFlagUnipotentFixer (n : GA D S) (hn : n ∈ radX d) (h : GA D S₀) : d.emb0 h * n * (d.emb0 h)⁻¹ ∈ radX d :=
  ⟨(flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n hn.1 h,
    (stabX d).mul_mem ((stabX d).mul_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h) hn.2) ((stabX d).inv_mem (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d h))⟩

theorem radX_sup_lv : radX d ⊔ (lv d).range = flagN d := by
  refine le_antisymm (sup_le (radX_le d) (by rintro _ ⟨u, rfl⟩; exact lv_mem d u)) fun n hn => ?_
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  exact mul_mem (Subgroup.mem_sup_right ⟨⟨u, hu⟩, rfl⟩)
    (Subgroup.mem_sup_left (mul_mem (nB_mem_radX d b) (nC_mem_radX d c)))

theorem wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer : radX d ⊔ d.emb0.range = stabX d := by
  refine le_antisymm (sup_le (radX_le_stabX d) (by rintro _ ⟨u, rfl⟩; exact wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic d u)) fun g hg => ?_
  obtain ⟨n, hn, h, rfl⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 g).1 hg
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem blockX_mul_lv {n : GA D S} (hn : n ∈ radX d) (u : UX D ρ) : blockX d (n * lv d u) = u.1.1 := by
  change d.pX ⬝ (mt S (n * d.levi u.1) ⬝ d.jX) = _
  rw [mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc (mt S n), mem_fixer.1 hn.2, ← Matrix.mul_assoc, d.pX_jX,
    Matrix.one_mul]

theorem exists_rad_lv {n : GA D S} (hn : n ∈ flagN d) : ∃ n₀ ∈ radX d, ∃ u, n = n₀ * lv d u :=
  exists_mul_of_mem_sup_range (radX d) (lv d) (lv_conj d) (by rw [radX_sup_lv]; exact hn)

theorem continuous_blockX : Continuous (blockX d) :=
  continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)

theorem isClosed_stabX : IsClosed (stabX d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  exact isClosed_eq ((continuous_mt S).matrix_mul continuous_const) continuous_const

theorem isClosed_flagN : IsClosed (flagN d : Set (GA D S)) := by
  haveI := (lattice_Mx D S.rank ρ).2.2.2.1
  haveI := (lattice_Mx D S₀.rank S₀.rank).2.2.2.1
  have e : (flagN d : Set (GA D S)) = (blockX d ⁻¹' GlobalTheory.UnitU.uniSet D ρ) ∩
      ({g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g} ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) = 1}) := by
    ext g
    constructor
    · intro hg
      refine ⟨?_, ?_, (GlobalTheory.JacProj.flag_le d hg).2⟩
      · obtain ⟨n, hn, u, rfl⟩ := exists_rad_lv d hg
        rw [Set.mem_preimage, blockX_mul_lv d hn]
        exact u.2
      · exact GlobalTheory.JacProj.keeps_jX d (GlobalTheory.JacProj.flag_le d hg).1
    · rintro ⟨h1, h2, h3⟩
      let u : UX D ρ := ⟨GlobalTheory.UnitU.toUnit _ h1, h1⟩
      have hs : (lv d u)⁻¹ * g ∈ stabX d := by
        change mt S ((lv d u)⁻¹ * g) ⬝ d.jX = d.jX
        have h4 : mt S g ⬝ d.jX = mt S (lv d u) ⬝ d.jX := (show _ = _ from h2).trans (d.levi_jX u.1).symm
        rw [mt_mul, Matrix.mul_assoc, h4, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
      obtain ⟨n, hn, h, he⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hs
      have hg : g = lv d u * n * d.emb0 h := by rw [mul_assoc, ← he, mul_inv_cancel_left]
      have hn' : lv d u * n ∈ flagN d := mul_mem (lv_mem d u) hn.1
      have h5 := GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn' h
      rw [← hg, show d.p0 ⬝ (mt S g ⬝ d.j0) = 1 from h3] at h5
      have h6 : h = 1 := mt_injective S₀ (h5.symm.trans (mt_one S₀).symm)
      rw [hg, h6, map_one, mul_one]
      exact hn'
  rw [e]
  exact ((GlobalTheory.UnitU.isClosed_uniSet D ρ).preimage (continuous_blockX d)).inter
    ((isClosed_eq ((continuous_mt S).matrix_mul continuous_const) (continuous_const.matrix_mul (continuous_blockX d))).inter
      (isClosed_eq (continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)) continuous_const))

theorem isClosed_radX : IsClosed (radX d : Set (GA D S)) := (isClosed_flagN d).inter (isClosed_stabX d)

theorem exists_proj_lv : ∃ p : flagN d → UX D ρ, Continuous p ∧
    ∀ (u : UX D ρ) (n : radX d) (hm : n.1 * lv d u ∈ flagN d), p ⟨n.1 * lv d u, hm⟩ = u := by
  choose n₀ hn₀ p hp using fun g : flagN d => exists_rad_lv d g.2
  have hb : ∀ g, (p g).1.1 = blockX d g.1 := fun g => by rw [hp g, blockX_mul_lv d (hn₀ g)]
  refine ⟨p, (GlobalTheory.UnitU.isClosedEmbedding_val D ρ).isInducing.continuous_iff.2 ?_, fun u n hm => ?_⟩
  · exact ((continuous_blockX d).comp continuous_subtype_val).congr fun g => (hb g).symm
  · exact Subtype.ext (Units.ext ((hb _).trans (blockX_mul_lv d n.2 u)))

theorem rat_lv (n : GA D S) (hn : n ∈ radX d) (u : UX D ρ) : n * lv d u ∈ GQ S ↔ n ∈ GQ S ∧ u ∈ UXQ D ρ := by
  have hb : ∀ g ∈ GQ S, blockX d g ∈ ratMx D ρ ρ := fun g hg =>
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S g).1 hg) (rat_mem _))
  refine ⟨fun h => ?_, fun h => mul_mem h.1 (d.levi_mem_GQ h.2.1 h.2.2)⟩
  have h1 := hb _ h
  have h2 := hb _ (inv_mem h)
  rw [show (n * lv d u)⁻¹ = (lv d u⁻¹ * n⁻¹ * (lv d u⁻¹)⁻¹) * lv d u⁻¹ by simp,
    blockX_mul_lv d (lv_conj d _ (inv_mem hn) _)] at h2
  rw [blockX_mul_lv d hn] at h1
  refine ⟨?_, h1, h2⟩
  rw [show n = n * lv d u * (lv d u)⁻¹ by simp]
  exact mul_mem h (inv_mem (d.levi_mem_GQ h1 h2))

theorem jac_measure : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  intro D ρ J vU ν₀ 𝓝₀ hν₀ h𝓝₀ h𝓝₀1
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have k4 := (GlobalTheory.UnitU.rational D ρ).1
  have k5 : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨hU, 𝓤, h𝓤, h𝓤1⟩ := vU.unit
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hle : radX J.d ⊔ J.d.emb0.range ≤ flagN J.d ⊔ J.d.emb0.range := sup_le_sup_right (radX_le J.d) _
  have H0 := semiMeas_haar_inv (radX J.d) J.d.emb0 (isClosed_radX J.d) J.d.continuous_embed (anisotropicEmbedding_conj_wittFlagUnipotentFixer J.d)
    ⟨fun g => p (Subgroup.inclusion hle g), hpc.comp (continuous_inclusion hle), fun h n => hp h ⟨n.1, n.2.1⟩⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund ν₀ h𝓝₀
    (by rw [h𝓝₀1]; exact ENNReal.one_ne_top)
  have H1 := semiMeas_haar_inv (flagN J.d) J.d.emb0 (isClosed_flagN J.d) J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  refine ⟨by rw [wittFlagUnipotentFixer_sup_anisotropic_eq_stabilizer]; exact isClosed_stabX J.d, H0.1, H0.2, H1.2, fun F hF => ?_⟩
  have l1 : LocallyCompactSpace (radX J.d) := (isClosed_radX J.d).locallyCompactSpace
  have l2 : SecondCountableTopology (radX J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have l3 : LocallyCompactSpace (flagN J.d) := (isClosed_flagN J.d).locallyCompactSpace
  have l4 : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hlv : Continuous (lv J.d) := J.d.continuous_levi.comp continuous_subtype_val
  have hs := J.d.continuous_embed
  have e1 : ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ :=
    lintegral_semiMeas (flagN J.d) J.d.emb0 hs J.v0.μ J.vN.ν F hF
  have e2 : ∀ h, ∫⁻ n, F (n.1 * J.d.emb0 h) ∂J.vN.ν = ∫⁻ u, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂vU.ν := fun h =>
    lintegral_of_covolOne (radX J.d) (lv J.d) (isClosed_radX J.d) hlv (lv_conj J.d) (flagN J.d) (radX_sup_lv J.d)
      (exists_proj_lv J.d) (GQ J.W) (UXQ D ρ) (rat_lv J.d) vU.ν h𝓤 h𝓤1 ν₀ h𝓝₀ h𝓝₀1 J.vN.ν h𝓝 h𝓝1
      (fun g => F (g * J.d.emb0 h)) (hF.comp (continuous_mul_const _).measurable)
  have e3 : ∀ u : UX D ρ, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1)
      ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) = ∫⁻ h, ∫⁻ n, F (n.1 * lv J.d u * J.d.emb0 h) ∂ν₀ ∂J.v0.μ := fun u => by
    rw [lintegral_semiMeas (radX J.d) J.d.emb0 hs J.v0.μ ν₀ (fun g => F (g * J.d.levi u.1))
      (hF.comp (continuous_mul_const _).measurable)]
    simp only [mul_assoc, J.d.wittHyperbolic_anisotropic_commute_levi]
    rfl
  have hm : Measurable fun q : (GA D J.W₀ × UX D ρ) × radX J.d => F (q.2.1 * lv J.d q.1.2 * J.d.emb0 q.1.1) :=
    hF.comp (Continuous.measurable (((continuous_subtype_val.comp continuous_snd).mul
      (hlv.comp (continuous_snd.comp continuous_fst))).mul (hs.comp (continuous_fst.comp continuous_fst))))
  rw [e1]
  simp only [e2, e3]
  haveI : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite vU.ν := by
    haveI : ∀ n, Fact (vU.ν (disjointed (spanningSets vU.ν) n) < ⊤) :=
      fun n => ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top vU.ν n)⟩
    exact ⟨⟨fun n => vU.ν.restrict (disjointed (spanningSets vU.ν) n), fun _ => inferInstance,
      (sum_restrict_disjointed_spanningSets vU.ν vU.ν).symm⟩⟩
  exact lintegral_lintegral_swap (hm.lintegral_prod_right' (ν := ν₀)).aemeasurable

end GlobalTheory.JacMeas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  first | exact @GlobalTheory.JacMeas.jac_measure | exact GlobalTheory.JacMeas.jac_measure | (intros; apply GlobalTheory.JacMeas.jac_measure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBoun
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBoun
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SBUnif

theorem uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) → ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧ ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := by
  intro k _ _ _ _ n n' _ _ _ _ Ψ hΨ
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset (GlobalTheory.LocMod.Inhab.eventually_invariant hΨ)
  have hinv : ∀ X u, u ∈ GlobalTheory.LocMod.Inhab.box n n' a → Ψ (X + u) = Ψ X := fun X u hu =>
    GlobalTheory.LocMod.Inhab.invariant_of_tsupport (K := GlobalTheory.LocMod.Inhab.box n n' a) (fun u hu => ha u hu) u hu X
  obtain ⟨R, hR⟩ := GlobalTheory.LocMod.Inhab.exists_cosets hΨ a
  let F : Finset k := insert (a : k) ((R ×ˢ (Finset.univ ×ˢ Finset.univ)).image fun x => x.1 x.2.1 x.2.2)
  obtain ⟨b, -, hb⟩ := F.exists_max_image (fun x => valuation k x) ⟨_, Finset.mem_insert_self _ _⟩
  have hab : valuation k (a : k) ≤ valuation k b := hb _ (Finset.mem_insert_self _ _)
  have ha0 : valuation k (a : k) ≠ 0 := by simp
  have hb0 : valuation k b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) zero_le')
  have hsupp : ∀ X, Ψ X ≠ 0 → ∀ i j, valuation k (X i j) ≤ valuation k b := by
    intro X hX i j
    obtain ⟨r, hr, hXr⟩ := hR X hX
    have h1 : valuation k ((X - r) i j) ≤ valuation k (a : k) := hXr i j
    have h2 : valuation k (r i j) ≤ valuation k b :=
      hb _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(r, i, j), by simp [hr], rfl⟩))
    have e : X i j = r i j + (X - r) i j := by simp
    rw [e]
    exact Valuation.map_add_le _ h2 (h1.trans hab)
  have hq := GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one (k := k)
  obtain ⟨e₁, he₁⟩ := exists_pow_lt₀ hq (Units.mk0 _ ha0)
  obtain ⟨e₂, he₂⟩ := exists_pow_lt₀ hq (Units.mk0 _ (inv_ne_zero hb0))
  have hpos : 0 < resCard k := Nat.card_pos
  refine ⟨resCard k ^ (e₁ + e₂), pow_pos hpos _, ?_, ?_⟩
  · intro X Y hY
    refine hinv X _ fun r q => ?_
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, Nat.cast_pow, map_pow]
    have hY' : valuation k (Y r q) ≤ 1 := hY r q
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (Y r q)
        ≤ valuation k (resCard k : k) ^ e₁ * 1 :=
          mul_le_mul' (pow_le_pow_right_of_le_one' hq.le (Nat.le_add_right _ _)) hY'
      _ ≤ valuation k (a : k) := by rw [mul_one]; exact he₁.le
  · intro X hX i j
    show valuation k _ ≤ 1
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (X i j)
        ≤ (valuation k b)⁻¹ * valuation k b :=
          mul_le_mul' ((pow_le_pow_right_of_le_one' hq.le (Nat.le_add_left _ _)).trans he₂.le) (hsupp X hX i j)
      _ = 1 := inv_mul_cancel₀ hb0

end GlobalTheory.SBUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBounStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_uniformly_locallyConstant_bounded : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) → ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧ ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := by
  first | exact @GlobalTheory.SBUnif.uniform | exact GlobalTheory.SBUnif.uniform | (intros; apply GlobalTheory.SBUnif.uniform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.QuotFubini

theorem existsUnique_mul_mem {G : Type} [Group G] {Γ R : Subgroup G} (hΓ : Γ ≤ R) {S : Set G}
    (hS : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ S) (h : G) (r : R) :
    ∃! γ : Γ.subgroupOf R, γ • r ∈ {r : R | (r : G) * h ∈ S} := by
  obtain ⟨γ, h1, h2⟩ := hS ((r : G) * h)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, γ.2⟩, ?_, fun δ hδ => ?_⟩
  · change ((γ : G) * r) * h ∈ S
    rw [mul_assoc]; exact h1
  · have h3 : (⟨((δ : R) : G), δ.2⟩ : Γ) = γ := by
      refine h2 _ ?_
      have : (((δ : R) : G) * r) * h ∈ S := hδ
      rw [mul_assoc] at this
      exact this
    ext
    exact congrArg (fun x : Γ => (x : G)) h3

end GlobalTheory.QuotFubini

namespace GlobalTheory


open GlobalTheory.QuotFubini in
theorem quot_fubini_mean : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R Γ : Subgroup G), Γ ≤ R → IsClosed (R : Set G) → Countable Γ → DiscreteTopology Γ → ∀ (μR : Measure R), μR.IsHaarMeasure → ∀ (𝓡 : Set R) (𝓑 : Set G), IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR → IsFundamentalDomain Γ 𝓑 μ → ∀ f : G → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → IsQuotIntL1 μR μ (fun h => ∫ r in 𝓡, f ((r : G) * h) ∂μR) (∫ g in 𝓑, f g ∂μ) := by
  intro G _ _ _ _ _ _ _ _ μ _ R Γ hΓR hR hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hf hfΓ hf𝓑 hf𝓡
  obtain ⟨-, S, hSm, hS⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hfΓ' : ∀ (γ : Γ) (x : G), f (γ • x) = f x := fun γ x => hfΓ γ γ.2 x
  have hmh : ∀ h : G, Measurable (fun r : R => (r : G) * h) := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h => hmh h hSm
  have hShfd : ∀ h : G, IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR := fun h =>
    IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (existsUnique_mul_mem hΓR hS h)
  have hfR : ∀ h : G, ∀ (γ : Γ.subgroupOf R) (r : R), f (((γ • r : R) : G) * h) = f ((r : G) * h) := by
    intro h γ r
    change f ((((γ : R) : G) * r) * h) = _
    rw [mul_assoc]; exact hfΓ _ γ.2 _
  have hind : ∀ h : G, (fun r : R => S.indicator f ((r : G) * h)) =
      {r : R | (r : G) * h ∈ S}.indicator (fun r : R => f ((r : G) * h)) := by
    intro h; ext r
    by_cases hr : (r : G) * h ∈ S
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ {r : R | (r : G) * h ∈ S} from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ {r : R | (r : G) * h ∈ S} from hr)]
  refine ⟨S.indicator f, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hSm).2 ((hSfd.integrableOn_iff h𝓑 hfΓ').2 hf𝓑)
  · rw [hind h]
    exact (integrable_indicator_iff (hSh h)).2 (((hShfd h).integrableOn_iff h𝓡 (hfR h)).2 (hf𝓡 h))
  · rw [hind h, integral_indicator (hSh h)]
    exact (h𝓡.setIntegral_eq (hShfd h) (hfR h))
  · rw [integral_indicator hSm]
    exact h𝓑.setIntegral_eq hSfd hfΓ'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_quotient_eq_mean_intermediate_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R Γ : Subgroup G), Γ ≤ R → IsClosed (R : Set G) → Countable Γ → DiscreteTopology Γ → ∀ (μR : Measure R), μR.IsHaarMeasure → ∀ (𝓡 : Set R) (𝓑 : Set G), IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR → IsFundamentalDomain Γ 𝓑 μ → ∀ f : G → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → IsQuotIntL1 μR μ (fun h => ∫ r in 𝓡, f ((r : G) * h) ∂μR) (∫ g in 𝓑, f g ∂μ) := by
  first | exact @GlobalTheory.quot_fubini_mean | exact GlobalTheory.quot_fubini_mean | (intros; apply GlobalTheory.quot_fubini_mean <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidDecRTrans
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RTransDecay

theorem rapidDec_rTrans : ∀ (D : D7) (V : HSp D) (G : GA D V → ℂ), RapidDec V G → (∀ h, RapidDec V (rTrans h G)) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ g h, ‖G (g * h)‖ * quotHeight V g ^ N ≤ C * height V h ^ N := by
  intro D V G hG
  refine ⟨fun h => hG.mul_right h, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hG.decay N
  refine ⟨C, fun g h => ?_⟩
  have h1 : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h := by
    simpa using GlobalTheory.Grow.quotHeight_mul_le V (g * h) h⁻¹
  calc ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V g ^ N
        ≤ ‖G (g * h)‖ * (GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos V g).le h1 N) (norm_nonneg _)
    _ = ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V (g * h) ^ N * GlobalTheory.Grow.height V h ^ N := by ring
    _ ≤ C * GlobalTheory.Grow.height V h ^ N := mul_le_mul_of_nonneg_right (hC _) (pow_pos (GlobalTheory.Grow.height_pos V h) N).le

end GlobalTheory.RTransDecay
end

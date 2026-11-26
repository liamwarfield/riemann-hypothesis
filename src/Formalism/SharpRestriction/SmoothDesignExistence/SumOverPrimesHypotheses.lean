module

public import Formalism.LocalToGlobal.GroupLattices.AdmissibleFamilyNoKernel
public import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.DivisionRationalLattice
public import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.GrowthBounds.JointsTw
public import Formalism.PeriodIntegrals.NablaSpans.ExpansionCoeffValuationGe
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LocalBoundElevenComparison
public import Formalism.SharpRestriction.Divisibility.ChainOperators.OrbitEntryBounds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzConstantTerm
public import Development.AutomorphicArithmetic.OrbitLabellings.SzEatIFree
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
noncomputable section

open scoped BigOperators
open Classical

namespace CutKW

def minorX (R : Type) [CommRing R] (N p : ℕ) (I : Fin p ↪o Fin N) : MvPolynomial (ℕ × Fin N) R :=
  Matrix.det (Matrix.of fun i k : Fin p => MvPolynomial.X ((i : ℕ), I k))

def nablaSpan (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram) :
    Submodule R (MvPolynomial (ℕ × Fin N) R) :=
  Submodule.span R (Set.range fun I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) ↪o Fin N =>
    ∏ c : Fin (nu.rowLen 0), minorX R N (nu.colLen c) (I c))

def MinorProdSpanHasCompl : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram),
    ∃ Cm : Submodule R (MvPolynomial (ℕ × Fin N) R), IsCompl (nablaSpan R N nu) Cm

def KWsb : Prop := MinorProdSpanHasCompl → KW

end CutKW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.NablaSpanC
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

abbrev nablaSpanC (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) : Submodule ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) :=
  Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))

def StepBack : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    ExpansionCoeffValuationGe N0 N1 l nu Th B → KvalGe N0 N1 l nu Th B

def StepSpan : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (I : ColChoice N1 nu),
    applyAt0 N0 N1 l Th (Gxz N0 N1 nu I) ∈ nablaSpanC Lt l N0 nu

def StepSat : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 : ℕ)
    (nu : Lt → YoungDiagram) (P : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) (B : ℝ),
    P ∈ nablaSpanC Lt l N0 nu →
    (∀ m, ‖AddMonoidAlgebra.coeff P m‖ ≤ (l : ℝ) ^ (-B)) →
    ∃ c : ColChoice N0 nu →₀ ℂ_[l], (∀ J, ‖c J‖ ≤ (l : ℝ) ^ (-B)) ∧
      P = c.sum fun J a => a • MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)

end GenFrameSpan
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.SixteenLeMulOfStdOfHypOfHyp0
noncomputable section

namespace Formalism.MainNotions.S.Inh

section a5

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

theorem tau_index_set_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  first
  | exact D.eTau.nonempty
  | exact ⟨D.eTau.symm 1⟩

variable {eps : ℝ}

end a5

end Formalism.MainNotions.S.Inh
end
end

section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSab
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem four_orbit_conditions_of_proof {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Formalism.MainNotions.OrbitPlaces.Ent D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp C : ℝ} (h : Formalism.MainNotions.OrbitPlaces.Conclusion₂ D L X K Dx T E lev Xe ce sp C) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.OrbitsWithoutOperator D L X K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp ∧
      Formalism.MainNotions.WeilJacquetShalikaLaw.LossAtDiscriminant D L K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.IsotypicPartsInternalDirectSum D Dx T sp := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Formalism.MainNotions.J
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.ChainOperators.GenericFramesLetters
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GenFrameSB
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.BasisMonomialsApply
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW MvPolynomial

section Span

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]

def atMon (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) :
    MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def Lj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  (basisMonomials (XZ Lt N0 N1) ℤ).constr ℤ (atMon Th)

def Sj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ →ₗ[ℤ] ℂ_[l] :=
  (basisMonomials (Lt × Fin N0 × Fin N1) ℤ).constr ℤ fun β =>
    (β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th

theorem basisMonomials_apply' {σ : Type} (μ : σ →₀ ℕ) :
    basisMonomials σ ℤ μ = monomial μ (1 : ℤ) := by
  simp [coe_basisMonomials]

theorem Lj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ)
    (c : ℤ) : Lj Th (monomial μ c) = c • atMon Th μ := by
  have h : (monomial μ c : MvPolynomial (XZ Lt N0 N1) ℤ) = c • basisMonomials (XZ Lt N0 N1) ℤ μ := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Lj, Module.Basis.constr_basis]

theorem Sj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (β : Lt × Fin N0 × Fin N1 →₀ ℕ) (c : ℤ) :
    Sj Th (monomial β c) = c • ((β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th) := by
  have h : (monomial β c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) =
      c • basisMonomials (Lt × Fin N0 × Fin N1) ℤ β := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Sj, Module.Basis.constr_basis]

theorem applyAt0_eq (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : applyAt0 N0 N1 l Th P = Lj Th P := by
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  unfold applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Lj_monomial, atMon, smul_monomial, zsmul_eq_mul, mul_assoc]

theorem sfe_inl_inr (α : Lt × ℕ × Fin N0 →₀ ℕ) (β : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp
      (α.mapDomain (Sum.inl : _ → XZ Lt N0 N1) + β.mapDomain Sum.inr) = (α, β) := by
  ext x
  · rw [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapDomain_of_notMem_range] <;> simp
  · rw [Finsupp.snd_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_of_notMem_range] <;> simp

theorem Lj_inl_inr (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (a : MvPolynomial (Lt × ℕ × Fin N0) ℤ) (q : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) :
    Lj Th (rename (Sum.inl : _ → XZ Lt N0 N1) a * rename (Sum.inr : _ → XZ Lt N0 N1) q) =
      Sj Th q • map (Int.castRingHom ℂ_[l]) a := by
  induction a using MvPolynomial.induction_on' with
  | monomial α r =>
    induction q using MvPolynomial.induction_on' with
    | monomial β t =>
      rw [rename_monomial, rename_monomial, monomial_mul, Lj_monomial, Sj_monomial, map_monomial,
        atMon, sfe_inl_inr]
      simp only [smul_monomial, zsmul_eq_mul, smul_eq_mul, eq_intCast, Int.cast_mul]
      congr 1
      ring
    | add q1 q2 h1 h2 => rw [map_add (f := _), mul_add, map_add (f := _), h1, h2, map_add (f := _), add_smul]
  | add a1 a2 h1 h2 => rw [map_add (f := _), add_mul, map_add (f := _), h1, h2, map_add (f := _), smul_add]

def Xm (s : Lt) (p : ℕ) : Matrix (Fin p) (Fin N0) (MvPolynomial (Lt × ℕ × Fin N0) ℤ) :=
  Matrix.of fun i a => X (s, (i : ℕ), a)

def Dm (s : Lt) (p : ℕ) (f : Fin p → Fin N0) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ((Xm (N0 := N0) s p).submatrix id f).det

def Zm (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) (f : Fin p → Fin N0) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ :=
  ∏ i, X (s, f i, I i)

theorem minorXZ_expand (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I = ∑ f : Fin p → Fin N0,
      rename (Sum.inl : _ → XZ Lt N0 N1) (Dm s p f) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (Zm s p I f) := by
  let A : Matrix (Fin p) (Fin N0) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun i a => X (Sum.inl (s, (i : ℕ), a))
  let B : Matrix (Fin N0) (Fin p) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun a k => X (Sum.inr (s, a, I k))
  have hAB : minorXZ N0 N1 s p I = (A * B).det := by
    unfold minorXZ
    congr 1
  rw [hAB, det_mul_rect]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [mul_comm]
  congr 1
  · rw [Dm, AlgHom.map_det]
    congr 1
    ext i k
    simp [A, Xm, AlgHom.mapMatrix_apply, rename_X]
  · simp [Zm, B, map_prod, rename_X]

theorem Gxz_expand (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∑ F : (∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0),
      rename (Sum.inl : _ → XZ Lt N0 N1) (∏ s, ∏ c, Dm s _ (F s c)) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (∏ s, ∏ c, Zm s _ (I s c) (F s c)) := by
  unfold Gxz
  simp_rw [minorXZ_expand, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp only [map_prod, Finset.prod_mul_distrib]

theorem nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, ∏ c, Dm s _ (J s c) := by
  unfold nablaX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  unfold Dm Xm
  rfl

theorem prodD_mem (nu : Lt → YoungDiagram)
    (F : ∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0) :
    map (Int.castRingHom ℂ_[l]) (∏ s, ∏ c, Dm s _ (F s c)) ∈ nablaSpanC Lt l N0 nu := by
  by_cases h : ∀ s (c : Fin ((nu s).rowLen 0)), ∃ (J : Fin ((nu s).colLen c) ↪o Fin N0) (e : ℤ),
      Dm s _ (F s c) = (e : MvPolynomial (Lt × ℕ × Fin N0) ℤ) * Dm s _ J
  · choose Jf ef hJ using h
    have hp : ∏ s, ∏ c, Dm s _ (F s c) =
        ((∏ s, ∏ c, ef s c : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) *
          nablaX N0 nu (Jf : ColChoice N0 nu) := by
      have hn : nablaX N0 nu Jf = ∏ s, ∏ c, Dm s _ (Jf s c) := nablaX_eq nu Jf
      rw [hn]
      simp_rw [hJ, Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hp, map_mul, map_intCast, ← zsmul_eq_mul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) Jf)) _
  · push Not at h
    obtain ⟨s, c, hsc⟩ := h
    have h0 : Dm s _ (F s c) = 0 := by
      rcases det_submatrix_fun (Xm (N0 := N0) s _) (F s c) with h0 | ⟨J, e, he⟩
      · exact h0
      · exact absurd he (hsc J e)
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero (Finset.mem_univ c) h0),
      map_zero]
    exact Submodule.zero_mem _

end Span

theorem stepSpan : StepSpan := by
  intro Lt _ _ l _ N0 N1 nu Th I
  set_option synthInstance.maxHeartbeats 100000 in
    rw [applyAt0_eq, Gxz_expand, map_sum]
  refine Submodule.sum_mem _ fun F _ => ?_
  rw [Lj_inl_inr]
  exact Submodule.smul_mem _ _ (prodD_mem nu F)

end GenFrameSpan
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOfSpan
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatDefs
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

def ProjZ : Prop :=
  MinorProdSpanHasCompl → ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 : ℕ) (nu : Lt → YoungDiagram),
    ∃ T : MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      (∀ P, T P ∈ Submodule.span ℤ (Set.range (nablaX N0 nu))) ∧ ∀ J, T (nablaX N0 nu J) = nablaX N0 nu J

end GenFrameSpan
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatFin
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

theorem stepSat_of (hP : ProjZ) : StepSat := by
  intro hadm Lt _ _ l _ N0 nu P B hPmem hPc
  obtain ⟨T, hTmem, hTfix⟩ := hP hadm Lt N0 nu
  have ha : ∀ m, ∃ a : ColChoice N0 nu →₀ ℤ,
      (a.sum fun J k => k • nablaX N0 nu J) = T (MvPolynomial.monomial m 1) :=
    fun m => Finsupp.mem_span_range_iff_exists_finsupp.mp (hTmem _)
  choose a ha using ha
  let S : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
    (MvPolynomial.basisMonomials _ ℂ_[l]).constr ℂ_[l]
      fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))
  have hS1 : ∀ m, S (MvPolynomial.monomial m 1) =
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    intro m
    have h := (MvPolynomial.basisMonomials _ ℂ_[l]).constr_basis ℂ_[l]
      (fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))) m
    simpa [MvPolynomial.coe_basisMonomials] using h
  have hSφ : ∀ Q : MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      S (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on' with
    | monomial m k =>
      have hk : MvPolynomial.monomial m k = k • MvPolynomial.monomial m (1 : ℤ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hk]
      simp only [map_zsmul]
      rw [MvPolynomial.map_monomial, map_one, hS1]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  have hle : Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) ≤ LinearMap.eqLocus S LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨J, rfl⟩
    exact (LinearMap.mem_eqLocus).mpr (by rw [hSφ, hTfix]; rfl)
  have hSP : S P = P := (LinearMap.mem_eqLocus).mp (hle hPmem)
  have hSexp : S P = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m •
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hS1, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let c : ColChoice N0 nu →₀ ℂ_[l] := ∑ m ∈ P.support,
    AddMonoidAlgebra.coeff P m • Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)
  have hc : ∀ J, c J = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m * (a m J : ℂ_[l]) := by
    intro J
    simp [c, Finsupp.finsetSum_apply]
  refine ⟨c, fun J => ?_, ?_⟩
  · rw [hc]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg l) _) fun m _ => ?_
    rw [norm_mul]
    calc ‖AddMonoidAlgebra.coeff P m‖ * ‖(a m J : ℂ_[l])‖ ≤ ‖AddMonoidAlgebra.coeff P m‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _)
      _ ≤ (l : ℝ) ^ (-B) := by rw [mul_one]; exact hPc m
  · rw [← Finsupp.linearCombination_apply]
    have hΦ : ∀ m, Finsupp.linearCombination ℂ_[l]
        (fun J => MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))
        (Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
      intro m
      rw [← ha, Finsupp.linearCombination_apply, map_finsuppSum]
      rw [Finsupp.sum_mapRange_index (by intro; exact zero_smul _ _)]
      refine Finsupp.sum_congr fun J _ => ?_
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c, map_sum, map_smul, hΦ]
    rw [← hSexp, hSP]

end GenFrameSpan
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatProj
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW MvPolynomial

namespace SatP

section Proj

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}

def emb (s : Lt) : ℕ × Fin N0 → Lt × ℕ × Fin N0 := fun p => (s, p.1, p.2)

theorem emb_inj (s : Lt) : Function.Injective (emb (N0 := N0) s) := by
  intro a b h
  simp only [emb, Prod.mk.injEq] at h
  exact Prod.ext h.2.1 h.2.2

def res (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) : ℕ × Fin N0 →₀ ℕ :=
  m.comapDomain (emb s) (emb_inj s).injOn

theorem res_apply (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) (p : ℕ × Fin N0) :
    res s m p = m (emb s p) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem res_sum (n : Lt → (ℕ × Fin N0 →₀ ℕ)) (t : Lt) :
    res t (∑ s, (n s).mapDomain (emb s)) = n t := by
  ext p
  rw [res_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · exact Finsupp.mapDomain_apply_of_injective (emb_inj t) _ _
  · intro s _ hst
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    simp only [emb, Prod.mk.injEq] at hq
    exact hst hq.1
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem prod_rename_monomial (n : Lt → (ℕ × Fin N0 →₀ ℕ)) :
    ∏ s, rename (emb s) (monomial (n s) (1 : ℤ)) =
      monomial (∑ s, (n s).mapDomain (emb s)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

theorem nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c)) := by
  unfold nablaX minorX
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det]
  congr 1
  ext i k
  simp [emb]

def Tmap (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ)) :
    MvPolynomial (Lt × ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  (basisMonomials (Lt × ℕ × Fin N0) ℤ).constr ℤ fun m =>
    ∏ s, rename (emb s) (π s (monomial (res s m) 1))

theorem Tmap_monomial (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (m : Lt × ℕ × Fin N0 →₀ ℕ) :
    Tmap π (monomial m 1) = ∏ s, rename (emb s) (π s (monomial (res s m) 1)) := by
  have : (monomial m (1 : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) =
      basisMonomials (Lt × ℕ × Fin N0) ℤ m := by
    rw [coe_basisMonomials]
  rw [this, Tmap, Module.Basis.constr_basis]

theorem Tmap_prod (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (h : Lt → MvPolynomial (ℕ × Fin N0) ℤ) :
    Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) := by
  suffices H : ∀ F : Finset Lt, ∀ h : Lt → MvPolynomial (ℕ × Fin N0) ℤ,
      (∀ s ∉ F, ∃ n, h s = monomial n 1) →
      Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) from
    H Finset.univ h (fun s hs => absurd (Finset.mem_univ s) hs)
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro h hh
    choose n hn using fun s => hh s (by simp)
    have : h = fun s => monomial (n s) 1 := funext hn
    subst this
    rw [prod_rename_monomial, Tmap_monomial]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [res_sum]
  | insert a F haF ih =>
    intro h hh
    have key : ∀ g : MvPolynomial (ℕ × Fin N0) ℤ,
        Tmap π (rename (emb a) g * ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) =
          rename (emb a) (π a g) * ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) := by
      let A : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        Tmap π ∘ₗ LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) ∘ₗ
          (rename (emb a)).toLinearMap
      let B : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s))) ∘ₗ
          (rename (emb a)).toLinearMap ∘ₗ π a
      have hAB : A = B := by
        refine (basisMonomials (ℕ × Fin N0) ℤ).ext fun u => ?_
        rw [coe_basisMonomials]
        simp only [A, B, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
          AlgHom.toLinearMap_apply]
        have h1 := ih (Function.update h a (monomial u 1)) (by
          intro s hs
          by_cases hsa : s = a
          · subst hsa
            exact ⟨u, by simp⟩
          · rw [Function.update_of_ne hsa]
            exact hh s (by simp [hsa, hs]))
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
          ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (Function.update h a (monomial u 1) s)))
            (Finset.mem_univ a)] at h1
        simp only [Function.update_self] at h1
        have e1 : ∏ s ∈ Finset.univ.erase a, rename (emb s) (Function.update h a (monomial u 1) s) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        have e2 : ∏ s ∈ Finset.univ.erase a,
            rename (emb s) (π s (Function.update h a (monomial u 1) s)) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        rw [e1, e2] at h1
        exact h1
      intro g
      exact LinearMap.congr_fun hAB g
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (h s))) (Finset.mem_univ a)]
    exact key (h a)

theorem prod_mem_span (nu : Lt → YoungDiagram) (g : Lt → MvPolynomial (ℕ × Fin N0) ℤ)
    (hg : ∀ s, g s ∈ nablaSpan ℤ N0 (nu s)) :
    ∏ s, rename (emb s) (g s) ∈ Submodule.span ℤ (Set.range (nablaX N0 nu)) := by
  by_cases hne : Nonempty (ColChoice N0 nu)
  · obtain ⟨J0⟩ := hne
    suffices H : ∀ F : Finset Lt, ∏ s ∈ F, rename (emb s) (g s) ∈ Submodule.span ℤ
        (Set.range fun J : ColChoice N0 nu =>
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) by
      have H1 := H Finset.univ
      have hf : (fun J : ColChoice N0 nu =>
          ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) = nablaX N0 nu :=
        funext fun J => (nablaX_eq nu J).symm
      rw [hf] at H1
      exact H1
    intro F
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact Submodule.subset_span ⟨J0, rfl⟩
    | insert a F haF ih =>
      rw [Finset.prod_insert haF]
      have ha : rename (emb a) (g a) ∈ Submodule.span ℤ (Set.range fun
          j : (∀ c : Fin ((nu a).rowLen 0), Fin ((nu a).colLen c) ↪o Fin N0) =>
            rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c))) := by
        have := Submodule.mem_map_of_mem (f := (rename (emb a)).toLinearMap) (hg a)
        rw [nablaSpan, Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hm := Submodule.mul_mem_mul ha ih
      rw [Submodule.span_mul_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
      change (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) at J
      refine ⟨Function.update J a j, ?_⟩
      show ∏ s ∈ insert a F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
          minorX ℤ N0 ((nu s).colLen c) (Function.update J a j s c)) =
        rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c)) *
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
            minorX ℤ N0 ((nu s).colLen c) (J s c))
      rw [Finset.prod_insert haF, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsa : s ≠ a := fun h => haF (h ▸ hs)
      rw [Function.update_of_ne hsa]
  · have hex : ∃ s, IsEmpty (∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) := by
      by_contra hcon
      push Not at hcon
      exact hne ⟨fun s => (hcon s).some⟩
    obtain ⟨s, hs⟩ := hex
    have h0 : g s = 0 := by
      have := hg s
      rw [nablaSpan, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
      exact this
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [h0, map_zero])]
    exact Submodule.zero_mem _

end Proj

end SatP

open SatP in
theorem projZ : ProjZ := by
  intro hSB Lt _ _ N0 nu
  choose Cm hCm using fun s => hSB ℤ N0 (nu s)
  let π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ) := fun s =>
    (nablaSpan ℤ N0 (nu s)).subtype ∘ₗ Submodule.projectionOnto _ _ (hCm s)
  have hπmem : ∀ s x, π s x ∈ nablaSpan ℤ N0 (nu s) := fun s x =>
    (Submodule.projectionOnto _ _ (hCm s) x).2
  have hπfix : ∀ s x, x ∈ nablaSpan ℤ N0 (nu s) → π s x = x := fun s x hx => by
    simp only [π, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [Submodule.projectionOnto_apply_left (hCm s) ⟨x, hx⟩]
  refine ⟨Tmap π, fun P => ?_, fun J => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [MvPolynomial.as_sum P, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      have : monomial m (AddMonoidAlgebra.coeff P m) = AddMonoidAlgebra.coeff P m • monomial m (1 : ℤ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, LinearMap.map_smul, Tmap_monomial]
      exact Submodule.smul_mem _ _ (prod_mem_span nu _ fun s => hπmem s _)
  · rw [SatP.nablaX_eq, Tmap_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hπfix]
    exact Submodule.subset_span ⟨J s, rfl⟩

end GenFrameSpan
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.StepBack
noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

theorem stepBack : StepBack := by
  intro Lt _ _ l _ N0 N1 nu Th B h I m
  obtain ⟨c, hc, heq⟩ := h I
  rw [heq]
  have hC : (0 : ℝ) ≤ (l : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun J _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, norm_mul]
  have h1 : ‖(Int.castRingHom ℂ_[l]) (AddMonoidAlgebra.coeff (nablaX N0 nu J) m)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[l] (AddMonoidAlgebra.coeff (nablaX N0 nu J) m)
  calc ‖c J‖ * ‖(Int.castRingHom ℂ_[l]) (AddMonoidAlgebra.coeff (nablaX N0 nu J) m)‖
      ≤ (l : ℝ) ^ (-B) * 1 := mul_le_mul (hc J) h1 (norm_nonneg _) hC
    _ = _ := mul_one _

end GenFrameSpan
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOf
namespace GenFrameSpan

open CutKW

theorem genFrameSB_of (hb : StepBack) (hs : StepSpan) (ht : StepSat) : CutKW.KWsb := by
  intro hSB Lt _ _ l _ N0 N1 nu Th B
  exact ⟨fun h I => ht hSB Lt l N0 nu _ B (hs Lt l N0 N1 nu Th I) (h I), hb Lt l N0 N1 nu Th B⟩

end GenFrameSpan
end

namespace GenFrameSpan

theorem stepSat : StepSat := stepSat_of projZ

theorem genFrameSB_of_span (hs : StepSpan) : CutKW.KWsb := genFrameSB_of stepBack hs stepSat

end GenFrameSpan
end

theorem coeffNormLE_iff_spanNormLE_of_hasCompl : CutKW.KWsb := GenFrameSpan.genFrameSB_of_span GenFrameSpan.stepSpan
end

section -- merged from Formalism.SharpRestriction.Divisibility.ChainOperators.WeightFramesOfSubgroupFrames
open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem kw_of_cutSB (h : CutKW.KWsb) : CutKW.KW := h minor_span_complement

end Formalism.MainNotions.DIV.Lemmas
end

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem cutKW_holds : CutKW.KW := kw_of_cutSB coeffNormLE_iff_spanNormLE_of_hasCompl

theorem theta_isometry_facts_hold (D : D7) : Formalism.MainNotions.OrbitPlaces.ConclusionW D := by
  intro l _ N0 N1 nu Th B
  apply cutKW_holds

end Formalism.MainNotions.DIV.Lemmas
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzEatI
theorem sz_eat_identity : PI.SzEatI.SzEatI := UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA
end

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

section Sz

open Formalism.MainNotions.G

theorem szCt_fam {eps : ℝ} (Fm : FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ u : (Fm.D x i).what₂.Word, ∑ t : HH (Fm.D x i), ctD (Fm.D x i) u j t ≤
      2 * ((Fm.D x i).host.TT.card : ℝ) * (Fm.L x i).sc.b + 2 * ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.k * (Fm.L x i).sc.b' := by
  obtain ⟨x0, hx0⟩ := sz_constant_term eps Fm.Ct Fm.CGam Fm.Cc Fm.CT2 Fm.PK
  refine ⟨x0, fun x hx hx1 i => hx0 (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i)
    ⟨Fm.L_eps x i, Fm.Ct_eq x i, Fm.CGam_eq x i, Fm.Cc_eq x i, Fm.secondConstant_eq x i, Fm.params_K x hx1 i⟩
    (by rw [Fm.L_x x i hx1]; exact hx) (Fm.sizes x hx1 i)⟩

theorem szEatI_fam {eps : ℝ} (Fm : FamP eps) : ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (IsResidueClassZero (Fm.D x i) p ∨ IsSg (Fm.D x i) p) ∧ ¬ (IsResidueClassZero (Fm.D x i) p ∧ hP (Fm.D x i) p = 0) ∧
        (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) →
      ∑ p ∈ S, Real.log p * (EatI (Fm.L x i) Fm.GK Fm.cX.err j p - max 0 (WeilJacquetShalikaLaw.FkindA (Fm.D x i) j p)) ≤
        C * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) := by
  obtain ⟨C, hC, x0, hx0⟩ := sz_eat_identity Fm.GK Fm.cX.err eps Fm.Ct Fm.CGam Fm.Cc Fm.CT2 Fm.PK
  refine ⟨C, hC, x0, fun x hx hx1 i => hx0 (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i)
    ⟨Fm.L_eps x i, Fm.Ct_eq x i, Fm.CGam_eq x i, Fm.Cc_eq x i, Fm.secondConstant_eq x i, Fm.params_K x hx1 i⟩
    (by rw [Fm.L_x x i hx1]; exact hx) (Fm.sizes x hx1 i)⟩

theorem one_le_Xpp {D : D7} (L : SizeData₂ D) (h : SizesAt L) (hm : 1 ≤ D.R.m) : 1 ≤ L.sc.X'' D.R.n := by
  obtain ⟨τ⟩ := S.Inh.tau_index_set_nonempty D
  have hX : SizeXpp L := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw : L.sc.w'' D.R.n ≤ wj D 1 τ := S.wj_ge L τ 1 le_rfl hm
  have hpos : 0 < wj D 1 τ := lt_of_lt_of_le (S.w''_pos L) hw
  have hr := hX 1 τ 1 τ le_rfl hm le_rfl hm
  nlinarith

theorem admissible_size_family {eps : ℝ} (Fm : FamP eps) (hD : DGamSize Fm) : ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), WeilJacquetShalikaLaw.TypePrimeSizeConds (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  obtain ⟨xz, hz⟩ := szCt_fam Fm
  obtain ⟨Ce, hCe, xe, he⟩ := szEatI_fam Fm
  obtain ⟨Cd, xd, hd⟩ := hD
  refine ⟨max Ce (max Cd 0), le_trans (le_max_right _ _) (le_max_right _ _), max xz (max xe xd), fun x hx h1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨ez, ee, ed⟩ := hx
  refine ⟨hz x ez h1 i, J.factDGam_mono (hd x ed i) (le_trans (le_max_left _ _) (le_max_right _ _)), fun j hj S hS => ?_⟩
  have hm : 1 ≤ (Fm.D x i).R.m := by
    simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
    omega
  have hlog : 0 ≤ Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) := Real.log_nonneg (one_le_Xpp (Fm.L x i) (Fm.sizes x h1 i) hm)
  have hb : 0 < (Fm.L x i).sc.b := by unfold Scale.b; positivity
  have hf : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) := Nat.cast_nonneg _
  have hnn : 0 ≤ ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) :=
    mul_nonneg (mul_nonneg hf hb.le) hlog
  refine (he x ee h1 i j hj S hS).trans ?_
  calc Ce * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n)
      = Ce * (((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n)) := by ring
    _ ≤ max Ce (max Cd 0) * (((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    _ = max Ce (max Cd 0) * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) := by ring

end Sz

section Re

open Formalism.MainNotions.G

def reY {D : D7} (Y : LatInst D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv) : LatInst D where
  vOf := Y.vOf
  Fl := Y.Fl
  Lv := fun u w hg => (LC (D.what₂.muAt w) u w hg).1
  Ch := fun u w hg => (LC (D.what₂.muAt w) u w hg).2
  Vram := Y.Vram

def reW {D : D7} (Y : LatInst D) (LC : _) : WeilJacquetShalikaLaw.TwLoc D (reY Y LC) := ⟨LC, fun _ _ _ => rfl⟩

theorem serv_re {D : D7} {L : SizeData₂ D} {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D}
    {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C : ℝ} (LC : _)
    (h : WeilJacquetShalikaLaw.Serv D L X (reY Y LC) K c Dx T lev Xe ce C) : WeilJacquetShalikaLaw.Serv D L X Y K c Dx T lev Xe ce C := by
  unfold WeilJacquetShalikaLaw.Serv at h ⊢
  refine ⟨h.1, ?_, h.2.2⟩
  have h2 := h.2.1
  unfold WeilJacquetShalikaLaw.Conclusion1 at h2 ⊢
  intro hT
  have hT' : WeilJacquetShalikaLaw.Ties9 D L X (reY Y LC) c := { hT with }
  exact h2 hT'

theorem num_re {D : D7} {L : SizeData₂ D} {X : Inst D L} {Y : LatInst D} {K : Consts} (LC : _)
    (h : FormalGroupSystem.SmallResidueCharComparison D L X Y K) : FormalGroupSystem.SmallResidueCharComparison D L X (reY Y LC) K := h

end Re


open Classical in
def SysTw (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (K : G.Consts) (Dx : DivX D) {Y : G.LatInst D} (W : WeilJacquetShalikaLaw.TwLoc D Y)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  ErrDefs D L Xe lev K ce → ∀ μ, DV.Used D μ → ∀ (hT : GatTies D), G.LatTied hT X (W.Yt μ) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp μ →
    ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
      (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) ((W.Yt μ).Fl u w hg)
        ((W.Yt μ).Lv u w hg) ((W.Yt μ).Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
      FormalGroupSystem.admitted D _ Y5 ∧
      ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
        (∀ v, v ∉ (G.reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg) → ∀ j < D.R.m,
          Y5.LowAt j v (Fn v (j + 1))) ∧
        WeilJacquetShalikaLaw.lowS L Xe K ce sp u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
          ∑ v ∈ Finset.univ \ (G.reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg), Fn v j) -
            ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

structure SumOverPrimesHypotheses (𝒞 : FamClass) : Prop where

  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1

  pdv : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ E : KerEnt (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw,
      (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg)

theorem typeG_ne_d {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (k : Fin 2) : D.host.g k ≠ D.host.d := by
  have hs := P.level_split _ (D.host.g_level k)
  intro h
  rw [h] at hs
  simp only [Host.cls, primeClass] at hs
  split_ifs at hs

theorem closed_large_pos {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (K0 : TransportedAlt) (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 0 < eps → Fm.Large K0 CH → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  unfold Closed at hP ⊢
  obtain ⟨ε1, hε1, hP⟩ := hP
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hK⟩ := hP eps he he1
  refine ⟨⟨max K.pre K0.pre, fun l => max (K.t l) (K0.t l), fun l => max (K.mid l) (K0.mid l),
    fun l => max (K.last l) (K0.last l)⟩, fun Fm CH hC hL => ?_⟩
  unfold Formalism.MainNotions.FamP.Large at hL
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hLK : Fm.Large K CH := by
    unfold Formalism.MainNotions.FamP.Large
    exact ⟨fun c hc => (le_max_left _ _).trans (h1 c hc), trivial,
      fun c hc => (le_max_left _ _).trans (h3 c hc), fun c hc => (le_max_left _ _).trans (h4 c hc)⟩
  have hLK0 : Fm.Large K0 CH := by
    unfold Formalism.MainNotions.FamP.Large
    exact ⟨fun c hc => (le_max_right _ _).trans (h1 c hc), trivial,
      fun c hc => (le_max_right _ _).trans (h3 c hc), fun c hc => (le_max_right _ _).trans (h4 c hc)⟩
  exact h Fm CH he hLK0 (hK Fm CH hC hLK)

theorem three_le_split {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) {x : ℝ} (hx : (3 : ℝ) ^ (5 / Fm.ez) ≤ x) (h1 : Fm.x1 < x)
    (i : Fm.Ix x) : 3 ≤ (Fm.D x i).host.splitBound := by
  have hez : 0 < Fm.ez := by rw [← Fm.L_ez x i]; exact (Fm.L x i).sc.ez_pos
  have hL := (Fm.L x i).split_tie
  rw [Fm.L_x x i h1, Fm.L_ez x i] at hL
  refine le_trans (Nat.le_floor ?_) hL
  have he : 5 / Fm.ez * (Fm.ez / 5) = 1 := by field_simp
  calc ((3 : ℕ) : ℝ) = ((3 : ℝ) ^ (5 / Fm.ez)) ^ (Fm.ez / 5) := by
        rw [← Real.rpow_mul (by norm_num), he, Real.rpow_one]; norm_num
    _ ≤ x ^ (Fm.ez / 5) := Real.rpow_le_rpow (by positivity) hx (by positivity)

theorem sum_over_primes_service (𝒞 : FamClass) (hD : Closed 𝒞 fun Fm _ => DGamSize Fm) (h : SumOverPrimesHypotheses 𝒞) :
    Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm := by
  have hpdv := h.pdv
  have h01 : OrbitPlaces.OrbitLetterBoundsAll 11 1 := DIV.Bridge.DworkPowerSeriesWeights.split_bound_eleven_one
  refine closed_large_pos ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
    (hD.and (h.twU.and (hpdv.and (G.num_closed 𝒞 FormalGroupSystem.Pf.stmtNumE))))
    fun {eps} Fm CH hpos hL ⟨hDg, ⟨xb, hb⟩, ⟨xc, hc⟩, ⟨xn, hnum⟩⟩ => ?_
  have hpr1 : 1 ≤ Fm.GK.Pr1 := le_of_eq Fm.fixed.1.symm
  have hCL : OrbitPlaces.CLarge 11 1 Fm.GK Fm.cX.err :=
    OrbitPlaces.cLarge_of_fixed Fm.fixed.2.2.2.2.1 Fm.fixed.2.2.2.2.2.1 Fm.fixed.2.1 (by rw [Fm.fixed.2.2.1]; norm_num)
  obtain ⟨Cs, hCs, xa, ha⟩ := admissible_size_family Fm hDg
  refine ⟨Cs, hCs, max (max xa xb) (max (max xc ((3 : ℝ) ^ (5 / Fm.ez))) xn), fun x hx h1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨ea, eb⟩, ⟨ec, ef⟩, en⟩ := hx
  obtain ⟨LC, hV, hSys⟩ := hb x eb h1 i
  have hU := G.Joints.unit_bound_of_sum_over_primes _ _ _ _ _ _ (reW (Fm.Gy x i) LC) _ _ _ 1 (FormalGroupSystem.Pf.stmt_proved _) hSys
    (num_re LC (hnum x en i))
    (G.TopChoiceBounds.hLarge_proved _ _ Fm.GK_nonneg hpr1 (Fm.params x h1 i))
  obtain ⟨E, ⟨hUn, hR, hKF, hS0⟩, ep, be, sg, b0, b0c, a', ei, sd, sh⟩ := hc x ec h1 i
  have gd : OrbitPlaces.TypePrimeNotDiscriminant (Fm.D x i) := fun k => typeG_ne_d (Fm.params x h1 i) k
  have o := DIV.Inh.orbit_admissible_of_split_bound (Fm.D x i) (three_le_split Fm hpos ef h1 i)
  have hW : OrbitPlaces.SB E := fun _ _ _ _ _ _ B hB => (DIV.Lemmas.theta_isometry_facts_hold (Fm.D x i) _ _ _ _ _ B).1 hB
  have hK : OrbitPlaces.KForm (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) (Fm.ex x h1 i).tw 1 :=
    OrbitPlaces.kform_of_ker E _ (fun _ _ => rfl) rfl hW hUn hR hKF
      (Or.inr ⟨rfl, hS0⟩)
  have hA : OrbitPlaces.admitted (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK (Fm.X x i) (Fm.ex x h1 i).tw
      (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) Fm.cX.err 1 11 1 :=
    ⟨hK, o, gd, b0, b0c, h01, a', ei, sd, sh, hCL⟩
  obtain ⟨n, c, d, it⟩ := J.four_orbit_conditions_of_proof (lev := (Fm.ex x h1 i).lev) (Xe := (Fm.ex x h1 i).errX)
    (OrbitPlaces.lift_bounds_of_essential hA (DIV.Lemmas.OrbitEntryBounds.orbit_entry_bounds_hold _ _ _ _ _ _ _ 11 1 h01 sd sh hCL))
  have hAdm : WeilJacquetShalikaLaw.admitted (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (reY (Fm.Gy x i) LC) Fm.GK (Fm.X x i) (Fm.ex x h1 i).tw
      (reW (Fm.Gy x i) LC) (Fm.ex x h1 i).lev (Fm.ex x h1 i).errX Fm.cX.err 1 :=
    ⟨hU, WeilJacquetShalikaLaw.local_theorem_of_statement _ (FormalGroupSystem.Pf.stmtAt_proved _), it, n, c, d⟩
  exact serv_re LC (WeilJacquetShalikaLaw.serv_of (WeilJacquetShalikaLaw.Proof.stmt_proved _ _ _ _ _ _ _) (reW (Fm.Gy x i) LC) hV hAdm
    (ha x ea h1 i))

end Formalism.MainNotions.Pk

end

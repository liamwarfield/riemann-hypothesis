module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.WwMain
noncomputable section

namespace PI.WwMain

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def applyQ {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) : ℂ_[l] :=
  let P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l] :=
    MvPolynomial.aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      MvPolynomial.C (y' v.1 b v.2.2) * MvPolynomial.X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q
  ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th

def WwMain : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]),
    (∀ y : Lt → Fin N0 → ℕ → ℂ_[l], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (DeX N0 nu y)) →
    ∀ y' : Lt → Fin N1 → ℕ → ℂ_[l],
      applyQ l N0 N1 Th Q y' = ∑ᶠ I : KM.ColChoice N1 nu, minY N1 nu I y' * ph (KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I))

end PI.WwMain
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice
open MvPolynomial Finset

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

instance finiteOE (p n : ℕ) : Finite (Fin p ↪o Fin n) :=
  Finite.of_injective (fun e : Fin p ↪o Fin n => (e : Fin p → Fin n))
    (fun _ _ h => DFunLike.coe_injective h)

instance fintypeOE (p n : ℕ) : Fintype (Fin p ↪o Fin n) := Fintype.ofFinite _

instance fintypeColChoice {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Fintype (ColChoice N nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N))

def CBSorted : Prop :=
  ∀ (R : Type) [CommRing R] (p n : ℕ) (A : Matrix (Fin p) (Fin n) R) (B : Matrix (Fin n) (Fin p) R),
    (A * B).det = ∑ J : Fin p ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det

def chi {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →+* MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  eval₂Hom ((C : ℂ_[l] →+* MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]).comp (Int.castRingHom ℂ_[l]))
    (Sum.elim X (fun w => C (z w)))

def Hpol {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (G : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l] :=
  ∑ μ ∈ G.support, monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    (((AddMonoidAlgebra.coeff G μ : ℤ) : ℂ_[l]) * ph (monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 1))

def wt {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (α : (Lt × Fin N0 × Fin N1) →₀ ℕ) : ℂ_[l] :=
  (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th

def Lfun {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) : ℂ_[l] :=
  ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * wt l N0 N1 Th α

def EvalH : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (G : MvPolynomial (XZ Lt N0 N1) ℤ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l]),
    eval z (Hpol l N0 N1 ph G) = ph (chi l N0 N1 z G)

def LH : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (G : MvPolynomial (XZ Lt N0 N1) ℤ),
    Lfun l N0 N1 Th (Hpol l N0 N1 ph G) = ph (applyAt0 N0 N1 l Th G)

def LLin : Prop :=
  ∀ (Lt : Type) (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    (∀ p q, Lfun l N0 N1 Th (p + q) = Lfun l N0 N1 Th p + Lfun l N0 N1 Th q) ∧
    Lfun l N0 N1 Th 0 = 0 ∧
    (∀ c p, Lfun l N0 N1 Th (C c * p) = c * Lfun l N0 N1 Th p)

def DeXCB : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]),
    DeX N0 nu (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j) =
      ∑ I : ColChoice N1 nu, C (minY N1 nu I y') * chi l N0 N1 z (Gxz N0 N1 nu I)

end PI.WwMainW
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.LfunEqOfSubset
open MvPolynomial Finset

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

theorem Lfun_eq_of_subset {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l])
    (s : Finset ((Lt × Fin N0 × Fin N1) →₀ ℕ)) (hs : P.support ⊆ s) :
    Lfun l N0 N1 Th P = ∑ α ∈ s, AddMonoidAlgebra.coeff P α * wt l N0 N1 Th α := by
  unfold Lfun
  exact Finset.sum_subset hs (fun α _ h => by
    rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul])

theorem lLin : LLin := by
  unfold LLin
  intro Lt l _ N0 N1 Th
  classical
  refine ⟨fun p q => ?_, ?_, fun c p => ?_⟩
  · rw [Lfun_eq_of_subset l N0 N1 Th (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      Lfun_eq_of_subset l N0 N1 Th p (p.support ∪ q.support) Finset.subset_union_left,
      Lfun_eq_of_subset l N0 N1 Th q (p.support ∪ q.support) Finset.subset_union_right]
    rw [← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_mul]
  · rw [Lfun_eq_of_subset l N0 N1 Th 0 ∅ (by simp)]
    simp
  · have hsub : (MvPolynomial.C c * p).support ⊆ p.support := fun x hx => by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hx
      exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx)
    rw [Lfun_eq_of_subset l N0 N1 Th (MvPolynomial.C c * p) p.support hsub,
      Lfun_eq_of_subset l N0 N1 Th p p.support subset_rfl, Finset.mul_sum]
    simp only [MvPolynomial.coeff_C_mul, mul_assoc]

theorem Lfun_monomial {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (α : (Lt × Fin N0 × Fin N1) →₀ ℕ) (c : ℂ_[l]) :
    Lfun l N0 N1 Th (monomial α c) = c * wt l N0 N1 Th α := by
  classical
  rw [Lfun_eq_of_subset l N0 N1 Th _ {α} MvPolynomial.support_monomial_subset]
  simp

theorem Lfun_sum' {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    Lfun l N0 N1 Th (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun l N0 N1 Th (f i) := by
  classical
  rw [Lfun_eq_of_subset l N0 N1 Th _ (s.biUnion fun i => (f i).support) MvPolynomial.support_sum]
  rw [Finset.sum_congr rfl (fun i hi => Lfun_eq_of_subset l N0 N1 Th (f i)
    (s.biUnion fun i => (f i).support) (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi))]
  simp only [MvPolynomial.coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem lH : LH := by
  unfold LH Hpol
  intro Lt _ _ l _ N0 N1 Th ph G
  rw [Lfun_sum']
  simp only [Lfun_monomial]
  unfold applyAt0
  have hm : ∀ (a : Lt × ℕ × Fin N0 →₀ ℕ) (c : ℂ_[l]),
      ph (MvPolynomial.monomial a c) = c * ph (MvPolynomial.monomial a 1) := fun a c => by
    rw [← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  conv_rhs => rw [hm]
  unfold wt
  ring

theorem sumElim_split {α β : Type} (μ : (α ⊕ β) →₀ ℕ) :
    μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1
      (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
  ext x
  rcases x with x | x <;> simp

theorem chi_monomial {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l])
    (μ : (XZ Lt N0 N1) →₀ ℕ) (n : ℤ) :
    chi l N0 N1 z (monomial μ n) =
      C ((n : ℂ_[l]) * (Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun w e => z w ^ e) *
        monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 1 := by
  unfold chi
  set p := Finsupp.sumFinsuppEquivProdFinsupp μ with hp
  have hμ : μ = Finsupp.sumElim p.1 p.2 := sumElim_split μ
  rw [hμ, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.monomial_eq, map_one, one_mul, map_mul, Finsupp.prod, map_prod, map_pow, eq_intCast]
  simp only [map_intCast]
  ring

theorem evalH : EvalH := by
  unfold EvalH Hpol
  intro Lt _ _ l _ N0 N1 ph G z
  conv_rhs => rw [G.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [chi_monomial, MvPolynomial.eval_monomial, MvPolynomial.C_mul', map_smul, smul_eq_mul]
  ring

end PI.WwMainW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.DeXCBOf
open MvPolynomial Finset Matrix

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

theorem block (hCB : CBSorted) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) (s : Lt) (p : ℕ) :
    Matrix.det (Matrix.of fun i j : Fin p => ∑ a : Fin N0,
        C (∑ b : Fin N1, z (s, a, b) * y' s b (j : ℕ)) *
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) =
      ∑ J : Fin p ↪o Fin N1, C (Matrix.det (Matrix.of fun i j : Fin p => y' s (J i) (j : ℕ))) *
        chi l N0 N1 z (minorXZ N0 N1 s p J) := by
  unfold chi minorXZ
  calc _ = ((Matrix.of (fun (i : Fin p) (b : Fin N1) => (∑ a : Fin N0,
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) * C (z (s, a, b)) :
            MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) :
            Matrix (Fin p) (Fin N1) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) *
        (Matrix.of (fun (b : Fin N1) (j : Fin p) =>
          (C (y' s b (j : ℕ)) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) :
            Matrix (Fin N1) (Fin p) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))).det := by
        congr 1
        refine Matrix.ext fun i j => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul]
        first
          | (rw [Finset.sum_comm]
             exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
          | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
          | (rw [Finset.sum_comm]; ring)
    _ = _ := hCB _ _ _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun J _ => ?_
        refine (mul_comm _ _).trans ?_
        congr 1
        · rw [RingHom.map_det]
          congr 1
          try (refine Matrix.ext fun i j => ?_; simp [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply])
        · rw [RingHom.map_det]
          congr 1
          try (refine Matrix.ext fun i k => ?_; simp [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
            map_sum, MvPolynomial.eval₂Hom_X'])

theorem deXCB_of (hCB : CBSorted) : DeXCB := by
  unfold DeXCB
  intro Lt _ _ l _ N0 N1 nu z y'
  unfold DeX minY Gxz
  simp only [block hCB l N0 N1 z y', map_prod, ← Finset.prod_mul_distrib]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  first
    | rfl
    | (congr 1)
    | exact Finset.sum_congr (Subsingleton.elim _ _) fun _ _ => rfl

end PI.WwMainW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.InfinitePadicComplex
open MvPolynomial Finset

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

instance infinitePadicComplex (l : ℕ) [Fact l.Prime] : Infinite ℂ_[l] :=
  Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective

theorem Lfun_sum (hLin : LLin) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    Lfun l N0 N1 Th (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun l N0 N1 Th (f i) := by
  classical
  obtain ⟨hadd, hzero, -⟩ := hLin Lt l N0 N1 Th
  refine Finset.induction_on s ?_ ?_
  · simp [hzero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

theorem applyQ_eq {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l])
    (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    applyQ l N0 N1 Th Q y' = Lfun l N0 N1 Th (aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q) := by
  unfold applyQ Lfun wt
  exact Finset.sum_congr rfl fun α _ => by ring

theorem wwMain_of (hE : EvalH) (hL : LH) (hLin : LLin) (hD : DeXCB) : WwMain := by
  intro Lt _ _ l _ N0 N1 nu Th ph Q hQ y'
  rw [applyQ_eq l N0 N1 Th Q y']
  have heval : ∀ (g : Lt × Fin N0 × ℕ → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l])
      (z : Lt × Fin N0 × Fin N1 → ℂ_[l]), eval z (aeval g Q) = eval (fun v => eval z (g v)) Q := by
    intro g z
    have h : (aeval z).comp (aeval g) = aeval (R := ℂ_[l]) (fun v => aeval z (g v)) :=
      MvPolynomial.algHom_ext fun v => by simp
    have h2 := congrArg (fun φ : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l] →ₐ[ℂ_[l]] ℂ_[l] => φ Q) h
    simpa [MvPolynomial.coe_aeval_eq_eval] using h2
  have hP : aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q =
      ∑ I : ColChoice N1 nu, C (minY N1 nu I y') * Hpol l N0 N1 ph (Gxz N0 N1 nu I) := by
    apply MvPolynomial.funext
    intro z
    rw [heval]
    have hy : (fun v : Lt × Fin N0 × ℕ => eval z (∑ b : Fin N1,
        C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1))) =
        fun v => (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j) v.1 v.2.1 v.2.2 := by
      funext v
      simp [mul_comm]
    rw [hy, hQ (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j), hD Lt l N0 N1 nu z y']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, C_mul', map_smul, smul_eq_mul, MvPolynomial.smul_eval,
      hE Lt l N0 N1 ph]
  rw [hP, Lfun_sum hLin, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(hLin Lt l N0 N1 Th).2.2, hL Lt l N0 N1 Th ph]

end PI.WwMainW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.SumInjEqSumPairs
open Matrix Finset Equiv

noncomputable section

namespace PI.WwMainW

theorem sum_inj_eq_sum_pairs {R : Type} [CommRing R] {p n : ℕ} (F : (Fin p → Fin n) → R) :
    ∑ x : (Fin p ↪o Fin n) × Perm (Fin p), F (x.1 ∘ x.2) =
      ∑ f ∈ univ.filter (fun f : Fin p → Fin n => Function.Injective f), F f := by
  classical
  refine Finset.sum_bij (fun x _ => (x.1 : Fin p → Fin n) ∘ x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.injective.comp x.2.injective
  · rintro ⟨I, σ⟩ _ ⟨J, τ⟩ _ h
    simp only at h
    have hr : Set.range (I : Fin p → Fin n) = Set.range (J : Fin p → Fin n) := by
      calc Set.range (I : Fin p → Fin n) = Set.range (⇑I ∘ ⇑σ) := (σ.surjective.range_comp _).symm
        _ = Set.range (⇑J ∘ ⇑τ) := by rw [h]
        _ = Set.range (J : Fin p → Fin n) := τ.surjective.range_comp _
    have hs : (Finset.univ.image (J : Fin p → Fin n)).card = p := by
      rw [Finset.card_image_of_injective _ J.injective]; simp
    have hIJ : (I : Fin p → Fin n) = J := by
      have e1 : (I : Fin p → Fin n) = (Finset.univ.image (J : Fin p → Fin n)).orderEmbOfFin hs :=
        Finset.orderEmbOfFin_unique hs (fun x => by
          have hx : I x ∈ Set.range (I : Fin p → Fin n) := ⟨x, rfl⟩
          rw [hr] at hx
          obtain ⟨y, hy⟩ := hx
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨y, hy⟩) I.strictMono
      have e2 : (J : Fin p → Fin n) = (Finset.univ.image (J : Fin p → Fin n)).orderEmbOfFin hs :=
        Finset.orderEmbOfFin_unique hs (fun x => by simp) J.strictMono
      exact e1.trans e2.symm
    have hIJ' : I = J := DFunLike.coe_injective hIJ
    subst hIJ'
    have hστ : σ = τ := Equiv.ext fun j => I.injective (congrFun h j)
    rw [hστ]
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hs : (Finset.univ.image f).card = p := by
      rw [Finset.card_image_of_injective _ hf]; simp
    set I := (Finset.univ.image f).orderEmbOfFin hs with hI
    have hex : ∀ j, ∃ k, I k = f j := by
      intro j
      have hm : f j ∈ Set.range (I : Fin p → Fin n) := by
        rw [hI, Finset.range_orderEmbOfFin]; simp
      exact hm
    choose g hg using hex
    have ginj : Function.Injective g := by
      intro a b hab
      apply hf
      rw [← hg a, ← hg b, hab]
    refine ⟨(I, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)), Finset.mem_univ _, ?_⟩
    funext j
    first
      | simp only [Function.comp_apply, Equiv.ofBijective_apply]; exact hg j
      | simp [hg]

theorem cbSorted : CBSorted := by
  unfold CBSorted
  intro R _ p n A B
  classical
  have step1 : (A * B).det = ∑ f : Fin p → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have step2 : ∑ f : Fin p → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det =
      ∑ x : (Fin p ↪o Fin n) × Perm (Fin p),
        (∏ i, B ((⇑x.1 ∘ ⇑x.2) i) i) * (A.submatrix id (⇑x.1 ∘ ⇑x.2)).det := by
    rw [sum_inj_eq_sum_pairs (fun f : Fin p → Fin n => (∏ i, B (f i) i) * (A.submatrix id f).det),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · rfl
    · have hf' : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        apply hf
        intro i j hij
        by_contra hne
        exact hc ⟨i, j, hij, hne⟩
      obtain ⟨i, j, hij, hne⟩ := hf'
      rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij]), mul_zero]
  rw [step1, step2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hsub : ∀ τ : Perm (Fin p),
      (A.submatrix id (⇑J ∘ ⇑τ)).det = Perm.sign τ * (A.submatrix id J).det := by
    intro τ
    have hm : A.submatrix id (⇑J ∘ ⇑τ) = (A.submatrix id J).submatrix id τ := by
      rw [Matrix.submatrix_submatrix]; rfl
    rw [hm, Matrix.det_permute']
  simp only [hsub]
  rw [Matrix.det_apply' (B.submatrix J id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Function.comp_apply]
  ring

end PI.WwMainW
end
end

theorem minor_identity : PI.WwMain.WwMain :=
  PI.WwMainW.wwMain_of PI.WwMainW.evalH PI.WwMainW.lH PI.WwMainW.lLin
    (PI.WwMainW.deXCB_of PI.WwMainW.cbSorted)
end

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

end Formalism.MainNotions.GL3Columns

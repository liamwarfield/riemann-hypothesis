module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
section -- merged from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OrderValuation
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (ι : c.F →+* T.Fr) (_y : IntFr Xo c T ι) : Prop := True

abbrev algVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la

abbrev allVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := Formalism.L2.PjFree.valSet Xo c (trivialClassCondition Xo c) la

def TrivOn (T : CDVR) (ι : c.F →+* T.Fr) : Prop := ∀ a : c.F, a ≠ 0 → vV T.V (ι a) = 0

def ordVal : Set (Rul Xo c → EReal) :=
  {o | ∃ (T : CDVR) (ι : c.F →+* T.Fr) (_ : TrivOn c T ι) (y : IntFr Xo c T ι),
    o = fun f => nval T.V 1 (evI y f)}

variable {Xo c}

def NoCommonZero {κ : Type} (w : κ → Rul Xo c) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → ∃ k, evR Xo c (w k) y ≠ 0

def NoCommonZeroAt (la : HeightOneSpectrum (𝓞 c.F)) {κ : Type} (w : κ → Rul Xo c) : Prop :=
  ∀ v ∈ algVal Xo c la, ∃ k, v (w k) ≠ ⊤

def LeastLe {R κ : Type} (w : κ → R) (ν : ℝ) (v : R → EReal) : Prop := ∃ k, v (w k) ≤ (ν : EReal)

def Comb {R κ : Type} (w : κ → R) (η : R) (ν c' : ℝ) (v : R → EReal) : Prop :=
  0 ≤ v η ∧ (v η ≠ ⊤ → ∃ k, v (w k) ≤ (ν : EReal) + (c' : EReal) * v η)

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)

def TransferInt : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ Formalism.L2.PjFree.cusp Xo c U a n,
    (∀ v ∈ algVal Xo c la, 0 ≤ v F) → (∀ v ∈ allVal Xo c la, 0 ≤ v F) ∧ ∀ o ∈ ordVal Xo c, 0 ≤ o F

def TransferComb (nz : HeightOneSpectrum (𝓞 c.F) → ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE : ℕ),
    Dom aL nL → Dom aE nE → ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ Formalism.L2.PjFree.cusp Xo c U aL nL) → nz la w →
    ∀ η ∈ Formalism.L2.PjFree.cusp Xo c U aE nE, ∀ ν c' : ℝ, 0 ≤ c' →
      (∀ v ∈ algVal Xo c la, Comb w η ν c' v) →
        (∀ v ∈ allVal Xo c la, Comb w η ν c' v) ∧ ∀ o ∈ ordVal Xo c, Comb w η 0 c' o

def TransferLeast (nz : HeightOneSpectrum (𝓞 c.F) → ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ), Dom aL nL →
    ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ Formalism.L2.PjFree.cusp Xo c U aL nL) → nz la w → ∀ ν : ℝ,
      (∀ v ∈ algVal Xo c la, LeastLe w ν v) →
        (∀ v ∈ allVal Xo c la, LeastLe w ν v) ∧ ∀ o ∈ ordVal Xo c, LeastLe w 0 o

def Transfer : Prop :=
  TransferInt Xo c U ∧ TransferComb Xo c U (fun _ _ w => NoCommonZero w) ∧
    TransferLeast Xo c U (fun _ _ w => NoCommonZero w)

def TransferAt : Prop :=
  TransferInt Xo c U ∧ TransferComb Xo c U (fun la _ w => NoCommonZeroAt la w) ∧
    TransferLeast Xo c U (fun la _ w => NoCommonZeroAt la w)

variable {Xo c U}

theorem ordVal_smul {o : Rul Xo c → EReal} (ho : o ∈ ordVal Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    o (a • f) = o f := by
  obtain ⟨T, ι, ht, y, rfl⟩ := ho
  show nval T.V 1 (evI y (a • f)) = nval T.V 1 (evI y f)
  rw [evI_smul]
  exact nval_mul_unit 1 ((map_ne_zero ι).2 ha) (ht a ha) _

end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
end
end

noncomputable section

namespace GlobalTheory.TransferCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.PjFree (valSet algCls cusp Unf regular₂ trivSet isVal_valSet DomWt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36 (algVal allVal ordVal Comb LeastLe Transfer TransferAt TransferInt TransferComb TransferLeast
  ordVal_smul)

section Order

end Order

section Approx

variable {K : Type} [Field K] [NumberField K]

end Approx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Objects

variable (Xo c)

variable {Xo c}

end Objects

section Joint

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)

variable {Xo c U}

variable (Xo c)

theorem evalWD_framed : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_fr (frChartF_of (GlobalTheory.T.chartCoverF_of_sectionBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c))

theorem frBC_framed : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem allTest_framed : AllTest Xo c :=
  GlobalTheory.T.framedPoint_reduced_from_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c



variable (U)

end Joint

end GlobalTheory.TransferCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis
variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_lieSet_iff_entry {X : Mx n} : X ∈ lieSet ε ↔
    ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  simp only [lieSet, Set.mem_setOf_eq, inG, Jm]
  rw [← Matrix.ext_iff]
  simp [mul_diagonal, diagonal_mul, conjTranspose_apply]

theorem smul_unitE_diag_mem (a : Fin n) {c : ℂ} (hc : star c = -c) : c • unitE a a ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

theorem star_invSqrtTwo_mul_I : star (invSqrtTwo * Complex.I) = -(invSqrtTwo * Complex.I) := by
  simp [invSqrtTwo]

theorem kList_mem_lieSet {X : Mx n} (hX : X ∈ kList ε) : X ∈ lieSet ε := by
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, hX⟩
  · exact smul_unitE_diag_mem a (by simp [Complex.star_def])
  · have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    rcases hX with rfl | rfl
    · exact smul_unitE_sub_mem_same hs star_invSqrtTwo
    · exact smul_unitE_add_mem_same hs star_invSqrtTwo_mul_I

theorem pList_mem_lieSet {X : Mx n} (hX : X ∈ pList ε) : X ∈ lieSet ε := by
  simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX
  obtain ⟨p, hp, hX⟩ := hX
  have hs : ε p.1 ≠ ε p.2 := by
    simp [pairs] at hp
    exact hp.2.2
  rcases hX with rfl | rfl
  · exact smul_unitE_add_mem_opp hs star_invSqrtTwo
  · exact smul_unitE_sub_mem_opp hs star_invSqrtTwo_mul_I

theorem bases_mem_lieSet : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε :=
  fun _ _ => ⟨fun i => kList_mem_lieSet (List.get_mem _ i), fun b => pList_mem_lieSet (List.get_mem _ b)⟩

end GlobalTheory.TypeSum.CasBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebraStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet <;> assumption)
end
end

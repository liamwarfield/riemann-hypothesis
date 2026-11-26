module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FinZeta.TrivCount

theorem trivial_isUnitarisable {G : Type} [Group G] :
    IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
      (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
  · intro v w; simp [mul_comm]
  · intro v hv; simpa [Complex.mul_conj] using hv
  · intro g v w; simp

theorem heckeVec_trivial_dosetInd {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) (t : G) :
    heckeVec (Representation.trivial ℂ G ℂ) K (dosetInd ℂ K t) 1 =
      ((Nat.card {a : G ⧸ K // a.out ∈ DoubleCoset.doubleCoset t (K : Set G) K} : ℝ) : ℂ) • 1 := by
  classical
  set D := DoubleCoset.doubleCoset t (K : Set G) K
  have hfin : {a : G ⧸ K | a.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ t).2).subset ?_
    intro a ha
    have h' : a.out ∈ D := ha
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have e : (fun c : G ⧸ K => dosetInd ℂ K t c.out • (Representation.trivial ℂ G ℂ) c.out (1 : ℂ)) =
      Set.indicator {a : G ⧸ K | a.out ∈ D} 1 := by
    funext c
    by_cases h : c.out ∈ D <;> simp [dosetInd, D, h, Set.indicator]
  rw [heckeVec, e, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hc : Nat.card {a : G ⧸ K // a.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {a : G ⧸ K | a.out ∈ D}
  rw [hc]
  simp

theorem hasSum_card_cosets_diag : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r ϖ hϖ T hT
  have hK : IsCommensurated (KGL w (n := r)) := Formalism.UG.Final.GLintComm E w r
  let ρ := Representation.trivial ℂ (GL (Fin r) (w.adicCompletion E)) ℂ
  have hu : IsUnitarisable ρ := trivial_isUnitarisable
  have hfix : (1 : ℂ) ∈ fixed ρ (KGL w (n := r)) := GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w (n := r)), ∃ c : ℂ, heckeVec ρ (KGL w (n := r)) h 1 = c • (1 : ℂ) :=
    fun h _ => ⟨heckeVec ρ (KGL w (n := r)) h 1, by rw [smul_eq_mul, mul_one]⟩
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ ρ hu 1 one_ne_zero hfix heig
  have hc : ∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) 1 =
      (fun d => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈
        DoubleCoset.doubleCoset (T d) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ)) d
        • (1 : ℂ) := fun d => heckeVec_trivial_dosetInd hK (T d)
  refine ⟨B, hbd, ?_⟩
  have key := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r ℂ ρ 1 B hB ϖ hϖ T hT _ hc
  beta_reduce at key
  exact key

end GlobalTheory.FinZeta.TrivCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag | exact GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag | (intros; apply GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.GLTwist

open Formalism.UG (Tj Ov)

section Twist

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ordV_mul {x y : w.adicCompletion E} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.UG.ordV E w (x * y) = Formalism.UG.ordV E w x + Formalism.UG.ordV E w y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_mul,
    WithZero.log_mul hx' hy']
  ring

theorem ordV_zpow {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℤ) : Formalism.UG.ordV E w (ϖ ^ k) = k := by
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_zpow₀, show Valued.v ϖ = _ from hϖ, WithZero.log_zpow,
    show WithZero.log (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) = -1 from rfl]
  simp

def ordDet (g : GL (Fin r) (w.adicCompletion E)) : ℤ := Formalism.UG.ordV E w g.val.det

theorem det_ne_zero (g : GL (Fin r) (w.adicCompletion E)) : g.val.det ≠ 0 :=
  (Matrix.GeneralLinearGroup.det g).ne_zero

theorem ordDet_mul (g h : GL (Fin r) (w.adicCompletion E)) : ordDet (g * h) = ordDet g + ordDet h := by
  rw [ordDet, Units.val_mul, Matrix.det_mul, ordV_mul (det_ne_zero g) (det_ne_zero h)]
  rfl

theorem ordDet_of_mem {k : GL (Fin r) (w.adicCompletion E)} (hk : k ∈ KGL w (n := r)) : ordDet k = 0 := by
  have h : Valued.v k.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hk
  rw [ordDet, GlobalTheory.LGrp.BorelCompletion.ordV_eq, h]
  simp

theorem ordDet_one : ordDet (1 : GL (Fin r) (w.adicCompletion E)) = 0 := ordDet_of_mem (one_mem _)

theorem prod_zpow_eq {ι : Type} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (d : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, ϖ ^ d i = ϖ ^ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ h0]

theorem ordDet_of_diagonal {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {t : GL (Fin r) (w.adicCompletion E)}
    {d : Fin r → ℤ} (ht : t.1 = Matrix.diagonal fun i => ϖ ^ d i) : ordDet t = ∑ i, d i := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  rw [ordDet, ht, Matrix.det_diagonal, prod_zpow_eq h0, ordV_zpow hϖ]

def twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ) :
    Representation ℂ (GL (Fin r) (w.adicCompletion E)) V where
  toFun g := ((z : ℂ) ^ ordDet g) • ρ g
  map_one' := by simp [ordDet_one]
  map_mul' g h := by
    rw [ordDet_mul, zpow_add₀ z.ne_zero, map_mul]
    refine LinearMap.ext fun y => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
    exact smul_comm _ _ _

theorem twistRep_apply (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (g : GL (Fin r) (w.adicCompletion E)) (y : V) : twistRep ρ z g y = ((z : ℂ) ^ ordDet g) • ρ g y := rfl

theorem heckeVec_twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (t : GL (Fin r) (w.adicCompletion E)) (x : V) :
    heckeVec (twistRep ρ z) (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) t) x =
      ((z : ℂ) ^ ordDet t) • heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) t) x := by
  rw [heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ a ∈ KGL w (n := r), ∃ b ∈ KGL w (n := r), c.out = a * t * b
  · obtain ⟨a, ha, b, hb, e⟩ := id hc
    have h : ordDet c.out = ordDet t := by
      rw [e, ordDet_mul, ordDet_mul, ordDet_of_mem ha, ordDet_of_mem hb]
      simp
    rw [twistRep_apply, h, smul_comm]
  · rw [GlobalTheory.WeylGL.dosetInd_of_not hc]
    simp

theorem isSatVecGL_twistRep {ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (z : ℂˣ) : IsSatVecGL w (twistRep ρ z) x (B.map (z * ·)) := by
  refine ⟨hx.1, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  · rw [twistRep_apply, ordDet_of_mem hk, zpow_zero, one_smul]
    exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk
  · have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
    have em : B.map (z * ·) = B.map (· * z) := Multiset.map_congr rfl fun b _ => mul_comm _ _
    have ho : ordDet (GlobalTheory.WeylGL.tor h0 fun i : Fin r => if (i : ℕ) < j then 1 else 0) = j := by
      rw [ordDet_of_diagonal hϖ (GlobalTheory.WeylGL.tor_val h0 _)]
      simp [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hj]
    rw [GlobalTheory.WeylGL.Tj_eq h0, heckeVec_twistRep, ← GlobalTheory.WeylGL.Tj_eq h0, hx.2.2.2 ϖ hϖ j hj, em,
      GlobalTheory.SphGal.satEig_map_mul, ho, zpow_natCast, smul_smul]

end Twist

theorem hasSum_twisted_hecke_eigenvalues : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ (z : ℂˣ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r V _ _ ρ x B hx z ϖ hϖ T hT c hc
  have hc' : ∀ d, heckeVec (twistRep ρ z) (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x =
      ((z : ℂ) ^ (∑ i, d i) * c d) • x := fun d => by
    rw [heckeVec_twistRep, hc d, ordDet_of_diagonal hϖ (hT d), smul_smul]
  obtain ⟨δ, h0, h⟩ := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r V (twistRep ρ z) x _ (isSatVecGL_twistRep hx z) ϖ hϖ T hT _ hc'
  refine ⟨δ, h0, fun X h1 h2 => ?_⟩
  have := h X h1 h2
  rw [Multiset.map_map] at this
  exact this

end GlobalTheory.FinZeta.GLTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_vector_hecke_eigenvalue : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ (z : ℂˣ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.GLTwist.hasSum_twisted_hecke_eigenvalues | exact GlobalTheory.FinZeta.GLTwist.hasSum_twisted_hecke_eigenvalues | (intros; apply GlobalTheory.FinZeta.GLTwist.hasSum_twisted_hecke_eigenvalues <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominated
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominated
open Filter Topology Metric Set

namespace GlobalTheory

theorem gradedSeries_regroup {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (x s : ℂ)
    (hs : HasSum (fun i => c i * x ^ deg i) s) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) s := by
  have h1 := hs.tsum_fiberwise deg
  have e : (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) =
      (fun k => ∑' i : deg ⁻¹' {k}, c i * x ^ deg i) := by
    funext k
    rw [← tsum_mul_right]
    apply tsum_congr
    rintro ⟨i, hi⟩
    simp only [mem_preimage, mem_singleton_iff] at hi
    simp [hi]
  rw [e]
  exact h1

theorem gradedSeries_continue {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (δ ρ : ℝ) (Q : ℂ → ℂ)
    (hδ : 0 < δ) (hQ : DifferentiableOn ℂ Q (ball 0 ρ))
    (h : ∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => c i * (x : ℂ) ^ deg i) (Q x))
    (X : ℂ) (hX : ‖X‖ < ρ) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * X ^ k) (Q X) := by
  set A : ℕ → ℂ := fun k => ∑' i : deg ⁻¹' {k}, c i with hAdef
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A with hpdef
  have hx0 : 0 < δ / 2 := by positivity
  set x0 : NNReal := ⟨δ / 2, hx0.le⟩ with hx0def
  have hrad : (x0 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    have hs := (gradedSeries_regroup deg c _ _ (h (δ / 2) hx0 (by linarith))).summable
    have hs' := summable_norm_iff.mpr hs
    refine hs'.congr fun n => ?_
    simp only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    rfl
  have hF := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hx0)) hrad)
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  have hs0 : 0 < min (δ / 2) ρ := lt_min hx0 hρ
  have hQan : AnalyticOnNhd ℂ Q (ball 0 ρ) := hQ.analyticOnNhd isOpen_ball
  have hmem : ∀ z : ℂ, ‖z‖ < δ / 2 → z ∈ Metric.eball (0 : ℂ) p.radius := by
    intro z hz
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    refine lt_of_lt_of_le ?_ hrad
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hz)
  have hFan : AnalyticOnNhd ℂ p.sum (ball 0 (min (δ / 2) ρ)) := fun z hz =>
    hF.analyticAt_of_mem (hmem z (lt_of_lt_of_le (by simpa using hz) (min_le_left _ _)))
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = Q z := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    have h1 := gradedSeries_regroup deg c _ _ (h x hx.1 (by linarith [hx.2]))
    simp only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact h1.tsum_eq
  have heq : EqOn p.sum Q (ball 0 (min (δ / 2) ρ)) :=
    hFan.eqOn_of_preconnected_of_frequently_eq
      (hQan.mono (ball_subset_ball (min_le_right _ _)))
      (convex_ball _ _).isPreconnected (mem_ball_self hs0) hfreq
  have hQp : HasFPowerSeriesAt Q p 0 :=
    hF.hasFPowerSeriesAt.congr (Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hs0) heq)
  have hR0 : 0 < (‖X‖ + ρ) / 2 := by positivity
  set R : NNReal := ⟨(‖X‖ + ρ) / 2, hR0.le⟩ with hRdef
  have hR : 0 < R := by rw [← NNReal.coe_pos]; exact hR0
  have hdR : DifferentiableOn ℂ Q (closedBall 0 R) :=
    hQ.mono (closedBall_subset_ball (by change (‖X‖ + ρ) / 2 < ρ; linarith))
  have hC := hdR.hasFPowerSeriesOnBall hR
  have hCp : cauchyPowerSeries Q 0 R = p := hC.hasFPowerSeriesAt.eq_formalMultilinearSeries hQp
  rw [hCp] at hC
  have hXm : X ∈ Metric.eball (0 : ℂ) R := by
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; change ‖X‖ < (‖X‖ + ρ) / 2; linarith)
  have := hC.hasSum hXm
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  exact this

theorem gradedSeries_continuation_dominated : ∀ {ι : Type} (deg : ι → ℕ),
    (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ),
    0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) →
    DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) →
    (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧
      HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) →
    ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧
      Summable (fun i => b i * ‖X‖ ^ deg i) := by
  intro ι deg hfin a b C δ ρ P P' hδ hb hab hP hP' h X hX
  have hA := gradedSeries_continue deg a δ ρ P hδ hP (fun x h1 h2 => (h x h1 h2).1) X hX
  have hB := gradedSeries_continue deg (fun i => (b i : ℂ)) δ ρ P' hδ hP'
    (fun x h1 h2 => (h x h1 h2).2) ((‖X‖ : ℝ) : ℂ) (by simpa using hX)
  have hBr : Summable (fun k => (∑' i : deg ⁻¹' {k}, b i) * ‖X‖ ^ k) := by
    rw [← Complex.summable_ofReal]
    refine hB.summable.congr fun k => ?_
    push_cast [Complex.ofReal_tsum]
    rfl
  have hsb : Summable (fun i => b i * ‖X‖ ^ deg i) := by
    rw [← (Equiv.sigmaFiberEquiv deg).summable_iff]
    rw [summable_sigma_of_nonneg (f := (fun i => b i * ‖X‖ ^ deg i) ∘ (Equiv.sigmaFiberEquiv deg))
      (fun _ => mul_nonneg (hb _) (pow_nonneg (norm_nonneg _) _))]
    refine ⟨fun k => ?_, ?_⟩
    · have : Finite {i // deg i = k} := (hfin k).to_subtype
      exact Summable.of_finite
    · refine hBr.congr fun k => ?_
      rw [← tsum_mul_right]
      exact tsum_congr fun y => by
        simp [Equiv.sigmaFiberEquiv, show deg y.1 = k from y.2]
  have hsa : Summable (fun i => a i * X ^ deg i) := by
    refine Summable.of_norm_bounded (hsb.mul_left C) fun i => ?_
    rw [norm_mul, norm_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hab i) (pow_nonneg (norm_nonneg _) _)
  refine ⟨?_, hsb⟩
  have h3 := hsa.hasSum
  have h4 := (gradedSeries_regroup deg a X _ h3).unique hA
  rw [h4] at h3
  exact h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominatedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval : ∀ {ι : Type} (deg : ι → ℕ), (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ), 0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) → DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) → (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧ HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) → ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧ Summable (fun i => b i * ‖X‖ ^ deg i) := by
  first | exact @GlobalTheory.gradedSeries_continuation_dominated | exact GlobalTheory.gradedSeries_continuation_dominated | (intros; apply GlobalTheory.gradedSeries_continuation_dominated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

theorem cartan_existsUnique (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E))
    (hT : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) (g : GL (Fin r) (w.adicCompletion E)) :
    ∃! d : {d : Fin r → ℤ // Antitone d},
      g ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r)) := by
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  have hg : g = k₁ * T a * k₂ := Units.ext (by rw [e, Units.val_mul, Units.val_mul, hT]; rfl)
  refine ⟨⟨a, ha⟩, DoubleCoset.mem_doubleCoset.2 ⟨k₁, hk₁, k₂, hk₂, hg⟩, ?_⟩
  rintro ⟨a', ha'⟩ h
  obtain ⟨k₁', hk₁', k₂', hk₂', e'⟩ := DoubleCoset.mem_doubleCoset.1 h
  rw [hg] at e'
  have e2 : T a' = (k₁'⁻¹ * k₁) * T a * (k₂ * k₂'⁻¹) := by
    calc T a' = k₁'⁻¹ * (k₁' * T a' * k₂') * k₂'⁻¹ := by group
      _ = _ := by rw [← e']; group
  have e3 := congrArg Units.val e2
  rw [Units.val_mul, Units.val_mul, hT, hT] at e3
  exact Subtype.ext (Formalism.UG.Final.CartanUnique E w r ϖ hm hϖ a a' ha ha' _ (mul_mem (inv_mem hk₁') hk₁) _
    (mul_mem hk₂ (inv_mem hk₂')) e3.symm).symm

theorem differentiable_eulerPoly (B : Multiset ℂˣ) (a : ℂ) : Differentiable ℂ fun X : ℂ => eulerPoly B (a * X) := by
  induction B using Multiset.induction_on with
  | empty => simp [eulerPoly]
  | cons b B ih =>
    simp only [eulerPoly_cons]
    exact (by fun_prop : Differentiable ℂ fun X : ℂ => 1 - (b : ℂ) * (a * X)).mul ih

theorem differentiableOn_eulerFac (B : Multiset ℂˣ) (a : ℂ) (R : ℝ)
    (h : ∀ b ∈ B, ∀ X : ℂ, ‖X‖ < R → ‖(b : ℂ) * (a * X)‖ < 1) :
    DifferentiableOn ℂ (fun X => eulerFac B (a * X)) (Metric.ball 0 R) := fun X hX =>
  ((differentiable_eulerPoly B a X).inv
    (eulerPoly_ne_zero fun b hb => h b hb X (by simpa using hX))).differentiableWithinAt

end GlobalTheory.ZetaGL

namespace GlobalTheory.ZetaGL

theorem zeta_sum_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x) := by
  intro H E _ _ w r t hrt z φ hz hφ V _ _ ρ x B hx hB ℓ hℓ
  obtain ⟨Cℓ, hC⟩ := hℓ
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have h0 : ϖ ≠ 0 := SatCompare.ne_zero_of_isUnifV hϖ
  let T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E) := fun d => GlobalTheory.WeylGL.tor h0 d
  have hTv : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i := fun d => rfl
  have hK : IsCommensurated (KGL w (n := r)) := Formalism.UG.Final.GLintComm E w r
  have hmem : ∀ g, dosetInd ℂ (KGL w (n := r)) g ∈ Hecke ℂ (KGL w (n := r)) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  choose c hc using fun d => SatCompare.exists_eigenvalue_GL hx hx _ (hmem (T d))
  let S : (Fin r → ℤ) → Set (GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)) := fun d =>
    {a | a.out ∈ DoubleCoset.doubleCoset (T d) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))}
  have hSfin : ∀ d, (S d).Finite := fun d =>
    (Formalism.UG.P.finite_support_cosets hK (hmem (T d)).2).subset fun a ha => by
      simp only [Set.mem_setOf_eq, dosetInd]; rw [Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; exact one_ne_zero
  have hsumS : ∀ d, ∑ᶠ a ∈ S d, ρ a.out x = c d • x := fun d => by
    rw [← (hc d).1, heckeVec, finsum_mem_def]
    refine finsum_congr fun a => ?_
    by_cases ha : a ∈ S d
    · rw [Set.indicator_of_mem ha, dosetInd, Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp
    · rw [Set.indicator_of_notMem ha, dosetInd, Set.indicator_of_notMem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp

  have hU := fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => cartan_existsUnique E w r hϖ T hTv a.out
  choose D hD using fun a => (hU a).exists
  have hDu : ∀ (d : {d : Fin r → ℤ // Antitone d}) (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)), a ∈ S d.1 → D a = d :=
    fun d a ha => (hU a).unique (hD a) ha
  let e : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) ≃ Σ d : {d : Fin r → ℤ // Antitone d}, S d.1 :=
    { toFun := fun a => ⟨D a, a, hD a⟩
      invFun := fun p => p.2.1
      left_inv := fun a => rfl
      right_inv := fun ⟨d, a, ha⟩ => by
        have h1 : D a = d := hDu d a ha
        subst h1
        rfl }
  haveI : ∀ d, Fintype (S d) := fun d => (hSfin d).fintype
  have hsumF : ∀ d, ∑ a : S d, ρ (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out x = c d • x := fun d => by
    rw [← hsumS d, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]

  set q : ℝ := (qV E w : ℝ) with hqdef
  have hq1 : (1 : ℝ) < q := by
    show (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ); exact_mod_cast one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith
  set M : ℝ := q ^ (((r : ℝ) - 1) / 2) with hM
  set ρ₀ : ℝ := q ^ (-((r : ℝ) - 1)) with hρ₀
  have hM0 : 0 < M := Real.rpow_pos_of_pos hq0 _
  have hMM : M * M * ρ₀ = 1 := by
    rw [hM, hρ₀, ← Real.rpow_add hq0, ← Real.rpow_add hq0,
      show ((r : ℝ) - 1) / 2 + ((r : ℝ) - 1) / 2 + -((r : ℝ) - 1) = 0 by ring, Real.rpow_zero]
  set cq : ℂ := (qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) with hcq
  have hcqn : ‖cq‖ = M := by
    rw [hcq, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (qV_ne_zero w))]
    congr 1; simp
  have hsmall : ∀ β : ℂ, ‖β‖ ≤ M → ∀ X : ℂ, ‖X‖ < ρ₀ → ‖β * (cq * X)‖ < 1 := fun β hβ X hX => by
    rw [norm_mul, norm_mul, hcqn]
    calc ‖β‖ * (M * ‖X‖) ≤ M * (M * ‖X‖) := mul_le_mul_of_nonneg_right hβ (by positivity)
      _ < M * (M * ρ₀) := by gcongr
      _ = 1 := by rw [← mul_assoc, hMM]
  set X₀ : ℝ := q ^ (-(((r : ℝ) + t) / 2)) with hX₀
  have hX₀pos : 0 < X₀ := Real.rpow_pos_of_pos hq0 _
  have hX₀ρ : X₀ < ρ₀ := Real.rpow_lt_rpow_of_exponent_lt hq1 (by
    have : (r : ℝ) ≤ t := by exact_mod_cast hrt
    linarith)
  have hX₀c : ((X₀ : ℝ) : ℂ) = (qV E w : ℂ) ^ (-(((r : ℂ) + t) / 2)) := by
    rw [hX₀, Complex.ofReal_cpow hq0.le]; push_cast; rfl

  let deg : {d : Fin r → ℤ // Antitone d} → ℕ := fun d => (∑ i, |d.1 i|).toNat
  have hdeg : ∀ k, {d | deg d = k}.Finite := fun k => by
    have hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-(k : ℤ)) k).Finite :=
      Set.Finite.pi fun _ => Set.finite_Icc _ _
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun d hd => ?_
    simp only [Set.mem_setOf_eq, deg] at hd
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    have h1 : |d.1 i| ≤ ∑ j, |d.1 j| := Finset.single_le_sum (fun j _ => abs_nonneg (d.1 j)) (Finset.mem_univ i)
    have h2 : ∑ j, |d.1 j| = k := by rw [← hd, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    constructor
    · linarith [neg_abs_le (d.1 i)]
    · linarith [le_abs_self (d.1 i)]

  obtain ⟨δ₁, hδ₁, hs₁⟩ := GlobalTheory.T.satake_vector_hecke_eigenvalue H E w r V ρ x B hx z ϖ hϖ T hTv c (fun d => (hc d).1)
  obtain ⟨B₀, hB₀, δ₂, hδ₂, hs₂⟩ := GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL H E w r ϖ hϖ T hTv
  let a : {d : Fin r → ℤ // Antitone d} → ℂ := fun d => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * ℓ x
  let b : {d : Fin r → ℤ // Antitone d} → ℝ := fun d => (Nat.card (S d.1) : ℝ)
  let P : ℂ → ℂ := fun X => eulerFac (B.map (z * ·)) (cq * X) * eulerFac (B.map fun β => (z * β)⁻¹) (cq * X) *
    (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x
  let P' : ℂ → ℂ := fun X => eulerFac B₀ (cq * X) * eulerFac (B₀.map (·⁻¹)) (cq * X) *
    ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)
  have hC0 : 0 ≤ Cℓ := (norm_nonneg _).trans (hC 1)
  have hab : ∀ d, ‖a d‖ ≤ Cℓ * b d := fun d => by
    have e1 : c d.1 * ℓ x = ∑ y : S d.1, ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hsumF, map_smul, smul_eq_mul]
    have hz' : ‖(z : ℂ) ^ (∑ i, d.1 i)‖ = 1 := by rw [norm_zpow, hz, _root_.one_zpow]
    simp only [a, b]
    rw [mul_assoc, norm_mul, hz', one_mul, e1]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => hC _).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
  have hbnd : ∀ β ∈ B.map (z * ·), ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    simpa [norm_mul, hz] using (hB b hb).1
  have hbnd' : ∀ β ∈ B.map fun β => (z * β)⁻¹, ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    simpa [norm_mul, hz, Units.val_inv_eq_inv_val] using (hB b hb).2
  have hbnd₀ : ∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ M := fun β hβ => (hB₀ β hβ).1
  have hbnd₀' : ∀ β ∈ B₀.map (·⁻¹), ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact (hB₀ b hb).2
  have hpoly : Differentiable ℂ fun X : ℂ => ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2) := by fun_prop
  have hE1 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd β hβ) X hX
  have hE2 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd' β hβ) X hX
  have hE3 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀ β hβ) X hX
  have hE4 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀' β hβ) X hX
  have hP : DifferentiableOn ℂ P (Metric.ball 0 ρ₀) :=
    (((hE1.mul hE2).mul hpoly.differentiableOn).mul_const (ℓ x)).congr fun X _ => by simp only [P, Pi.mul_apply]
  have hP' : DifferentiableOn ℂ P' (Metric.ball 0 ρ₀) :=
    ((hE3.mul hE4).mul hpoly.differentiableOn).congr fun X _ => rfl
  have hser : ∀ X : ℝ, 0 < X → X < min δ₁ δ₂ → HasSum (fun d => a d * (X : ℂ) ^ deg d) (P X) ∧
      HasSum (fun d => (b d : ℂ) * (X : ℂ) ^ deg d) (P' X) := fun X hX h =>
    ⟨by
      have h1 := (hs₁ X hX (lt_of_lt_of_le h (min_le_left _ _))).mul_right (ℓ x)
      rw [show (fun d => a d * (X : ℂ) ^ deg d) = fun d : {d : Fin r → ℤ // Antitone d} =>
        (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat * ℓ x from funext fun d => by
          simp only [a, deg]; ring]
      exact h1,
    hs₂ X hX (lt_of_lt_of_le h (min_le_right _ _))⟩
  obtain ⟨hA, hBs⟩ := GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval deg hdeg a b Cℓ (min δ₁ δ₂) ρ₀ P P' (lt_min hδ₁ hδ₂) (fun d => Nat.cast_nonneg _)
    hab hP hP' hser (X₀ : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hX₀pos.le]; exact hX₀ρ)

  have hφv : ∀ a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r),
      φ a.out = (z : ℂ) ^ (∑ i, (D a).1 i) * (X₀ : ℂ) ^ deg (D a) := fun a => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hD a)
    rw [e1, hφ ϖ hϖ (D a).1 (T (D a).1) (hTv _) k₁ hk₁ k₂ hk₂]
    congr 1
    have hn : ((∑ i, |(D a).1 i| : ℤ) : ℂ) = ((deg (D a) : ℕ) : ℂ) := by
      simp only [deg]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    rw [hn, hX₀c, ← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring

  let f : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) → ℂ := fun a => φ a.out * ℓ (ρ a.out x)
  let u : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) → ℝ := fun a => Cℓ * X₀ ^ deg (D a)
  have hfu : ∀ a, ‖f a‖ ≤ u a := fun a => by
    simp only [f, u]
    rw [hφv, norm_mul, norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hX₀pos.le, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (pow_nonneg hX₀pos.le _)
  have hu : Summable u := by
    rw [← e.symm.summable_iff]
    refine (summable_sigma_of_nonneg fun p => mul_nonneg hC0 (pow_nonneg hX₀pos.le _)).2
      ⟨fun d => Summable.of_finite, ?_⟩
    have h1 : ∀ d : {d : Fin r → ℤ // Antitone d},
        Cℓ * (b d * ‖(X₀ : ℂ)‖ ^ deg d) = ∑' y : S d.1, (u ∘ e.symm) ⟨d, y⟩ := fun d => by
      have h2 : ∀ y : S d.1, (u ∘ e.symm) ⟨d, y⟩ = Cℓ * X₀ ^ deg d := fun y => by
        show Cℓ * X₀ ^ deg (D y.1) = _
        rw [hDu d y.1 y.2]
      simp_rw [h2]
      rw [tsum_const, nsmul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hX₀pos.le]
      simp only [b]
      ring
    exact (hBs.mul_left Cℓ).congr h1
  have hf : Summable f := Summable.of_norm_bounded hu hfu
  have hfib : ∀ d : {d : Fin r → ℤ // Antitone d},
      HasSum (fun y : S d.1 => (f ∘ e.symm) ⟨d, y⟩) (a d * (X₀ : ℂ) ^ deg d) := fun d => by
    have h2 : ∀ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ =
        (z : ℂ) ^ (∑ i, d.1 i) * (X₀ : ℂ) ^ deg d * ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out x) :=
      fun y => by
        show φ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out * _ = _
        rw [hφv, hDu d y.1 y.2]
        rfl
    have h3 : ∑ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ = a d * (X₀ : ℂ) ^ deg d := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum, ← map_sum, hsumF, map_smul, smul_eq_mul]
      simp only [a]
      ring
    exact h3 ▸ hasSum_fintype _
  have heq : ∑' a, f a = P X₀ := (((e.symm.hasSum_iff).2 hf.hasSum).sigma hfib).unique hA
  have hfin := hf.hasSum
  rw [heq] at hfin

  have hcX : cq * (X₀ : ℂ) = npow w (-((1 + (t : ℂ)) / 2)) := by
    have hqC : (qV E w : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
    rw [hcq, hX₀c, ← Complex.cpow_add _ _ hqC]
    show ((qV E w : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
    congr 1
    ring
  have hX2 : (X₀ : ℂ) ^ 2 = ((qV E w : ℂ) ^ (r + t))⁻¹ := by
    rw [hX₀c, ← Complex.cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(((r : ℂ) + t) / 2) = -(((r + t : ℕ) : ℂ)) by push_cast; ring,
      Complex.cpow_neg, Complex.cpow_natCast]
  have hprod : ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X₀ : ℂ) ^ 2) =
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹) := by
    have hqC : (qV E w : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
    refine Finset.prod_nbij' (fun i => r + t - i) (fun j => r + t - j) (fun i hi => ?_) (fun j hj => ?_)
      (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)
    · simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_coe] at hi ⊢; omega
    · simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_coe] at hj ⊢; omega
    · simp only [Finset.mem_range, Finset.mem_coe] at hi; omega
    · simp only [Finset.mem_Ioc, Finset.mem_coe] at hj; omega
    · simp only [Finset.mem_range, Finset.mem_coe] at hi
      have hp : (qV E w : ℂ) ^ (r + t) = (qV E w : ℂ) ^ (r + t - i) * (qV E w : ℂ) ^ i := by
        rw [← pow_add]; congr 1; omega
      rw [hX2, hp]
      congr 1
      field_simp
  have hval : P X₀ = eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) *
      eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) *
      (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x := by
    simp only [P]
    rw [hcX, hprod]
  rw [hval] at hfin
  exact hfin

end GlobalTheory.ZetaGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_zeta_sum_GL_cosets : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x) := by
  first | exact @GlobalTheory.ZetaGL.zeta_sum_GL | exact GlobalTheory.ZetaGL.zeta_sum_GL | (intros; apply GlobalTheory.ZetaGL.zeta_sum_GL <;> assumption)
end

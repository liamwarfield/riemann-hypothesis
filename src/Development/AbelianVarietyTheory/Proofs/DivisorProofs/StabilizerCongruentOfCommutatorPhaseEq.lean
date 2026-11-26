module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEq
open scoped Pointwise nonZeroDivisors
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.PhaseCong

variable {D : D7}

def skewCoef (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {e | ∀ b ∈ D.host.𝔟, ∀ c ∈ D.host.conj • 𝔪, ∃ m ∈ 𝔪,
    algebraMap (𝓞 D.host.E) D.host.E m = e * algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c}
  zero_mem' := fun _ _ _ _ => ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro e f he hf b hb c hc
    obtain ⟨m, hm, h1⟩ := he b hb c hc
    obtain ⟨n, hn, h2⟩ := hf b hb c hc
    exact ⟨m + n, add_mem hm hn, by rw [map_add (f := _), h1, h2]; ring⟩
  smul_mem' := by
    rintro s e he b hb c hc
    obtain ⟨m, hm, h1⟩ := he b hb c hc
    exact ⟨s * m, Ideal.mul_mem_left _ _ hm, by rw [map_mul, h1, Algebra.smul_def]; ring⟩

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem entries_of_homL {𝔪 : Ideal (𝓞 D.host.E)} {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ homL D (stdL D a) (skewLat D 𝔪 d)) (i : Fin d) (j : Fin a) :
    A i j ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have hs : (Pi.single j 1 : Fin a → D.host.E) ∈ stdL D a := by
      simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
      intro k
      rw [Pi.single_apply]
      split_ifs
      exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
    have := hA _ hs
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff] at this
    simpa using this i
  | zero => exact Submodule.zero_mem _
  | add A B _ _ hA hB => exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact Submodule.smul_mem _ c hA

theorem entries_of_YYl {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) (i : Fin d) (j : Fin a) : A i j ∈ skewCoef D 𝔪 := by
  have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => h𝔪 (by
      have h' := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
      simpa using h')
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hB
    intro b hb c hc
    have h1 : t * algebraMap (𝓞 D.host.E) D.host.E b ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      (FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩)
    have h2 : A i j * algebraMap (𝓞 D.host.E) D.host.E c ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      (FractionalIdeal.mem_div_iff_of_ne_zero hne).1 (entries_of_homL hA i j) _
        ((FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    obtain ⟨m, hm, hm'⟩ := (FractionalIdeal.mem_coeIdeal _).1 h2
    refine ⟨o * m, Ideal.mul_mem_left _ _ hm, ?_⟩
    rw [map_mul, ho, hm', Matrix.smul_apply, smul_eq_mul]
    ring
  | zero => exact (skewCoef D 𝔪).zero_mem
  | add A B _ _ hA hB => exact (skewCoef D 𝔪).add_mem hA hB
  | smul c A _ hA =>
    rw [Matrix.smul_apply]
    exact (skewCoef D 𝔪).smul_mem c hA

theorem entries_of_mem {δ : ℂ} (hc : Crv D ⊤ δ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ}
    (z : Matrix (Fin d) (Fin a) D.host.E)
    (hz : pt D (tor0 D ⊤ δ) δ z ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) (i : Fin d) (j : Fin a) :
    z i j ∈ skewCoef D 𝔪 := by
  let S : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
    { carrier := {z | ∀ i j, z i j ∈ skewCoef D 𝔪}
      zero_mem' := fun _ _ => (skewCoef D 𝔪).zero_mem
      add_mem' := fun ha hb i j => (skewCoef D 𝔪).add_mem (ha i j) (hb i j)
      neg_mem' := fun ha i j => (skewCoef D 𝔪).neg_mem (ha i j) }
  have hle : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ≤ S.map (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
    have hint : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
      (RingOfIntegers.isIntegral_coe c).algebraMap (B := D.host.E)
    have := (skewCoef D 𝔪).smul_mem (⟨_, hint⟩ : 𝓞 D.host.E) (entries_of_YYl h𝔪 hA i j)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact this
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc).2.1
  obtain ⟨z', hz', e⟩ := hle hz
  have : z' = z := GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ hδ a d e
  exact this ▸ hz' i j

theorem mem_of_int {𝔪 : Ideal (𝓞 D.host.E)} (h1 : IsCoprime 𝔪 (D.host.conj • 𝔪)) (h2 : IsCoprime 𝔪 D.host.𝔟)
    {e : D.host.E} (he : e ∈ skewCoef D 𝔪) (hi : IsIntegral ℤ e) :
    ∃ m ∈ 𝔪, algebraMap (𝓞 D.host.E) D.host.E m = e := by
  obtain ⟨μ, hμ, β, hβ, hμβ⟩ := Ideal.isCoprime_iff_exists.1 h2
  obtain ⟨μ', hμ', ν, hν, hμν⟩ := Ideal.isCoprime_iff_exists.1 h1
  obtain ⟨m, hm, hme⟩ := he β hβ ν hν
  let o : 𝓞 D.host.E := ⟨e, hi⟩
  have ho : algebraMap (𝓞 D.host.E) D.host.E o = e := rfl
  refine ⟨o * μ + o * β * μ' + m, add_mem (add_mem (Ideal.mul_mem_left _ _ hμ) (Ideal.mul_mem_left _ _ hμ')) hm, ?_⟩
  have ea : algebraMap (𝓞 D.host.E) D.host.E μ + algebraMap (𝓞 D.host.E) D.host.E β = 1 := by
    rw [← map_add (f := _), hμβ, map_one]
  have eb : algebraMap (𝓞 D.host.E) D.host.E μ' + algebraMap (𝓞 D.host.E) D.host.E ν = 1 := by
    rw [← map_add (f := _), hμν, map_one]
  rw [map_add (f := _), map_add (f := _), hme, map_mul, map_mul, map_mul, ho]
  linear_combination e * ea + e * algebraMap (𝓞 D.host.E) D.host.E β * eb

theorem im_int_of_kap_eq (T : Tor D) {N N' : ℕ} (u u' y : VC D N N')
    (h : Formalism.MainNotions.TaylorLogMetric.kap D T u y = Formalism.MainNotions.TaylorLogMetric.kap D T u' y) : ∃ m : ℤ, (Hf D T (u - u') y).im = m := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨-n, ?_⟩
  have e : Hf D T u y = Hf D T (u - u') y + Hf D T u' y := by rw [← VacMove.hf_add_left, sub_add_cancel]
  have e2 : (Hf D T u y).im = (Hf D T (u - u') y).im + (Hf D T u' y).im := by rw [e, Complex.add_im]
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 : ((Hf D T u y).im : ℂ) = (Hf D T u' y).im - n := by
    apply mul_left_cancel₀ hpi
    linear_combination -hn
  have h4 : (Hf D T u y).im = (Hf D T u' y).im - n := by exact_mod_cast h3
  push_cast
  linarith

end GlobalTheory.FunObj.StdDatum.PhaseCong

namespace GlobalTheory.FunObj.StdDatum.PhaseCong

variable {D : D7}

theorem alg1 {G : Type*} [AddCommGroup G] (p q u v : G) : p - q = (v - q) - (u - p) + (u - v) := by abel

theorem alg2 {G : Type*} [AddCommGroup G] (s t w : G) : w = s - t + w - s + t := by abel

theorem mem_OhE_of_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) : y ∈ OhE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, -, s, hs, rfl⟩ := hy
    exact mul_mem ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (RingOfIntegers.isIntegral_coe b)) hs
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | neg _ _ h => exact neg_mem h

theorem hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h


set_option maxHeartbeats 2000000 in
theorem cong_of_kap_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → ∀ {a d : ℕ}, a ≤ d → ∀ (r r' : GA D a), r ∈ intG D a → r' ∈ intG D a → ∀ x x' : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) → pt D (tor0 D ⊤ δ) δ x' ∈ (La0 D (tor0 D ⊤ δ) a d) → (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ i j, (x'.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) y = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x') y) → CongOne D 𝔪 (r⁻¹ * r') := by
  intro D δ hc 𝔪 h𝔪 hcop hb a d had r r' hr hr' x x' _ _ hx hx' hk
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D a), GlobalTheory.T.selfDualSkewIdealLattice_isSelfDual D 𝔪 d h𝔪, rfl⟩
  have hpt : pt D (tor0 D ⊤ δ) δ (x - x') = pt D (tor0 D ⊤ δ) δ x - pt D (tor0 D ⊤ δ) δ x' :=
    map_sub (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) x x'
  have hmem : pt D (tor0 D ⊤ δ) δ (x - x') ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
    refine (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hc a d _ kp).2.2.2.1 _ fun y hy => ?_
    rw [hpt]
    exact im_int_of_kap_eq _ _ _ y (hk y hy)
  have hz := entries_of_mem hc h𝔪 (x - x') hmem
  set B := (unitBlock D 0 a d).map (inc D) with hB
  set R := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hRdef
  set R' := (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR'def
  set P' := (((r' : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hP'def
  have hri := (mem_intG r).1 hr
  have hri' := (mem_intG r').1 hr'
  have hR : ∀ i j, R i j ∈ OhE D := fun i j => (hri i j).2
  have hR' : ∀ i j, R' i j ∈ OhE D := fun i j => (hri' i j).2
  have hP' : ∀ i j, P' i j ∈ OhE D := fun i j => (hri' i j).1
  have hBi : ∀ i k, B i k ∈ OhE D := fun i k => by
    simp only [hB, Matrix.map_apply, unitBlock, Matrix.of_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _

  have hrow : ∀ (i : Fin d) (j : Fin a), (B * (R - R')) i j ∈ hatId D 𝔪 := by
    intro i j
    have e : (B * (R - R')) i j = (x'.map (inc D) - B * R') i j - (x.map (inc D) - B * R) i j + inc D ((x - x') i j) := by
      simp only [Matrix.mul_sub, Matrix.sub_apply, Matrix.map_apply, map_sub]
      exact alg1 _ _ _ _
    have hint : (B * (R - R')) i j ∈ OhE D := by
      rw [Matrix.mul_apply]
      exact sum_mem fun k _ => mul_mem (hBi i k) (by rw [Matrix.sub_apply]; exact sub_mem (hR k j) (hR' k j))
    have hzi : inc D ((x - x') i j) ∈ OhE D := by
      have : inc D ((x - x') i j) = (B * (R - R')) i j - (x'.map (inc D) - B * R') i j + (x.map (inc D) - B * R) i j := by
        rw [e]; exact alg2 _ _ _
      rw [this]
      exact add_mem (sub_mem hint (mem_OhE_of_hatId (hx' i j))) (mem_OhE_of_hatId (hx i j))
    obtain ⟨m, hm, hme⟩ := mem_of_int hcop hb (hz i j) ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 hzi)
    have hzm : inc D ((x - x') i j) ∈ hatId D 𝔪 :=
      AddSubgroup.subset_closure ⟨m, hm, 1, one_mem _, by rw [mul_one, ← hme]⟩
    rw [e]
    exact add_mem (sub_mem (hx' i j) (hx i j)) hzm

  have hdiff : ∀ i j : Fin a, (R - R') i j ∈ hatId D 𝔪 := by
    intro i j
    have e : (B * (R - R')) ⟨i.1, lt_of_lt_of_le i.2 had⟩ j = (R - R') i j := by
      simp only [hB, Matrix.mul_apply, Matrix.map_apply, unitBlock, Matrix.of_apply, zero_add]
      simp [apply_ite (inc D), Fin.val_inj]
    rw [← e]
    exact hrow _ j
  have e1 : R' * P' = 1 := by
    simp only [hR'def, hP'def, Subgroup.coe_inv]
    exact Units.inv_mul _
  intro i j
  have e2 : (((r⁻¹ * r' : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - 1 = (R - R') * P' := by
    rw [Matrix.sub_mul, e1]
    rfl
  rw [e2, Matrix.mul_apply]
  exact sum_mem fun k _ => by rw [mul_comm]; exact hatId_mul (hP' k j) (hdiff i k)

end GlobalTheory.FunObj.StdDatum.PhaseCong

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEqStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → ∀ {a d : ℕ}, a ≤ d → ∀ (r r' : GA D a), r ∈ intG D a → r' ∈ intG D a → ∀ x x' : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) → pt D (tor0 D ⊤ δ) δ x' ∈ (La0 D (tor0 D ⊤ δ) a d) → (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ i j, (x'.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) → (∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) y = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x') y) → CongOne D 𝔪 (r⁻¹ * r') := by
  first | exact @GlobalTheory.FunObj.StdDatum.PhaseCong.cong_of_kap_eq | exact GlobalTheory.FunObj.StdDatum.PhaseCong.cong_of_kap_eq | (intros; apply GlobalTheory.FunObj.StdDatum.PhaseCong.cong_of_kap_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSigna
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSigna
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ArchCoordsD


open GlobalTheory.FockVacuum in
theorem herm_rot_pos {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b *
      star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith


open GlobalTheory.FockVacuum in
theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_rot_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoordsD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSignaStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoordsD.exists_coords | exact GlobalTheory.ArchCoordsD.exists_coords | (intros; apply GlobalTheory.ArchCoordsD.exists_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThetaDiagUnfold

theorem dot_sumElim {R : Type} [CommSemiring R] {κ : Type} [Fintype κ] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem integral_thetaSum_schr_diag : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (κ ⊕ κ), ∀ x : κ → AF F,
      ∫ y in 𝓕₁, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) ∂μ =
        (μ.real 𝓕₁ : ℂ) * ∑' η : κ → F, Φ (Sum.elim ((fun i => algebraMap F (AF F) (η i)) + x)
          ((fun i => algebraMap F (AF F) (η i)) + x)) := by
  intro F _ _ ψ hψ κ _
  intro μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ ⊕ κ → F) → ℂ, a = fun ξ => Φ ((fun i => algebraMap F (AF F) (ξ i)) + Sum.elim x x) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : (κ ⊕ κ → F) → (κ → F), d = fun ξ => ξ ∘ Sum.inl - ξ ∘ Sum.inr := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F (Sum.elim x x) hΦ)
    subst ha
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hpt : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) =
      ∑' ξ, a ξ * e (d ξ) y := by
    intro y
    unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    refine tsum_congr fun ξ => ?_
    have hsplit : (fun i => algebraMap F (AF F) (ξ i)) =
        Sum.elim (emb (ξ ∘ Sum.inl)) (emb (ξ ∘ Sum.inr)) := by
      funext s; cases s <;> simp [hemb]
    have hx0 : Sum.elim x x ⬝ᵥ Sum.elim y (-y) = 0 := by
      rw [dot_sumElim, dotProduct_neg, add_neg_cancel]
    have hdot : (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ Sum.elim y (-y) = emb (d ξ) ⬝ᵥ y := by
      rw [hsplit, dot_sumElim, dotProduct_neg, hd]
      have : emb (ξ ∘ Sum.inl - ξ ∘ Sum.inr) = emb (ξ ∘ Sum.inl) - emb (ξ ∘ Sum.inr) := by
        rw [hemb]; funext i; simp [map_sub]
      rw [this, sub_dotProduct, sub_eq_add_neg]
    simp only
    rw [hx0, mul_zero, add_zero, hdot, ha, he]
    ring
  have hFint : ∀ ξ : κ ⊕ κ → F, Integrable (fun y => a ξ * e (d ξ) y) (μ.restrict 𝓕₁) := fun ξ =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ = ‖a ξ‖ * μ.real 𝓕₁ := by
    intro ξ
    simp only [norm_mul, he_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ : κ ⊕ κ → F => ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, a ξ * e (d ξ) y ∂μ =
      if d ξ = 0 then (μ.real 𝓕₁ : ℂ) * a ξ else 0 := by
    intro ξ
    rw [integral_const_mul, horth]
    split_ifs <;> ring
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [hFval]
  have hinj : Function.Injective (fun η : κ → F => (Sum.elim η η : κ ⊕ κ → F)) := fun η η' h => by
    funext i; exact congrFun h (Sum.inl i)
  rw [← hinj.tsum_eq, ← tsum_mul_left]
  · refine tsum_congr fun η => ?_
    have hd0 : d (Sum.elim η η) = 0 := by rw [hd]; funext i; simp
    rw [if_pos hd0, ha]
    dsimp only
    congr 2
    funext s; cases s <;> simp
  · intro ξ hξ
    have h0 : d ξ = 0 := by
      by_contra h; exact hξ (if_neg h)
    refine ⟨ξ ∘ Sum.inl, ?_⟩
    funext s
    cases s with
    | inl i => rfl
    | inr i =>
      have := congrFun h0 i
      rw [hd] at this
      simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, sub_eq_zero] at this
      simpa using this

end GlobalTheory.ThetaDiagUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (κ ⊕ κ), ∀ x : κ → AF F,
      ∫ y in 𝓕₁, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) ∂μ =
        (μ.real 𝓕₁ : ℂ) * ∑' η : κ → F, Φ (Sum.elim ((fun i => algebraMap F (AF F) (η i)) + x)
          ((fun i => algebraMap F (AF F) (η i)) + x)) := by
  first | exact @GlobalTheory.ThetaDiagUnfold.integral_thetaSum_schr_diag | exact GlobalTheory.ThetaDiagUnfold.integral_thetaSum_schr_diag | (intros; apply GlobalTheory.ThetaDiagUnfold.integral_thetaSum_schr_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminorms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminorms
open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem seminorm_finset_sum_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℂ (SchwartzMap E ℂ)) (u : Finset ℕ) (t : ℕ → SchwartzMap E ℂ) :
    p (∑ j ∈ u, t j) ≤ ∑ j ∈ u, p (t j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add p _ _).trans (by gcongr)

theorem summable_of_summable_seminorm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℕ → SchwartzMap E ℂ)
    (h : ∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) : Summable t := by
  classical
  have iteratedFDeriv_sub' (f g : (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
    have hf : ContDiff ℝ n f := f.smooth n
    have hg : ContDiff ℝ n g := g.smooth n
    rw [show (⇑(f - g) : E → ℂ) = ⇑f - ⇑g from rfl]
    exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt
  
  have cauchy_seminorm {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    have h := ((schwartz_withSeminorms ℝ E ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
    obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
    refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
    have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
    simpa [schwartzSeminormFamily] using this
  
  let limD (u : ℕ → (SchwartzMap E ℂ)) (n : ℕ) (x : E) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ :=
    limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x
  
  have tendsto_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [dist_eq_norm, ← iteratedFDeriv_sub']
    have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
    simp only [pow_zero, one_mul] at this
    exact this.trans_lt (hN a ha b hb)
  
  have key {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
    refine ⟨N, fun j hj x => ?_⟩
    have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
      ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
    refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
    rw [← iteratedFDeriv_sub']
    exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le
  
  have tendstoUniformly_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
    have := hN j hj x
    rw [pow_zero, one_mul] at this
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  
  have continuous_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) :
      Continuous (limD u n) :=
    (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
      ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently
  
  have hasFDerivAt_limD {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (m : ℕ) (x : E) :
      HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
    refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
      (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (⇑(u j))) y)
      (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
        (tendstoUniformly_limD hu (m + 1))
    · intro j y
      exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt
  
  have hasFTaylorSeries {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
        (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ E ℂ)) := by
    exact { zero_eq := fun _ => rfl
            fderiv := fun m _ x => hasFDerivAt_limD hu m x
            cont := fun m _ => continuous_limD hu m }
  
  let limMap (u : ℕ → (SchwartzMap E ℂ)) (hu : CauchySeq u) : (SchwartzMap E ℂ) := by
    refine { toFun := fun x => (limD u 0 x).curry0
             smooth' := (hasFTaylorSeries hu).contDiff
             decay' := ?_ }
    intro k n
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

  have iteratedFDeriv_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) (n : ℕ) (x : E) :
      iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
    ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm
  
  have tendsto_limMap {u : ℕ → (SchwartzMap E ℂ)} (hu : CauchySeq u) :
      Tendsto u atTop (𝓝 (limMap u hu)) := by
    rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
    rintro ⟨k, n⟩ ε hε
    obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
    rw [iteratedFDeriv_sub', iteratedFDeriv_limMap hu]
    exact hN j hj x
  
  haveI : CompleteSpace (SchwartzMap E ℂ) := by
    haveI : (uniformity (SchwartzMap E ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩
  rw [summable_iff_vanishing]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := (schwartz_withSeminorms ℂ E ℂ).mem_nhds_iff 0 U |>.1 hU
  have hr' : 0 < r / 2 := half_pos hr
  have hS : ∀ i : ℕ × ℕ, ∃ S : Finset ℕ, ∀ u : Finset ℕ, Disjoint u S →
      ∑ j ∈ u, SchwartzMap.seminorm ℂ i.1 i.2 (t j) ∈ Set.Iio (r / 2) :=
    fun i => summable_iff_vanishing.1 (h i.1 i.2) _ (Iio_mem_nhds (by simpa using hr'))
  choose S hS using hS
  refine ⟨s.biUnion S, fun u hu => hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine lt_of_le_of_lt (Seminorm.finset_sup_apply_le hr'.le fun i hi => ?_) (half_lt_self hr)
  refine (seminorm_finset_sum_le _ u t).trans ?_
  exact (hS i u (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem S hi) hu)).le

end GlobalTheory.ConvSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminormsStatement
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  first | exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm | exact GlobalTheory.ConvSeries.summable_of_summable_seminorm | (intros; apply GlobalTheory.ConvSeries.summable_of_summable_seminorm <;> assumption)
end
end

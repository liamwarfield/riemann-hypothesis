module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegment
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegment
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

private theorem multiset_range_map_eq_sum_singleton (f : ℕ → ℂˣ) (N : ℕ) :
    (Multiset.range N).map f = ∑ j ∈ Finset.range N, ({f j} : Multiset ℂˣ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ← ih, add_comm, Multiset.singleton_add]

theorem str_eq_sum (q : ℂˣ) (t : ℤ) :
    str q t = ∑ j ∈ Finset.range t.toNat, ({q ^ (2 * (j : ℤ) - (t - 1))} : Multiset ℂˣ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str]
  exact multiset_range_map_eq_sum_singleton _ _

theorem str_even (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) := by
  rw [str_eq_sum, show t.toNat = d + d by omega, Finset.sum_range_add]
  conv_lhs => arg 2; rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d := Finset.mem_range.mp hk
  rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
  congr 3 <;> omega

theorem str_odd (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d + 1) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) + {1} := by
  rw [str_eq_sum, show t.toNat = d + (d + 1) by omega, Finset.sum_range_add, Finset.sum_range_succ']
  conv_lhs => arg 2; arg 1; rw [← Finset.sum_range_reflect]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < d := Finset.mem_range.mp hk
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
    congr 3 <;> omega
  · rw [← zpow_zero q]
    congr 2
    omega

theorem lift_key (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') :
    ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      Multiset.replicate (n' % 2) ((-1 : ℂˣ) ^ n)⁻¹ =
    Multiset.replicate (n % 2) ((-1 : ℂˣ) ^ n')⁻¹ + str q ((n' : ℤ) - n) := by
  have hsq : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m) = 1 := fun m => by rw [pow_mul, neg_one_sq, one_pow]
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩ <;> rcases Nat.even_or_odd' n' with ⟨b, rfl | rfl⟩
  · rw [str_even q (b - a) _ (by omega), show 2 * b / 2 - 2 * a / 2 = b - a by omega,
      show 2 * b % 2 = 0 by omega, show 2 * a % 2 = 0 by omega]
    simp only [Multiset.replicate_zero, add_zero, zero_add]
  · rw [str_odd q (b - a) _ (by omega), show (2 * b + 1) / 2 - 2 * a / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show 2 * a % 2 = 0 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, zero_add]
  · have e0 : ((2 * b : ℕ) : ℤ) - ((2 * a + 1 : ℕ) : ℤ) - 1 - 2 * ((b - a - 1 : ℕ) : ℤ) = 0 := by omega
    rw [str_odd q (b - a - 1) _ (by omega), show 2 * b / 2 - (2 * a + 1) / 2 = b - a - 1 + 1 by omega,
      Finset.sum_range_succ, e0, neg_zero, zpow_zero,
      show 2 * b % 2 = 0 by omega, show (2 * a + 1) % 2 = 1 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, add_zero, Multiset.insert_eq_cons,
      ← Multiset.singleton_add]
    abel
  · have hodd : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m + 1) = -1 := fun m => by rw [pow_succ, hsq, one_mul]
    rw [str_even q (b - a) _ (by omega), show (2 * b + 1) / 2 - (2 * a + 1) / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show (2 * a + 1) % 2 = 1 by omega, hodd, hodd, add_comm]

private theorem sum_pi_single_one_smul {ι : Type} (s : Finset ι) (f : ι → ℂˣ) :
    ∑ i ∈ s, ({f i} : Multiset ℂˣ) = s.val.map f := by
  rw [Finset.sum_eq_multiset_sum]
  generalize s.val = m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.singleton_add]


open GlobalTheory.LGrp (bcParam) in
theorem bcParam_map_mul (c : ℂˣ) (N : ℕ) (γ : Fin (N / 2) → ℂˣ) :
    (bcParam N γ).map (fun x => c * x) =
      ∑ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) + Multiset.replicate (N % 2) c := by
  have hpair : ∀ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) = {c * γ i} + {c * (γ i)⁻¹} := fun i => by
    rw [Multiset.insert_eq_cons, Multiset.singleton_add]
  simp only [hpair, Finset.sum_add_distrib, sum_pi_single_one_smul, bcParam, Multiset.map_add (f := _), Multiset.map_map,
    Multiset.map_replicate, mul_one]
  rfl

theorem neg_one_pow_inv (k : ℕ) : ((-1 : ℂˣ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg_one]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂˣ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem pair_inv_mul_eq_of_mul_self_eq_one (s t a : ℂˣ) (hs : s * s = 1) (ht : t * t = 1) :
    ({s⁻¹ * (s * t * a⁻¹), s⁻¹ * (s * t * a⁻¹)⁻¹} : Multiset ℂˣ) = {t⁻¹ * a, t⁻¹ * a⁻¹} := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : s⁻¹ * (s * t * a⁻¹) = t⁻¹ * a⁻¹ := by rw [mul_assoc, inv_mul_cancel_left, ht']
  have e2 : s⁻¹ * (s * t * a⁻¹)⁻¹ = t⁻¹ * a := by
    simp only [mul_inv, inv_inv]
    rw [hs', ← mul_assoc, ← mul_assoc, hs, one_mul]
  rw [e1, e2, Multiset.pair_comm]

theorem bcParam_liftPar (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') (α : Fin (n / 2) → ℂˣ) :
    (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) =
      (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  have hD : n' / 2 - n / 2 + n / 2 = n' / 2 := by omega
  have hs : (-1 : ℂˣ) ^ n * (-1) ^ n = 1 := neg_one_pow_mul_self n
  have hsum : (∑ i : Fin (n' / 2), ({((-1 : ℂˣ) ^ n)⁻¹ * liftPar q n n' α i,
        ((-1 : ℂˣ) ^ n)⁻¹ * (liftPar q n n' α i)⁻¹} : Multiset ℂˣ)) =
      ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      ∑ i : Fin (n / 2), ({((-1 : ℂˣ) ^ n')⁻¹ * α i, ((-1 : ℂˣ) ^ n')⁻¹ * (α i)⁻¹} : Multiset ℂˣ) := by
    rw [← Equiv.sum_comp (finCongr hD), Fin.sum_univ_add, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.castAdd (n / 2) i)) =
          (-1) ^ n * q ^ ((n' : ℤ) - n - 1 - 2 * ((i : ℕ) : ℤ)) := by
        unfold liftPar
        rw [dite_eq_left (by simp)]
        simp
      rw [hL, mul_inv, inv_mul_cancel_left, neg_one_pow_inv, ← mul_assoc, hs, one_mul, ← _root_.zpow_neg]
    · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.natAdd (n' / 2 - n / 2) j)) =
          (-1) ^ n * (-1) ^ n' * (α (Fin.revPerm j))⁻¹ := by
        unfold liftPar
        rw [dite_eq_right (by simp), pow_add]
        congr 3
        ext
        simp
        omega
      rw [hL]
      exact pair_inv_mul_eq_of_mul_self_eq_one _ _ _ hs (neg_one_pow_mul_self n')
  rw [bcParam_map_mul, bcParam_map_mul, hsum, add_assoc _ (Multiset.replicate (n % 2) _), ← lift_key q n n' h]
  abel

end GlobalTheory.SphTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegmentStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment : ∀ (q : ℂˣ) (n n' : ℕ), n ≤ n' → ∀ α : Fin (n / 2) → ℂˣ, (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) = (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  first | exact @GlobalTheory.SphTheta.bcParam_liftPar | exact GlobalTheory.SphTheta.bcParam_liftPar | (intros; apply GlobalTheory.SphTheta.bcParam_liftPar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionHomMulEmbeddedAnisotropic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacHom

variable {D : D7}

section Inv

variable {S T : HSp D}

theorem symplOH_mul_mt (a b : WO S T) (g : GA D S) :
    symplOH S T (a ⬝ mt S g) (b ⬝ mt S g) = symplOH S T a b := by
  have h1 : mt S g ⬝ mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  rw [mt_inv] at h1
  have key : mt S g ⬝ (giA S ⬝ adj (mt S g)) = giA S := by
    have e : mt S g ⬝ (giA S ⬝ adj (mt S g)) = mt S g ⬝ (giA S ⬝ (adj (mt S g) ⬝ gA S)) ⬝ giA S := by
      simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]
    rw [e, h1, Matrix.one_mul]
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul]
  have e2 : giA S ⬝ (adj (mt S g) ⬝ adj b ⬝ (gA T ⬝ (a ⬝ mt S g))) =
      (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) ⬝ mt S g := by simp only [Matrix.mul_assoc]
  have e3 : mt S g ⬝ (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) =
      (mt S g ⬝ (giA S ⬝ adj (mt S g))) ⬝ (adj b ⬝ (gA T ⬝ a)) := by simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, e3, key]

theorem symplOH_mul_mt_right (a b : WO S T) (g : GA D S) :
    symplOH S T a (b ⬝ mt S g) = symplOH S T (a ⬝ mt S g⁻¹) b := by
  conv_lhs => rw [← symplOH_mul_mt a (b ⬝ mt S g) g⁻¹]
  rw [Matrix.mul_assoc b, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

end Inv

section FinalTheorems

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)

theorem extX_mul (n : GA D S) : d.extX T x ⬝ mt S n =
    d.extX T (d.extX T x ⬝ mt S n ⬝ d.jX) + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  rw [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, HypDec.extX_apply, ptS, HypDec.extX_apply]
  conv_lhs => rw [← Matrix.mul_one (x ⬝ d.pX ⬝ mt S n), ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

variable {T x}

theorem extX_mul_jX (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x) {n : GA D S} (hn : n ∈ flagN d) :
    d.extX T x ⬝ mt S n ⬝ d.jX = x := by
  obtain ⟨M, b, hM, h1, -⟩ := exists_blocks d hn
  have htri : (1 + M).BlockTriangular id := fun i j (h : j < i) => by
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt h), hM i j (le_of_lt h), add_zero]
  have hdiag : ∀ i, (1 + M) i i = 1 := fun i => by rw [Matrix.add_apply, Matrix.one_apply_eq, hM i i le_rfl, add_zero]
  have hu : IsUnit (1 + M) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => by
    refine ⟨fun h => ?_, ?_⟩
    · change (1 + M) i j = 0; exact htri h
    · change (1 + M) i i = 1; exact hdiag i
  have e : d.extX T x ⬝ mt S n ⬝ d.jX = x ⬝ (1 + M) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_add, ← Matrix.mul_assoc d.pX, d.pX_jX,
      Matrix.one_mul]
  rw [e]
  exact hx _ hmem

end FinalTheorems

section Flag

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}
  (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem extX_mul_flag {n : GA D S} (hn : n ∈ flagN d) : d.extX T x ⬝ mt S n =
    d.extX T x + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  have h := extX_mul d T x n
  rwa [extX_mul_jX d hx hn] at h

theorem ptS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    ptS d T x (n * n') = ptS d T x n + ptS d T x n' := by
  obtain ⟨M, b, -, -, h2⟩ := exists_blocks d hn'
  have e : ptS d T x (n * n') = d.extX T x ⬝ mt S n ⬝ (mt S n' ⬝ d.j0) := by
    rw [ptS, mt_mul, Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, h2]
  have e' : ptS d T x n' = d.extX T x ⬝ (d.j0 + d.jX ⬝ b) := by rw [ptS, Matrix.mul_assoc, h2]
  rw [e']
  simp only [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    d.pX_j0, d.p0_j0, d.pY_j0, d.p0_jX, d.pY_jX, cancel₂ d.p0_jX, cancel₂ d.pY_jX, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]

end Flag

section Flag2

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}

theorem symplOH_neg_left' {A B : HSp D} (a b : WO A B) : symplOH A B (-a) b = -symplOH A B a b := by
  rw [eq_neg_iff_add_eq_zero, ← GlobalTheory.OrientedHeis.symplOH_add_left, neg_add_cancel, symplOH_zero_left]

theorem ptS_one : ptS d T x 1 = 0 := by
  rw [ptS, mt_one, Matrix.mul_one, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]

variable (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem ptS_inv {n : GA D S} (hn : n ∈ flagN d) : ptS d T x n⁻¹ = -ptS d T x n := by
  have h := ptS_mul d hx (inv_mem hn) hn
  rw [inv_mul_cancel, ptS_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cenS_flag {n : GA D S} (hn : n ∈ flagN d) :
    cenS d T x n = symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY)) := by
  conv_lhs => rw [cenS, extX_mul_flag d hx hn]
  rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, zero_add, zero_add]

theorem cenS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
  have hi : n'⁻¹ ∈ flagN d := inv_mem hn'
  have h0 : symplOH S T (d.extX T x) (d.ext0 T (ptS d T x n) ⬝ mt S n') =
      symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      ptS_inv d hx hn', symplOH_neg_left', symplOH_skew S₀ T (ptS d T x n), neg_neg, zero_add, add_zero]
  have hY : symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) ⬝ mt S n') = cenS d T x n := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extY T _) (d.ext0 T _), HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      HypDec.symplOH_extY_extY, neg_zero, add_zero, add_zero, cenS_flag d hx hn]
  have e : cenS d T x (n * n') = symplOH S T (d.extX T x) (d.extX T x ⬝ mt S n ⬝ mt S n') := by
    rw [cenS, mt_mul, Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, Matrix.add_mul, Matrix.add_mul, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, h0, hY, ← cenS]
  ring

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem jacS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) (f : WO S₀ T → ℂ) :
    jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f) := by
  funext w
  simp only [jacS, ptS_mul d hx hn hn', cenS_mul d hx hn hn', Pi.smul_apply, smul_eq_mul, heisO,
    GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem jacS_mul_levi (n : GA D S) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    jacS ψ d T x (n * d.levi u) = jacS ψ d T x n := by
  have hL : d.extX T x ⬝ mt S (d.levi u)⁻¹ = d.extX T x := by
    rw [← map_inv, HypDec.extX_levi, hx _ (inv_mem hu)]
  have hpt : ptS d T x (n * d.levi u) = ptS d T x n := by
    rw [ptS, ptS, mt_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (mt S (d.levi u)), d.wittDecomp_levi_inclAnisotropic]
  have hcen : cenS d T x (n * d.levi u) = cenS d T x n := by
    rw [cenS, cenS, mt_mul, ← Matrix.mul_assoc, symplOH_mul_mt_right, hL]
  funext f
  simp only [jacS, hpt, hcen]

end Flag2

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} (x : Mx D T.rank ρ)

theorem witt_extension_hom_mul_embedded_anisotropic (g : GA D S₀) : d.extX T x ⬝ mt S (d.emb0 g) = d.extX T x := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem extX_conj (n : GA D S) (g : GA D S₀) :
    d.extX T x ⬝ mt S (d.emb0 g * n * (d.emb0 g)⁻¹) = d.extX T x ⬝ mt S n ⬝ mt S (d.emb0 g⁻¹) := by
  rw [← map_inv, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, witt_extension_hom_mul_embedded_anisotropic]

theorem ptS_conj (n : GA D S) (g : GA D S₀) :
    ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) := by
  rw [ptS, ptS, extX_conj, actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc (d.extX T x ⬝ mt S n), d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  exact (Matrix.mul_assoc _ _ _).symm

theorem cenS_conj (n : GA D S) (g : GA D S₀) :
    cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  rw [cenS, cenS, extX_conj, symplOH_mul_mt_right, ← map_inv, inv_inv, witt_extension_hom_mul_embedded_anisotropic]

end Conj

theorem jacS_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (x : Mx D T.rank ρ), (∀ u ∈ UX D ρ, x ⬝ u.1 = x) → (∀ b c, cenS d T x (d.nB b * d.nC c) = d.qS T c x) ∧
    (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptS d T x (n * n') = ptS d T x n + ptS d T x n' ∧
      cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') ∧
      ∀ f, jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f)) ∧
    (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacS ψ d T x (n * d.levi u) = jacS ψ d T x n) ∧
    ∀ n g, ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) ∧
      cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  intro D ψ S S₀ T ρ d x hx
  refine ⟨fun b c => ?_, fun n hn n' hn' => ⟨ptS_mul d hx hn hn', cenS_mul d hx hn hn', jacS_mul d hx ψ hn hn'⟩,
    fun n _ u hu => jacS_mul_levi d hx ψ n hu, fun n g => ⟨ptS_conj d x n g, cenS_conj d x n g⟩⟩
  have hB : d.nB b ∈ flagN d := d.nB_mem_NFlag b
  have hC : d.nC c ∈ flagN d := d.nC_mem_NFlag c
  have hpC : ptS d T x (d.nC c) = 0 := by
    rw [ptS, Matrix.mul_assoc, d.nC_j0, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]
  have e : pairS T x (x ⬝ (half D • (b ⬝ plus S₀ b))) = half D * hO S₀ T (x ⬝ b) (x ⬝ b) := by
    rw [← pairS_plus]
    simp only [pairS, Matrix.mul_smul, adj_smul, cA_half, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h2 : symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
    refine eq_of_add_self (F := D.host.F) ?_
    rw [HypDec.symplOH_extX_extY, e, trHalf_half, ← symplOH_eq, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
  have hcB : cenS d T x (d.nB b) = 0 := by
    have h1 : symplOH S T (d.extX T x) (d.extX T x ⬝ mt S (d.nB b)) +
        symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
      rw [← GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.extX_nB, sub_add_cancel, GlobalTheory.OrientedHeis.symplOH_add_right,
        GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero]
    rw [h2, add_zero] at h1
    exact h1
  rw [cenS_mul d hx hB hC, hcB, cenS_nC, hpC, symplOH_zero_right, zero_add, add_zero]

end GlobalTheory.JacHom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsDefiniteExist
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRows

theorem goodForms_definite_exist : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodVectorsDefinite → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥ := by
  intro hGV eps heps
  obtain ⟨x₀, hx₀⟩ := hGV.2 eps heps
  refine ⟨x₀, ?_⟩
  intro D L hP heps' hxL hSz G _ _ Pl0 T A Ks _ _ _ R F hGiv b

  have hTie : GlobalTheory.GLq.ESerTie D := by
    intro k
    obtain ⟨LD, hT, hE, _⟩ := hGiv.types k
    exact ⟨LD, hT, hE⟩

  obtain ⟨kap, lam, hScal⟩ := Formalism.IndefR.Links.scal_exists (F := F) R
  have hSet : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.HidaSetting (R.upd6 kap lam) F :=
    { lev := hGiv.core.lev
      grp := { hGiv.core.grp with }
      fam := { hGiv.core.fam with }
      models := { hGiv.core.models with }
      chain := Formalism.IndefR.Links.RealDat.chain_of_scalar_update hGiv.core.chain kap lam
      thP := Formalism.IndefR.Links.RealDat.theta_props_of_scalar_update hGiv.core.thP kap lam
      scal := hScal }

  obtain ⟨i, hi⟩ := GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.exists_last D
  have hShare := hx₀ D L hP heps' hxL hSz hTie G Pl0 T A Ks (R.upd6 kap lam) F hSet i hi b
  exact ⟨i, GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodShare.ne_bot (R.upd6 kap lam) F hShare⟩

end GlobalTheory.LiftRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TraceFrames

theorem hO_eq_trace_mul {D : D7} (S T : HSp D) (k y : WO S T) :
    hO S T y k = Matrix.trace (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D))
      * (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]; enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem toEAf_hO_eq_trace_frames {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D))
    (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  set X₀ : Matrix (Fin S.rank) (Fin T.rank) (AE D) := HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D)) with hX
  set Y₀ : Matrix (Fin T.rank) (Fin S.rank) (AE D) := y with hY
  set A : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := (βS⁻¹).val with hA
  set A' : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := βS.val with hA'
  set B : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := βT.val with hB
  set B' : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := (βT⁻¹).val with hB'
  set Xf : Matrix (Fin S.rank) (Fin T.rank) (Datum.EAf D) := X₀.map (toEAf D) with hXf
  set Yf : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := Y₀.map (toEAf D) with hYf
  have hBB : HMul.hMul B B' = (1 : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D)) := Units.mul_inv βT
  have hAA : HMul.hMul A' A = (1 : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) := Units.mul_inv βS
  have h1 : frMapAdj S T βS βT k = HMul.hMul (HMul.hMul A Xf) B := rfl
  have h2 : frMapO S T βS βT y = HMul.hMul (HMul.hMul B' Yf) A' := rfl
  have h4 : HMul.hMul Xf Yf = (HMul.hMul X₀ Y₀ : Matrix (Fin S.rank) (Fin S.rank) (AE D)).map (toEAf D) :=
    (Matrix.map_mul).symm
  have h3 : (HMul.hMul (HMul.hMul (HMul.hMul A Xf) B) (HMul.hMul (HMul.hMul B' Yf) A') :
      Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) = HMul.hMul A (HMul.hMul (HMul.hMul Xf Yf) A') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
  rw [h1, h2, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, hAA, Matrix.mul_one, h4, hO_eq_trace_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rfl

end GlobalTheory.TraceFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toEAf_orientedHermitianForm_eq_trace_frames : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T), toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  first | exact @GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames | exact GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames | (intros; apply GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasFiniteOnCompactsAndOpenPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem exists_mul_of_mem_sup_range {G H : Type} [Group G] [Group H] (N : Subgroup G) (s : H →* G)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) {g : G} (hg : g ∈ N ⊔ s.range) :
    ∃ n ∈ N, ∃ h, g = n * s h := by
  let K : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ h, x = n * s h}
      one_mem' := ⟨1, N.one_mem, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
        refine ⟨n₁ * (s h₁ * n₂ * (s h₁)⁻¹), N.mul_mem hn₁ (hnorm n₂ hn₂ h₁), h₁ * h₂, ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨n, hn, h, rfl⟩
        refine ⟨s h⁻¹ * n⁻¹ * (s h⁻¹)⁻¹, hnorm n⁻¹ (N.inv_mem hn) h⁻¹, h⁻¹, ?_⟩
        rw [map_inv]
        group }
  have hle : N ⊔ s.range ≤ K := by
    refine sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) ?_
    rintro _ ⟨h, rfl⟩
    exact ⟨1, N.one_mem, h, by simp⟩
  exact hle hg

theorem semiMeas_finite_on_compacts_and_open_pos : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G), IsClosed (N : Set G) → Continuous s → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N), p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h) → ∀ (μ : Measure H) (ν : Measure N), μ.IsHaarMeasure → ν.IsHaarMeasure → (∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) → IsFiniteMeasureOnCompacts (semiMeas N s μ ν) ∧ (semiMeas N s μ ν).IsOpenPosMeasure := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N s hN hs hnorm hp μ ν hμ hν _
  obtain ⟨p, hpc, hps⟩ := hp
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := inferInstanceAs (SecondCountableTopology (N : Set G))
  haveI : IsFiniteMeasureOnCompacts ν := inferInstance
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : ν.IsOpenPosMeasure := inferInstance
  haveI : (μ.prod ν).IsOpenPosMeasure := inferInstance

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun q =>
    ⟨q.2.1 * s q.1, mul_mem (Subgroup.mem_sup_left q.2.2) (Subgroup.mem_sup_right ⟨q.1, rfl⟩)⟩
  have hφc : Continuous φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)).subtype_mk _
  have hmemN : ∀ k : (N ⊔ s.range : Subgroup G), (k : G) * (s (p k))⁻¹ ∈ N := by
    intro k
    obtain ⟨n, hn, h, hk⟩ := exists_mul_of_mem_sup_range N s hnorm k.2
    have hpk : p k = h := by
      have hk' : k = ⟨n * s h, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ :=
        Subtype.ext hk
      rw [hk']
      exact hps h ⟨n, hn⟩
    rw [hpk, hk, mul_inv_cancel_right]
    exact hn
  let ψ : (N ⊔ s.range : Subgroup G) → H × N := fun k => (p k, ⟨(k : G) * (s (p k))⁻¹, hmemN k⟩)
  have hψc : Continuous ψ :=
    hpc.prodMk ((continuous_subtype_val.mul (hs.comp hpc).inv).subtype_mk _)
  have hψφ : ∀ q, ψ (φ q) = q := by
    rintro ⟨h, n⟩
    have h1 : p (φ (h, n)) = h := hps h n
    refine Prod.ext h1 (Subtype.ext ?_)
    show (n : G) * s h * (s (p (φ (h, n))))⁻¹ = n
    rw [h1, mul_inv_cancel_right]
  have hφψ : ∀ k, φ (ψ k) = k := by
    intro k
    apply Subtype.ext
    show (k : G) * (s (p k))⁻¹ * s (p k) = k
    rw [inv_mul_cancel_right]
  have hsurj : Function.Surjective φ := fun k => ⟨ψ k, hφψ k⟩
  show IsFiniteMeasureOnCompacts ((μ.prod ν).map φ) ∧ ((μ.prod ν).map φ).IsOpenPosMeasure
  refine ⟨⟨fun C hC => ?_⟩, hφc.isOpenPosMeasure_map hsurj⟩
  rw [Measure.map_apply hφc.measurable hC.measurableSet]
  refine lt_of_le_of_lt (measure_mono ?_) (hC.image hψc).measure_lt_top
  intro q hq
  exact ⟨φ q, hq, hψφ q⟩

end GlobalTheory.MixPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameUnimod

theorem isLattice_of_squeeze {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module E M] [Module (𝓞 E) M]
    [IsScalarTower (𝓞 E) E M] {L Λ : Submodule (𝓞 E) M} (hL : Submodule.IsLattice E L) {c : E} (hc : c ≠ 0)
    (h1 : ∀ x ∈ L, c • x ∈ Λ) (h2 : ∀ x ∈ Λ, c • x ∈ L) : Submodule.IsLattice E Λ := by
  let f : M →ₗ[𝓞 E] M := ((c⁻¹ • LinearMap.id : M →ₗ[E] M)).restrictScalars (𝓞 E)
  have hfg : (L.map f).FG := hL.fg.map f
  have hle : Λ ≤ L.map f := fun x hx => ⟨c • x, h2 x hx, by simp [f, smul_smul, hc]⟩
  exact Submodule.IsLattice.of_fg E (hfg.of_le hle)

theorem coe_span_dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) :
    (Submodule.span (𝓞 E) (dualSet σ J L) : Set (n → E)) = dualSet σ J L := by
  refine Set.Subset.antisymm (fun y hy => ?_) Submodule.subset_span
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simpa [Formalism.UG.hform] using (algebraMap (𝓞 E) E).range.zero_mem
  | add y z _ _ hy hz =>
    intro x hx
    have : Formalism.UG.hform σ J x (y + z) = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x z := by
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
    rw [this]
    exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : Formalism.UG.hform σ J x (a • y) = algebraMap (𝓞 E) E a * Formalism.UG.hform σ J x y := by
      simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem isDefUnimod_of_isBaseFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  intro D V β Λ N hs hp ⟨_, hdual, hN, h1, h2⟩
  obtain ⟨-, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hL : Submodule.IsLattice D.host.E (Formalism.L2.Herm.crdLat V V.L0) :=
    Submodule.IsLattice.of_fg D.host.E (V.standardTuple_isLattice.fg.map _)
  have hmem : ∀ x, x ∈ Formalism.L2.Herm.crdLat V V.L0 ↔ x ∈ L0c D V := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  refine ⟨Matrix.ext fun i j => (hJ V).1 i j, (hJ V).2.isUnit,
    GlobalTheory.Proof.TotallyDefiniteMass.isTotDef_gram D.sp.cm V hs hp,
    isLattice_of_squeeze hL (Nat.cast_ne_zero.2 hN.ne') (fun x hx => h1 x ((hmem x).1 hx))
      (fun x hx => (hmem _).2 (h2 x hx)), ?_⟩
  rw [← coe_span_dualSet]
  exact congrArg SetLike.coe hdual

end GlobalTheory.BaseFrameUnimod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDefStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDefiniteSelfDual_of_baseFrame_posDef : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  first | exact @GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame | exact GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame | (intros; apply GlobalTheory.BaseFrameUnimod.isDefUnimod_of_isBaseFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasIsMulLeftInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MixPer.semiMeas_isMulLeftInvariant {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (_hp : ∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N),
      p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h)
    (μ : Measure H) (ν : Measure N) (hμ : μ.IsHaarMeasure) (hν : ν.IsHaarMeasure)
    (hc : ∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) :
    (semiMeas N s μ ν).IsMulLeftInvariant := by
  have := hμ
  have := hν
  have : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  have : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite ν := inferInstance
  have : SigmaFinite μ := inferInstance
  have hemb : MeasurableEmbedding (Subtype.val : N → G) :=
    MeasurableEmbedding.subtype_coe hN.measurableSet

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun p =>
    ⟨p.2.1 * s p.1, mul_mem (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right ⟨p.1, rfl⟩)⟩
  have hφ : Measurable φ :=
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul
      (hs.comp continuous_fst)) _).measurable
  have hm : semiMeas N s μ ν = (μ.prod ν).map φ := rfl

  let T : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ N ⊔ s.range,
        (semiMeas N s μ ν).map (fun x => (⟨g, hg⟩ : (N ⊔ s.range : Subgroup G)) * x) =
          semiMeas N s μ ν}
      one_mem' := by
        refine ⟨one_mem _, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨1, one_mem _⟩ : (N ⊔ s.range : Subgroup G)) * x) = id := funext fun x => one_mul x
        rw [e, Measure.map_id]
      mul_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : (fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a * b, mul_mem ha hb⟩ : (N ⊔ s.range : Subgroup G)) * x) =
            (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨b, hb⟩ : (N ⊔ s.range : Subgroup G)) * x) :=
          funext fun x => mul_assoc (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) ⟨b, hb⟩ x
        rw [e, ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), eb, ea]
      inv_mem' := by
        rintro a ⟨ha, ea⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← ea]
        rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
        have e : ((fun x : (N ⊔ s.range : Subgroup G) =>
            (⟨a⁻¹, inv_mem ha⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘
              (fun x => (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) * x)) = id :=
          funext fun x => inv_mul_cancel_left (⟨a, ha⟩ : (N ⊔ s.range : Subgroup G)) x
        rw [e, Measure.map_id] }

  have hNT : N ≤ T := by
    intro n hn
    refine ⟨Subgroup.mem_sup_left hn, ?_⟩
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨n, Subgroup.mem_sup_left hn⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map id (fun m : N => (⟨n, hn⟩ : N) * m) := by
      funext p
      apply Subtype.ext
      simp [φ, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ (measurable_id.prodMap (measurable_const_mul _)),
      ← Measure.map_prod_map μ ν measurable_id (measurable_const_mul _), Measure.map_id,
      map_mul_left_eq_self]

  have hST : s.range ≤ T := by
    rintro _ ⟨h₀, rfl⟩
    refine ⟨Subgroup.mem_sup_right ⟨h₀, rfl⟩, ?_⟩
    let c : N → N := fun m => ⟨s h₀ * m.1 * (s h₀)⁻¹, hnorm m.1 m.2 h₀⟩
    have hcm : Measurable c :=
      (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const)
        _).measurable
    have hcν : ν.map c = ν := by
      rw [← hemb.comap_map (ν.map c), Measure.map_map hemb.measurable hcm]
      have e : (Subtype.val ∘ c) = (fun m : N => s h₀ * m.1 * (s h₀)⁻¹) := rfl
      rw [e, hc h₀, hemb.comap_map]
    have e : (fun x : (N ⊔ s.range : Subgroup G) =>
        (⟨s h₀, Subgroup.mem_sup_right ⟨h₀, rfl⟩⟩ : (N ⊔ s.range : Subgroup G)) * x) ∘ φ =
        φ ∘ Prod.map (fun h => h₀ * h) c := by
      funext p
      apply Subtype.ext
      simp [φ, c, mul_assoc]
    rw [hm, Measure.map_map (measurable_const_mul _) hφ, e,
      ← Measure.map_map hφ ((measurable_const_mul _).prodMap hcm),
      ← Measure.map_prod_map μ ν (measurable_const_mul _) hcm, hcν, map_mul_left_eq_self]
  have hT : N ⊔ s.range ≤ T := sup_le hNT hST
  exact ⟨fun k => by
    obtain ⟨hk, ek⟩ := hT k.2
    exact ek⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.MaxParabIwasawa

theorem iwasawa_stdMaxParab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r a b : ℕ) (h : a + b = r) (g : GL (Fin r) k),
    (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
      ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := by
  intro k _ _ _ _ r a b h g
  have key : ∀ x : GL (Fin r) k, ∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, x = κ * p := by
    intro x
    obtain ⟨k₀, p, hp, hx⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r x
    have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi =>
      hp (show j < i from by rw [Fin.lt_def]; omega)
    exact ⟨_, ⟨k₀, rfl⟩, p, hpP, hx⟩
  refine ⟨key g, ?_⟩
  obtain ⟨κ, hκ, p, hp, e⟩ := key g⁻¹
  refine ⟨p⁻¹, inv_mem hp, κ⁻¹, inv_mem hκ, ?_⟩
  rw [← mul_inv_rev, ← e, inv_inv]

end GlobalTheory.MaxParabIwasawa
end
end

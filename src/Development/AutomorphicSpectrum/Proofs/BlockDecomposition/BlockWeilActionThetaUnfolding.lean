module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleRootExt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Summand

variable {D : D7}

theorem trace_inner_join (V : HSp D) {r s : ℕ} (x₁ y₁ : Mx D V.rank r) (x₂ y₂ : Mx D V.rank s) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (colJoin x₁ x₂) (colJoin y₁ y₂)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x₁ y₁) + Matrix.trace (GlobalTheory.StdUnn.inner V x₂ y₂) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]

theorem trace_inner_mul (V : HSp D) {n : ℕ} (U W : Mx D V.rank n) (A A' : Mx D n n)
    (h : HMul.hMul A' (adj A) = (1 : Mx D n n)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A')) = Matrix.trace (GlobalTheory.StdUnn.inner V U W) := by
  have e : GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A') =
      HMul.hMul (adj A) (HMul.hMul (GlobalTheory.StdUnn.inner V U W) A') := by
    simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

theorem inner_neg_left (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (-x) y = -GlobalTheory.StdUnn.inner V x y := by
  have : adj (-x) = -adj x := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (-y) = -GlobalTheory.StdUnn.inner V x y := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem inner_sub_left (V : HSp D) {n : ℕ} (x x' y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (x - x') y = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x' y := by
  have : adj (x - x') = adj x - adj x' := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.sub_mul]

theorem inner_sub_right (V : HSp D) {n : ℕ} (x y y' : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (y - y') = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x y' := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_sub]

theorem inner_zero_left (V : HSp D) {n : ℕ} (y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
  have : adj (0 : Mx D V.rank n) = 0 := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.zero_mul]

theorem inner_mul_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) :
    GlobalTheory.StdUnn.inner V x (HMul.hMul y B) = HMul.hMul (GlobalTheory.StdUnn.inner V x y) B := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_adj {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, adj, map_sum]

theorem adj_inner (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V x y) = GlobalTheory.StdUnn.inner V y x := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) (hB : adj B = B) :
    Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y x) B) =
      cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V x y) B)) := by
  rw [← trace_adj, adj_mul, adj_inner, hB, Matrix.trace_mul_comm]

theorem exp_ring {R : Type*} [CommRing R] (c t₁ t₃ t₄ t₅ : R) (h : c + c = 1) :
    -t₁ + t₅ + c * t₃ + c * t₄ = t₅ + c * (t₃ - t₁ - t₁ + t₄) := by
  linear_combination t₁ * h

theorem sub_group {G : Type*} [AddCommGroup G] (a b c d : G) : a - b - (c - d) = a - b - c + d := by
  abel

theorem halfTr_eq (z : AE D) : halfTr z = algebraMap D.host.F (AF D.host.F) (1 / 2) * trA z := rfl

theorem half_add_half : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_add (f := _), add_halves, map_one]

theorem psi_halfTr_incA (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (e : D.host.E) :
    ψ (halfTr (incA D e)) = 1 := by
  have : halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
    have h : Algebra.trace (AF D.host.F) (AE D) (incA D e) =
        algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
      show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    rw [halfTr_eq, map_mul, trA, h]
  rw [this]
  exact hψ.2.2.1 _

theorem trace_inner_rat (V : HSp D) {n : ℕ} (p : Matrix (Fin V.rank) (Fin n) D.host.E) (b : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ e : D.host.E, Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) = incA D e := by
  refine ⟨Matrix.trace (pᴴ * (HSpace.gram V * p) * b), ?_⟩
  have : HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b) = rat (pᴴ * (HSpace.gram V * p) * b) := by
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, rat, Matrix.map_apply, map_sum]

theorem psi_combine (ψ : AddChar (AF D.host.F) ℂ) (X Y T t₁ t₃ t₄ t₅ : AE D) (e₁ : X = -t₁ + t₅) (e₂ : Y = t₃)
    (e₃ : T = t₃ - cA D t₁ - t₁ + t₄) (e₄ : ψ (halfTr t₄) = 1) :
    ψ (trA X + halfTr Y) = ψ (trA t₅) * ψ (halfTr T) := by
  subst e₁ e₂ e₃
  have h : trA (-t₁ + t₅) + halfTr Y + halfTr t₄ = trA t₅ + halfTr (Y - cA D t₁ - t₁ + t₄) := by
    simp only [halfTr_eq, trA, map_add (f := _), map_sub, map_neg, GlobalTheory.DualPairCheck.trace_cA]
    exact exp_ring _ _ _ _ _ half_add_half
  rw [← AddChar.map_add_eq_mul, ← h, AddChar.map_add_eq_mul ψ _ (halfTr t₄), e₄, mul_one]

theorem summand (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (hb : (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (ha : IsUnit a.det)
    (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s)))
    (hx : xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a))
    (hy : yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹))
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E) :
    Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  have hunit : IsUnit (aᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  have hA : HMul.hMul (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) (adj (rat a)) = (1 : Mx D (r + s) (r + s)) := by
    have : cT (D.sp.cm.sig : D.host.E →+* D.host.E) a = aᴴ := rfl
    rw [this, ← rat_conjTranspose, ← rat_mul, Matrix.nonsing_inv_mul _ hunit, rat_one]
  have hB : adj (rat b) = rat b := by
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hz : rat (colJoin p q * a) = HMul.hMul (colJoin (rat p) (rat q)) (rat a) := by
    rw [rat_mul, rat_colJoin]
  have hzx : rat (colJoin p q * a) + xPart v = HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a) := by
    rw [hz, hx, ← sub_eq_add_neg, ← Matrix.sub_mul, ← colJoin_sub, sub_zero]
  obtain ⟨e, he⟩ := trace_inner_rat V p b
  have e₄ : ψ (halfTr (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)))) = 1 := by
    rw [he]
    exact psi_halfTr_incA ψ hψ e
  have e1 : Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v)) =
      -Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)) + Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) y₂) := by
    rw [hz, hy, trace_inner_mul V _ _ _ _ hA, trace_inner_join, inner_neg_right, inner_mul_right, Matrix.trace_neg]
  have e2 : Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b)) := by
    rw [hx, hy, ← Matrix.neg_mul, trace_inner_mul V _ _ _ _ hA]
    have : -colJoin y₁ (0 : Mx D V.rank s) = colJoin (-y₁) (0 : Mx D V.rank s) := by
      rw [← colJoin_neg, neg_zero]
    rw [this, trace_inner_join, inner_zero_left, inner_neg_left, inner_neg_right, inner_mul_right]
    simp
  have e3 : Matrix.trace (HMul.hMul (rat b) (GlobalTheory.StdUnn.inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b))
        - cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)))
        - Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b))
        + Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) := by
    rw [Matrix.trace_mul_comm, ← trace_swap V (rat p) y₁ (rat b) hB, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [Matrix.sub_mul, Matrix.trace_sub]
    exact sub_group _ _ _ _
  have hc := psi_combine ψ _ _ _ _ _ _ _ e1 e2 e3 e₄
  show ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v))) +
      halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) * Φ (rat (colJoin p q * a) + xPart v) = _
  rw [hc, hzx, mul_assoc]
  rfl

end GlobalTheory.CompanionTheory.EisUnfold.Summand
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfoldingStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_weil_action_theta_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E), (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b →
    ∀ (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s))),
    xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a) →
    yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) →
    ∀ (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E),
      Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | exact GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Summand.summand <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChart
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech.Omega
open GlobalTheory.CompanionTheory.GrForm GlobalTheory.CompanionTheory.GrVB

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem evLift_mul_sub {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (z x : Γ(X, W))
    (T : P.FullSubcategory) :
    (show T.obj.B from evLift hP z T) * lft W T.obj x - lft W T.obj (z * x) ∈ T.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, mk_evLift, lft_spec _ (hP _ T.property), lft_spec _ (hP _ T.property), map_mul]

theorem rp_fAct {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hF : IsFil (sP P) (sFil P))
    (hP : ∀ T, P T → InU W T) {d r : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (z : Γ(X, W)) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r)
    (hc : Rp (W := W) P u x c) : Rp (W := W) P u (fun I => z * x I) (fAct hF hP r z c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulMor hF r (evLift hP z) (evLift_nat hP z)).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from evLift hP z (s.obj (Fin.last r))) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have := J_mul_sFil P r _ (evLift_mul_sub hP z (x I) (s.obj (Fin.last r))) hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (evLift hP z (s.obj (Fin.last r))) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

theorem basis : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  classical
  intro hLoc hPoly O _ l s hb X q W₀ d c r hr
  have hL : StLoc := stLoc stFrame hLoc hPoly
  have hE : StExists := exists_of_cocycle stCocycle
  let u : Fin d → ∀ T : Thick (LL q), T.B := fun k T => lft W₀ T (c.t k)
  have hu : IsLift W₀ c.t u := fun k T h => lft_spec T h _
  choose ω hω using fun k : Idx r d => hE W₀ c.t u hu (SS q l s W₀) (ss_inU l s W₀) r (Pi.single k 1)
  refine ⟨ω, ?_⟩
  intro W hW hle Q hQ hQ₀ hF hQW h
  have hFree : Free W Q r u := free_at hL hb hle hW c hu hr hQ
  have hu' : IsLift W (fun i => rs hle (c.t i)) u := isLift_res hle hu fun _ => rfl
  have hrep : ∀ f : Idx r d → Γ(X, W), Rp (W := W) Q u f
      (∑ k, fAct hF hQW r (f k) ((resU (GF q r) hQ₀).pull r (ω k))) := by
    intro f
    have s1 := rp_sum hE stAdd hu' hQW Finset.univ
      (fun k I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) _
      (fun k _ => rp_fAct hF hQW hu' (f k) _ _
        (stRes W₀ W hle c.t u hu (SS q l s W₀) Q hQ₀ (ss_inU l s W₀) hQW r _ _ (hω k)))
    have e : (∑ k, fun I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) = f := by
      funext I
      rw [Finset.sum_apply, Finset.sum_eq_single I]
      · simp
      · intro b _ hb'
        simp [Pi.single_eq_of_ne (Ne.symm hb')]
      · simp
    rwa [e] at s1
  obtain ⟨x, hx⟩ := hFree.1 h
  refine ⟨x, rp_class hx (hrep x), fun y hy => ?_⟩
  have hy' : Rp (W := W) Q u y h := by
    rw [hy]
    exact hrep y
  exact rp_coef stAdd hu' hQW hFree hy' hx

end GlobalTheory.CompanionTheory.GrCech.Omega
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChartStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_graded_form_on_affine_chart : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.Omega.basis | exact GlobalTheory.CompanionTheory.GrCech.Omega.basis | (intros; apply GlobalTheory.CompanionTheory.GrCech.Omega.basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
namespace GlobalTheory.CompanionTheory.GrCech

theorem capO_affine {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (U : Cov q) (n : ℕ)
    (i : Fin (n + 1) → U.ι) : IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = capO U.U i := by
    refine le_antisymm (le_iInf fun a => ?_) (le_iInf₂ fun α hα => ?_)
    · exact iInf₂_le (i a) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i a
  rwa [e] at h

theorem inU_capO {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have h := GlobalTheory.T.inOpen_finite_inf_iff (γ := γ) (p := p) (q := q) (κ := κ) (fun a => U (i a)) Finset.univ T
  simpa [capO] using h

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  refine propext ⟨fun h => ⟨(h 0).1, capO U i, rfl, (inU_capO U i T).2 fun a => ?_⟩, ?_⟩
  · obtain ⟨-, V, hV, hT⟩ := h a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact hT
  · rintro ⟨hq, V, hV, hT⟩ a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, _, rfl, (inU_capO U i T).1 hT a⟩

end GlobalTheory.CompanionTheory.GrCech

namespace GlobalTheory.CompanionTheory.GrCech

theorem inU_mono {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {V W : X.Opens} (h : V ≤ W) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) : InU W T :=
  fun x hx => h (hT hx)

theorem vb_cech (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (U : Cov q) (r : ℕ) (hr : r < s) :
    Nonempty (VB (fun W : X.Opens => strV q W) U.U (CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r)) := by
  classical
  have isF : ∀ Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), IsFil (sP Q) (sFil Q) :=
    fun Q => GlobalTheory.T.sheaf_filtration_property Q
  choose ω hω using fun α => GlobalTheory.T.exists_graded_form_on_affine_chart hLoc hPoly l s hb q (U.c α) r hr
  have hT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (T : Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), capT (fun α => St (TF l s) {U.U α}) i T → InU (capO U.U i) T := by
    intro n i T h
    rw [capT_eq] at h
    obtain ⟨-, V, hV, hT⟩ := h
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hle : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)),
      capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a)} := fun i a T h => h a
  have hpair : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := by
    intro α β
    have h := U.inter {α, β} ⟨α, by simp⟩
    have e : (⨅ γ ∈ ({α, β} : Finset U.ι), U.U γ) = U.U α ⊓ U.U β := by
      rw [Finset.iInf_insert, Finset.iInf_singleton]
    rwa [e] at h
  have hl2 : ∀ {V W : X.Opens} (h : V ≤ W), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} ≤ St (TF l s) {W} := by
    rintro V W h T ⟨hq, V', hV, hT⟩
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, W, rfl, inU_mono h hT⟩
  have hq2 : ∀ {V : X.Opens} (T), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} T → InU V T := by
    rintro V T ⟨hq, V', hV, hT⟩
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hg0 := fun α β (k' : Idx r (U.d β)) => (hω α (U.U α ⊓ U.U β) (hpair α β) inf_le_left _ rfl (hl2 inf_le_left) (isF _) hq2
    ((resU _ (hl2 inf_le_right)).pull r (ω β k'))).exists
  choose g' hg' using hg0
  refine GlobalTheory.T.cover_cup_action_basis (fun W => strV q W) _ U.U _ r (fun α => Idx r (U.d α))
    (fun i => fHom (isF _) (hT i) r) (fun i a k => (resU _ (hle i a)).pull r (ω (i a) k)) (fun α β k k' => g' α β k' k)
    ?_ ?_ ?_ ?_ ?_
  · intro n i a h
    exact hω (i a) (capO U.U i) (capO_affine U n i) (capO_le U.U i a) _ (capT_eq _ _ i) (hle i a) (isF _) (hT i) h
  · intro n i c h
    exact fAct_str (isF _) (hT i) r c h
  · intro n i j f h
    exact res_fAct (isF _) (hT _) r (isF _) (hT i) (capO_comp U.U i j.succAbove) _ f h
  · intro n i j a k
    exact res_res _ _ _ r _
  · intro n i a a' k'
    have hle2 : capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a) ⊓ U.U (i a')} := by
      intro T h
      exact ⟨(h a).1, _, rfl, le_preimage_inf (pt T) (hq2 T (hle i a T h)) (hq2 T (hle i a' T h))⟩
    have h1 := congrArg ((resU _ hle2).pull r) (hg' (i a) (i a') k')
    set_option synthInstance.maxHeartbeats 100000 in
      rw [res_res, map_sum] at h1
    refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (res_fAct (isF _) hq2 r (isF _) (hT i) (le_inf (capO_le U.U i a) (capO_le U.U i a')) hle2 _ _).trans ?_
    change fAct _ _ r _ _ = fAct _ _ r _ _
    rw [res_res]

theorem main_nl (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ) :
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r).cx.H p) := by
  obtain ⟨V⟩ := vb_cech hLoc hPoly l s hb q U r hr
  exact GlobalTheory.T.affine_cover_cohomology_finite q U.U U.cover (capO_affine U) _ V p


set_option maxHeartbeats 1000000 in
theorem main_thm : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (Pb.sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  intro hLoc hPoly _ _ O _ _ l s hb X q _ U r hr p
  exact main_nl hLoc hPoly l s hb q U r hr p

end GlobalTheory.CompanionTheory.GrCech
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFiniteStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_cech_cohomology_finite : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((cechH (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.main_thm | exact GlobalTheory.CompanionTheory.GrCech.main_thm | (intros; apply GlobalTheory.CompanionTheory.GrCech.main_thm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecomposition
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.DecN

open NumberField IsDedekindDomain GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport
open scoped Topology

variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def lvN (v : HeightOneSpectrum (𝓞 F)) (P : AddSubgroup (Fv F v)) (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) where
  carrier := {Z | ∀ a i k, crd b (Fv F v) (Z a i) k ∈ P}
  add_mem' hx hy a i k := by
    rw [Pi.add_apply, Pi.add_apply, crd_add]
    exact add_mem (hx a i k) (hy a i k)
  zero_mem' a i k := by
    rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
    exact zero_mem P
  neg_mem' hx a i k := by
    rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
    exact neg_mem (hx a i k)

theorem isClopen_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (n M : ℕ) :
    IsClopen (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : ∀ (x : Fin n) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹' (P : Set (Fv F v)) := by
    ext Y
    simp [lvN]
  rw [e]
  exact ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    P.isClosed.preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => P.isOpen.preimage (hc x i k)⟩

theorem isCompact_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v) (n M : ℕ) :
    IsCompact (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
  (isCompact_latV b v n M).of_isClosed_subset (isClopen_lvN b v P n M).isClosed
    fun _ hZ a i k => hP (hZ a i k)

theorem projV_subN (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X - Y) = projV v X - projV v Y := by
  funext a i
  simp [projV, map_sub]

def cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) {n M : ℕ}
    (a : Fin n → Fin M → Fv F v ⊗[F] E) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Z | Z - a ∈ lvN b v (P : AddSubgroup (Fv F v)) n M}

theorem isCompact_isOpen_cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v)
    {n M : ℕ} (a : Fin n → Fin M → Fv F v ⊗[F] E) : IsCompact (cosVN b v P a) ∧ IsOpen (cosVN b v P a) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have e : cosVN b v P a = (Homeomorph.subRight a) ⁻¹' (lvN b v (P : AddSubgroup (Fv F v)) n M : Set _) := rfl
  rw [e]
  exact ⟨(Homeomorph.subRight a).isCompact_preimage.2 (isCompact_lvN b v P hP n M),
    (isClopen_lvN b v P n M).isOpen.preimage (Homeomorph.subRight a).continuous⟩

theorem cosVN_intSub (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} {a : Fin n → Fin M → Fv F v ⊗[F] E}
    (ha : a ∈ latV b v) : cosVN b v (intSub v) a = latV b v := by
  have ha' : a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := ha
  ext Z
  have e1 : Z ∈ cosVN b v (intSub v) a ↔ Z - a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M :=
    Iff.rfl
  have e2 : Z ∈ latV b v ↔ Z ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := Iff.rfl
  rw [e1, e2, sub_eq_add_neg]
  exact add_mem_cancel_right (neg_mem ha')

theorem exists_box_combN {n M : ℕ} (g : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (hg : IsSB g) :
    ∃ (s : Finset (Fin n → Fin M → Af F ⊗[F] E))
      (A : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
      (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ a v, IsCompact (A a v) ∧ IsOpen (A a v)) ∧ (∀ a ∈ s, ∀ v, v ∉ S → A a v = latV b v) ∧
        ∀ Y, g Y = ∑ a ∈ s, g a * (boxF (A a)).indicator (fun _ => (1 : ℂ)) Y := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have hU := invariant_mem_nhds hg.1 hg.2
  let Lc : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  let B : AddSubgroup (Af F) :=
    { carrier := {y | ∀ v, y v ∈ P v}
      add_mem' := fun hx hy v => add_mem (hx v) (hy v)
      zero_mem' := fun v => zero_mem (P v)
      neg_mem' := fun hx v => neg_mem (hx v) }
  have hBo : IsOpen (B : Set (Af F)) := by
    have e : (B : Set (Af F)) = {y : Af F | ∀ v, y v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ T, (fun y : Af F => y v) ⁻¹' (P v : Set (Fv F v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨fun v => hPO v (hy v), Set.mem_iInter₂.2 fun v _ => hy v⟩
      · rintro ⟨hy1, hy2⟩ v
        by_cases hv : v ∈ T
        · exact Set.mem_iInter₂.1 hy2 v hv
        · rw [hPT v hv]
          exact hy1 v
    rw [e]
    refine IsOpen.inter ?_ (T.finite_toSet.isOpen_biInter fun v _ => (P v).isOpen.preimage
      (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v))
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let L : AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) :=
    { carrier := {X | ∀ a i k, crd b (Af F) (X a i) k ∈ B}
      add_mem' := fun {x y} hx hy a i k => by
        rw [Pi.add_apply, Pi.add_apply, crd_add]
        exact add_mem (hx a i k) (hy a i k)
      zero_mem' := fun a i k => by
        rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
        exact zero_mem B
      neg_mem' := fun {x} hx a i k => by
        rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
        exact neg_mem (hx a i k) }
  have hLo : IsOpen (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
    have e : (L : Set (Fin n → Fin M → Af F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
        (fun X : Fin n → Fin M → Af F ⊗[F] E => crd b (Af F) (X a i) k) ⁻¹' (B : Set (Af F)) := by
      ext X
      simp [L]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hBo.preimage ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply a)))
  have hinv : ∀ x, ∀ l ∈ L, g (x + l) = g x := by
    intro x l hl
    have hl' : l = Lc fun a i k => crd b (Af F) (l a i) k := by
      funext a i
      exact eq_sum_crd b (Af F) (l a i)
    rw [hl']
    refine h1 _ (fun a => h2 _ fun i => h3 _ fun k => hsub (hl a i k)) x
  obtain ⟨s, hs⟩ := eq_sum_cosets hg.2 L hLo hinv
  have hbad : ∀ a : Fin n → Fin M → Af F ⊗[F] E, {v | ¬ projV v a ∈ latV b v}.Finite := fun a =>
    Filter.eventually_cofinite.1 (eventually_mem_latV b a)
  refine ⟨s, fun a v => cosVN b v (P v) (projV v a), T ∪ s.biUnion fun a => (hbad a).toFinset,
    fun a v => isCompact_isOpen_cosVN b v (P v) (hPO v) _, fun a ha v hv => ?_, fun Y => ?_⟩
  · have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    have hva : projV v a ∈ latV b v := by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, (hbad a).mem_toFinset.2 h⟩))
    show cosVN b v (P v) (projV v a) = latV b v
    rw [hPT v hvT]
    exact cosVN_intSub b v hva
  · rw [hs Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    ext X
    show X - a ∈ L ↔ ∀ v, projV v X - projV v a ∈ lvN b v ((P v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M
    constructor
    · intro h v i j k
      rw [← projV_subN]
      have := crd_projV b (X - a) v i j k
      rw [this]
      exact h i j k v
    · intro h i j k v
      have := crd_projV b (X - a) v i j k
      rw [← this, projV_subN]
      exact h v i j k

theorem isSchwartzArch_const_mulN {n M : ℕ} {φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ} (h : IsSchwartzArch φ) (c : ℂ) :
    IsSchwartzArch fun X => φ X * c := by
  obtain ⟨N, e, c1, c2, f, hf⟩ := h
  exact ⟨N, e, c1, c2, c • f, fun X => by simp [hf X, mul_comm]⟩

end GlobalTheory.CompanionTheory.WhitFree.DecN

namespace GlobalTheory.CompanionTheory.WhitFree

theorem schwartzBruhat_eq_sum_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨k', Φinf, Φf, hi, hf, hs⟩ := hΦ
  choose s A S hA hS hdec using fun i => DecN.exists_box_combN b (Φf i) (hf i)
  let I := Σ i : Fin k', ↥(s i)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j X => Φinf (e.symm j).1 X * Φf (e.symm j).1 (e.symm j).2.1,
    fun j => A (e.symm j).1 (e.symm j).2.1, Finset.univ.biUnion S, fun j => ?_, fun j v => hA _ _ v,
    fun j v hv => ?_, fun X => ?_⟩
  · exact DecN.isSchwartzArch_const_mulN (hi _) _
  · refine hS _ _ (e.symm j).2.2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩)
  · rw [hs X, Fintype.sum_equiv e.symm _ (fun p : I => pureN (fun Y => Φinf p.1 Y * Φf p.1 p.2.1) (A p.1 p.2.1) X)
      (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [pureN, mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WhitFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecompositionStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_factorizable_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN | exact GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN | (intros; apply GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimum
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvInfProof

theorem tendsto_prod_shift (m₀ : Multiset ℂ) {z : ℕ → ℂ} {z₀ : ℂ} (h : Tendsto z atTop (𝓝 z₀)) (u : ℂ) :
    Tendsto (fun k => ((m₀.map (· + z k)).map (u + ·)).prod) atTop
      (𝓝 (((m₀.map (· + z₀)).map (u + ·)).prod)) := by
  induction m₀ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (tendsto_const_nhds.add (h.const_add a)).mul ih

theorem convInf_of_discInf_topInf : DiscInf → TopInf → ConvInf := by
  intro hD hT E _ _ _ N t s τ hc hs
  induction hc with
  | leaf V z z₀ h =>
    have hex : ∃ m₀, HasInfCharGL V τ m₀ := by
      rcases hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩
      · exact ⟨0, hT E τ⟩
      · exact hD E _ V hV τ
    obtain ⟨m₀, h₀⟩ := hex
    exact ⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩,
      fun u => tendsto_prod_shift m₀ h u⟩
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a₀, a, ha₀, ha, hat⟩ := ih₁ hs.1
    obtain ⟨b₀, b, hb₀, hb, hbt⟩ := ih₂ hs.2
    refine ⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩,
      fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩
    simp only [Multiset.map_add (f := _), Multiset.prod_add]
    exact (hat u).mul (hbt u)

end GlobalTheory.CompanionTheory.EGlue.ConvInfProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimumStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.ConvInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | exact GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExists
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.LTPer

theorem map_subst_comm {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) {F G : PowerSeries A}
    {F' : PowerSeries B} (hF' : PowerSeries.map h F = F')
    (hF : PowerSeries.constantCoeff F = 0) (hG : PowerSeries.constantCoeff G = 0)
    (hs : PowerSeries.subst G F = PowerSeries.subst F G) :
    PowerSeries.subst (PowerSeries.map h G) F' = PowerSeries.subst F' (PowerSeries.map h G) := by
  subst hF'
  have h2 := congrArg (MvPowerSeries.map h) hs
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)] at h2
  exact h2


open GlobalTheory.CompanionTheory.LTHodge.CharEx GroundTheory.LocalField GroundTheory.LocalField.FormalGroup ValuativeRel in
theorem exists_series_comm : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  intro l _ K π hπ a
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let e : ↥(OL K) ≃+* 𝒪[↥K.1] := intEquiv K
  let es : 𝒪[↥K.1] →+* ↥(OL K) := (e.symm : 𝒪[↥K.1] →+* ↥(OL K))
  have hp : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hf := isLubinTateSeries_ltPoly (e π)
  have hm := map_ltSeries K hp
  have hes : (intEquiv K).symm (e π) = π := e.symm_apply_apply π
  rw [hes] at hm
  have hF : PowerSeries.map es (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = ltSeries π := by
    rw [← hm]
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _
  have hF0 : PowerSeries.constantCoeff (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = 0 :=
    hf.constantCoeff_eq_zero
  let h := lubinTateHom hp hf hf (e a)
  have h0 : PowerSeries.constantCoeff h.toPowerSeries = 0 := h.constantCoeff_eq_zero
  have h1 : PowerSeries.coeff 1 h.toPowerSeries = e a := coeff_one_lubinTateHom hp hf hf (e a)
  have hs := subst_lubinTateHom hp hf hf (e a)
  refine ⟨PowerSeries.map es h.toPowerSeries, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rw [PowerSeries.coeff_map, h1]
    exact e.symm_apply_apply a
  · exact map_subst_comm es hF hF0 h0 hs

end GlobalTheory.CompanionTheory.LTPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExistsStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_endomorphism_series_exists : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_series_comm | exact GlobalTheory.CompanionTheory.LTPer.exists_series_comm | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_series_comm <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinates
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar

theorem tup_coord_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  intro F E _ _ _ _ _ σ _ e τ Θ hco n M
  have hΘ : IsHomeomorph Θ := hco.1
  have hΘc : Continuous Θ := hΘ.continuous
  have hs : Continuous (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) := by
    have h := (IsHomeomorph.homeomorph (⇑Θ) hΘ).symm.continuous
    convert h using 1
    funext y
    apply Θ.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph (⇑Θ) hΘ).apply_symm_apply y).symm
  let Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    { toFun := fun X w a i => Θ (X a i) w
      invFun := fun Y a i => Θ.symm (fun w => Y w a i)
      left_inv := fun X => by funext a i; simp
      right_inv := fun Y => by funext w a i; simp
      map_add' := fun X X' => by funext w a i; simp }
  have hc' : Continuous (fun (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) (a : Fin n)
      (i : Fin M) => Θ (X a i) w) := by fun_prop
  have hcs' : Continuous (fun (Y : InfinitePlace F → Fin n → Fin M → ℂ) (a : Fin n) (i : Fin M) =>
      Θ.symm (fun w => Y w a i)) := by fun_prop
  have hc : Continuous Φ := hc'
  have hcs : Continuous Φ.symm := hcs'
  refine ⟨Φ, fun X => rfl, hc, hcs, fun μ hμ => ?_⟩
  haveI := hμ
  refine ⟨AddEquiv.isAddHaarMeasure_map μ Φ hc hcs, fun g => ?_⟩
  let h : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    ⟨Φ.toEquiv, hc, hcs⟩
  exact (h.measurableEmbedding.integral_map g).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinatesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar <;> assumption)
end
end

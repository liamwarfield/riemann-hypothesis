module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieComb

open GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem isLieComb_iff_tanExp (c : Fin n → R) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = tanExp v c := isLieComb_iff_lieExp c w

theorem isTangent_tanExp (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) : IsTangent (tanExp v c) :=
  (isTan_iff _).1 (isTanOver_tanExp hv c)

def combHom (hv : ∀ i, IsTangent (v i)) :
    (Fin n → R) →+ Additive (sp (R₀ := R) (DualNumber R) ⟶ G) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul (tanExp v c)) (fun c c' => by
    rw [← ofMul_mul]
    refine congrArg Additive.ofMul ?_
    rw [← lieExp_add hv _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
      (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
    exact lieExp_congr _ (fun i => TrivSqZeroExt.inr_add _ _ _) _ _)

theorem tanExp_tanExp (hv : ∀ i, IsTangent (v i)) {m : ℕ} (M : Fin m → Fin n → R)
    (c : Fin m → R) : tanExp (fun i => tanExp v (M i)) c = tanExp v (∑ i, c i • M i) := by
  change _ = (combHom hv (∑ i, c i • M i)).toMul
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, toMul_sum, tanExp, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (comp_lieExp v _ _ _).trans ?_
  exact lieExp_congr _ (fun j => by
    simp [epsTo, dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr,
      mul_comm, smul_smul]) _ _

theorem tanExp_single (hv : ∀ i, IsTangent (v i)) (i : Fin n) :
    tanExp v (Pi.single i (1 : R)) = v i := by
  rw [tanExp, lieExp, Finset.prod_eq_single i]
  · have : ∀ h, epsTo R (inr ((Pi.single i (1 : R) : Fin n → R) i) : DualNumber R) h =
        AlgHom.id R _ := fun h => DualNumber.algHom_ext (by
      rw [epsTo_eps, Pi.single_eq_same]; rfl)
    rw [this, spMap_id]
    exact Category.id_comp _
  · intro j _ hj
    exact epsTo_zero_comp ((isTan_iff _).2 (hv j)) _ (by simp [Pi.single_eq_of_ne hj]) _
  · simp

theorem isLieBasis_iff_isUnit_det (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) R) :
    IsLieBasis (fun i => tanExp v (M i)) ↔ IsUnit M.det := by
  have key : ∀ c : Fin n → R,
      tanExp (fun i => tanExp v (M i)) c = tanExp v (Matrix.vecMul c M) := fun c => by
    rw [Matrix.vecMul_eq_sum]
    exact tanExp_tanExp hv.1 (fun i => M i) c
  have hinj : Function.Injective (fun c : Fin n → R => tanExp v c) := by
    intro a b hab
    obtain ⟨c, hc, hu⟩ := hv.2 (tanExp v b) (isTangent_tanExp hv.1 b)
    have ha : IsLieComb a v (tanExp v b) :=
      (isLieComb_iff_tanExp _ _).2 hab.symm
    have hb : IsLieComb b v (tanExp v b) :=
      (isLieComb_iff_tanExp _ _).2 rfl
    exact (hu a ha).trans (hu b hb).symm
  rw [← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    refine Matrix.vecMul_surjective_iff_isUnit.1 fun d => ?_
    obtain ⟨c, hc, -⟩ := h.2 _ (isTangent_tanExp hv.1 d)
    rw [isLieComb_iff_tanExp, key] at hc
    exact ⟨c, (hinj hc).symm⟩
  · intro h
    refine ⟨fun i => isTangent_tanExp hv.1 _, fun w hw => ?_⟩
    obtain ⟨d, hd, -⟩ := hv.2 w hw
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.2 h d
    have hc' : Matrix.vecMul c M = d := hc
    rw [isLieComb_iff_tanExp] at hd
    refine ⟨c, ?_, fun c' h' => ?_⟩
    · change IsLieComb _ _ _
      rw [isLieComb_iff_tanExp, key, hc', hd]
    · change IsLieComb _ _ _ at h'
      rw [isLieComb_iff_tanExp, key, hd, ← hc'] at h'
      exact Matrix.vecMul_injective_of_isUnit h (hinj h').symm

theorem lieComb_algebra (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (hv : ∀ i, IsTangent (v i)) :
    (∀ c, ∃! w, IsLieComb c v w) ∧ (∀ c w, IsLieComb c v w → IsTangent w) ∧
    (∀ (m : ℕ) (M : Fin m → Fin n → R) (v' : Fin m → (epsR R ⟶ G)) (c : Fin m → R) (w),
      (∀ i, IsLieComb (M i) v (v' i)) → IsLieComb c v' w → IsLieComb (∑ i, c i • M i) v w) ∧
    (∀ i, IsLieComb (Pi.single i 1) v (v i)) ∧
    ∀ (M : Matrix (Fin n) (Fin n) R) (v' : Fin n → (epsR R ⟶ G)), IsLieBasis v →
      (∀ i, IsLieComb (M i) v (v' i)) → (IsLieBasis v' ↔ IsUnit M.det) := by
  refine ⟨fun c => ⟨tanExp v c, (isLieComb_iff_tanExp _ _).2 rfl,
    fun w hw => (isLieComb_iff_tanExp _ _).1 hw⟩, fun c w hw => ?_, fun m M v' c w hM hw => ?_,
    fun i => (isLieComb_iff_tanExp _ _).2 (tanExp_single hv i).symm, fun M v' hb hM => ?_⟩
  · rw [(isLieComb_iff_tanExp _ _).1 hw]
    exact isTangent_tanExp hv c
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    rw [isLieComb_iff_tanExp] at hw ⊢
    rw [hw, tanExp_tanExp hv]
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    exact isLieBasis_iff_isUnit_det hb M

end GlobalTheory.LieComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace UnifCompare

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

lemma mem_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z ∈ u₀.Λ ↔ z ∈ u.Λ := by
  rw [← u₀.ker, ← u.ker, hF]

lemma injective (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) : Function.Injective F := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  have hm : ∀ t : ℂ, t • z ∈ u.Λ := fun t => by
    rw [← mem_iff u u₀ F hF, map_smul, hz, smul_zero]
    exact u₀.Λ.zero_mem
  have := u.discrete
  have hc : Continuous fun t : ℂ => (⟨t • z, hm t⟩ : u.Λ) :=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val h

lemma isDiff_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) :
    u.IsDiff w v ↔ u₀.IsDiff (F w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w =
        fderiv ℂ (fun z => valAt' (u₀.ex z).left U f) 0 (F w) := fun U f => by
    have e : (fun z => valAt' (u.ex z).left U f) = (fun z => valAt' (u₀.ex z).left U f) ∘ F := by
      funext z
      simp only [Function.comp, hF]
    rw [e, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  simp only [HolUnif.IsDiff, key]


open PullHermitian in
lemma hermForm_eq (hL : L.IsLB) (u u₀ : HolUnif A L g) {Hm H₀ : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} {χ₀ : u₀.Λ → ℂ} (hu : u.IsAH Hm χ) (hu₀ : u₀.IsAH H₀ χ₀)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u₀.ex (F z) = u.ex z) (z w : Fin g → ℂ) :
    hermForm H₀ (F z) (F w) = hermForm Hm z w := by
  have hΛ : ∀ l : u.Λ, F l ∈ u₀.Λ := fun l => (mem_iff u u₀ F hF l).2 l.2
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * H₀ * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu₀.1
  have hsub : ∀ z w, hermForm (Hm - H₂) z w = hermForm Hm z w - hermForm H₀ (F z) (F w) :=
    fun z w => by
      have := hermForm_sub_smul Hm H₂ 1 1 z w
      rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, hermForm_pull] at this
  have := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    (Hm - H₂) (fun l => χ l / χ₀ ⟨F l, hΛ l⟩) r (hu.1.sub hH₂h)
    (fun l => by simp [hu.2.2.1, hu₀.2.2.1]) hr
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      rw [hrφ i z hi]
      exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi))
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu₀.2.2.2 ⟨F l, hΛ l⟩ i (F z) (tr hi)
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ₀ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu₀.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ i z hi, hrφ i (z + l) hi']
      simp only [hsub, map_add (f := _)]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ H₀.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ H₀.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
        rw [← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      field_simp)
  have h := hsub z w
  rw [key.1] at h
  have h0 : hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z w = 0 := by simp [hermForm]
  rw [h0] at h
  exact (sub_eq_zero.1 h.symm).symm

end UnifCompare


open UnifCompare in
theorem unimodular_and_tangent_of_isAH :
    ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∀ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    (∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro hT P rig hrig u Hm χ hu
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, hEb, -⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  have hinj := injective u u₀ F hF
  let e : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun z => rfl
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v hv' => ?_, fun w => ?_⟩
  · let φ : u.Λ ≃ₗ[ℤ] u₀.Λ :=
      { toFun := fun a => ⟨e a, (mem_iff u u₀ F hF a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (mem_iff u u₀ F hF _).1 (by
          rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e a.1 b.1)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n a.1)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }
    refine ⟨φ.dualMap.toLinearMap ∘ₗ E₀ ∘ₗ φ.toLinearMap, fun a b => ?_,
      φ.dualMap.bijective.comp (hEb.comp φ.bijective)⟩
    rw [← hermForm_eq P.isLB u u₀ hu hu₀ F hF]
    exact hE (φ a) (φ b)
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharBlockDiagonal
noncomputable section

open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaPow

variable {j g G : ℕ}

theorem dotProduct_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G) (x y : Fin G → R) :
    x ⬝ᵥ y = ∑ i : Fin j, (fun k => x (e (i, k))) ⬝ᵥ (fun k => y (e (i, k))) := by
  unfold dotProduct
  rw [← e.sum_comp, Fintype.sum_prod_type]

theorem mulVec_blocks {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) (y : Fin G → R) (i : Fin j) :
    (fun k => ((Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) *ᵥ y) (e (i, k))) =
      M *ᵥ fun k => y (e (i, k)) := by
  funext k
  simp only [mulVec, dotProduct, of_apply]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

theorem posDef_blocks (e : Fin j × Fin g ≃ Fin G) {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.PosDef) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext p q
    have h := hM.1.apply (e.symm p).2 (e.symm q).2
    simp only [conjTranspose_apply, of_apply, star_trivial] at h ⊢
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, h]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · rw [dotProduct_blocks e]
    simp only [mulVec_blocks]
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun i _ => ?_) ⟨(e.symm p).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg _
    · refine (posDef_iff_dotProduct_mulVec.1 hM).2 (x := fun k => x (e ((e.symm p).1, k))) ?_
      refine Function.ne_iff.2 ⟨(e.symm p).2, ?_⟩
      simpa using hp

def blockEquiv (e : Fin j × Fin g ≃ Fin G) : (Fin G → ℤ) ≃ (Fin j → Fin g → ℤ) :=
  (Equiv.arrowCongr e.symm (Equiv.refl ℤ)).trans (Equiv.curry _ _ _)

theorem blockEquiv_apply (e : Fin j × Fin g ≃ Fin G) (m : Fin G → ℤ) (i : Fin j) (k : Fin g) :
    blockEquiv e m i k = m (e (i, k)) := rfl

theorem thTerm_blocks (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin G → ℂ) (m : Fin G → ℤ) :
    CanTh.thTerm (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        τ (e.symm p).2 (e.symm q).2 else 0) (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z m =
      ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (blockEquiv e m i) := by
  unfold CanTh.thTerm
  rw [← Complex.exp_sum, dotProduct_blocks e, dotProduct_blocks e (y := z + _), Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_blocks]
  simp only [Pi.add_def, Equiv.symm_apply_apply, blockEquiv_apply]

end GlobalTheory.ThetaPow

namespace GlobalTheory


open ThetaPow in
theorem thetaChar_blockDiagonal (j g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (G : ℕ)
    (e : Fin j × Fin g ≃ Fin G) (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    let τ' : Matrix (Fin G) (Fin G) ℂ := Matrix.of fun p q =>
      if (e.symm p).1 = (e.symm q).1 then τ (e.symm p).2 (e.symm q).2 else 0
    τ'.IsSymm ∧ (τ'.map Complex.im).PosDef ∧ ∀ z : Fin G → ℂ,
      thetaChar τ' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) z =
        ∏ i : Fin j, thetaChar τ (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) (fun k => z (e (i, k))) := by
  intro τ'
  refine ⟨?_, ?_, fun z => ?_⟩
  · ext p q
    simp only [τ', transpose_apply, of_apply]
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, hs.apply]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · convert posDef_blocks e hp using 1
    ext p q
    simp only [τ', map_apply, of_apply]
    split_ifs <;> simp
  · rw [CanTh.thetaChar_eq_tsum τ' (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z]
    simp only [τ', thTerm_blocks]
    rw [(blockEquiv e).tsum_eq
      (fun m => ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (m i))]
    exact (CanTh.hasSum_prod_thTerm (τ := fun _ : Fin j => τ) (fun _ => CanTh.mem_thetaDomain hp)
      (fun _ => a) (fun _ => b) (fun i k => z (e (i, k)))).tsum_eq

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem det_blocks {j g G : ℕ} {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R).det = M.det ^ j := by
  have h : (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) =
      Matrix.reindex ((Equiv.prodComm _ _).trans e) ((Equiv.prodComm _ _).trans e)
        (Matrix.blockDiagonal fun _ : Fin j => M) := by
    ext p q
    simp [Matrix.blockDiagonal_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp

theorem lattice_blocks {j g G : ℕ} (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin G → ℂ) :
    (∀ i, ∃ m n : Fin g → ℤ, (fun k => z (e (i, k))) = (fun k => (m k : ℂ)) + τ.mulVec (fun k => (n k : ℂ))) ↔
      ∃ m n : Fin G → ℤ, z = (fun p => (m p : ℂ)) +
        (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
          τ (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℂ).mulVec (fun p => (n p : ℂ)) := by
  constructor
  · intro h
    choose m n h using h
    refine ⟨fun p => m (e.symm p).1 (e.symm p).2, fun p => n (e.symm p).1 (e.symm p).2, ?_⟩
    funext p
    obtain ⟨⟨i, k⟩, rfl⟩ := e.surjective p
    have h₁ := congrFun (ThetaPow.mulVec_blocks e τ (fun p => (n (e.symm p).1 (e.symm p).2 : ℂ)) i) k
    have h₂ := congrFun (h i) k
    simp only [Equiv.symm_apply_apply, Pi.add_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  · rintro ⟨m, n, rfl⟩ i
    refine ⟨fun k => m (e (i, k)), fun k => n (e (i, k)), ?_⟩
    rw [← ThetaPow.mulVec_blocks e τ (fun p => (n p : ℂ)) i]
    rfl

theorem normalAt_pow : ∀ (x y : KeyIn ℂ) (j : ℕ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℝ) (c : ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → GlobalTheory.KeyPow.NormalAt x τ M (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) c → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (τ' M' : Matrix (Fin y.P.g) (Fin y.P.g) ℂ), M'.det = M.det ^ j ∧ GlobalTheory.KeyPow.NormalAt y τ' M' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) (c ^ j) := by
  rintro x y j τ M a b c hp ⟨u, hs, hd, hΛ, hr, hf, hv⟩
  obtain ⟨e, u', hΛ', hr', hf', hv'⟩ := GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum x y j u _
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M) hp hr hf hv
  obtain ⟨hs', hd', hθ⟩ := thetaChar_blockDiagonal j _ τ a b _ e hs hd
  refine ⟨e, _, _, det_blocks e M, u', hs', hd', fun z => ?_, hr', ?_, fun p => ?_⟩
  · rw [hΛ', ← lattice_blocks]
    exact forall_congr' fun i => hΛ _
  · convert hf' using 2 with z
    rw [hθ, Finset.prod_mul_distrib]
    simp
  · convert hv' p using 1
    funext q
    simp only [Pi.smul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp

end GlobalTheory.KeyPow
end
end

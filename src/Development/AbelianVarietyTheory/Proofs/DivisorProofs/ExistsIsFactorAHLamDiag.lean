module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem padd_eq {T : Over (Sp ℂ)} (a b : T ⟶ A) : padd A a b = a * b := (Hom.mul_def a b).symm

theorem pzero_eq (T : Over (Sp ℂ)) : pzero A T = 1 := by
  rw [pzero, Hom.one_def]

theorem pt_diag_psum (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (I : Finset (Fin 2)) :
    y ≫ (lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I) = y ^ I.card := by
  have h0 : y ≫ lift (𝟙 A) (𝟙 A) ≫ fst A A = y := by simp
  have h1 : y ≫ lift (𝟙 A) (𝟙 A) ≫ snd A A = y := by simp
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd_eq, pzero_eq, x2, List.finRange_succ, comp_mul, comp_one, h0, h1, pow_two]

theorem sum_exp_sq :
    (∑ I : ULift.{0} (Finset (Fin 2)), (((-1 : ℤ) ^ (2 - I.down.card) : ℤ) : ℂ) * ((I.down.card : ℕ) : ℂ) ^ 2) = 2 := by
  have hZ : (∑ I : Finset (Fin 2), ((-1 : ℤ) ^ (2 - I.card)) * (I.card : ℤ) ^ 2) = 2 := by decide
  have hU : (∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) * (I.down.card : ℤ) ^ 2) = 2 :=
    (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) * (I.card : ℤ) ^ 2)
      (fun _ => rfl)).trans hZ
  exact_mod_cast hU

theorem herm_smul_nat {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℕ) (z l : Fin g → ℂ) :
    ((c : ℂ) • z) ⬝ᵥ Hm.mulVec (star ((c : ℂ) • l)) = (c : ℂ) ^ 2 * (z ⬝ᵥ Hm.mulVec (star l)) := by
  have hs : star ((c : ℂ) • l) = (c : ℂ) • star l := by
    rw [star_smul]; simp
  rw [hs, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def diagSum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : ULift.{0} (Finset (Fin 2))) : A ⟶ A :=
  lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I.down

theorem chart (M : LB A.left) (x : Sp ℂ ⟶ A.left) (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J ↔
      ∀ I, ⊤ ≤ (x ≫ (diagSum A I).left) ⁻¹ᵁ M.U (J PUnit.unit I) := by
  rw [GlobalTheory.ThetaPoint.top_le_pull_iff]
  show ⊤ ≤ (x ≫ (lift (𝟙 A) (𝟙 A)).left) ⁻¹ᵁ
      LB.wchart M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) (J PUnit.unit) ↔ _
  refine (CubeValues.le_preimage_wchart _ M (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left)
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι)).trans ?_
  simp only [diagSum, Over.comp_left, Category.assoc]

theorem chart' (M : LB A.left) (x : Sp ℂ ⟶ A.left) (j : ULift.{0} (Finset (Fin 2)) → M.ι) :
    (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ LB.wchart M (fun I => (diagSum A I).left) j ↔
      ∀ I, ⊤ ≤ (x ≫ (diagSum A I).left) ⁻¹ᵁ M.U (j I) :=
  CubeValues.le_preimage_wchart _ _ _ _

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

def expo (I : ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - I.down.card)

theorem val_g (M : LB A.left) (x : Sp ℂ ⟶ A.left) (J J' : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι)
    (h : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J)
    (h' : (⊤ : (Sp ℂ).Opens) ≤ x ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J') :
    valAt' x (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J ⊓ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J')
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).g J J').val =
      valAt' x ((M.LinComb (fun I => (diagSum A I).left) expo).U (J PUnit.unit) ⊓
          (M.LinComb (fun I => (diagSum A I).left) expo).U (J' PUnit.unit))
        ((M.LinComb (fun I => (diagSum A I).left) expo).g (J PUnit.unit) (J' PUnit.unit)).val := by
  refine (GlobalTheory.ThetaPoint.valAt'_pull_g _ _ _ _ _ h h').trans ?_
  have hL := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h
  have hL' := (GlobalTheory.ThetaPoint.top_le_pull_iff _ _ _ _).1 h'
  have hc := (chart' M x (J PUnit.unit)).2 ((chart M x J).1 h)
  have hc' := (chart' M x (J' PUnit.unit)).2 ((chart M x J').1 h')
  refine (CubeValues.val_linComb (x ≫ (lift (𝟙 A) (𝟙 A)).left) valAt'_rules M
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum A (x2 A) I.down).left) expo
    (J PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) (J' PUnit.unit : ULift.{0} (Finset (Fin 2)) → M.ι) hL hL').trans ?_
  refine Eq.trans ?_ (CubeValues.val_linComb x valAt'_rules M (fun I => (diagSum A I).left) expo _ _ hc hc').symm
  simp only [diagSum, Over.comp_left, Category.assoc]

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {M : LB A.left} {g : ℕ}

def mulCard (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ((I.down.card : ℕ) : ℂ) • LinearMap.id

theorem mulCard_apply (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) :
    mulCard g I z = ((I.down.card : ℕ) : ℂ) • z := rfl

theorem ex_mulCard (u : HolUnif A M g) (I : ULift.{0} (Finset (Fin 2))) (z : Fin g → ℂ) :
    u.ex (mulCard g I z) = u.ex z ≫ diagSum A I := by
  rw [mulCard_apply, Nat.cast_smul_eq_nsmul, holUnif_ex_nsmul_eq_pow]
  exact (pt_diag_psum (u.ex z) I.down).symm

theorem smul_mem_lat (u : HolUnif A M g) (l : u.Λ) (I : ULift.{0} (Finset (Fin 2))) :
    ((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ) ∈ u.Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem l.2 _

def diagUnif (u : HolUnif A M g) : HolUnif A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) g :=
  let u₁ := linCombUnif u u (diagSum A) (mulCard g) expo (ex_mulCard u)
  have hc : ∀ (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) (z : Fin g → ℂ),
      (⊤ : (Sp ℂ).Opens) ≤ (u.ex z).left ⁻¹ᵁ ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).U J →
      (⊤ : (Sp ℂ).Opens) ≤ (u₁.ex z).left ⁻¹ᵁ (M.LinComb (fun I => (diagSum A I).left) expo).U (J PUnit.unit) :=
    fun J z hz => (chart' M _ (J PUnit.unit)).2 ((chart M _ J).1 hz)
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun J z => u₁.fr (J PUnit.unit) z
    fr_hol := fun J => (u₁.fr_hol (J PUnit.unit)).mono fun z hz => hc J z hz
    fr_ne := fun J z hz => u₁.fr_ne _ z (hc J z hz)
    fr_compat := fun J J' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      rw [val_g M _ J J' h1 h2]
      exact u₁.fr_compat _ _ z ((top_le_preimage_inf _ _ _).2 ⟨hc J z h1, hc J' z h2⟩) }

theorem diagUnif_fr (u : HolUnif A M g) (J : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).ι) (z : Fin g → ℂ) :
    (diagUnif u).fr J z = ∏ I, u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • z) ^ expo I := rfl

theorem diagUnif_ex (u : HolUnif A M g) : (diagUnif u).ex = u.ex := rfl

def diagChar (u : HolUnif A M g) (χ : u.Λ → ℂ) (l : u.Λ) : ℂ :=
  ∏ I, χ ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ ^ expo I

end GlobalTheory.TorusRM.DiagFrame

namespace GlobalTheory.TorusRM.DiagFrame

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {M : LB A.left} {g : ℕ}

theorem isFactorAH_diagUnif (u : HolUnif A M g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hF : IsFactorAH u Hm χ) : IsFactorAH (diagUnif u) ((2 : ℂ) • Hm) (diagChar u χ) := by
  refine ⟨?_, fun l => ?_, fun l J z hz => ?_⟩
  · show Matrix.conjTranspose ((2 : ℂ) • Hm) = (2 : ℂ) • Hm
    rw [Matrix.conjTranspose_smul, hF.1.eq]
    simp
  · show ‖∏ I, _‖ = 1
    rw [norm_prod]
    exact Finset.prod_eq_one fun I _ => by rw [norm_zpow, hF.2.1, one_zpow]
  · have hc : ∀ I, (⊤ : (Sp ℂ).Opens) ≤ (u.ex (((I.down.card : ℕ) : ℂ) • z)).left ⁻¹ᵁ M.U (J PUnit.unit I) := by
      intro I
      have h := (chart M _ J).1 hz I
      rw [← mulCard_apply, ex_mulCard, Over.comp_left]
      exact h
    set E : ℂ := Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) with hE
    have key : ∀ I : ULift.{0} (Finset (Fin 2)),
        u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • z) ^ expo I =
          χ ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ ^ expo I *
            Complex.exp ((expo I : ℂ) * ((((I.down.card : ℕ) : ℂ)) ^ 2 * E)) *
            u.fr (J PUnit.unit I) (((I.down.card : ℕ) : ℂ) • (z + (l : Fin g → ℂ))) ^ expo I := by
      intro I
      rw [hF.2.2 ⟨((I.down.card : ℕ) : ℂ) • (l : Fin g → ℂ), smul_mem_lat u l I⟩ (J PUnit.unit I) _ (hc I)]
      simp only []
      rw [herm_smul_nat, herm_smul_nat, smul_add, mul_zpow, mul_zpow, Complex.exp_int_mul]
      congr 3
      rw [hE]
      ring_nf
    rw [diagUnif_fr, diagUnif_fr, Finset.prod_congr rfl fun I _ => key I, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    have hs := sum_exp_sq
    have e1 : (∑ I : ULift.{0} (Finset (Fin 2)), (expo I : ℂ) * ((((I.down.card : ℕ) : ℂ)) ^ 2 * E)) =
        (∑ I : ULift.{0} (Finset (Fin 2)), (((-1 : ℤ) ^ (2 - I.down.card) : ℤ) : ℂ) * ((I.down.card : ℕ) : ℂ) ^ 2) * E := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [expo]
      ring
    rw [e1, hs, hE, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    congr 1
    ring

end GlobalTheory.TorusRM.DiagFrame


open GlobalTheory GlobalTheory.TorusRM.DiagFrame in
theorem GlobalTheory.TorusRM.exists_isFactorAH_lam_diag : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → IsFactorAH u Hm χ →
    ∃ (u' : HolUnif A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) g) (χ' : u'.Λ → ℂ),
      u'.ex = u.ex ∧ IsFactorAH u' ((2 : ℂ) • Hm) χ' := by
  intro g A _ hA M u Hm χ hM hF
  haveI : IsCommMonObj A := hA.comm
  exact ⟨diagUnif u, diagChar u χ, rfl, isFactorAH_diagUnif u hF⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifHom


open GlobalTheory.SS GlobalTheory.EighthPowerFactor CechPic in
theorem exists_polAV_retract_dim (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ)
    (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension g B.hom) (M : LB B.left) (hM : M.IsLB)
    (ha : Out.RelAmple B M) (hK : Out.KTriv B M) :
    ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  have := hB.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns hB hM g).Principal :=
    ⟨relAmple_diag_lam hB hM (exists_gen_theta_of_isAbelianScheme k B hB M hM) ha,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, -⟩, -, -, -⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g _ W _ a w w' bas hW hb
    hw hw' hs 1 k b _ (𝟙 _) (siegOne L₁.globalFns hB hM g) (one_pow _) odd_one hc hd
  obtain ⟨i, hi, -⟩ := hu B fun _ => 𝟙 B
  refine ⟨t.pol, i, pr 0, rfl, isMonHom_of_coord hpr hu fun u => ?_, hpr 0, hi 0⟩
  rw [hi u]
  exact inferInstanceAs (IsMonHom (𝟙 B))

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom


open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel GlobalTheory.HolUnifEnd in
theorem exists_linear_factor (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hgA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (u : HolUnif A L g) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (v : HolUnif Q.A Q.L (8 * g)) (i : A ⟶ Q.A) (r : Q.A ⟶ A)
      (J : (Fin g → ℂ) →ₗ[ℂ] (Fin (8 * g) → ℂ)) (R : (Fin (8 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (m : ℕ),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ (∀ z, v.ex (J z) = u.ex z ≫ i) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ r) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z := by
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', hQg, hi', hr', hir'⟩ := exists_polAV_retract_dim ℂ B g hB hgB MB hMB hamp hK
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  suffices key : ∀ n, Q.g = n → ∃ (v : HolUnif Q.A Q.L n) (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ))
      (R : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, v.ex (J z) = u.ex z ≫ (i ≫ i')) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ (r' ≫ r)) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z by
    obtain ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩ := key (8 * g) hQg
    exact ⟨Q, v, i ≫ i', r' ≫ r, J, R, m, hQg, inferInstance, inferInstance, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩
  rintro n rfl
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance
  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i
  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0
  exact ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom


open GlobalTheory.HolUnifEnd in
theorem exists_isMonHom_of_map_lattice :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g : ℕ), IsAbelianScheme A → IsAbelianScheme A' →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom →
    ∀ (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g) (u' : HolUnif A' L' g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u'.Λ) → ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  intro A A' _ _ g hA hA' hgA hgA' L L' u u' M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q' (8 * g) v v'
    (J' ∘ₗ M ∘ₗ R) hQ hQ' (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirational
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hs E
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hs
  let V : ValuationSubring Y.functionField := E.ring.comap e.symm.toRingHom
  have hV (f : X.functionField) : f ∈ E.ring ↔ functionFieldMap s f ∈ V := by
    change f ∈ E.ring ↔ e.symm (e f) ∈ E.ring
    rw [e.symm_apply_apply]
  let φ : E.ring →+* V :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict V fun a => (hV _).1 a.2
  have hφ : Function.Bijective φ :=
    ⟨fun _ _ h => Subtype.ext (hs.1 (congrArg Subtype.val h)),
      fun f => ⟨⟨e.symm f.1, f.2⟩, Subtype.ext (e.apply_symm_apply f.1)⟩⟩
  have hc (a : k) : functionFieldMap s (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a :=
    RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s) a
  refine ⟨⟨V, fun a => hc a ▸ (hV _).1 (E.const_mem a),
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective φ hφ), ?_⟩, hV⟩
  have h3 := E.essFiniteType.comp (RingHom.FiniteType.of_surjective φ hφ.2).essFiniteType
  convert h3 using 1
  exact RingHom.ext fun a => Subtype.ext (hc a).symm

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_source_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over | exact GlobalTheory.Discrepancy.DivOver.exists_over | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.ord_fnPull_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  intro k _ X Y _ _ p s _ hs E' E h g
  let φ : E.ring →+* E'.ring :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict E'.ring fun a => (h _).1 a.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hs.1 (congrArg Subtype.val e)), fun b => ?_⟩
    obtain ⟨a, ha⟩ := hs.2 (b : Y.functionField)
    exact ⟨⟨a, (h a).2 (ha ▸ b.2)⟩, Subtype.ext ha⟩
  let e : E.ring ≃+* E'.ring := RingEquiv.ofBijective φ hφ
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, u, eg⟩ := exists_eq_unit_mul_zpow ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := X.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := Y.functionField) (ht.map e)
    (Units.map e.toMonoidHom u) m
  rw [← eg, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have eg' : ((fnPull s g : Y.functionFieldˣ) : Y.functionField) =
      algebraMap E'.ring Y.functionField (Units.map e.toMonoidHom u : E'.ringˣ) *
        algebraMap E'.ring Y.functionField (e t) ^ m := by
    change functionFieldMap s (g : X.functionField) = _
    rw [eg, map_mul, map_zpow₀]
    rfl
  rw [← eg', ordTop_vw_of_ne_zero _ (fnPull s g).ne_zero, WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ord_functionField_pullback_primeDivisor_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  first | exact @GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective | exact GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective | (intros; apply GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ev_eq_fv_of_triv {R : Type} [CommRing R] {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (x : Pt X D) (x' : Pt X D')
    (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x') (h : ∀ r : D, a.φ r = φ r) :
    spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  have e : spOver φ ≫ x = x' := by
    have h0 : a.φ₀ = (φ : D →+* D') := RingHom.ext fun r ↦ (a.comm r).trans (h r)
    have hp := a.pt
    rw [h0] at hp
    exact Over.OverMorphism.ext hp
  subst x'
  refine ⟨rfl, ?_⟩
  have ha : a = trivMap φ x := Thick.Hom.ext' (AlgHom.ext h)
  exact congrArg (ev f) ha

theorem fv_isCoc_and_ev_eq :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))),
      IsCoc (whole X) (fv f) ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
          (x : Pt X D) (x' : Pt X D') (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x'),
          (∀ r : D, a.φ r = φ r) → spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  intro R _ X f
  refine ⟨?_, fun D _ _ D' _ _ x x' φ a h ↦ ev_eq_fv_of_triv f D D' x x' φ a h⟩
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  let y : Pt X D' := spOver φ ≫ x
  let z : Pt X D'' := spOver ψ ≫ y
  have h := (ev_eq_fv_of_triv f D D'' x z (ψ.comp φ)
    (trivMap φ x ≫ trivMap ψ y) (fun _ ↦ rfl)).2
  exact h.symm.trans (ev_comp f (trivMap φ x) (trivMap ψ y))

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEqStatement
alias GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq :=
  GlobalTheory.PtExt.fv_isCoc_and_ev_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def fracMap (ρ : R →+* R') (hρ : Function.Injective ρ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (A := R) (B := R') (K := FractionRing R) (L := FractionRing R') (j := ρ) hρ

theorem fracMap_algebraMap (ρ : R →+* R') (hρ : Function.Injective ρ) (r : R) :
    fracMap ρ hρ (algebraMap R _ r) = algebraMap R' _ (ρ r) := by
  simp [fracMap, IsFractionRing.map]

theorem jK_comp_spMap (ρ : R →+* R') (hρ : Function.Injective ρ) :
    jK R' ≫ spMap ρ = spMap (fracMap ρ hρ) ≫ jK R := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (fracMap_algebraMap ρ hρ r).symm

def fracAut (σ : R' ≃+* R') : FractionRing R' ≃+* FractionRing R' :=
  IsFractionRing.ringEquivOfRingEquiv σ

theorem fracAut_algebraMap (σ : R' ≃+* R') (x : R') :
    fracAut σ (algebraMap R' _ x) = algebraMap R' _ (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

theorem fracAut_fracMap {ρ : R →+* R'} (hρ : Function.Injective ρ) (σ : Gal ρ) (x : FractionRing R) :
    fracAut σ.1 (fracMap ρ hρ x) = fracMap ρ hρ x := by
  have h : ((fracAut σ.1).toRingHom.comp (fracMap ρ hρ)) = fracMap ρ hρ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracMap_algebraMap, fracAut_algebraMap, σ.2 r]
  exact congrArg (fun f : FractionRing R →+* FractionRing R' => f x) h

def genMap {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ) (β : G'.left ⟶ G.left)
    (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _ ≫ spMap (fracMap ρ hρ)) (by
    rw [Category.assoc, hβ, ← Category.assoc, pullback.condition, Category.assoc, jK_comp_spMap ρ hρ,
      Category.assoc])

theorem genMap_fst {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β :=
  pullback.lift_fst _ _ _

theorem genMap_snd {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap ρ hρ) :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.GenDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

variable {K : Type} [Field K]

abbrev baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B] : K →+* B :=
  (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))

def transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) : Sp (DualNumber B) ⟶ A.left :=
  if h : ∃ w, IsTransl φ x v w then h.choose else spMap (algebraMap B (DualNumber B)) ≫ x

theorem isTransl_transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) : IsTransl φ x v (transl φ x v) := by
  have h : ∃ w, IsTransl φ x v w := exists_isTransl φ x hx v
  rw [transl, dite_eq_left h]
  exact h.choose_spec

def dlogAt {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) : B :=
  (valR (transl φ x v) Wo g.val).snd * valR x Wo g⁻¹.val

def chartVal {A : Over (Sp K)} [GrpObj A] {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (f : Γ(Z, Ω)) : B :=
  valR (x ≫ m) Ω f + algebraMap (DualNumber K) B DualNumber.eps *
    (valR (x ≫ m) Ω (δ f) + ∑ a, (∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g) *
      (valR (transl (baseMap K B) x (u a) ≫ m) Ω f).snd)

def IsChartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) {Z : Scheme.{0}} (m : A.left ⟶ Z)
    (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (l : Sp B ⟶ A'.left) : Prop :=
  l ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧ ⊤ ≤ (l ≫ m') ⁻¹ᵁ Ω ∧
    ∀ f, valR (l ≫ m') Ω f = chartVal m Ω δ u θ Wo g x f

def chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) {Z : Scheme.{0}}
    (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) : Sp B ⟶ A'.left :=
  if h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l then h.choose else x ≫ i

theorem isChartPt_chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left)
    {Z : Scheme.{0}} (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ}
    (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
    (h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l) :
    IsChartPt A' m m' Ω δ u θ Wo g x (chartPt A' i m m' Ω δ u θ Wo g x) := by
  rw [chartPt, dite_eq_left h]
  exact h.choose_spec

theorem valR_eq_ev {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (f : Γ(Z, U)) : valR z U f = ev z U h f := by
  rw [valR, dite_eq_left h]
  rfl

theorem IsChartPt.unique {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z}
    (hm' : IsPullback m' A'.hom h y1) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ}
    {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ}
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l l' : Sp B ⟶ A'.left}
    (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l) (hl' : IsChartPt A' m m' Ω.1 δ u θ Wo g x l') : l = l' := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  have e : ev (l ≫ m') Ω.1 h2 = ev (l' ≫ m') Ω.1 h2' := by
    ext f
    rw [← valR_eq_ev, ← valR_eq_ev, h3 f, h3' f]
  have e2 : l ≫ m' = l' ≫ m' := by
    rw [← GlobalTheory.FlagMod.spMap_ev (l ≫ m') Ω.2 h2, ← GlobalTheory.FlagMod.spMap_ev (l' ≫ m') Ω.2 h2', e]
  exact hm'.hom_ext e2 (h1.trans h1'.symm)

end GlobalTheory.CechKS

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProdUnifSq

variable {g : ℕ}

def halfL (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.castAdd g k)

def halfR (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.natAdd g k)

theorem halfL_apply (v : Fin (g + g) → ℂ) : halfL g v = fun k => v (Fin.castAdd g k) := rfl
theorem halfR_apply (v : Fin (g + g) → ℂ) : halfR g v = fun k => v (Fin.natAdd g k) := rfl

theorem halfL_append (x y : Fin g → ℂ) : halfL g (Fin.append x y) = x := by
  funext k; simp [halfL_apply]
theorem halfR_append (x y : Fin g → ℂ) : halfR g (Fin.append x y) = y := by
  funext k; exact Fin.append_right x y k

theorem append_halves (v : Fin (g + g) → ℂ) : Fin.append (halfL g v) (halfR g v) = v := by
  funext q
  refine Fin.addCases (fun k => ?_) (fun k => ?_) q
  · rw [Fin.append_left, halfL_apply]
  · rw [Fin.append_right, halfR_apply]

def sqLat (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin (g + g) → ℂ) :=
  Λ.comap ((halfL g).toLinearMap.restrictScalars ℤ) ⊓ Λ.comap ((halfR g).toLinearMap.restrictScalars ℤ)

theorem mem_sqLat (Λ : Submodule ℤ (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    v ∈ sqLat Λ ↔ halfL g v ∈ Λ ∧ halfR g v ∈ Λ := Iff.rfl

theorem sqLat_discrete (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] : DiscreteTopology (sqLat Λ) := by
  refine DiscreteTopology.of_continuous_injective (β := Λ × Λ)
    (f := fun z => (⟨halfL g z.1, z.2.1⟩, ⟨halfR g z.1, z.2.2⟩))
    (Continuous.prodMk (((halfL g).continuous.comp continuous_subtype_val).subtype_mk _)
      (((halfR g).continuous.comp continuous_subtype_val).subtype_mk _)) fun z z' h => ?_
  refine Subtype.ext ?_
  rw [← append_halves z.1, ← append_halves z'.1]
  simp only [Prod.mk.injEq] at h
  have h1 : halfL g z.1 = halfL g z'.1 := congrArg Subtype.val h.1
  have h2 : halfR g z.1 = halfR g z'.1 := congrArg Subtype.val h.2
  rw [h1, h2]

def appendL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

def appendR (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

theorem sqLat_full (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) = ⊤ := by
  have hL : Set.range (appendL g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendL g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append x 0) ∈ Λ
        rw [halfL_append]; exact hx
      · change halfR g (Fin.append x 0) ∈ Λ
        rw [halfR_append]; exact Λ.zero_mem
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  have hR : Set.range (appendR g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendR g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append 0 x) ∈ Λ
        rw [halfL_append]; exact Λ.zero_mem
      · change halfR g (Fin.append 0 x) ∈ Λ
        rw [halfR_append]; exact hx
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = appendL g (halfL g v) + appendR g (halfR g v) := by
    conv_lhs => rw [← append_halves v]
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [appendL, appendR, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Fin.append_left, Fin.append_right,
        Pi.zero_apply, add_zero, zero_add]
  rw [hv]
  exact Submodule.add_mem _ (hL ⟨_, rfl⟩) (hR ⟨_, rfl⟩)

variable (A : Over (Sp ℂ)) [GrpObj A]

abbrev trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def sqUnif {L : LB A.left} (u : HolUnif A L g) : HolUnif (A ⊗ A) (trivLB (A ⊗ A).left) (g + g) where
  ex v := lift (u.ex (halfL g v)) (u.ex (halfR g v))
  ex_add z w := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst, map_add (f := _), u.ex_add]
    · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd, map_add (f := _), u.ex_add]
  ex_onto p := by
    obtain ⟨x, hx⟩ := u.ex_onto (p ≫ fst _ _)
    obtain ⟨y, hy⟩ := u.ex_onto (p ≫ snd _ _)
    refine ⟨Fin.append x y, ?_⟩
    show lift (u.ex (halfL g (Fin.append x y))) (u.ex (halfR g (Fin.append x y))) = p
    rw [halfL_append, halfR_append, hx, hy]
    exact (CartesianMonoidalCategory.hom_ext _ _ (lift_fst _ _) (lift_snd _ _))
  Λ := sqLat u.Λ
  ker z := by
    rw [mem_sqLat, ← u.ker, ← u.ker]
    constructor
    · intro h
      constructor
      · have := congrArg (· ≫ fst A A) h
        simpa only [lift_fst, MonObj.one_comp] using this
      · have := congrArg (· ≫ snd A A) h
        simpa only [lift_snd, MonObj.one_comp] using this
    · rintro ⟨h1, h2⟩
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst, MonObj.one_comp, h1]
      · rw [lift_snd, MonObj.one_comp, h2]
  discrete := by
    have := u.discrete
    exact sqLat_discrete u.Λ
  full := sqLat_full u.Λ u.full
  hol := by
    have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
    refine GlobalTheory.PowUnif.isHolFamily_tensor A A _ ?_ ?_
    · simp only [lift_fst]
      exact hd.precomp (halfL g).differentiable
    · simp only [lift_snd]
      exact hd.precomp (halfR g).differentiable
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat i j z h := by
    rw [Units.val_one, valAt'_one _ h, _root_.one_mul]

end GlobalTheory.ProdUnifSq
end
end

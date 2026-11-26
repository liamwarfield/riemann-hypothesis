module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem mulB_assoc (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V y (mulB (L := L) P V y' w) = mulB (L := L) P V (mulB (L := L) P (Fin 1 → ↥L.1) y y') w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v c =>
        rw [mulB_tmul, mulB_tmul, mulB_tmul, mulB_tmul, Pi.smul_apply, smul_eq_mul, mul_smul, mul_assoc]
      | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']

theorem mulB_comm (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P (Fin 1 → ↥L.1) y y' = mulB (L := L) P (Fin 1 → ↥L.1) y' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      rw [mulB_tmul, mulB_tmul, mul_comm b b']
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
      simp [mul_comm]
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']

theorem one_mulB (w : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [mulB_tmul, one_smul, one_mul]
  | add w w' hw hw' => simp only [map_add (f := _), hw, hw']

variable {K : FinExt l}

theorem stRep_twist (ρs ρt : Representation ↥L.1 ↥(GK K) V) (χ : ↥(GK K) → ↥L.1)
    (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K)) (w : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g w = χ g • stRep P ρs g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [stRep_tmul, stRep_tmul, ht, TensorProduct.smul_tmul']
  | add w w' hw hw' => simp only [map_add (f := _), smul_add, hw, hw']

theorem stRep_trivial_one (g : ↥(GK K)) :
    stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) =
      (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  rw [stRep_tmul, map_one]
  rfl

end GlobalTheory.Pst.TwistLetters.Invert


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.Pst.TwistLetters.Invert in
theorem GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht y y' hinv z
  have hmτ : ∀ g w, stRep P ρm g w =
      χ g • stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w :=
    stRep_twist _ ρm χ (fun g v => by rw [hm]; rfl)
  have hτmul : ∀ g (a w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P),
      stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (mulB (L := L) P (Fin 1 → ↥L.1) a w) =
        mulB (L := L) P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a)
          (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w) := fun g a w =>
    stRep_mulB _ _ _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hsmul : ∀ g (a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P),
      stRep P ρs g (mulB (L := L) P V a w) =
        mulB (L := L) P V (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a) (stRep P ρs g w) :=
    fun g a w => stRep_mulB ρs ρs _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hτe := stRep_trivial_one (P := P) (L := L) (K := K)
  have hone : ∀ w : V ⊗[ℚ_[l]] Bst P, mulB (L := L) P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hone' : ∀ w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P,
      mulB (L := L) P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hχ : ∀ g, χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g⁻¹ * g) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by simp
    rw [map_mul, Module.End.mul_apply, hm, hm, h0] at h1
    have := congrFun h1 0
    simp at this
  have hcomm1 : ∀ a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, mulB (L := L) P (Fin 1 → ↥L.1) a ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = a := fun a => by
    rw [mulB_comm, hone']
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρm).mp y.2
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρt).mp z.2
  have hx : mulB (L := L) P V y' (z : V ⊗[ℚ_[l]] Bst P) ∈ Dpst P ρs := by
    refine (mem_Dpst P ρs).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
    have hy := h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
    have hz := h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    have hc := hχ g
    have hτy : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      rw [hmτ] at hy
      conv_rhs => rw [← hy]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hprod : mulB (L := L) P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = χ g • ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      have h3 := congrArg (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g) hinv
      rw [hτmul, hτy, hτe, mulB_smul] at h3
      rw [← h3, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hτy' : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = χ g • y' := by
      calc stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = mulB (L := L) P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hone']
        _ = mulB (L := L) P (Fin 1 → ↥L.1) (mulB (L := L) P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hinv]
        _ = mulB (L := L) P (Fin 1 → ↥L.1) y' (mulB (L := L) P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
          rw [← mulB_assoc, mulB_comm (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)]
        _ = χ g • y' := by rw [hprod, mulB_smul, hcomm1]
    have hsz : stRep P ρs g (z : V ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (z : V ⊗[ℚ_[l]] Bst P) := by
      rw [stRep_twist ρs ρt χ ht] at hz
      conv_rhs => rw [← hz]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hsmul, hτy', hsz, mulB_smul, mulB_smul_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
  rw [coe_dmul, mulB_assoc, mulB_comm, hinv, hone]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodProduct_eq_of_invertible_character : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  first | exact @GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | exact GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv | (intros; apply GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.SphSupport

open ValuativeRel Cardinal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_one_comm (x y : GL (Fin 1) k) : x * y = y * x := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem levi_comm {m : ℕ} (g h : Levi k (fun _ : Fin m => Fin 1)) : g * h = h * g :=
  funext fun a => gl_one_comm (g a) (h a)

theorem scalar_det_fin_one (g : GL (Fin 1) k) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g) = g := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_one]

theorem det_scalar_fin_one (z : kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem mk_ne_zero (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hχ : IsSmoothChar χ) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y)
    {s : ℕ} (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin m) :
    (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) ≠ 0 := by
  intro h0
  let σ' : Representation ℂ (GL (Fin m) k) V := GlobalTheory.SmGL.twist σ (detChar (Fin m) χ⁻¹)
  let π : Irr k m := ⟨V, σ', isSmooth_twist hs hχ.inv.detChar, GlobalTheory.LocGL.isIrreducible_twist hi _⟩
  have hker : twKer σ' (unipRad k e) 1 = twKer σ (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor <;> rintro ⟨u, v, rfl⟩ <;> refine ⟨u, v, ?_⟩ <;>
      simp [σ', det_eq_one_of_mem_unipRad k u.2]
  have hle : KOne k (Fin m) ⊔ (unipRad k e ⊓ KO k (Fin m)) ≤ KO k (Fin m) :=
    sup_le (Subgroup.map_le_range _ _) inf_le_right
  refine hy (hD k m s d e π y ?_ ?_)
  · intro h
    have hKO := hle h.2
    show σ' h y = _
    simp only [σ', twist_apply, detChar_apply, hK _ hKO, smul_smul, MonoidHom.inv_apply]
    simp
  · show (Submodule.Quotient.mk y : V ⧸ twKer σ' (unipRad k e) 1) = 0
    rw [Submodule.Quotient.mk_eq_zero, hker]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0

theorem inSupport_of_KO_eigen (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ)
    (hi : σ.IsIrreducible) (hχ : IsSmoothChar χ) (hm : 0 < m) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) :
    ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  let e : (Σ _ : Fin m, Fin 1) ≃ Fin m := Equiv.sigmaUnique (Fin m) fun _ => Fin 1
  have hy' := mk_ne_zero hD σ χ y hs hi hχ hy hK (fun _ : Fin m => 1) e
  let a0 : Fin m := ⟨0, hm⟩
  let S : Set (Levi k (fun _ : Fin m => Fin 1)) :=
    {g | ∀ a, valuation k ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) = 1}
  let θ : Levi k (fun _ : Fin m => Fin 1) → ℂ := fun g =>
    (((deltaHalf k (fun _ : Fin m => Fin 1) g)⁻¹ : ℂˣ) : ℂ) *
      (χ (Matrix.GeneralLinearGroup.det (leviEmb k e g)) : ℂ)
  have hKOlevi : ∀ g ∈ S, leviEmb k e g ∈ KO k (Fin m) := by
    intro g hg
    have h1 : leviEmb k e g = diagT k (Fin m) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
      conv_lhs => rw [GlobalTheory.EigenSupport.eq_torusToLevi m g]
      exact GlobalTheory.SmGL.EmptyBlocks.leviEmb_torusToLevi k e _
    rw [h1]
    exact iwahori_le_KO k (Fin m) (diagT_mem_iwahori (t := fun j => Matrix.GeneralLinearGroup.det (g j)) hg)
  have hδ : ∀ g ∈ S, deltaHalf k (fun _ : Fin m => Fin 1) g = 1 := by
    intro g hg
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ (hg a)
  have hθ : ∀ g ∈ S, GlobalTheory.SmGL.jac e σ g (Submodule.Quotient.mk y) = θ g • (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) := by
    intro g hg
    rw [jac_mk, hK _ (hKOlevi g hg), Submodule.Quotient.mk_smul, smul_smul]
  obtain ⟨Y, _, _, τ, hτi, hτs, y₀, hy₀, hy₀θ⟩ :=
    GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen _ _ (GlobalTheory.SmGL.jac e σ) S θ _ hy' hθ
  have hrank : Module.rank ℂ Y ≤ ℵ₀ := by
    obtain ⟨S', f, hf⟩ := hτs
    haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin m)
    exact (LinearMap.rank_le_of_surjective f.toLinearMap hf).trans ((Submodule.rank_le _).trans
      ((LinearMap.rank_le_of_surjective _ (Submodule.mkQ_surjective _)).trans (GlobalTheory.LocGL.rank_le_aleph0_of_isIrreducible hs hi)))
  have hc : ∀ g : GL (Fin 1) k, ∃ c : ℂ, ∀ w, τ (Pi.mulSingle a0 g) w = c • w := fun g =>
    GlobalTheory.LocGL.exists_eq_smul_of_rank_le hτi hrank ⟨τ (Pi.mulSingle a0 g), fun h => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, levi_comm]⟩
  choose c hc using hc
  have hc1 : c 1 = 1 := smul_left_injective ℂ hy₀ (by
    show c 1 • y₀ = (1 : ℂ) • y₀
    rw [← hc, Pi.mulSingle_one, map_one, one_smul]; rfl)
  have hcmul : ∀ g h, c (g * h) = c g * c h := fun g h => smul_left_injective ℂ hy₀ (by
    show c (g * h) • y₀ = (c g * c h) • y₀
    rw [← hc, Pi.mulSingle_mul, map_mul, Module.End.mul_apply, hc h, hc g, smul_smul])
  let ω' : GL (Fin 1) k →* ℂˣ := MonoidHom.toHomUnits ⟨⟨c, hc1⟩, hcmul⟩
  let ω : kˣ →* ℂˣ := ω'.comp (Matrix.GeneralLinearGroup.scalar (Fin 1))
  have hω : ∀ u : kˣ, valuation k (u : k) = 1 → ω u = χ u := by
    intro u hu
    let g : Levi k (fun _ : Fin m => Fin 1) := Pi.mulSingle a0 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)
    have hg : g ∈ S := by
      intro a
      by_cases ha : a = a0
      · subst ha; simp [g, det_scalar_fin_one, hu]
      · simp [g, Pi.mulSingle_eq_of_ne ha]
    have hdet : Matrix.GeneralLinearGroup.det (leviEmb k e g) = u := by
      rw [det_leviEmb, Finset.prod_eq_single a0]
      · simp [g, det_scalar_fin_one]
      · intro b _ hb; simp [g, Pi.mulSingle_eq_of_ne hb]
      · simp
    have h1 := (hc _ y₀).symm.trans (hy₀θ g hg)
    simp only [θ, hδ g hg, hdet, inv_one, Units.val_one, one_mul] at h1
    exact Units.ext (smul_left_injective ℂ hy₀ h1)
  obtain ⟨α, hα⟩ := GlobalTheory.JacSuppCount.eq_mul_unrChar_of_eq_on_units k χ ω hω
  refine ⟨α, m, fun _ => 1, e, a0, rfl, Y, inferInstance, inferInstance, τ, hτi, hτs, fun g w => ?_⟩
  rw [← hα]
  show τ (Pi.mulSingle a0 g) w = c (Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g)) • w
  rw [scalar_det_fin_one, hc]

end GlobalTheory.SphSupport

theorem GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  intro _ _ hD k _ _ _ _ m V _ _ σ χ y hs hi hχ hm hy hK
  exact GlobalTheory.SphSupport.inSupport_of_KO_eigen hD σ χ y hs hi hχ hm hy hK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  first | exact @GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen | exact GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen | (intros; apply GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen <;> assumption)
end
end

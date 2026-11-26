module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficients

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
noncomputable section

open Matrix

namespace GlobalTheory.PMon

variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def vecM {S : Type*} (X : Matrix a b S) : a × b → S := fun p => X p.1 p.2

def homUnit (A : GL a R) (B : GL b R) : GL (a × b) R where
  val := Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ
  inv := Matrix.kroneckerMap (· * ·) ((A⁻¹ : GL a R) : Matrix a a R) (B : Matrix b b R)ᵀ
  val_inv := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]
  inv_val := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]

theorem homUnit_val (A : GL a R) (B : GL b R) :
    ((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R) =
      Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ := rfl

theorem kronecker_transpose_mulVec {S : Type*} [CommRing S] (A : Matrix a a S) (C : Matrix b b S) (X : Matrix a b S) :
    (Matrix.kroneckerMap (· * ·) A Cᵀ).mulVec (vecM X) = vecM (A * X * C) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem homUnit_mulVec {S : Type*} [CommRing S] (f : R →+* S) (A : GL a R) (B : GL b R) (X : Matrix a b S) :
    (((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R).map f).mulVec (vecM X) =
      vecM ((A : Matrix a a R).map f * X * ((B⁻¹ : GL b R) : Matrix b b R).map f) := by
  rw [homUnit_val, ← kronecker_transpose_mulVec]
  congr 1
  ext p q
  simp [Matrix.kroneckerMap_apply]

def homRep {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) : G →* GL (a × b) R where
  toFun g := homUnit (ρ₁ g) (ρ₂ g)
  map_one' := by
    ext1
    simp [homUnit_val, Matrix.one_kronecker_one]
  map_mul' g h := by
    ext1
    show ((homUnit (ρ₁ (g * h)) (ρ₂ (g * h)) : GL (a × b) R) : Matrix _ _ R) = ((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) R) : Matrix (a × b) (a × b) R) * ((homUnit (ρ₁ h) (ρ₂ h) : GL (a × b) R) : Matrix (a × b) (a × b) R)
    rw [homUnit_val, homUnit_val, homUnit_val, map_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul]

theorem homRep_apply {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (g : G) :
    homRep ρ₁ ρ₂ g = homUnit (ρ₁ g) (ρ₂ g) := rfl

def extCoc {G : Type*} [Group G] (ρ₂ : G →* GL b R) (c : G → Matrix a b R) (g : G) : a × b → R :=
  vecM (c g * (((ρ₂ g)⁻¹ : GL b R) : Matrix b b R))

theorem vecM_injective {S : Type*} : Function.Injective (vecM : Matrix a b S → a × b → S) := by
  intro X Y h
  ext i j
  exact congrFun h (i, j)

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantRightInverseField
namespace GlobalTheory.InvariantRightInverse

theorem exists_rightInverse_subfield {L : Type} [Field L] (K : Subfield L) {N b : Type}
    [Fintype N] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L)
    (h : κ * Y = 1) (hκ : ∀ i k, κ i k ∈ K) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ k j, Λ k j ∈ K := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (fun x y hxy => Subtype.ext hxy))
  have hπ' : ∀ x : K, π (x : L) = x := fun x => LinearMap.congr_fun hπ x
  refine ⟨Matrix.of fun k j => (π (Y k j) : L), ?_, fun k j => (π (Y k j)).2⟩
  ext i j
  have h1 : ∑ k, κ i k * Y k j = (1 : Matrix b b L) i j := by
    rw [← h, Matrix.mul_apply]
  have h2 : ∀ k, κ i k * (π (Y k j) : L) = (π (κ i k * Y k j) : L) := by
    intro k
    have := π.map_smul (⟨κ i k, hκ i k⟩ : K) (Y k j)
    have e : (⟨κ i k, hκ i k⟩ : K) • Y k j = κ i k * Y k j := rfl
    rw [e] at this
    rw [this]
    rfl
  have h3 : (1 : Matrix b b L) i j ∈ K := by
    rw [Matrix.one_apply]
    split_ifs
    · exact K.one_mem
    · exact K.zero_mem
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  calc ∑ k, κ i k * (π (Y k j) : L) = ∑ k, (π (κ i k * Y k j) : L) :=
        Finset.sum_congr rfl (fun k _ => h2 k)
    _ = ((∑ k, π (κ i k * Y k j) : K) : L) := by push_cast; rfl
    _ = (π (∑ k, κ i k * Y k j) : L) := by rw [map_sum]
    _ = (1 : Matrix b b L) i j := by
        rw [h1]
        exact congrArg Subtype.val (hπ' ⟨_, h3⟩)

theorem exists_invariant_rightInverse_field {L : Type} [Field L] (G : Type)
    (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq b]
    (κ : Matrix b N L) (Y : Matrix N b L) (h : κ * Y = 1)
    (hκ : ∀ g : G, Matrix.map κ (⇑(act g) : L → L) = κ) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g : G, Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  have hK : ∀ x : L, x ∈ (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) ↔
      ∀ g, act g x = x := by
    intro x
    rw [Subfield.mem_iInf]
    exact Iff.rfl
  obtain ⟨Λ, h1, h2⟩ := exists_rightInverse_subfield
    (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) κ Y h
    (fun i k => (hK _).2 (fun g => congrFun (congrFun (hκ g) i) k))
  refine ⟨Λ, h1, fun g => ?_⟩
  ext k j
  exact (hK _).1 (h2 k j) g

theorem exists_invariant_rightInverse :
    ∀ (L : Type) [inst : CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [inst_1 : Fintype N] [DecidableEq N] [Fintype b] [inst_4 : DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = (1 : Matrix b b L) → (∀ (g : G), Matrix.map κ (⇑(act g) : L → L) = κ) → ∃ (Λ : Matrix N b L), κ * Λ = (1 : Matrix b b L) ∧ ∀ (g : G), Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  intro L _ hL G act N b _ _ _ _ κ Y h hκ
  letI : Field L := hL.toField
  exact exists_invariant_rightInverse_field G act N b κ Y h hκ

end GlobalTheory.InvariantRightInverse
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverse
open Matrix

namespace GlobalTheory

theorem invariant_right_inverse_of_right_inverse :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first
  | exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | (apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverseStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_right_inverse : ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) → ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first | exact @GlobalTheory.invariant_right_inverse_of_right_inverse | exact GlobalTheory.invariant_right_inverse_of_right_inverse | (intros; apply GlobalTheory.invariant_right_inverse_of_right_inverse <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRham
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PMon.extCoc_dies_in_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  intro l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m
  obtain ⟨Q, hQm⟩ := hQ m
  obtain ⟨R, hRm⟩ := hR m
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l m)
  let σ : ↥(GK K) → P.R.BdR →+* P.R.BdR := fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)

  let A : ↥(GK K) → Matrix a a P.R.BdR := fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f
  let C : ↥(GK K) → Matrix a b P.R.BdR := fun g => (c g).map f
  let D : ↥(GK K) → Matrix b b P.R.BdR := fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  let Di : ↥(GK K) → Matrix b b P.R.BdR := fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  have hDDi : ∀ g, D g * Di g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hDiD : ∀ g, Di g * D g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g) := fun g => by
    show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _
    rw [hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  let Qa : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
  let Qb : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
  have hb : ∀ g, D g * Qb.map (σ g) = Qb := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inr i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ] using h
  have ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inl i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ] using h
  have hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R := fun g => hRm g
  let S : Matrix b b P.R.BdR := ((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)
  have hSR : S * R = 1 := by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRS : (R : Matrix b b P.R.BdR) * S = 1 := by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgS : ∀ g, S.map (σ g) = S * D g := fun g => by
    calc S.map (σ g) = (S * (D g * (R : Matrix b b P.R.BdR).map (σ g))) * S.map (σ g) := by
          rw [hRg g, hSR, Matrix.one_mul]
      _ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by
          simp only [Matrix.mul_assoc]
      _ = S * D g := by rw [hgRS g, Matrix.mul_one]
  have hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R := fun g => by
    symm
    conv_lhs => rw [← hRg g]
    rw [← Matrix.mul_assoc, hDiD g, Matrix.one_mul]
  obtain ⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb := ⟨_, rfl⟩
  have hκ : ∀ g, κ.map (σ g) = κ := fun g => by
    rw [hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]
  let Y : Matrix (a ⊕ b) b P.R.BdR :=
    (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)
  have hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Qb] using h
  have hY : κ * Y = 1 := by
    simp only [Y]
    rw [hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]
  obtain ⟨Λ, hκΛ, hΛ⟩ := GlobalTheory.T.exists_invariant_right_inverse P.R.BdR (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ
  have hQbR : Qb = (R : Matrix b b P.R.BdR) * κ := by
    rw [hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ := fun g => by
    conv_lhs => rw [hQbR]
    rw [Matrix.map_mul, hκ g]
  let Z : Matrix a b P.R.BdR := Qa * Λ
  have hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g) := fun g => by
    have e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ) := by
      rw [← hgQb g]
      exact eq_sub_of_add_eq (ha g)
    simp only [Z]
    rw [Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g),
      Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]
  refine ⟨vecM (-(Z * S)), fun g => ?_⟩
  have hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g) := by
    show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _
    rw [Matrix.map_mul]
  have hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) =
      vecM (A g * (-(Z * S)).map (σ g) * Di g) := by
    show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec
      (vecM ((-(Z * S)).map (σ g))) = _
    rw [homUnit_mulVec]
  rw [hL, hR']
  have hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y) := fun _ _ => rfl
  rw [hsub]
  congr 1
  have hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g)) := by
    rw [Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]
  rw [hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]
  abel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRhamStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockTriangular_extensionCocycle_trivial_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  first | exact @GlobalTheory.PMon.extCoc_dies_in_BdR | exact GlobalTheory.PMon.extCoc_dies_in_BdR | (intros; apply GlobalTheory.PMon.extCoc_dies_in_BdR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistable
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem extPeriodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ Q₁ Q₂ h₁ h₂ v hv
  let β : Matrix a b (Bst P) := Matrix.of fun i j => v (i, j)
  have hvβ : v = vecM β := rfl
  let Qm : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks (Q₁ : Matrix a a (Bst P)) (-(β * (Q₂ : Matrix b b (Bst P)))) 0 (Q₂ : Matrix b b (Bst P))
  let Qi : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks ((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) (((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) * β) 0
      ((Q₂⁻¹ : GL b (Bst P)) : Matrix b b (Bst P))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.mul_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc β, Units.mul_inv, Matrix.mul_one,
      add_neg_cancel, Matrix.fromBlocks_one]
  have hQ' : Qi * Qm = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_neg, ← Matrix.mul_assoc, neg_add_cancel, neg_zero, Matrix.fromBlocks_one]
  refine ⟨⟨Qm, Qi, hQ, hQ'⟩, fun g => ?_⟩
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have hσc : ⇑(actSt P (g : GQ l)) = ⇑σ := rfl
  have hc : ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map (ks P)) =
      (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β := by
    apply vecM_injective
    have h := hv g
    rw [homRep_apply, hvβ] at h
    have e1 : (fun i => actSt P (g : GQ l) (vecM β i)) = vecM (β.map σ) := rfl
    rw [e1, homUnit_mulVec] at h
    exact h
  have hR : (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ2 : (Q₂ : Matrix b b (Bst P)).map σ =
      (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)) := by
    calc (Q₂ : Matrix b b (Bst P)).map σ
        = ((((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P)) *
            (Q₂ : Matrix b b (Bst P)).map σ := by rw [hR, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc]; exact congrArg _ (h₂ g)
  have hC : (c g).map (ks P) * (Q₂ : Matrix b b (Bst P)).map σ =
      ((ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β) *
        (Q₂ : Matrix b b (Bst P)) := by
    rw [hQ2, ← hc, Matrix.map_mul, Matrix.mul_assoc]
  show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * Qm.map σ = Qm
  rw [hρ g]
  simp only [Qm, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  have e1 := h₁ g
  have e2 := h₂ g
  rw [hσc] at e1 e2
  rw [e1, e2]
  congr 1
  rw [Matrix.map_neg _ (map_neg σ), Matrix.map_mul, hC, hQ2]
  simp only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistableStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_block_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  first | exact @GlobalTheory.PMon.extPeriodMatrix | exact GlobalTheory.PMon.extPeriodMatrix | (intros; apply GlobalTheory.PMon.extPeriodMatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuou
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuou
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem isRat_homRep_restrict : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hρ hb
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have e1 : ∀ g i j, (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inl j) := by
    intro g i j; rw [hb]; rfl
  have e2 : ∀ g i j, (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inr j) := by
    intro g i j; rw [hb]; rfl
  have key : ∀ g' p q, ((homRep (ρ₁.comp ι) (ρ₂.comp ι) g' : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)) p q =
      (ρ (ι g') : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl p.1) (Sum.inl q.1) *
        (ρ (ι g')⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr q.2) (Sum.inr p.2) := by
    intro g' p q
    rw [homRep_apply, homUnit_val, Matrix.kroneckerMap_apply, Matrix.transpose_apply, ← map_inv, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e1, e2, map_inv ι]
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  refine ⟨hρ.pos, fun x hx => hK (hρ.le x hx), ?_, ?_⟩
  · intro g p q
    rw [key, map_mul, hρ.rat, hρ.rat]
  · intro p q
    simp only [key, IntermediateField.coe_mul]
    exact ((hρ.cont _ _).comp hιc).mul ((hρ.cont _ _).comp (hιc.inv))

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuouStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixHomRepresentation_restrict_rational_continuous : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  first | exact @GlobalTheory.PMon.isRat_homRep_restrict | exact GlobalTheory.PMon.isRat_homRep_restrict | (intros; apply GlobalTheory.PMon.isRat_homRep_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuous
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
open Matrix

namespace GlobalTheory.PMon

theorem matrixHomRepresentationCocycleCoords_cocycle {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {G : Type*} [Group G] (ρ : G →* GL (a ⊕ b) R) (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (c : G → Matrix a b R)
    (hρ : ∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (ρ₁ g : Matrix a a R) (c g) 0 (ρ₂ g : Matrix b b R))
    (g h : G) :
    extCoc ρ₂ c (g * h) = extCoc ρ₂ c g + ((homRep ρ₁ ρ₂ g : GL (a × b) R) : Matrix (a × b) (a × b) R).mulVec (extCoc ρ₂ c h) := by
  have hc : c (g * h) = (ρ₁ g : Matrix a a R) * c h + c g * (ρ₂ h : Matrix b b R) := by
    have := congrArg (fun M : GL (a ⊕ b) R => Matrix.toBlocks₁₂ (M : Matrix (a ⊕ b) (a ⊕ b) R)) (map_mul ρ g h)
    simp only [Units.val_mul, hρ, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at this
    simpa using this
  unfold extCoc
  rw [homRep_apply, homUnit_val, kronecker_transpose_mulVec]
  rw [hc, map_mul, _root_.mul_inv_rev, Units.val_mul]
  have h2 : (ρ₂ h : Matrix b b R) * (((ρ₂ h)⁻¹ : GL b R) : Matrix b b R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.add_mul, Matrix.mul_assoc (c g), ← Matrix.mul_assoc (ρ₂ h : Matrix b b R), h2, Matrix.one_mul]
  funext p
  simp only [vecM, Pi.add_apply, Matrix.add_apply, Matrix.mul_assoc]
  ring

theorem extCoc_rat_cont_cocycle : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hrat hρ
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have hent : ∀ g (i : a) (k : b), c g i k = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inr k) := by
    intro g i k; rw [hρ]; rfl
  have hinv : ∀ g (k j : b), (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)) k j =
      (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr j) := by
    intro g k j; rw [← map_inv, hρ]; rfl
  have hform : ∀ g (i : a × b), extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i =
      ∑ k, (ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) *
        (ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) := by
    intro g i
    simp only [extCoc, vecM, MonoidHom.comp_apply, Matrix.mul_apply, hent, hinv]
  have hcι : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  refine ⟨?_, ?_, ?_⟩
  · intro g i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hform, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hrat.rat, hrat.rat]
  · intro i
    have : (fun g => ((extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, (((ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) : ↥(MaximalUnramifiedExtension l)) : Om l) *
          (((ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [hform]
      push_cast
      rfl
    rw [this]
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((hrat.cont _ _).comp hcι).mul ((hrat.cont _ _).comp (continuous_inv.comp hcι))
  · intro g h
    exact matrixHomRepresentationCocycleCoords_cocycle (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hρ (ι g)) g h

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixHomRepresentationCocycle_rational_continuous : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  first | exact @GlobalTheory.PMon.extCoc_rat_cont_cocycle | exact GlobalTheory.PMon.extCoc_rat_cont_cocycle | (intros; apply GlobalTheory.PMon.extCoc_rat_cont_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistable
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem kroneckerMap_mul_map_ringHom {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (f : R →+* S)
    (A : Matrix a a R) (B : Matrix b b R) :
    (Matrix.kroneckerMap (· * ·) A B).map f = Matrix.kroneckerMap (· * ·) (A.map f) (B.map f) := by
  ext p q
  simp [Matrix.kroneckerMap_apply]

theorem inv_periodMatrix_map_mul_eq_inv {S T : Type*} [CommRing S] [CommRing T] {b : Type*} [Fintype b] [DecidableEq b]
    (k : S →+* T) (σ : T →+* T) (r : GL b S) (Q : GL b T)
    (h : (r : Matrix b b S).map k * (Q : Matrix b b T).map σ = Q) :
    ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k = ((Q⁻¹ : GL b T) : Matrix b b T) := by
  have hQ : (Q : Matrix b b T) * (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) = 1 := by
    rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc ((Q : Matrix b b T).map σ), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero k) (map_one k)]
  calc ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k
      = ((Q⁻¹ : GL b T) : Matrix b b T) * (Q : Matrix b b T) *
          (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) := by
        rw [Units.inv_mul, Matrix.one_mul]
    _ = ((Q⁻¹ : GL b T) : Matrix b b T) := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem homUnit_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  intro l _ P a b _ _ _ _ K ρ₁ ρ₂ Q₁ Q₂ h₁ h₂ g
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have e : ∀ {n : Type} (M : Matrix n n (Bst P)), M.map (actSt P (g : GQ l)) = M.map σ := fun M => rfl
  have h1 := h₁ g
  have h2 := h₂ g
  rw [e] at h1 h2
  rw [e, homRep_apply, homUnit_val, homUnit_val, kroneckerMap_mul_map_ringHom, kroneckerMap_mul_map_ringHom, ← Matrix.mul_kronecker_mul, h1,
    Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul, inv_periodMatrix_map_mul_eq_inv (ks P) σ (ρ₂ g) Q₂ h2]

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistableStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixHom_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  first | exact @GlobalTheory.PMon.homUnit_period | exact GlobalTheory.PMon.homUnit_period | (intros; apply GlobalTheory.PMon.homUnit_period <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem extStep_holds : ExtStep := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c hρ hblk hdR h₁ h₂
  obtain ⟨K₁, hK₁, Q₁, hQ₁⟩ := h₁
  obtain ⟨K₂, hK₂, Q₂, hQ₂⟩ := h₂
  haveI := K₁.2
  haveI := K₂.2
  let K' : FinExt l := ⟨K₁.1 ⊔ K₂.1, inferInstance⟩
  have h1' : K₁.1 ≤ K'.1 := le_sup_left
  have h2' : K₂.1 ≤ K'.1 := le_sup_right
  have hK : K.1 ≤ K'.1 := hK₁.trans h1'
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  have hQ₁' : ∀ g : ↥(GK K'), ((ρ₁.comp ι) g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁ := fun g => hQ₁ ⟨g, GK_le h1' g.2⟩
  have hQ₂' : ∀ g : ↥(GK K'), ((ρ₂.comp ι) g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂ := fun g => hQ₂ ⟨g, GK_le h2' g.2⟩
  have hdR₂ : AdmDR P ρ₂ := (GlobalTheory.T.deRham_blockTriangular_diagonal_blocks l P AI T a b K r ρ ρ₁ ρ₂ c hρ hblk hdR).2
  obtain ⟨hcr, hcc, hcoc⟩ := GlobalTheory.T.matrixHomRepresentationCocycle_rational_continuous l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk
  obtain ⟨v, hv⟩ := GlobalTheory.T.hyodo_theorem_matrix_unramifiedCoefficients l P AI T (a × b) K' r (homRep (ρ₁.comp ι) (ρ₂.comp ι)) (homUnit Q₁ Q₂)
    (GlobalTheory.T.matrixHomRepresentation_restrict_rational_continuous l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk) (GlobalTheory.T.matrixHom_periodMatrix_semistable l P a b K' (ρ₁.comp ι) (ρ₂.comp ι) Q₁ Q₂ hQ₁' hQ₂')
    (extCoc (ρ₂.comp ι) (fun g => c (ι g))) hcr hcc hcoc
    (fun m => by
      obtain ⟨w, hw⟩ := GlobalTheory.T.blockTriangular_extensionCocycle_trivial_deRham l P AI T a b K ρ ρ₁ ρ₂ c hblk hdR hdR₂ m
      exact ⟨w, fun g => hw (ι g)⟩)
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.extension_block_periodMatrix_semistable l P a b K' (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hblk (ι g))
    Q₁ Q₂ hQ₁' hQ₂' v hv
  exact ⟨K', hK, Q, fun g => hQ g⟩

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistableStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamExtension_potentiallySemistable : ExtStep := by
  first | exact @GlobalTheory.PMon.extStep_holds | exact GlobalTheory.PMon.extStep_holds | (intros; apply GlobalTheory.PMon.extStep_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplit
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Red

section Conj

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def conjHom (X : Matrix m n R) (Y : Matrix n m R) (hXY : X * Y = 1) (hYX : Y * X = 1) : GL n R →* GL m R where
  toFun A := ⟨X * (A : Matrix n n R) * Y, X * ((A⁻¹ : GL n R) : Matrix n n R) * Y, by
      have hA : (A : Matrix n n R) * ((A⁻¹ : GL n R) : Matrix n n R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul, ← Matrix.mul_assoc (A : Matrix n n R), hA, Matrix.one_mul, hXY], by
      have hA : ((A⁻¹ : GL n R) : Matrix n n R) * (A : Matrix n n R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul, ← Matrix.mul_assoc ((A⁻¹ : GL n R) : Matrix n n R), hA,
        Matrix.one_mul, hXY]⟩
  map_one' := by
    ext1
    simp only [Units.val_one, Matrix.mul_one, hXY]
  map_mul' A B := by
    ext1
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y X, hYX, Matrix.one_mul]

theorem conjHom_val (X : Matrix m n R) (Y : Matrix n m R) (hXY : X * Y = 1) (hYX : Y * X = 1) (A : GL n R) :
    ((conjHom X Y hXY hYX A : GL m R) : Matrix m m R) = X * (A : Matrix n n R) * Y := rfl

end Conj

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section Transport

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {K : FinExt l} {r : ℕ}

def RatM (r : ℕ) {a b : Type} (X : Matrix a b ↥(MaximalUnramifiedExtension l)) : Prop := ∀ i j, fr l r (X i j) = X i j

theorem map_fr {a b : Type} {X : Matrix a b ↥(MaximalUnramifiedExtension l)} (h : RatM r X) : X.map (fr l r) = X := by
  exact Matrix.ext fun i j => h i j

variable (X : Matrix m n ↥(MaximalUnramifiedExtension l)) (Y : Matrix n m ↥(MaximalUnramifiedExtension l)) (hXY : X * Y = 1) (hYX : Y * X = 1)
  (hX : RatM r X) (hY : RatM r Y) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ' : ↥(GK K) →* GL m ↥(MaximalUnramifiedExtension l))
  (h : ∀ g, (ρ' g : Matrix m m ↥(MaximalUnramifiedExtension l)) = X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y)

include hX hY h in
theorem isRat_of (hρ : IsRat r ρ) : IsRat r ρ' := by
  refine ⟨hρ.pos, hρ.le, ?_, ?_⟩
  · intro g i j
    have hρg : (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l r) = ρ g := Matrix.ext fun a b => hρ.rat g a b
    have e : (X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y).map (fr l r) = X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y := by
      rw [Matrix.map_mul, Matrix.map_mul, map_fr hX, map_fr hY, hρg]
    rw [h g]
    exact congrFun (congrFun e i) j
  · intro i j
    have e : (fun g => (((ρ' g : Matrix m m ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, ∑ k', ((X i k' : ↥(MaximalUnramifiedExtension l)) : Om l) * (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) k' k : ↥(MaximalUnramifiedExtension l)) : Om l) *
          ((Y k j : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [h g]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      change algebraMap ↥(MaximalUnramifiedExtension l) (Om l) _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul]
      rfl
    rw [e]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun k' _ => ?_
    exact (continuous_const.mul (hρ.cont k' k)).mul continuous_const

include hXY hYX hX hY h in
theorem deRham_of_conjugate_unramified_rational (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1) (hρ : AdmDR P ρ) : AdmDR P ρ' := by
  intro k
  obtain ⟨Q, hQ⟩ := hρ k
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l k)
  have hf : ∀ {a b : Type} (M : Matrix a b ↥(MaximalUnramifiedExtension l)), M.map (fun c => kd P (fr l k c)) = M.map f := fun _ => rfl
  have h1 : X.map f * Y.map f = 1 := by
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero f) (map_one f)]
  have h2 : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero f) (map_one f)]
  have hfix : ∀ g : ↥(GK K), (X.map f).map (P.actQdR (g : GQ l)) = X.map f := fun g =>
    Matrix.ext fun i j => act_kd P g (hle _ (fr_comm (hX i j) k))
  have hfixY : ∀ g : ↥(GK K), (Y.map f).map (P.actQdR (g : GQ l)) = Y.map f := fun g =>
    Matrix.ext fun i j => act_kd P g (hle _ (fr_comm (hY i j) k))
  refine ⟨conjHom (X.map f) (Y.map f) h1 h2 Q, fun g => ?_⟩
  have hm : matD P ρ' k g = X.map f * matD P ρ k g * Y.map f := by
    rw [matD, hf, h g, Matrix.map_mul, Matrix.map_mul, matD, hf]
  rw [conjHom_val, hm, Matrix.map_mul, Matrix.map_mul, hfix, hfixY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Y.map f) (X.map f), h2, Matrix.one_mul, ← Matrix.mul_assoc (matD P ρ k g), hQ]

include hXY hYX hX hY h in
theorem semistable_of_conjugate_unramified_rational (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1) (hρ : AdmSt P ρ) : AdmSt P ρ' := by
  obtain ⟨K', hK, Q, hQ⟩ := hρ
  let f : ↥(MaximalUnramifiedExtension l) →+* Bst P := ks P
  have h1 : X.map f * Y.map f = 1 := by
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero f) (map_one f)]
  have h2 : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero f) (map_one f)]
  have hfix : ∀ g : ↥(GK K'), (X.map f).map (actSt P (g : GQ l)) = X.map f := fun g =>
    Matrix.ext fun i j => act_ks P g (hK (hle _ (hX i j)))
  have hfixY : ∀ g : ↥(GK K'), (Y.map f).map (actSt P (g : GQ l)) = Y.map f := fun g =>
    Matrix.ext fun i j => act_ks P g (hK (hle _ (hY i j)))
  refine ⟨K', hK, conjHom (X.map f) (Y.map f) h1 h2 Q, fun g => ?_⟩
  rw [conjHom_val, h, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hfix, hfixY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Y.map f) (X.map f), h2, Matrix.one_mul, ← Matrix.mul_assoc (((ρ ⟨g, GK_le hK g.2⟩ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)), hQ g]

end Transport

section Blocks

variable {G : Type} [Group G] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {R : Type} [CommRing R]

theorem toBlocks₁₁_mul (A B : Matrix (a ⊕ b) (a ⊕ b) R) (hB : ∀ i j, B (Sum.inr i) (Sum.inl j) = 0) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, hB]

theorem toBlocks₂₂_mul (A B : Matrix (a ⊕ b) (a ⊕ b) R) (hA : ∀ i j, A (Sum.inr i) (Sum.inl j) = 0) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, hA]

theorem toBlocks₁₁_one : (1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem toBlocks₂₂_one : (1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ = 1 := by
  ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]

variable (ρ : G →* GL (a ⊕ b) R) (hz : ∀ g i j, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) (Sum.inr i) (Sum.inl j) = 0)

include hz in
theorem blk_mul₁ (g h : G) : (ρ (g * h) : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ =
    (ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ * (ρ h : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ := by
  rw [map_mul, Units.val_mul, toBlocks₁₁_mul _ _ (hz h)]

include hz in
theorem blk_mul₂ (g h : G) : (ρ (g * h) : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ =
    (ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ * (ρ h : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ := by
  rw [map_mul, Units.val_mul, toBlocks₂₂_mul _ _ (hz g)]

def blk₁ : G →* GL a R where
  toFun g := ⟨(ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁, (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁,
    by rw [← blk_mul₁ ρ hz, mul_inv_cancel, map_one, Units.val_one, toBlocks₁₁_one],
    by rw [← blk_mul₁ ρ hz, inv_mul_cancel, map_one, Units.val_one, toBlocks₁₁_one]⟩
  map_one' := by
    ext1
    show (ρ 1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₁ = 1
    rw [map_one, Units.val_one, toBlocks₁₁_one]
  map_mul' g h := by
    ext1
    exact blk_mul₁ ρ hz g h

def blk₂ : G →* GL b R where
  toFun g := ⟨(ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂, (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂,
    by rw [← blk_mul₂ ρ hz, mul_inv_cancel, map_one, Units.val_one, toBlocks₂₂_one],
    by rw [← blk_mul₂ ρ hz, inv_mul_cancel, map_one, Units.val_one, toBlocks₂₂_one]⟩
  map_one' := by
    ext1
    show (ρ 1 : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₂ = 1
    rw [map_one, Units.val_one, toBlocks₂₂_one]
  map_mul' g h := by
    ext1
    exact blk_mul₂ ρ hz g h

theorem blk_form (g : G) : (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (blk₁ ρ hz g : Matrix a a R)
    ((ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₁₂) 0 (blk₂ ρ hz g : Matrix b b R) := by
  have h0 : (ρ g : Matrix (a ⊕ b) (a ⊕ b) R).toBlocks₂₁ = 0 := Matrix.ext fun i j => hz g i j
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (ρ g : Matrix (a ⊕ b) (a ⊕ b) R), h0]
  rfl

end Blocks

section BlocksRat

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {K : FinExt l} {r : ℕ}
  (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l))
  (hz : ∀ g i j, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inl j) = 0)

theorem isRat_blk₁ (hρ : IsRat r ρ) : IsRat r (blk₁ ρ hz) := by
  exact ⟨hρ.pos, hρ.le, fun g i j => hρ.rat g (Sum.inl i) (Sum.inl j),
    fun i j => hρ.cont (Sum.inl i) (Sum.inl j)⟩

theorem isRat_blk₂ (hρ : IsRat r ρ) : IsRat r (blk₂ ρ hz) := by
  exact ⟨hρ.pos, hρ.le, fun g i j => hρ.rat g (Sum.inr i) (Sum.inr j),
    fun i j => hρ.cont (Sum.inr i) (Sum.inr j)⟩

end BlocksRat

theorem rat_inv {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} (p : GL n ↥(MaximalUnramifiedExtension l))
    (hp : ∀ i j, fr l r ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) :
    RatM r ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
  have hp' : (p : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l r) = p := Matrix.ext hp
  set M := ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l r) with hM
  have h1 : M * (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← hp', hM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : M = ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
    calc M = M * ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) * ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l))) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = M * (p : Matrix n n ↥(MaximalUnramifiedExtension l)) * ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) := (mul_assoc _ _ _).symm
      _ = _ := by rw [h1, one_mul]
  intro i j
  exact congrFun (congrFun h2 i) j

theorem redStep : RedStep := by
  intro l _ P AI T n _ _ K r ρ hR hD hS IH
  obtain ⟨s, p, ⟨x, hx⟩, hs, hp, hz⟩ := hS
  obtain ⟨y, hy⟩ : ∃ y, y ∉ s := by
    by_contra hc
    exact hs (Finset.eq_univ_iff_forall.2 fun y => by_contra fun h => hc ⟨y, h⟩)
  let e : {i // i ∈ s} ⊕ {i // i ∉ s} ≃ n := Equiv.sumCompl (· ∈ s)
  let X : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) n ↥(MaximalUnramifiedExtension l) :=
    fun i j => ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) (e i) j
  let Y : Matrix n ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l) := fun i j => (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i (e j)
  have hXY : X * Y = 1 := by
    ext i j
    have h1 : ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) * (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrFun (congrFun h1 (e i)) (e j)
    rw [Matrix.mul_apply] at h2
    rw [Matrix.mul_apply]
    simp only [X, Y]
    rw [h2]
    simp only [Matrix.one_apply, e.injective.eq_iff]
  have hYX : Y * X = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [X, Y]
    rw [Equiv.sum_comp e (fun k => (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i k * ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) k j),
      ← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hX : RatM r X := fun i j => rat_inv p hp (e i) j
  have hY : RatM r Y := fun i j => hp i (e j)
  let ρ' := (conjHom X Y hXY hYX).comp ρ
  have h : ∀ g, (ρ' g : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l)) = X * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) * Y := fun g => rfl
  have h' : ∀ g, (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) = Y * (ρ' g : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l)) * X := fun g => by
    rw [h g]
    simp only [Matrix.mul_assoc]
    rw [hYX, Matrix.mul_one, ← Matrix.mul_assoc Y X, hYX, Matrix.one_mul]
  have hR' : IsRat r ρ' := isRat_of (X := X) (Y := Y) hX hY ρ ρ' h hR
  have hD' : AdmDR P ρ' := deRham_of_conjugate_unramified_rational P X Y hXY hYX hX hY ρ ρ' h hR.le hD
  have hz' : ∀ g i j, (ρ' g : Matrix ({i // i ∈ s} ⊕ {i // i ∉ s}) ({i // i ∈ s} ⊕ {i // i ∉ s}) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inl j) = 0 := fun g i j =>
    hz g i.1 j.1 i.2 j.2
  have hform := blk_form ρ' hz'
  have hsub := GlobalTheory.T.deRham_blockTriangular_diagonal_blocks l P AI T _ _ K r ρ' (blk₁ ρ' hz') (blk₂ ρ' hz') _ hR' hform hD'
  have hS1 : AdmSt P (blk₁ ρ' hz') :=
    IH _ (Fintype.card_subtype_lt (x := y) hy) _ (isRat_blk₁ ρ' hz' hR') hsub.1
  have hS2 : AdmSt P (blk₂ ρ' hz') :=
    IH _ (Fintype.card_subtype_lt (p := fun i => i ∉ s) (x := x) (not_not.2 hx)) _ (isRat_blk₂ ρ' hz' hR') hsub.2
  have hS' := GlobalTheory.T.deRhamExtension_potentiallySemistable l P AI T _ _ K r ρ' (blk₁ ρ' hz') (blk₂ ρ' hz') _ hR' hform hD' hS1 hS2
  exact semistable_of_conjugate_unramified_rational P Y X hYX hXY hY hX ρ' ρ h' hR.le hS'

end GlobalTheory.PMon.Red

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentially_semistable_reducible_unramified_split : RedStep := by
  first | exact @GlobalTheory.PMon.Red.redStep | exact GlobalTheory.PMon.Red.redStep | (intros; apply GlobalTheory.PMon.Red.redStep <;> assumption)
end

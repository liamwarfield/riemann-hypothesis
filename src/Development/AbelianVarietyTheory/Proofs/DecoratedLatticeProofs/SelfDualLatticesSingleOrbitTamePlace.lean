module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnimodularBasisSelfDualLatticeAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertibl
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertibl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaPlace.GramBasis

variable {D : D7} {S : HSp D}

def cv {n : ℕ} (y : Fin n → AE D) : Fin n → AE D := fun i => cA D (y i)

theorem hermAt_eq (x y : Fin S.rank → AE D) : hermAt S x y = cv y ⬝ᵥ (gA S *ᵥ x) := by
  unfold hermAt cv
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cv_mulVec {m : ℕ} (N : Matrix (Fin S.rank) (Fin m) (AE D)) (b : Fin m → AE D) :
    cv (N *ᵥ b) = vecMul (cv b) (adj N) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cv, mulVec, vecMul, dotProduct, map_sum, map_mul, adj, transpose_apply, map_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem hermAt_mulVec {m n : ℕ} (M : Matrix (Fin S.rank) (Fin m) (AE D)) (a : Fin m → AE D)
    (N : Matrix (Fin S.rank) (Fin n) (AE D)) (b : Fin n → AE D) :
    hermAt S (M *ᵥ a) (N *ᵥ b) = cv b ⬝ᵥ ((adj N * (gA S * M)) *ᵥ a) := by
  rw [hermAt_eq, cv_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem cv_single {n : ℕ} (i : Fin n) : cv (Pi.single i (1 : AE D)) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h; simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (i : Fin m) (j : Fin n) :
    (M *ᵥ Pi.single j (1 : AE D)) i = M i j := by
  rw [mulVec_single_one]; rfl

theorem gram_basis : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ β β' hεε hcε hε hact hΛ hβ hβ' h1 h2 hmem
  have h0 : (0 : AE D) ∈ intAt D (· = v) := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  have hcs : ∀ j k, (β *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun j k => by
    rw [mulVec_single_apply]; exact hβ k j
  have hcol : ∀ j, β *ᵥ Pi.single j (1 : AE D) ∈ Λ := fun j => (hmem _ (hcs j)).2 fun i => by
    rw [mulVec_mulVec, mulVec_single_apply, h2, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs
    · rw [mul_one]; exact hε
    · rw [mul_zero]; exact h0
  have hadj : adj β * adj β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [← adj_mul, h2, adj_smul, adj_one, hcε]
  have hz : adj β * (gA S * (giA S * adj β')) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [gA_giA_cancel, hadj]
  refine ⟨fun i j => ?_, fun i j => ?_, β' * (giA S * adj β'), fun i j => ?_, ?_⟩
  · have h := (hΛ.2.2 _ (hcs j)).1 (hcol j) _ (hcol i)
    rwa [hermAt_mulVec, cv_single, single_dotProduct, one_mul, mulVec_single_apply] at h
  · have h : adj (adj β * (gA S * β)) = adj β * (gA S * β) := by
      rw [adj_mul, adj_mul, adj_gA, adj_adj, Matrix.mul_assoc]
    exact congrFun (congrFun h j) i
  · have hs : ∀ k, ((giA S * adj β') *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun k => by
      rw [← mulVec_mulVec]
      refine mulVec_mem_idAt _ (fun l => ?_) k
      rw [mulVec_single_apply]
      change cA D (β' j l) ∈ _
      rw [← (hact _).1 (hβ' j l), RingHom.map_mul, hcε]
      exact Ideal.mul_mem_right _ _ hε.1
    have hin : (giA S * adj β') *ᵥ Pi.single j (1 : AE D) ∈ Λ := (hΛ.2.2 _ hs).2 fun x hx => by
      refine ⟨LocSD.hermAt_mem_idAt hs x, ?_⟩
      have hw := (hmem x (hΛ.1 x hx)).1 hx j
      have e : x = β *ᵥ (β' *ᵥ x) := by
        rw [mulVec_mulVec, h1, smul_mulVec, one_mulVec]
        funext k
        exact ((hact _).1 (hΛ.1 x hx k)).symm
      rw [e, hermAt_mulVec, hz, smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
        RingHom.map_mul]
      exact FrameLat.mul_mem_intAE hε.2 ((FrameLat.cA_int_iff _).2 hw.2)
    have h := (hmem _ hs).1 hin i
    rwa [mulVec_mulVec, mulVec_single_apply] at h
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc β, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_smul, hz, smul_smul, hεε]

end GlobalTheory.IwaPlace.GramBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertiblStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_basis_gram_integral_invertible : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.GramBasis.gram_basis | exact GlobalTheory.IwaPlace.GramBasis.gram_basis | (intros; apply GlobalTheory.IwaPlace.GramBasis.gram_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnimodularBasisSelfDualLatticeAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDBasis

theorem exists_basis_unimodular : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ hT hεε hcε hεO hε hΛ
  obtain ⟨β, β', hβ, hβ', h1, h2, h3⟩ :=
    GlobalTheory.T.exists_integralBasis_of_latticeAtPlace_stable D S.rank v ε Λ hT hεε hcε hεO hε hΛ.1 (GlobalTheory.T.selfDualLatticeAtPlace_smul_integral_mem D S v Λ hΛ) hΛ.2.1 (GlobalTheory.T.exists_nat_mul_selfDualLatticeAtPlace_integral D S v Λ hΛ)
  exact ⟨β, β', hβ, hβ', h1, h2, h3, GlobalTheory.T.selfDualLatticeAtPlace_basis_gram_integral_invertible D S v ε Λ β β' hεε hcε hεO hε hΛ hβ hβ' h1 h2 h3⟩

end GlobalTheory.IwaPlace.SDBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnimodularBasisSelfDualLatticeAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_basis_selfDual_lattice_at_place : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular | exact GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular | (intros; apply GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.IwaOrbit

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_zero {P : Pl D → Prop} : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact mul_mem_intAE ha.2 hb.2⟩

theorem mulVec_mem_intAt {P : Pl D → Prop} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {z : Fin n → AE D}
    (hM : ∀ i j, M i j ∈ intAt D P) (hz : ∀ j, z j ∈ intAt D P) (i : Fin m) : (M *ᵥ z) i ∈ intAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_induction _ (· ∈ intAt D P) (fun _ _ => intAt_add) intAt_zero
    fun j _ => intAt_mul (hM i j) (hz j)

theorem mul_mem_idAt_left {P : Pl D → Prop} {l m n : ℕ} {A : Matrix (Fin l) (Fin m) (AE D)}
    (B : Matrix (Fin m) (Fin n) (AE D)) (hA : ∀ i j, A i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hA i k)

theorem mul_mem_idAt_right {P : Pl D → Prop} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (AE D))
    {B : Matrix (Fin m) (Fin n) (AE D)} (hB : ∀ i j, B i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hB k j)

theorem smul_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) : ε • X = X := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hX i j)

theorem smul_vec_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {n : ℕ}
    {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) : ε • y = y := by
  funext i; rw [Pi.smul_apply, smul_eq_mul]; exact (hε _).1 (hy i)

theorem smul_mulVec' {m n : ℕ} (a : AE D) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D) :
    (a • A) *ᵥ y = a • (A *ᵥ y) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem adj_smul {m n : ℕ} (a : AE D) (X : Matrix (Fin m) (Fin n) (AE D)) : adj (a • X) = cA D a • adj X := by
  ext i j
  change cA D (a * X j i) = cA D a * cA D (X j i)
  exact (cA D).map_mul _ _

theorem adj_sub {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X - Y) = adj X - adj Y := by
  ext i j
  change cA D (X j i - Y j i) = cA D (X j i) - cA D (Y j i)
  exact (cA D).map_sub _ _

theorem adj_mem_idAt {P : Pl D → Prop} {ε : AE D} (hcε : cA D ε = ε) (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) (i : Fin n) (j : Fin m) :
    adj X i j ∈ idAt D P := by
  rw [hε]
  have h := congrArg (cA D) ((hε _).1 (hX j i))
  rw [(cA D).map_mul, hcε] at h
  exact h

theorem exists_onb (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (ht : Tame D v)
    (hεε : ε * ε = ε) (hcε : cA D ε = ε) (hεO : ε ∈ intAt D (· = v)) (hεI : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (hΛ : IsSDAt S v Λ) :
    ∃ b b' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, b i j ∈ idAt D (· = v)) ∧
      (∀ i j, b' i j ∈ idAt D (· = v)) ∧ b * b' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      b' * b = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (b' *ᵥ y) i ∈ intAt D (· = v))) ∧
      adj b * (gA S * b) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  have adj_mul {l m n : ℕ} (X : Matrix (Fin l) (Fin m) (AE D)) (Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X * Y) = adj Y * adj X := by
    ext i j
    change cA D ((X * Y) j i) = (adj Y * adj X) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  obtain ⟨β, β', hβ, hβ', h1, h2, hmem, hHO, hHc, hH⟩ := GlobalTheory.T.exists_unimodular_basis_selfDual_lattice_at_place D S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨P, P', hP, hP', hPP', hP'P, hPH⟩ := GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace D v ε S.rank _ ht hεε hcε hεO hεI hHO hHc hH
  refine ⟨β * P, P' * β', mul_mem_idAt_left P hβ, mul_mem_idAt_right P' hβ', ?_, ?_, ?_, ?_⟩
  · calc β * P * (P' * β') = β * (P * P') * β' := by simp only [Matrix.mul_assoc]
      _ = ε • (β * β') := by rw [hPP', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [h1, smul_smul, hεε]
  · calc P' * β' * (β * P) = P' * (β' * β) * P := by simp only [Matrix.mul_assoc]
      _ = ε • (P' * P) := by rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [hP'P, smul_smul, hεε]
  · intro y hy
    rw [hmem y hy]
    constructor
    · intro h i
      rw [← Matrix.mulVec_mulVec]
      exact mulVec_mem_intAt hP' h i
    · intro h i
      have hz : β' *ᵥ y = P *ᵥ (P' *ᵥ (β' *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, hPP', smul_mulVec', Matrix.one_mulVec,
          smul_vec_eq_self hεI (mulVec_mem_idAt β' hy)]
      rw [hz]
      exact mulVec_mem_intAt hP (fun j => by rw [Matrix.mulVec_mulVec]; exact h j) i
  · rw [adj_mul, ← hPH]
    simp only [Matrix.mul_assoc]

theorem selfDual_orbit : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  intro D S v Λ Λ' ht hΛ hΛ'
  have adj_mul {l m n : ℕ} (X : Matrix (Fin l) (Fin m) (AE D)) (Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X * Y) = adj Y * adj X := by
    ext i j
    change cA D ((X * Y) j i) = (adj Y * adj X) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  obtain ⟨⟨ε, hεε, hcε, hεO, hεI, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  obtain ⟨b, b', hb, hb', hbb', hb'b, hmem, hG⟩ := exists_onb S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨c, c', hc, hc', hcc', hc'c, hmem', hG'⟩ := exists_onb S v ε Λ' ht hεε hcε hεO hεI hΛ'
  set g := c * b' with hg
  have hgI : ∀ i j, g i j ∈ idAt D (· = v) := mul_mem_idAt_right c hb'
  have hag : ε • adj g = adj g := smul_eq_self hεI (adj_mem_idAt hcε hεI hgI)
  have hgg : ε • g = g := smul_eq_self hεI hgI
  have hb'b' : adj b' * b' = ε • gA S := by
    have h := congrArg (fun X => adj b' * X * b') hG
    rw [Matrix.mul_smul, Matrix.mul_one, smul_eq_self hεI (adj_mem_idAt hcε hεI hb')] at h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, hbb', adj_smul,
      adj_one, hcε, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hεε]
  have hf1 : adj g * (gA S * g) = ε • gA S := by
    rw [hg, adj_mul]
    calc adj b' * adj c * (gA S * (c * b')) = adj b' * (adj c * (gA S * c)) * b' := by simp only [Matrix.mul_assoc]
      _ = ε • gA S := by rw [hG', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hb'b', smul_smul, hεε]
  have haG : adj g * gA S = ε • (adj g * gA S) := by rw [← Matrix.smul_mul, hag]
  have hGg : gA S * g = ε • (gA S * g) := by rw [← Matrix.mul_smul, hgg]
  have hunit : adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S := by
    show adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S
    rw [adj_add, adj_sub, adj_one, adj_smul, adj_one, hcε]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    rw [hf1]
    simp only [smul_add, smul_sub]
    rw [← haG, ← hGg, smul_smul, hεε]
    abel
  refine ⟨ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit, ?_, ?_⟩
  · refine (mem_congGrp_iff S (idAt D (· = v)) _).2 fun i j => ?_
    show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idAt D (· = v)
    have e : (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j =
        g i j - ε * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact sub_mem (hgI i j) (Ideal.mul_mem_right _ _ hεO.1)
  · intro y hy
    have hMy : mt S (ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit) *ᵥ y = g *ᵥ y := by
      show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) *ᵥ y = g *ᵥ y
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec', Matrix.one_mulVec,
        smul_vec_eq_self hεI hy, sub_self, add_zero]
    rw [hMy, hmem y hy, hmem' _ (mulVec_mem_idAt g hy)]
    have : c' *ᵥ (g *ᵥ y) = b' *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mul_assoc, hc'c, Matrix.smul_mul, Matrix.one_mul,
        smul_eq_self hεI hb']
    rw [this]

end GlobalTheory.IwaOrbit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattices_single_orbit_tamePlace : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  first | exact @GlobalTheory.IwaOrbit.selfDual_orbit | exact GlobalTheory.IwaOrbit.selfDual_orbit | (intros; apply GlobalTheory.IwaOrbit.selfDual_orbit <;> assumption)
end

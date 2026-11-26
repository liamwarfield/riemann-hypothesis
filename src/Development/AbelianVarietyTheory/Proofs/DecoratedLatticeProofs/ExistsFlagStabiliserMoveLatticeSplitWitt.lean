module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7}

theorem mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
    M *ᵥ colMul X i a = fun r => a * (M * X) r i := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adj_diagonal {n : ℕ} (f : Fin n → AE D) :
    adj (Matrix.diagonal f) = Matrix.diagonal (fun i => cA D (f i)) := by
  ext i j; simp [adj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
    (h : A * (B * B') = C) (X : Mx D p k) :
    A * (B * (B' * X)) = C * X := by
  rw [← h]; simp only [Matrix.mul_assoc]

theorem mul_tail₄ {a m n p q k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {B'' : Mx D p q} {C : Mx D a q}
    (h : A * (B * (B' * B'')) = C) (X : Mx D q k) :
    A * (B * (B' * (B'' * X))) = C * X := by
  rw [← h]; simp only [Matrix.mul_assoc]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem gXX {k : ℕ} (X : Mx D ρ k) : adj d.jX * (gA S * (d.jX * X)) = 0 := by
  rw [mul_tail₃ d.gram_XX, Matrix.zero_mul]
theorem gYX {k : ℕ} (X : Mx D ρ k) : adj d.jY * (gA S * (d.jX * X)) = X := by
  rw [mul_tail₃ d.gram_YX, Matrix.one_mul]
theorem g0X {k : ℕ} (X : Mx D ρ k) : adj d.j0 * (gA S * (d.jX * X)) = 0 := by
  rw [mul_tail₃ d.gram_0X, Matrix.zero_mul]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_eq_of_mem {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {x : Mx D m n} (hx : ∀ i j, x i j ∈ idAt D P) : ε • x = x := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul, (hε _).1 (hx i j)]

theorem one_sub_mul_self {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hεε, sub_self]

theorem one_sub_sq {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [mul_sub, mul_one, one_sub_mul_self hεε, sub_zero]

theorem kill_left {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    (1 - ε) • (x * X) = 0 := by
  rw [← Matrix.smul_mul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.zero_mul]

theorem diag_absorb {ε : AE D} {n : ℕ} {α : Fin n → AE D} (hαε : ∀ i, ε * α i = α i) :
    ε • Matrix.diagonal α = Matrix.diagonal α := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · exact hαε i
  · rw [mul_zero]

theorem diag_const {ε : AE D} {n : ℕ} {α β : Fin n → AE D} (hαβ : ∀ i, α i * β i = ε) :
    (Matrix.diagonal fun i => α i * β i) = ε • (1 : Mx D n n) := by
  have : (fun i => α i * β i) = fun _ => ε := funext hαβ
  rw [this]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

set_option maxHeartbeats 1000000 in
theorem imYX {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α β : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    (hαβ : ∀ i, α i * β i = ε) {b : Mx D ρ ρ} (hb : ε • b = b) {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ)) :
    adj (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) *
      (gA S * (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 1 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₄ H1, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, gYX d, d.gram_YX, kill_left hεε (diag_absorb hαε), kill_left hεε hb, add_zero, smul_smul]
  rw [zero_add, Matrix.diagonal_mul_diagonal, one_sub_sq hεε]
  rw [diag_const hαβ, smul_smul, hεε, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem kill_mid₂ {ε : AE D} (hεε : ε * ε = ε) {m n p q k : ℕ} {x : Mx D p q} (hx : ε • x = x)
    (A : Mx D m n) (B : Mx D n p) (X : Mx D q k) : (1 - ε) • (A * (B * (x * X))) = 0 := by
  rw [← Matrix.mul_smul, ← Matrix.mul_smul, kill_left hεε hx, Matrix.mul_zero, Matrix.mul_zero]

theorem absorb_mul {ε : AE D} {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    x * (ε • X) = x * X := by
  rw [Matrix.mul_smul, ← Matrix.smul_mul, hx]

theorem imXX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} :
    adj (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))) *
      (gA S * (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  rw [adj_mul, Matrix.mul_assoc, gXX, Matrix.mul_zero]

set_option maxHeartbeats 1000000 in
theorem imYY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c') (H2 : adj c' * (gA S * c') = 0) :
    adj (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) *
      (gA S * (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₃ H2, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, d.gram_YY, smul_zero,
    kill_mid₂ hεε hc, kill_left hεε (diag_absorb hαε), add_zero, Matrix.zero_mul]

set_option maxHeartbeats 1000000 in
theorem imOO {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0))) * (gA S * (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0)))) = gA S₀ := by
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, d.gram_00, d.wittDecomp_gram_X_anisotropic,
    gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0))) * (gA S * (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  simp only [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} {b : Mx D ρ ρ} (hb : ε • b = b)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ)) :
    adj (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0))) * (gA S * (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have adjH1 : adj b * (adj d.jX * (gA S * c')) = ε • (1 : Mx D ρ ρ) := by
    have := congrArg adj H1
    simpa only [adj_mul, adj_gA, adj_adj, adj_smul, adj_one, hεc, Matrix.mul_assoc] using this
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [mul_tail₄ adjH1, Matrix.smul_mul, Matrix.one_mul, absorb_mul hc, sub_self, zero_add]
  simp only [Matrix.mul_smul, d.gram_0Y, d.gram_XY, Matrix.mul_one, smul_zero, kill_mid₂ hεε hc, sub_zero]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)


set_option maxHeartbeats 1000000 in
theorem smul_sub_one {ε : AE D} (M : Mx D S.rank S.rank)
    (hX : ε • (M * d.jX - d.jX) = M * d.jX - d.jX) (h0 : ε • (M * d.j0 - d.j0) = M * d.j0 - d.j0)
    (hY : ε • (M * d.jY - d.jY) = M * d.jY - d.jY) : ε • (M - 1) = M - 1 := by
  have e : M - 1 = (M * d.jX - d.jX) * d.pX + (M * d.j0 - d.j0) * d.p0 + (M * d.jY - d.jY) * d.pY := by
    have e1 : M - 1 = (M - 1) * (d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY) := by
      rw [d.sum_eq_one, Matrix.mul_one]
    rw [e1]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  rw [e, smul_add, smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, hX, h0, hY]

theorem smul_shift {ε : AE D} (hεε : ε * ε = ε) {m n : ℕ} {x : Mx D m n} (hx : ε • x = x) (y : Mx D m n) :
    ε • (x + (1 - ε) • y - y) = x + (1 - ε) • y - y := by
  have e : x + (1 - ε) • y - y = x - ε • y := by
    rw [sub_smul, one_smul]; abel
  rw [e, smul_sub, hx, smul_smul, hεε]

theorem scalar_X {R : Type*} [CommRing R] {ε a b x y : R} (ha : ε * a = a) (hab : a * b = ε) (hx : ε * x = x) :
    a * (x * b + (1 - ε) * y) = x := by
  linear_combination x * hab + hx - y * ha

end GlobalTheory.IwaPlace.BuildQ


open GlobalTheory.IwaPlace.BuildQ in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → adj c' * (gA S * c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q * d.jX = d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX * b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  intro D S S₀ ρ d v ε hεε hεc _ hε α β b c' hα hβ hαβ hb hc' H1 H2
  have hb' : ε • b = b := smul_eq_of_mem hε hb
  have hc : ε • c' = c' := smul_eq_of_mem hε hc'
  have hαε : ∀ i, ε * α i = α i := fun i => (hε _).1 (hα i)
  have hβε : ∀ i, ε * β i = β i := fun i => (hε _).1 (hβ i)
  have h : HypDec.Images S S₀ (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))
      (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0)))
      (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) :=
    ⟨imXX d, imYY d hεε hεc hαε hc H2, imYX d hεε hεc hαε hαβ hb' hc H1, imOO d, imOX d, imOY d hεε hεc hb' hc H1⟩
  have hjb : ε • (d.jX * b) = d.jX * b := by rw [← Matrix.mul_smul, hb']
  have hE : d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))
      = (d.jX * b) * Matrix.diagonal β + (1 - ε) • d.jX := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨d.ofImages _ _ _ h, ?_, d.ofImages_jX h, fun i => ?_, fun i => ?_⟩
  · have key := smul_sub_one d (ε := ε) (Formalism.L2.Theta.mt S (d.ofImages _ _ _ h))
      (by rw [d.ofImages_jX h, hE]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hjb]) _)
      (by rw [d.wittDecomp_ofImages_inclAnisotropic h, sub_sub_cancel_left, smul_neg, ← Matrix.smul_mul, hjb])
      (by rw [d.ofImages_jY h]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hc]) _)
    refine (mem_congGrp_iff S _ _).2 fun i j => (hε _).2 ?_
    exact congrFun (congrFun key i) j
  · rw [mulVec_colMul, d.ofImages_jX h, hE]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    exact scalar_X (hαε i) (hαβ i) (congrFun (congrFun hjb k) i)
  · rw [mulVec_colMul, d.ofImages_jY h]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    refine scalar_X ?_ ?_ (congrFun (congrFun hc k) i)
    · rw [← hεc, ← map_mul, hβε]
    · rw [← map_mul, mul_comm, hαβ, hεc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFramStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.IwaPlace.BuildQ in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → adj c' * (gA S * c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q * d.jX = d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX * b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  exact @_root_.GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.DualIso

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
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

theorem intAt_mul_mem {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem hermAt_smul_left (S : HSp D) (o : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (o • y) x = o * hermAt S y x := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_mem_of_isSDAt {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {o : AE D} (ho : o ∈ intAt D (· = v)) {y : Fin S.rank → AE D} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM.2.2 _ fun i => ?_).2 fun x hx => ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hM.1 y hy i)
  · rw [hermAt_smul_left]; exact intAt_mul_mem ho ((hM.2.2 y (hM.1 y hy)).1 hy x hx)

theorem col_mul_mem {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M) {ρ : ℕ}
    (A : Mx D S.rank ρ) (B : Mx D ρ ρ) (hA : ∀ i, (fun k => A k i) ∈ M) (hB : ∀ m i, B m i ∈ intAt D (· = v))
    (i : Fin ρ) : (fun k => (A ⬝ B) k i) ∈ M := by
  have e : (fun k => (A ⬝ B) k i) = ∑ m, B m i • (fun k => A k m) := by
    funext k; simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [e]; exact AddSubgroup.sum_mem _ fun m _ => smul_mem_of_isSDAt hM (hB m i) (hA m)

theorem gram_entry (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) (i j : Fin ρ) :
    (adj c' ⬝ (gA S ⬝ c')) i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
  simp only [hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem smul_mul_smul_one {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (ε • (1 : Mx D ρ ρ)) ⬝ (w • H) = (ε * w) • H := by
  rw [smul_mul_assoc, one_mul, smul_smul]

theorem smul_mul_smul_one' {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (w • H) ⬝ (ε • (1 : Mx D ρ ρ)) = (ε * w) • H := by
  rw [mul_smul_comm, mul_one, smul_smul]

theorem adj_gram_self (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) : adj (adj c' ⬝ (gA S ⬝ c')) = adj c' ⬝ (gA S ⬝ c') := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem gram_swap_smul (S : HSp D) {ρ : ℕ} {ε : AE D} (hεc : cA D ε = ε) (c c' : Mx D S.rank ρ)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ) := by
  have := congrArg adj hcc
  rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at this

theorem pair_sub (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc0 : adj c ⬝ (gA S ⬝ c) = 0) (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero, sub_zero, hcc]

theorem pair_sub' (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc' : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c') = adj c' ⬝ (gA S ⬝ c') - adj K ⬝ (ε • (1 : Mx D ρ ρ)) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']

theorem self_sub (S : HSp D) {ρ : ℕ} (c'' c c' : Mx D S.rank ρ) (K : Mx D ρ ρ) (h : c'' = c' - c ⬝ K) :
    adj c'' ⬝ (gA S ⬝ c'') = adj c'' ⬝ (gA S ⬝ c') - adj c'' ⬝ (gA S ⬝ c) ⬝ K := by
  rw [h, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
    ← Matrix.mul_assoc (adj (c' - c ⬝ K)) (gA S ⬝ c) K]

theorem isotropic_core {S : HSp D} {v : Pl D} {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {w : AE D} (hw : w ∈ intAt D (· = v)) (hwc : w + cA D w = ε) {ρ : ℕ} (c c' : Mx D S.rank ρ)
    (hc : ∀ i, (fun k => c k i) ∈ M) (hc' : ∀ i, (fun k => c' k i) ∈ M) (hcc0 : adj c ⬝ (gA S ⬝ c) = 0)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) ∧
      adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  obtain ⟨H, hH⟩ : ∃ H : Mx D ρ ρ, H = adj c' ⬝ (gA S ⬝ c') := ⟨_, rfl⟩
  have hHint : ∀ i j, H i j ∈ intAt D (· = v) := fun i j => by
    rw [hH, gram_entry]; exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by rw [hH]; exact adj_gram_self S c'
  have hcc' := gram_swap_smul S hεc c c' hcc
  have hKint : ∀ m i, (w • H) m i ∈ intAt D (· = v) := fun m i => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact intAt_mul_mem hw (hHint m i)
  have e3 : ε * cA D w + ε * w = ε := by rw [← mul_add, add_comm, hwc, hεε]
  have f3 : H - (ε * cA D w) • H - (ε * w) • H = 0 := by
    rw [sub_sub, ← add_smul, e3, hεH, sub_self]
  have e1 := pair_sub S (ε := ε) c c' (w • H) hcc0 hcc
  have e2 := pair_sub' S c c' (w • H) hcc'
  rw [← hH, adj_smul, hadjH, smul_mul_smul_one'] at e2
  refine ⟨c' - c ⬝ (w • H), fun i => ?_, e1, ?_⟩
  · have e : (fun k => (c' - c ⬝ (w • H)) k i) = (fun k => c' k i) - fun k => (c ⬝ (w • H)) k i := rfl
    rw [e]; exact sub_mem (hc' i) (col_mul_mem hM c _ hc hKint i)
  · rw [self_sub S _ c c' (w • H) rfl, e1, e2, smul_mul_smul_one, f3]
theorem dual_isotropic : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  have hcc0 : adj (d.jX ⬝ b) ⬝ (gA S ⬝ (d.jX ⬝ b)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b, ← Matrix.mul_assoc (adj d.jX),
      d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  exact isotropic_core hεε hεc hε hM hw hwc (d.jX ⬝ b) c' hc hc' hcc0 hcc

end GlobalTheory.IwaPlace.DualIso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX * b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' * (gA S * c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  let c : Mx D S.rank ρ := d.jX * b
  change adj c' * (gA S * c) = ε • (1 : Mx D ρ ρ) at hcc
  have hcc0 : adj c * (gA S * c) = 0 := by
    dsimp only [c]
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b,
      ← Matrix.mul_assoc (adj d.jX), d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  have hcc' : adj c * (gA S * c') = ε • (1 : Mx D ρ ρ) := by
    have h := congrArg adj hcc
    rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at h
  let H : Mx D ρ ρ := adj c' * (gA S * c')
  have hHint (i j : Fin ρ) : H i j ∈ intAt D (· = v) := by
    have hgram : H i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
      simp only [H, hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Finset.mul_sum, mul_assoc]
    rw [hgram]
    exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by
    dsimp only [H]
    rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]
  let K : Mx D ρ ρ := w • H
  have hKint (m i : Fin ρ) : K m i ∈ intAt D (· = v) := by
    change (w • H) m i ∈ intAt D (· = v)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.IwaPlace.DualIso.intAt_mul_mem hw (hHint m i)
  let c'' : Mx D S.rank ρ := c' - c * K
  have hpair : adj c'' * (gA S * c) = ε • (1 : Mx D ρ ρ) := by
    dsimp only [c'']
    rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero,
      sub_zero, hcc]
  refine ⟨c'', ?_, hpair, ?_⟩
  · intro i
    have hcol : (fun k => (c * K) k i) = ∑ m, K m i • (fun k => c k m) := by
      funext k
      simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
    change (fun k => c' k i) - (fun k => (c * K) k i) ∈ M
    rw [hcol]
    exact sub_mem (hc' i) (AddSubgroup.sum_mem _ fun m _ =>
      GlobalTheory.IwaPlace.DualIso.smul_mem_of_isSDAt hM (hKint m i) (hc m))
  · have hleft : adj c'' * (gA S * c') = H - (ε * cA D w) • H := by
      dsimp only [c'']
      rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']
      change H - adj (w • H) * (ε • (1 : Mx D ρ ρ)) = _
      rw [adj_smul, hadjH, mul_smul_comm, mul_one, smul_smul]
    have hsum : ε * cA D w + ε * w = ε := by
      rw [← mul_add, add_comm, hwc, hεε]
    calc
      adj c'' * (gA S * c'') =
          adj c'' * (gA S * c') - (adj c'' * (gA S * c)) * K := by
        change adj c'' * (gA S * (c' - c * K)) = _
        rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
          ← Matrix.mul_assoc (adj c'') (gA S * c) K]
      _ = H - (ε * cA D w) • H - (ε * w) • H := by
        rw [hleft, hpair]
        change H - (ε * cA D w) • H - (ε • (1 : Mx D ρ ρ)) * (w • H) = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      _ = 0 := by rw [sub_sub, ← add_smul, hsum, hεH, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

theorem iwasawa_flag_move : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d L L₀ v hT hL hM h hh
  obtain ⟨⟨ε, hεε, hεc, hεI, hε, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hMsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v h⁻¹ (inv_mem hh) _ hL
  set M := (latV S L (· = v)).comap (Matrix.mulVecLin (mt S h⁻¹)).toAddMonoidHom with hMdef
  obtain ⟨b, hbu, hbI, hbM, c', hc'M, hpair⟩ := GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε hT M hMsd
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace D v ε hεε hεc hεI hε hT
  obtain ⟨c'', hc''M, hpair', hiso⟩ := GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε M hMsd w hw hw1 b c' hbI hbM hc'M hpair
  obtain ⟨α, β, hα, hβ, hαβ, hX, hY⟩ := GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hL hM
  have hc''I : ∀ i j, c'' i j ∈ idAt D (· = v) := fun i j => hMsd.1 _ (hc''M j) i
  obtain ⟨q, hq, hqX, hqα, hqβ⟩ := GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames D S S₀ ρ d v ε hεε hεc hεI hε α β b c'' hα hβ hαβ hbI hc''I hpair' hiso
  have hNsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v q hq M hMsd
  obtain ⟨Λ₀, hΛ, hz⟩ := GlobalTheory.T.selfDualLatticeAtPlace_splits_hyperbolic_plus_core D S S₀ ρ d v ε hεε hεc hεI hε _ α β hNsd hα hβ hαβ
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jX i (α i) ∈ M
      rw [hqα]; exact hbM i)
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jY i (cA D (β i)) ∈ M
      rw [hqβ]; exact hc''M i)
  refine ⟨q, hq, ⟨b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ), fun i j hji => ?_, hqX⟩, Λ₀, hΛ, fun z hz' => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_diagonal, hbu i j hji, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  · have e1 : (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v)) ↔
        z ∈ (M.comap (Matrix.mulVecLin (mt S q)).toAddMonoidHom) := by
      rw [AddSubgroup.mem_comap, hMdef, AddSubgroup.mem_comap]
      change _ ↔ mt S h⁻¹ *ᵥ (mt S q *ᵥ z) ∈ _
      rw [Matrix.mulVec_mulVec, ← mt_mul]
    rw [e1, hz z hz']
    refine and_congr (forall_congr' fun i => (hX i _ (mulVec_mem_idAt _ hz' i)).symm)
      (and_congr (forall_congr' fun i => (hY i _ (mulVec_mem_idAt _ hz' i)).symm) Iff.rfl)

end GlobalTheory.IwaPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWittStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_stabiliser_move_lattice_split_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  first | exact @GlobalTheory.IwaPlace.iwasawa_flag_move | exact GlobalTheory.IwaPlace.iwasawa_flag_move | (intros; apply GlobalTheory.IwaPlace.iwasawa_flag_move <;> assumption)
end

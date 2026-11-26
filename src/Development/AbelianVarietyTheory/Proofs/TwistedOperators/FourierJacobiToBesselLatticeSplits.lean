module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLatti

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjections
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

variable {D : D7}

theorem colsOf_eq_mul {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    colsOf a f s = a * Matrix.of (fun q p => if q = f p then s p else 0) := by
  ext i p
  simp only [colsOf, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

theorem antiDiagonalGram_neg_one_castLE_row {c ρ : ℕ} (h : 2 * ρ ≤ c) (p : Fin ρ) (r : Fin c) :
    antiDiagonalSignGramMatrix c (-1 : D.host.E) (Fin.castLE (by omega) p) r = if r = (Fin.castLE (by omega) p : Fin c).rev then 1 else 0 := by
  have := p.2; have := r.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
  split_ifs <;> first | rfl | omega

theorem projY_mem_lat : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d ⟨h, he, s, he'⟩ Λ 𝔟 v ⟨y, hy, u, hu, hv⟩
  subst hv
  set f : Fin ρ → Fin c := Fin.castLE (by omega) with hf
  set t : Fin ρ → D.host.E := fun p => (-D.host.xi0) ^ (p.1 + 1) with ht
  set Pe : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = f p then t p else 0) with hPe
  set Pe' : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = (f p).rev then s p else 0) with hPe'
  have hE : d.e = a.a * Pe := by rw [he, colsOf_eq_mul]
  have hE' : d.e' = a.a * Pe' := by rw [he', colsOf_eq_mul]
  have hG : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  have hperp' : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc] at this
  have hQF : d.qY * frameMat B A a.ι = 0 := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hperp', Matrix.mul_zero]
  have hQA : d.qY * a.a = Matrix.of (fun p r => if r = (f p).rev then star (t p) else 0) := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hgram]
    ext p r
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hf, antiDiagonalGram_neg_one_castLE_row h, mul_ite, mul_one, mul_zero]
  have hS : ∀ p, s p * star (t p) = 1 := by
    intro p
    have h1 : d.eᴴ * B.gram * d.e' = 1 := by
      have := congrArg Matrix.conjTranspose d.e'e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_one, ← Matrix.mul_assoc] at this
    have h2 : (d.qY * a.a * Pe') p p = 1 := by
      rw [Matrix.mul_assoc, ← hE', HypDec.qY, h1, Matrix.one_apply_eq]
    rw [hQA] at h2
    simp only [Matrix.mul_apply, hPe', Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    rw [mul_comm]; exact h2
  refine ⟨0, Λ.zero_mem, fun q => ∑ p, if q = (f p).rev then u q else 0, fun q => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · exact hu q
    · exact Submodule.zero_mem _
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, hQF, zero_mulVec, zero_add,
      mulVec_mulVec, hQA, hE', Matrix.mul_assoc, ← mulVec_mulVec]
    apply congrArg (fun x => a.a *ᵥ x)
    ext q
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hPe', Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hq : q = (f p).rev
    · subst hq
      simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hS p, one_mul]
    · simp only [hq, if_false, zero_mul, Finset.sum_const_zero]

end GlobalTheory.AscFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proj_Y_preserves_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  first | exact @GlobalTheory.AscFin.projY_mem_lat | exact GlobalTheory.AscFin.projY_mem_lat | (intros; apply GlobalTheory.AscFin.projY_mem_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory

theorem projX_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d hA Λ 𝔟 v hv
  obtain ⟨hc, he, s, he'⟩ := hA
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have hGh : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  set N : Matrix (Fin c) (Fin c) D.host.E := antiDiagonalSignGramMatrix c (-1) with hN
  have hK : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    simpa [Matrix.conjTranspose_mul, hGh, Matrix.mul_assoc] using this
  have hρc : ρ ≤ c := by omega
  let P : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = (Fin.castLE hρc p).rev then s p else 0
  let Q : Matrix (Fin c) (Fin ρ) D.host.E := fun q p => if q = Fin.castLE hρc p then (-D.host.xi0) ^ (p.1 + 1) else 0
  have heP : d.e' = a.a * P := by
    rw [he']; ext i p; rw [Matrix.mul_apply]; simp [colsOf, P, mul_comm]
  have heQ : d.e = a.a * Q := by
    rw [he]; ext i p; rw [Matrix.mul_apply]; simp [colsOf, Q, mul_comm]
  have hPN : ∀ p q, (Pᴴ * N) p q = if q = Fin.castLE hρc p then star (s p) else 0 := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    simp only [P, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := p.2; have := q.2
    simp only [hN, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
    split_ifs <;> first | (exfalso; omega) | ring
  have hdiag : ∀ p : Fin ρ, star (s p) * (-D.host.xi0) ^ (p.1 + 1) = 1 := by
    intro p
    have h1 := d.e'e
    rw [heP, heQ, Matrix.conjTranspose_mul] at h1
    have h2 : Pᴴ * a.aᴴ * B.gram * (a.a * Q) = Pᴴ * N * Q := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 p) p
    rw [Matrix.mul_apply] at h3
    simp only [hPN, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Q, Matrix.one_apply_eq] at h3
    simpa using h3
  have hqX : d.qX = Pᴴ * a.aᴴ * B.gram := by
    rw [HypDec.qX, heP, Matrix.conjTranspose_mul]
  have ht : d.qX *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = (Pᴴ * N) *ᵥ u := by
    have h1 : Pᴴ * a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
      calc _ = Pᴴ * (a.aᴴ * B.gram * frameMat B A a.ι) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hK, Matrix.mul_zero]
    have h2 : Pᴴ * a.aᴴ * B.gram * a.a = Pᴴ * N := by
      rw [← hgram]; simp only [Matrix.mul_assoc]
    rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hqX, h1, h2, zero_mulVec, zero_add]
  have hu' : ∀ q : Fin c, (Q *ᵥ ((Pᴴ * N) *ᵥ u)) q = if q.1 < ρ then u q else 0 := by
    intro q
    simp only [mulVec, dotProduct, hPN, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Q]
    split_ifs with hq
    · rw [Finset.sum_eq_single ⟨q.1, hq⟩]
      · have e1 : q = Fin.castLE hρc ⟨q.1, hq⟩ := Fin.ext rfl
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← mul_assoc, mul_comm ((-D.host.xi0) ^ _), hdiag, one_mul, if_pos e1, ← e1]
      · intro b _ hb
        rw [if_neg]
        intro e; apply hb; ext; simp only [Fin.ext_iff, Fin.val_castLE, Fin.val_mk] at e ⊢; omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e; apply hq; rw [e]; simp
  refine ⟨0, Λ.zero_mem, Q *ᵥ ((Pᴴ * N) *ᵥ u), fun q => ?_, ?_⟩
  · rw [hu']; split_ifs
    · exact hu q
    · exact (𝔟 q).val.zero_mem
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, ht, heQ, ← mulVec_mulVec]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proj_X_preserves_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  first | exact @GlobalTheory.projX_embedding_lattice | exact GlobalTheory.projX_embedding_lattice | (intros; apply GlobalTheory.projX_embedding_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjections
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjLat

variable {D : D7}

theorem tmul_mul_incA (x : AF D.host.F) (y z : D.host.E) : (x ⊗ₜ[D.host.F] y) * incA D z = x ⊗ₜ[D.host.F] (y * z) := by
  show (x ⊗ₜ[D.host.F] y) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem of_tmul_mul_rat {m n k : ℕ} (x : AF D.host.F) (X : Matrix (Fin m) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin k) D.host.E) :
    HMul.hMul (Matrix.of fun i j => x ⊗ₜ[D.host.F] X i j : Mx D m n) (rat M : Mx D n k) =
      Matrix.of fun i j => x ⊗ₜ[D.host.F] (X * M) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, TensorProduct.tmul_sum]

theorem latO_mul_rat {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} (M M' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hadj : M'ᴴ * S.gram = S.gram * M) (hL : ∀ s ∈ LS, M' *ᵥ s ∈ LS) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    HMul.hMul (u : Mx D T.rank S.rank) (rat M : Mx D S.rank S.rank) ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a, ha, M' *ᵥ s, hL s hs, t, ht, ?_⟩
    have h : ∀ l j, ∑ k, star (M' k l) * S.gram k j = ∑ k, S.gram l k * M k j := fun l j => by
      have := congrFun (congrFun hadj l) j
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, ← TensorProduct.tmul_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum, mul_assoc]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp_rw [mul_left_comm (star (M' _ y)) (star (s y))]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h y j]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_rat {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hN : ∀ x ∈ N, x * M ∈ N) {w : Mx D m n} (hw : w ∈ hatMx N) :
    HMul.hMul w (rat M : Mx D n n) ∈ hatMx N := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    exact ⟨α, hα, x * M, hN x hx, of_tmul_mul_rat _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ)
    {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') : x * M ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on (p := fun x => x * M ∈ I • homLat Λ Λ') hx ?_ ?_
  · intro r hr n hn
    show (r • n) * M ∈ _
    rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (fun y hy => by rw [← Matrix.mulVec_mulVec]; exact hn _ (hM y hy))
  · intro x y hx hy
    show (x + y) * M ∈ _
    rw [Matrix.add_mul]; exact add_mem hx hy

theorem proj_adj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e' * d.qY)ᴴ * S.gram = S.gram * (d.e * d.qX) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem proj_adj' {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e * d.qX)ᴴ * S.gram = S.gram * (d.e' * d.qY) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem latRow_mul_rat {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ)
    (Mx₁ Mx₂ : Matrix (Fin (G.V (.grid (i + 1) 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) D.host.E)
    (hadj : Mx₂ᴴ * (G.V (.grid (i + 1) 0)).gram = (G.V (.grid (i + 1) 0)).gram * Mx₁)
    (h1 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₁ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    (h2 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₂ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    {u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))} (hu : u ∈ latRow G i) :
    HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ latRow G i := by
  obtain ⟨hu1, hu2⟩ := hu
  have hadj' : Mx₂ᴴ * (G.pS (.chi i 0)).gram = (G.pS (.chi i 0)).gram * Mx₁ := by
    show Mx₂ᴴ * (-(G.V (.grid (i + 1) 0)).gram) = (-(G.V (.grid (i + 1) 0)).gram) * Mx₁
    rw [Matrix.mul_neg, Matrix.neg_mul, hadj]
  have hu1' : u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) := hu1
  have L1 := @latO_mul_rat D (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) Mx₁ Mx₂ hadj' h2
  have t1 := L1 hu1'
  have t2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ hatMx (G.modul • homLat (G.latS (.chi i 0)) (G.latT (.chi i 0))) := by
    intro e he
    rw [← Matrix.smul_mul]
    exact hatMx_mul_rat _ _ (fun x hx => smul_homLat_mul _ _ _ _ h1 hx) (hu2 e he)
  exact ⟨t1, t2⟩

theorem latRow_proj : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  have hA := hF.hJ (σ + 1) h
  have e : G.Λ (.grid (2 * σ + 2 + 1) 0) = _ := G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)
  have hX : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact GlobalTheory.T.proj_X_preserves_embedding_lattice _ _ hA _ _ _ hv
  have hY : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact GlobalTheory.T.proj_Y_preserves_embedding_lattice _ _ hA _ _ _ hv
  rw [show (F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX = rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) from (rat_mul _ _).symm,
    show (F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY = rat ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) from (rat_mul _ _).symm]
  exact ⟨latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj _) hX hY hu, latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj' _) hY hX hu⟩

end GlobalTheory.ProjLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjectionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_witt_projections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.ProjLat.latRow_proj | exact GlobalTheory.ProjLat.latRow_proj | (intros; apply GlobalTheory.ProjLat.latRow_proj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.SplitsFB

theorem inv_neg_mat {D : D7} {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplO_negSp {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have e : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem symplO_zero_left' {D : D7} (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  unfold symplO hO
  simp

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sd_grid (i : ℕ) (h1 : 1 ≤ i) (h : i ≤ D.R.m) : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
  (G.isV (X := .grid i 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd

theorem latRow_mxAt (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u} (hu : u ∈ latRow G i) : MxAt (fun _ => True) u :=
  ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega)) (fun _ => True) u).1
    hu.1).1

theorem latRow_pair (W : G.Weil) (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u u'} (hu : u ∈ latRow G i) (hu' : u' ∈ latRow G i) :
    W.ψ (symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u') = 1 := by
  have := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega))
    (fun _ => True) u (latRow_mxAt G i h1 h hu)).1 hu.1 u' hu'.1
  rwa [symplO_negSp, AddChar.map_neg_eq_inv, inv_eq_one] at this

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {x : Mx D m n} (hx : MxAt P x) (y : Mx D n k) : MxAt P (x ⬝ y) :=
  fun i j => by
    show (x * y) i j ∈ _
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

end


set_option maxHeartbeats 2000000 in
theorem splits_FB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hS := GlobalTheory.T.depthLatticeGridRow_stable_witt_projections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hT := GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hC := GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hB := GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) (by omega)
  refine ⟨fun u hu => ?_⟩
  set dV := F.dJ (σ + 1) h with hdV
  set dW := F.dB σ h' with hdW
  obtain ⟨hX, hY⟩ := hS u hu
  have e1 := dV.sum_eq_one
  have e2 := dW.sum_eq_one
  have h0 : u ⬝ (dV.j0 ⬝ dV.p0) ∈ latRow G (2 * σ + 2) := by
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    have e : u ⬝ (dV.j0 ⬝ dV.p0) = u - u ⬝ (dV.jX ⬝ dV.pX) - u ⬝ (dV.jY ⬝ dV.pY) := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem hu hX) hY
  set w := u ⬝ (dV.j0 ⬝ dV.p0) with hw
  obtain ⟨gX, gY⟩ := hT w h0
  have g0 : (dW.j0 ⬝ dW.p0) ⬝ w ∈ latRow G (2 * σ + 2) := by
    have s : (dW.jX ⬝ dW.pX) ⬝ w + (dW.j0 ⬝ dW.p0) ⬝ w + (dW.jY ⬝ dW.pY) ⬝ w = w := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, e2, Matrix.one_mul]
    have e : (dW.j0 ⬝ dW.p0) ⬝ w = w - (dW.jX ⬝ dW.pX) ⬝ w - (dW.jY ⬝ dW.pY) ⬝ w := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem h0 gX) gY
  have hA1 : dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc]; exact hX
  have hA2 : dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extY_apply, Matrix.mul_assoc]; exact hY
  have hB1 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) = (dW.jX ⬝ dW.pX) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, hw]; simp only [Matrix.mul_assoc]
  have hB2 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) = (dW.jY ⬝ dW.pY) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, hw]; simp only [Matrix.mul_assoc]
  have hG0 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) = (dW.j0 ⬝ dW.p0) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, hw]; simp only [Matrix.mul_assoc]
  have heq : u = dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) + dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) +
      dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0)) + dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0)) +
        dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) := by
    rw [map_add (f := _), map_add (f := _), hB1, hB2, hG0, HypDec.extX_apply, HypDec.extY_apply, ← Matrix.add_mul, ← Matrix.add_mul,
      show dW.jX ⬝ dW.pX + dW.jY ⬝ dW.pY + dW.j0 ⬝ dW.p0 = 1 from (add_right_comm _ _ _).trans e2, Matrix.one_mul, hw,
      Matrix.mul_assoc, Matrix.mul_assoc]
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    conv_lhs => rw [← s]
    abel
  refine ⟨u ⬝ dV.jX, hA1, u ⬝ dV.jY, AddSubgroup.subset_closure
      ⟨mxAt_mul (latRow_mxAt G (2 * σ + 2) (by omega) (by omega) hu) _,
        fun a ha => latRow_pair G W (2 * σ + 2) (by omega) (by omega) ha hA2⟩,
    dW.pX ⬝ (u ⬝ dV.j0), ?_, dW.pY ⬝ (u ⬝ dV.j0), ?_, dW.p0 ⬝ (u ⬝ dV.j0), ?_, heq, hC _ hA2, ?_⟩
  · show dV.ext0 _ (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB1]; exact hB gX
  · show dV.ext0 _ (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB2]; exact hB gY
  · show dV.ext0 _ (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) ∈ latRow G (2 * σ + 2)
    rw [hG0]; exact g0
  · rw [map_zero, symplO_zero_left', AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.SplitsFB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiToBessel_lattice_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  first | exact @GlobalTheory.AscFin.SplitsFB.splits_FB | exact GlobalTheory.AscFin.SplitsFB.splits_FB | (intros; apply GlobalTheory.AscFin.SplitsFB.splits_FB <;> assumption)
end

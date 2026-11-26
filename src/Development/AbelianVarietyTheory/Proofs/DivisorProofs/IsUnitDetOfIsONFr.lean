module

public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem reads_of_perC {D : D7} {r g : ℕ} (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x x' : Frame X.Ψ r)
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (f : WO V W → ℂ) (φ : TF V.rank g) (hf : Reads θ V W hr X bas idx f φ x) :
    Reads θ V W hr X bas idx f ((M.det ^ (V.rank / 2)) • φ) x' := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    have := congrFun (h fun τ => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
    exact this
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  obtain ⟨⟨R, hR, h1, h2⟩, h3⟩ := hf
  refine ⟨⟨R, hR, fun y hy => h1 y fun e => hy (by simp [e]), fun y z hz => by simp [h2 y z hz]⟩, fun w hw => ?_⟩
  have hz : ∀ b, hMat X bas idx x' *ᵥ zOf θ V W hr X idx x' w b = hMat X bas idx x *ᵥ zOf θ V W hr X idx x w b := by
    intro b
    have : zOf θ V W hr X idx x' w b = M *ᵥ zOf θ V W hr X idx x w b := h _
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  have hS : ∀ (c : ℂ) t z, thS (c • φ) t z = c * thS φ t z := by
    intro c t z
    simp only [thS, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
  rw [h3 w hw]
  simp only [hx, thA, hz, hT, hI, hS]
  have hd : (hMat X bas idx x).det = (hMat X bas idx x').det * M.det := by
    rw [hH, ← det_mul, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  rw [hd, mul_pow]
  ring

theorem det_tr_inv_block {r : ℕ} (P Q b : Matrix (Fin r) (Fin r) ℂ) (hb : IsUnit b.det) (hPQ : P + Q = 1)
    (hPP : P * P = P) (hc : b * P = P * b) (hs : Pᵀ = P) :
    (P * bᵀ + Q * b⁻¹).det ≠ 0 ∧ (P * bᵀ + Q * b⁻¹).det = (P * b + Q).det / (Q * b + P).det := by
  have hQ : Q = 1 - P := by rw [← hPQ]; abel
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  have h2 : b⁻¹ * b = 1 := nonsing_inv_mul _ hb
  generalize b⁻¹ = c at h1 h2 ⊢
  have hc' : c * P = P * c := by
    calc c * P = c * P * (b * c) := by rw [h1, Matrix.mul_one]
      _ = c * (P * b) * c := by simp only [Matrix.mul_assoc]
      _ = P * c := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hct : bᵀ * P = P * bᵀ := by
    have := congrArg transpose hc
    rw [transpose_mul, transpose_mul, hs] at this
    exact this.symm
  have hPP' : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
  have e1 : (Q * c + P) * (Q * b + P) = 1 := by
    have : c * (P * b) = P := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    subst hQ
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, h2, this, hc', hPP, hPP']
    abel
  have e2 : (P * c + Q) * (P * b + Q) = 1 := by
    have : c * (P * b) = P := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    subst hQ
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, h2, this, hc', hPP, hPP']
    abel
  have e3 : P * bᵀ + Q * c = (P * b + Q)ᵀ * (Q * c + P) := by
    have : ∀ y : Matrix (Fin r) (Fin r) ℂ, bᵀ * (P * y) = P * (bᵀ * y) := fun y => by
      rw [← Matrix.mul_assoc, hct, Matrix.mul_assoc]
    subst hQ
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, hs,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, this, hct, hPP, hPP']
    abel
  have d1 := congrArg det e1
  have d2 := congrArg det e2
  rw [det_mul, det_one] at d1 d2
  rw [e3, det_mul, det_transpose]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul_eq_one d2) (left_ne_zero_of_mul_eq_one d1), ?_⟩
  rw [div_eq_mul_inv, eq_inv_of_mul_eq_one_left d1]

theorem isUnit_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (h : IsONFr X x) (τ : X.Ψ) : IsUnit (mat x τ).det := by
  have e : FD.gram τ.1 X.Gm (mat x τ) = (mat x τ)ᵀ * (X.Gm.map τ.1 * (mat x τ).map conj) := by
    ext a b
    simp only [FD.gram, hermC, FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]
  have d := congrArg det (e.symm.trans (h τ))
  rw [det_mul, det_transpose, sgnM, det_diagonal] at d
  refine isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (d ▸ Finset.prod_ne_zero_iff.2 fun a _ => ?_))
  unfold sgn
  split_ifs <;> simp

def prFst (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => if (a : ℕ) < p then 1 else 0

theorem prFst_block_zero {r p : ℕ} {b : Matrix (Fin r) (Fin r) ℂ} (h : b * prFst r p = prFst r p * b) {a c : Fin r}
    (hac : ¬ ((a : ℕ) < p ↔ (c : ℕ) < p)) : b a c = 0 := by
  have := congrFun (congrFun h a) c
  simp only [prFst, mul_diagonal, diagonal_mul] at this
  by_cases ha : (a : ℕ) < p <;> by_cases hc : (c : ℕ) < p <;> simp_all

theorem perC_block {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x x' : Frame X.Ψ r) (τ : X.Ψ) (b : Matrix (Fin r) (Fin r) ℂ) (hb : IsUnit b.det)
    (hx' : mat x' τ = mat x τ * b) (hc : b * prFst r X.p0 = prFst r X.p0 * b) (u : X.Ψ → Fin r → ℂ) (a : Fin r) :
    perC X x' u (τ, a) = ∑ c, (prFst r X.p0 * bᵀ + (1 - prFst r X.p0) * b⁻¹) a c * perC X x u (τ, c) := by
  have hc' : b⁻¹ * prFst r X.p0 = prFst r X.p0 * b⁻¹ := by
    calc b⁻¹ * prFst r X.p0 = b⁻¹ * prFst r X.p0 * (b * b⁻¹) := by rw [mul_nonsing_inv _ hb, Matrix.mul_one]
      _ = b⁻¹ * (prFst r X.p0 * b) * b⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hc, ← Matrix.mul_assoc, nonsing_inv_mul _ hb, Matrix.one_mul]
  have hN : ∀ c, (prFst r X.p0 * bᵀ + (1 - prFst r X.p0) * b⁻¹) a c = if (a : ℕ) < X.p0 then b c a else b⁻¹ a c := by
    intro c
    simp only [Matrix.sub_mul, Matrix.one_mul, prFst, Matrix.add_apply, Matrix.sub_apply, diagonal_mul, transpose_apply]
    split_ifs <;> simp
  simp only [hN, perC, hx']
  by_cases ha : (a : ℕ) < X.p0
  · simp only [ha, if_true]
    have : hermC τ.1 X.Gm (FD.col (mat x τ * b) a) (u τ) =
        ∑ c, b c a * hermC τ.1 X.Gm (FD.col (mat x τ) c) (u τ) := by
      simp only [hermC, FD.col, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc0 : (c : ℕ) < X.p0
    · simp only [hc0, if_true]
    · rw [prFst_block_zero hc (by tauto), zero_mul, zero_mul]
  · simp only [ha, if_false]
    rw [Matrix.mul_inv_rev, ← mulVec_mulVec]
    change ∑ c, b⁻¹ a c * _ = _
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc0 : (c : ℕ) < X.p0
    · rw [prFst_block_zero hc' (by tauto), zero_mul, zero_mul]
    · simp only [hc0, if_false]

theorem sgnM_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    sgnM X = (2 : ℂ) • prFst r X.p0 - 1 := by
  ext a c
  by_cases h : a = c
  · subst h
    simp only [sgnM, prFst, sgn, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq]
    split_ifs <;> norm_num
  · simp [sgnM, prFst, h]

theorem block_of_inv {r : ℕ} (P x k s : Matrix (Fin r) (Fin r) ℂ) (hx : IsUnit x.det)
    (h1 : s * x = -(x * ((2 : ℂ) • P - 1))) (h2 : s * (k * x) = -(k * x * ((2 : ℂ) • P - 1))) :
    (x⁻¹ * (k * x)) * P = P * (x⁻¹ * (k * x)) ∧
      ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det = (P * (x⁻¹ * (k * x)) + (1 - P)).det ∧
      ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det = ((1 - P) * (x⁻¹ * (k * x)) + P).det := by
  have i1 : x * x⁻¹ = 1 := mul_nonsing_inv _ hx
  have i2 : x⁻¹ * x = 1 := nonsing_inv_mul _ hx
  generalize x⁻¹ = y at i1 i2 ⊢
  have i2' : ∀ z : Matrix (Fin r) (Fin r) ℂ, y * (x * z) = z := fun z => by rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have hs : s = 1 - (2 : ℂ) • (x * (P * y)) := by
    calc s = s * x * y := by rw [Matrix.mul_assoc, i1, Matrix.mul_one]
      _ = _ := by
        rw [h1]
        simp only [Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.mul_assoc, i1, neg_sub]
  have hconj : ∀ A : Matrix (Fin r) (Fin r) ℂ, A.det = (y * (A * x)).det := by
    intro A
    rw [det_mul, det_mul, mul_comm A.det, ← mul_assoc, ← det_mul, i2, det_one, one_mul]
  have a1 : (1 / 2 : ℂ) • (1 - s) = x * (P * y) := by rw [hs]; module
  have a2 : (1 / 2 : ℂ) • (1 + s) = 1 - x * (P * y) := by rw [hs]; module
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun z => y * z) h2
    simp only [hs, Matrix.mul_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', neg_sub, sub_right_inj] at this
    simpa only [Matrix.mul_assoc] using (smul_right_injective _ (two_ne_zero (α := ℂ)) this).symm
  · rw [a1, a2, hconj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', i2]
  · rw [a1, a2, hconj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', i2]

theorem reads_two_frames : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x x' : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsONFr X x' → IsInvOf W hr X x s → IsInvOf W hr X x' s → ∀ k : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → mat x' τ = Matrix.reindex (finCongr hr) (finCongr hr) (k ρ) * mat x τ) → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f ((∏ ρ, (((1 / 2 : ℂ) • (1 - s ρ) * k ρ + (1 / 2 : ℂ) • (1 + s ρ)).det / ((1 / 2 : ℂ) • (1 + s ρ) * k ρ + (1 / 2 : ℂ) • (1 - s ρ)).det) ^ (V.rank / 2)) • φ) x' := by
  intro D ψ θ V W r g hr X bas idx _ _ _ _ hmod _ x x' s hx hx' hs hs' k hk f φ hf
  subst hr
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))
  let t : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hmod.psi _).2 ⟨ρ, rfl⟩⟩
  have ht : Function.Bijective t := ⟨fun a b h => hinj (congrArg Subtype.val h), fun τ => by
    obtain ⟨ρ, h⟩ := (hmod.psi τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext h.symm⟩⟩
  have hu := isUnit_det_of_isONFr X x hx
  have hu' := isUnit_det_of_isONFr X x' hx'
  let b : X.Ψ → Matrix (Fin W.rank) (Fin W.rank) ℂ := fun τ => (mat x τ)⁻¹ * mat x' τ
  have hb : ∀ τ, IsUnit (b τ).det := fun τ => by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (hu τ)).mul (hu' τ)
  have hxb : ∀ τ, mat x' τ = mat x τ * b τ := fun τ => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  set P := prFst W.rank X.p0 with hP
  have key : ∀ ρ, b (t ρ) * P = P * b (t ρ) ∧
      ((1 / 2 : ℂ) • (1 - s ρ) * k ρ + (1 / 2 : ℂ) • (1 + s ρ)).det = (P * b (t ρ) + (1 - P)).det ∧
      ((1 / 2 : ℂ) • (1 + s ρ) * k ρ + (1 / 2 : ℂ) • (1 - s ρ)).det = ((1 - P) * b (t ρ) + P).det := by
    intro ρ
    have e0 : mat x' (t ρ) = k ρ * mat x (t ρ) := hk ρ (t ρ) rfl
    have e1 : s ρ * mat x (t ρ) = -(mat x (t ρ) * sgnM X) := hs ρ (t ρ) rfl
    have e2 : s ρ * mat x' (t ρ) = -(mat x' (t ρ) * sgnM X) := hs' ρ (t ρ) rfl
    rw [sgnM_eq] at e1 e2
    rw [e0] at e2
    have := block_of_inv P _ _ _ (hu _) e1 e2
    rw [← e0] at this
    exact this
  have hc : ∀ τ, b τ * P = P * b τ := fun τ => by
    obtain ⟨ρ, rfl⟩ := ht.2 τ
    exact (key ρ).1
  let N : X.Ψ → Matrix (Fin W.rank) (Fin W.rank) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin W.rank × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := reads_of_perC θ V W rfl X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin W.rank × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
        rw [← e.sum_comp]
        rfl
      rw [h1, Fintype.sum_prod_type]
      refine (perC_block X x x' (idx j).1 (b _) (hb _) (hxb _) (hc _) u (idx j).2).trans ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (idx j).1]
      · exact congrArg (· * _) (blockDiagonal_apply_eq N (idx j).2 c (idx j).1).symm
      · intro τ _ hτ
        have : blockDiagonal N (e j) (c, τ) = 0 := blockDiagonal_apply_ne N (idx j).2 c hτ.symm
        rw [this, zero_mul]
      · simp) f φ hf
  convert main using 2
  rw [hdet, Finset.prod_pow, ← ht.prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [(hN _).2, (key ρ).2.1, (key ρ).2.2]

end

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitEntriesMatrixInverseClosedProof
open GlobalTheory.IsoTriv

namespace GlobalTheory.LimInv

variable {R V : Type} [CommRing R] [CommRing V]

def limSub (φ : R →+* V) (q : R) : Subring V where
  carrier := {t | ∀ N : ℕ, ∃ a z, φ a = t + φ q ^ N * z}
  mul_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    refine ⟨a * b, z * t + s * w + φ q ^ N * z * w, ?_⟩
    rw [map_mul, ha, hb]; ring
  one_mem' := fun N => ⟨1, 0, by simp⟩
  add_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    exact ⟨a + b, z + w, by rw [map_add (f := _), ha, hb]; ring⟩
  zero_mem' := fun N => ⟨0, 0, by simp⟩
  neg_mem' := by
    intro s hs N
    obtain ⟨a, z, ha⟩ := hs N
    exact ⟨-a, -z, by rw [map_neg, ha]; ring⟩

theorem inv_mem_limSub [IsDedekindDomain R] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R) (hq0 : φ q ≠ 0) (hqu : ¬ IsUnit (φ q)) (u : Vˣ)
    (hu : (u : V) ∈ limSub φ q) : ((u⁻¹ : Vˣ) : V) ∈ limSub φ q := by
  intro N
  obtain ⟨a, z, ha⟩ := hu (N + 1)
  have hqm : φ q ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hqu
  have haU : IsUnit (φ a) := by
    by_contra h
    have h1 : φ a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 : φ q ^ (N + 1) * z ∈ IsLocalRing.maximalIdeal V :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hqm _ (Nat.succ_pos N))
    have h3 : (u : V) ∈ IsLocalRing.maximalIdeal V := by
      have : (u : V) = φ a - φ q ^ (N + 1) * z := by rw [ha]; ring
      rw [this]; exact Ideal.sub_mem _ h1 h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 h3) u.isUnit
  set w : Ideal R := (IsLocalRing.maximalIdeal V).comap φ with hw
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hqw : q ∈ w := hqm
  have hwne : w ≠ ⊥ := by
    intro h
    have : q = 0 := by rw [h] at hqw; exact (Submodule.mem_bot R).1 hqw
    exact hq0 (by rw [this, map_zero])
  have hwm : w.IsMaximal := hwp.isMaximal hwne
  have haw : a ∉ w := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) haU
  obtain ⟨y, i, hiw, hyi⟩ := hwm.exists_inv haw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (pow_ne_zero N hq0) hϖ
  have hiV : φ i ∈ Ideal.span {ϖ} := by rw [← hϖ.maximalIdeal_eq]; exact hiw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hiV
  let b : R := y * ∑ j ∈ Finset.range n, i ^ j
  have hab : φ a * φ b = 1 - φ q ^ N * ((e⁻¹ : Vˣ) * c ^ n) := by
    have h1 : a * b = 1 - i ^ n := by
      have : a * y = 1 - i := by linear_combination hyi
      calc a * b = (a * y) * ∑ j ∈ Finset.range n, i ^ j := by ring
        _ = 1 - i ^ n := by rw [this, mul_neg_geom_sum]
    have h2 : φ a * φ b = 1 - φ i ^ n := by rw [← map_mul, h1, map_sub, map_one, map_pow]
    rw [h2, he, ← hc, mul_pow]
    have : ((e : V) * (e⁻¹ : Vˣ)) = 1 := Units.mul_inv e
    linear_combination (c ^ n * ϖ ^ n) * this
  refine ⟨b, -((u⁻¹ : Vˣ) : V) * ((e⁻¹ : Vˣ) * c ^ n) - ((u⁻¹ : Vˣ) : V) * φ q * z * φ b, ?_⟩
  have hu1 : (u : V) * ((u⁻¹ : Vˣ) : V) = 1 := Units.mul_inv u
  linear_combination ((u⁻¹ : Vˣ) : V) * hab - (((u⁻¹ : Vˣ) : V) * φ b) * ha - φ b * hu1

end GlobalTheory.LimInv

open GlobalTheory.LimInv in
theorem GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof : InvSt := by
  intro R V _ _ _ _ _ φ q hq0 hqu n M hdet hM
  classical
  let S := limSub φ q
  let M₀ : Matrix (Fin n) (Fin n) S := fun b b' => ⟨M b b', fun N => hM b b' N⟩
  have hMM : S.subtype.mapMatrix M₀ = M := by ext b b'; rfl
  have hadj : ∀ b b', M.adjugate b b' ∈ S := by
    intro b b'
    rw [← hMM, ← RingHom.map_adjugate]
    exact (M₀.adjugate b b').2
  have hdetS : M.det ∈ S := by
    rw [← hMM, ← RingHom.map_det]; exact (M₀.det).2
  set u := hdet.unit with hu
  have huS : (u : V) ∈ S := by rw [hu, IsUnit.unit_spec]; exact hdetS
  have hinv := inv_mem_limSub φ q hq0 hqu u huS
  refine ⟨((u⁻¹ : Vˣ) : V) • M.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    have : ((u⁻¹ : Vˣ) : V) * M.det = 1 := by
      rw [show M.det = (u : V) by rw [hu, IsUnit.unit_spec]]; exact Units.inv_mul u
    rw [this, one_smul]
  · intro b b' N
    have : (((u⁻¹ : Vˣ) : V) • M.adjugate) b b' ∈ S := by
      rw [Matrix.smul_apply, smul_eq_mul]; exact S.mul_mem hinv (hadj b b')
    exact this N
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.Incl

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem subst_expAlong {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin d → C)
    (A : κ → Matrix (Fin d) (Fin d) C) (t : κ → C) (hA : ∀ b a, (A b).mulVec (u b a) = t b • u b a) (i : Fin d) :
    subst (expAlong (fun _ : κ => G) u)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C))) i) =
      subst (fun e : Fin d => ∑ ℓ : (Σ b, ι b), (t ℓ.1 * u ℓ.1 ℓ.2 e) • (X ℓ : MvPowerSeries (Σ b, ι b) C))
        (expOf G i) := by
  have hu : ∀ (b : κ) (e : Fin d),
      constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have hE : ∀ (b : κ), (fun e : Fin d => expAlong (fun _ : κ => G) u ⟨b, e⟩) =
      expPt G (fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b => rfl
  have hs : HasSubst (expAlong (fun _ : κ => G) u) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hu q.1) q.2
  have hX : ∀ (b : κ) (e : Fin d), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C) = 0 := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_expPt G hs (fun e => by
    rw [Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun b _ => cc_mv _ (cc_lgPt G (hX b)) e)]
  unfold expPt
  congr 1
  funext e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, ← coe_substAlgHom hs, map_sum, coe_substAlgHom, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv hs]
  have h1 : (fun e' => subst (expAlong (fun _ : κ => G) u)
      (lgPt G (fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C)) e')) =
      fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
    funext e'
    rw [subst_lgPt G hs (hX b)]
    simp only [subst_X hs]
    rw [hE b, lgPt_expPt G (hu b)]
  rw [h1]
  simp only [mv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact congrFun (hA b a) e

theorem isotropic_blocks {O : Type} [CommRing O] [StarRing O] (I : Ideal O) {φ : Type} {r m : φ → ℕ} {n : ℕ}
    (blk : (Σ f : φ, Fin (m f)) ↪ Fin n) (ε : φ → O) (x : ∀ f, Fin (r f) → Fin n → O)
    (h0 : ∀ f b j, j ∉ Set.range (fun j => blk ⟨f, j⟩) → x f b j = 0)
    (hiso : ∀ f b b', ∑ j, x f b j * star (x f b' j) ∈ I) (b b' : Σ f, Fin (r f)) :
    ∑ j, star (ε b.1 * x b.1 b.2 j) * (ε b'.1 * x b'.1 b'.2 j) ∈ I := by
  obtain ⟨f, β⟩ := b
  obtain ⟨f', β'⟩ := b'
  by_cases hf : f = f'
  · subst hf
    have e : ∑ j, star (ε f * x f β j) * (ε f * x f β' j) =
        (star (ε f) * ε f) * ∑ j, x f β' j * star (x f β j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]; ring
    rw [e]
    exact I.mul_mem_left _ (hiso f β' β)
  · refine Ideal.sum_mem _ fun j _ => ?_
    by_cases h1 : j ∈ Set.range (fun j => blk ⟨f, j⟩)
    · by_cases h2 : j ∈ Set.range (fun j => blk ⟨f', j⟩)
      · obtain ⟨j1, h1⟩ := h1
        obtain ⟨j2, h2⟩ := h2
        exact absurd (congrArg Sigma.fst (blk.injective (h1.trans h2.symm))) hf
      · simp [h0 f' β' j h2]
    · simp [h0 f β j h1]

theorem inclSt_of_lim (hAct : LimActSt) (hPt : LimPtSt) (hFr : LimFrameSt) : InclSt := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ Y cx n B hB
  obtain ⟨blk, hblk⟩ := hB
  choose x hx0 hxB hxiso using fun (f : {f : Lt1 Dw // cx f ≠ 0}) (N : ℕ) => (hblk f).2.2 N
  choose ε hε using fun τ : E →+* ℂ => hAct E H Dw l Xo c hstar T io y Ch p Y τ
  choose A hAapp hAlie using fun (b : Col cx) (j : Fin n) =>
    hε b.1.1.1 (B b.1.1 b.2 j) (fun N => x b.1 N b.2 j) (fun N => hxB b.1 N b.2 j)
  letI := io.toAlgebra
  letI : Algebra T.Fr Y.C := Y.ιF.toAlgebra
  have hw : ∀ b : Col cx, IntLog (fglOf (isIntFB_chart Ch Y)) (lgPt (fgl Ch Y)
      fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) Y.C)) :=
    fun b => intLog_lgPt_X (fgl Ch Y) (fun e => (⟨b, e⟩ : Σ _ : Col cx, Fin (chD Ch.ch)))
  have hint := fun j : Fin n => hPt Y.C (vX_vp Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (Col cx) _ hw
    (fun b => A b j) (fun N b => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b => hAapp b j N)
  refine ⟨fun q => expPt (fgl Ch Y) (∑ b, mv (A b q.1) (lgPt (fgl Ch Y) fun e => X ⟨b, e⟩)) q.2,
    fun q => cc_expPt _ (hint q.1).1 q.2, fun q => (hint q.1).2 q.2, fun q => ?_, ?_⟩
  · exact subst_expAlong (fgl Ch Y) (fun b : Col cx => frame Ch Y b.1.1) (fun b => A b q.1)
      (fun b => jX Y (B b.1.1 b.2 q.1)) (fun b a => hAlie b q.1 _) q.2
  · exact hFr Y.C (vX_vp Y) p (vX_vp_p Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (gauge_chart Ch Y) _ (Col cx) _
      hw H.w0 n A (fun N b j => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b j => hAapp b j N)
      (fun N => isotropic_blocks _ blk (fun f => ε f.1.1 N) (fun f => x f N) (fun f => hx0 f N)
        (fun f b b' => by simpa only [hstar] using hxiso f N b b'))

end GlobalTheory.IsoTriv.Incl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitStepsStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

section Units

variable {X : Scheme.{0}} [IsIntegral X]

def UnitAt (x : X) (t : X.functionField) : Prop :=
  ∃ u : (X.presheaf.stalk x)ˣ, algebraMap _ X.functionField (u : X.presheaf.stalk x) = t

theorem UnitAt.mul {x : X} {s t : X.functionField} (hs : UnitAt x s) (ht : UnitAt x t) : UnitAt x (s * t) := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := ht
  exact ⟨u * v, by rw [Units.val_mul, map_mul]⟩

theorem UnitAt.inv {x : X} {s : X.functionField} (hs : UnitAt x s) : UnitAt x s⁻¹ := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u⁻¹, by rw [map_units_inv]⟩

theorem UnitAt.ne_zero {x : X} {s : X.functionField} (hs : UnitAt x s) : s ≠ 0 := by
  obtain ⟨u, rfl⟩ := hs
  exact (u.isUnit.map _).ne_zero

theorem isOpen_unitAt (t : X.functionField) : IsOpen {x : X | UnitAt x t} := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro x ⟨u, hu⟩
  obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk x)
  refine ⟨X.basicOpen s, fun y hy => ?_, (X.basicOpen s).isOpen,
    (X.mem_basicOpen s x hV).2 (by rw [hs]; exact u.isUnit)⟩
  have hyV := X.basicOpen_le s hy
  refine ⟨((X.mem_basicOpen s y hyV).1 hy).unit, ?_⟩
  rw [← hu, ← hs, IsUnit.unit_spec]
  exact (X.presheaf.germ_stalkSpecializes_apply hyV _ _).trans
    (X.presheaf.germ_stalkSpecializes_apply hV _ _).symm

theorem exists_unit_eq [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (V : X.Opens) [Nonempty V]
    (t : X.functionField) (h0 : t ≠ 0) (h : ∀ x ∈ V, Order.coheight x = 1 → UnitAt x t) :
    ∃ u : Γ(X, V)ˣ, X.germToFunctionField V u = t := by
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t fun x hx h1 =>
    let ⟨u, hu⟩ := h x hx h1; ⟨u, hu⟩
  obtain ⟨s', hs'⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t⁻¹ fun x hx h1 =>
    let ⟨u, hu⟩ := (h x hx h1).inv; ⟨u, hu⟩
  have : IsUnit s := IsUnit.of_mul_eq_one s' (X.germToFunctionField_injective V (by
    rw [map_mul, hs, hs', map_one, mul_inv_cancel₀ h0]))
  exact ⟨this.unit, hs⟩

end Units

theorem constFn_top {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp A) (a : A) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a = q.appTop ((Scheme.ΓSpecIso (.of A)).inv a) :=
  congrArg (fun m : Γ(Sp A, ⊤) ⟶ Γ(X, ⊤) => m ((Scheme.ΓSpecIso (.of A)).inv a)) (q.appLE_eq_app (U := ⊤))

theorem app_constFn {A C : Type} [CommRing A] [CommRing C] {g : A →+* C} {X Y : Scheme.{0}} {q : X ⟶ Sp A}
    {p : Y ⟶ Sp C} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (a : A) :
    φ.app ⊤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p ⊤ (g a) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp A ↦ φ.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) w
  have h₂ := congrArg (fun φ : CommRingCat.of A ⟶ Γ(Spec (.of C), ⊤) ↦ φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [constFn_top, constFn_top]
  exact h₁.trans (congrArg p.appTop h₂.symm)

section Transport

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) (hφ : φ (genericPoint Y) ⤳ genericPoint X)

noncomputable def ffMap : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes hφ ≫ φ.stalkMap (genericPoint Y)

theorem ffMap_germ (V : X.Opens) [Nonempty V] (W : Y.Opens) [Nonempty W] (h : W ≤ φ ⁻¹ᵁ V) (s : Γ(X, V)) :
    ffMap φ hφ (X.germToFunctionField V s) = Y.germToFunctionField W (φ.appLE V W h s) := by
  refine (congrArg (φ.stalkMap _) (X.presheaf.germ_stalkSpecializes_apply _ hφ s)).trans
    ((φ.germ_stalkMap_apply V _ _ s).trans ?_)
  exact (Y.presheaf.germ_res_apply (homOfLE h) _ _ _).symm

variable [∀ y, IsIso (φ.stalkMap y)]

theorem ffMap_bijective : Function.Bijective (ffMap φ hφ) := by
  have : IsIso (X.presheaf.stalkSpecializes hφ) :=
    (X.presheaf.stalkCongr ((genericPoint_specializes _).antisymm hφ)).isIso_hom
  have : IsIso (ffMap φ hφ) := by unfold ffMap; infer_instance
  exact ConcreteCategory.bijective_of_isIso _

theorem unitAt_of_isUnit {W : Y.Opens} [Nonempty W] {τ : Γ(Y, W)} (hτ : IsUnit τ) {y : Y} (hy : y ∈ W)
    {t : X.functionField} (ht : ffMap φ hφ t = Y.germToFunctionField W τ) : UnitAt (φ y) t := by
  obtain ⟨σ, hσ⟩ := (ConcreteCategory.bijective_of_isIso (φ.stalkMap y)).2 (Y.presheaf.germ W y hy τ)
  have hu : IsUnit σ := (isUnit_map_iff (φ.stalkMap y).hom σ).1 (by
    rw [hσ]; exact hτ.map _)
  refine ⟨hu.unit, (ffMap_bijective φ hφ).1 ?_⟩
  rw [ht, IsUnit.unit_spec]
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq σ
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : Nonempty (φ ⁻¹ᵁ V) := ⟨⟨y, hV⟩⟩
  refine (congrArg (ffMap φ hφ) (X.presheaf.germ_stalkSpecializes_apply hV _ s)).trans
    ((ffMap_germ φ hφ V (φ ⁻¹ᵁ V) le_rfl s).trans ?_)
  rw [φ.germ_stalkMap_apply] at hσ
  rw [φ.appLE_eq_app]
  have := congrArg (Y.presheaf.stalkSpecializes (genericPoint_specializes y)) hσ
  rwa [Y.presheaf.germ_stalkSpecializes_apply, Y.presheaf.germ_stalkSpecializes_apply] at this

end Transport

open MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.VerticalUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.CoeffCont

open MvPowerSeries

theorem coe_le_add {a b : WithTop ℝ} {x y : ℝ} (ha : (x : WithTop ℝ) ≤ a) (hb : (y : WithTop ℝ) ≤ b) :
    ((x + y : ℝ) : WithTop ℝ) ≤ a + b := by
  rw [WithTop.coe_add]; exact add_le_add ha hb

theorem poly_bound {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {κ : Type} (Q : MvPolynomial κ C) :
    ∃ K : ℝ, ∀ (N : ℝ) (s s' : κ → C), (∀ k, (0 : WithTop ℝ) ≤ v (s k)) → (∀ k, (0 : WithTop ℝ) ≤ v (s' k)) →
      (∀ k, ((N : ℝ) : WithTop ℝ) ≤ v (s k - s' k)) →
      ((N - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q - MvPolynomial.eval s' Q) ∧
      ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i c
    by_cases ht : v c = ⊤
    · refine ⟨0, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ht, le_top, and_self]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
      refine ⟨-r, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ← hr, le_top, neg_neg, le_refl, and_self]
  · rename_i p q hp hq
    obtain ⟨K₁, h₁⟩ := hp
    obtain ⟨K₂, h₂⟩ := hq
    refine ⟨max K₁ K₂, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a₁, b₁⟩ := h₁ N s s' hs hs' hss
    obtain ⟨a₂, b₂⟩ := h₂ N s s' hs hs' hss
    rw [map_add (MvPolynomial.eval s), map_add (MvPolynomial.eval s')]
    constructor
    · have e : MvPolynomial.eval s p + MvPolynomial.eval s q - (MvPolynomial.eval s' p + MvPolynomial.eval s' q) =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) + (MvPolynomial.eval s q - MvPolynomial.eval s' q) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) a₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) a₂
    · refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) b₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) b₂
  · rename_i p k hp
    obtain ⟨K, h⟩ := hp
    refine ⟨K, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a, b⟩ := h N s s' hs hs' hss
    rw [map_mul (MvPolynomial.eval s), map_mul (MvPolynomial.eval s'), MvPolynomial.eval_X, MvPolynomial.eval_X]
    constructor
    · have e : MvPolynomial.eval s p * s k - MvPolynomial.eval s' p * s' k =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) * s k + MvPolynomial.eval s' p * (s k - s' k) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · rw [v.map_mul]
        have := coe_le_add (y := 0) a (hs k)
        rwa [add_zero] at this
      · rw [v.map_mul]
        have := coe_le_add (h N s' s' hs' hs' (fun k => by rw [sub_self, v.map_zero]; exact le_top)).2 (hss k)
        have e2 : (-K + N : ℝ) = N - K := by ring
        rw [e2] at this
        exact this
    · rw [v.map_mul]
      have := coe_le_add (y := 0) b (hs k)
      rwa [add_zero] at this

theorem coeff_subst_eq_eval {C : Type} [Field C] {τ σ ι : Type} [Fintype τ] [Fintype ι]
    (W : MvPowerSeries τ C) (g : ι → MvPowerSeries σ C) (hg : ∀ i, constantCoeff (g i) = 0) (α : σ →₀ ℕ) :
    ∃ Q : MvPolynomial (τ × ι) C, ∀ s : τ → ι → C,
      coeff α (subst (fun q => ∑ i, s q i • g i) W : MvPowerSeries σ C) =
        MvPolynomial.eval (fun x => s x.1 x.2) Q := by
  classical
  let G : ι → MvPowerSeries σ (MvPolynomial (τ × ι) C) := fun i => (g i).map MvPolynomial.C
  let a : τ → MvPowerSeries σ (MvPolynomial (τ × ι) C) :=
    fun q => ∑ i, (MvPolynomial.X (q, i) : MvPolynomial (τ × ι) C) • G i
  have hG : ∀ i, constantCoeff (G i) = 0 := fun i => by simp [G, hg]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun q => by simp [a, hG])
  refine ⟨coeff α (subst a (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)) :
    MvPowerSeries σ (MvPolynomial (τ × ι) C)), fun s => ?_⟩
  have h1 := congrArg (coeff α) (map_subst ha (h := MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))
    (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)))
  rw [coeff_map] at h1
  have hW : (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)).map
      (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2)) = W := by
    ext n; simp [coeff_map]
  have hA : (fun q => (a q).map (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))) =
      fun q => ∑ i, s q i • g i := by
    funext q; ext n; simp [a, G, coeff_map, map_sum]
  rw [h1, hW, hA]

end GlobalTheory.IsoTriv.CoeffCont

namespace GlobalTheory.IsoTriv

open MvPowerSeries

theorem contSt_holds : ContSt := by
  intro C _ v τ σ ι _ _ _ W g hg α
  obtain ⟨Q, hQ⟩ := CoeffCont.coeff_subst_eq_eval W g hg α
  obtain ⟨K, hK⟩ := CoeffCont.poly_bound v Q
  refine ⟨⌈K⌉₊, fun s s' hs hs' hss => ?_⟩
  rw [hQ, hQ]
  have h := (hK (⌈K⌉₊ : ℝ) (fun x => s x.1 x.2) (fun x => s' x.1 x.2) (fun x => hs _ _) (fun x => hs' _ _)
    (fun x => hss _ _)).1
  show (0 : WithTop ℝ) ≤ _
  refine le_trans ?_ h
  rw [← WithTop.coe_zero, WithTop.coe_le_coe]
  linarith [Nat.le_ceil K]

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProofStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof : ContSt := by
  first | exact @GlobalTheory.IsoTriv.contSt_holds | exact GlobalTheory.IsoTriv.contSt_holds | (intros; apply GlobalTheory.IsoTriv.contSt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfSteps
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem subst_comb_expPt {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : κ → Fin d → MvPowerSeries σ C) (hw : ∀ b i, constantCoeff (w b i) = 0)
    (F : MvPowerSeries (Fin n × Fin d) C) (M : κ → Fin n → Matrix (Fin d) (Fin d) C) :
    (subst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2)
      (subst (fun q : Fin n × Fin d => expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) F :
        MvPowerSeries (Fin n × Fin d) C) : MvPowerSeries σ C) =
      subst (fun q : Fin n × Fin d => expPt G (∑ b, mv (M b q.1) (w b)) q.2) F := by
  have ht : HasSubst (fun q : Fin n × Fin d => ∑ i : κ × Fin d, M i.1 q.1 q.2 i.2 • w i.1 i.2) :=
    hasSubst_of_constantCoeff_zero (by intro q; simp [hw])
  have hs : HasSubst (fun q : Fin n × Fin d =>
      expPt G (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2) :=
    hasSubst_of_constantCoeff_zero (fun q => cc_expPt G (by simp) q.2)
  refine (subst_comp_subst_apply hs ht F).trans ?_
  congr 1
  funext q
  refine (subst_expPt G ht (by simp) q.2).trans ?_
  congr 1
  funext e
  refine (subst_X ht _).trans ?_
  simp [mv, Fintype.sum_prod_type, Finset.sum_apply]

theorem le_v_pow_mul_int {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {p : ℕ} (hp : v (p : C) = 1)
    (N : ℕ) (z : ℤ) : ((N : ℝ) : WithTop ℝ) ≤ v ((((p : ℤ) ^ N * z : ℤ)) : C) := by
  have hz : 0 ≤ v (z : C) := intCast_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v) z
  push_cast
  rw [v.map_mul, v.map_pow, hp]
  calc ((N : ℕ) : WithTop ℝ) = N • (1 : WithTop ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_right hz

theorem limFrame : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  classical
  intro _ hAct hUnit hBi hFr hFin hCont C _ _ v p hp d R _ _ O _ _ _ B hB h hh σ _ κ _ w hw w0 n A a hA hiso α
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have mono : ∀ {M N : ℕ} {x : WithTop ℝ}, M ≤ N → ((N : ℝ) : WithTop ℝ) ≤ x → ((M : ℝ) : WithTop ℝ) ≤ x :=
    fun hMN hx => le_trans (WithTop.coe_le_coe.2 (Nat.cast_le.2 hMN)) hx
  have zle : ∀ {N : ℕ} {x : C}, ((N : ℝ) : WithTop ℝ) ≤ v x → IsIntV v x := fun hx => by
    have := mono (Nat.zero_le _) hx
    simpa [IsIntV] using this
  have hD : ∀ (x : O) i j, IsIntV v (dAct C B x i j) := fun x i j => hB.2.1 x i _
  have hAi : ∀ b j e e', IsIntV v (A b j e e') := fun b j e e' => by
    have := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem (zle (hA 0 b j e e')) (hD (a 0 b j) e e')
    rw [sub_add_cancel] at this
    exact this
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  let g : κ × κ × Fin m → MvPowerSeries σ C := fun i =>
    pairSer (fglOf hB) h (w i.1) (mv (dAct C B (e i.2.2)) (w i.2.1))
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i =>
    (hBi C v d R O B hB h hh σ (w i.1) (w i.1) _ (hw _) (hw _)
      ((hAct C v d R O B hB σ (e i.2.2)).2 _ (hw i.2.1))).1
  obtain ⟨N₀, hN₀⟩ := hCont C v (Fin n × Fin d) σ (κ × Fin d)
    (subst (fun q : Fin n × Fin d => expPt (fglOf hB) (fun e => (X (q.1, e) : MvPowerSeries (Fin n × Fin d) C)) q.2)
      (frameSer B h w0 n)) (fun i => w i.1 i.2) (fun i => hw0 _ _) α
  choose N₁ hN₁ using fun γ => hCont C v Unit σ (κ × κ × Fin m) (PowerSeries.exp C) g hg0 γ
  obtain ⟨N, hN0, hN1⟩ : ∃ N : ℕ, N₀ ≤ N ∧ ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, N₁ x.2 ≤ N :=
    ⟨max N₀ ((Finset.HasAntidiagonal.antidiagonal α).sup fun x => N₁ x.2), le_max_left _ _,
      fun x hx => le_trans (Finset.le_sup (f := fun x => N₁ x.2) hx) (le_max_right _ _)⟩
  have hdec : ∀ b b', ∃ nn : Fin m → ℤ,
      (∑ j, star (a N b j) * a N b' j) * w0 = ∑ i, ((p : ℤ) ^ N * nn i) • e i := fun b b' => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hiso N b b')
    obtain ⟨nn, hnn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := e) (x := c * w0)).1
      (by rw [he]; exact Submodule.mem_top)
    refine ⟨nn, ?_⟩
    rw [hc, mul_assoc, ← hnn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_assoc]
  choose nn hnn using hdec
  have hU := hFin C v d R O B hB h hh σ κ w hw w0 n (a N) (Fin m) e (fun b b' i => (p : ℤ) ^ N * nn b b' i) hnn
  have hF := (hFr C v d R O B hB h hh w0 n).2.2 σ (fun j => ∑ b, mv (dAct C B (a N b j)) (w b))
    (fun j i => by simp [Finset.sum_apply, mv, hw0])
  let s : κ × κ × Fin m → C := fun i => (((p : ℤ) ^ N * nn i.1 i.2.1 i.2.2 : ℤ) : C)
  have hT : ∑ b, ∑ b', ∑ i, (((p : ℤ) ^ N * nn b b' i : ℤ) : C) •
      pairSer (fglOf hB) h (w b) (mv (dAct C B (e i)) (w b')) = ∑ i, s i • g i := by
    simp only [Fintype.sum_prod_type, s, g]
  rw [hT] at hU
  have hT0 : constantCoeff (∑ i, s i • g i) = 0 := by simp [hg0]
  obtain ⟨hz, -, -, hmul, -⟩ := hUnit C v σ
  have hprod := hmul _ _ hU.1 hT0
  rw [sub_add_cancel, ← hF] at hprod
  have h1 := hN₀ (fun q i => A i.1 q.1 q.2 i.2) (fun q i => dAct C B (a N i.1 q.1) q.2 i.2)
    (fun q i => hAi _ _ _ _) (fun q i => hD _ _ _) (fun q i => mono hN0 (hA N _ _ _ _))
  rw [subst_comb_expPt (fglOf hB) w hw0 _ A,
    subst_comb_expPt (fglOf hB) w hw0 _ (fun b j => dAct C B (a N b j)), hprod] at h1
  have h2 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α,
      IsIntV v (coeff x.2 (PowerSeries.subst (∑ i, s i • g i) (PowerSeries.exp C))) := fun x hx => by
    have h3 := hN₁ x.2 (fun _ => s) (fun _ _ => 0) (fun _ i => zle (le_v_pow_mul_int hp N _))
      (fun _ _ => by simp [IsIntV]) (fun _ i => by
        rw [sub_zero]; exact mono (hN1 x hx) (le_v_pow_mul_int hp N _))
    simp only [zero_smul, Finset.sum_const_zero] at h3
    have h4 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h3 (hz.2 x.2)
    have h5 : ∀ y z : C, y - z + z ∈ ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v → IsIntV v y := fun y z hyz => by
      rw [sub_add_cancel] at hyz
      exact hyz
    exact h5 _ _ h4
  rw [coeff_mul] at h1
  have h6 := (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).add_mem h1
    ((ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).sum_mem fun x hx =>
      (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSub v).mul_mem (hU.2 x.1) (h2 x hx))
  rw [sub_add_cancel] at h6
  exact h6

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfStepsStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitIsotropicFrameIntegral_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  first | exact @GlobalTheory.IsoTriv.limFrame | exact GlobalTheory.IsoTriv.limFrame | (intros; apply GlobalTheory.IsoTriv.limFrame <;> assumption)
end
end

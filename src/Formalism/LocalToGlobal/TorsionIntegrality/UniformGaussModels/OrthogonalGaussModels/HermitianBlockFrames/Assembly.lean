module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

theorem bd4_mul_apply {R : Type*} [CommRing R] (P : Matrix n n R) (Q : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (a : Fin 4) (i : n) (w : Fin 4 × n) : (bd4 P * Q) (a, i) w = ∑ j, P i j * Q (a, j) w := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [bd4]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [bd4, Ne.symm hb]
  · simp

theorem bd4_mul {R : Type*} [CommRing R] (P Q : Matrix n n R) : bd4 P * bd4 Q = bd4 (P * Q) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [bd4_mul_apply]
  by_cases hab : a = b
  · subst hab
    simp [bd4, Matrix.mul_apply]
  · simp [bd4, hab]

theorem bd4_map {R S : Type*} [Zero R] [Zero S] (f : R → S) (hf : f 0 = 0) (P : Matrix n n R) :
    (bd4 P).map f = bd4 (P.map f) := by
  ext x y
  simp only [Matrix.map_apply, bd4]
  split_ifs
  · rfl
  · exact hf

theorem blockShift_map {R S : Type*} [Zero R] [One R] [Zero S] [One S] (f : R → S) (hf : f 0 = 0) (hf1 : f 1 = 1)
    (k : Fin 4) : (bmv0 (n := n) k : Matrix _ _ R).map f = bmv0 k := by
  ext x y
  simp only [Matrix.map_apply, bmv0]
  split_ifs
  · exact hf1
  · exact hf

end Blocks

theorem sq_sq (d : ℕ) : sq d ^ 2 = -(d : ℂ) := by
  show (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ)
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  ring

theorem lmat_coe {l : ℕ} [Fact l.Prime] {m m' : Type} (d : ℕ) (ι : ℂ ≃+* ℂ_[l]) (δ : MaximalUnramifiedExtension l)
    (hδ : (δ : ℂ_[l]) = ι (sq d)) (A B : Matrix m m' ℚ) :
    (lmat δ A B).map (MaximalUnramifiedExtension l).subtype = (kmat d A B).map ι := by
  ext x y
  simp only [lmat, kmat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_ratCast, hδ]
  simp
  exact Or.inl hδ

theorem hermFrame_of (hF : FrobStep) (hR : RatStep) (hL : LocCore) : Formalism.L2.Th1.Top.FrP.HermFrame := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm l _ hl hldK hsq ι σ hσ n _ _ h Λ g₀ g₁ hlat hiso hidx
  obtain ⟨P₀, M₁, M₂, R₁, R₂, c, hc, hg, hRR, hU⟩ :=
    hR a₀ b₀ c₀ dK ha hdK lam hlam hcm l hl hldK hsq n h Λ g₀ g₁ hlat hiso hidx
  obtain ⟨hnorm, δ, hδ, hσδ⟩ := hF l dK hl hldK hcm.2.2.2 hcm.2.2.1 hsq ι σ hσ
  have hδ2 : δ ^ 2 = -(dK : MaximalUnramifiedExtension l) := by
    apply Subtype.ext
    have e1 : ((δ ^ 2 : MaximalUnramifiedExtension l) : ℂ_[l]) = (δ : ℂ_[l]) ^ 2 := rfl
    have e2 : ((-(dK : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l]) = -(dK : ℂ_[l]) := by simp
    rw [e1, e2, hδ, ← map_pow, sq_sq, map_neg, map_natCast]
  have hmulι : ∀ {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ),
      (A * B).map ι = A.map ι * B.map ι := by
    intro p q r _ A B
    have : (A * B).map (ι : ℂ →+* ℂ_[l]) = A.map (ι : ℂ →+* ℂ_[l]) * B.map (ι : ℂ →+* ℂ_[l]) :=
      Matrix.map_mul
    simpa using this
  have hinj : ∀ {p q : Type}, Function.Injective
      (fun A : Matrix p q (MaximalUnramifiedExtension l) => A.map (MaximalUnramifiedExtension l).subtype) :=
    fun {p q} => Matrix.map_injective Subtype.val_injective
  have hLeq : (lmat δ M₁ M₂).transpose * bd4 (lmat δ R₁ R₂) * lmat δ M₁ (-M₂) =
      (c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) := by
    apply hinj
    have h1 := congrArg (fun A => A.map ι) hRR
    simp only [hmulι, Matrix.transpose_map, bd4_map ι (map_zero ι)] at h1
    simp only [Matrix.map_mul, Matrix.transpose_map, bd4_map (MaximalUnramifiedExtension l).subtype (map_zero _),
      lmat_coe dK ι δ hδ]
    rw [h1]
    ext x y
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [map_ratCast]
  have hUk : ∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
      (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
      bmv0 k * lmat δ M₁ M₂ = lmat δ M₁ M₂ * lmat δ U₁ U₂ := by
    intro k
    obtain ⟨U₁, U₂, hUn, hUe⟩ := hU k
    refine ⟨U₁, U₂, hUn, ?_⟩
    apply hinj
    have h1 := congrArg (fun A => A.map ι) hUe
    simp only [hmulι, blockShift_map ι (map_zero ι) (map_one ι)] at h1
    simp only [Matrix.map_mul, blockShift_map (MaximalUnramifiedExtension l).subtype (map_zero _) (map_one _),
      lmat_coe dK ι δ hδ]
    exact h1
  obtain ⟨T, Ti, hTTi, hUn⟩ := hL l dK σ δ hl hldK hsq hnorm hδ2 hσδ n M₁ M₂ R₁ R₂ c hc hLeq hUk
  refine ⟨bd4 Ti * lmat δ M₁ M₂, ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype), hUn, ?_⟩
  intro i' i w
  have hγ : (bd4 Ti * lmat δ M₁ M₂).map (MaximalUnramifiedExtension l).subtype =
      bd4 (Ti.map (MaximalUnramifiedExtension l).subtype) * (kmat dK M₁ M₂).map ι := by
    rw [Matrix.map_mul, bd4_map (MaximalUnramifiedExtension l).subtype (map_zero _), lmat_coe dK ι δ hδ]
  have hTT : T.map (MaximalUnramifiedExtension l).subtype * Ti.map (MaximalUnramifiedExtension l).subtype = 1 := by
    rw [← Matrix.map_mul, hTTi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hB : bd4 (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) * bd4 (Ti.map (MaximalUnramifiedExtension l).subtype) =
      bd4 (ι lam⁻¹ • P₀.map ι) := by
    rw [bd4_mul, Matrix.smul_mul, Matrix.mul_assoc, hTT, Matrix.mul_one]
  have hsm : ∀ (x : ℂ_[l]) (Q : Matrix n n ℂ_[l]), bd4 (x • Q) = x • bd4 Q := by
    intro x Q
    ext p q
    simp only [bd4, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hG : (gmat g₁).map ι = bd4 (ι lam⁻¹ • P₀.map ι) * (kmat dK M₁ M₂).map ι := by
    rw [hg, hsm, Matrix.smul_mul, ← bd4_map ι (map_zero ι), ← hmulι]
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  calc ∑ j, (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) i j *
        (((bd4 Ti * lmat δ M₁ M₂) (i', j) w : MaximalUnramifiedExtension l) : ℂ_[l])
      = (bd4 (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) *
          (bd4 Ti * lmat δ M₁ M₂).map (MaximalUnramifiedExtension l).subtype) (i', i) w := by
        rw [bd4_mul_apply]
        rfl
    _ = (gmat g₁).map ι (i', i) w := by
        rw [hγ, ← Matrix.mul_assoc, hB, hG]
    _ = ι (g₁.symm (Pi.single w 1) (i', i)) := rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.MemLatticeFourfoldOfMemDualLattice
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem im_mul_conj_lattice (L : PeriodPair) {z w : ℂ} (hz : z ∈ L.lattice) (hw : w ∈ L.lattice) :
    ∃ k : ℤ, (z * conj w).im = k * (L.ω₁ * conj L.ω₂).im := by
  have hz' : z ∈ Submodule.span ℤ {L.ω₁, L.ω₂} := hz
  have hw' : w ∈ Submodule.span ℤ {L.ω₁, L.ω₂} := hw
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz'
  obtain ⟨c, e, rfl⟩ := Submodule.mem_span_pair.mp hw'
  refine ⟨a * e - b * c, ?_⟩
  simp only [zsmul_eq_mul, map_add (f := _), map_mul, map_intCast, Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem im_div_area (L : PeriodPair) : ∃ e : ℤ, (L.ω₁ * conj L.ω₂).im / area L = e := by
  have h : (L.ω₁ * conj L.ω₂).im = -(conj L.ω₁ * L.ω₂).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h]
  unfold area
  rcases lt_trichotomy (conj L.ω₁ * L.ω₂).im 0 with ht | ht | ht
  · refine ⟨1, ?_⟩
    rw [abs_of_neg ht, div_self (neg_ne_zero.mpr ht.ne)]
    simp
  · exact ⟨0, by simp [ht]⟩
  · refine ⟨-1, ?_⟩
    rw [abs_of_pos ht, neg_div, div_self ht.ne']
    simp

theorem stdH_apply (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] (z w : N → ℂ) :
    stdH L N z w = ∑ i, z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i) := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem stdLat_int (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] {z w : N → ℂ}
    (hz : z ∈ stdLat L N) (hw : w ∈ stdLat L N) : ∃ k : ℤ, altE (stdH L N) z w = k := by
  have hzi : ∀ i, z i ∈ L.lattice := fun i =>
    (show ∀ i ∈ (Set.univ : Set N), z i ∈ L.lattice.toAddSubgroup from hz) i (Set.mem_univ i)
  have hwi : ∀ i, w i ∈ L.lattice := fun i =>
    (show ∀ i ∈ (Set.univ : Set N), w i ∈ L.lattice.toAddSubgroup from hw) i (Set.mem_univ i)
  choose k hk using fun i => im_mul_conj_lattice L (hzi i) (hwi i)
  obtain ⟨e, he⟩ := im_div_area L
  refine ⟨(∑ i, k i) * e, ?_⟩
  have hterm : ∀ i, (z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i)).im =
      (k i : ℝ) * ((L.ω₁ * conj L.ω₂).im / area L) := by
    intro i
    rw [show z i * ((area L : ℝ) : ℂ)⁻¹ * conj (w i) = (((area L)⁻¹ : ℝ) : ℂ) * (z i * conj (w i)) by
      push_cast; ring, Complex.im_ofReal_mul, hk i]
    ring
  unfold altE
  rw [stdH_apply, Complex.im_sum, Finset.sum_congr rfl (fun i _ => hterm i), he, ← Finset.sum_mul]
  push_cast
  ring

theorem idx_smul_mem {n : Type} [Fintype n] [DecidableEq n] (L : PeriodPair) (Λ : AddSubgroup (n → ℂ))
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) {y : Fin 4 × n → ℂ} (hy : y ∈ pow4 Λ) :
    relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • g₁ y
      ∈ stdLat L (Fin 4 × n) := by
  have hmem : g₁ y ∈ imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) :=
    AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have h1 := AddSubgroup.nsmul_index_mem ((stdLat L (Fin 4 × n)).addSubgroupOf
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) ⟨g₁ y, hmem⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  simpa [relIdx, AddSubgroup.relIndex] using h1

def emb {n : Type} (a : Fin 4) (v : n → ℂ) : Fin 4 × n → ℂ := fun x => if x.1 = a then v x.2 else 0

theorem emb_mem {n : Type} {Λ : AddSubgroup (n → ℂ)} (a : Fin 4) {v : n → ℂ} (hv : v ∈ Λ) :
    emb a v ∈ pow4 Λ := by
  intro b
  by_cases h : b = a
  · subst h
    convert hv using 1
    funext i
    simp [slice, emb]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, emb, h]

theorem matrixForm_diagBlocks_blockEmbed {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (x : Fin 4 × n → ℂ) (a : Fin 4)
    (v : n → ℂ) : matH (blk4 h) x (emb a v) = matH h (slice a x) v := by
  simp only [matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp [blk4, emb, slice]
    · intro c _ hc
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [emb, hc]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : c = a
    · subst hc
      simp [blk4, hb]
    · simp [emb, hc]
  · simp

theorem mem_latticeFourfold_of_mem_dualLattice {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hΛ : IsSelfDual (matH h) Λ) {x : Fin 4 × n → ℂ} (hx : x ∈ dualLat (matH (blk4 h)) (pow4 Λ)) :
    x ∈ pow4 Λ := by
  have hx' : ∀ y ∈ pow4 Λ, ∃ m : ℤ, altE (matH (blk4 h)) x y = (m : ℝ) := hx
  intro a
  rw [← hΛ]
  show ∀ y ∈ Λ, ∃ m : ℤ, altE (matH h) (slice a x) y = (m : ℝ)
  intro v hv
  obtain ⟨m, hm⟩ := hx' (emb a v) (emb_mem a hv)
  refine ⟨m, ?_⟩
  unfold altE at hm ⊢
  rw [matrixForm_diagBlocks_blockEmbed] at hm
  exact hm

theorem idx_smul_symm_mem {n : Type} [Fintype n] [DecidableEq n] (L : PeriodPair) (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ) (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    {z : Fin 4 × n → ℂ} (hz : z ∈ stdLat L (Fin 4 × n)) :
    g₁.symm (relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • z)
      ∈ pow4 Λ := by
  apply mem_latticeFourfold_of_mem_dualLattice h Λ hΛ
  show ∀ y ∈ pow4 Λ, ∃ m : ℤ, altE (matH (blk4 h)) (g₁.symm (relIdx (stdLat L (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) • z)) y = (m : ℝ)
  intro y hy
  obtain ⟨k, hk⟩ := stdLat_int L hz (idx_smul_mem L Λ g₁ hy)
  refine ⟨k, ?_⟩
  unfold altE at hk ⊢
  rw [← hIso]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_nsmul, LinearMap.smul_apply] at hk ⊢
  exact hk

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

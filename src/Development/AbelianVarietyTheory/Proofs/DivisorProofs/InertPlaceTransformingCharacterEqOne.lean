module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShifts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentBlockUnipotentIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Decomposition
open Matrix

namespace GlobalTheory.UnipotentCongruenceInverse

section Ring
variable {R M : Type} [CommRing R] [Ring M] [Algebra R M]

theorem cong_mul {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hy : (1 - e) • (y - 1) = 0) :
    (1 - e) • (x * y - 1) = 0 := by
  have h1 : x * y - 1 = (x - 1) * y + (y - 1) := by noncomm_ring
  rw [h1, smul_add, ← smul_mul_assoc, hx, zero_mul, zero_add, hy]

theorem cong_inv {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hxy : y * x = 1) :
    (1 - e) • (y - 1) = 0 := by
  have h1 : y - 1 = -(y * (x - 1)) := by rw [mul_sub, hxy, mul_one]; abel
  rw [h1, smul_neg, ← mul_smul_comm, hx, mul_zero, neg_zero]

theorem key {e : R} {k K h h' a b : M} (hKk : K * k = 1) (hh : h' * h = 1)
    (hK : (1 - e) • (K - 1) = 0) (hhe : (1 - e) • (h - 1) = 0)
    (ha : (1 - k) * a = e • (1 : M)) (hb : b * (1 - h') = e • (1 : M)) :
    (K - 1) * (1 - (b - a) * (h - 1)) = h - 1 := by

  have hu : e • (K - 1) = K - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hK; exact hK.symm
  have hv : e • (h - 1) = h - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hhe; exact hhe.symm
  have hua : (K - 1) * a = e • K := by
    have hK1 : K - 1 = K * (1 - k) := by rw [mul_sub, mul_one, hKk]
    rw [hK1, mul_assoc, ha, mul_smul_comm, mul_one]
  have hbv : b * (h - 1) = e • h := by
    have hh1 : h - 1 = (1 - h') * h := by rw [sub_mul, one_mul, hh]
    rw [hh1, ← mul_assoc, hb, smul_mul_assoc, one_mul]
  calc (K - 1) * (1 - (b - a) * (h - 1))
      = (K - 1) - (K - 1) * (b * (h - 1)) + ((K - 1) * a) * (h - 1) := by noncomm_ring
    _ = (K - 1) - (e • (K - 1)) * h + K * (e • (h - 1)) := by
        rw [hbv, hua]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = h - 1 := by rw [hu, hv]; noncomm_ring

end Ring

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {β : Type} [Fintype β] [DecidableEq β]

theorem cayley (c : A →ₐ[R] A) {J k a : Matrix β β A} {e : R} (hk : kᵀ * J * k.map c = J) (hea : e • a = a)
    (ha : (1 - k) * a = e • (1 : Matrix β β A)) (he : e * e = e) : aᵀ * J + J * a.map c = e • J := by
  have hT : aᵀ * (1 - k)ᵀ = e • (1 : Matrix β β A) := by
    rw [← transpose_mul, ha, transpose_smul, transpose_one]
  have hac : (1 - k.map c) * a.map c = e • (1 : Matrix β β A) := by
    have h1 := congrArg c.mapMatrix ha
    rwa [map_mul, map_sub, map_one, map_smul, map_one, AlgHom.mapMatrix_apply,
      AlgHom.mapMatrix_apply] at h1
  have heac : e • a.map c = a.map c := by
    have h1 := congrArg c.mapMatrix hea
    rwa [map_smul, AlgHom.mapMatrix_apply] at h1
  have heaT : e • aᵀ = aᵀ := by rw [← transpose_smul, hea]

  have hid : (1 - k)ᵀ * J * (1 - k.map c) = (1 - k)ᵀ * J + J * (1 - k.map c) := by
    rw [transpose_sub, transpose_one]
    have e1 : (1 - kᵀ) * J * (1 - k.map c)
        = (1 - kᵀ) * J + J * (1 - k.map c) + (kᵀ * J * k.map c - J) := by noncomm_ring
    rw [e1, hk, sub_self, add_zero]
  have main : aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c = e • J := by
    calc aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c
        = (aᵀ * (1 - k)ᵀ) * J * ((1 - k.map c) * a.map c) := by simp only [Matrix.mul_assoc]
      _ = e • J := by
          rw [hT, hac, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul, he]
  have t1 : aᵀ * ((1 - k)ᵀ * J) * a.map c = J * a.map c := by
    rw [← Matrix.mul_assoc, hT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      ← Matrix.mul_smul, heac]
  have t2 : aᵀ * (J * (1 - k.map c)) * a.map c = aᵀ * J := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hac, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_smul, ← Matrix.smul_mul, heaT]
  rw [hid, Matrix.mul_add, Matrix.add_mul, t1, t2] at main
  rw [add_comm]
  exact main

def unip (N : Matrix β β A) : GL (β ⊕ β) A where
  val := fromBlocks (1 + N) (-N) N (1 - N)
  inv := fromBlocks (1 - N) N (-N) (1 + N)
  val_inv := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring
  inv_val := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring

theorem unip_mem (c : A →ₐ[R] A) {J N : Matrix β β A} (hN : Nᵀ * J + J * N.map c = 0) :
    unip N ∈ GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) := by
  show ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * GlobalTheory.WeilM.dbl J *
      ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A).map c = GlobalTheory.WeilM.dbl J
  have hU : ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) =
      fromBlocks (1 + N) (-N) N (1 - N) := rfl
  have hm1 : (1 + N).map c = 1 + N.map c := by
    have h := map_add c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  have hm2 : (-N).map c = -N.map c := map_neg c.mapMatrix N
  have hm3 : (1 - N).map c = 1 - N.map c := by
    have h := map_sub c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  rw [hU, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [transpose_add, transpose_sub, transpose_neg, transpose_one, hm1, hm2, hm3]

  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · calc _ = J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = J := by rw [hN, add_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = -J := by rw [hN, add_zero]

theorem cong_block {e : R} {x : Matrix β β A} (hx : (1 - e) • (x - 1) = 0) :
    (1 - e) • (fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1) = 0 := by
  have h1 : fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1 =
      fromBlocks (x - 1) 0 0 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, fromBlocks_smul, hx]
  simp

theorem decomposition : ∀ (R A : Type) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (c : A →ₐ[R] A) (β : Type) [inst_3 : Fintype β] [inst_4 : DecidableEq β] (J : Matrix β β A), IsUnit (Matrix.det J) →
    ∀ (e : R), e * e = e →
    ∀ (g k : ↥(GlobalTheory.WeilM.UG c J)), ((1 : R) - e) • ((↑(↑g : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ((1 : R) - e) • ((↑(↑k : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ∀ (a b : Matrix β β A), e • a = a →
    e • b = b →
    a * ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ (gd kd : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))), (↑(↑gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑g : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    (↑(↑kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑k : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    ∃ (p₁ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (p₂ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (t₁ : GL β A) (t₂ : GL β A), ((1 : R) - e) • ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((1 : R) - e) • ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₁ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₂ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    gd = kd * p₁ * kd⁻¹ * p₂ := by
  intro R A _ _ _ c β _ _ J _ e he g k hg hk a b hea heb hak hka hbh hhb gd kd hgd hkd
  obtain ⟨Km, hKm⟩ : ∃ Km : Matrix β β A, Km = (((k : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  obtain ⟨gi, hgi⟩ : ∃ gi : Matrix β β A, gi = (((g : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  have hKk : Km * ((k : GL β A) : Matrix β β A) = 1 := by rw [hKm]; exact Units.inv_mul _
  have hkK : ((k : GL β A) : Matrix β β A) * Km = 1 := by rw [hKm]; exact Units.mul_inv _
  have hgig : gi * ((g : GL β A) : Matrix β β A) = 1 := by rw [hgi]; exact Units.inv_mul _
  have hggi : ((g : GL β A) : Matrix β β A) * gi = 1 := by rw [hgi]; exact Units.mul_inv _
  have hhgk : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = gi * ((k : GL β A) : Matrix β β A) := by rw [hgi]; rfl

  have hh : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) * (Km * ((g : GL β A) : Matrix β β A)) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((k : GL β A) : Matrix β β A) Km, hkK, Matrix.one_mul, hgig]
  have hh2 : Km * ((g : GL β A) : Matrix β β A) * (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((g : GL β A) : Matrix β β A) gi, hggi, Matrix.one_mul, hKk]
  have hKc : (1 - e) • (Km - 1) = 0 := cong_inv hk hKk
  have hhc : (1 - e) • (Km * ((g : GL β A) : Matrix β β A) - 1) = 0 := cong_mul hKc hg
  have key1 := key hKk hh hKc hhc hka hbh
  have key2 := key hh2 hkK hhc hKc hhb hak

  have hca := cayley c (J := J) (k := ((k : GL β A) : Matrix β β A)) (a := a) k.2 hea hka he
  have hcb := cayley c (J := J) (k := (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A)) (a := b) (g⁻¹ * k).2 heb hhb he
  have hskew : (a - b)ᵀ * J + J * (a - b).map c = 0 := by
    have hmap : (a - b).map c = a.map c - b.map c := by ext i j; simp
    rw [transpose_sub, hmap, Matrix.sub_mul, Matrix.mul_sub]
    calc aᵀ * J - bᵀ * J + (J * a.map c - J * b.map c)
        = (aᵀ * J + J * a.map c) - (bᵀ * J + J * b.map c) := by abel
      _ = 0 := by rw [hca, hcb, sub_self]
  obtain ⟨u, hu⟩ : ∃ u : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J),
      ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 + (a - b)) (-(a - b)) (a - b) (1 - (a - b)) ∧
      (((u⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 - (a - b)) (a - b) (-(a - b)) (1 + (a - b)) :=
    ⟨⟨unip (a - b), unip_mem c hskew⟩, rfl, rfl⟩
  have h2 : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = 1 := Units.inv_mul _
  have hkdinv : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks Km 0 0 1 := by
    have h1 : ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1 = 1 := by
      rw [hkd, fromBlocks_multiply, hkK]; simp [fromBlocks_one]
    calc (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1) := by rw [h1, Matrix.mul_one]
      _ = fromBlocks Km 0 0 1 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hblk : ∀ P Q S T : Matrix β β A,
      fromBlocks P Q S T - 1 = fromBlocks (P - 1) Q S (T - 1) := by
    intro P Q S T
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  have hN0 : (1 - e) • (a - b) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hN0' : (1 - e) • (b - a) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hkdc : (1 - e) • (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hkd]; exact cong_block hk
  have hgdc : (1 - e) • (((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hgd]; exact cong_block hg
  have hkdic : (1 - e) • ((((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := cong_inv hkdc h2
  have huc : (1 - e) • (((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by
    rw [hu.1, hblk, fromBlocks_smul]; simp [hN0, hN0']

  have ht : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) = 1 := by
    have e1 : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) =
        (1 - (a - b) * (Km - 1)) - (b - a) * ((Km * ((g : GL β A) : Matrix β β A) - 1) * (1 - (a - b) * (Km - 1))) := by
      noncomm_ring
    rw [e1, key2]
    noncomm_ring
  have hK2 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) = (1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b) := by
    have e1 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) =
        (Km - 1) * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) + (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) := by
      noncomm_ring
    rw [e1, key1]
    noncomm_ring
  have hfin : ((k : GL β A) : Matrix β β A) * ((1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b)) = 1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1) := by
    rw [← hK2, ← Matrix.mul_assoc, hkK, Matrix.one_mul]
  have hv : (((kd * u * kd⁻¹ * gd : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) :
      Matrix (β ⊕ β) (β ⊕ β) A) = ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) := rfl
  refine ⟨u⁻¹, kd * u * kd⁻¹ * gd, 1,
    ⟨1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1), 1 - (a - b) * (Km - 1), ht, mul_eq_one_comm.mp ht⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.2, hblk, fromBlocks_smul]; simp [hN0, hN0']
  · rw [hv]; exact cong_mul (cong_mul (cong_mul hkdc huc) hkdic) hgdc
  · rw [hu.2, GlobalTheory.WeilM.diagCols]
    simp only [fromBlocks_mul_fromRows, fromRows_mul, Units.val_one, Matrix.mul_one,
      Matrix.one_mul]
    rw [fromRows_ext_iff]
    constructor <;> abel
  · rw [hv, hkd, hu.1, hkdinv, hgd, GlobalTheory.WeilM.diagCols]
    simp only [Matrix.mul_assoc, fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Units.val_mk]
    rw [fromRows_ext_iff]
    constructor
    · refine Eq.trans ?_ (hfin.trans ?_) <;> noncomm_ring
    · noncomm_ring
  · group

end GlobalTheory.UnipotentCongruenceInverse
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentBlockUnipotentIdentity
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SiegelDiagDecomp
open Matrix

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {β : Type} [Fintype β] [DecidableEq β]

theorem diag_decomp : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (β : Type) [Fintype β] [DecidableEq β]
    (J : Matrix β β A), IsUnit J.det → ∀ e : R, e * e = e → ∀ g k : UG c J,
    (1 - e) • ((g.1.1 : Matrix β β A) - 1) = 0 → (1 - e) • ((k.1.1 : Matrix β β A) - 1) = 0 →
    ∀ a b : Matrix β β A, e • a = a → e • b = b →
    a * (1 - (k.1.1 : Matrix β β A)) = e • (1 : Matrix β β A) → (1 - (k.1.1 : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) = e • (1 : Matrix β β A) →
    (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ gd kd : UG c (dbl J), (gd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (g.1.1 : Matrix β β A) 0 0 1 →
    (kd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (k.1.1 : Matrix β β A) 0 0 1 →
    ∃ (p₁ p₂ : UG c (dbl J)) (t₁ t₂ : GL β A), (1 - e) • ((p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (1 - e) • ((p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₁.val ∧
      (p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₂.val ∧ gd = kd * p₁ * kd⁻¹ * p₂ := by
  first
  | exact @_root_.GlobalTheory.UnipotentCongruenceInverse.decomposition
  | exact _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition
  | (apply _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentCongruenceInverse.decomposition <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentCongruenceInverse.decomposition ..)

end GlobalTheory.SiegelDiagDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentBlockUnipotentIdentityStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_block_unipotent_identity : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (β : Type) [Fintype β] [DecidableEq β]
    (J : Matrix β β A), IsUnit J.det → ∀ e : R, e * e = e → ∀ g k : UG c J,
    (1 - e) • ((g.1.1 : Matrix β β A) - 1) = 0 → (1 - e) • ((k.1.1 : Matrix β β A) - 1) = 0 →
    ∀ a b : Matrix β β A, e • a = a → e • b = b →
    a * (1 - (k.1.1 : Matrix β β A)) = e • (1 : Matrix β β A) → (1 - (k.1.1 : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) = e • (1 : Matrix β β A) →
    (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ gd kd : UG c (dbl J), (gd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (g.1.1 : Matrix β β A) 0 0 1 →
    (kd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (k.1.1 : Matrix β β A) 0 0 1 →
    ∃ (p₁ p₂ : UG c (dbl J)) (t₁ t₂ : GL β A), (1 - e) • ((p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (1 - e) • ((p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₁.val ∧
      (p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₂.val ∧ gd = kd * p₁ * kd⁻¹ * p₂ := by
  first | exact @GlobalTheory.SiegelDiagDecomp.diag_decomp | exact GlobalTheory.SiegelDiagDecomp.diag_decomp | (intros; apply GlobalTheory.SiegelDiagDecomp.diag_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearForm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.InertLagChar.LinForm

theorem hasCompactSupport_comp_of_leftInverse {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [Zero M] {f : X → Y} {l : Y → X} (hl : Continuous l) (hlf : ∀ x, l (f x) = x) {g : Y → M}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ f) := by
  refine IsCompact.of_isClosed_subset (hg.image hl) isClosed_closure ?_
  refine closure_minimal ?_ (hg.image hl).isClosed
  intro x hx
  exact ⟨f x, subset_tsupport _ hx, hlf x⟩

theorem integrable_of_cont_cs {X : Type} [TopologicalSpace X] (μ : @Measure X (borel X))
    [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f μ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport hcs

end GlobalTheory.InertLagChar.LinForm

open GlobalTheory.InertLagChar.LinForm in
theorem GlobalTheory.InertLagChar.lagInt_linForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  intro F _ _ v κ _ ψ hψ μ hμ N ν hν j hj hdiag

  have hd : Continuous (fun x : κ → Fv F v => (Sum.elim x x : κ ⊕ κ → Fv F v)) := by
    refine continuous_pi fun i => ?_
    cases i <;> exact continuous_apply _
  have hdl : Continuous (fun z : κ ⊕ κ → Fv F v => fun i => z (Sum.inl i)) :=
    continuous_pi fun i => continuous_apply _

  have hin : ∀ w : (κ → Fv F v) × (κ → Fv F v), ∀ Φ ∈ SB (κ ⊕ κ → Fv F v),
      Integrable (fun x => schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x)) μ := by
    intro w Φ hΦ
    have hs := GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ hΦ
    exact integrable_of_cont_cs μ (hs.1.continuous.comp hd)
      (hasCompactSupport_comp_of_leftInverse hdl (fun x => rfl) hs.2)
  have hschr_add : ∀ w (Φ Φ' : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (Φ + Φ') = schr ψ w Φ + schr ψ w Φ' := by
    intro w Φ Φ'; funext x; simp [schr, mul_add]
  have hschr_smul : ∀ w (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (c • Φ) = c • schr ψ w Φ := by
    intro w c Φ; funext x; simp [schr]; ring
  have hdiag_add : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∀ Φ' ∈ SB (κ ⊕ κ → Fv F v),
      diagW ψ μ (Φ + Φ') = diagW ψ μ Φ + diagW ψ μ Φ' := by
    intro Φ hΦ Φ' hΦ'
    funext w
    simp only [diagW, Pi.add_apply, hschr_add]
    exact integral_add (hin w Φ hΦ) (hin w Φ' hΦ')
  have hdiag_smul : ∀ (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), diagW ψ μ (c • Φ) = c • diagW ψ μ Φ := by
    intro c Φ
    funext w
    simp only [diagW, Pi.smul_apply, hschr_smul, smul_eq_mul]
    exact integral_const_mul (μ := μ) c _

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
  have hlj : ∀ y, l (j y) = y := fun y => by
    have := LinearMap.congr_fun hl y
    simpa using this
  have hout : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Integrable (fun y => diagW ψ μ Φ (j y)) ν := by
    intro Φ hΦ
    have hs := hdiag Φ hΦ
    have hcs : HasCompactSupport (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hasCompactSupport_comp_of_leftInverse (f := (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v)))
        (l := (l : (κ → Fv F v) × (κ → Fv F v) → (Fin N → Fv F v))) hlc hlj hs.2
    have hc : Continuous (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hs.1.continuous.comp hjc
    exact integrable_of_cont_cs ν hc hcs
  let f : SB (κ ⊕ κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => lagInt ψ μ ν j Φ.1
      map_add' := by
        intro Φ Φ'
        simp only [Submodule.coe_add, lagInt, hdiag_add _ Φ.2 _ Φ'.2, Pi.add_apply]
        exact integral_add (hout _ Φ.2) (hout _ Φ'.2)
      map_smul' := by
        intro c Φ
        simp only [Submodule.coe_smul, lagInt, hdiag_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul (μ := ν) c _ }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun Φ hΦ => LinearMap.congr_fun hg ⟨Φ, hΦ⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearFormStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  first | exact @GlobalTheory.InertLagChar.lagInt_linForm | exact GlobalTheory.InertLagChar.lagInt_linForm | (intros; apply GlobalTheory.InertLagChar.lagInt_linForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralHeisenbergTranslateIntegralIndic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralHeisenbergTranslateIntegralIndic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagInd

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

theorem invOf_two_mem (h : (2 : 𝓞 F) ∉ v.asIdeal) : ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [invOf_eq_inv, map_inv₀, h2]

theorem schr_box_apply (ψ : AddChar (Fv F v) ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v))
    (x : κ → Fv F v) :
    schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) (boxFun φ₁ φ₂) (Sum.elim x x) =
      ψ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * (φ₁ (x + w.1) * φ₂ x) := by
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 2
  all_goals (congr 1; funext i; simp)

end GlobalTheory.InertLagInd

namespace GlobalTheory.InertLagInd

theorem diagW_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  intro F _ _ v κ _ ψ hψ h2 μ hμ
  classical
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨S, hS⟩ : ∃ S : Set (κ → Fv F v), S = {x | ∀ k, x k ∈ v.adicCompletionIntegers F} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ S ↔ ∀ k, x k ∈ v.adicCompletionIntegers F := fun x => by subst hS; rfl
  have hpi : S = Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp [hmem]
  have hSo : IsOpen S := by
    rw [hpi]; exact isOpen_set_pi Set.finite_univ (fun _ _ => Valued.isOpen_integer _)
  have hSc : IsCompact S := by
    rw [hpi]; exact isCompact_univ_pi (fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h0S : (0 : κ → Fv F v) ∈ S := (hmem 0).2 fun k => zero_mem _
  have hadd : ∀ {a}, a ∈ S → ∀ x, (x + a ∈ S ↔ x ∈ S) := fun {a} ha x => by
    rw [hmem, hmem]
    rw [hmem] at ha
    exact ⟨fun h k => by simpa using sub_mem (h k) (ha k), fun h k => add_mem (h k) (ha k)⟩
  have hind : ∀ {a}, a ∈ S → ∀ x, S.indicator (1 : (κ → Fv F v) → ℂ) (x + a) = S.indicator 1 x := fun ha x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hadd ha x).2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hadd ha x).1 hx)]
  have hψ1 : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    rw [psiAt_apply]; simpa using (hψ 1).2 (one_mem _) y hy
  have hφ : S.indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
    rw [hS]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨S.indicator 1, hφ, ((μ.real S : ℝ) : ℂ), ?_, S ×ˢ S, hSo.prod hSo, hSc.prod hSc, ⟨h0S, h0S⟩, ?_⟩
  · have h1 : μ S ≠ 0 := hSo.measure_ne_zero μ ⟨0, h0S⟩
    have h2' : μ S ≠ ⊤ := hSc.measure_lt_top.ne
    exact Complex.ofReal_ne_zero.2 (by rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h1, h2'⟩)
  intro w
  simp only [diagW, schr_box_apply]
  by_cases hw1 : w.1 ∈ S
  · by_cases hw2 : w.2 ∈ S
    · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hw1, hw2⟩)]
      have key : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) = S.indicator (1 : (κ → Fv F v) → ℂ) x := by
        intro x
        rw [hind hw1 x]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hψ1]
          · simp
          · rw [hmem] at hx hw1 hw2
            exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw2 i))
              (mul_mem (invOf_two_mem h2) (sum_mem fun i _ => mul_mem (hw1 i) (hw2 i)))
        · simp [Set.indicator_of_notMem hx]
      simp_rw [key]
      rw [show S.indicator (1 : (κ → Fv F v) → ℂ) = S.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hSo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (fun h => hw2 (Set.mem_prod.1 h).2)]
      obtain ⟨i, hi⟩ : ∃ i, w.2 i ∉ v.adicCompletionIntegers F := by
        by_contra h; push_neg at h; exact hw2 ((hmem _).2 h)
      obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (w.2 i * y) ≠ 1 := by
        by_contra h; push_neg at h; exact hi ((hψ _).1 h)
      have ha : Pi.single i y ∈ S := (hmem _).2 fun k => by
        rw [Pi.single_apply]; split_ifs
        · exact hy
        · exact zero_mem _
      set g : (κ → Fv F v) → ℂ := fun x => psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) with hg
      have hshift : ∀ x, g (x + Pi.single i y) = psiAt ψ v (w.2 i * y) * g x := by
        intro x
        simp only [hg]
        rw [add_right_comm, hind ha, hind ha, add_dotProduct, single_dotProduct,
          show x ⬝ᵥ w.2 + y * w.2 i + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) =
            w.2 i * y + (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) by ring, AddChar.map_add_eq_mul]
        ring
      have hI : ∫ x, g x ∂μ = psiAt ψ v (w.2 i * y) * ∫ x, g x ∂μ := by
        rw [← integral_const_mul, ← integral_add_right_eq_self _ (Pi.single i y)]
        simp only [hshift]
      rw [psiAt_apply] at hI
      have : (1 - psiLoc ψ v (w.2 i * y)) * ∫ x, g x ∂μ = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  · rw [Set.indicator_of_notMem (fun h => hw1 (Set.mem_prod.1 h).1)]
    have hz : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
        (S.indicator (1 : (κ → Fv F v) → ℂ) (x + w.1) * S.indicator 1 x) = 0 := by
      intro x
      by_cases hx : x ∈ S
      · have : x + w.1 ∉ S := fun h => hw1 (by rw [add_comm] at h; exact (hadd hx w.1).1 h)
        simp [Set.indicator_of_notMem this]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [hz]
    exact integral_zero _ _

end GlobalTheory.InertLagInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralHeisenbergTranslateIntegralIndicStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  first | exact @GlobalTheory.InertLagInd.diagW_box_indicator | exact GlobalTheory.InertLagInd.diagW_box_indicator | (intros; apply GlobalTheory.InertLagInd.diagW_box_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZeroStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  first | exact @GlobalTheory.integral_indicator_preimage_injective_ne_zero | exact GlobalTheory.integral_indicator_preimage_injective_ne_zero | (intros; apply GlobalTheory.integral_indicator_preimage_injective_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTransformingCharacterEqOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagChar

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

def boxL {k κ κ' : Type} [CommRing k] (φ₂ : (κ' → k) → ℂ) : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → k) → ℂ) where
  toFun φ := boxFun φ φ₂
  map_add' a b := by funext x; simp [boxFun, add_mul]
  map_smul' a b := by funext x; simp [boxFun, mul_assoc]

variable {F : Type} [Field F] [NumberField F]

theorem one_sub_smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {u : M} (hu : At (evFin F v) u) :
    (1 - liftV v (1 : Fv F v)) • u = 0 := hu _ (by rw [map_sub, map_one, evFin_liftV, sub_self])

theorem smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {u : M} (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := one_sub_smul_of_at hu
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem at_of_one_sub_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {u : M}
    (h : (1 - liftV v (1 : Fv F v)) • u = 0) : At (evFin F v) u := fun t ht => by
  have h1 : t * (1 - liftV v (1 : Fv F v)) = t := by
    have h2 := at_liftV v (1 : Fv F v) t ht
    rw [smul_eq_mul] at h2
    rw [mul_sub, mul_one, h2, sub_zero]
  rw [← h1, mul_smul, h, smul_zero]

def Scales {κ : Type} [Fintype κ] (v : Pl (F := F)) (Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (a : ℂ) : Prop :=
  ∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T Φ Φ₁ ∧ Λ Φ₁ = a * Λ Φ

theorem Scales.mul {κ : Type} [Fintype κ] {v : Pl (F := F)} {Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ}
    {T T' : Module.End ℂ ((κ → AF F) → ℂ)} {a a' : ℂ} (h : Scales v Λ T a) (h' : Scales v Λ T' a')
    (hp : ∀ Φ ∈ schA F κ, T' Φ ∈ schA F κ) : Scales v Λ (T * T') (a * a') := by
  intro Φ hΦ
  obtain ⟨Φ₁, hΦ₁, hA₁, e₁⟩ := h' Φ hΦ
  obtain ⟨Φ₂, hΦ₂, hA₂, e₂⟩ := h Φ₁ hΦ₁
  refine ⟨Φ₂, hΦ₂, fun r hr => ?_, by rw [e₂, e₁, mul_assoc]⟩
  have hr1 : Rest (evFin F v) Φ₁ r := ⟨hr.1, by rw [← hA₁ r hr]; exact hp _ hr.2⟩
  show T (T' _) = _
  rw [hA₁ r hr, hA₂ r hr1]

theorem Scales.unique {κ : Type} [Fintype κ] {v : Pl (F := F)} {Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ}
    {T : Module.End ℂ ((κ → AF F) → ℂ)} {a a' : ℂ} (h : Scales v Λ T a) (h' : Scales v Λ T a')
    {Φ : (κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ → Fv F v)) (h0 : Λ Φ ≠ 0) : a = a' := by
  obtain ⟨Φ₁, -, hA₁, e₁⟩ := h Φ hΦ
  obtain ⟨Φ₂, -, hA₂, e₂⟩ := h' Φ hΦ
  have e : Φ₁ = Φ₂ := GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v Φ Φ₁ Φ₂ hΦ fun r hr => (hA₁ r hr).symm.trans (hA₂ r hr)
  rw [e, e₂] at e₁
  exact (mul_right_cancel₀ h0 e₁).symm

theorem scales_one {κ : Type} [Fintype κ] (v : Pl (F := F)) (Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Scales v Λ 1 1 :=
  fun Φ hΦ => ⟨Φ, hΦ, fun _ _ => rfl, (one_mul _).symm⟩

theorem scales_of_box {κ : Type} [Fintype κ] {v : Pl (F := F)} (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (T : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (a : ℂ)
    (hex : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∃ Φ₁ ∈ SB (κ ⊕ κ → Fv F v), Acts (evFin F v) T Φ Φ₁)
    (r : (κ ⊕ κ → AF F) → ℂ) (hr0 : r 0 ≠ 0) (hr : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Rest (evFin F v) Φ r)
    (hbox : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ∀ Φ₁, Acts (evFin F v) T (boxFun φ₁ φ₂) Φ₁ →
      Λ Φ₁ = a * Λ (boxFun φ₁ φ₂)) : Scales v Λ T a := by
  let S : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → Fv F v) → ℂ) :=
    { toFun := fun f t => (r 0)⁻¹ * T (tens (evFin F v) f r) (fun i => liftV v (t i))
      map_add' := fun f f' => by
        have e : tens (evFin F v) (f + f') r = tens (evFin F v) f r + tens (evFin F v) f' r := by
          funext x; simp [tens, add_mul]
        funext t; simp only [e, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        have e : tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := by
          funext x; simp [tens, mul_assoc]
        funext t; simp only [e, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hS : ∀ f ∈ SB (κ ⊕ κ → Fv F v), ∀ f₁, Acts (evFin F v) T f f₁ → f₁ = S f := by
    intro f hf f₁ hA
    funext t
    show f₁ t = (r 0)⁻¹ * T (tens (evFin F v) f r) (fun i => liftV v (t i))
    rw [hA r (hr f hf)]
    have hat : At (evFin F v) (fun i => liftV v (t i)) := by
      intro u hu; funext i; exact at_liftV v _ u hu
    have h1 : r (fun i => liftV v (t i)) = r 0 := by
      simpa using (hr f hf).1 0 _ hat
    simp only [tens, h1, evFin_liftV]
    field_simp
  have key := GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat F v κ κ ψ hψ hψ1 (Λ ∘ₗ S - a • Λ) (fun φ₁ h₁ φ₂ h₂ => by
    obtain ⟨Φ₁, -, hA⟩ := hex _ (box_mem_SB h₁ h₂)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply]
    rw [← hS _ (box_mem_SB h₁ h₂) Φ₁ hA, hbox φ₁ h₁ φ₂ h₂ Φ₁ hA, sub_self])
  intro Φ hΦ
  obtain ⟨Φ₁, hΦ₁, hA⟩ := hex Φ hΦ
  refine ⟨Φ₁, hΦ₁, hA, ?_⟩
  have h := key Φ hΦ
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h
  rw [hS Φ hΦ Φ₁ hA]
  exact sub_eq_zero.1 h

theorem char_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    (∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), l φ ≠ 0) →
    ∀ c : UA σ G.V'.J → ℂ, (∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = c g * l φ) →
    ∀ g ∈ UAt σ G.V' (evFin F v), c g = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl hne c hc g hg
  obtain ⟨h2, -, hunr⟩ := hT.base.inert v w hin
  have hψc : Continuous (psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hψ1 : psiAt B.ψ v ≠ 1 := by
    obtain ⟨t, ht⟩ := GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hT.base.std v
    intro h; exact ht (by rw [h]; rfl)
  have hJ : IsUnit G.V'.J.det := GlobalTheory.isUnit_det_of_isHerm F E σ B a' G.V' _ _ hT.geo.hV'
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw
  obtain ⟨L, hL, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hLφ, -⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  obtain ⟨hdm, N, j, ζ, hj, hζ, hζs, hT'⟩ := GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace F E σ a' (a + a') G.V' G.W G.M' v m C hC
  obtain ⟨ν, hν⟩ : ∃ ν : @Measure (Fin N → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
    letI : MeasurableSpace (Fin N → Fv F v) := borel _
    haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
    exact ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨φ₀, hφ₀, c₁, hc₁, U, hUo, hUc, hU0, hU⟩ := GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator F v _ B.ψ hunr h2 μ hμ
  have hSB := GlobalTheory.T.heisenbergDiagonalIntegral_mem_schwartzBruhat F v _ _ hψc hψ1 μ hμ _ (box_mem_SB hφ₀ hφ₀) c₁ hc₁ U hUo hUc hU0 hU
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm F v _ _ hψc μ hμ N ν hν j hj hSB
  have hΛ0 : Λ (boxFun φ₀ φ₀) ≠ 0 := by
    rw [hΛ _ (box_mem_SB hφ₀ hφ₀), lagInt]
    simp only [hU]
    exact GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero F v _ N ν hν j hj c₁ hc₁ U hUo hUc hU0
  have hlag : ∀ y, ζ y * Cᵀ ∈ lagAt v C := fun y =>
    ⟨fun t ht => by rw [← Matrix.smul_mul, (hζ y).1 t ht, Matrix.zero_mul], ζ y, rfl⟩
  have hiso : ∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2 := by
    intro y y'
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hC (-1) _ _ (hlag y) (hlag y')
    change symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (ζ y * Cᵀ) (ζ y' * Cᵀ) = 0 at h0
    rw [G.M'.co.form] at h0
    have h1 := congrArg (evFin F v) h0
    rw [← sub_eq_zero, ← (hζ y).2, ← (hζ y').2]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

  have hHeis : ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v), HeisInv G.M' B.ψ v C (Λ ∘ₗ boxL φ₂) := by
    rintro φ₂ hφ₂ u ⟨hu, z, hz⟩ φ hφ φ₁ hφ₁ hA
    obtain ⟨y, hy⟩ := hζs (liftV v (1 : Fv F v) • z) (fun t ht => by
      rw [smul_smul, ← smul_eq_mul, at_liftV v _ t ht, zero_smul])
    have hu' : u = ζ y * Cᵀ := by rw [hy, Matrix.smul_mul, ← hz, smul_of_at hu]
    have hA' := GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hu φ
    have e : φ₁ = _ := GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => (hA r hr).symm.trans (hA' r hr)
    show Λ (boxFun φ₁ φ₂) = Λ (boxFun φ φ₂)
    rw [hΛ _ (box_mem_SB hφ₁ hφ₂), hΛ _ (box_mem_SB hφ hφ₂), e, hu', (hζ y).2]
    exact GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars F v _ _ μ hμ N ν hν j hiso y φ φ₂
  obtain ⟨φt, hφt, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v hunr m C hC
  have hlt : l φt ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hne; exact hne (hline l hl h f hf)
  have hprop : ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Λ (boxFun φ φ₂) = Λ (boxFun φt φ₂) / l φt * l φ := by
    intro φ₂ hφ₂ φ hφ
    have hl' : HeisInv G.M' B.ψ v C (Λ ∘ₗ boxL φ₂ - (Λ (boxFun φt φ₂) / l φt) • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hHeis φ₂ hφ₂ u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (Λ ∘ₗ boxL φ₂ - (Λ (boxFun φt φ₂) / l φt) • l) φt = 0 := by
      show Λ (boxFun φt φ₂) - (Λ (boxFun φt φ₂) / l φt) * l φt = 0
      rw [div_mul_cancel₀ _ hlt, sub_self]
    exact sub_eq_zero.1 (hline _ hl' h0 φ hφ)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))) v

  have hdiag : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ kd : UG (cA σ) (dbl (incM F G.V'.J)),
      (kd.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
      Scales v Λ (omd kd) (c k) := by
    intro k hk kd hkd
    have hAt : At (evFin F v) ((kd.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
      intro u hu
      have hk1 : u • (mat k - 1) = 0 := hk u hu
      have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
          Matrix.fromBlocks (mat k - 1) 0 0 0 := by
        rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
        simp [sub_eq_add_neg]
      rw [hkd, e, Matrix.fromBlocks_smul]
      simp [hk1]
    refine scales_of_box _ hψc hψ1 Λ (omd kd) (c k) (GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v kd hAt) R hR0 hR ?_
    intro φ₁ h₁ φ₂ h₂ Φ₁ hA
    obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v k hk
    rw [GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first F v _ _ (om' (k, 1)) (omd kd) (fun Φ₁ h₁ Φ₂ h₂ => hres k kd hkd Φ₁ h₁ Φ₂ h₂) φ₁ h₁ φ₂ h₂ _ Φ₁ (hS φ₁ h₁).2 hA,
      hprop φ₂ h₂ _ (hS φ₁ h₁).1, hprop φ₂ h₂ φ₁ h₁, hc k hk φ₁ h₁ _ (hS φ₁ h₁).1 (hS φ₁ h₁).2]
    ring

  have hpar : ∀ (p : UG (cA σ) (dbl (incM F G.V'.J))) (t : GL (Fin a') (AE F E)),
      At (evFin F v) ((p.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) →
      (p.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) * diagCols (Fin a') = diagCols (Fin a') * t.val →
      Scales v Λ (omd p) 1 := by
    intro p t hp hpt Φ hΦ
    obtain ⟨Φ₁, hΦ₁, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hp Φ hΦ
    refine ⟨Φ₁, hΦ₁, hA, ?_⟩
    obtain ⟨hdt, hnt, s, hs, hns⟩ := GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm F E σ hT.base.cm a' G.V'.J hJ.ne_zero v p t hp hpt
    obtain ⟨T, hTζ, hTd⟩ := hT' s
    have hpt' := GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point F E σ a' (a + a') G.V' G.W G.M' B.ψ hT.base.std.1 v m C hC d' hd' dd hdd omd hspl.toIsSplitting
      L hinv r₀ hr₀ c₀ hc₀ μ hLφ p _ (hsieg L hL hinv p t hpt) Φ hΦ Φ₁ hΦ₁ hA
    have hχ : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
      rw [MonoidHom.div_apply, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hT v w hin hv
        (Matrix.GeneralLinearGroup.det t) hdt, div_self']
    set u : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t) with hu
    have hmod : (((adeleClass F).modu u : NNReal) : ℝ) =
        GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue F v u hnt
    have hdT : Matrix.GeneralLinearGroup.det T = (Units.map (evFin F v : AF F →* Fv F v) u) ^ m := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hTd, ← GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm, hns, Units.val_pow_eq_pow_val]
      rfl
    have hpow : ∀ (x : (Fv F v)ˣ) (k : ℕ), GlobalTheory.SplitWeil.nabs (Fv F v) (x ^ k) = GlobalTheory.SplitWeil.nabs (Fv F v) x ^ k := by
      intro x k
      induction k with
      | zero => rw [pow_zero, pow_zero, GlobalTheory.SplitWeil.nabs_one]
      | succ k ih => rw [pow_succ, pow_succ, GlobalTheory.SplitWeil.nabs_mul, ih]
    have hexp : ((Fintype.card (Fin (a + a')) : ℝ) / 2) = (m : ℝ) := by
      rw [Fintype.card_fin, hdm]; push_cast; ring
    rw [hχ, hmod, hexp, Real.rpow_natCast, ← hpow, ← hdT, Circle.coe_one, one_mul] at hpt'
    rw [hΛ _ hΦ₁, hΛ _ hΦ, one_mul, lagInt, lagInt, ← GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace F v N ν hν T (fun y => diagW (psiAt B.ψ v) μ Φ (j y)),
      ← integral_const_mul]
    refine congrArg _ (funext fun y => ?_)
    set_option backward.isDefEq.respectTransparency false in
      rw [← (hζ y).2, hpt' _ (hζ y).1, ← hs, ← hTζ, (hζ _).2]

  obtain ⟨k, hk, α, β, hα, hβ, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unitaryScalar_inertPlace_invertible_shifts F E σ B hT.base v w hin a' G.V'.J g
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) g
  obtain ⟨kd, hkd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) k
  have hJA : IsUnit (incM F G.V'.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  have hee : liftV v (1 : Fv F v) * liftV v (1 : Fv F v) = liftV v (1 : Fv F v) := smul_of_at (at_liftV v 1)
  obtain ⟨p₁, p₂, t₁, t₂, hp₁, hp₂, ht₁, ht₂, hdec⟩ := GlobalTheory.T.idempotent_block_unipotent_identity (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) hJA _ hee g k
    (one_sub_smul_of_at hg) (one_sub_smul_of_at hk) α β (smul_of_at hα) (smul_of_at hβ) e1 e2 e3 e4 gd kd hgd hkd
  have hkk : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
  have hki : k⁻¹ ∈ UAt σ G.V' (evFin F v) := fun u hu => by
    have e : mat k⁻¹ - 1 = -((mat k - 1) * mat k⁻¹) := by rw [Matrix.sub_mul, hkk, Matrix.one_mul, neg_sub]
    rw [e, smul_neg, ← Matrix.smul_mul, hk u hu, Matrix.zero_mul, neg_zero]
  have hkdi : ((kd⁻¹).1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k⁻¹) 0 0 1 := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hkd, Matrix.fromBlocks_multiply]
    have : (k.1.1 : Matrix (Fin a') (Fin a') (AE F E)) * mat k⁻¹ = 1 := hkk
    simp [this, Matrix.fromBlocks_one]
  have s1 := hdiag k hk kd hkd
  have s2 := hdiag k⁻¹ hki kd⁻¹ hkdi
  have q1 := hpar p₁ t₁ (at_of_one_sub_smul hp₁) ht₁
  have q2 := hpar p₂ t₂ (at_of_one_sub_smul hp₂) ht₂
  have hb := box_mem_SB hφ₀ hφ₀
  have f1 : c k * c k⁻¹ = 1 := by
    have h := s1.mul s2 (hspl.pres _)
    rw [← map_mul, mul_inv_cancel, map_one] at h
    exact h.unique (scales_one v Λ) hb hΛ0
  have h := ((s1.mul q1 (hspl.pres _)).mul s2 (hspl.pres _)).mul q2 (hspl.pres _)
  rw [← map_mul, ← map_mul, ← map_mul, ← hdec, mul_one, mul_one, f1] at h
  exact (hdiag g hg gd hgd).unique h hb hΛ0

end GlobalTheory.InertLagChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTransformingCharacterEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_transforming_character_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    (∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), l φ ≠ 0) →
    ∀ c : UA σ G.V'.J → ℂ, (∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = c g * l φ) →
    ∀ g ∈ UAt σ G.V' (evFin F v), c g = 1 := by
  first | exact @GlobalTheory.InertLagChar.char_eq_one | exact GlobalTheory.InertLagChar.char_eq_one | (intros; apply GlobalTheory.InertLagChar.char_eq_one <;> assumption)
end

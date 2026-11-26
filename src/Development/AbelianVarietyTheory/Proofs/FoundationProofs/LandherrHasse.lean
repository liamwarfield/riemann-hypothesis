module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteOrthonormal

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_orthonormal (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ b : Fin W.rank → W.V, LinearIndependent E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry hc W hs hp
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, Module.Basis.linearIndependent _, fun a c => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  change ∑ i, star ((Pi.single a (1 : E) : Fin W.rank → E) i) * (Pi.single c (1 : E) : Fin W.rank → E) i = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

end

theorem landherrHasse : ∀ D : D7, LandherrHasse D := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => exists_orthonormal (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteOrthonormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse
open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd (D : D7) : GenusMassStd D :=
  GlobalTheory.DefiniteMass.mass_eq_massI D

theorem genusMassStd_of_landherrHasse :
    (∀ D : D7, LandherrHasse D) → ∀ D : D7, GenusMassStd D :=
  fun _ D => genusMassStd D

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjBlockLowerMemPrincipalSeriesCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjBlockLowerMemPrincipalSeriesCongruence
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType

theorem conj_blockLower_mem_theta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ g ∈ grp ψ, (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → g.val a b = 0) → z⁻¹ * g * z ∈ grp ψ ∧ theta ψ (z⁻¹ * g * z) = theta ψ g := by
  intro k _ _ _ _ n ψ r ϖ hϖ hv z hz g hg hup
  set d : Fin n → k := fun i => if (i : ℕ) < r then ϖ else 1 with hd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [hϖ]
  have h2 : diagonal (fun i => (d i)⁻¹) * z.val = 1 := by
    rw [hz, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd0 i)
  have hzi : (z⁻¹).val = diagonal (fun i => (d i)⁻¹) := by
    calc (z⁻¹).val = (diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by rw [h2, Matrix.one_mul]
      _ = diagonal (fun i => (d i)⁻¹) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hent : ∀ i j, (z⁻¹ * g * z).val i j = (d i)⁻¹ * g.val i j * d j := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hzi, hz, mul_diagonal, diagonal_mul]
  have hupper : ∀ i j : Fin n, i < j → (z⁻¹ * g * z).val i j = g.val i j := by
    intro i j hij
    rw [hent]
    have hij' : (i : ℕ) < j := hij
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]; field_simp
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · have hj : ¬ (j : ℕ) < r := by omega
      simp only [hd, if_neg hi, if_neg hj]; simp
  have hle : ∀ i j, valuation k ((z⁻¹ * g * z).val i j) ≤ valuation k (g.val i j) := by
    intro i j
    rw [hent]
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]
        have : ϖ⁻¹ * g.val i j * ϖ = g.val i j := by field_simp
        rw [this]
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_neg hi, if_pos hj, inv_one, one_mul, map_mul]
        calc valuation k (g.val i j) * valuation k ϖ ≤ valuation k (g.val i j) * 1 := by
              gcongr
          _ = _ := mul_one _
      · simp only [hd, if_neg hi, if_neg hj]; simp
  have hdet : (z⁻¹ * g * z).val.det = g.val.det := by
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]
  have hminor : ∀ m, minor (z⁻¹ * g * z) m = minor g m := by
    intro m
    simp only [minor]
    set G := g.val.toSquareBlockProp (fun i => i ≤ m) with hG
    have e : (z⁻¹ * g * z).val.toSquareBlockProp (fun i => i ≤ m) =
        of fun (i j : {a // a ≤ m}) => (d i)⁻¹ * (of fun (i j : {a // a ≤ m}) => d j * G i j) i j := by
      ext i j
      simp only [hG, toSquareBlockProp_def, toBlock_apply, of_apply, hent]
      ring
    rw [e, det_mul_column (fun i : {a // a ≤ m} => (d i)⁻¹), det_mul_row (fun j : {a // a ≤ m} => d j) G,
      ← mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one (fun (i : {a // a ≤ m}) _ => inv_mul_cancel₀ (hd0 i.1)), one_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hgk := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1)
    refine GlobalTheory.LocStd.mem_KO_iff_det.2 ⟨fun i j => ?_, by rw [hdet]; exact hgk.2⟩
    exact (Valuation.mem_integer_iff _ _).2 ((hle i j).trans ((Valuation.mem_integer_iff _ _).1 (hgk.1 i j)))
  · intro i j hij
    rw [hupper i j hij]
    exact hg.2 i j hij
  · simp only [theta, hminor]

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjBlockLowerMemPrincipalSeriesCongruenceStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_blockLower_mem_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ g ∈ grp ψ, (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → g.val a b = 0) → z⁻¹ * g * z ∈ grp ψ ∧ theta ψ (z⁻¹ * g * z) = theta ψ g := by
  first | exact @GlobalTheory.PsType.conj_blockLower_mem_theta | exact GlobalTheory.PsType.conj_blockLower_mem_theta | (intros; apply GlobalTheory.PsType.conj_blockLower_mem_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsStripClearingUpperRightPrincipalSeriesCong
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsStripClearingUpperRightPrincipalSeriesCong
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.ClearBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_congr (χ : kˣ →* ℂˣ) {x y : k} (h : valuation k x = valuation k y) : Triv χ x ↔ Triv χ y := by
  unfold Triv; rw [h]

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h) zero_le'
  rw [Valuation.zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  simp [this]

theorem res_zero_iff (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem val_det_eq_one {n r : ℕ} {M M' : Matrix (Fin n) (Fin n) k}
    (hM : ∀ i j, valuation k (M i j) ≤ 1) (hM' : ∀ i j, valuation k (M' i j) ≤ 1)
    (hsame : ∀ i j : Fin n, ((i : ℕ) < r ↔ (j : ℕ) < r) → M i j = M' i j)
    (hur : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (M i j) < 1)
    (hur' : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (M' i j) < 1)
    (hd : valuation k M.det = 1) : valuation k M'.det = 1 := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨M i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨M' i j, (Valuation.mem_integer_iff _ _).2 (hM' i j)⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hA' : (algebraMap 𝒪[k] k).mapMatrix A' = M' := rfl
  have hI := Valuation.integer.integers (valuation k)
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝒪[k], (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (B i j : k) < 1) →
      ((IsLocalRing.residue 𝒪[k]).mapMatrix B).det =
        (toSquareBlockProp ((IsLocalRing.residue 𝒪[k]).mapMatrix B) (fun i => r ≤ (i : ℕ))).det *
        (toSquareBlockProp ((IsLocalRing.residue 𝒪[k]).mapMatrix B) (fun i => ¬ r ≤ (i : ℕ))).det := by
    intro B hB
    refine twoBlockTriangular_det _ _ fun i hi j hj => ?_
    exact (res_zero_iff _).2 (hB i j (by omega) hj)
  have e1 : ((IsLocalRing.residue 𝒪[k]).mapMatrix A).det = ((IsLocalRing.residue 𝒪[k]).mapMatrix A').det := by
    rw [key A hur, key A' hur']
    congr 2
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toSquareBlockProp_def, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      congr 1; exact Subtype.ext (hsame i j (by omega))
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toSquareBlockProp_def, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      congr 1; exact Subtype.ext (hsame i j (by omega))
  have u1 : IsUnit A.det := hI.isUnit_iff_valuation_eq_one.2 (by rw [RingHom.map_det, hA, hd])
  have u2 : IsUnit A'.det := by
    by_contra hc
    have h0 : IsLocalRing.residue 𝒪[k] A'.det = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hc
    rw [RingHom.map_det, ← e1, ← RingHom.map_det, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 u1
  have := hI.isUnit_iff_valuation_eq_one.1 u2
  rwa [RingHom.map_det, hA'] at this

end GlobalTheory.PsType.ClearBlock

namespace GlobalTheory.PsType


open ClearBlock in
theorem clear_upper_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), Ordered ψ → Cut ψ r → ∀ j ∈ grp ψ, ∃ y ∈ strip ψ r ϖ 0,
      ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → (y⁻¹ * j).val a b = 0 := by
  intro k _ _ _ _ n ψ r ϖ hord hcut g hg
  have hint : ∀ a b, valuation k (g.val a b) ≤ 1 := GlobalTheory.BlockType.val_le_one_of_mem_KO hg.1
  have hur : ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → valuation k (g.val a b) < 1 := by
    intro a b ha hb
    refine lt_of_le_of_ne (hint a b) fun h1 => hcut a b ha hb ?_
    exact (triv_congr _ (h1.trans (map_one _).symm)).1 (hg.2 a b (Fin.lt_iff_val_lt_val.2 (by omega)))
  have hdet : valuation k g.val.det = 1 := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1).2
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin n) (Fin n) k, ∀ a b, Dm a b = if ((a : ℕ) < r ↔ (b : ℕ) < r) then g.val a b else 0 :=
    ⟨fun a b => _, fun _ _ => rfl⟩
  obtain ⟨Um, hUm⟩ : ∃ Um : Matrix (Fin n) (Fin n) k, ∀ a b, Um a b = if r ≤ (a : ℕ) ∧ (b : ℕ) < r then 0 else g.val a b :=
    ⟨fun a b => _, fun _ _ => rfl⟩
  have hDint : ∀ a b, valuation k (Dm a b) ≤ 1 := fun a b => by
    rw [hDm]; split_ifs
    · exact hint a b
    · simp
  have hUint : ∀ a b, valuation k (Um a b) ≤ 1 := fun a b => by
    rw [hUm]; split_ifs
    · simp
    · exact hint a b
  have hDdet : valuation k Dm.det = 1 :=
    val_det_eq_one hint hDint (fun a b h => by rw [hDm, if_pos h]) hur
      (fun a b ha hb => by rw [hDm, if_neg (by omega)]; simp) hdet
  have hUdet : valuation k Um.det = 1 :=
    val_det_eq_one hint hUint (fun a b h => by rw [hUm, if_neg (by omega)]) hur
      (fun a b ha hb => by rw [hUm, if_neg (by omega)]; exact hur a b ha hb) hdet
  obtain ⟨Dg, hDK, hDv⟩ := GlobalTheory.LocStd.mem_image_KO.2
    ⟨fun a b => (Valuation.mem_integer_iff _ _).2 (hDint a b), hDdet⟩
  obtain ⟨Ug, hUK, hUv⟩ := GlobalTheory.LocStd.mem_image_KO.2
    ⟨fun a b => (Valuation.mem_integer_iff _ _).2 (hUint a b), hUdet⟩
  have hD : Dg ∈ grp ψ := ⟨hDK, fun a b hab => by
    rw [hDv, hDm]; split_ifs
    · exact hg.2 a b hab
    · exact triv_zero _⟩
  have hU : Ug ∈ grp ψ := ⟨hUK, fun a b hab => by
    rw [hUv, hUm]; split_ifs
    · exact triv_zero _
    · exact hg.2 a b hab⟩
  have hy : Ug * Dg⁻¹ ∈ grp ψ := GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hord Ug hU _ (GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ hord Dg hD)
  set Di : Matrix (Fin n) (Fin n) k := ((Dg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hDi
  have hDi1 : Dm * Di = 1 := by rw [← hDv]; exact Dg.mul_inv
  have hDi2 : Di * Dm = 1 := by rw [← hDv]; exact Dg.inv_mul
  let Q : Matrix (Fin n) (Fin n) k := diagonal fun a => if (a : ℕ) < r then (0 : k) else 1
  have hDQ : Dm * Q = Q * Dm := by
    ext a b
    simp only [Q, mul_diagonal, diagonal_mul, hDm]
    by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb]
  have hQDi : Di * Q = Q * Di := calc
    Di * Q = Di * Q * (Dm * Di) := by rw [hDi1, Matrix.mul_one]
    _ = Di * (Dm * Q) * Di := by rw [hDQ]; simp only [Matrix.mul_assoc]
    _ = (Di * Dm) * Q * Di := by simp only [Matrix.mul_assoc]
    _ = Q * Di := by rw [hDi2, Matrix.one_mul]
  have hDioff : ∀ l b : Fin n, r ≤ (l : ℕ) → (b : ℕ) < r → Di l b = 0 := by
    intro l b hl hb
    have := congrFun (congrFun hQDi l) b
    simp only [Q, mul_diagonal, diagonal_mul, if_pos hb, if_neg (Nat.not_lt.2 hl)] at this
    simpa using this.symm
  refine ⟨Ug * Dg⁻¹, ?_, ?_⟩
  · have hyv : (Ug * Dg⁻¹).val = (Um - Dm) * Di + 1 := by
      rw [Units.val_mul, hUv, Matrix.sub_mul, hDi1, sub_add_cancel]
    intro a b
    split_ifs with hab
    · rw [pow_zero, one_mul]
      exact ⟨GlobalTheory.BlockType.val_le_one_of_mem_KO hy.1 a b,
        hy.2 a b (Fin.lt_iff_val_lt_val.2 (by omega))⟩
    · rw [hyv, Matrix.add_apply, Matrix.mul_apply]
      rw [Finset.sum_eq_zero, zero_add]
      intro l _
      rw [Matrix.sub_apply]
      by_cases ha : (a : ℕ) < r
      · have hb : (b : ℕ) < r := by omega
        by_cases hl : (l : ℕ) < r
        · simp [hUm, hDm, ha, hl, Nat.not_le.2 ha]
        · rw [hDioff l b (by omega) hb, mul_zero]
      · by_cases hl : (l : ℕ) < r <;> simp [hUm, hDm, ha, hl]
  · intro a b ha hb
    set Ui : Matrix (Fin n) (Fin n) k := ((Ug⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hUi
    have hUi1 : Ui * Um = 1 := by rw [← hUv]; exact Ug.inv_mul
    have e : ((Ug * Dg⁻¹)⁻¹ * g).val = Dm + Dm * Ui * (g.val - Um) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, hDv, Matrix.mul_sub, Matrix.mul_assoc Dm Ui Um, hUi1,
        Matrix.mul_one, add_sub_cancel]
    rw [e, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero]
    · rw [hDm, if_neg (by omega), zero_add]
    · intro l _
      rw [Matrix.sub_apply, hUm, if_neg (by omega), sub_self, mul_zero]

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsStripClearingUpperRightPrincipalSeriesCongStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strip_clearing_upperRight_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), Ordered ψ → Cut ψ r → ∀ j ∈ grp ψ, ∃ y ∈ strip ψ r ϖ 0, ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → (y⁻¹ * j).val a b = 0 := by
  first | exact @GlobalTheory.PsType.clear_upper_right | exact GlobalTheory.PsType.clear_upper_right | (intros; apply GlobalTheory.PsType.clear_upper_right <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntegralHermitianCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIff
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CongNorm

variable {E : Type} [Field E] [NumberField E]

theorem val_mul_mul_le {R Γ : Type} [CommRing R] [LinearOrderedCommMonoidWithZero Γ] (v : Valuation R Γ) {n : ℕ}
    (A X B : Matrix (Fin n) (Fin n) R) (c : Γ) (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hX : ∀ i j, v (X i j) ≤ c) (i j : Fin n) : v ((A * X * B) i j) ≤ c := by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun l _ => ?_
  rw [Matrix.mul_apply, v.map_mul]
  have h1 : v (∑ m, A i m * X m l) ≤ c := v.map_sum_le fun m _ => by
    rw [v.map_mul]
    calc v (A i m) * v (X m l) ≤ 1 * c := mul_le_mul' (hA i m) (hX m l)
      _ = c := one_mul c
  calc v (∑ m, A i m * X m l) * v (B l j) ≤ c * 1 := mul_le_mul' h1 (hB l j)
    _ = c := mul_one c

theorem val_le_one_of_mem_KGL (w : Pl E) {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    Valued.v (g.val i j) ≤ 1 := by
  obtain ⟨y, rfl⟩ := hg
  have : ((Formalism.UG.bc (n := Fin n) (Ov E w).subtype y).val i j) = ((y.val i j : Ov E w) : w.adicCompletion E) := rfl
  rw [this]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := w)).1 (y.val i j).2

theorem conj_bound (w : Pl E) {n : ℕ} (c : WithZero (Multiplicative ℤ)) {a x : GLw n w} (ha : a ∈ GlobalTheory.LFun.KGL w (n := n))
    (hx : ∀ i j, Valued.v ((x.val - 1) i j) ≤ c) (i j : Fin n) :
    Valued.v (((a⁻¹ * x * a).val - 1) i j) ≤ c := by
  have e : (a⁻¹ * x * a).val - 1 = (a⁻¹).val * (x.val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, Units.val_mul, Units.val_mul]
  rw [e]
  exact val_mul_mul_le Valued.v _ _ _ c (val_le_one_of_mem_KGL w (inv_mem ha))
    (val_le_one_of_mem_KGL w ha) hx i j

end GlobalTheory.KapOrb.CongNorm

namespace GlobalTheory.KapOrb

theorem conj_mem_congSet_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ)
    (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  intro E _ _ _ w n m h k hk
  have hmem : k⁻¹ * h * k ∈ GlobalTheory.LFun.KGL w (n := n) ↔ h ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
  have hb : ∀ g : GLw n w, (∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(m : ℤ))) ↔ ∀ i j, Valued.v ((g.val - 1) i j) ≤ WithZero.exp (-(m : ℤ)) := fun g => by
    simp only [Matrix.sub_apply]
  simp only [congSet, Set.mem_ofPred_eq, hb, hmem]
  refine and_congr_right fun _ => ⟨fun H => ?_, fun H => CongNorm.conj_bound w _ hk H⟩
  have e : h = k⁻¹⁻¹ * (k⁻¹ * h * k) * k⁻¹ := by group
  rw [e]
  exact CongNorm.conj_bound w _ (inv_mem hk) H

end GlobalTheory.KapOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIffStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ) (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  first | exact @GlobalTheory.KapOrb.conj_mem_congSet_iff | exact GlobalTheory.KapOrb.conj_mem_congSet_iff | (intros; apply GlobalTheory.KapOrb.conj_mem_congSet_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeSelfDualOfUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeSelfDualOfUnitary
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.SDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_int {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (t : w.adicCompletion E) (ht : t ∈ w.adicCompletionIntegers E) : cj w t ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ⊢
  have h1 : e.symm t ∈ (algebraMap K.O K.E).range := (hB.2.1 _).2 (by simpa using ht)
  obtain ⟨o, ho⟩ := h1
  obtain ⟨o', ho'⟩ := K.c_int o
  have h2 : cj w t = e (algebraMap K.O K.E o') := by
    rw [← ho', ho, hB.1, RingEquiv.apply_symm_apply]
  rw [h2]
  exact (hB.2.1 _).1 ⟨o', rfl⟩

theorem cj_cj {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (t : w.adicCompletion E) : cj w (cj w t) = t := by
  obtain ⟨a, rfl⟩ := e.surjective t
  rw [← hB.1, ← hB.1, K.c_c]

theorem stdH_unitary {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hM : Formalism.UG.cT (cj w) M * 1 * M = 1)
    (v v' : Fin n → w.adicCompletion E) : stdH w (M *ᵥ v) (M *ᵥ v') = stdH w v v' := by
  have hM' : Mᵀ * M.map (cj w) = 1 := by
    have h := congrArg (fun X => X.map (cj w)) hM
    simp only [Formalism.UG.cT, Matrix.mul_one] at h
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
    have hid : (cj w) ∘ (cj w) = id := funext (cj_cj hB)
    rw [hid, Matrix.map_id, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hc : ∀ u : Fin n → w.adicCompletion E, (fun k => cj w ((M *ᵥ u) k)) = M.map (cj w) *ᵥ (fun k => cj w (u k)) := by
    intro u; funext k
    exact RingHom.map_mulVec (cj w) M u k
  have hs : ∀ u u' : Fin n → w.adicCompletion E, stdH w u u' = u ⬝ᵥ (fun k => cj w (u' k)) := fun _ _ => rfl
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hM', Matrix.vecMul_one]

theorem pullLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ g ∈ UL n w, GlobalTheory.UnitLemma.IsLat K.O K.E (pullLat w B ψ g) ∧ ∀ y, y ∈ pullLat w B ψ g ↔ ∀ z ∈ pullLat w B ψ g, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ w hw K e hB B x n ψ hlin hherm g hg
  set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (g⁻¹ : GLw n w).val with hMdef
  have hgi : g⁻¹ ∈ UL n w := inv_mem hg
  have hMu : Formalism.UG.cT (cj w) M * 1 * M = 1 := by
    have h := hgi
    unfold UL at h
    rw [if_neg hw] at h
    exact h
  have hMg : M * g.val = 1 := by rw [hMdef]; exact Units.inv_mul g
  have hgM : g.val * M = 1 := by rw [hMdef]; exact Units.mul_inv g
  have hint : ∀ a : K.E, a ∈ (algebraMap K.O K.E).range ↔ e a ∈ w.adicCompletionIntegers E := by
    intro a; rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hB.2.1 a
  let φ : B.A →+ (Fin n → w.adicCompletion E) :=
    (Matrix.mulVecLin M).toAddMonoidHom.comp ψ.toAddMonoidHom
  have hφ : ∀ y, φ y = M *ᵥ ψ y := fun y => rfl
  have hφs : ∀ (c : K.E) y, φ (c • y) = e c • φ y := by
    intro c y; rw [hφ, hφ, hlin, Matrix.mulVec_smul]
  have hφinj : ∀ y z, φ y = φ z → y = z := by
    intro y z h
    rw [hφ, hφ] at h
    apply ψ.injective
    have := congrArg (fun u => g.val *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec, hgM, Matrix.one_mulVec] using this
  let pre : (Fin n → w.adicCompletion E) → B.A := fun v => ψ.symm (g.val *ᵥ v)
  have hpre : ∀ v, φ (pre v) = v := by
    intro v; rw [hφ]; simp only [pre, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
  have hmem : ∀ y, y ∈ pullLat w B ψ g ↔ ∀ i, φ y i ∈ w.adicCompletionIntegers E := by
    intro y
    have key : y ∈ pullLat w B ψ g ↔ ∀ (c : K.O) (i : Fin n),
        ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E := Iff.rfl
    rw [key]
    constructor
    · intro h i
      have := h 1 i
      rwa [one_smul] at this
    · intro h c i
      rw [← algebraMap_smul K.E c y, ← hMdef, ← hφ, hφs, Pi.smul_apply, smul_eq_mul]
      exact mul_mem ((hint _).1 ⟨c, rfl⟩) (h i)
  let z : Fin n → B.A := fun i => pre (Pi.single i 1)
  have hz : ∀ i, z i ∈ pullLat w B ψ g := by
    intro i; rw [hmem]; intro j
    simp only [z, hpre, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hdecomp : ∀ (a : Fin n → K.E) y, (∀ i, e (a i) = φ y i) → y = ∑ i, a i • z i := by
    intro a y ha
    apply hφinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext j
    rw [Finset.sum_apply]
    simp only [hφs, z, hpre, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (ha j).symm
  have hsd : ∀ y, (∀ i, φ y i ∈ w.adicCompletionIntegers E) ↔
      ∀ z' ∈ pullLat w B ψ g, B.herm x y z' ∈ (algebraMap K.O K.E).range := by
    intro y
    have hh : ∀ z', B.herm x y z' ∈ (algebraMap K.O K.E).range ↔ stdH w (φ y) (φ z') ∈ w.adicCompletionIntegers E := by
      intro z'
      rw [hint, ← hherm, hφ, hφ, SDual.stdH_unitary hB M hMu]
    constructor
    · intro hy z' hz'
      rw [hh]
      rw [hmem] at hz'
      unfold stdH
      exact sum_mem fun k _ => mul_mem (hy k) (SDual.cj_int hB _ (hz' k))
    · intro h i
      have := (hh _).1 (h (z i) (hz i))
      have hcalc : stdH w (φ y) (φ (z i)) = φ y i := by
        rw [show φ (z i) = Pi.single i 1 from hpre _]
        unfold stdH
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      rwa [hcalc] at this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.fg_def]
    refine ⟨Set.range z, Set.finite_range z, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩; exact hz i
    · intro y hy
      rw [hmem] at hy
      have hc : ∀ i, ∃ o : K.O, e (algebraMap K.O K.E o) = φ y i := by
        intro i
        obtain ⟨o, ho⟩ := (hint (e.symm (φ y i))).2 (by simpa using hy i)
        exact ⟨o, by rw [ho, RingEquiv.apply_symm_apply]⟩
      choose o ho using hc
      rw [hdecomp (fun i => algebraMap K.O K.E (o i)) y ho]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro y _
    rw [hdecomp (fun i => e.symm (φ y i)) y (fun i => by simp)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hz i))
  · intro y
    rw [hmem]
    exact hsd y

end GlobalTheory.KapOrb.SDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeSelfDualOfUnitaryStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_selfDual_of_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ g ∈ UL n w, GlobalTheory.UnitLemma.IsLat K.O K.E (pullLat w B ψ g) ∧ ∀ y, y ∈ pullLat w B ψ g ↔ ∀ z ∈ pullLat w B ψ g, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  first | exact @GlobalTheory.KapOrb.SDual.pullLat_selfDual | exact GlobalTheory.KapOrb.SDual.pullLat_selfDual | (intros; apply GlobalTheory.KapOrb.SDual.pullLat_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImage
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb

theorem pullLat_mul_eq_mulLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  intro E _ _ _ w K B n ψ h g a ha
  have hinv : ∀ z, ψ (((a⁻¹ : B.Aˣ) : B.A) * z) = (h⁻¹ : GLw n w).val *ᵥ ψ z := by
    intro z
    have h1 := ha (((a⁻¹ : B.Aˣ) : B.A) * z)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec]
    have : ((h⁻¹ : GLw n w).val * h.val) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
  have key : ∀ y, y ∈ pullLat w B ψ (h * g) ↔ ((a⁻¹ : B.Aˣ) : B.A) * y ∈ pullLat w B ψ g := by
    intro y
    show (∀ (c : K.O) (i : Fin n), (((h * g)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
      (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y))) i ∈
        w.adicCompletionIntegers E)
    have e1 : ∀ c : K.O, ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y)) = (h⁻¹ : GLw n w).val *ᵥ ψ (c • y) := by
      intro c
      rw [← hinv, Algebra.mul_smul_comm]
    have e2 : ((h * g)⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * (h⁻¹ : GLw n w).val := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    simp only [e1, e2, Matrix.mulVec_mulVec]
  ext y
  constructor
  · intro hy
    refine ⟨((a⁻¹ : B.Aˣ) : B.A) * y, (key y).1 hy, ?_⟩
    show (a : B.A) * (((a⁻¹ : B.Aˣ) : B.A) * y) = y
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨z, hz, rfl⟩
    rw [key]
    show ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * z) ∈ pullLat w B ψ g
    rw [← mul_assoc, Units.inv_mul, one_mul]
    exact hz

end GlobalTheory.KapOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImageStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_mul_eq_mulLeftImage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_eq_mulLat | exact GlobalTheory.KapOrb.pullLat_mul_eq_mulLat | (intros; apply GlobalTheory.KapOrb.pullLat_mul_eq_mulLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCentralizerStabilizerEqLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCentralizerStabilizerEqLatticeStabilizer
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbWeights

theorem mem_stabLat_iff_mulLat_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (t : Aˣ) (L : Submodule O A) :
    t ∈ GlobalTheory.UnitLemma.stabLat O L ↔ GlobalTheory.UnitLemma.mulLat O (t : A) L = L := by
  constructor
  · intro ht
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (ht y).1 hy
    · intro y hy
      have h1 : ((t⁻¹ : Aˣ) : A) * y ∈ L := by
        rw [ht]
        rw [← mul_assoc, Units.mul_inv, one_mul]
        exact hy
      refine ⟨((t⁻¹ : Aˣ) : A) * y, h1, ?_⟩
      change (t : A) * (((t⁻¹ : Aˣ) : A) * y) = y
      rw [← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      change (t : A) * z = (t : A) * y at hzy
      have : z = y := by
        have := congrArg (fun w => ((t⁻¹ : Aˣ) : A) * w) hzy
        simpa [← mul_assoc] using this
      rw [← this]
      exact hz

theorem relIndex_stab_eq_relIndex_stabLat : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ (h * h') = τ h * τ h') → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ h = τ h' → h = h') → (∀ h ∈ twCent (MonoidHom.id G) δ, h ∈ cptPart (twCent (MonoidHom.id G) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits O A) → ∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb) := by
  intro G _ _ Kg δ O A _ _ _ Tb M τ hK hM hτ hsurj hmul hinj hcpt g
  set T := twCent (MonoidHom.id G) δ with hT
  have hone : τ 1 = 1 := by
    have := hmul 1 T.one_mem 1 T.one_mem
    rw [one_mul] at this
    exact (mul_eq_left.mp this.symm)
  let φ : T →* Aˣ :=
    { toFun := fun h => τ h
      map_one' := hone
      map_mul' := fun a b => hmul a a.2 b b.2 }
  have hφ : ∀ x : T, φ x = τ x := fun _ => rfl
  have hinjφ : Function.Injective φ := fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab)
  have hCT : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  rw [← Subgroup.relIndex_subgroupOf (H := T ⊓ Kg.map (MulAut.conj g).toMonoidHom) hCT,
    ← Subgroup.relIndex_map_map_of_injective _ _ hinjφ]
  congr 1
  · ext t
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, ⟨_, k, hk, hkx⟩, rfl⟩
      refine ⟨?_, (hτ x x.2).1⟩
      rw [hφ, mem_stabLat_iff_mulLat_eq, ← (hτ x x.2).2 g]
      have : (x : G) * g = g * k := by
        rw [← hkx]
        simp [mul_assoc]
      rw [this, hK g k hk]
    · rintro ⟨hs, hb⟩
      obtain ⟨h, hh, rfl⟩ := hsurj t hb
      refine ⟨⟨h, hh⟩, ⟨hh, g⁻¹ * (h * g), ?_, ?_⟩, rfl⟩
      · apply hM
        rw [mem_stabLat_iff_mulLat_eq, ← (hτ h hh).2 g] at hs
        exact hs.symm
      · simp [mul_assoc]
  · ext t
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hcpt x x.2).1 hx, (hτ x x.2).1⟩
    · rintro ⟨hi, hb⟩
      obtain ⟨h, hh, rfl⟩ := hsurj t hb
      exact ⟨⟨h, hh⟩, (hcpt h hh).2 hi, rfl⟩

end GlobalTheory.OrbWeights
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCentralizerStabilizerEqLatticeStabilizerStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_centralizerStabilizer_eq_latticeStabilizer : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ (h * h') = τ h * τ h') → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ h = τ h' → h = h') → (∀ h ∈ twCent (MonoidHom.id G) δ, h ∈ cptPart (twCent (MonoidHom.id G) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits O A) → ∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb) := by
  first | exact @GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat | exact GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat | (intros; apply GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCoset
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.PullInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_KGL_of_int {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_pullLat_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ} (ψ : B.A ≃+ (Fin n → w.adicCompletion E))
    (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (g : GLw n w) (y : B.A) :
    y ∈ pullLat w B ψ g ↔ ∀ i, ((g⁻¹ : GLw n w).val *ᵥ ψ y) i ∈ w.adicCompletionIntegers E := by
  constructor
  · intro h i
    simpa using h 1 i
  · intro h c i
    have hc : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (hB.2.1 _).1 ⟨c, rfl⟩
    have hc' : e (algebraMap K.O K.E c) ∈ w.adicCompletionIntegers E := hc
    change ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E
    rw [← algebraMap_smul K.E c y, hψ, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem hc' (h i)

theorem entries_int_of_le (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ} (ψ : B.A ≃+ (Fin n → w.adicCompletion E))
    (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (g g' : GLw n w)
    (h : pullLat w B ψ g' ≤ pullLat w B ψ g) (i j : Fin n) :
    (g⁻¹ * g').val i j ∈ w.adicCompletionIntegers E := by
  set y := ψ.symm (g'.val *ᵥ Pi.single j 1) with hy
  have hψy : ψ y = g'.val *ᵥ Pi.single j 1 := by simp [hy]
  have hy' : y ∈ pullLat w B ψ g' := by
    rw [mem_pullLat_iff w hB B ψ hψ, hψy]
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := (mem_pullLat_iff w hB B ψ hψ g y).1 (h hy') i
  rw [hψy, Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at this
  simpa using this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) →
    ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ _ w K e hB B n ψ hψ g g' h
  refine mem_KGL_of_int w _ (entries_int_of_le w hB B ψ hψ g g' h.ge) ?_
  intro a b
  have e1 : (g⁻¹ * g')⁻¹ = g'⁻¹ * g := by group
  rw [e1]
  exact entries_int_of_le w hB B ψ hψ g' g h.le a b

end GlobalTheory.KapOrb.PullInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCosetStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.KapOrb.PullInj.main | exact GlobalTheory.KapOrb.PullInj.main | (intros; apply GlobalTheory.KapOrb.PullInj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqWeightedLatticeOrbitCount
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqWeightedLatticeOrbitCount
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbReindex

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) (y : A) :
    y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [LinearMap.mulLeft_apply, Units.inv_mul_cancel_left] using hx
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, Units.mul_inv_cancel_left]⟩

theorem stabLat_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) :
    GlobalTheory.UnitLemma.stabLat O (GlobalTheory.UnitLemma.mulLat O (t : A) L) = GlobalTheory.UnitLemma.stabLat O L := by
  ext s
  change (∀ y, y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ (s : A) * y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L) ↔
    (∀ y, y ∈ L ↔ (s : A) * y ∈ L)
  simp only [mem_mulLat_unit]
  constructor
  · intro h y
    have e : ((t⁻¹ : Aˣ) : A) * ((s : A) * ((t : A) * y)) = (s : A) * y := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    have := h ((t : A) * y)
    rwa [Units.inv_mul_cancel_left, e] at this
  · intro h y
    rw [h (((t⁻¹ : Aˣ) : A) * y), mul_left_comm]

theorem cast_finsum_rat {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · simpa using map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support (fun a => ((u a : ℚ) : ℂ))).Finite := by
      have : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u := by
        ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.OrbReindex

namespace GlobalTheory.OrbReindex
open GlobalTheory.UnitLemma

theorem finsum_ite_subtype {α : Type*} (p : α → Prop) (c : α → ℂ) :
    (∑ᶠ q, if p q then c q else 0) = ∑ᶠ s : {q // p q}, c s.1 := by
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]

theorem twOrb_eq_orbSum : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  intro G _ _ Kg δ f O A _ _ _ Tb X M τ hK hinj hsurj hT hTs havg hidx

  have hX : ∀ h ∈ twCent (MonoidHom.id G) δ, ∀ g : G, (M (h * g) ∈ X ↔ M g ∈ X) := by
    intro h hh g
    have hc : h * δ = δ * h := hh
    have hc' : h⁻¹ * δ * h = δ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have e : avg (fun k : Kg => f ((h * g * k)⁻¹ * δ * (MonoidHom.id G) (h * g * k))) =
        avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) := by
      congr 1
      funext k
      congr 1
      simp only [MonoidHom.id_apply]
      calc (h * g * (k : G))⁻¹ * δ * (h * g * k) = (g * (k : G))⁻¹ * (h⁻¹ * δ * h) * (g * k) := by group
        _ = _ := by rw [hc']
    have := (havg (h * g)).symm.trans (e.trans (havg g))
    by_cases a : M (h * g) ∈ X <;> by_cases b : M g ∈ X <;> simp_all
  let r : X → X → Prop := fun L L' => ∃ t ∈ Tb, (L' : Submodule O A) = mulLat O (t : A) (L : Submodule O A)
  have hw : ∀ L L' : X, Relation.EqvGen r L L' → stabLat O L.1 = stabLat O L'.1 := by
    intro L L' h
    induction h with
    | rel a b hab =>
      obtain ⟨t, -, ht⟩ := hab
      rw [ht, stabLat_mulLat_unit]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} → Orb O Tb X := fun q => Quot.mk r ⟨M (Quotient.out q.1), q.2⟩
  let ψ : Orb O Tb X → DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) :=
    Quot.lift (fun L : X => DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj L.1 L.2))) (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨t, ht, hLL⟩
      obtain ⟨h, hh, rfl⟩ := hTs t ht
      have hg := Classical.choose_spec (hsurj L hL)
      have hg' := Classical.choose_spec (hsurj L' hL')
      set g := Classical.choose (hsurj L hL)
      set g' := Classical.choose (hsurj L' hL')
      have hMM : M (h * g) = M g' := by
        rw [(hT h hh).2, hg, hg']
        exact hLL.symm
      have hk := hinj _ _ hMM
      show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g = DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g'
      rw [DoubleCoset.eq]
      exact ⟨h, hh, _, hk, by group⟩)
  have hleft : ∀ q : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, ψ (φ q) = q.1 := by
    intro q
    show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj (M (Quotient.out q.1)) q.2)) = q.1
    have hg := Classical.choose_spec (hsurj (M (Quotient.out q.1)) q.2)
    set g := Classical.choose (hsurj (M (Quotient.out q.1)) q.2)
    have hk := hinj _ _ hg.symm
    rw [← DoubleCoset.out_eq' q.1, DoubleCoset.eq]
    exact ⟨1, (twCent (MonoidHom.id G) δ).one_mem, _, Kg.inv_mem hk, by group⟩
  have hinjφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    rw [← hleft a, ← hleft b, hab]
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨L, hL⟩
    obtain ⟨g, rfl⟩ := hsurj L hL
    obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id G) δ) Kg g
    have hM : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) = mulLat O (τ h : A) (M g) := by
      rw [hout, hK _ _ hk, (hT h hh).2]
    have hmem : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) ∈ X := by
      rw [hout, hK _ _ hk, hX h hh]
      exact hL
    refine ⟨⟨DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g, hmem⟩, ?_⟩
    exact (Quot.sound ⟨τ h, (hT h hh).1, hM⟩).symm
  let e : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} ≃ Orb O Tb X := Equiv.ofBijective φ ⟨hinjφ, hsurjφ⟩

  have hwt : ∀ s : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, stabLat O (Quot.out (e s)).1 = stabLat O (M (Quotient.out s.1)) := by
    intro s
    have h1 : Quot.mk r (Quot.out (φ s)) = φ s := Quot.out_eq _
    exact hw _ _ (Quot.eqvGen_exact h1)
  unfold twOrb orbSum
  simp only [havg, hidx]
  rw [cast_finsum_rat, ← finsum_comp_equiv e]
  simp only [hwt, one_mul, mul_ite, mul_one, mul_zero]
  simp only [Rat.cast_natCast]
  exact finsum_ite_subtype _ _

end GlobalTheory.OrbReindex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqWeightedLatticeOrbitCountStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_eq_weighted_lattice_orbit_count : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  first | exact @GlobalTheory.OrbReindex.twOrb_eq_orbSum | exact GlobalTheory.OrbReindex.twOrb_eq_orbSum | (intros; apply GlobalTheory.OrbReindex.twOrb_eq_orbSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGL
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

theorem entry_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) (i j : Fin n) : (k : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨k0, rfl⟩ := hk
  exact (k0.val i j).2

theorem mulVec_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) {v : Fin n → L} (hv : ∀ i, v i ∈ O) (i : Fin n) :
    ((k : Matrix (Fin n) (Fin n) L) *ᵥ v) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (entry_mem_of_mem_GLint hk i j) (hv j)

theorem pullLat_mul_of_mem_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  intro E _ _ _ w K B n ψ g k hk
  have hk' : k⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hk
  ext y
  show (∀ (c : K.O) (i : Fin n), (((g * k)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
    (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E)
  simp only [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro h c i
    have e : (g⁻¹ : GLw n w).val *ᵥ ψ (c • y) =
        (k : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ((k⁻¹ : GLw n w).val *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y))) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_of_mem_GLint hk (fun j => h c j) i
  · intro h c i
    exact mulVec_mem_of_mem_GLint hk' (fun j => h c j) i

end GlobalTheory.KapOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGLStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | exact GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | (intros; apply GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCommutingOfMemNormOneTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCommutingOfMemNormOneTorus
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section
namespace GlobalTheory.KapOrb

theorem exists_unitary_of_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → ∀ s ∈ B.T, ∃ h : GLw n w, h ∈ UL n w ∧ h * γ = γ * h ∧ ∀ y, ψ ((s : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w K e B u x n γ ψ hψ s hs
  obtain ⟨hsl, hu, hh⟩ := hψ
  have hs' : (s : B.A) * B.σ (s : B.A) = 1 := hs
  let Lm : B.A → (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) := fun a =>
    { toFun := fun v => ψ (a * ψ.symm v)
      map_add' := by intro v v'; simp [mul_add]
      map_smul' := by
        intro c v
        have h1 : ψ.symm (c • v) = e.symm c • ψ.symm v := by
          apply ψ.injective
          rw [ψ.apply_symm_apply, hsl, ψ.apply_symm_apply, e.apply_symm_apply]
        simp only [RingHom.id_apply]
        rw [h1, Algebra.mul_smul_comm, hsl, e.apply_symm_apply] }
  have hLm : ∀ a y, Lm a (ψ y) = ψ (a * y) := by
    intro a y; simp [Lm]
  have hLmul : ∀ a b, Lm a ∘ₗ Lm b = Lm (a * b) := by
    intro a b; ext v; simp [Lm, mul_assoc]
  have hLone : Lm 1 = LinearMap.id := by
    ext v; simp [Lm]
  let h : GLw n w :=
    ⟨LinearMap.toMatrix' (Lm (s : B.A)), LinearMap.toMatrix' (Lm ((s⁻¹ : B.Aˣ) : B.A)),
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.mul_inv, hLone, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.inv_mul, hLone, LinearMap.toMatrix'_id]⟩
  have hmv : ∀ v, h.val *ᵥ v = Lm (s : B.A) v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hpres : ∀ v v', stdH w (h.val *ᵥ v) (h.val *ᵥ v') = stdH w v v' := by
    intro v v'
    obtain ⟨y, rfl⟩ := ψ.surjective v
    obtain ⟨z, rfl⟩ := ψ.surjective v'
    rw [hmv, hmv, hLm, hLm, hh, hh]
    congr 1
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 1
    rw [map_mul]
    calc x * ((s : B.A) * y) * (B.σ (s : B.A) * B.σ z) = x * y * B.σ z * ((s : B.A) * B.σ (s : B.A)) := by ring
      _ = x * y * B.σ z := by rw [hs', mul_one]
  refine ⟨h, ?_, ?_, ?_⟩
  · unfold UL
    split_ifs
    · exact Subgroup.mem_top _
    · show cT (cj w) h.val * 1 * h.val = 1
      ext i j
      have hp := hpres (Pi.single j 1) (Pi.single i 1)
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hp
      rw [Matrix.mul_one, Matrix.mul_apply, Matrix.one_apply]
      simp only [stdH, Matrix.transpose_apply, Matrix.col_apply] at hp
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [Finset.sum_congr rfl (fun k _ => mul_comm (cj w (h.val k i)) (h.val k j)), hp]
      by_cases hij : i = j
      · subst hij; simp [Pi.single_apply]
      · rw [if_neg hij, Finset.sum_eq_zero]
        intro k _
        by_cases hk : k = j
        · subst hk; simp [Pi.single_apply, Ne.symm hij, hij]
        · simp [Pi.single_apply, hk]
  · apply Units.ext
    apply Matrix.toLin'.injective
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, rfl⟩ := ψ.surjective v
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [← hu, hmv, hmv, hLm, hLm, ← hu, mul_left_comm]
  · intro y
    rw [hmv, hLm]

end GlobalTheory.KapOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCommutingOfMemNormOneTorusStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_commuting_of_mem_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → ∀ s ∈ B.T, ∃ h : GLw n w, h ∈ UL n w ∧ h * γ = γ * h ∧ ∀ y, ψ ((s : B.A) * y) = h.val *ᵥ ψ y := by
  first | exact @GlobalTheory.KapOrb.exists_unitary_of_torus | exact GlobalTheory.KapOrb.exists_unitary_of_torus | (intros; apply GlobalTheory.KapOrb.exists_unitary_of_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCount
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

theorem twOrb_congruence_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Q.Separable → Fits w e B Q u → u = 1 + algebraMap K.O B.A t * B.g → ∀ (γ : GLw n w) (hγ : γ ∈ UL n w), IsModel w e B u x γ → twOrb (MonoidHom.id (UL n w)) (KL n w) ⟨γ, hγ⟩ (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ w hw K e hBr k t ht htk n Q B u x hsep hF hu γ hγ hM
  obtain ⟨ψ, hψ⟩ := (isModel_iff w e B u x γ).1 hM
  have hψ1 := hψ.1
  have hψ3 := hψ.2.2
  let δ : UL n w := ⟨γ, hγ⟩
  let M : UL n w → Submodule K.O B.A := fun g => pullLat w B ψ g.1
  let τ : UL n w → B.Aˣ := fun g => torusOf w B ψ g.1
  have hcomm : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, h.1 * γ = γ * h.1 := by
    intro h hh
    have := congrArg Subtype.val hh
    simpa using this
  have h1 : ∀ g kk : UL n w, kk ∈ KL n w → M (g * kk) = M g := fun g kk hk =>
    GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL E w K B n ψ g.1 kk.1 (Subgroup.mem_subgroupOf.1 hk)
  have h2 : ∀ g g' : UL n w, M g = M g' → g⁻¹ * g' ∈ KL n w := fun g g' hgg =>
    Subgroup.mem_subgroupOf.2 (by simpa using GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset E w K e hBr B n ψ hψ1 g.1 g'.1 hgg)
  have h3 : ∀ L ∈ B.X x, ∃ g, M g = L := by
    intro L hL
    obtain ⟨hlat, -, hsd⟩ := hL
    obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.lattice_integral_hermitian_completion E w hw K e hBr B x n ψ hψ1 hψ3 L hlat hsd
    exact ⟨⟨g, hg⟩, hgL⟩
  have hT : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧ ∀ y, ψ ((τ h : B.A) * y) = h.1.val *ᵥ ψ y :=
    fun h hh => GlobalTheory.T.unitary_commuting_eq_mul_normOneTorus E w hw K e B Q u x n γ ψ hF hψ h.1 h.2 (hcomm h hh)
  have h4 : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧
      ∀ g, M (h * g) = GlobalTheory.UnitLemma.mulLat K.O (τ h : B.A) (M g) :=
    fun h hh => ⟨(hT h hh).1, fun g => GlobalTheory.T.pullbackLattice_mul_eq_mulLeftImage E w K B n ψ h.1 g.1 _ (hT h hh).2⟩
  have h5 : ∀ s ∈ B.T, ∃ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h = s := by
    intro s hs
    obtain ⟨h, hU, hc, hspec⟩ := GlobalTheory.T.exists_unitary_commuting_of_mem_normOneTorus E w K e B u x n γ ψ hψ s hs
    refine ⟨⟨h, hU⟩, ?_, torusOf_spec w B ψ h s hspec⟩
    show (⟨h, hU⟩ : UL n w) * δ = δ * (MonoidHom.id (UL n w)) ⟨h, hU⟩
    exact Subtype.ext hc
  have hiff : ∀ g : UL n w, M g ∈ B.X x ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k := by
    intro g
    obtain ⟨hlat, hsd⟩ := GlobalTheory.T.pullbackLattice_selfDual_of_unitary E w hw K e hBr B x n ψ hψ1 hψ3 g.1 g.2
    rw [← GlobalTheory.T.pullbackLattice_stable_iff_principalCongruence E w hw K e hBr k t ht htk B u x n γ ψ hψ hu hγ g.1 g.2]
    exact ⟨fun h => h.2.1, fun h => ⟨hlat, h, hsd⟩⟩
  have h6 : ∀ g : UL n w, avg (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1)
      ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) = if M g ∈ B.X x then 1 else 0 := by
    intro g
    have hfun : (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1)
        ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) =
        fun _ => (if g.1⁻¹ * γ * g.1 ∈ congSet w n k then 1 else 0 : ℂ) := by
      funext kk
      rw [Set.indicator_apply]
      have hc : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 =
          (kk.1.1)⁻¹ * (g.1⁻¹ * γ * g.1) * kk.1.1 := by
        simp [δ, mul_assoc]
      have hm : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)) ∈
          ({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)) ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k := by
        show ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 ∈ congSet w n k ↔ _
        rw [hc]
        exact GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff E w n k _ _ (Subgroup.mem_subgroupOf.1 kk.2)
      by_cases h : g.1⁻¹ * γ * g.1 ∈ congSet w n k
      · rw [if_pos (hm.2 h), if_pos h]; rfl
      · rw [if_neg (fun h' => h (hm.1 h')), if_neg h]
    rw [hfun, GlobalTheory.TwOrbGood.avg_const]
    by_cases h : g.1⁻¹ * γ * g.1 ∈ congSet w n k
    · rw [if_pos h, if_pos ((hiff g).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff g).1 h'))]
  have hmul : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ,
      τ (h * h') = τ h * τ h' := by
    intro h hh h' hh'
    apply torusOf_spec
    intro y
    rw [Units.val_mul, mul_assoc, (hT h hh).2, (hT h' hh').2, Matrix.mulVec_mulVec]
    rfl
  have hinj : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ,
      τ h = τ h' → h = h' := by
    intro h hh h' hh' heq
    have hv : ∀ v, h.1.val *ᵥ v = h'.1.val *ᵥ v := by
      intro v
      obtain ⟨y, rfl⟩ := ψ.surjective v
      rw [← (hT h hh).2, ← (hT h' hh').2, heq]
    have hm : h.1.val = h'.1.val :=
      Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v)
    exact Subtype.ext (Units.ext hm)
  have hcpt : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ,
      h ∈ cptPart (twCent (MonoidHom.id (UL n w)) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
    fun h hh => GlobalTheory.T.mem_compactPart_centralizer_iff_torus_integral_units E w hw K e hBr B Q u x n γ hγ ψ hF hψ h hh
  have h7 := GlobalTheory.T.relIndex_centralizerStabilizer_eq_latticeStabilizer (KL n w) δ B.T M τ h1 h2 h4 h5 hmul hinj hcpt
  exact GlobalTheory.T.orbitalIntegral_eq_weighted_lattice_orbit_count (KL n w) δ _ B.T (B.X x) M τ h1 h2 h3 h4 h5 h6 h7

end GlobalTheory.KapOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCountStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Q.Separable → Fits w e B Q u → u = 1 + algebraMap K.O B.A t * B.g → ∀ (γ : GLw n w) (hγ : γ ∈ UL n w), IsModel w e B u x γ → twOrb (MonoidHom.id (UL n w)) (KL n w) ⟨γ, hγ⟩ (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapOrb.twOrb_congruence_eq_N | exact GlobalTheory.KapOrb.twOrb_congruence_eq_N | (intros; apply GlobalTheory.KapOrb.twOrb_congruence_eq_N <;> assumption)
end

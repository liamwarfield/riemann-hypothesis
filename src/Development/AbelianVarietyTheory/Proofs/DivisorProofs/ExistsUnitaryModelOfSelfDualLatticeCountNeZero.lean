module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactOfComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtension
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory

theorem selfDual_orthogonal_unit_step : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hLfg hLspan hdual k f hfL horth hunit hk
  have alg_inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hadd2 : ∀ y z z', h y (z + z') = h y z + h y z' := by
    intro y z z'
    rw [hsym (z + z') y, hadd, map_add (f := _), ← hsym, ← hsym]
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym (a • z) y, hsmul, map_mul, ← hsym]
  let H1 : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z,
      map_smul' := fun a y => by simp [hsmul] }
  let H2 : V → V →+ K.E := fun y => AddMonoidHom.mk' (fun z => h y z) (hadd2 y)
  have h0l : ∀ z, h 0 z = 0 := fun z => (H1 z).map_zero
  have hsub1 : ∀ a b z, h (a - b) z = h a z - h b z := fun a b z => (H1 z).map_sub a b
  have hsub2 : ∀ y a b, h y (a - b) = h y a - h y b := fun y a b => (H2 y).map_sub a b
  have hsum1 : ∀ (g : Fin k → V) z, h (∑ i, g i) z = ∑ i, h (g i) z :=
    fun g z => map_sum (H1 z) g Finset.univ
  have hsum2 : ∀ (g : Fin k → V) y, h y (∑ i, g i) = ∑ i, h y (g i) :=
    fun g y => map_sum (H2 y) g Finset.univ
  have hsmulO : ∀ (o : K.O) (v : V), (algebraMap K.O K.E o) • v = o • v :=
    fun o v => algebraMap_smul K.E o v
  have hint : ∀ y ∈ L, ∀ z ∈ L, ∃ a : K.O, h y z = algebraMap K.O K.E a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    exact ⟨a, ha.symm⟩
  have hs : ∀ i, h (f i) (f i) ≠ 0 := by
    intro i
    obtain ⟨t, ht, he⟩ := hunit i
    rw [he]
    intro h0
    apply ht.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  let M : Submodule K.O V :=
    { carrier := {y | y ∈ L ∧ ∀ i, h y (f i) = 0}
      add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, fun i => by rw [hadd, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, fun i => h0l (f i)⟩
      smul_mem' := fun o y hy => ⟨L.smul_mem o hy.1, fun i => by rw [← hsmulO, hsmul, hy.2 i, mul_zero]⟩ }
  have memM : ∀ y, y ∈ M ↔ y ∈ L ∧ ∀ i, h y (f i) = 0 := fun y => Iff.rfl

  have hP : ∀ l ∈ L, ∃ p ∈ M, (∀ w, (∀ i, h w (f i) = 0) → h w l = h w p) ∧
      (l ∉ Submodule.span K.E (Set.range f) → p ≠ 0) := by
    intro l hl
    set g : Fin k → V := fun i => (h l (f i) / h (f i) (f i)) • f i with hg
    have hgL : ∀ i, g i ∈ L := by
      intro i
      obtain ⟨a, ha⟩ := hint l hl (f i) (hfL i)
      obtain ⟨t, ht, he⟩ := hunit i
      have hc : h l (f i) / h (f i) (f i) = algebraMap K.O K.E (a * ↑ht.unit⁻¹) := by
        rw [ha, he, map_mul, div_eq_mul_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
      simp only [hg]
      rw [hc, hsmulO]
      exact L.smul_mem _ (hfL i)
    refine ⟨l - ∑ i, g i, (memM _).2 ⟨L.sub_mem hl (L.sum_mem fun i _ => hgL i), fun j => ?_⟩,
      fun w hw => ?_, fun hn h0 => ?_⟩
    · rw [hsub1, hsum1, Finset.sum_eq_single j]
      · simp only [hg, hsmul]
        rw [div_mul_cancel₀ _ (hs j), sub_self]
      · intro i _ hij
        simp only [hg, hsmul, horth i j hij, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · rw [hsub2, hsum2, Finset.sum_eq_zero, sub_zero]
      intro i _
      simp only [hg, hsmul2, hw i, mul_zero]
    · apply hn
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hspan : Submodule.span K.E (Set.range f) ≠ ⊤ := by
    intro htop
    have h1 := finrank_range_le_card (R := K.E) f
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
    omega
  obtain ⟨l, hl, hlnot⟩ : ∃ l ∈ L, l ∉ Submodule.span K.E (Set.range f) := by
    by_contra hcon
    push_neg at hcon
    apply hspan
    rw [eq_top_iff, ← hLspan]
    exact Submodule.span_le.2 (fun x hx => hcon x hx)
  have hMne : M ≠ ⊥ := by
    obtain ⟨p, hpM, -, hp0⟩ := hP l hl
    intro hb
    rw [hb] at hpM
    exact hp0 hlnot ((Submodule.mem_bot _).1 hpM)

  by_contra hno
  push_neg at hno
  let Q : Submodule K.O K.E := Submodule.map (Algebra.linearMap K.O K.E) (IsLocalRing.maximalIdeal K.O)
  have hQsmul : ∀ (o : K.O) x, x ∈ Q → algebraMap K.O K.E o * x ∈ Q := by
    intro o x hx
    rw [← Algebra.smul_def]
    exact Q.smul_mem o hx
  have hQdiag : ∀ y ∈ M, h y y ∈ Q := by
    intro y hy
    obtain ⟨t, ht⟩ := hint y hy.1 y hy.1
    refine Submodule.mem_map.2 ⟨t, ?_, by rw [Algebra.linearMap_apply, ht]⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hno y hy.1 hy.2 t hu ht
  have hpol : ∀ y ∈ M, ∀ z ∈ M, ∀ o : K.O,
      algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z ∈ Q := by
    intro y hy z hz o
    obtain ⟨μ, hμ⟩ := K.c_int o
    have hw : y + (algebraMap K.O K.E o) • z ∈ M := by
      rw [hsmulO]
      exact M.add_mem hy (M.smul_mem o hz)
    have e : algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z =
        h (y + (algebraMap K.O K.E o) • z) (y + (algebraMap K.O K.E o) • z) - h y y
          - algebraMap K.O K.E o * (algebraMap K.O K.E μ * h z z) := by
      simp only [hadd, hadd2, hsmul, hsmul2, hμ]
      ring
    rw [e]
    exact Q.sub_mem (Q.sub_mem (hQdiag _ hw) (hQdiag _ hy)) (hQsmul _ _ (hQsmul _ _ (hQdiag _ hz)))
  have hQall : ∀ y ∈ M, ∀ z ∈ M, h y z ∈ Q := by
    intro y hy z hz
    obtain ⟨a, b, hab, hnot⟩ := K.c_res
    have h1 := hpol y hy z hz 1
    have h2 := hpol y hy z hz a
    simp only [map_one, one_mul] at h1
    rw [hab] at h2
    have h3 : algebraMap K.O K.E (a - b) * h y z ∈ Q := by
      have := Q.sub_mem (hQsmul a _ h1) h2
      convert this using 1
      rw [map_sub]
      ring
    obtain ⟨e, he⟩ := hint y hy.1 z hz.1
    rw [he, ← map_mul] at h3
    obtain ⟨m', hm', hm'e⟩ := Submodule.mem_map.1 h3
    rw [Algebra.linearMap_apply] at hm'e
    have hme := alg_inj hm'e
    rw [hme] at hm'
    rw [he]
    exact Submodule.mem_map.2 ⟨e,
      ((IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hm').resolve_left hnot, rfl⟩

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπm : IsLocalRing.maximalIdeal K.O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπmem : π ∈ IsLocalRing.maximalIdeal K.O := by
    rw [hπm]; exact Ideal.mem_span_singleton_self π
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  have hle : M ≤ IsLocalRing.maximalIdeal K.O • M := by
    intro w hw
    have hw' : (algebraMap K.O K.E π)⁻¹ • w ∈ M := by
      refine (memM _).2 ⟨(hdual _).2 fun l hl => ?_, fun i => by rw [hsmul, hw.2 i, mul_zero]⟩
      obtain ⟨p, hp, hpw, -⟩ := hP l hl
      rw [hsmul, hpw w hw.2]
      obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 (hQall w hw p hp)
      rw [hπm, Ideal.mem_span_singleton'] at hb
      obtain ⟨d, rfl⟩ := hb
      rw [← hbe, Algebra.linearMap_apply, map_mul]
      exact ⟨d, by field_simp⟩
    have hweq : w = π • ((algebraMap K.O K.E π)⁻¹ • w) := by
      rw [← hsmulO, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    rw [hweq]
    exact Submodule.smul_mem_smul hπmem hw'
  have hfg : M.FG := Submodule.FG.of_le hLfg (fun y hy => hy.1)
  exact hMne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle
    (IsLocalRing.maximalIdeal_le_jacobson _))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtensionStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_orthogonal_unit_norm_extension : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  first | exact @GlobalTheory.selfDual_orthogonal_unit_step | exact GlobalTheory.selfDual_orthogonal_unit_step | (intros; apply GlobalTheory.selfDual_orthogonal_unit_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat.ModelOfBasis

variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem herm_sum_left (x z : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (x y : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_eq_sum {n : ℕ} (x : B.A) (b : Module.Basis (Fin n) K.E B.A)
    (hb : ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) (y z : B.A) :
    B.herm x y z = ∑ k, b.repr y k * K.c (b.repr z k) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [herm_sum_right, Finset.sum_eq_single k]
  · rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_pos rfl]; ring
  · intro l _ hl
    rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.KapLat.ModelOfBasis

open GlobalTheory.KapLat.ModelOfBasis in
theorem GlobalTheory.KapLat.exists_model_of_orthonormal_basis :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hbr n B u x hu b hb
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    b.equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hψ : ∀ y k, ψ y k = e (b.repr y k) := fun y k => rfl
  have hstd : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [herm_eq_sum B x b hb, map_sum]
    unfold stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, hψ, map_mul, hbr.1]
  let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := Matrix.of fun k i => e (b.repr (u * b i) k)
  have hM : ∀ y, ψ (u * y) = M *ᵥ ψ y := by
    intro y
    funext k
    have hy : u * y = ∑ i, b.repr y i • (u * b i) := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hψ, hy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, hψ, map_smul, Finsupp.smul_apply, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hunit : cT (cj w) M * M = 1 := by
    ext i j
    have h := hstd (u * b j) (u * b i)
    rw [← GlobalTheory.UnitLemma.Basic.herm_norm, hu, mul_one, hb] at h
    simp only [stdH, hψ] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, M, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunit' : M * cT (cj w) M = 1 := mul_eq_one_comm.mp hunit
  let γ : GLw n w := ⟨M, cT (cj w) M, hunit', hunit⟩
  refine ⟨γ, ?_, ψ, ?_, hM, hstd⟩
  · unfold UL
    rw [if_neg hw]
    show cT (cj w) M * 1 * M = 1
    rw [Matrix.mul_one, hunit]
  · intro c y
    funext k
    rw [hψ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, hψ, smul_eq_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasisStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_orthonormal_basis | exact GlobalTheory.KapLat.exists_model_of_orthonormal_basis | (intros; apply GlobalTheory.KapLat.exists_model_of_orthonormal_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramified
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem UQ.norm_of_fixed_unit {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (w w' : E) (hs : star w = w) (h1 : ‖w‖ ≤ 1)
    (h1' : ‖w'‖ ≤ 1) (hww : w * w' = 1) : ∃ v : E, v * star v = w := by
  obtain ⟨ζ, -, hζ⟩ := GlobalTheory.NormUnits.exists_far_unit F E
  obtain ⟨a, ha⟩ := GlobalTheory.NormUnits.fixed_mem_range F E ζ hζ w hs
  have hprod : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, hww, norm_one]
  have hwn : ‖w‖ = 1 := by
    refine le_antisymm h1 ?_
    by_contra h
    push_neg at h
    have : ‖w‖ * ‖w'‖ < 1 :=
      calc ‖w‖ * ‖w'‖ ≤ ‖w‖ * 1 := by gcongr
        _ < 1 := by simpa using h
    linarith
  have han : ‖a‖ = 1 := by rw [← norm_algebraMap' E a, ha, hwn]
  obtain ⟨v, hv⟩ := GlobalTheory.NormUnits.norm_onto_units F E a han
  exact ⟨v, by rw [hv, ha]⟩

theorem UQ.unit_fixed_is_norm : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  intro K t ht hct
  obtain ⟨F, nF, nE, hE, nA, st, hU, hst, hball⟩ := K.exists_unram
  have hmul : ∀ x y : K.E, @HMul.hMul K.E K.E K.E (@instHMul K.E nE.toMul) x y = x * y := by
    intro x y; rw [← hE]
  have hone : @OfNat.ofNat K.E 1 (@One.toOfNat1 K.E nE.toOne) = 1 := by rw [← hE]
  obtain ⟨u, rfl⟩ := ht
  have hww : algebraMap K.O K.E u * algebraMap K.O K.E (u⁻¹ : K.Oˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨v, hv⟩ := @UQ.norm_of_fixed_unit F K.E nF nE nA st hU (algebraMap K.O K.E u)
    (algebraMap K.O K.E (u⁻¹ : K.Oˣ)) (by rw [hst]; exact hct) ((hball _).2 ⟨u, rfl⟩) ((hball _).2 ⟨_, rfl⟩)
    (by rw [hmul, hone]; exact hww)
  refine ⟨v, ?_⟩
  rw [← hst, ← hmul]; exact hv

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramifiedStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_integral_unit_eq_norm_unramified : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  first | exact @GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | exact GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | (intros; apply GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZero
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

theorem exists_orthonormal_of_selfDual (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V]
    [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z) (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (L : Submodule K.O V) (hfg : L.FG)
    (hsp : Submodule.span K.E (L : Set V) = ⊤) (hsd : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  have key : ∀ k, k ≤ Module.finrank K.E V → ∃ f : Fin k → V, (∀ i, f i ∈ L) ∧
      (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfo, hfu⟩ := ih (by omega)
      obtain ⟨y, hyL, hyo, hyu⟩ := GlobalTheory.T.selfDual_lattice_orthogonal_unit_norm_extension K V h hadd hsmul hsym L hfg hsp hsd k f hfL hfo hfu (by omega)
      refine ⟨Fin.snoc f y, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyL
        | cast i => simpa using hfL i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j => simpa using hyo j
        | cast i =>
          induction j using Fin.lastCases with
          | last => simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hsym, hyo i, map_zero]
          | cast j =>
            simp only [Fin.snoc_castSucc]
            exact hfo i j fun e => hij (by rw [e])
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyu
        | cast i => simpa using hfu i
  obtain ⟨f, -, hfo, hfu⟩ := key _ le_rfl
  choose t ht hft using hfu
  choose v hv using fun i => GlobalTheory.T.fixed_integral_unit_eq_norm_unramified K (t i) (ht i) (by rw [← hft, ← hsym])
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym, hsmul, map_mul, hsym z y]
  have ht0 : ∀ i, algebraMap K.O K.E (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (ht i).ne_zero
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i h0
    apply ht0 i
    rw [← hv i, h0, zero_mul]
  let g : Fin (Module.finrank K.E V) → V := fun i => (v i)⁻¹ • f i
  have hg : ∀ i j, h (g i) (g j) = if i = j then 1 else 0 := by
    intro i j
    simp only [g, hsmul, hsmul2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hft, ← hv i, map_inv₀]
      have : K.c (v i) ≠ 0 := by simpa using hv0 i
      field_simp
      exact div_self (hv0 i)
    · rw [if_neg hij, hfo i j hij, mul_zero, mul_zero]
  let φ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z
      map_add' := fun y y' => hadd y y' z
      map_smul' := fun a y => by simp [hsmul] }
  have hli : LinearIndependent K.E g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrArg (φ (g i)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero] at this
    simpa [φ, hg] using this
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge, fun i j => ?_⟩
  rw [Module.Basis.mk_apply, Module.Basis.mk_apply]
  exact hg i j

theorem X_nonempty_of_N_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (hN : B.N x ≠ 0) :
    (B.X x).Nonempty := by
  by_contra hX
  rw [Set.not_nonempty_iff_eq_empty] at hX
  apply hN
  haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) :=
    ⟨fun o => by
      induction o using Quot.ind with
      | mk L => exact Set.eq_empty_iff_forall_notMem.1 hX L.1 L.2⟩
  unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
  exact finsum_of_isEmpty _

theorem exists_model_of_N_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hB n Q B u x hF hn hσx _ hN
  obtain ⟨L, hlat, -, hsd⟩ := X_nonempty_of_N_ne_zero B x hN
  obtain ⟨b, hb⟩ := exists_orthonormal_of_selfDual K B.A (B.herm x)
    (fun y y' z => by unfold GlobalTheory.UnitLemma.InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)])
    (fun a y z => GlobalTheory.UnitLemma.Basic.herm_smul_left B x y z a)
    (fun y z => GlobalTheory.UnitLemma.Basic.herm_symm B x hσx y z) L hlat.1 hlat.2 hsd
  have hd : Module.finrank K.E B.A = n := hF.2.2.1.trans hn
  refine GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis E w hw K e hB n B u x hF.2.2.2 (b.reindex (finCongr hd)) fun i j => ?_
  simp only [Module.Basis.reindex_apply, hb, EmbeddingLike.apply_eq_iff_eq]

end GlobalTheory.KapLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZeroStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_N_ne_zero | exact GlobalTheory.KapLat.exists_model_of_N_ne_zero | (intros; apply GlobalTheory.KapLat.exists_model_of_N_ne_zero <;> assumption)
end

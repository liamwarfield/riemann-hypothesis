module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIntegralAlt
namespace GlobalTheory.NatSmulMemIntegral

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ b : RingOfIntegers E, (b : E) = (k : E) * a := by

  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hi : IsIntegral ℤ (y • a) := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with hpos | hneg
  · refine ⟨⟨y • a, hi⟩, ?_⟩
    change y • a = _
    rw [zsmul_eq_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]
  · refine ⟨-⟨y • a, hi⟩, ?_⟩
    change -(y • a) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonpos (by omega), Int.cast_neg]

theorem exists_nat_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • y ∈ Λ := by
  have hy : y ∈ Submodule.span E (↑Λ : Set (Fin n → E)) := by rw [h]; exact Submodule.mem_top
  simp only [Nat.cast_smul_eq_nsmul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hz
    refine ⟨m₂ * m₁, mul_ne_zero hm₂ hm₁, ?_⟩
    have ex : (m₂ * m₁) • x = m₂ • (m₁ • x) := by rw [mul_smul]
    have ez : (m₂ * m₁) • z = m₁ • (m₂ • z) := by rw [mul_comm, mul_smul]
    rw [smul_add, ex, ez]
    exact Λ.add_mem (Λ.nsmul_mem h₁ m₂) (Λ.nsmul_mem h₂ m₁)
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, b, hb⟩ := exists_nat_mul_integral c
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have hbx : b • (m • x) ∈ Λ := Λ.smul_mem b hmx
    convert hbx using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [Algebra.smul_def, show (algebraMap (RingOfIntegers E) E b) = (b : E) from rfl, hb]
    simp only [Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul]
    ring

end GlobalTheory.NatSmulMemIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.OpenPrinc

theorem close_of_open {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (K : Set R) (hK : IsCompact K)
    (ht : Filter.Tendsto (fun k : ℕ => ((k.factorial : ℕ) : R)) Filter.atTop (nhds 0))
    (G U : Subgroup (GL (Fin n) R)) (hU : IsOpen {x : G | (x : GL (Fin n) R) ∈ U}) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ z ∈ G, ∀ A B : Matrix (Fin n) (Fin n) R, (∀ i j, A i j ∈ K) → (∀ i j, B i j ∈ K) →
      (z : Matrix (Fin n) (Fin n) R) = 1 + (M : R) • A →
      ((z⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + (M : R) • B → z ∈ U := by
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  obtain ⟨O, hO, hOW⟩ := (Units.isInducing_embedProduct.isOpen_iff).1 hW
  have h1 : ((1 : Matrix (Fin n) (Fin n) R), MulOpposite.op (1 : Matrix (Fin n) (Fin n) R)) ∈ O := by
    have : (1 : G) ∈ {x : G | (x : GL (Fin n) R) ∈ U} := U.one_mem
    rw [← hWU, ← hOW] at this
    simpa using this
  have hKM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ K} := by
    have := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hK))
    have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ K} =
        Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n => K)) := by
      ext A
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact this
  have hg : Continuous (fun p : R × (Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) =>
      ((1 + p.1 • p.2.1, MulOpposite.op (1 + p.1 • p.2.2)) :
        Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ)) := by
    fun_prop
  have hev := (hKM.prod hKM).eventually_forall_of_forall_eventually (x₀ := (0 : R))
    (P := fun c p => ((1 + c • p.1, MulOpposite.op (1 + c • p.2)) :
        Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ) ∈ O) (by
      intro y _
      apply (hO.preimage hg).mem_nhds
      simpa using h1)
  obtain ⟨k, hk⟩ := (ht.eventually hev).exists
  refine ⟨k.factorial, k.factorial_ne_zero, fun z hz A B hA hB h₁ h₂ => ?_⟩
  have := hk (A, B) ⟨hA, hB⟩
  have h3 : (⟨z, hz⟩ : G) ∈ {x : G | (x : GL (Fin n) R) ∈ U} := by
    rw [← hWU, ← hOW]
    simp only [Set.mem_preimage, Units.embedProduct_apply]
    rw [h₁, h₂]
    exact this
  exact h3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem den_nat {κ : Type} [Fintype κ] (f : κ → E) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  obtain ⟨m, hm, h⟩ := Formalism.UG.P.adelstabL_den f
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm, fun i => ?_⟩
  rcases Int.natAbs_eq m with e | e
  · have := h i
    rw [e, Int.cast_natCast] at this
    exact this
  · have := (h i).neg
    rw [e, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
    exact this

theorem exists_smul_mem {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ m : ℕ, m ≠ 0 ∧ (m : E) • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem ..)

theorem exists_den {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ y ∈ Λ, ∀ i, IsIntegral ℤ ((m : E) * y i) := by
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.1 hf
  obtain ⟨m, hm, h⟩ := den_nat (fun p : s × Fin n => (p.1 : Fin n → E) p.2)
  refine ⟨m, hm, fun y hy i => ?_⟩
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact h (⟨x, hx⟩, i)
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
  | smul e x _ hx =>
    have : (m : E) * (e • x) i = (e : E) * ((m : E) * x i) := by
      change (m : E) * ((e : E) * x i) = _
      ring
    rw [this]
    exact e.isIntegral_coe.mul hx

theorem incl_mem_intV (v : HeightOneSpectrum (𝓞 F)) {e : E} (he : IsIntegral ℤ e) :
    inclE (v.adicCompletion F) e ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩)

theorem loc_upper {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hf : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ y ∈ Formalism.L2.Herm.locL v Λ, ∀ i,
      (m : E ⊗[F] v.adicCompletion F) * y i ∈ intV E v := by
  obtain ⟨m, hm, h⟩ := exists_den Λ hf
  refine ⟨m, hm, fun y hy i => ?_⟩
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    have := incl_mem_intV v (h u hu i)
    rwa [map_mul, map_natCast] at this
  | zero => simpa using (intV E v).zero_mem
  | add x y _ _ hx hy => simpa [mul_add] using (intV E v).add_mem hx hy
  | smul e x _ hx =>
    have : (m : E ⊗[F] v.adicCompletion F) * (e • x) i =
        (e : E ⊗[F] v.adicCompletion F) * ((m : E ⊗[F] v.adicCompletion F) * x i) := by
      change (m : E ⊗[F] v.adicCompletion F) * ((e : E ⊗[F] v.adicCompletion F) * x i) = _
      ring
    rw [this]
    exact (intV E v).mul_mem e.2 hx

theorem loc_lower {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ j, (Pi.single j (m : E ⊗[F] v.adicCompletion F) : Fin n → E ⊗[F] v.adicCompletion F)
      ∈ Formalism.L2.Herm.locL v Λ := by
  choose a ha h using fun j : Fin n => exists_smul_mem Λ hs (Pi.single j 1)
  refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.2 fun j _ => ha j, fun j => ?_⟩
  obtain ⟨c, hc⟩ : a j ∣ ∏ j, a j := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have h1 : (fun i => inclE (v.adicCompletion F) (((a j : E) • (Pi.single j 1 : Fin n → E)) i))
      ∈ Formalism.L2.Herm.locL v Λ := Submodule.subset_span ⟨_, h j, rfl⟩
  have h2 := nsmul_mem h1 c
  convert h2 using 1
  funext i
  by_cases hij : i = j
  · subst hij
    simp [hc, mul_comm]
  · simp [hij]

theorem loc_entries {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hf : Module.Finite (𝓞 E) Λ) (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ (M : ℕ) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)),
      (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ,
        x *ᵥ y - y = ((d * M : ℕ) : E ⊗[F] v.adicCompletion F) • z) →
      ∃ A : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F), (∀ i j, A i j ∈ intV E v) ∧
        x = 1 + (M : E ⊗[F] v.adicCompletion F) • A := by
  obtain ⟨a, ha, h₁⟩ := loc_upper v Λ hf
  obtain ⟨b, hb, h₂⟩ := loc_lower v Λ hs
  refine ⟨a * b, mul_ne_zero ha hb, fun M x hx => ?_⟩
  choose z hz hxz using fun j => hx _ (h₂ j)
  refine ⟨fun i j => (a : E ⊗[F] v.adicCompletion F) * z j i, fun i j => h₁ _ (hz j) i, ?_⟩
  have hu : IsUnit (b : E ⊗[F] v.adicCompletion F) := by
    have : IsUnit (b : E) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hb)
    simpa using this.map (inclE (F := F) (v.adicCompletion F))
  ext i j
  apply hu.mul_left_cancel
  have := congrFun (hxz j) i
  simp only [Pi.sub_apply, Matrix.mulVec_single, Pi.smul_apply, smul_eq_mul, Nat.cast_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.col_apply] at this
  change _ = (b : E ⊗[F] v.adicCompletion F) * ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j +
    (M : E ⊗[F] v.adicCompletion F) * ((a : E ⊗[F] v.adicCompletion F) * z j i))
  have e : (Pi.single j (b : E ⊗[F] v.adicCompletion F) : Fin n → E ⊗[F] v.adicCompletion F) i =
      b * (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [e] at this
  linear_combination this

theorem glob_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (M : ℕ)
    (A : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    Formalism.UG.P.afsplitC v (1 + (M : E ⊗[F] v.adicCompletion F) • A) 1 =
      1 + (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • A.map (Formalism.UG.P.afsplitIE v) := by
  ext i j
  rw [Formalism.UG.P.afsplitC_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, Nat.cast_smul_eq_nsmul, map_add (f := _), map_nsmul,
    Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
    ring
  · simp [Matrix.one_apply_ne hij]

attribute [local instance] rlt_top rlt_topRing

theorem tendsto_fact_tens : Filter.Tendsto
    (fun k : ℕ => ((k.factorial : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Filter.atTop (nhds 0) := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  haveI := rlt_isModTop F E
  have := (GlobalTheory.Mem.Col2.AdT.Opn.tendsto_fact F).smul_const (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
  simpa [Nat.cast_smul_eq_nsmul] using this

theorem open_princ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ J v S.Lb →
      (∀ y ∈ Formalism.L2.Herm.locL v S.Lb, ∃ z ∈ Formalism.L2.Herm.locL v S.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y =
          (N : E ⊗[F] v.adicCompletion F) • z) → x ∈ S.Uloc v := by
  obtain ⟨M, hM, hU⟩ := close_of_open _ (rlt_isCompact_intAf (F := F) (E := E)) tendsto_fact_tens
    (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U S.U_open
  obtain ⟨d, hd, hL⟩ := loc_entries v S.Lb S.Lb_fin S.Lb_span
  refine ⟨d * M, Nat.pos_of_ne_zero (mul_ne_zero hd hM), fun x hx hc => ?_⟩
  have hxi : ∀ y ∈ Formalism.L2.Herm.locL v S.Lb,
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y
        ∈ Formalism.L2.Herm.locL v S.Lb := fun y hy =>
    (((levelVL σ J v S.Lb).inv_mem hx).2 y).1 hy
  obtain ⟨A, hA, hxA⟩ := hL M x hc
  obtain ⟨B, hB, hxB⟩ := hL M ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix _ _ _) (by
    intro y hy
    obtain ⟨z, hz, e⟩ := hc y hy
    refine ⟨_, Submodule.neg_mem _ (hxi z hz), ?_⟩
    rw [smul_neg, ← Matrix.mulVec_smul, ← e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec, neg_sub])
  have hX : Formalism.UG.P.afsplitU v x 1 ∈ S.U := by
    refine hU _ (Formalism.UG.P.afsplitU_mem v σ J x 1 hx.1 (Subgroup.one_mem _))
      (A.map (Formalism.UG.P.afsplitIE v)) (B.map (Formalism.UG.P.afsplitIE v))
      (fun i j => Formalism.UG.P.afsplit_IE_int v _ (hA i j))
      (fun i j => Formalism.UG.P.afsplit_IE_int v _ (hB i j)) ?_ ?_
    · rw [Formalism.UG.P.afsplitU_coe, hxA, Units.val_one, glob_eq]
    · rw [Formalism.UG.P.afsplitU_inv_coe, hxB, inv_one, Units.val_one, glob_eq]
  have h := ((S.U_eq _).1 hX).2 v
  have e : bc (prV v) (Formalism.UG.P.afsplitU v x 1) = x := by
    apply Units.ext
    have := Formalism.UG.P.afsplitC_prV v (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      ((1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _)
    rw [← Formalism.UG.P.afsplitU_coe] at this
    exact this
  rwa [e] at h

end GlobalTheory.OpenPrinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_congruence_subgroup_preserves_principal_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), ∃ N : ℕ, 0 < N ∧ ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ J v S.Lb → (∀ y ∈ Formalism.L2.Herm.locL v S.Lb, ∃ z ∈ Formalism.L2.Herm.locL v S.Lb, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (N : E ⊗[F] v.adicCompletion F) • z) → x ∈ S.Uloc v := by
  first | exact @GlobalTheory.OpenPrinc.open_princ | exact GlobalTheory.OpenPrinc.open_princ | (intros; apply GlobalTheory.OpenPrinc.open_princ <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartQ

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stepQ_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (K : Formalism.L2.Forms.StepLevel F E σ J T f bad) (H0 : Formalism.L2.Herm.StepLevel hc S gp T f)
    (hQ : ∀ v ∈ Q, ((T : ℕ) : 𝓞 F) ∉ v.asIdeal ∧ ∀ j, ((gp j : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hLb : K.Lb = reL h H0.Lb) (hU : ∀ v, v ∉ Q → K.Uloc v = (H0.Uloc v).map (reGL h _).toMonoidHom) :
    ∃ L : Formalism.L2.Herm.StepLevelQ hc S gp T f Q, L.Lb = H0.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  simp only [GlobalTheory.HermTransport.reL_refl'] at hLb
  simp only [GlobalTheory.HermTransport.reGL_refl_hom', Subgroup.map_id] at hU ⊢
  have hgQ : ∀ (i : Fin 2) v, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∉ Q := fun i v hv hvQ => (hQ v hvQ).2 i hv
  have hTQ : ∀ v, ((T : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∉ Q := fun v hv hvQ => (hQ v hvQ).1 hv
  let L : Formalism.L2.Herm.StepLevelQ hc S gp T f Q :=
    { Lb := H0.Lb
      Lb_fin := H0.Lb_fin
      Lb_span := H0.Lb_span
      Lb_int := H0.Lb_int
      Lb_dual := H0.Lb_dual
      Lb_index := H0.Lb_index
      Uloc := K.Uloc
      Uloc_lev := fun v => hLb ▸ K.Uloc_lev v
      Uloc_hyp := fun v h0 h1 hT hvQ => (hU v hvQ).trans (H0.Uloc_hyp v h0 h1 hT)
      Uloc_g := fun i v hv x hx => (hU v (hgQ i v hv)) ▸ H0.Uloc_g i v hv x hx
      UlocAlt := fun v hv x => (hU v (hTQ v hv)) ▸ H0.UlocAlt v hv x
      Uloc_Q := fun v _ => by
        obtain ⟨N, hN, hx⟩ := GlobalTheory.T.open_congruence_subgroup_preserves_principal_lattice hc.sig S.gram K v
        exact ⟨N, hN, fun x hx' => hx x (hLb ▸ hx'.1) (hLb ▸ hx'.2)⟩
      U := K.U
      U_eq := K.U_eq }
  exact ⟨L, rfl, fun v => rfl, rfl⟩

end Gen

theorem chartTie_toQ : ∀ {D : D7} {T : ℕ} (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) {i : ℕ} (hm : i ≤ D.R.m) {cl : Type} (st : cl → Type) [∀ c, Group (st c)] (lt : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V) (K : LevelChart D T (badQ D Q) i hm st (fun c => latCrd D i hm (lt c))) (H0 : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T D.R.f), (∀ v ∈ Q, ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ j, ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) → K.lev.Lb = reL (rankN D i hm) H0.Lb → (∀ v, v ∉ Q → K.lev.Uloc v = (H0.Uloc v).map (reGL (rankN D i hm) _).toMonoidHom) → ∃ (L : Formalism.L2.Herm.StepLevelQ D.sp.cm (D.sp.X i) D.host.g T D.R.f Q) (C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U st lt), L.Lb = H0.Lb ∧ SameCar (rankN D i hm) L.Lb K.lev.Lb L.Uloc K.lev.Uloc L.U K.lev.U (fun c => (C.y c).1) (fun c => (K.y c).1) (fun c s => (C.stabI c s).1) (fun c s => (K.stabI c s).1) := by
  intro D T Q i hm cl st _ lt K H0 hQ hLb hU
  obtain ⟨L, hL, hUloc, hUU⟩ := GlobalTheory.ChartQ.stepQ_of_reindex D.sp.cm (D.sp.X i) (rankN D i hm) (σ := sigD D) rfl
    (fun a b => rfl) Q K.lev H0 hQ hLb hU
  obtain ⟨C, hy, hst⟩ := GlobalTheory.HermTransport.classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hm) rfl (fun a b => rfl)
    (Equiv.refl cl) lt K.y K.y_bij (fun c x => by rw [← GlobalTheory.HermTransport.latCrd_eq_reL]; exact K.y_lat c x) K.stabI
    K.stabI_inj K.stabI_range L.Lb L.U (hL ▸ hLb) hUU
  exact ⟨L, C, hL, ⟨hL ▸ hLb, hUloc, hUU, fun c => hy c, fun c s => hst c s⟩⟩

end GlobalTheory.ChartQ

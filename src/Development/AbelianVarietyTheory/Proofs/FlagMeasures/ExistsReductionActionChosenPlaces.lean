module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKg
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKg
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Inhab GlobalTheory.Mem.RowsBundle

theorem hAf_add_left (I : AutInst) (x x' y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (x + x') y = hAf I x y + hAf I x' y := by
  unfold hAf Formalism.UG.hform
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hAf_smul_left (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (a • x) y = Formalism.UG.sigR I.cm.sig (Af I.F) a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem mapsTo_conj_of_adjoint (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E))
    (T T' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (hc : IsConj I w w')
    (hadj : ∀ x y, hAf I (T' *ᵥ x) y = hAf I x (T *ᵥ y))
    (hT' : ∀ y ∈ I.Lf, T' *ᵥ y ∈ extId I w.asIdeal • I.Lf) :
    ∀ y ∈ I.Lf, T *ᵥ y ∈ extId I w'.asIdeal • I.Lf := by
  intro y hy
  rw [DualIdeal.mem_extId_smul_iff I _ w'.ne_bot]
  intro y' hy'
  rw [← hadj]
  have key : ∀ u ∈ extId I w.asIdeal • I.Lf, ∃ z ∈ extId I w'.asIdeal,
      (z : I.E ⊗[I.F] Af I.F) = hAf I u y := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) (fun u u' hu hu' => ?_)
    · obtain ⟨a', ha', e⟩ := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2 w w' hc a ha
      refine ⟨a' * ⟨_, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy l hl⟩, Ideal.mul_mem_right _ _ ha', ?_⟩
      rw [Subring.coe_mul, e]
      show _ = hAf I ((a : I.E ⊗[I.F] Af I.F) • l) y
      rw [hAf_smul_left]
    · obtain ⟨z, hz, e⟩ := hu
      obtain ⟨z', hz', e'⟩ := hu'
      exact ⟨z + z', add_mem hz hz', by rw [Subring.coe_add, e, e', hAf_add_left]⟩
  exact key _ (hT' y' hy')

theorem PlFrame.trivial_iff {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : x ∈ I.Kset) :
    (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y) ↔
      ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf := by
  have key : ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y ↔
      (I.fmat x - 1) *ᵥ (y : Fin I.n → _) ∈ extId I w.asIdeal • I.Lf := by
    intro y h
    rw [← sub_eq_zero, ← map_sub, fr.c_ker, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  exact ⟨fun H y hy => (key ⟨y, hy⟩ (mulVec_mem hx hy)).1 (H _ _), fun H y h => (key y h).2 (H y.1 y.2)⟩

theorem IsChoice.isRadical_mul {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (hC : IsChoice I g Pl w) :
    (Ideal.span {((g 0 * g 1 : ℕ) : 𝓞 I.E)}).IsRadical := by
  have hc : Nat.Coprime (g 0) (g 1) := (Nat.coprime_primes (hC.1 0) (hC.1 1)).2 hC.2.1
  have hc' : IsCoprime ((g 0 : ℕ) : 𝓞 I.E) ((g 1 : ℕ) : 𝓞 I.E) := Nat.Coprime.cast hc
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.mul_eq_inf_of_isCoprime ((Ideal.isCoprime_span_singleton_iff _ _).2 hc')]
  exact (hC.2.2.1 0).inf (hC.2.2.1 1)

theorem trivial_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N →
    IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
      (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  intro I N g Pl w fr _ hC x hx
  have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
  have hone : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hmem : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ I.Lf := fun y hy => by
    simpa using sub_one_pow_mem hx 1 hy
  have crt := fun y hy => GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I (g 0 * g 1) hone hC.isRadical_mul _ (hmem y hy)
  constructor
  · intro H
    have H1 := fun k v => ((fr k v).trivial_iff hx).1 (H k v)
    have H2 : ∀ k v, ∀ y ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ y ∈ extId I (w k v).asIdeal • I.Lf := by
      intro k v y hy
      have h1 : I.fmat x * I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
      have h := neg_mem (H1 k v _ (mulVec_mem hx' hy))
      rw [Matrix.mulVec_mulVec, sub_mul, h1, one_mul, ← Matrix.neg_mulVec, neg_sub] at h
      exact h
    refine ⟨hx, fun y hy => (crt y hy).1 fun u hu => ?_⟩
    have hk : ∃ k, ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rw [Nat.cast_mul] at hu
      exact (u.isPrime.mem_or_mem hu).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨v, rfl | hv⟩ := hC.2.2.2.2.2.2 k u hk
    · exact H1 k v y hy
    · refine mapsTo_conj_of_adjoint I _ _ _ _ hv (fun a b => ?_) (H2 k v) y hy
      simpa only [pow_one] using hAf_pow_adjoint x 1 a b
  · intro H k v
    refine ((fr k v).trivial_iff hx).2 fun y hy => (crt y hy).2 (H.2 y hy) _ ?_
    have h := (hC.2.2.2.1 k v).1
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKgStatement
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type) (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N → IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  first | exact @GlobalTheory.RowLev.trivial_iff_mem_Kg | exact GlobalTheory.RowLev.trivial_iff_mem_Kg | (intros; apply GlobalTheory.RowLev.trivial_iff_mem_Kg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryStabilizerLiftOfSplitIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryStabilizerLiftOfSplitIdempotent
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitLift

open Formalism.UG

variable {A : Type} [CommRing A] {n : ℕ}

theorem exists_lift_matrix {S k : Type} [CommRing S] [Field k] (r : S →+* k) (ε : S)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (M : GL (Fin n) k) :
    ∃ N N' : Matrix (Fin n) (Fin n) S, N.map r = (M : Matrix (Fin n) (Fin n) k) ∧
      N * N' = ε • (1 : Matrix (Fin n) (Fin n) S) ∧ N' * N = ε • (1 : Matrix (Fin n) (Fin n) S) := by
  choose f hf using hr
  let N : Matrix (Fin n) (Fin n) S := (M : Matrix (Fin n) (Fin n) k).map f
  have hN : N.map r = (M : Matrix (Fin n) (Fin n) k) := by
    ext i j; simp [N, hf]
  have hd : r N.det ≠ 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hN]
    exact (Matrix.isUnits_det_units M).ne_zero
  obtain ⟨t, ht⟩ := hloc _ hd
  refine ⟨N, (t * ε) • N.adjugate, hN, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1; linear_combination ht
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    congr 1; linear_combination ht

theorem exists_gen (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ μ : Fin n → Λ, (∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i)) ∧
      (∀ i, ε • μ i = μ i) ∧ ∀ y : Λ, ∃ a : Fin n → S, ε • y = ∑ i, a i • μ i := by
  choose g hg using hc
  let μ : Fin n → Λ := fun i => ε • g (Pi.single i 1)
  have h1 : ∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    ext j
    simp [μ, map_smulₛₗ, hg, hrε, Finset.sum_apply, Pi.single_apply]
  have h2 : ∀ i, ε • μ i = μ i := fun i => by simp only [μ, smul_smul, hε]
  refine ⟨μ, h1, h2, ?_⟩
  let N : Submodule S (Fin n → A) := Submodule.span S (Set.range fun i => (μ i : Fin n → A))
  have hle : Λ ≤ N ⊔ RingHom.ker r • Λ := by
    intro y hy
    choose f hf using hr
    let a : Fin n → S := fun i => f (c ⟨y, hy⟩ i)
    have h0 : c (⟨y, hy⟩ - ∑ i, a i • μ i) = 0 := by
      rw [map_sub, h1]; ext j; simp [a, hf]
    have h3 := hker _ h0
    have h4 : ((∑ i, a i • μ i : Λ) : Fin n → A) ∈ N := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ =>
        N.smul_mem (a i) (Submodule.subset_span ⟨i, rfl⟩)
    have : y = ((∑ i, a i • μ i : Λ) : Fin n → A) +
        ((⟨y, hy⟩ - ∑ i, a i • μ i : Λ) : Fin n → A) := by
      rw [Submodule.coe_sub]; simp
    rw [this]
    exact Submodule.add_mem_sup h4 h3
  obtain ⟨z, hz, hzle⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  have hz1 : r z ≠ 0 := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hz
    rw [hz]; exact one_ne_zero
  obtain ⟨t, ht⟩ := hloc z hz1
  intro y
  have hy : z • (y : Fin n → A) ∈ N := hzle (Submodule.smul_mem_pointwise_smul _ _ _ y.2)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
  refine ⟨fun i => t * ε * b i, Subtype.ext ?_⟩
  have : ε • (y : Fin n → A) = (t * ε) • z • (y : Fin n → A) := by
    rw [smul_smul]; congr 1; linear_combination -ht
  rw [Submodule.coe_smul, this, ← hb, Finset.smul_sum, Submodule.coe_sum]
  simp only [Submodule.coe_smul, smul_smul]

theorem exists_basis (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hsp : Submodule.span A (Λ : Set (Fin n → A)) = ⊤)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ B B' : Matrix (Fin n) (Fin n) A, B * B' = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) ∧
      B' * B = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) ∧ (ε : A) • B = B ∧ (ε : A) • B' = B' ∧
      (∀ y : Λ, ∃ a : Fin n → S, B' *ᵥ (y : Fin n → A) = (fun i => (a i : A)) ∧
        c y = fun i => r (a i)) ∧
      ∀ a : Fin n → S, ∃ y : Λ, B *ᵥ (fun i => (a i : A)) = y ∧ c y = fun i => r (a i) := by
  obtain ⟨μ, h1, h2, h3⟩ := exists_gen S Λ r c ε hfg hε hrε hr hloc hc hker
  have hεA : (ε : A) * ε = ε := by exact_mod_cast congrArg Subtype.val hε
  let B : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => (μ j : Fin n → A) i
  have hB : ∀ a : Fin n → S, B *ᵥ (fun i => (a i : A)) = ((∑ i, a i • μ i : Λ) : Fin n → A) := by
    intro a
    ext i
    rw [Submodule.coe_sum]
    simp [B, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Subring.smul_def]
  have hεB : (ε : A) • B = B := by
    ext i j
    have := congrFun (congrArg Subtype.val (h2 j)) i
    simpa [B, Subring.smul_def] using this
  have hall : ∀ v : Fin n → A, ∃ w, B *ᵥ w = (ε : A) • v := by
    intro v
    have hv : v ∈ Submodule.span A (Λ : Set (Fin n → A)) := hsp ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha⟩ := h3 ⟨y, hy⟩
      exact ⟨_, by rw [hB a, ← ha]; rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨u + w, by rw [Matrix.mulVec_add, hu, hw, smul_add]⟩
    | smul a x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨a • u, by rw [Matrix.mulVec_smul, hu, smul_comm]⟩
  choose w hw using hall
  let C : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => w (Pi.single j 1) i
  have hBC : B * C = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    have := congrFun (hw (Pi.single j 1)) i
    simpa [C, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply] using this
  let B' : Matrix (Fin n) (Fin n) A := (ε : A) • C
  have hεB' : (ε : A) • B' = B' := by simp only [B', smul_smul, hεA]
  have hBB' : B * B' = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    simp only [B', Matrix.mul_smul, hBC, smul_smul, hεA]
  have hz : (1 - (ε : A)) • B = 0 := by rw [sub_smul, one_smul, hεB, sub_self]
  have hz' : (1 - (ε : A)) • B' = 0 := by rw [sub_smul, one_smul, hεB', sub_self]
  have hsq : (1 - (ε : A)) * (1 - ε) = 1 - ε := by linear_combination hεA
  have hB'B : B' * B = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    have e1 : (B + (1 - (ε : A)) • (1 : Matrix (Fin n) (Fin n) A)) *
        (B' + (1 - (ε : A)) • (1 : Matrix (Fin n) (Fin n) A)) = 1 := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one, hz, hz', hBB', smul_add, smul_smul, hsq]
      simp [sub_smul]
    have e2 := mul_eq_one_comm.1 e1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one, hz, hz', smul_add, smul_smul, hsq] at e2
    simp only [sub_smul, one_smul, add_zero, zero_add] at e2
    linear_combination (norm := abel_nf) e2
  refine ⟨B, B', hBB', hB'B, hεB, hεB', ?_, fun a => ⟨_, hB a, h1 a⟩⟩
  intro y
  obtain ⟨a, ha⟩ := h3 y
  refine ⟨fun i => ε * a i, ?_, ?_⟩
  · have e : (ε : A) • (y : Fin n → A) = B *ᵥ (fun i => (a i : A)) := by
      rw [hB a, ← ha]; rfl
    rw [← hεB', Matrix.smul_mulVec, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hB'B,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp
  · have := h1 a
    rw [← ha, map_smulₛₗ, hrε, one_smul] at this
    simp [this, hrε]

noncomputable def adj (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  J⁻¹ * cT s Y * J

theorem cT_add (s : A →+* A) (X Y : Matrix (Fin n) (Fin n) A) :
    cT s (X + Y) = cT s X + cT s Y := by ext i j; simp [cT]

theorem cT_smul (s : A →+* A) (a : A) (X : Matrix (Fin n) (Fin n) A) :
    cT s (a • X) = s a • cT s X := by ext i j; simp [cT]

theorem cT_cT (s : A →+* A) (hs : ∀ a, s (s a) = a) (X : Matrix (Fin n) (Fin n) A) :
    cT s (cT s X) = X := by ext i j; simp [cT, hs]

theorem adj_mul (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X Y : Matrix (Fin n) (Fin n) A) : adj s J X * adj s J Y = adj s J (Y * X) := by
  simp only [adj, cT_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem adj_smul (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (a : A)
    (X : Matrix (Fin n) (Fin n) A) : adj s J (a • X) = s a • adj s J X := by
  simp only [adj, cT_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) :
    adj s J 1 = 1 := by
  simp only [adj, cT_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hJ]

theorem mul_adj (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) : J * adj s J X = cT s X * J := by
  simp only [adj, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem cT_adj_mul (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) : cT s (adj s J X) * J = J * X := by
  have hH' : cT s J = J := hH
  have h1 : cT s J⁻¹ * J = 1 := by
    have := congrArg (cT s) (Matrix.mul_nonsing_inv _ hJ)
    rwa [cT_mul, cT_one, hH'] at this
  simp only [adj, cT_mul, cT_cT s hs, hH', Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hform_dot (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_adj (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform s J x (adj s J X *ᵥ y) = hform s J (X *ᵥ x) y := by
  rw [hform_dot, hform_dot, Matrix.mulVec_mulVec, mul_adj s hJ, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]

noncomputable def glue (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (X X' : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  (1 - e - s e) • (1 : Matrix (Fin n) (Fin n) A) + X + adj s J X'

theorem glue_mul (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) {e : A}
    (he : e * e = e) (hes : e * s e = 0) {X X' : Matrix (Fin n) (Fin n) A}
    (hX : e • X = X) (hX' : e • X' = X') (h : X * X' = e • (1 : Matrix (Fin n) (Fin n) A)) :
    glue s J e X X' * glue s J e X' X = 1 := by
  have hse : s e * s e = s e := by rw [← map_mul, he]
  have a1 : s e • adj s J X = adj s J X := by rw [← adj_smul, hX]
  have a2 : s e • adj s J X' = adj s J X' := by rw [← adj_smul, hX']
  have u1 : (1 - e - s e) * e = 0 := by linear_combination -he - hes
  have u2 : (1 - e - s e) * s e = 0 := by linear_combination -hse - hes
  have z1 : (1 - e - s e) • X = 0 := by rw [← hX, smul_smul, u1, zero_smul]
  have z2 : (1 - e - s e) • X' = 0 := by rw [← hX', smul_smul, u1, zero_smul]
  have z3 : (1 - e - s e) • adj s J X = 0 := by rw [← a1, smul_smul, u2, zero_smul]
  have z4 : (1 - e - s e) • adj s J X' = 0 := by rw [← a2, smul_smul, u2, zero_smul]
  have z5 : X * adj s J X = 0 := by
    rw [← a1]; nth_rewrite 1 [← hX]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hes, zero_smul]
  have z6 : adj s J X' * X' = 0 := by
    rw [← a2]; nth_rewrite 2 [← hX']
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, hes, zero_smul]
  have z7 : adj s J X' * adj s J X = s e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [adj_mul s hJ, h, adj_smul, adj_one s hJ]
  have u3 : (1 - e - s e) * (1 - e - s e) = 1 - e - s e := by linear_combination -u1 - u2
  simp only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, z1, z2, z3, z4, z5, z6, z7, h, u3]
  module

theorem cT_glue (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det) (e : A) (X X' : Matrix (Fin n) (Fin n) A) :
    cT s (glue s J e X X') * J = J * glue s J e X' X := by
  simp only [glue, cT_add, cT_smul, cT_one, Matrix.add_mul, Matrix.mul_add, cT_adj_mul s hs hH hJ,
    mul_adj s hJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, map_sub,
    map_one, hs]
  rw [sub_right_comm]
  abel

theorem exists_unitary_lift : ∀ (A : Type) [CommRing A] (s : A →+* A) (S : Subring A) (n : ℕ) (J : Matrix (Fin n) (Fin n) A) (Λ : Submodule S (Fin n → A)) (k : Type) [Field k] (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S), (∀ a, s (s a) = a) → (∀ a ∈ S, s a ∈ S) → Formalism.UG.IsHerm s J → IsUnit J.det → Λ.FG → Submodule.span A (Λ : Set (Fin n → A)) = ⊤ → (∀ y, y ∈ Λ ↔ ∀ y' ∈ Λ, Formalism.UG.hform s J y' y ∈ S) → ε * ε = ε → (ε : A) * s ε = 0 → r ε = 1 → Function.Surjective r → (∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε) → Function.Surjective c → (∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) → ∀ M : GL (Fin n) k, ∃ x : GL (Fin n) A, x ∈ Formalism.UG.UJ s J ∧ x ∈ Formalism.UG.stabGL Λ ∧ (∀ (y : Λ) (h : (x : Matrix (Fin n) (Fin n) A) *ᵥ (y : Fin n → A) ∈ Λ), c ⟨_, h⟩ = (M : Matrix (Fin n) (Fin n) k) *ᵥ c y) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ((x : Matrix (Fin n) (Fin n) A) - 1) *ᵥ y = ((ε : A) + s ε) • z := by
  intro A _ s S n J Λ k _ r c ε hs hS hH hJ hfg hsp hdual hε hes hrε hr hloc hc hker M
  obtain ⟨B, B', hBB', hB'B, hεB, hεB', hB', hB⟩ :=
    exists_basis S Λ r c ε hfg hsp hε hrε hr hloc hc hker
  obtain ⟨N, N', hN, hNN', hN'N⟩ := exists_lift_matrix r ε hr hloc M
  have hεA : (ε : A) * ε = ε := by exact_mod_cast congrArg Subtype.val hε
  let F : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) A := fun P => B * P.map S.subtype * B'
  have hFε : ∀ P, (ε : A) • F P = F P := fun P => by
    simp only [F, ← Matrix.mul_smul, hεB']
  have hFmul : ∀ P Q, P * Q = ε • (1 : Matrix (Fin n) (Fin n) S) →
      F P * F Q = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    intro P Q h
    have h' : P.map S.subtype * Q.map S.subtype = (ε : A) • (1 : Matrix (Fin n) (Fin n) A) := by
      rw [← Matrix.map_mul, h]
      ext i j
      by_cases hij : i = j <;> simp [hij]
    calc F P * F Q = B * (P.map S.subtype * (B' * B) * Q.map S.subtype) * B' := by
          simp only [F, Matrix.mul_assoc]
      _ = _ := by
          simp only [hB'B, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h', hBB', smul_smul,
            hεA]
  have hFΛ : ∀ P (y : Λ), ∃ z : Λ, F P *ᵥ (y : Fin n → A) = z ∧ c z = P.map r *ᵥ c y := by
    intro P y
    obtain ⟨a, ha, hca⟩ := hB' y
    obtain ⟨z, hz, hcz⟩ := hB (P *ᵥ a)
    refine ⟨z, ?_, ?_⟩
    · rw [← hz]
      simp only [F, ← Matrix.mulVec_mulVec, ha]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct]
    · rw [hcz, hca]
      ext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum]
  have hFmem : ∀ P, ∀ y ∈ Λ, F P *ᵥ y ∈ Λ := fun P y hy => by
    obtain ⟨z, hz, -⟩ := hFΛ P ⟨y, hy⟩
    exact hz ▸ z.2
  have hadj : ∀ P, ∀ y ∈ Λ, adj s J (F P) *ᵥ y ∈ Λ := fun P y hy => by
    rw [hdual]
    intro y' hy'
    rw [hform_adj s hJ]
    exact (hdual y).1 hy _ (hFmem P y' hy')
  let ε' : S := ⟨s ε, hS _ ε.2⟩
  have hrε' : r ε' = 0 := by
    have : ε * ε' = 0 := Subtype.ext hes
    have := congrArg r this
    rwa [map_mul, hrε, one_mul, map_zero] at this
  have hglue : ∀ P Q y, glue s J ε (F P) (F Q) *ᵥ y =
      (1 - ε - ε') • y + F P *ᵥ y + ε' • adj s J (F Q) *ᵥ y := by
    intro P Q y
    have a1 : s ε • adj s J (F Q) = adj s J (F Q) := by rw [← adj_smul, hFε]
    rw [glue, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    nth_rewrite 1 [← a1]
    rw [Matrix.smul_mulVec]
    rfl
  have hgmem : ∀ P Q, ∀ y ∈ Λ, glue s J ε (F P) (F Q) *ᵥ y ∈ Λ := fun P Q y hy => by
    rw [hglue]
    exact Λ.add_mem (Λ.add_mem (Λ.smul_mem _ hy) (hFmem P y hy)) (Λ.smul_mem _ (hadj Q y hy))
  have g1 := glue_mul s hJ hεA hes (hFε N) (hFε N') (hFmul _ _ hNN')
  have g2 := glue_mul s hJ hεA hes (hFε N') (hFε N) (hFmul _ _ hN'N)
  refine ⟨⟨glue s J ε (F N) (F N'), glue s J ε (F N') (F N), g1, g2⟩, ?_, ?_, ?_, ?_⟩
  · change cT s (glue s J ε (F N) (F N')) * J * glue s J ε (F N) (F N') = J
    rw [cT_glue s hs hH hJ, Matrix.mul_assoc, g2, Matrix.mul_one]
  · intro y
    refine ⟨hgmem N N' y, fun hy => ?_⟩
    have := hgmem N' N _ hy
    rwa [Matrix.mulVec_mulVec, g2, Matrix.one_mulVec] at this
  · intro y h
    obtain ⟨z, hz, hcz⟩ := hFΛ N y
    have : (⟨_, h⟩ : Λ) = (1 - ε - ε') • y + z + ε' • ⟨_, hadj N' y y.2⟩ := by
      apply Subtype.ext
      change glue s J ε (F N) (F N') *ᵥ (y : Fin n → A) = _
      rw [hglue, hz]; rfl
    rw [this, map_add (f := _), map_add (f := _), map_smulₛₗ, map_smulₛₗ, hcz, hN, hrε']
    simp [hrε, hrε']
  · intro y hy
    refine ⟨-y + F N *ᵥ y + adj s J (F N') *ᵥ y,
      Λ.add_mem (Λ.add_mem (Λ.neg_mem hy) (hFmem N y hy)) (hadj N' y hy), ?_⟩
    change (glue s J ε (F N) (F N') - 1) *ᵥ y = _
    have a1 : s ε • adj s J (F N') = adj s J (F N') := by rw [← adj_smul, hFε]
    have b1 : ((ε : A) + s ε) • F N = F N := by
      rw [← hFε N, smul_smul]; congr 1; linear_combination hεA + hes
    have b2 : ((ε : A) + s ε) • adj s J (F N') = adj s J (F N') := by
      have hse : s ε * s ε = s ε := by rw [← map_mul, hεA]
      rw [← a1, smul_smul]; congr 1; linear_combination hse + hes
    rw [smul_add, smul_add, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, b1, b2, glue,
      Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    module

end GlobalTheory.SplitLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryStabilizerLiftOfSplitIdempotentStatement
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_stabilizer_lift_of_split_idempotent : ∀ (A : Type) [CommRing A] (s : A →+* A) (S : Subring A) (n : ℕ) (J : Matrix (Fin n) (Fin n) A) (Λ : Submodule S (Fin n → A)) (k : Type) [Field k] (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S), (∀ a, s (s a) = a) → (∀ a ∈ S, s a ∈ S) → Formalism.UG.IsHerm s J → IsUnit J.det → Λ.FG → Submodule.span A (Λ : Set (Fin n → A)) = ⊤ → (∀ y, y ∈ Λ ↔ ∀ y' ∈ Λ, Formalism.UG.hform s J y' y ∈ S) → ε * ε = ε → (ε : A) * s ε = 0 → r ε = 1 → Function.Surjective r → (∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε) → Function.Surjective c → (∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) → ∀ M : GL (Fin n) k, ∃ x : GL (Fin n) A, x ∈ Formalism.UG.UJ s J ∧ x ∈ Formalism.UG.stabGL Λ ∧ (∀ (y : Λ) (h : (x : Matrix (Fin n) (Fin n) A) *ᵥ (y : Fin n → A) ∈ Λ), c ⟨_, h⟩ = (M : Matrix (Fin n) (Fin n) k) *ᵥ c y) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ((x : Matrix (Fin n) (Fin n) A) - 1) *ᵥ y = ((ε : A) + s ε) • z := by
  first | exact @GlobalTheory.SplitLift.exists_unitary_lift | exact GlobalTheory.SplitLift.exists_unitary_lift | (intros; apply GlobalTheory.SplitLift.exists_unitary_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrime
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem sigR_sigR_af (I : AutInst) (x : I.E ⊗[I.F] Af I.F) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isHerm_af (I : AutInst) :
    Formalism.UG.IsHerm (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) := by
  have hs : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig] <;> rfl
  have hJ := I.J_herm
  unfold Formalism.UG.IsHerm Formalism.UG.cT at hJ ⊢
  ext i j
  have h := congrArg (fun M => M i j) hJ
  simp only [Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h ⊢
  rw [hs, h]

theorem isUnit_det_af (I : AutInst) : IsUnit (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).det := by
  have h : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).det = Formalism.UG.inclE (F := I.F) (Af I.F) I.J.det :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact (Ne.isUnit I.J_det).map _

theorem exists_mem_Kset_actsAs_trivial_away : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  intro I N p w fr hN hp hw hw' M
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hεε, h1ε, hεu, hεt, hεσ⟩ := GlobalTheory.T.exists_prime_idempotent_integralAdeles I w
  have hA := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I 1 le_rfl
  have hL := GlobalTheory.AdelicLattice.adelicLattice_spec I 1 le_rfl
  have hX := GlobalTheory.RowLev.extId_mul_sup_natCast_conj I
  have hker : ∀ z, fr.r z = 0 ↔ z ∈ extId I w.asIdeal := fun z => by
    rw [← RingHom.mem_ker, fr.ker_r]
  have hrε : fr.r ε = 1 := by
    have h0 : fr.r (1 - ε) = 0 := (hker _).2 h1ε
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨x, hxU, hxS, hact, htriv⟩ := GlobalTheory.T.exists_unitary_stabilizer_lift_of_split_idempotent (I.E ⊗[I.F] Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F))
    (IntAf I.F I.E) I.n (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) I.Lf (ZMod p) fr.r fr.c ε
    (fun a => sigR_sigR_af I a) (fun a ha => hA.2.2.2 a ha) (isHerm_af I) (isUnit_det_af I)
    hL.2.2.2.1 hL.2.2.1 (fun y => GlobalTheory.AdelicLattice.adelicLattice_selfDual I y) hεε (hεσ hw') hrε
    (ZMod.ringHom_surjective fr.r) (fun z hz => hεt z fun h => hz ((hker z).2 h)) fr.c_surj
    (fun y hy => by rw [fr.ker_r]; exact (fr.c_ker y).1 hy) M
  refine ⟨⟨x, hxU⟩, hxS, fun y h => hact y h, ?_⟩
  intro u hu hcu y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  obtain ⟨u', hu'⟩ := hX.2.2.2.1 u
  have hu'w : u' ≠ w := by
    rintro rfl
    exact hcu (hX.2.2.2.2.1 u u' hu')
  obtain ⟨z', hz', hz'e⟩ := hX.2.2.2.2.2.2 u' u (hX.2.2.2.2.1 u u' hu') ε (hεu u' hu'w)
  have hmem : ε + z' ∈ extId I u.asIdeal := add_mem (hεu u hu) hz'
  have hfin : (I.fmat ⟨x, hxU⟩ - 1) *ᵥ y = (ε + z') • z := by
    change ((x : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) - 1) *ᵥ y = _
    rw [e, ← hz'e]
    rfl
  rw [hfin]
  exact Submodule.smul_mem_smul hmem hz

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrimeStatement
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  first | exact @GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | exact GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | (intros; apply GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away <;> assumption)
end
end

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem IsChoice.eq_of_mem {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {k k' : Fin 2}
    (u : HeightOneSpectrum (𝓞 I.E)) (h1 : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal) (h2 : ((g k' : ℕ) : 𝓞 I.E) ∈ u.asIdeal) :
    k = k' := by
  by_contra hkk
  have hg : g k ≠ g k' := by
    intro e
    apply hkk
    fin_cases k <;> fin_cases k'
    · rfl
    · exact absurd e h.2.1
    · exact absurd e.symm h.2.1
    · rfl
  obtain ⟨a, b, hab⟩ : IsCoprime (g k : ℤ) (g k') :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (h.1 k) (h.1 k')).mpr hg)
  have e : (a : 𝓞 I.E) * ((g k : ℕ) : 𝓞 I.E) + (b : 𝓞 I.E) * ((g k' : ℕ) : 𝓞 I.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 I.E) hab
    push_cast at this
    exact this
  apply u.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem IsChoice.ne_of_ne {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {a b : Σ k, Pl k} (hab : b ≠ a) :
    w b.1 b.2 ≠ w a.1 a.2 ∧ ¬ IsConj I (w a.1 a.2) (w b.1 b.2) := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  dsimp only
  have hmem := h.2.2.2.1
  by_cases hk : kb = ka
  · subst hk
    have hv : vb ≠ va := fun e => hab (by rw [e])
    exact ⟨fun e => hv (h.2.2.2.2.1 kb e), h.2.2.2.2.2.1 kb va vb⟩
  · refine ⟨fun e => hk (h.eq_of_mem (w kb vb) (hmem kb vb).1 (by rw [e]; exact (hmem ka va).1)), fun hcj => hk ?_⟩
    have hx := (hcj ((g ka : ℕ) : 𝓞 I.E) ((g ka : ℕ) : 𝓞 I.E) (by simp)).mp (hmem ka va).1
    exact (h.eq_of_mem (w kb vb) hx (hmem kb vb).1).symm

theorem PlFrame.actsAs_one_of_mem {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf) : fr.ActsAs x 1 := by
  intro y h
  rw [Matrix.one_mulVec, ← sub_eq_zero, ← map_sub]
  refine (fr.c_ker _).mpr ?_
  have e : ((⟨_, h⟩ - y : I.Lf) : Fin I.n → _) = (I.fmat x - 1) *ᵥ (y : Fin I.n → _) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Submodule.coe_sub]
  rw [e]
  exact hx _ y.2

private theorem val_eq_lemma {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} {fr : ∀ k v, PlFrame I N (g k) (w k v)}
    {ρ : I.Gf → GProd N g Pl} (hρ : ActsBy fr ρ) {x : I.Gf} (hx : x ∈ I.Kset) (kv : Σ k, Pl k)
    {M : GL (Fin N) (ZMod (g kv.1))} (hM : (fr kv.1 kv.2).ActsAs x (M : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))) :
    ρ x kv = M :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (hρ x hx kv.1 kv.2) hM)

theorem exists_red_actsBy : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)) [∀ k, Finite (Pl k)],
    I.n = N → IsChoice I g Pl w → ∃ ρ : Red I (g 0 * g 1) (GProd N g Pl), ActsBy fr ρ.toFun := by
  intro I N g Pl w fr _ hn hc
  classical
  obtain ⟨ρ, hρ, hmul⟩ := exists_actsBy fr
  have hK1 : (1 : I.Gf) ∈ I.Kset := (Inhab.mem_Ksub I 1).mp (Inhab.Ksub I).one_mem
  have hKmul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, x * y ∈ I.Kset := fun x hx y hy =>
    (Inhab.mem_Ksub I _).mp
      ((Inhab.Ksub I).mul_mem ((Inhab.mem_Ksub I x).mpr hx) ((Inhab.mem_Ksub I y).mpr hy))
  have hone : ∀ x ∈ I.Kset, ∀ kv : (Σ k, Pl k), (fr kv.1 kv.2).ActsAs x 1 → ρ x kv = 1 :=
    fun x hx kv h => val_eq_lemma hρ hx kv (M := 1) (by rw [Units.val_one]; exact h)
  have : Fintype (Σ k, Pl k) := Fintype.ofFinite _
  refine ⟨⟨ρ, hmul, fun x hx => ?_, fun q => ?_⟩, hρ⟩
  · rw [← GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg I N g Pl w fr hn hc x hx]
    constructor
    · intro h1 k v y h
      rw [hρ x hx k v y h, h1]
      simp
    · intro h
      funext kv
      exact hone x hx kv (fun y hy => by rw [h kv.1 kv.2 y hy, Matrix.one_mulVec])
  · have key : ∀ s : Finset (Σ k, Pl k), ∃ x ∈ I.Kset, ρ x = fun kv => if kv ∈ s then q kv else 1 := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · exact ⟨1, hK1, funext fun kv => by simpa using hone 1 hK1 kv (fr kv.1 kv.2).actsAs_one⟩
      · intro a s ha ih
        obtain ⟨xs, hxs, es⟩ := ih
        obtain ⟨xa, hxa, hact, hoth⟩ := GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime I N (g a.1) (w a.1 a.2) (fr a.1 a.2) hn (hc.1 a.1)
          (hc.2.2.2.1 a.1 a.2).2 (hc.2.2.2.2.2.1 a.1 a.2 a.2) (q a)
        refine ⟨xa * xs, hKmul xa hxa xs hxs, ?_⟩
        rw [hmul xa hxa xs hxs, es]
        funext kv
        by_cases hk : kv = a
        · rw [hk, Pi.mul_apply, val_eq_lemma hρ hxa a hact]
          simp [ha]
        · have hne := IsChoice.ne_of_ne hc hk
          rw [Pi.mul_apply, hone xa hxa kv (PlFrame.actsAs_one_of_mem _ (hoth _ hne.1 hne.2))]
          simp [hk]
    obtain ⟨x, hx, e⟩ := key Finset.univ
    exact ⟨x, hx, by rw [e]; simp⟩

end GlobalTheory.RowLev

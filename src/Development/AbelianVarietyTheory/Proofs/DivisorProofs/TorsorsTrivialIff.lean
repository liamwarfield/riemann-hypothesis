module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivTruncExpICompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
open IsLocalRing

noncomputable section

namespace GlobalTheory.LocAcyc

def IsZModTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) : Prop :=
  Module.Finite B D ∧ Module.Projective B D ∧ Module.FaithfullyFlat B D ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)))

theorem torsorsTrivial_iff (B : Type) [CommRing B] (q : ℕ) :
    TorsorsTrivial B q ↔ ∀ (D : Type) [CommRing D] [Algebra B D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)), IsZModTorsor B D q act →
        Nonempty (D →ₐ[B] B) := by
  constructor
  · intro h D _ _ act hD
    exact h D hD.1 hD.2.1 hD.2.2.1 act hD.2.2.2
  · intro h D _ _ h1 h2 h3 act h4
    exact h D act ⟨h1, h2, h3, h4⟩

def LocPiecesEtale (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
    ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)

end GlobalTheory.LocAcyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
open MeasureTheory Filter Topology

namespace GlobalTheory.WeilM.HaarUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] :
    ∃ K : OpenAddSubgroup V, IsCompact (K : Set V) := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  exact ⟨K, hC.of_isClosed_subset K.isClosed hK⟩


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem [IsTopologicalAddGroup V] [T2Space V]
    (K : OpenAddSubgroup V) (hK : IsCompact (K : Set V)) :
    Set.indicator (K : Set V) (fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.WeilM.SB V := by
  simp only [_root_.GlobalTheory.WeilM.SB, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ (K : Set V)
  · exact ⟨K, K.isOpen, hx, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set V)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant [NonarchimedeanAddGroup V] {φ : V → ℂ}
    (hφ : φ ∈ _root_.GlobalTheory.WeilM.SB V) :
    ∃ K : OpenAddSubgroup V, ∀ k ∈ K, ∀ x, φ (x + k) = φ x := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨hlc, hcs⟩ := hφ'
  have hnhds : ∀ x : V, (fun w => x + w) ⁻¹' {y | φ y = φ x} ∈ 𝓝 (0 : V) := by
    intro x
    refine (continuous_const_add x).continuousAt.preimage_mem_nhds ?_
    rw [add_zero]
    exact (hlc.isOpen_fiber (φ x)).mem_nhds rfl
  choose W hW using fun x => NonarchimedeanAddGroup.is_nonarchimedean _ (hnhds x)
  have hval : ∀ i y, y - i ∈ W i → φ y = φ i := by
    intro i y hy
    have := hW i hy
    simpa using this
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun i => (fun y => y - i) ⁻¹' (W i))
    (fun i => (W i).isOpen.preimage (continuous_sub_right i))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using (W y).zero_mem⟩)
  refine ⟨t.inf W, fun k hk x => ?_⟩
  have hkW : ∀ i ∈ t, k ∈ W i := fun i hi => (Finset.inf_le hi : t.inf W ≤ W i) hk
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hxi' : x - i ∈ W i := hxi
    have hxk : x + k - i ∈ W i := by
      have := (W i).add_mem hxi' (hkW i hi)
      rwa [sub_add_eq_add_sub] at this
    rw [hval i _ hxk, hval i _ hxi']
  by_cases hxk : x + k ∈ tsupport φ
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hxk)
    have hxi' : x + k - i ∈ W i := hxi
    have hx' : x - i ∈ W i := by
      have := (W i).sub_mem hxi' (hkW i hi)
      rwa [sub_right_comm, add_sub_cancel_right] at this
    rw [hval i _ hxi', hval i _ hx']
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxk]


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp [IsTopologicalAddGroup V] (K : OpenAddSubgroup V)
    {φ : V → ℂ} (hc : HasCompactSupport φ) (hinv : ∀ k ∈ K, ∀ x, φ (x + k) = φ x) :
    ∃ S : Finset (V ⧸ K.toAddSubgroup),
      φ = ∑ q ∈ S, φ q.out • (fun x => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (x + -q.out)) := by
  classical
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun p : V => (fun y => -p + y) ⁻¹' (K : Set V))
    (fun p => K.isOpen.preimage (continuous_const_add (-p)))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using K.zero_mem⟩)
  refine ⟨t.image (QuotientAddGroup.mk : V → V ⧸ K.toAddSubgroup), ?_⟩
  funext x
  have hmem : ∀ q : V ⧸ K.toAddSubgroup,
      (x + -q.out ∈ (K : Set V)) ↔ q = (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, add_comm]
    simp
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, hmem,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hS
  · have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup)
    rw [QuotientAddGroup.eq] at h
    have := hinv _ h ((QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup).out)
    rw [add_neg_cancel_left] at this
    exact this
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa using hxp

open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
private theorem exists_coeff_form_and_integral [IsTopologicalAddGroup V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ)
    (H : OpenAddSubgroup V) (hH : IsCompact (H : Set V)) {φ : V → ℂ} (hc : HasCompactSupport φ)
    (hinv : ∀ k ∈ H, ∀ x, φ (x + k) = φ x) :
    ∃ A : ℂ, m φ = A * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) ∧
      ∫ x, φ x ∂μ = A * (μ.real (H : Set V) : ℂ) := by
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp H hc hinv
  have hmemH := _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem H hH
  have hint : Integrable (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) μ :=
    (integrable_indicator_iff H.isOpen.measurableSet).2 (integrableOn_const hH.measure_lt_top.ne)
  refine ⟨∑ q ∈ S, φ q.out, ?_, ?_⟩
  · calc m φ = m (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) := congrArg m hS
      _ = ∑ q ∈ S, φ q.out * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, smul_eq_mul, hm _ hmemH]
      _ = _ := by rw [Finset.sum_mul]
  · calc ∫ x, φ x ∂μ = ∫ x, (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) x ∂μ := by
            rw [← hS]
      _ = ∑ q ∈ S, φ q.out * (μ.real (H : Set V) : ℂ) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [MeasureTheory.integral_finsetSum]
          · refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_const_mul,
              integral_add_right_eq_self (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) x),
              integral_indicator_const _ H.isOpen.measurableSet]
            simp
          · intro q _
            exact (hint.comp_add_right _).const_mul _
      _ = _ := by rw [Finset.sum_mul]


open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
theorem _root_.GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral : ∀ (V : Type) [AddCommGroup V]
    [TopologicalSpace V] [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ), (∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ) →
    ∃ c : ℂ, ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, m φ = c * ∫ x, φ x ∂μ := by
  intro V _ _ _ _ _ _ _ μ _ m hm
  obtain ⟨K₀, hK₀⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup (V := V)
  have hpos : ∀ H : OpenAddSubgroup V, IsCompact (H : Set V) → μ.real (H : Set V) ≠ 0 := by
    intro H hH
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨(H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩).ne', hH.measure_lt_top.ne⟩
  refine ⟨m (Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ))) / (μ.real (K₀ : Set V) : ℂ),
    fun φ hφ => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨K₁, hK₁⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant hφ
  set H : OpenAddSubgroup V := K₀ ⊓ K₁
  have hH : IsCompact (H : Set V) := by
    refine hK₀.of_isClosed_subset H.isClosed ?_
    rw [OpenAddSubgroup.coe_inf]
    exact Set.inter_subset_left
  have hHK₁ : ∀ k ∈ H, k ∈ K₁ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.2
  have hHK₀ : ∀ k ∈ H, k ∈ K₀ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.1
  obtain ⟨A, hA₁, hA₂⟩ := exists_coeff_form_and_integral μ m hm H hH hφ'.2
    (fun k hk x => hK₁ k (hHK₁ k hk) x)
  obtain ⟨B, hB₁, hB₂⟩ := exists_coeff_form_and_integral μ m hm H hH
    (φ := Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ)))
    (HasCompactSupport.intro hK₀ fun x hx => Set.indicator_of_notMem hx _)
    (fun k hk x => by
      by_cases hx : x ∈ K₀ <;>
        simp [Set.indicator_apply, hx, add_mem_cancel_right (hHK₀ k hk)])
  rw [integral_indicator_const _ K₀.isOpen.measurableSet, Complex.real_smul, mul_one] at hB₂
  have hH0 : (μ.real (H : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos H hH)
  have hK0 : (μ.real (K₀ : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos K₀ hK₀)
  rw [hA₁, hA₂, hB₁, hB₂]
  have hB0 : B ≠ 0 := by
    rintro rfl
    apply hK0
    rw [hB₂, zero_mul]
  field_simp

end GlobalTheory.WeilM.HaarUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing

namespace GlobalTheory

def PurityFree (R : Type) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 →
    (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
    Module.Free R A

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.TorsMem

private theorem div_N_mem_tauPair_lattice_iff_dvd (N : ℕ) [NeZero N] (τ : ℍ) (a b : ℤ) :
    ((a : ℂ) * τ + (b : ℂ)) / N ∈ (tauPair τ).lattice ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    rw [h1, h2, eq_div_iff hN] at h
    obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.mp (tauPair τ).indep
      (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by
        rw [h1, h2, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination h)
    norm_cast at k1 k2
    exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    rw [h1, h2, eq_div_iff hN]
    push_cast
    ring

theorem div_mem_iff (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  rw [div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  intro N _ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : ∀ x : Fin 2 → ZMod N,
      tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N := by
    intro x
    simp only [tors, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ
        + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht]; push_cast; ring
    rw [e, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp [sub_eq_zero]
  · intro x y
    have e : tors N τ (x + y) - (tors N τ x + tors N τ y) =
        (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ)
        + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht, ht]; push_cast; ring
    rw [e, div_mem_iff]
    simp
  · intro x
    rw [ht, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp
  · intro x
    rw [PeriodPair.mem_lattice]
    refine ⟨(x 0).val, (x 1).val, ?_⟩
    change (((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _
    rw [ht]
    field_simp
  · intro z hz
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
    change (m : ℂ) * τ + n * 1 = N * z at h
    refine ⟨![(m : ZMod N), (n : ZMod N)], ?_⟩
    have hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N := by
      rw [eq_div_iff hN]
      linear_combination -h
    have e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] =
        (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N := by
      rw [hz', ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    rw [e, div_mem_iff]
    simp

end GlobalTheory.WpFam.TorsMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembershipStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  first | exact @GlobalTheory.WpFam.TorsMem.main | exact GlobalTheory.WpFam.TorsMem.main | (intros; apply GlobalTheory.WpFam.TorsMem.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.BlockPar

variable {F : Type} [Field F] {a b : ℕ}

def sm (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl a M = (sm M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₁₁, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_left]
  rfl

theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br a b M = (sm M).toBlocks₂₂ := by
  ext i j
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₂₂, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_right]
  rfl

theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (sm (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    simp only [sm, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply h <;> simp
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
      ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castAdd b j' = j := ⟨⟨j, hj⟩, rfl⟩
    have := congrFun (congrFun h i') j'
    simpa [sm, Matrix.toBlocks₂₁] using this

theorem sm_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    sm M = Matrix.fromBlocks (tl a M) (sm M).toBlocks₁₂ 0 (br a b M) := by
  rw [tl_eq, br_eq, ← h, Matrix.fromBlocks_toBlocks]

theorem sm_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) : sm (M * N) = sm M * sm N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem mul_blocks {M N : Matrix (Fin (a + b)) (Fin (a + b)) F} (hM : (sm M).toBlocks₂₁ = 0)
    (hN : (sm N).toBlocks₂₁ = 0) :
    (sm (M * N)).toBlocks₂₁ = 0 ∧ tl a (M * N) = tl a M * tl a N ∧ br a b (M * N) = br a b M * br a b N := by
  have e : sm (M * N) = Matrix.fromBlocks (tl a M * tl a N)
      (tl a M * (sm N).toBlocks₁₂ + (sm M).toBlocks₁₂ * br a b N) 0 (br a b M * br a b N) := by
    rw [sm_mul, sm_eq hM, sm_eq hN, Matrix.fromBlocks_multiply]
    simp
  refine ⟨by rw [e, Matrix.toBlocks_fromBlocks₂₁], ?_, ?_⟩
  · rw [tl_eq (M * N), e, Matrix.toBlocks_fromBlocks₁₁]
  · rw [br_eq (M * N), e, Matrix.toBlocks_fromBlocks₂₂]

theorem det_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.det = (tl a M).det * (br a b M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M]
  change (sm M).det = _
  rw [sm_eq h, Matrix.det_fromBlocks_zero₂₁]

theorem charpoly_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.charpoly = (tl a M).charpoly * (br a b M).charpoly := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv.symm M]
  have : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M = sm M := by
    rw [Matrix.reindex_apply, Equiv.symm_symm]; rfl
  rw [this, sm_eq h, Matrix.charpoly_fromBlocks_zero₂₁]

theorem toG_val {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem units_of_par (x : GL (Fin (a + b)) F) (h : InPar a x) :
    IsUnit (tl a (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) ∧ IsUnit (br a b (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
  have hu : IsUnit (x : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  rw [det_eq ((inPar_iff x).1 h)] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu),
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)⟩

theorem inPar_inv (x : GL (Fin (a + b)) F) (h : InPar a x) : InPar a x⁻¹ := by
  let β : Fin (a + b) → Bool := fun i => decide (a ≤ (i : ℕ))
  have hb : (x : Matrix (Fin (a + b)) (Fin (a + b)) F).BlockTriangular β := by
    intro i j hij
    rw [Bool.lt_iff] at hij
    simp only [β, decide_eq_false_iff_not, decide_eq_true_eq, not_le] at hij
    exact h i j hij.1 hij.2
  haveI := x.invertible
  have hb' := Matrix.blockTriangular_inv_of_blockTriangular hb
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact hb' (by rw [Bool.lt_iff]; simp [β]; omega)

theorem block_par : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  intro F _ a b n hn
  subst hn
  let H : Subgroup (GL (Fin (a + b)) F) :=
    { carrier := {x | InPar a x}
      one_mem' := by
        intro i j hj hi
        rw [Units.val_one, Matrix.one_apply_ne]
        intro e; subst e; omega
      mul_mem' := by
        intro x y hx hy
        exact (inPar_iff _).2 (mul_blocks ((inPar_iff x).1 hx) ((inPar_iff y).1 hy)).1
      inv_mem' := fun {x} hx => inPar_inv x hx }
  have hH : ∀ x, x ∈ H ↔ InPar a x := fun _ => Iff.rfl
  have hpar : ∀ p : H, (sm ((p.1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 :=
    fun p => (inPar_iff _).1 p.2
  have hval : ∀ p : H, ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) ∧
      ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) :=
    fun p => ⟨toG_val (units_of_par _ p.2).1, toG_val (units_of_par _ p.2).2⟩
  let π : H →* GL (Fin a) F × GL (Fin b) F :=
    MonoidHom.mk' (fun p => (tlG a p.1, brG a b p.1)) (by
      intro p q
      have hm := mul_blocks (hpar p) (hpar q)
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · change ((tlG a (p * q).1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * ((tlG a q.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
        rw [(hval (p * q)).1, (hval p).1, (hval q).1]
        exact hm.2.1
      · change ((brG a b (p * q).1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * ((brG a b q.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        rw [(hval (p * q)).2, (hval p).2, (hval q).2]
        exact hm.2.2)
  have hπ : ∀ p : H, π p = (tlG a p.1, brG a b p.1) := fun _ => rfl
  refine ⟨H, π, hH, ?_, hπ, fun p => hval p, fun p => ?_⟩
  · rintro ⟨u, v⟩
    let M : Matrix (Fin (a + b)) (Fin (a + b)) F :=
      (Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
    have hsm : sm M = Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F) := by
      simp only [sm, M, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
    have h21 : (sm M).toBlocks₂₁ = 0 := by rw [hsm, Matrix.toBlocks_fromBlocks₂₁]
    have htl : tl a M = u := by rw [tl_eq, hsm, Matrix.toBlocks_fromBlocks₁₁]
    have hbr : br a b M = v := by rw [br_eq, hsm, Matrix.toBlocks_fromBlocks₂₂]
    have hu : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det, det_eq h21, htl, hbr]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 v.isUnit)
    have hmem : hu.unit ∈ H := by
      rw [hH, inPar_iff]
      exact h21
    refine ⟨⟨hu.unit, hmem⟩, ?_⟩
    have hv := hval ⟨hu.unit, hmem⟩
    simp only [IsUnit.unit_spec] at hv
    rw [hπ]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact hv.1.trans htl
    · exact hv.2.trans hbr
  · rw [hπ, (hval p).1, (hval p).2]
    exact charpoly_eq (hpar p)

end GlobalTheory.Shin.BlockPar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  first | (exact @GlobalTheory.Shin.BlockPar.block_par) | (exact GlobalTheory.Shin.BlockPar.block_par) | (intros; apply GlobalTheory.Shin.BlockPar.block_par  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

def DivConst (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Prop :=
  ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (a : T) (w : Oˣ), b = algebraMap T O a * (w : O)

def DivConstAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → DivConst T O

def DivConstWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) :
    Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P → DivConst T O

def DivConstLocal : Prop := DivConstWith (fun _ _ _ _ => True)

def DivConstGeneric : Prop :=
  DivConstWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstClosedPts : Prop :=
  DivConstWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstOrigin : Prop :=
  DivConstWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

theorem divConstLocal_of (h₁ : DivConstClosedPts) (h₂ : DivConstGeneric) : DivConstLocal := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP _
  by_cases hg : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h₂ T O hT P φ hφ hsh hP hg
  · exact h₁ T O hT P φ hφ hsh hP hg

end GlobalTheory.VertUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicProperties
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NrmBasic

section General

variable {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ)

theorem nrmG_zero (δ : G) : nrmG φ s 0 δ = 1 := by
  simp [nrmG]

theorem nrmG_succ (l : ℕ) (δ : G) : nrmG φ s (l + 1) δ = nrmG φ s l δ * φ (s ^ l) δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem nrmG_twConj (l : ℕ) (δ y : G) :
    nrmG φ s l (y⁻¹ * δ * φ s y) = y⁻¹ * nrmG φ s l δ * φ (s ^ l) y := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, ih]
    have h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y := by
      rw [map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]
    rw [h1]
    group

theorem mul_map_nrmG (l : ℕ) (δ : G) :
    δ * φ s (nrmG φ s l δ) = nrmG φ s l δ * φ (s ^ l) δ := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]

theorem nrmG_mul (l : ℕ) (δ ε : G) (h : ∀ i j : ℕ, Commute (φ (s ^ i) δ) (φ (s ^ j) ε)) :
    nrmG φ s l (δ * ε) = nrmG φ s l δ * nrmG φ s l ε := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]
    have hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ) := by
      unfold nrmG
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (h l i).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]

end General

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem pow_finrank_eq_one (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem fixed_iff (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    s x = x ↔ x ∈ Set.range (algebraMap F F') := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro t _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hs t)
    have h1 : ∀ m : ℕ, (s ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    have h2 : ∀ m : ℕ, (s⁻¹ ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply]
        have : s⁻¹ x = x := by
          conv_lhs => rw [← hx]
          exact s.symm_apply_apply x
        rw [this, ih]
    cases k with
    | ofNat m => simpa using h1 m
    | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact h2 (m + 1)
  · rintro ⟨a, rfl⟩
    exact s.commutes a

end Fields

theorem main : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  intro F F' _ _ _ _ s hs n
  have hl := pow_finrank_eq_one s
  have hinj : Function.Injective (algebraMap F F') := (algebraMap F F').injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j := by
        intro i j
        have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx
        simpa [galAct_apply, gal] using this
      choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)
      let M : Matrix (Fin n) (Fin n) F := Matrix.of M0
      have hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact hM i j
      have hu : IsUnit M := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro h0
        have : (x : Matrix (Fin n) (Fin n) F').det = 0 := by rw [← hdet, h0, map_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero x) this
      refine ⟨hu.unit, ?_⟩
      ext i j
      simp [incl, gal, M, hM]
    · rintro ⟨y, rfl⟩
      ext i j
      simp [galAct_apply, gal, incl]
  · intro a b hab
    ext i j
    have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab
    exact hinj (by simpa [incl, gal] using this)
  · intro δ y
    unfold nrm
    rw [nrmG_twConj, hl, map_one, MulAut.one_apply]
  · intro δ
    unfold nrm
    rw [mul_map_nrmG, hl, map_one, MulAut.one_apply]
  · intro δ ε h
    unfold nrm
    exact nrmG_mul _ _ _ _ _ fun i j => h _ _

end GlobalTheory.Shin.NrmBasic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTwistedNormGL_basic_properties : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  first | (exact @GlobalTheory.Shin.NrmBasic.main) | (exact GlobalTheory.Shin.NrmBasic.main) | (intros; apply GlobalTheory.Shin.NrmBasic.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZero
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem _root_.GlobalTheory.ainf_isDomain_and_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hprim
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  refine ⟨by unfold _root_.GlobalTheory.Sandwich.Ainf; infer_instance, ?_⟩
  intro h
  unfold _root_.GlobalTheory.Sandwich.mu at h
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have hε : ε = 1 := by
    have := congrArg (fun x => WittVector.coeff x 0) h1
    simpa [WittVector.teichmuller_coeff_zero] using this
  have hroot : _root_.GlobalTheory.Sandwich.root ε = 1 := by
    unfold _root_.GlobalTheory.Sandwich.root
    rw [hε, map_one]
  rw [hroot, map_one] at hprim
  exact (Fact.out : p.Prime).one_lt.ne' (IsPrimitiveRoot.one_left_iff.mp hprim)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem QAll.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {p : ℂ → Prop} {f : ℍ → ℂ}
    (h0 : p 0) (hf : QAll p N f) : QAll p N' f := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, hpa⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, fun n => ?_⟩
  unfold spread
  split_ifs
  · exact hpa _
  · exact h0

theorem QConj.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {g : ℂ ≃+* ℂ} {f f' : ℍ → ℂ}
    (hf : QConj g N f f') : QConj g N' f f' := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, ha'⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, ?_⟩
  have key : (fun n => g (spread M a n)) = spread M (fun n => g (a n)) := by
    funext n
    unfold spread
    split_ifs <;> simp
  rw [key]
  exact hasQ_mul_spread N M f' _ hN hM ha'

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.HasQ.mdifferentiable {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N)
    (h : _root_.GlobalTheory.QFam.HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  exact ((_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h').mdifferentiable (by exact_mod_cast hN)


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty :
    ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → _root_.GlobalTheory.QFam.HasQ N f a →
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  intro N f a hN h
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  have hq := (_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h'
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨hq.mdifferentiable hpos, hq.isBoundedAtImInfty hpos⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInftyStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → HasQ N f a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | exact GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | (intros; apply GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory

theorem wB_nonhol_correction : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  intro N y τ
  rw [wB, gN, G2s]
  push_cast
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentityStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  first | exact @GlobalTheory.wB_nonhol_correction | exact GlobalTheory.wB_nonhol_correction | (intros; apply GlobalTheory.wB_nonhol_correction <;> assumption)
end
end

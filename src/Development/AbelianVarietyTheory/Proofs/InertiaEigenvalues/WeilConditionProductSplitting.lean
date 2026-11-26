module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRepApply
namespace GlobalTheory.JR.WeilProd

def tensorRep {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    G × H → (X × Y → ℂ) → X × Y → ℂ :=
  fun g f p => W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1

theorem tensorRep_apply {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) (g : G × H)
    (f : X × Y → ℂ) (p : X × Y) :
    tensorRep W₁ W₂ g f p = W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1 := rfl

end GlobalTheory.JR.WeilProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplitting
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplitting
open GlobalTheory.JR MeasureTheory
open scoped Pointwise

namespace GlobalTheory.JR.EtProdAbs

theorem distribHaarChar_prod {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [LocallyCompactSpace R₁] [T2Space R₁] [SecondCountableTopology R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [LocallyCompactSpace R₂] [T2Space R₂] [SecondCountableTopology R₂] (v : (R₁ × R₂)ˣ) :
    distribHaarChar (R₁ × R₂) v =
      distribHaarChar R₁ (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v) *
        distribHaarChar R₂ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v) := by
  borelize R₁ R₂
  let μ₁ : Measure R₁ := Measure.addHaar
  let μ₂ : Measure R₂ := Measure.addHaar
  obtain ⟨S₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₁) := inferInstance
  obtain ⟨S₂⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₂) := inferInstance
  have h0₁ : μ₁ (S₁ : Set R₁) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₁ S₁.interior_nonempty).ne'
  have h0₂ : μ₂ (S₂ : Set R₂) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₂ S₂.interior_nonempty).ne'
  have h1₁ : μ₁ (S₁ : Set R₁) ≠ ⊤ := S₁.isCompact.measure_lt_top.ne
  have h1₂ : μ₂ (S₂ : Set R₂) ≠ ⊤ := S₂.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₁.prod μ₂) (s := (S₁ : Set R₁) ×ˢ (S₂ : Set R₂))
    (by rw [Measure.prod_prod]; exact mul_ne_zero h0₁ h0₂)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top h1₁ h1₂) ?_
  have hs : v • ((S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) =
      (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v • (S₁ : Set R₁)) ×ˢ
        (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v • (S₂ : Set R₂)) := by
    ext ⟨x, y⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, Set.mem_prod, Set.mem_smul_set_iff_inv_smul_mem,
      Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ← map_inv]
    exact Iff.rfl
  rw [hs, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul μ₁, ← distribHaarChar_mul μ₂]
  push_cast
  ring

theorem absK_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  intro F E _ _ _ _ U A A₁ A₂ eK t
  have := U.ultraF; have := U.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.K
  by_cases ht : IsUnit t
  · let u : A.Kˣ := ht.unit
    let v : (A₁.K × A₂.K)ˣ := Units.map (eK : A.K →* A₁.K × A₂.K) u
    let e' : A.K ≃ₜ+ A₁.K × A₂.K :=
      { eK.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap eK.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap eK.symm.toLinearMap }
    have h1 : distribHaarChar (A₁.K × A₂.K) v = distribHaarChar A.K u :=
      ModuleNorm.distribHaarChar_transport e' u v (fun x => by
        change eK ((u : A.K) * x) = eK (u : A.K) * eK x
        rw [map_mul])
    rw [distribHaarChar_prod] at h1
    have ht' : t = (u : A.K) := (IsUnit.unit_spec ht).symm
    have e1 : (eK t).1 = ((Units.map (RingHom.fst A₁.K A₂.K : A₁.K × A₂.K →* A₁.K) v : A₁.Kˣ) : A₁.K) := by
      rw [ht']; rfl
    have e2 : (eK t).2 = ((Units.map (RingHom.snd A₁.K A₂.K : A₁.K × A₂.K →* A₂.K) v : A₂.Kˣ) : A₂.K) := by
      rw [ht']; rfl
    rw [e1, e2, ht', EtMeas.absK_unit, EtMeas.absK_unit, EtMeas.absK_unit, ← h1]
    push_cast
    rfl
  · have h0 : A.absK t = 0 := by simp [Et.absK, ht]
    have hn : ¬ IsUnit (eK t) := fun h => ht ((isUnit_map_iff eK t).1 h)
    rw [Prod.isUnit_iff, not_and_or] at hn
    rw [h0]
    rcases hn with hn | hn
    · have : A₁.absK (eK t).1 = 0 := by simp [Et.absK, hn]
      rw [this, zero_mul]
    · have : A₂.absK (eK t).2 = 0 := by simp [Et.absK, hn]
      rw [this, mul_zero]

end GlobalTheory.JR.EtProdAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplittingStatement
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absK_mul_of_etale_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  first | exact @GlobalTheory.JR.EtProdAbs.absK_prod | exact GlobalTheory.JR.EtProdAbs.absK_prod | (intros; apply GlobalTheory.JR.EtProdAbs.absK_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProduct
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology

namespace GlobalTheory.JR.WeilProd.TensorTest

section Basic
variable {X : Type} [TopologicalSpace X]

theorem isTest_of_lc {g : X → ℂ} (hg : IsLocallyConstant g) {K : Set X} (hK : IsCompact K)
    (hs : Function.support g ⊆ K) : IsTest g := by
  refine ⟨hg, ?_⟩
  have hcl : IsClosed (Function.support g) := by
    show IsClosed {x | g x ≠ 0}
    exact (hg.isOpen_fiber 0).isClosed_compl
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hs

theorem isTest_zero : IsTest (0 : X → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isTest_add {f f' : X → ℂ} (hf : IsTest f) (hf' : IsTest f') : IsTest (f + f') :=
  ⟨hf.1.add hf'.1, hf.2.add hf'.2⟩

theorem isTest_smul (c : ℂ) {f : X → ℂ} (hf : IsTest f) : IsTest (c • f) :=
  ⟨hf.1.comp (c * ·), hf.2.smul_left⟩

theorem isTest_sum {ι : Type} (s : Finset ι) (F : ι → X → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (∑ j ∈ s, F j) := by
  classical
  revert hF
  refine Finset.induction_on s (fun _ => by simpa using (isTest_zero : IsTest (0 : X → ℂ))) ?_
  intro a s ha ih hF
  rw [Finset.sum_insert ha]
  exact isTest_add (hF a (Finset.mem_insert_self a s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem map_zero {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) : W g 0 = 0 := by
  have := hW.2.2.2 g 1 0 0 isTest_zero isTest_zero
  simpa using this

theorem map_sum {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j ∈ s, IsTest (f j)) :
    W g (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • W g (f j) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => by simp [map_zero hW g]) ?_
  intro a s ha ih hf
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  have hs : IsTest (∑ j ∈ s, c j • f j) :=
    isTest_sum s _ fun j hj => isTest_smul _ (hf j (Finset.mem_insert_of_mem hj))
  rw [hW.2.2.2 g (c a) (f a) _ (hf a (Finset.mem_insert_self a s)) hs,
    ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end Basic

section Prod
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isTest_mul_prod {a : X → ℂ} {b : Y → ℂ} (ha : IsTest a) (hb : IsTest b) :
    IsTest (fun p : X × Y => a p.1 * b p.2) := by
  refine isTest_of_lc ?_ (ha.2.isCompact.prod hb.2.isCompact) ?_
  · exact IsLocallyConstant.comp₂ (ha.1.comp_continuous continuous_fst) (hb.1.comp_continuous continuous_snd)
      (fun x y => x * y)
  · intro p hp
    have h1 : a p.1 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : b p.2 ≠ 0 := right_ne_zero_of_mul hp
    exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

theorem isTest_fibre {f : X × Y → ℂ} (hf : IsTest f) (u : X) : IsTest (fun v => f (u, v)) := by
  refine isTest_of_lc (hf.1.comp_continuous (continuous_const.prodMk continuous_id)) (hf.2.isCompact.image continuous_snd) ?_
  intro v hv
  exact ⟨(u, v), subset_tsupport _ hv, rfl⟩

theorem isLocallyConstant_curry {f : X × Y → ℂ} (hf : IsTest f) :
    IsLocallyConstant (fun u => fun v => f (u, v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hK : IsCompact (Prod.snd '' tsupport f) := hf.2.isCompact.image continuous_snd
  have hev : ∀ᶠ u in 𝓝 u₀, ∀ v ∈ Prod.snd '' tsupport f, f (u, v) = f (u₀, v) := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro y _
    have h1 : ∀ᶠ z in 𝓝 (u₀, y), f z = f (u₀, y) := ((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y)
    have hc : Continuous (fun z : X × Y => (u₀, z.2)) := (continuous_const.prodMk continuous_id).comp continuous_snd
    have ht : Tendsto (fun z : X × Y => (u₀, z.2)) (𝓝 (u₀, y)) (𝓝 (u₀, y)) := hc.continuousAt
    have h2 : ∀ᶠ z in 𝓝 (u₀, y), f (u₀, z.2) = f (u₀, y) :=
      ht.eventually (((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y))
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  filter_upwards [hev] with u hu
  funext v
  by_cases hv : v ∈ Prod.snd '' tsupport f
  · exact hu v hv
  · have hA : (u, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    have hB : (u₀, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isTest_sum_fn {ι : Type} (s : Finset ι) (F : ι → X × Y → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (fun p => ∑ j ∈ s, F j p) := by
  have := isTest_sum s F hF
  rwa [Finset.sum_fn] at this

theorem decomp {f : X × Y → ℂ} (hf : IsTest f) :
    ∃ (s : Finset (Y → ℂ)) (a : (Y → ℂ) → X → ℂ), (∀ φ ∈ s, IsTest (a φ)) ∧ (∀ φ ∈ s, IsTest φ) ∧
      ∀ p : X × Y, f p = ∑ φ ∈ s, a φ p.1 * φ p.2 := by
  classical
  have hF : IsLocallyConstant (fun u => fun v => f (u, v)) := isLocallyConstant_curry hf
  have hK₁ : IsCompact (Prod.fst '' tsupport f) := hf.2.isCompact.image continuous_fst
  have hzero : ∀ u, u ∉ Prod.fst '' tsupport f → (fun v => f (u, v)) = 0 := by
    intro u hu; funext v
    by_contra h
    exact hu ⟨(u, v), subset_tsupport _ h, rfl⟩
  have hfin : (Set.range (fun u => fun v => f (u, v))).Finite := by
    have : CompactSpace (Prod.fst '' tsupport f) := isCompact_iff_compactSpace.1 hK₁
    have h1 : (Set.range ((fun u => fun v => f (u, v)) ∘ ((↑) : Prod.fst '' tsupport f → X))).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ Prod.fst '' tsupport f
    · exact Or.inl ⟨⟨u, hu⟩, rfl⟩
    · exact Or.inr (hzero u hu)
  refine ⟨hfin.toFinset.erase 0, fun φ u => if (fun v => f (u, v)) = φ then 1 else 0, ?_, ?_, ?_⟩
  · intro φ hφ
    have hφ0 : φ ≠ 0 := Finset.ne_of_mem_erase hφ
    refine isTest_of_lc (hF.comp fun ψ => if ψ = φ then (1:ℂ) else 0) hK₁ ?_
    intro u hu
    by_contra hK
    apply hu
    show (if (fun v => f (u, v)) = φ then (1:ℂ) else 0) = 0
    rw [hzero u hK, if_neg (Ne.symm hφ0)]
  · intro φ hφ
    obtain ⟨u, rfl⟩ : φ ∈ Set.range (fun u => fun v => f (u, v)) :=
      (hfin.mem_toFinset).1 (Finset.mem_of_mem_erase hφ)
    exact isTest_fibre hf u
  · rintro ⟨u, v⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have h0 : (fun v => f (u, v)) = 0 := by
        by_contra h0
        exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨u, rfl⟩⟩)
      exact congrFun h0 v

theorem tensorRep_eq {G H : Type} [Group G] [Group H] {W₁ : G → (X → ℂ) → X → ℂ}
    {W₂ : H → (Y → ℂ) → Y → ℂ} (hW₁ : IsTestRep W₁) (hW₂ : IsTestRep W₂) {ι : Type} (s : Finset ι)
    (A : ι → X → ℂ) (B : ι → Y → ℂ) (hA : ∀ j ∈ s, IsTest (A j)) (hB : ∀ j ∈ s, IsTest (B j))
    (f : X × Y → ℂ) (hf : ∀ p : X × Y, f p = ∑ j ∈ s, A j p.1 * B j p.2) (gh : G × H) :
    tensorRep W₁ W₂ gh f = fun p => ∑ j ∈ s, W₁ gh.1 (A j) p.1 * W₂ gh.2 (B j) p.2 := by
  funext p
  have h1 : ∀ u, (fun v => f (u, v)) = ∑ j ∈ s, A j u • B j := by
    intro u; funext v; rw [hf (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
  have h2 : (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) = ∑ j ∈ s, W₂ gh.2 (B j) p.2 • A j := by
    funext u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1 u, map_sum hW₂ gh.2 s _ _ hB, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tensorRep_apply, h2, map_sum hW₁ gh.1 s _ _ hA, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul, mul_comm]

end Prod
end GlobalTheory.JR.WeilProd.TensorTest

namespace GlobalTheory.JR.WeilProd
open TensorTest

theorem isTestRep_tensorRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  intro hW₁ hW₂
  have hslice : ∀ f : X × Y → ℂ, IsTest f → ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
    intro f hf h y
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have e : (fun u => W₂ h (fun v => f (u, v)) y) = ∑ φ ∈ s, W₂ h φ y • a φ := by
      funext u
      have h1 : (fun v => f (u, v)) = ∑ φ ∈ s, a φ u • φ := by
        funext v; rw [hfs (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum hW₂ h s (fun φ => a φ u) (fun φ => φ) hb, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp [smul_eq_mul, mul_comm]
    rw [e]
    exact isTest_sum s _ fun φ hφ => isTest_smul _ (ha φ hφ)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun f hf => ⟨isTest_fibre hf, hslice f hf⟩⟩
  · intro gh f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh]
    exact isTest_sum_fn s _ fun φ hφ => isTest_mul_prod (hW₁.1 _ _ (ha φ hφ)) (hW₂.1 _ _ (hb φ hφ))
  · intro f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs 1]
    funext p
    rw [hfs p]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_one, Prod.snd_one]
    rw [hW₁.2.1 _ (ha φ hφ), hW₂.2.1 _ (hb φ hφ)]
  · intro gh gh' f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have hs' : ∀ p, tensorRep W₁ W₂ gh' f p = ∑ φ ∈ s, W₁ gh'.1 (a φ) p.1 * W₂ gh'.2 φ p.2 := fun p => by
      rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh']
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs (gh * gh'),
      tensorRep_eq hW₁ hW₂ s (fun φ => W₁ gh'.1 (a φ)) (fun φ => W₂ gh'.2 φ) (fun φ hφ => hW₁.1 _ _ (ha φ hφ))
        (fun φ hφ => hW₂.1 _ _ (hb φ hφ)) _ hs' gh]
    funext p
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hW₁.2.2.1 _ _ _ (ha φ hφ), hW₂.2.2.1 _ _ _ (hb φ hφ)]
  · intro gh c f f' hf hf'
    funext p
    have e2 : (fun u => W₂ gh.2 (fun v => (c • f + f') (u, v)) p.2) =
        c • (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) + (fun u => W₂ gh.2 (fun v => f' (u, v)) p.2) := by
      funext u
      show W₂ gh.2 (c • (fun v => f (u, v)) + fun v => f' (u, v)) p.2 = _
      rw [hW₂.2.2.2 gh.2 c _ _ (isTest_fibre hf u) (isTest_fibre hf' u)]
      rfl
    rw [tensorRep_apply, e2, hW₁.2.2.2 gh.1 c _ _ (hslice f hf _ _) (hslice f' hf' _ _)]
    rfl

end GlobalTheory.JR.WeilProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProductStatement
open GlobalTheory.JR GlobalTheory.JR.WeilProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  first | exact @GlobalTheory.JR.WeilProd.isTestRep_tensorRep | exact GlobalTheory.JR.WeilProd.isTestRep_tensorRep | (intros; apply GlobalTheory.JR.WeilProd.isTestRep_tensorRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourBProdIterated
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourBProdIterated
open GlobalTheory.JR MeasureTheory

theorem GlobalTheory.JR.fourB_prod_iterated : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  intro V V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he hes B B₁ B₂ hB₁ hB₂ hB μ μ₁ μ₂ hμ hμ₁ hμ₂
  let h : V ≃ₜ V₁ × V₂ := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  let hm : V ≃ᵐ V₁ × V₂ := h.toMeasurableEquiv
  haveI : (Measure.map e μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e he hes
  haveI : (μ₁.prod μ₂).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ₁ μ₂
  set k := Measure.addHaarScalarFactor (Measure.map e μ) (μ₁.prod μ₂) with hk
  have hkeq : Measure.map e μ = k • (μ₁.prod μ₂) := Measure.isAddLeftInvariant_eq_smul _ _
  have hkpos : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨((k : ℝ) : ℂ), by exact_mod_cast hkpos.ne', fun φ hφ y => ?_⟩
  have hmap : Measure.map hm μ = Measure.map e μ := rfl
  have step1 : fourB μ B φ y = ∫ q, φ (e.symm q) * B (e.symm q) y ∂(Measure.map e μ) := by
    rw [← hmap, hm.measurableEmbedding.integral_map]
    simp [fourB, hm, h]
  rw [step1, hkeq, integral_smul_nnreal_measure]
  have hcont : Continuous fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) :=
    (hφ.1.continuous.comp hes).mul ((hB₁.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.1, (e y).1))).mul
      (hB₂.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.2, (e y).2))))
  have hsupp : HasCompactSupport fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    have : HasCompactSupport (φ ∘ h.symm) := hφ.2.comp_homeomorph h.symm
    exact this.mul_right
  have hint := hcont.integrable_of_hasCompactSupport hsupp (μ := μ₁.prod μ₂)
  have e2 : (fun q : V₁ × V₂ => φ (e.symm q) * B (e.symm q) y) =
      fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    ext q; rw [hB]; simp
  rw [e2, integral_prod _ hint]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  congr 1; ext v; ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourBProdIteratedStatement
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourB_prod_iterated_alt : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  first | exact @GlobalTheory.JR.fourB_prod_iterated | exact GlobalTheory.JR.fourB_prod_iterated | (intros; apply GlobalTheory.JR.fourB_prod_iterated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConditionProductSplitting
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilProd

def transRep {G H X Y : Type} (ρ : G → H) (e : X ≃ Y) (W : H → (Y → ℂ) → Y → ℂ) : G → (X → ℂ) → X → ℂ :=
  fun g f x => W (ρ g) (f ∘ e.symm) (e x)

theorem isTest_comp_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : IsTest f) : IsTest (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem isTestRep_transRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (ρ : G →* H) (e : X ≃ₜ Y) (W : H → (Y → ℂ) → Y → ℂ) (hW : IsTestRep W) :
    IsTestRep (transRep ρ e.toEquiv W) := by
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have ht : ∀ f, IsTest f → IsTest (f ∘ e.symm) := fun f hf => isTest_comp_homeomorph e.symm hf
  refine ⟨fun g f hf => isTest_comp_homeomorph e (h1 _ _ (ht f hf)), fun f hf => ?_, fun g h f hf => ?_,
    fun g c f f' hf hf' => ?_⟩
  · funext x
    simp [transRep, map_one, h2 _ (ht f hf)]
  · funext x
    show W (ρ (g * h)) (f ∘ e.symm) (e x) = W (ρ g) ((fun x => W (ρ h) (f ∘ e.symm) (e x)) ∘ e.symm) (e x)
    rw [map_mul, h3 _ _ _ (ht f hf)]
    congr 1
    funext y; simp
  · funext x
    have : (c • f + f') ∘ e.toEquiv.symm = c • (f ∘ e.symm) + f' ∘ e.symm := rfl
    simp only [transRep, this, h4 _ c _ _ (ht f hf) (ht f' hf')]
    rfl

theorem norm_prod_apply {R S T : Type} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] (p : S × T) :
    Algebra.norm R p = Algebra.norm R p.1 * Algebra.norm R p.2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem trace_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (k : A.K) :
    Algebra.trace F A.K k = Algebra.trace F A₁.K (eK k).1 + Algebra.trace F A₂.K (eK k).2 := by
  rw [← Algebra.trace_eq_of_algEquiv eK, Algebra.trace_prod_apply]

theorem norm_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (k : A.K) :
    Algebra.norm F k = Algebra.norm F (eK k).1 * Algebra.norm F (eK k).2 := by
  rw [← Algebra.norm_eq_of_algEquiv eK, norm_prod_apply]

theorem splitL [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (y : A.L) :
    eK (A.NL y) = (A₁.NL (eL y).1, A₂.NL (eL y).2) ∧
      eK (Algebra.trace A.K A.L y) = (Algebra.trace A₁.K A₁.L (eL y).1, Algebra.trace A₂.K A₂.L (eL y).2) := by
  obtain ⟨-, i₁, n₁, t₁, -⟩ := Et.quadratic_structure F E A₁
  obtain ⟨-, i₂, n₂, t₂, -⟩ := Et.quadratic_structure F E A₂
  obtain ⟨-, -, n, t, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hK, -, hst⟩ := hS
  have e1 := hK (A.NL y)
  rw [n, map_mul, hst] at e1
  have e2 := hK (Algebra.trace A.K A.L y)
  rw [t, map_add (f := _), hst] at e2
  refine ⟨Prod.ext (i₁ ?_) (i₂ ?_), Prod.ext (i₁ ?_) (i₂ ?_)⟩
  · rw [n₁]; simpa using (congrArg Prod.fst e1).symm
  · rw [n₂]; simpa using (congrArg Prod.snd e1).symm
  · rw [t₁]; simpa using (congrArg Prod.fst e2).symm
  · rw [t₂]; simpa using (congrArg Prod.snd e2).symm

theorem kerL_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) :
    A.kerL ψ x y' y = A₁.kerL ψ (eK x).1 (eL y').1 (eL y).1 * A₂.kerL ψ (eK x).2 (eL y').2 (eL y).2 := by
  have h := (splitL A A₁ A₂ eK eL hS (star y' * y)).2
  rw [map_mul eL, hS.2.2] at h
  simp only [Et.kerL, Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, h]
  rfl

theorem psiK_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (z x : A.K) (y : A.L) :
    A.psiK ψ (z * x * A.NL y) = A₁.psiK ψ ((eK z).1 * (eK x).1 * A₁.NL (eL y).1) *
      A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) := by
  simp only [Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, map_mul, (splitL A A₁ A₂ eK eL hS y).1]
  rfl

theorem etaK_split [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (s : A.Kˣ) :
    A.etaK s = A₁.etaK (eK s).1 * A₂.etaK (eK s).2 := by
  have hu : IsUnit (eK (s : A.K)) := s.isUnit.map eK
  have h₁ : Algebra.norm F (eK s).1 ≠ 0 := ((Prod.isUnit_iff.1 hu).1.map (Algebra.norm F)).ne_zero
  have h₂ : Algebra.norm F (eK s).2 ≠ 0 := ((Prod.isUnit_iff.1 hu).2.map (Algebra.norm F)).ne_zero
  simp only [Et.etaK]
  rw [norm_split A A₁ A₂ eK, (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ h₁ h₂]

theorem smul_split (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (k : A.K) (y : A.L) :
    eL (k • y) = ((eK k).1 • (eL y).1, (eK k).2 • (eL y).2) := by
  rw [Algebra.smul_def, map_mul, hS.1, Algebra.smul_def, Algebra.smul_def]
  rfl

theorem continuous_kerL [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) :
    Continuous (fun p : A.L × A.L => A.kerL ψ x p.1 p.2) := by
  have := U.ultraF; have := U.lcF; have := EtMeas.finite_L A
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  let T : A.L →ₗ[F] F :=
    (Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F))
  have hT : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
  exact (DualLattice.stdChar_continuous hψ).comp (hT.comp ((hs.comp continuous_fst).mul continuous_snd))

theorem tensor_isTestRep : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ →
    IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct

theorem fourB_split : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁]
    [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁]
    [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂]
    [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂]
    (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm →
    ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ),
    Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) →
    (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) →
    ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure →
    μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y,
      fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := GlobalTheory.T.fourB_prod_iterated_alt

theorem absK_split : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := GlobalTheory.T.absK_mul_of_etale_splitting

theorem map_nS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : R) :
    SpecialLinearGroup.map f (nS z) = nS (f z) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [nS]

theorem map_mS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (s : Rˣ) :
    SpecialLinearGroup.map f (mS s) = mS (Units.map (f : R →* S) s) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [mS]

theorem map_wS {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    SpecialLinearGroup.map f (wS R) = wS S := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [wS]

section rel
variable [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
  (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K)
  (W₁ : SpecialLinearGroup (Fin 2) A₁.K → (A₁.L → ℂ) → A₁.L → ℂ)
  (W₂ : SpecialLinearGroup (Fin 2) A₂.K → (A₂.L → ℂ) → A₂.L → ℂ) (γ₁ γ₂ : ℂ) (μ₁ : Measure A₁.L) (μ₂ : Measure A₂.L)
  (hW₁ : A₁.IsWeil ψ (eK x).1 A₁.etaK μ₁ γ₁ W₁) (hW₂ : A₂.IsWeil ψ (eK x).2 A₂.etaK μ₂ γ₂ W₂)
  (f : A₁.L × A₂.L → ℂ) (hf1 : ∀ u, IsTest (fun v => f (u, v)))
  (hf2 : ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y))
include hS hW₁ hW₂ hf1 hf2

theorem rel_n (z : A.K) (y : A.L) :
    tensorRep W₁ W₂ (nS (eK z).1, nS (eK z).2) f (eL y) = A.psiK ψ (z * x * A.NL y) * f (eL y) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (nS (eK z).2) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.psiK ψ ((eK z).2 * (eK x).2 * A₂.NL (eL y).2) * f (u, (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).1 _ _
  have t := hf2 (nS (eK z).2) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).1, psiK_split A A₁ A₂ eK eL hS ψ z x y]
  ring

theorem rel_m (s : A.Kˣ) (s₁ : A₁.Kˣ) (s₂ : A₂.Kˣ) (hs₁ : (s₁ : A₁.K) = (eK s).1) (hs₂ : (s₂ : A₂.K) = (eK s).2)
    (y : A.L) :
    tensorRep W₁ W₂ (mS s₁, mS s₂) f (eL y) = A.etaK s * (A.absK s : ℂ) * f (eL ((s : A.K) • y)) := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (mS s₂) (fun v => f (u, v)) (eL y).2) =
      fun u => A₂.etaK s₂ * (A₂.absK s₂ : ℂ) * f (u, (s₂ : A₂.K) • (eL y).2) :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.1 _ _
  have t := hf2 (mS s₂) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.1, smul_split A A₁ A₂ eK eL hS, etaK_split A A₁ A₂ eK s,
    absK_split F E A A₁ A₂ eK s, hs₁, hs₂]
  push_cast
  ring

theorem rel_w (y : A.L) :
    tensorRep W₁ W₂ (wS A₁.K, wS A₂.K) f (eL y) = γ₁ * γ₂ *
      ∫ u, (∫ v, f (u, v) * A₂.kerL ψ (eK x).2 v (eL y).2 ∂μ₂) * A₁.kerL ψ (eK x).1 u (eL y).1 ∂μ₁ := by
  simp only [tensorRep]
  have e2 : (fun u => W₂ (wS A₂.K) (fun v => f (u, v)) (eL y).2) =
      fun u => γ₂ * fourB μ₂ (A₂.kerL ψ (eK x).2) (fun v => f (u, v)) (eL y).2 :=
    funext fun u => (hW₂.2 _ (hf1 u)).2.2 _
  have t := hf2 (wS A₂.K) (eL y).2
  rw [e2] at t ⊢
  rw [(hW₁.2 _ t).2.2]
  simp only [fourB, mul_assoc, integral_const_mul]

end rel

theorem weilAt_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
    IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  intro F E _ _ _ _ U A A₁ A₂ eK eL hS h₁ h₂ ψ hψ x μ hμ
  have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A; have := EtMeas.finite_L A₁; have := EtMeas.finite_L A₂
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.L
  let f₁ : A.K →+* A₁.K := (RingHom.fst A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let f₂ : A.K →+* A₂.K := (RingHom.snd A₁.K A₂.K).comp (eK : A.K →+* A₁.K × A₂.K)
  let x₁ : A₁.Kˣ := Units.map (f₁ : A.K →* A₁.K) x
  let x₂ : A₂.Kˣ := Units.map (f₂ : A.K →* A₂.K) x
  obtain ⟨μ₁, hμ₁⟩ := EtMeas.exists_selfDual_L A₁ ψ hψ x₁
  obtain ⟨μ₂, hμ₂⟩ := EtMeas.exists_selfDual_L A₂ ψ hψ x₂
  obtain ⟨γ₁, W₁, hW₁⟩ := h₁ ψ hψ x₁ μ₁ hμ₁
  obtain ⟨γ₂, W₂, hW₂⟩ := h₂ ψ hψ x₂ μ₂ hμ₂
  have hc₁ : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc₂ : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let eH : A.L ≃ₜ A₁.L × A₂.L := ⟨eL.toEquiv, hc₁, hc₂⟩
  obtain ⟨c, hc0, hc⟩ := fourB_split eL.toRingEquiv.toAddEquiv hc₁ hc₂ (A.kerL ψ x) (A₁.kerL ψ x₁)
    (A₂.kerL ψ x₂) (continuous_kerL A₁ ψ hψ _) (continuous_kerL A₂ ψ hψ _)
    (fun y' y => kerL_split A A₁ A₂ eK eL hS ψ x y' y) μ μ₁ μ₂ hμ.1 hμ₁.1 hμ₂.1
  let ρ : SpecialLinearGroup (Fin 2) A.K →* SpecialLinearGroup (Fin 2) A₁.K × SpecialLinearGroup (Fin 2) A₂.K :=
    (SpecialLinearGroup.map f₁).prod (SpecialLinearGroup.map f₂)
  obtain ⟨hT, hfib⟩ := tensor_isTestRep W₁ W₂ hW₁.1 hW₂.1
  refine ⟨γ₁ * γ₂ / c, transRep ρ eH.toEquiv (tensorRep W₁ W₂), isTestRep_transRep ρ eH _ hT, fun φ hφ => ?_⟩
  have hf : IsTest (φ ∘ eH.symm) := isTest_comp_homeomorph eH.symm hφ
  obtain ⟨hf1, hf2⟩ := hfib _ hf
  have hy : ∀ y, eH.symm (eL y) = y := fun y => eL.symm_apply_apply y
  have hx₁ : ((x₁ : A₁.Kˣ) : A₁.K) = (eK x).1 := rfl
  have hx₂ : ((x₂ : A₂.Kˣ) : A₂.K) = (eK x).2 := rfl
  refine ⟨fun z y => ?_, fun s y => ?_, fun y => ?_⟩
  · show tensorRep W₁ W₂ (ρ (nS z)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (nS z) = (nS (eK z).1, nS (eK z).2) := Prod.ext (map_nS f₁ z) (map_nS f₂ z)
    rw [hρ, rel_n A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (mS s)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (mS s) = (mS (Units.map (f₁ : A.K →* A₁.K) s), mS (Units.map (f₂ : A.K →* A₂.K) s)) :=
      Prod.ext (map_mS f₁ s) (map_mS f₂ s)
    rw [hρ, rel_m A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2 s _ _ rfl rfl]
    simp [hy]
  · show tensorRep W₁ W₂ (ρ (wS A.K)) (φ ∘ eH.symm) (eL y) = _
    have hρ : ρ (wS A.K) = (wS A₁.K, wS A₂.K) := Prod.ext (map_wS f₁) (map_wS f₂)
    rw [hρ, rel_w A A₁ A₂ eK eL hS ψ x W₁ W₂ γ₁ γ₂ μ₁ μ₂ hW₁ hW₂ _ hf1 hf2, hc φ hφ y]
    simp only [Function.comp]
    field_simp
    rfl

end GlobalTheory.JR.WeilProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConditionProductSplittingStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_condition_product_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  first | exact @GlobalTheory.JR.WeilProd.weilAt_prod | exact GlobalTheory.JR.WeilProd.weilAt_prod | (intros; apply GlobalTheory.JR.WeilProd.weilAt_prod <;> assumption)
end

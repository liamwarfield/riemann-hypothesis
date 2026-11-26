module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDet
open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.IndexDet

theorem relIndex_mul_measure_of_isCompact {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsAddLeftInvariant] {H L : AddSubgroup G} (hL : IsCompact (L : Set G))
    (hH : IsOpen (H : Set G)) (hHL : H ≤ L) :
    (H.relIndex L : ℝ≥0∞) * μ H = μ L := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.addSubgroupOf L : AddSubgroup L) : Set L) := hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho
  haveI : (H.addSubgroupOf L).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact GlobalTheory.BaseModule.addRelIndex_mul_measure H L hHL hH.measurableSet μ

theorem relIndex_eq_distribHaarChar_det_mul (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k)
    (A₀ A : AddSubgroup (Fin n → k)) (hA : IsCompact (A : Set (Fin n → k)))
    (hA₀ : IsOpen (A₀ : Set (Fin n → k))) (h₀ : A₀ ≤ A)
    (h₁ : A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) :
    ((A₀.relIndex A : ℕ) : ℝ) = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) *
      ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  set B := A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom with hB
  let μ : Measure (Fin n → k) := Measure.pi fun _ : Fin n => (Measure.addHaar : Measure k)
  have hBset : (B : Set (Fin n → k)) = (fun x => (g⁻¹).val *ᵥ x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.val *ᵥ x, hx, ?_⟩
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      change g.val *ᵥ ((g⁻¹).val *ᵥ y) ∈ A
      simpa only [mulVec_mulVec, Units.mul_inv, one_mulVec, SetLike.mem_coe] using hy
  have hBc : IsCompact (B : Set (Fin n → k)) := by
    rw [hBset]
    exact hA.image (by fun_prop)
  have hAm : MeasurableSet (A : Set (Fin n → k)) := hA.measurableSet
  have hm : Measurable (g.val.mulVec) := (continuous_const.matrix_mulVec continuous_id).measurable
  have hscale : μ A = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * μ B := by
    have h := GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure k) g.val
      (Matrix.GeneralLinearGroup.det g) rfl
    have h2 := congrArg (fun m : Measure (Fin n → k) => m (A : Set (Fin n → k))) h
    simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hAm] at h2
    exact h2.symm
  have i1 := relIndex_mul_measure_of_isCompact μ hA hA₀ h₀
  have i2 := relIndex_mul_measure_of_isCompact μ hBc hA₀ h₁
  have hpos : μ A₀ ≠ 0 := (hA₀.measure_pos μ ⟨0, A₀.zero_mem⟩).ne'
  have htop : μ A₀ ≠ ∞ := ((measure_mono h₀).trans_lt hA.measure_lt_top).ne
  have key : ((A₀.relIndex A : ℕ) : ℝ≥0∞) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * ((A₀.relIndex B : ℕ) : ℝ≥0∞) := by
    refine (ENNReal.mul_left_inj hpos htop).mp ?_
    rw [i1, hscale, ← i2, mul_assoc]
  have := congrArg ENNReal.toReal key
  simpa using this

end GlobalTheory.CompanionTheory.IndexDet
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDetStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_lattice_eq_haar_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k) (A₀ A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → A₀ ≤ A → A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom → ((A₀.relIndex A : ℕ) : ℝ) = (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) * ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | exact GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | (intros; apply GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul <;> assumption)
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.mir

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def gLat {n : ℕ} (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) :=
  A.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).toAddMonoidHom

theorem mulVec_inv_mulVec {n : ℕ} (g : GL (Fin n) k) (x : Fin n → k) :
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv {n : ℕ} (g : GL (Fin n) k) (x : Fin n → k) :
    (g : Matrix (Fin n) (Fin n) k) *ᵥ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem comap_gLat {n : ℕ} (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) :
    (gLat g A).comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom = A := by
  ext x
  show ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) ∈ A ↔ x ∈ A
  rw [mulVec_inv_mulVec]

theorem continuous_mulVec' {n : ℕ} (M : Matrix (Fin n) (Fin n) k) : Continuous fun x : Fin n → k => M *ᵥ x :=
  continuous_const.matrix_mulVec continuous_id

theorem isLat_gLat {m : ℕ} (g : GL (Fin (m + 1)) k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) :
    IsLat (gLat g A) := by
  have e : ((gLat g A : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) =
      (fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) '' (A : Set (Fin (m + 1) → k)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, mulVec_mulVec_inv g x⟩
    · rintro ⟨y, hy, rfl⟩
      show ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ _ ∈ A
      rw [mulVec_inv_mulVec]; exact hy
  refine ⟨?_, ?_⟩
  · rw [e]; exact hA.1.image (continuous_mulVec' _)
  · exact hA.2.preimage (continuous_mulVec' _)

theorem isLat_sup {m : ℕ} {A B : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hB : IsLat B) : IsLat (A ⊔ B) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have e : ((A ⊔ B : AddSubgroup (Fin (m + 1) → k)) : Set (Fin (m + 1) → k)) =
      (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => p.1 + p.2) '' ((A : Set _) ×ˢ (B : Set _)) := by
    ext x
    rw [SetLike.mem_coe, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨(y, z), ⟨hy, hz⟩, rfl⟩
    · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
      exact ⟨y, hy, z, hz, rfl⟩
  rw [e]
  exact (hA.1.prod hB.1).image continuous_add

theorem avg_eq_of_data (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) (p) (hp : AvgData ψ h π ξ A v p) :
    avg ψ h π ξ A v =
      ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v := by
  obtain ⟨q, hq, hav⟩ := avg_spec ψ h π hψ hπ ξ A hA v
  rw [hav]
  set f : (Fin (m + 1) → k) → V := fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
    with hf
  have inv : ∀ (r : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)), AvgData ψ h π ξ A v r →
      ∀ x, ∀ d ∈ r.1, f (x + d) = f x := by
    intro r hr x d hd
    simp only [hf]
    rw [colEl_add, map_mul, Module.End.mul_apply, hr.2.2.1 d hd, dotProduct_add, AddChar.map_add_eq_mul,
      hr.2.2.2.1 d hd, mul_one]

  have hpq : ∑ t ∈ p.2, ∑ s ∈ q.2, f (s + t) = (p.2.card : ℂ) • ∑ s ∈ q.2, f s := by
    rw [Finset.sum_congr rfl (fun t ht => sum_translate_transversal A q.1 q.2 hq.2.2.2.2.1 hq.2.2.2.2.2 f
      (inv q hq) t (hp.2.2.2.2.1 t ht)), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  have hqp : ∑ s ∈ q.2, ∑ t ∈ p.2, f (t + s) = (q.2.card : ℂ) • ∑ t ∈ p.2, f t := by
    rw [Finset.sum_congr rfl (fun s hs => sum_translate_transversal A p.1 p.2 hp.2.2.2.2.1 hp.2.2.2.2.2 f
      (inv p hp) s (hq.2.2.2.2.1 s hs)), Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  have hcomm : ∑ t ∈ p.2, ∑ s ∈ q.2, f (s + t) = ∑ s ∈ q.2, ∑ t ∈ p.2, f (t + s) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [add_comm]
  obtain ⟨t₀, ⟨ht₀, _⟩, _⟩ := hp.2.2.2.2.2 0 A.zero_mem
  obtain ⟨s₀, ⟨hs₀, _⟩, _⟩ := hq.2.2.2.2.2 0 A.zero_mem
  have hcp : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht₀)
  have hcq : (q.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs₀)
  have key : (p.2.card : ℂ) • ∑ s ∈ q.2, f s = (q.2.card : ℂ) • ∑ t ∈ p.2, f t := by
    rw [← hpq, ← hqp, hcomm]
  have key2 := congrArg (fun x => ((p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹) • x) key
  simp only [smul_smul] at key2
  rw [show (p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹ * (p.2.card : ℂ) = (q.2.card : ℂ)⁻¹ by field_simp,
    show (p.2.card : ℂ)⁻¹ * (q.2.card : ℂ)⁻¹ * (q.2.card : ℂ) = (p.2.card : ℂ)⁻¹ by field_simp] at key2
  exact key2

theorem avg_conj (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hψ : Continuous ψ) (hπ : IsSmooth π) (g : GL (Fin (m + 1)) k)
    (ξ η : Fin (m + 1) → k) (hη : ∀ x, η ⬝ᵥ ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = ξ ⬝ᵥ x)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    π (blkAt k (m + 1) N (by omega) g) (avg ψ h π ξ A v) =
      avg ψ h π η (gLat g A) (π (blkAt k (m + 1) N (by omega) g) v) := by
  classical
  set P := blkAt k (m + 1) N (by omega) g with hP
  have hconj : ∀ x, π P (π (colEl k m N h x) v) =
      π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) (π P v) := by
    intro x
    have e : P * colEl k m N h x = colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) * P := by
      rw [← blkAt_conj_colEl h g x, ← hP]; group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  obtain ⟨p, hp, hav⟩ := avg_spec ψ h π hψ hπ ξ A hA v
  obtain ⟨hMA, hMo, hMfix, hMchar, hT, hu⟩ := hp
  let gv : (Fin (m + 1) → k) → (Fin (m + 1) → k) := fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x
  have ginj : Function.Injective gv := fun x y e => by
    have := congrArg (fun z => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ z) e
    simpa [gv, mulVec_inv_mulVec] using this
  let p' : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k) := (gLat g p.1, p.2.image gv)
  have hp' : AvgData ψ h π η (gLat g A) (π P v) p' := by
    refine ⟨fun x hx => hMA hx, hMo.preimage (continuous_mulVec' _), fun a ha => ?_, fun a ha => ?_, ?_, ?_⟩
    · have e := hconj (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a)
      rw [mulVec_mulVec_inv, hMfix (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ha] at e
      exact e.symm
    · have e := hη (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a)
      rw [mulVec_mulVec_inv] at e
      rw [e]; exact hMchar (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ha
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
      show _ *ᵥ (gv t') ∈ A
      simp only [gv, mulVec_inv_mulVec]; exact hT t' ht'
    · intro a ha
      obtain ⟨t, ⟨htT, hta⟩, hun⟩ := hu _ ha
      refine ⟨gv t, ⟨Finset.mem_image_of_mem _ htT, ?_⟩, ?_⟩
      · show _ *ᵥ (a - gv t) ∈ p.1
        rw [Matrix.mulVec_sub]; simp only [gv, mulVec_inv_mulVec]; exact hta
      · rintro t' ⟨ht', ht'a⟩
        obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.1 ht'
        congr 1
        refine hun t1 ⟨ht1, ?_⟩
        have : _ *ᵥ (a - gv t1) ∈ p.1 := ht'a
        rwa [Matrix.mulVec_sub, mulVec_inv_mulVec] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_eq_of_data ψ h π hψ hπ η (isLat_gLat g hA) _ p' hp', hav, map_smul, map_sum,
    Finset.card_image_of_injective _ ginj, Finset.sum_image (fun x _ y _ e => ginj e)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hconj, hη]

theorem dens_mir {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : Lv ψ h π s B)
    {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') : MirEq π m (by omega) (s + 1) B' := by
  intro p hp v w
  set P := blkAt k (m + 1) N (by omega) p with hPdef
  obtain ⟨A₁, hA₁, h01, hA₁'⟩ := hD (π P v) (π P w)
  obtain ⟨A₂, hA₂, h02, hA₂'⟩ := hD v w

  set A' := A₂ ⊔ A₁.comap (Matrix.mulVecLin (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom with hA'
  have hA'l : IsLat A' := by
    refine isLat_sup hA₂ ?_
    have := isLat_gLat p⁻¹ hA₁
    simpa [gLat] using this
  set A := gLat p A' with hAdef
  have hAl : IsLat A := isLat_gLat p hA'l
  have h1A : A₁ ≤ A := by
    intro x hx
    show _ *ᵥ x ∈ A'
    refine AddSubgroup.mem_sup_right ?_
    show (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ (_ *ᵥ x) ∈ A₁
    rw [mulVec_mulVec_inv]; exact hx
  have h2A' : A₂ ≤ A' := le_sup_left
  have hη : ∀ x, xi0 k m ⬝ᵥ ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = xi0 k m ⬝ᵥ x := by
    intro x
    rw [Matrix.dotProduct_mulVec]
    exact congrArg (· ⬝ᵥ x) hp
  have e1 := hA₁' A hAl h1A
  have e2 := hA₂' A' hA'l h2A'
  have hconj := avg_conj ψ h π hB.cont hB.smooth p (xi0 k m) (xi0 k m) hη hA'l v
  rw [← hPdef] at hconj

  have hBP : ∀ a b, B (π P a) (π P b) = ((nabs k (Matrix.GeneralLinearGroup.det p) ^ s : ℝ) : ℂ) * B a b := by
    intro a b
    have e := hB.mir (glEmb k (m + 1) p) (glEmb_mem_Mir k (m + 1) p) a b
    rw [blkAt_glEmb h p, det_glEmb] at e
    exact e

  have hidx : ((A₀.relIndex A : ℕ) : ℝ) =
      (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det p) : ℝ) * ((A₀.relIndex A' : ℕ) : ℝ) := by
    have := GlobalTheory.T.relIndex_lattice_eq_haar_det k (m + 1) p A₀ A hAl.1 hA₀.2 (h01.trans h1A)
      (by rw [comap_gLat]; exact h02.trans h2A')
    rwa [comap_gLat] at this
  rw [e1, ← hconj, hBP, e2]
  have hn : nabs k (Matrix.GeneralLinearGroup.det p) =
      (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det p) : ℝ) := rfl
  have hpos : 0 < nabs k (Matrix.GeneralLinearGroup.det p) := by
    rw [hn]; exact NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos
  have hidxC : ((A₀.relIndex A : ℕ) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det p) : ℝ) : ℂ) * ((A₀.relIndex A' : ℕ) : ℂ) := by
    rw [hn]; exact_mod_cast hidx
  rw [hidxC, Real.rpow_add hpos, Real.rpow_one]
  push_cast
  ring

end PositivityTheory.RgUd.Form.LeviSmoothness.mir

module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.RadCov

open scoped InnerProductSpace

theorem mem_of_orth_piece {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : Submodule ℂ E} (hAB : A ≤ B) {y : E} (hy : y ∈ B)
    (ho : y ∈ (Aᗮ ⊓ B)ᗮ) : y ∈ A := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := A) y
  have hwB : w ∈ B := by
    have := B.sub_mem hy (hAB hv)
    simpa using this
  have h1 : ⟪w, v + w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 ho w ⟨hw, hwB⟩
  have h2 : ⟪w, v⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 hw v hv
  rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
  simpa [h1] using hv

theorem exists_orthonormal_family {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Submodule ℂ E) {r : ℕ} (hr : Module.finrank ℂ P = r) :
    ∃ e : Fin r → E, Orthonormal ℂ e ∧ (∀ j, e j ∈ P) ∧
      ∀ y, (∀ j, ⟪e j, y⟫_ℂ = 0) → y ∈ Pᗮ := by
  subst hr
  let b := stdOrthonormalBasis ℂ P
  refine ⟨fun j => (b j : E), ?_, fun j => (b j).2, fun y hy => ?_⟩
  · exact b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  · rw [Submodule.mem_orthogonal]
    intro u hu
    have h := congrArg (fun x : P => (x : E)) (b.sum_repr ⟨u, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, hy j, mul_zero]

theorem exists_orthonormal_block_frame :
    ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ →
      (∀ b, m ≤ b → W b = ⊤) →
      (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) →
      ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧
        ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  intro n m W r hmono h0 htop hr
  let L : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin n)) := fun b => (W b).map L.toLinearMap
  have hV : ∀ b y, L y ∈ V b ↔ y ∈ W b := fun b y => by
    simp [V]
  have hVm : Monotone V := fun a b h => Submodule.map_mono (hmono h)
  have hfin : ∀ b, Module.finrank ℂ ((V b)ᗮ ⊓ V (b + 1) : Submodule ℂ _) = r b := fun b => by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Nat.le_succ b))
    have h2 : ∀ c, Module.finrank ℂ (V c) = Module.finrank ℂ (W c) := fun c =>
      LinearEquiv.finrank_map_eq L (W c)
    rw [h2, h2, hr] at h1
    exact Nat.add_left_cancel h1
  choose e he hmem hdet using fun b => exists_orthonormal_family _ (hfin b)
  let U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ := fun b => Matrix.of fun i j => e b j i
  have hU : ∀ b y j, ((U b)ᴴ *ᵥ y) j = ⟪e b j, L y⟫_ℂ := fun b y j => by
    simp [U, L, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hUU : ∀ b b' j j', ((U b)ᴴ * U b') j j' = ⟪e b j, e b' j'⟫_ℂ := fun b b' j j' => by
    simp [U, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have hflag : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
    intro k y
    constructor
    · intro hy b hb
      funext j
      rw [hU]
      exact (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm hb ((hV k y).2 hy))
    · intro hy
      have key : ∀ d, L y ∈ V (k + d) → L y ∈ V k := by
        intro d
        induction d with
        | zero => exact id
        | succ d ih =>
          intro h
          refine ih (mem_of_orth_piece (hVm (Nat.le_succ (k + d))) h (hdet _ _ fun j => ?_))
          rw [← hU, hy _ (Nat.le_add_right k d)]
          rfl
      refine (hV k y).1 (key m ((hV _ y).2 ?_))
      rw [htop _ (Nat.le_add_left m k)]
      trivial
  have h1 : ∀ b, (U b)ᴴ * U b = 1 := fun b => by
    ext j j'
    rw [hUU, orthonormal_iff_ite.1 (he b), Matrix.one_apply]
  have hlt : ∀ b b', b' < b → ∀ j j', ⟪e b j, e b' j'⟫_ℂ = 0 := fun b b' h j j' =>
    (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm (Nat.succ_le_of_lt h) (hmem b' j').2)
  have h2 : ∀ b b', b ≠ b' → (U b)ᴴ * U b' = 0 := fun b b' h => by
    ext j j'
    rw [hUU, Matrix.zero_apply]
    rcases lt_or_gt_of_ne h with h | h
    · rw [inner_eq_zero_symm]; exact hlt _ _ h _ _
    · exact hlt _ _ h _ _
  refine ⟨U, ⟨h1, h2, ?_⟩, hflag⟩
  have h3 : ∀ y, (1 - ∑ b ∈ Finset.range m, U b * (U b)ᴴ) *ᵥ y = 0 := by
    intro y
    rw [← Submodule.mem_bot ℂ, ← h0, hflag]
    intro b _
    by_cases hb : m ≤ b
    · refine (hflag m _).1 ?_ b hb
      rw [htop m le_rfl]; trivial
    · rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_sum,
        Finset.sum_eq_single b, ← Matrix.mul_assoc, h1]
      · simp
      · intro c _ hc
        rw [← Matrix.mul_assoc, h2 _ _ hc.symm, Matrix.zero_mul]
      · intro hc
        exact absurd (Finset.mem_range.2 (by omega)) hc
  refine (sub_eq_zero.1 ?_).symm
  ext i k
  have := congrFun (h3 (Pi.single k 1)) i
  simpa using this

end GlobalTheory.RadCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_block_frame_of_complex_flag : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ → (∀ b, m ≤ b → W b = ⊤) → (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) → ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧ ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  first | exact @GlobalTheory.RadCov.exists_orthonormal_block_frame | exact GlobalTheory.RadCov.exists_orthonormal_block_frame | (intros; apply GlobalTheory.RadCov.exists_orthonormal_block_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLattice
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.RowDomain

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

noncomputable def rowLat (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule ℤ (VecInf E k) :=
  AddSubgroup.toIntSubmodule
  { carrier := {z | ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b)}
    zero_mem' := ⟨0, fun y _ => by simp only [zero_dotProduct]; exact Λ₀.zero_mem, by funext w b; simp⟩
    add_mem' := by
      rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
      refine ⟨σ + τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.add_mem (hσ y hy) (hτ y hy)
      convert this using 1
      funext _; simp
    neg_mem' := by
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨-τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.neg_mem (hτ y hy)
      convert this using 1
      funext _; simp }

theorem mem_rowLat {E : Type} [Field E] [NumberField E] {k : ℕ} {Λ₀ : Submodule (𝓞 E) (Fin 1 → E)}
    {Λ' : Submodule (𝓞 E) (Fin k → E)} {z : VecInf E k} : z ∈ rowLat E k Λ₀ Λ' ↔
    ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b) := by
  rfl

theorem hasCov_rowLat (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E) (k : ℕ)
    (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)) (h₀ : Submodule.IsFullLattice E Λ₀)
    (h' : Submodule.IsFullLattice E Λ') : GlobalTheory.HomCovolume.HasCov volume (rowLat E k Λ₀ Λ')
      (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) := by
  classical

  let e : VecInf E k ≃L[ℝ] (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (LinearEquiv.piCongrRight fun _ : InfinitePlace E =>
      (LinearEquiv.funUnique (Fin 1) ℝ (Fin k → ℂ)).symm).toContinuousLinearEquiv
  have hes : ∀ x w b, e.symm x w b = x w 0 b := fun _ _ _ => rfl
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_pi fun _ : InfinitePlace E =>
      MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) (Fin k → ℂ))
  let L' : Submodule ℤ (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (rowLat E k Λ₀ Λ').comap ((e.symm : _ →L[ℝ] VecInf E k).toLinearMap.restrictScalars ℤ)
  have hL' : ∀ z, z ∈ L' ↔ e.symm z ∈ rowLat E k Λ₀ Λ' := fun _ => Iff.rfl
  refine GlobalTheory.HomCovolume.HasCov.of_measurePreserving e hmp (L' := L')
    (fun x => by rw [hL', ContinuousLinearEquiv.symm_apply_apply]) ?_
  have hpos : ∀ j, 0 < detNorm E j (oneInf E j) := fun j => by rw [detNorm_oneInf]; exact one_pos
  obtain ⟨hd, hz, hc⟩ := GlobalTheory.HomCovolume.homCovolume E hE 1 k Λ₀ Λ' h₀ h' (oneInf E 1) (oneInf E k)
    (hpos 1) (hpos k) L' (by
      intro z
      rw [hL', mem_rowLat]
      simp only [of_oneInf, inv_one]
      constructor
      · rintro ⟨τ, hτ, hzτ⟩
        refine ⟨Matrix.of fun _ b => τ b, fun y hy => ?_, fun w => ?_⟩
        · exact hτ y hy
        · ext i b
          fin_cases i
          have := congrFun (congrFun hzτ w) b
          simpa [hes] using this
      · rintro ⟨T, hT, hTz⟩
        refine ⟨fun b => T 0 b, fun y hy => ?_, ?_⟩
        · convert hT y hy using 1
          funext i
          fin_cases i
          rfl
        · funext w b
          have := congrFun (congrFun (hTz w) 0) b
          simpa [hes] using this)
  exact ⟨hd, hz, by rw [hc, pow_one]⟩

theorem rowDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  obtain ⟨hd, hz, hc⟩ := hasCov_rowLat E hE k Λ₀ Λ' h₀ h'

  let b := Module.Free.chooseBasis ℤ (rowLat E k Λ₀ Λ')
  have hspan := b.ofZLatticeBasis_span ℝ
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (VecInf E k))
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ?_, fun T => ?_, fun T τ hτ hT hT' => ?_⟩
  · rw [← hc, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF]
    have hfin : (volume : Measure (VecInf E k)) (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
    exact (ofReal_measureReal hfin).symm
  · obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T
    have hvL : (v : VecInf E k) ∈ rowLat E k Λ₀ Λ' := hspan.le v.2
    obtain ⟨τ, hτ, hvτ⟩ := mem_rowLat.1 hvL
    refine ⟨τ, hτ, ?_⟩
    convert hv using 1
    rw [Submodule.vadd_def, vadd_eq_add, hvτ]
    funext w b
    simp [add_comm]
  · have hzL : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) ∈
        Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) :=
      hspan.ge (mem_rowLat.2 ⟨τ, hτ, rfl⟩)
    have hu := (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T).unique
      (y₁ := ⟨_, hzL⟩) (y₂ := 0) (by
        rw [Submodule.vadd_def, vadd_eq_add]
        convert hT' using 1
        funext w b
        simp [add_comm]) (by simpa using hT)
    have h0 : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) = 0 :=
      congrArg Subtype.val hu
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    funext b
    have := congrFun (congrFun h0 w) b
    simpa using this

end GlobalTheory.RowDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLatticeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  first
  | exact GlobalTheory.RowDomain.rowDomain E hE k Λ₀ Λ' h₀ h'
  | exact GlobalTheory.RowDomain.rowDomain E hE k Λ₀ Λ' h₀.toIsLattice h'.toIsLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeCovolumeInverseIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeCovolumeInverseIdeal
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm Module
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CovIdeal

open GlobalTheory.LatFacts

variable (E : Type) [Field E] [NumberField E]

def lat (I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 1 → E) :=
  (I : Submodule (𝓞 E) E).comap (LinearMap.proj 0)

theorem mem_lat (I : FractionalIdeal (𝓞 E)⁰ E) (y : Fin 1 → E) : y ∈ lat E I ↔ y 0 ∈ I := by
  simp [lat]

theorem lat_eq_map (I : FractionalIdeal (𝓞 E)⁰ E) :
    lat E I = (I : Submodule (𝓞 E) E).map (LinearMap.single (𝓞 E) (fun _ : Fin 1 => E) 0) := by
  ext y
  rw [mem_lat, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨y 0, h, ?_⟩
    funext a
    fin_cases a
    simp
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem isLattice_lat (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) : Submodule.IsLattice E (lat E I) := by
  apply Submodule.IsLattice.of_fg
  rw [lat_eq_map]
  exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _

theorem latAt_lat [_root_.NumberField.IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    latAt E 1 (lat E I.1) (oneInf E 1) = Submodule.span ℤ (Set.range
      ((Pi.basis fun _ : Fin 1 => mixedEmbedding.fractionalIdealLatticeBasis E I).map (mix E 1))) := by
  set B := mixedEmbedding.fractionalIdealLatticeBasis E I

  let φ : mixedEmbedding.mixedSpace E →ₗ[ℤ] VecInf E 1 :=
    ((mix E 1).toLinearMap.toAddMonoidHom.comp
      (AddMonoidHom.single (fun _ : Fin 1 => mixedEmbedding.mixedSpace E) 0)).toIntLinearMap
  have hφ : ∀ z, φ z = mix E 1 (Pi.single 0 z) := fun _ => rfl

  have key : ∀ (y : Fin 1 → E) (w : InfinitePlace E),
      (Matrix.of (oneInf E 1 w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = φ (mixedEmbedding E (y 0)) w := by
    intro y w
    rw [of_oneInf, inv_one, one_mulVec, hφ]
    funext a
    fin_cases a
    simp [mix_apply]
  have hrange : Set.range ((Pi.basis fun _ : Fin 1 => B).map (mix E 1)) = φ '' Set.range B := by
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, rfl⟩
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      exact ⟨B k, ⟨k, rfl⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨⟨0, k⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩

  have hspan : Submodule.span ℤ (mixedEmbedding E '' (I.1 : Set E)) = Submodule.span ℤ (Set.range B) := by
    conv_rhs => rw [← Submodule.span_eq (Submodule.span ℤ (Set.range B))]
    congr 1
    ext x
    rw [SetLike.mem_coe, mixedEmbedding.mem_span_fractionalIdealLatticeBasis]
  unfold latAt
  rw [hrange, Submodule.span_image, ← hspan, ← Submodule.span_image, ← Set.image_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y 0, (mem_lat E _ y).1 hy, funext fun w => (key y w).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨fun _ => t, (mem_lat E _ _).2 ht, funext fun w => key _ w⟩

theorem covAt_lat [_root_.NumberField.IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    covAt E 1 (latAt E 1 (lat E I.1) (oneInf E 1)) =
      (FractionalIdeal.absNorm I.1 : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E := by

  have hO := volume_fd_intB E 1
  rw [mul_one, intB, volume_fd_map, pow_one, measureReal_def] at hO

  rw [latAt_lat, covAt_span, volume_fd_map, pow_one, measureReal_def,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hO]

theorem covolume_inv_ideal : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ Λ₀ : Submodule (𝓞 E) (Fin 1 → E), (∀ y, y ∈ Λ₀ ↔ ∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Submodule.IsLattice E Λ₀ ∧ covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) := by
  intro E _ _ hE 𝔞 h𝔞
  have hne : (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ (inv_ne_zero hne)
  refine ⟨lat E J.1, fun y => ?_, isLattice_lat E J.1 (inv_ne_zero hne), ?_⟩
  · rw [mem_lat]
    change y 0 ∈ (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔ _
    rw [FractionalIdeal.mem_inv_iff hne]
    constructor
    · intro h t ht
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
        (h (t : E) (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
      exact ⟨r, by rw [hr, mul_comm]⟩
    · intro h x hx
      obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      obtain ⟨r, hr⟩ := h t ht
      exact (FractionalIdeal.mem_one_iff _).2 ⟨r, by rw [hr, mul_comm]⟩
  · have := hE
    rw [covAt_lat E J]
    change (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : ℝ) * _ = _
    rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    ring

end GlobalTheory.CovIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeCovolumeInverseIdealStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_covolume_inverse_ideal : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ Λ₀ : Submodule (𝓞 E) (Fin 1 → E), (∀ y, y ∈ Λ₀ ↔ ∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Submodule.IsLattice E Λ₀ ∧ covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) := by
  first | exact @GlobalTheory.CovIdeal.covolume_inv_ideal | exact GlobalTheory.CovIdeal.covolume_inv_ideal | (intros; apply GlobalTheory.CovIdeal.covolume_inv_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAdd
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LowDim

variable {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ}

theorem block_eq_zero (hB : Biorth r m U (fun b => (U b)ᴴ)) {s : ℕ} (hs : m ≤ s) : U s = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  calc U s = (∑ b ∈ range m, U b * (U b)ᴴ) * U s := by rw [h3, Matrix.one_mul]
    _ = 0 := by
      rw [Matrix.sum_mul]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' : b ≠ s := by have := Finset.mem_range.1 hb; omega
      rw [Matrix.mul_assoc, h2 b s hb', Matrix.mul_zero]

theorem mem_lowers_iff_blocks (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  rw [mem_lowers]
  constructor
  · intro h s t hst
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have hy : U t *ᵥ Pi.single j 1 ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hy) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW]
    intro s hs
    have e : (U s)ᴴ *ᵥ Y *ᵥ y = ((U s)ᴴ * Y * ∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by
      rw [h3, Matrix.mul_one, Matrix.mulVec_mulVec]
    rw [e, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    by_cases hst : t ≤ s + c
    · rw [h s t hst, Matrix.zero_mulVec]
    · rw [(hW _ _).1 hy t (by omega), Matrix.mulVec_zero]

noncomputable def layer (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (c : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) ℂ where
  toFun Y b := (U b)ᴴ * Y * U (b + c + 1)
  map_add' Y Z := by
    funext b
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a Y := by
    funext b
    simp

end GlobalTheory.RadCov.LowDim

namespace GlobalTheory.RadCov


open LowDim in
theorem finrank_lowers_eq_succ_add (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) :
    Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) +
      ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  have hle : lowers W (c + 1) ≤ lowers W c := by
    intro Y hY
    rw [mem_lowers_iff_blocks hB hW] at hY ⊢
    exact fun s t hst => hY s t (by omega)
  let φ := (layer m U c).domRestrict (lowers W c)
  have hker : LinearMap.ker φ = (lowers W (c + 1)).comap (lowers W c).subtype := by
    ext ⟨Y, hY⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_lowers_iff_blocks hB hW]
    rw [mem_lowers_iff_blocks hB hW] at hY
    constructor
    · intro h s t hst
      by_cases h' : t ≤ s + c
      · exact hY s t h'
      · obtain rfl : t = s + c + 1 := by omega
        by_cases hs : s < m
        · exact congrFun h ⟨s, hs⟩
        · rw [block_eq_zero hB (not_lt.1 hs)]
          simp
    · intro h
      funext b
      exact h b (b + c + 1) le_rfl
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro Z
    obtain ⟨h1, h2, -⟩ := id hB
    have key : ∀ s t, (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U t
        = ∑ b : Fin m, ((U s)ᴴ * U b) * Z b * ((U (b + c + 1))ᴴ * U t) := by
      intro s t
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp only [Matrix.mul_assoc]
    refine ⟨⟨∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ, ?_⟩, ?_⟩
    · rw [mem_lowers_iff_blocks hB hW]
      intro s t hst
      rw [key]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : s = b
      · rw [h2 (b + c + 1) t (by omega), Matrix.mul_zero]
      · rw [h2 s b hb, Matrix.zero_mul, Matrix.zero_mul]
    · funext s
      change (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U (s + c + 1) = Z s
      rw [key, Finset.sum_eq_single s]
      · rw [h1, h1, Matrix.one_mul, Matrix.mul_one]
      · intro b _ hb
        rw [h2 s b (fun h => hb (Fin.ext h.symm)), Matrix.zero_mul, Matrix.zero_mul]
      · simp
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    Module.finrank_pi_fintype] at h
  rw [← h, add_comm, ← Fin.sum_univ_eq_sum_range (fun b => r b * r (b + c + 1)) m]
  simp [Module.finrank_matrix]

end GlobalTheory.RadCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAddStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_matricesLoweringFiltrationBy_eq_succ_add : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → ∀ c, Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) + ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadCov.finrank_lowers_eq_succ_add | exact GlobalTheory.RadCov.finrank_lowers_eq_succ_add | (intros; apply GlobalTheory.RadCov.finrank_lowers_eq_succ_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalars
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.CovScal

theorem abs_det_mul_covolume_eq_nat_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (A B : Submodule ℤ E) [DiscreteTopology A] [IsZLattice ℝ A]
    [DiscreteTopology B] [IsZLattice ℝ B] (T : E →ₗ[ℝ] E) (hT : ∀ y ∈ A, T y ∈ B) :
    ∃ n : ℕ, |LinearMap.det T| * ZLattice.covolume A μ = n * ZLattice.covolume B μ := by
  classical

  let bA := Module.Free.chooseBasis ℤ A
  let bB := Module.Free.chooseBasis ℤ B
  let b₀ := bA.ofZLatticeBasis ℝ A
  let e := (bB.ofZLatticeBasis ℝ B).indexEquiv b₀
  let bB' := bB.reindex e
  let c := bB'.ofZLatticeBasis ℝ B
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ A) (Module.Free.ChooseBasisIndex ℤ A) ℤ :=
    fun i j => bB'.repr ⟨T (bA j), hT _ (bA j).2⟩ i
  have hb₀ : ((↑) : A → E) ∘ bA = b₀ := funext fun i => (bA.ofZLatticeBasis_apply ℝ A i).symm
  have hc : ((↑) : B → E) ∘ bB' = c := funext fun i => (bB'.ofZLatticeBasis_apply ℝ B i).symm

  have hM : c.toMatrix (T ∘ b₀) = M.map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.map_apply, Function.comp_apply,
      show b₀ j = ((bA j : A) : E) from bA.ofZLatticeBasis_apply ℝ A j]
    exact bB'.ofZLatticeBasis_repr_apply ℝ B ⟨T (bA j), hT _ (bA j).2⟩ i
  have hdet : LinearMap.det T = b₀.det c * (M.det : ℝ) := by
    have h1 : b₀.det (T ∘ b₀) = LinearMap.det T := by
      rw [b₀.det_comp T b₀, b₀.det_self, mul_one]
    rw [← h1, b₀.det_apply, ← b₀.toMatrix_mul_toMatrix c (T ∘ b₀), Matrix.det_mul,
      ← b₀.det_apply, hM, Int.cast_det]
  have hcA := ZLattice.covolume_eq_det_mul_measureReal A μ bA b₀
  have hcB := ZLattice.covolume_eq_det_mul_measureReal B μ bB' b₀
  rw [hb₀, b₀.det_self, abs_one, one_mul] at hcA
  rw [hc] at hcB
  refine ⟨M.det.natAbs, ?_⟩
  rw [hcA, hcB, hdet, Nat.cast_natAbs, Int.cast_abs, abs_mul]
  ring

noncomputable def blockScal {ι : Type} (κ : Type) (d : ι → ℝ) : (ι → κ → ℝ) →ₗ[ℝ] (ι → κ → ℝ) :=
  LinearMap.pi fun v => (d v • (LinearMap.id : (κ → ℝ) →ₗ[ℝ] (κ → ℝ))).comp (LinearMap.proj v)

theorem blockScal_apply {ι κ : Type} (d : ι → ℝ) (y : ι → κ → ℝ) :
    blockScal κ d y = fun v i => d v * y v i := by
  funext v i
  simp [blockScal]

theorem det_blockScal {ι κ : Type} [Fintype ι] [Fintype κ] (d : ι → ℝ) :
    LinearMap.det (blockScal κ d) = ∏ v, d v ^ Fintype.card κ := by
  unfold blockScal
  rw [LinearMap.det_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]

theorem eq_one_of_forall_prime {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ p : ℕ, p.Prime → ∃ a b : ℕ, ¬ p ∣ a * b ∧ ρ ^ 2 * b = a) : ρ = 1 := by
  obtain ⟨a₀, b₀, h2, hab₀⟩ := h 2 Nat.prime_two
  have ha₀ : a₀ ≠ 0 := by rintro rfl; simp at h2
  have hb₀ : b₀ ≠ 0 := by rintro rfl; simp at h2

  have key : a₀ = b₀ := by
    refine Nat.eq_of_factorization_eq ha₀ hb₀ fun p => ?_
    by_cases hp : p.Prime
    · obtain ⟨a, b, hp', hab⟩ := h p hp
      have ha : a ≠ 0 := by rintro rfl; simp at hp'
      have hb : b ≠ 0 := by rintro rfl; simp at hp'
      have hcast : ((a₀ * b : ℕ) : ℝ) = ((a * b₀ : ℕ) : ℝ) := by
        push_cast
        rw [← hab₀, ← hab]
        ring
      have hnat : a₀ * b = a * b₀ := by exact_mod_cast hcast
      have hpa : a.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_left hd b)
      have hpb : b.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd => hp' (dvd_mul_of_dvd_right hd a)
      have hf := congrArg (fun n => n.factorization p) hnat
      simp only [Nat.factorization_mul ha₀ hb, Nat.factorization_mul ha hb₀, Finsupp.add_apply,
        hpa, hpb] at hf
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [key] at hab₀
  have hb₀' : (b₀ : ℝ) ≠ 0 := by exact_mod_cast hb₀
  have hsq : ρ ^ 2 = 1 := mul_right_cancel₀ hb₀' (by rw [hab₀, one_mul])
  have hfac : (ρ - 1) * (ρ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h' | h' <;> linarith

theorem covolume_eq_of_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  intro ι κ _ _ A B _ _ _ _ h
  have hA : 0 < ZLattice.covolume A volume := ZLattice.covolume_pos A volume
  have hB : 0 < ZLattice.covolume B volume := ZLattice.covolume_pos B volume
  set cA := ZLattice.covolume A volume
  set cB := ZLattice.covolume B volume
  suffices key : cA / cB = 1 from (div_eq_one_iff_eq hB.ne').mp key
  refine eq_one_of_forall_prime (div_pos hA hB) fun p hp => ?_
  obtain ⟨d, N, hpN, hN, hAB, hBA⟩ := h p hp
  have hT : ∀ y ∈ A, blockScal κ d y ∈ B := fun y hy => by rw [blockScal_apply]; exact hAB y hy
  have hT' : ∀ y ∈ B, blockScal κ d y ∈ A := fun y hy => by rw [blockScal_apply]; exact hBA y hy
  obtain ⟨n, hn⟩ := abs_det_mul_covolume_eq_nat_mul volume A B (blockScal κ d) hT
  obtain ⟨m, hm⟩ := abs_det_mul_covolume_eq_nat_mul volume B A (blockScal κ d) hT'
  set D := |LinearMap.det (blockScal κ d)|

  have hD2 : D ^ 2 = (N : ℝ) ^ Fintype.card κ := by
    rw [sq_abs, det_blockScal, ← hN, Finset.prod_pow, Finset.prod_pow]
    ring
  have hnm : ((n * m : ℕ) : ℝ) = ((N ^ Fintype.card κ : ℕ) : ℝ) := by
    push_cast
    have h0 : ((n : ℝ) * m - D ^ 2) * (cA * cB) = 0 := by
      linear_combination (-(D * cB)) * hn - (n * cB) * hm
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rw [← hD2]; linarith
    · exact absurd h0 (mul_pos hA hB).ne'
  have hnat : n * m = N ^ Fintype.card κ := by exact_mod_cast hnm
  refine ⟨n, m, ?_, ?_⟩
  · rw [hnat]
    exact fun hd => hpN (hp.dvd_of_dvd_pow hd)
  · rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hB.ne')]
    linear_combination (-cA) * hm + cB * hn

end GlobalTheory.CovScal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalarsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  first | exact @GlobalTheory.CovScal.covolume_eq_of_scalars | exact GlobalTheory.CovScal.covolume_eq_of_scalars | (intros; apply GlobalTheory.CovScal.covolume_eq_of_scalars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagPieceHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagPieceHeights
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private theorem hform_eq_dotProduct_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (s y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J s y = star s ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem pieceHt_dualFlag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), IsDualFlag I.J F (2 * a + 1) → F (2 * a + 1) = lamX I (1, xf) → (∀ i : Fin (a + 1), F i = S i) → (∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ∧ pieceHt (frm I (1, xf)) F i = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) ∧ pieceHt (frm I (1, xf)) F (2 * a - i) = (Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i))⁻¹) ∧ pieceHt (frm I (1, xf)) F a = 1 ∧ ∀ b, 2 * a + 1 ≤ b → pieceHt (frm I (1, xf)) F b = 1 := by
  intro I xf a j hj S hS F hF hFm hFS
  have hmaj := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  haveI : IsTotallyComplex I.E := hmaj.1
  have hf : Formalism.HN.nPl I.E = I.f := hmaj.2.1
  have hX : ∀ w, IsUnit (frm I (1, xf) w).det := fun w => GlobalTheory.Count.FrameMajorant.frm_unit I (1, xf) w
  have hΛfg : (lamX I (1, xf)).FG := (GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.1
  have hmain := GlobalTheory.Count.PerpStep.main I (1, xf)
  have hht1 : Formalism.HN.ht (bas I) (frm I (1, xf)) (lamX I (1, xf)) = 1 := hmain.1
  have hperp := hmain.2.2.2
  have hfg : ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian _ hΛfg
    have h1 : (N.comap (lamX I (1, xf)).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (lamX I (1, xf)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2

  have hrat : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      Formalism.HN.ht (bas I) (frm I (1, xf)) N / Formalism.HN.ht (bas I) (frm I (1, xf)) T =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX N (hfg N hN),
      GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX T (hfg T (hT.1.trans hN)),
      GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT, ← Real.exp_sub]
    congr 1
    ring
  have hqpos : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      0 < Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT]
    exact Real.exp_pos _

  have hdual : ∀ b, b ≤ 2 * a + 1 → perpIn I (1, xf) (F b) = F (2 * a + 1 - b) := by
    intro b hb
    ext y
    rw [GlobalTheory.Count.PerpStep.perpIn_eq, GlobalTheory.Count.PerpStep.mem_perp, hF.2.2.2 b hb y, hFm]
    refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
    rw [hform_eq_dotProduct_mulVec]

  have hsatS : ∀ i : Fin (a + 1),
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (S i) := by
    intro i
    have h := GlobalTheory.Count.PerpStep.sat_inf (bas I) (frm I (1, xf)) hX (lamX I (1, xf)) hΛfg
      (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    convert h using 1
    ext y
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact hS.2.2.2.1 i y
  have hsatF : ∀ b, b ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (F b) := by
    intro b hb
    by_cases hba : b ≤ a
    · have e : F b = S ⟨b, by omega⟩ := hFS ⟨b, by omega⟩
      rw [e]
      exact hsatS _
    · have e : F (2 * a + 1 - b) = S ⟨2 * a + 1 - b, by omega⟩ := hFS ⟨2 * a + 1 - b, by omega⟩
      have h := (hperp (F (2 * a + 1 - b)) (F (2 * a + 1 - b)) (by rw [e]; exact hsatS _)
        (by rw [e]; exact hsatS _) le_rfl).1
      rwa [hdual _ (by omega), show 2 * a + 1 - (2 * a + 1 - b) = b by omega] at h
  have hpiece : ∀ b, b + 1 ≤ 2 * a + 1 →
      pieceHt (frm I (1, xf)) F b = Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (b + 1)) (F b) := by
    intro b hb
    unfold pieceHt
    exact hrat _ _ (hsatF _ hb).1
      (GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
        (hF.1 (Nat.le_succ b)) (hsatF _ hb).1)
  have hsat' : ∀ b, b + 1 ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (F (b + 1)) (F b) := fun b hb =>
    GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
      (hF.1 (Nat.le_succ b)) (hsatF _ hb).1
  refine ⟨fun i => ?_, ?_, fun b hb => ?_⟩
  · have hi := i.isLt
    have hFi : F i = S i.castSucc := by simpa using hFS i.castSucc
    have hFi1 : F (i + 1) = S i.succ := by simpa using hFS i.succ
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' i (by omega))
    rw [hFi1, hFi] at hq
    have hrk : ((Formalism.HN.rkK (S i.succ) : ℝ) - Formalism.HN.rkK (S i.castSucc)) = j i := by
      rw [hS.2.2.1 i]
      push_cast
      ring
    have hjpos : (0 : ℝ) < j i := by exact_mod_cast hj i
    have hfpos : (0 : ℝ) < I.f := by
      rw [← hf]
      exact_mod_cast Fintype.card_pos
    have hsz : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^
          ((1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ))) := by
      unfold Formalism.HN.sizeQ
      rw [hrk, hf]
    have hpow : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hsz, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      have hc : (1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ)) * ((2 * I.f * j i : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [hc, Real.rpow_one]
    have hpi : pieceHt (frm I (1, xf)) F i =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hpiece i (by omega), hFi1, hFi]
    refine ⟨by rw [hsz]; exact Real.rpow_pos_of_pos hq _, by rw [hpi, hpow], ?_⟩
    rw [hpow, hpiece (2 * a - i) (by omega)]
    have hPi := hdual i (by omega)
    have hPi1 := hdual (i + 1) (by omega)
    rw [show 2 * a + 1 - i = 2 * a - i + 1 by omega] at hPi
    rw [show 2 * a + 1 - (i + 1) = 2 * a - i by omega] at hPi1
    have h := (hperp (F i) (F (i + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPi, hPi1, hFi1, hFi] at h
    exact h
  · have hPa := hdual a (by omega)
    have hPa1 := hdual (a + 1) (by omega)
    rw [show 2 * a + 1 - a = a + 1 by omega] at hPa
    rw [show 2 * a + 1 - (a + 1) = a by omega] at hPa1
    have h := (hperp (F a) (F (a + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPa, hPa1] at h
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' a (by omega))
    rw [hpiece a (by omega)]
    set q := Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (a + 1)) (F a) with hqdef
    have hmul : q * q = 1 := by
      calc q * q = q⁻¹ * q := by rw [← h]
        _ = 1 := inv_mul_cancel₀ hq.ne'
    nlinarith
  · unfold pieceHt
    rw [hF.2.2.1 (b + 1) (by omega), hF.2.2.1 b hb, hFm, hht1]
    norm_num

end GlobalTheory.RadCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagPieceHeightsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualHermitianFlag_piece_heights : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), IsDualFlag I.J F (2 * a + 1) → F (2 * a + 1) = lamX I (1, xf) → (∀ i : Fin (a + 1), F i = S i) → (∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ∧ pieceHt (frm I (1, xf)) F i = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) ∧ pieceHt (frm I (1, xf)) F (2 * a - i) = (Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i))⁻¹) ∧ pieceHt (frm I (1, xf)) F a = 1 ∧ ∀ b, 2 * a + 1 ≤ b → pieceHt (frm I (1, xf)) F b = 1 := by
  first | exact @GlobalTheory.RadCov.pieceHt_dualFlag | exact GlobalTheory.RadCov.pieceHt_dualFlag | (intros; apply GlobalTheory.RadCov.pieceHt_dualFlag <;> assumption)
end
end

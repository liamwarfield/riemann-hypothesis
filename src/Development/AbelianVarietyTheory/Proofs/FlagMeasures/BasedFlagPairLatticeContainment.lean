module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrbitLatticesInfFrameSpanEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionLatticeInfOrthEqOrthPart
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionLatticeInfOrthEqOrthPart
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.OrthLoc

variable {D : D7}

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x y z : Vp D p) :
    LocFacts₂ Z.M p (x + y) z = LocFacts₂ Z.M p x z + LocFacts₂ Z.M p y z := by
  simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x z : Vp D p) :
    LocFacts₂ Z.M p (c • x) z = c * LocFacts₂ Z.M p x z := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def orthP (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule (D.s.atP p).Ep (Vp D p) where
  carrier := {v | ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0}
  zero_mem' := by intro u _; simp [LocFacts₂]
  add_mem' := by intro a b ha hb u hu; rw [localForm_add_left, ha u hu, hb u hu, add_zero]
  smul_mem' := by intro c a ha u hu; rw [localForm_smul_left, ha u hu, mul_zero]

theorem span_orth_le (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ≤ orthP Z p U := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩ u hu
  have ha' : (VS D).hT u a = 0 := by
    have ha2 : a ∈ orth (VS D) U := ha
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at ha2
    exact ha2 u hu
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, ha']

theorem mem_localLattice_inf_orthogonal : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V),
    (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) →
    (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) →
      (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) →
    ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ →
      (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  intro D Z U hdec huniq Λ hΛ p t ht horth
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) U) hΛ.fg
  have hmem : t ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) : Set (Vp D p)) := by
    rw [hsat]
    refine ⟨ht, ?_⟩
    have htop : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) = ⊤ := by
      apply top_unique
      rw [← span_baseChange_eq_top p]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
      rw [map_add]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
    have ht' : t ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) := htop ▸ Submodule.mem_top
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 ht'
    have hβ0 : β = 0 := by
      apply huniq p β hβ
      have e : β = t - α := by rw [← hαβ]; abel
      have hto : t ∈ orthP Z p U := horth
      have h2 := (orthP Z p U).sub_mem hto (span_orth_le Z p U hα)
      rw [← e] at h2
      exact h2
    rw [← hαβ, hβ0, add_zero]
    exact hα
  exact hmem

end GlobalTheory.Unfold.OrthLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionLatticeInfOrthEqOrthPartStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_lattice_inf_orth_eq_orth_part : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V), (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) → (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ → (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  first | exact @GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal | exact GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal | (intros; apply GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatSmulMemOfMemSpan
open NumberField

namespace GlobalTheory.NatSmulMemOfSpan

theorem exists_nat_mul_eq_coe {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (m : K) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y.natAbs : K) * c) := by
    have hc : (y.natAbs : K) = ((y.natAbs : ℤ) : K) := (Int.cast_natCast _).symm
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · rw [hc, ← h]; exact hint
    · have h2 : ((y.natAbs : ℤ) : K) = -(y : K) := by
        have : (y.natAbs : ℤ) = -y := by omega
        rw [this, Int.cast_neg]
      rw [hc, h2, neg_mul]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, ⟨_, hint'⟩, rfl⟩

theorem exists_nat_smul_mem_of_mem_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span K (Λ : Set V)) : ∃ n : ℕ, 0 < n ∧ (n : K) • v ∈ Λ := by
  have key : ∀ (a : 𝓞 K) (w : V), w ∈ Λ → algebraMap (𝓞 K) K a • w ∈ Λ := fun a w hw => by
    rw [algebraMap_smul]; exact Λ.smul_mem a hw
  have keyN : ∀ (m : ℕ) (w : V), w ∈ Λ → (m : K) • w ∈ Λ := fun m w hw => by
    simpa using key (m : 𝓞 K) w hw
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (x + y) = (n : K) • ((m : K) • x) + (m : K) • ((n : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (n : K)]
    rw [this]
    exact Λ.add_mem (keyN n _ hx) (keyN m _ hy)
  | smul c x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_coe c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (c • x) = algebraMap (𝓞 K) K a • ((n : K) • x) := by
      rw [ha, smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact key a _ hx

theorem exists_nat_smul_mem {D : Formalism.BasicNotions.D7} (Λ : GlobalTheory.Unfold.LV D)
    (hΛ : Submodule.IsFullLattice ((Formalism.BasicNotions.D7.host D).E) Λ)
    (v : Formalism.BasicNotions.HSpace.V (Formalism.MainNotions.S.VS D)) :
    ∃ n : ℕ, 0 < n ∧ (n : (Formalism.BasicNotions.D7.host D).E) • v ∈ Λ :=
  exists_nat_smul_mem_of_mem_span Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end GlobalTheory.NatSmulMemOfSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalDecompositionLocalNondegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalDecompositionLocalNondegenerate
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecompOrth

variable {D : D7}

theorem mem_orth_of_basis {n : ℕ} (U : Submodule D.host.E (VS D).V)
    (b : Module.Basis (Fin n) D.host.E U) (y : (VS D).V)
    (hy : ∀ i, (VS D).hT (b i : (VS D).V) y = 0) : y ∈ orth (VS D) U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
    have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu', map_sum]
  simp [hy]

theorem exists_decomp (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (x : (VS D).V) : ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b := by
  let b := Module.finBasis D.host.E U
  let L : U →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
    LinearMap.pi (fun i => ((VS D).hT (b i : (VS D).V)).comp U.subtype)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0 := fun i => congrFun hy i
    have hmem : (y : (VS D).V) ∈ U ⊓ orth (VS D) U := ⟨y.2, mem_orth_of_basis U b y hy'⟩
    rw [hU] at hmem
    exact Subtype.ext ((Submodule.mem_bot _).1 hmem)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨y, hy⟩ := hsurj (fun i => (VS D).hT (b i : (VS D).V) x)
  refine ⟨x - y, mem_orth_of_basis U b _ (fun i => ?_), y, y.2, by abel⟩
  have := congrFun hy i
  simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [map_sub, this, sub_self]

theorem gram_det_ne_zero {n : ℕ} (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (b : Module.Basis (Fin n) D.host.E U) :
    (Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V)).det ≠ 0 := by
  intro h
  obtain ⟨α, hα0, hα⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hα0
  have hy : ∀ i, (VS D).hT (b i : (VS D).V) (((∑ j, α j • b j : U)) : (VS D).V) = 0 := by
    intro i
    have := congrFun hα i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, map_sum]
    simpa [mul_comm] using this
  have hmem : ((∑ j, α j • b j : U) : (VS D).V) ∈ U ⊓ orth (VS D) U :=
    ⟨Subtype.prop _, mem_orth_of_basis U b _ hy⟩
  rw [hU, Submodule.mem_bot] at hmem
  have h0 : ∑ j, α j • b j = 0 := Subtype.ext hmem
  funext j
  exact Fintype.linearIndependent_iff.1 b.linearIndependent α h0 j

end GlobalTheory.DecompOrth

namespace GlobalTheory.DecompOrth

variable {D : D7}

noncomputable def formLeft (Z : LocDat D) (p : PlF D) (w : Vp D p) : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep where
  toFun v := LocFacts₂ Z.M p v w
  map_add' x y := (locH Z p).h_add_left x y w
  map_smul' a x := (locH Z p).h_smul_left a x w

theorem formLeft_apply (Z : LocDat D) (p : PlF D) (w v : Vp D p) :
    formLeft Z p w v = LocFacts₂ Z.M p v w := rfl

theorem eq_zero_of_local_orth (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (Z : LocDat D) (p : PlF D) (v : Vp D p)
    (hv : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)))
    (horth : ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) : v = 0 := by
  let b := Module.finBasis D.host.E U
  have hspan : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) ≤
      Submodule.span (D.s.atP p).Ep (Set.range fun j => baseChange₂ D p (b j : (VS D).V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hu', map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [baseChange_smul₂]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan hv)
  set G := Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V) with hGdef
  set A := G.map (D.s.atP p).ιE with hA
  have hAβ : Matrix.mulVec A β = 0 := by
    funext i
    have h1 := horth (b i) (b i).2
    have h2 : LocFacts₂ Z.M p (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) (baseChange₂ D p (b i : (VS D).V)) =
        formLeft Z p (baseChange₂ D p (b i : (VS D).V)) (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [formLeft_apply, baseChangeAt_form Z.M p (Z.hcj p), brS] at h1
    simp only [Matrix.mulVec, dotProduct, hA, hGdef, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
    simpa [mul_comm] using h1
  have hdet : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne_zero U hU b)).map _
  have hβ : β = 0 := by
    have := congrArg (fun w => Matrix.mulVec A⁻¹ w) hAβ
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  simp [hβ]

end GlobalTheory.DecompOrth

theorem GlobalTheory.decomp_orth_complement : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 :=
  fun _ U hU => ⟨GlobalTheory.DecompOrth.exists_decomp U hU,
    fun Z p v hv horth => GlobalTheory.DecompOrth.eq_zero_of_local_orth U hU Z p v hv horth⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalDecompositionLocalNondegenerateStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_decomposition_local_nondegenerate : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 := by
  first | exact @GlobalTheory.decomp_orth_complement | exact GlobalTheory.decomp_orth_complement | (intros; apply GlobalTheory.decomp_orth_complement <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasedFlagPairLatticeContainment
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompScale

variable {D : D7}

theorem mem_range_of_int {x : D.host.E} (h : IsIntegral ℤ x) : x ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
  ⟨⟨x, h⟩, rfl⟩

theorem exists_nat_mul (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ (n : D.host.E) * z ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, mem_range_of_int ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : D.host.E) * z = y • z := by
      rw [zsmul_eq_mul]; congr 1
      have e : ((y : ℤ) : D.host.E) = (((y.natAbs : ℕ) : ℤ) : D.host.E) := by rw [← h]
      rw [e, Int.cast_natCast]
    rw [this]; exact hy
  · have : ((y.natAbs : ℕ) : D.host.E) * z = -(y • z) := by
      rw [zsmul_eq_mul, ← neg_mul]; congr 1
      have e : ((y : ℤ) : D.host.E) = ((-((y.natAbs : ℕ) : ℤ) : ℤ) : D.host.E) := by rw [← h]
      rw [e, Int.cast_neg, Int.cast_natCast, neg_neg]
    rw [this]; exact hy.neg

theorem range_mul {a b : D.host.E} (ha : a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E))
    (hb : b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) : a * b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, map_mul _ _ _⟩

theorem natCast_mem (n : ℕ) : (n : D.host.E) ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := ⟨n, map_natCast _ _⟩

theorem exists_nat_mul_fin {ι : Type} [Fintype ι] (f : ι → D.host.E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, (n : D.host.E) * f i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  choose m hm0 hm using fun i => exists_nat_mul (D := D) (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i), Nat.cast_mul, mul_comm ((m i : ℕ) : D.host.E), mul_assoc]
  exact range_mul (natCast_mem _) (hm i)

theorem iota_mem_O (Z : LocDat D) (p : PlF D) (o : 𝓞 D.host.E) :
    (D.s.atP p).ιE (o : D.host.E) ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def]
  exact ((NumberField.RingOfIntegers.isIntegral_coe o).map ((D.s.atP p).ιE.toIntAlgHom)).tower_top

theorem iota_mem_O' (Z : LocDat D) (p : PlF D) {z : D.host.E}
    (h : z ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) : (D.s.atP p).ιE z ∈ (Z.M p).L.O := by
  obtain ⟨o, rfl⟩ := h; exact iota_mem_O Z p o

open ValuativeRel in
theorem cj_mem (Z : LocDat D) (p : PlF D) {x : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O) :
    (Z.M p).L.cj x ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def] at *
  exact hx.map (((Z.M p).L.cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars 𝒪[(D.s.atP p).Fp])

theorem complement_unitary_preserves_form {Z : LocDat D} {p : PlF D} (P : LocNG.FPair (locH Z p) D.R.rS)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ P.UW0) :
    ∀ x y, LocFacts₂ Z.M p (g x) (g y) = LocFacts₂ Z.M p x y := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => exact fun _ _ => rfl
  | mul x y _ _ hx hy =>
    intro a b
    change LocFacts₂ Z.M p (x (y a)) (x (y b)) = _
    rw [hx, hy]
  | inv x _ hx =>
    intro a b
    change LocFacts₂ Z.M p (x.symm a) (x.symm b) = _
    rw [← hx, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x x' y : Vp D p) :
    LocFacts₂ Z.M p (x + x') y = LocFacts₂ Z.M p x y + LocFacts₂ Z.M p x' y := (locH Z p).h_add_left x x' y

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (a : (D.s.atP p).Ep) (x y : Vp D p) :
    LocFacts₂ Z.M p (a • x) y = a * LocFacts₂ Z.M p x y := (locH Z p).h_smul_left a x y

theorem localForm_zero_left (Z : LocDat D) (p : PlF D) (y : Vp D p) : LocFacts₂ Z.M p 0 y = 0 := by
  simp [LocFacts₂]

theorem localForm_sub_left (Z : LocDat D) (p : PlF D) (x x' y : Vp D p) :
    LocFacts₂ Z.M p (x - x') y = LocFacts₂ Z.M p x y - LocFacts₂ Z.M p x' y := by
  have h := localForm_add_left Z p (x - x') x' y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem localForm_smul_right₂ (Z : LocDat D) (p : PlF D) (a : (D.s.atP p).Ep) (x y : Vp D p) :
    LocFacts₂ Z.M p x (a • y) = (Z.M p).L.cj a * LocFacts₂ Z.M p x y := by
  have h1 := (locH Z p).h_herm (a • y) x
  have h2 := (locH Z p).h_herm y x
  change LocFacts₂ Z.M p x (a • y) = (Z.M p).L.cj (LocFacts₂ Z.M p (a • y) x) at h1
  change LocFacts₂ Z.M p x y = (Z.M p).L.cj (LocFacts₂ Z.M p y x) at h2
  rw [h1, localForm_smul_left, map_mul, ← h2]

theorem localForm_add_right₂ (Z : LocDat D) (p : PlF D) (x y y' : Vp D p) :
    LocFacts₂ Z.M p x (y + y') = LocFacts₂ Z.M p x y + LocFacts₂ Z.M p x y' := by
  have h1 := (locH Z p).h_herm (y + y') x
  have h2 := (locH Z p).h_herm y x
  have h3 := (locH Z p).h_herm y' x
  change LocFacts₂ Z.M p x (y + y') = (Z.M p).L.cj (LocFacts₂ Z.M p (y + y') x) at h1
  change LocFacts₂ Z.M p x y = (Z.M p).L.cj (LocFacts₂ Z.M p y x) at h2
  change LocFacts₂ Z.M p x y' = (Z.M p).L.cj (LocFacts₂ Z.M p y' x) at h3
  rw [h1, localForm_add_left, map_add (f := _), ← h2, ← h3]

theorem localForm_zero_right₂ (Z : LocDat D) (p : PlF D) (x : Vp D p) : LocFacts₂ Z.M p x 0 = 0 := by
  simp [LocFacts₂]

theorem mem_of_loc (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V)
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ) : x ∈ Λ :=
  GlobalTheory.Unfold.LsubG.mem_of_local Z Λ hΛ x h

theorem exists_nat_smul_mem (Λ : LV D) (hΛ : Submodule.IsFullLattice D.host.E Λ) (v : (VS D).V) :
    ∃ n : ℕ, 0 < n ∧ (n : D.host.E) • v ∈ Λ :=
  _root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem Λ hΛ v

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

variable {D : D7}

theorem mem_int_of_loc (Z : LocDat D) (z : D.host.E) (hz : ∀ p, (D.s.atP p).ιE z ∈ (Z.M p).L.O) :
    z ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact ((GlobalTheory.HL.PlacesInt.integers_local (GlobalTheory.HL.placesOf Z)).1 z).1 hz

theorem range_add {a b : D.host.E} (ha : a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E))
    (hb : b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) : a + b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, map_add _ _ _⟩

theorem star_mem (o : 𝓞 D.host.E) : star (o : D.host.E) ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
  mem_range_of_int ((NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd D.host.E).toIntAlgHom)

theorem localForm_sum_left (Z : LocDat D) (p : PlF D) {ι : Type} (s : Finset ι) (f : ι → Vp D p) (z : Vp D p) :
    LocFacts₂ Z.M p (∑ j ∈ s, f j) z = ∑ j ∈ s, LocFacts₂ Z.M p (f j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, localForm_add_left, ih]

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

variable {D : D7}

theorem scale_part : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ d : ℕ, 0 < d ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  intro D X Y u u' F F' w _ _ Z FP _ _ Λ₀ h0
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.1 h0.fg
  haveI : Fintype S := hSfin.fintype
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_fin (D := D) (fun ij : S × S => (VS D).hT ij.1 ij.2)
  have hzero : (0 : D.host.E) ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := ⟨0, map_zero _⟩

  have hint1 : ∀ a ∈ S, ∀ b ∈ Λ₀, (d : D.host.E) * (VS D).hT a b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
    intro a ha b hb
    rw [← hSspan] at hb
    induction hb using Submodule.span_induction with
    | mem b hb => exact hd (⟨a, ha⟩, ⟨b, hb⟩)
    | zero => rw [map_zero, mul_zero]; exact hzero
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add]; exact range_add hx hy
    | smul o x _ hx =>
      rw [← algebraMap_smul D.host.E o x, map_smul, smul_eq_mul, mul_left_comm]
      exact range_mul ⟨o, rfl⟩ hx
  have hint0 : ∀ a ∈ Λ₀, ∀ b ∈ Λ₀, (d : D.host.E) * (VS D).hT a b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
    intro a ha b hb
    rw [← hSspan] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hint1 a ha b hb
    | zero => rw [map_zero, LinearMap.zero_apply, mul_zero]; exact hzero
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, mul_add]; exact range_add hx hy
    | smul o x _ hx =>
      rw [← algebraMap_smul D.host.E o x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mul_left_comm]
      exact range_mul (star_mem o) hx
  refine ⟨d, hd0, fun Λ _ hloc x hx y hy => mem_int_of_loc Z _ fun p => ?_⟩
  obtain ⟨h, hh, himg⟩ := hloc p
  have hun := complement_unitary_preserves_form (FP p) hh
  have hxp : baseChange₂ D p x ∈ LocNG.img h (lattice₂ D Z.M p Λ₀) := by rw [himg]; exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hyp : baseChange₂ D p y ∈ LocNG.img h (lattice₂ D Z.M p Λ₀) := by rw [himg]; exact Submodule.subset_span ⟨y, hy, rfl⟩
  obtain ⟨x₀, hx₀, hxe⟩ := Submodule.mem_map.1 hxp
  obtain ⟨y₀, hy₀, hye⟩ := Submodule.mem_map.1 hyp
  have hform : ∀ a b, LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p b) = (D.s.atP p).ιE ((VS D).hT b a) :=
    fun a b => baseChangeAt_form Z.M p (Z.hcj p) a b
  have e : (D.s.atP p).ιE ((d : D.host.E) * (VS D).hT x y) = (d : (D.s.atP p).Ep) * LocFacts₂ Z.M p y₀ x₀ := by
    rw [map_mul, map_natCast, ← hform, ← hye, ← hxe]
    exact congrArg _ (hun y₀ x₀)
  rw [e]

  have hloc0 : ∀ a ∈ lattice₂ D Z.M p Λ₀, ∀ b ∈ lattice₂ D Z.M p Λ₀, (d : (D.s.atP p).Ep) * LocFacts₂ Z.M p a b ∈ (Z.M p).L.O := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨b, hb, rfl⟩ := hb
        rw [hform, ← map_natCast (D.s.atP p).ιE, ← map_mul]
        exact iota_mem_O' Z p (hint0 b hb a ha)
      | zero => rw [localForm_zero_right₂, mul_zero]; exact (Z.M p).L.O.zero_mem
      | add x y _ _ hx hy => rw [localForm_add_right₂, mul_add]; exact (Z.M p).L.O.add_mem hx hy
      | smul o x _ hx =>
        rw [Subring.smul_def, localForm_smul_right₂, mul_left_comm]
        exact (Z.M p).L.O.mul_mem (cj_mem Z p o.2) hx
    | zero => rw [localForm_zero_left, mul_zero]; exact (Z.M p).L.O.zero_mem
    | add x y _ _ hx hy => rw [localForm_add_left, mul_add]; exact (Z.M p).L.O.add_mem hx hy
    | smul o x _ hx =>
      rw [Subring.smul_def, localForm_smul_left, mul_left_comm]
      exact (Z.M p).L.O.mul_mem o.2 hx
  exact hloc0 y₀ hy₀ x₀ hx₀

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

variable {D : D7}


set_option maxHeartbeats 2000000 in
theorem dual_part : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ c : ℕ, 0 < c ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  set U := Xplus F ⊔ Xplus F' with hU
  have memW : ∀ x, x ∈ orth (VS D) U ↔ ∀ v ∈ U, (VS D).hT v x = 0 := fun x => by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  have hdef : ∀ x ∈ orth (VS D) U, (VS D).hT x x = 0 → x = 0 := fun x hx h => by
    by_contra hne
    have := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hw hG x hx hne
    rw [h, map_zero] at this; exact lt_irrefl _ this
  have hUW : U ⊓ orth (VS D) U = ⊥ := by
    rw [eq_bot_iff]; rintro x ⟨hxU, hxW⟩
    exact (Submodule.mem_bot _).2 (hdef x hxW ((memW x).1 hxW x hxU))
  obtain ⟨hdec, hloc0⟩ := GlobalTheory.T.orthogonal_decomposition_local_nondegenerate D U hUW

  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent D.host.E
    ((Λ₀ ⊓ toO (VS D) (orth (VS D) U) : LV D) : Set (VS D).V)
  have hspanW : Submodule.span D.host.E b = orth (VS D) U := by
    rw [hbspan]; apply le_antisymm
    · rw [Submodule.span_le]; exact fun x hx => hx.2
    · intro x hx
      obtain ⟨n, hn, hnx⟩ := exists_nat_smul_mem Λ₀ h0 x
      have hmem : (n : D.host.E) • x ∈ Submodule.span D.host.E
          ((Λ₀ ⊓ toO (VS D) (orth (VS D) U) : LV D) : Set (VS D).V) :=
        Submodule.subset_span ⟨hnx, (orth (VS D) U).smul_mem _ hx⟩
      have hn' : (n : D.host.E) ≠ 0 := by exact_mod_cast hn.ne'
      have := Submodule.smul_mem _ ((n : D.host.E)⁻¹) hmem
      rwa [smul_smul, inv_mul_cancel₀ hn', one_smul] at this
  haveI : Finite b := hli.finite
  haveI : Fintype b := Fintype.ofFinite b
  have hvΛ : ∀ i : b, (i : (VS D).V) ∈ Λ₀ := fun i => (hbs i.2).1
  have hvW : ∀ i : b, (i : (VS D).V) ∈ orth (VS D) U := fun i => (hbs i.2).2
  let B : Matrix b b D.host.E := fun i j => (VS D).hT (j : (VS D).V) (i : (VS D).V)
  have hBdet : B.det ≠ 0 := by
    intro hd
    obtain ⟨α, hα0, hα⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hα0
    have hj : ∀ j : b, (VS D).hT (j : (VS D).V) (∑ i, α i • (i : (VS D).V)) = 0 := by
      intro j
      have := congrFun hα j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, B] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simpa [map_smul, smul_eq_mul, mul_comm] using this
    have hxW : (∑ i, α i • (i : (VS D).V)) ∈ orth (VS D) U :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvW i)
    have hxx : ∀ x', (∀ j : b, (VS D).hT (j : (VS D).V) x' = 0) →
        (VS D).hT (∑ i, α i • (i : (VS D).V)) x' = 0 := by
      intro x' hx'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx' i, smul_zero]
    have h0' := hdef _ hxW (hxx _ hj)
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h0' i
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hBdet
  obtain ⟨c, hc0, hc⟩ := exists_nat_mul_fin (D := D) (fun ij : b × b => B⁻¹ ij.1 ij.2)
  refine ⟨c, hc0, fun Λ hΛ hloc y hyW hy => mem_of_loc Z Λ hΛ _ fun p => ?_⟩
  obtain ⟨h, hh, himg⟩ := hloc p
  have hfix : ∀ x ∈ U, h (baseChange₂ D p x) = baseChange₂ D p x := fun x hx =>
    GlobalTheory.FrameSpanLat.fix_span F F' Z FP hB hR p hh hx
  have hun := complement_unitary_preserves_form (FP p) hh
  have hform : ∀ a b, LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p b) = (D.s.atP p).ιE ((VS D).hT b a) :=
    fun a b => baseChangeAt_form Z.M p (Z.hcj p) a b
  have horthW : ∀ a ∈ orth (VS D) U, ∀ x ∈ U, LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p x) = 0 := fun a ha x hx => by
    rw [hform, (memW a).1 ha x hx, map_zero]
  have hy'o : ∀ x ∈ U, LocFacts₂ Z.M p (h.symm (baseChange₂ D p y)) (baseChange₂ D p x) = 0 := fun x hx => by
    rw [← hun, LinearEquiv.apply_symm_apply, hfix x hx]; exact horthW y hyW x hx
  let Sb := Submodule.span (D.s.atP p).Ep (Set.range fun i : b => baseChange₂ D p (i : (VS D).V))
  let SU := Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V))
  have hSbo : ∀ s ∈ Sb, ∀ x ∈ U, LocFacts₂ Z.M p s (baseChange₂ D p x) = 0 := by
    intro s hs x hx
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨i, rfl⟩ := hs; exact horthW _ (hvW i) x hx
    | zero => exact localForm_zero_left Z p _
    | add a a' _ _ ha ha' => rw [localForm_add_left, ha, ha', add_zero]
    | smul e a _ ha => rw [localForm_smul_left, ha, mul_zero]
  have hbcW : ∀ a ∈ orth (VS D) U, baseChange₂ D p a ∈ Sb := by
    intro a ha
    rw [← hspanW] at ha
    have ha' : a ∈ Submodule.span D.host.E (Set.range (fun i : b => (i : (VS D).V))) := by
      rwa [Subtype.range_coe]
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 ha'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : ∀ z : Vp D p, z ∈ Sb ⊔ SU := by
    intro z
    have : z ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, ha, b', hb', rfl⟩ := hdec x
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hbcW a ha) (Submodule.subset_span ⟨b', hb', rfl⟩)
  have hy'Sb : h.symm (baseChange₂ D p y) ∈ Sb := by
    obtain ⟨s1, hs1, s2, hs2, hsum⟩ := Submodule.mem_sup.1 (htop (h.symm (baseChange₂ D p y)))
    have hs2o : ∀ x ∈ U, LocFacts₂ Z.M p s2 (baseChange₂ D p x) = 0 := fun x hx => by
      have e2 : s2 = h.symm (baseChange₂ D p y) - s1 := by rw [← hsum]; abel
      rw [e2, localForm_sub_left, hy'o x hx, hSbo s1 hs1 x hx, sub_zero]
    have := hloc0 Z p s2 hs2 hs2o
    rw [← hsum, this, add_zero]; exact hs1
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hy'Sb

  have hK : ∀ i : b, LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V))) ∈ (Z.M p).L.O := by
    intro i
    have ht : h (baseChange₂ D p (i : (VS D).V)) ∈ lattice₂ D Z.M p Λ := by
      rw [← himg]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, hvΛ i, rfl⟩)
    have hto : ∀ x ∈ U, LocFacts₂ Z.M p (h (baseChange₂ D p (i : (VS D).V))) (baseChange₂ D p x) = 0 := fun x hx => by
      rw [← hfix x hx, hun]; exact horthW _ (hvW i) x hx
    have htK := GlobalTheory.T.completion_lattice_inf_orth_eq_orth_part D Z U hdec (hloc0 Z) Λ hΛ p _ ht hto
    generalize h (baseChange₂ D p (i : (VS D).V)) = t at htK
    induction htK using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨k, hk, rfl⟩ := hs
      rw [hform]; exact iota_mem_O' Z p (hy k hk)
    | zero => rw [localForm_zero_right₂]; exact (Z.M p).L.O.zero_mem
    | add a a' _ _ ha ha' => rw [localForm_add_right₂]; exact (Z.M p).L.O.add_mem ha ha'
    | smul o a _ ha =>
      rw [Subring.smul_def, localForm_smul_right₂]
      exact (Z.M p).L.O.mul_mem (cj_mem Z p o.2) ha
  have hrel : (fun i : b => LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V)))) =
      Matrix.vecMul β (B.map (D.s.atP p).ιE) := by
    funext i
    have e1 : LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V))) =
        LocFacts₂ Z.M p (h.symm (baseChange₂ D p y)) (baseChange₂ D p (i : (VS D).V)) := by
      have := hun (h.symm (baseChange₂ D p y)) (baseChange₂ D p (i : (VS D).V))
      rwa [LinearEquiv.apply_symm_apply] at this
    rw [e1, ← hβ, localForm_sum_left]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [localForm_smul_left, hform]
  have hβeq : β = Matrix.vecMul (fun i : b => LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V))))
      (B⁻¹.map (D.s.atP p).ιE) := by
    rw [hrel, Matrix.vecMul_vecMul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hBu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
  have hmem : ∀ j : b, (c : (D.s.atP p).Ep) * β j ∈ (Z.M p).L.O := by
    intro j
    have e : (c : (D.s.atP p).Ep) * β j = ∑ k : b, LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (k : (VS D).V))) *
        (D.s.atP p).ιE ((c : D.host.E) * B⁻¹ k j) := by
      conv_lhs => rw [hβeq]
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_mul, map_natCast]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact Subring.sum_mem _ fun k _ => (Z.M p).L.O.mul_mem (hK k) (iota_mem_O' Z p (hc (k, j)))
  have hcy' : (c : (D.s.atP p).Ep) • h.symm (baseChange₂ D p y) ∈ lattice₂ D Z.M p Λ₀ := by
    rw [← hβ, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_smul]
    have e : ((c : (D.s.atP p).Ep) * β j) • baseChange₂ D p (j : (VS D).V) =
        (⟨_, hmem j⟩ : (Z.M p).L.O) • baseChange₂ D p (j : (VS D).V) := rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hvΛ j, rfl⟩)
  rw [baseChange_smul₂, map_natCast, ← himg, ← LinearEquiv.apply_symm_apply h (baseChange₂ D p y), ← h.map_smul]
  exact Submodule.mem_map_of_mem hcy'

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

theorem scale_dual : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ d c : ℕ, 0 < d ∧ 0 < c ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) ∧ ∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  obtain ⟨d, hd0, hd⟩ := scale_part D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0.toIsLattice
  obtain ⟨c, hc0, hc⟩ := dual_part D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  exact ⟨d, c, hd0, hc0, fun Λ hΛ hloc => ⟨hd Λ hΛ hloc, hc Λ hΛ hloc⟩⟩

end GlobalTheory.CompScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasedFlagPairLatticeContainmentStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.based_flag_pair_lattice_containment : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ d c : ℕ, 0 < d ∧ 0 < c ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) ∧ ∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ := by
  first | exact @GlobalTheory.CompScale.scale_dual | exact GlobalTheory.CompScale.scale_dual | (intros; apply GlobalTheory.CompScale.scale_dual <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end

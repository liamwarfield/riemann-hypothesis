module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GluedExists
public import Lemmata.MiscLemmasI.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowSurjective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HermFormShiftedVectorZero

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TraceOneUnramified
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trace_one_unramified : TraceOne := fun D =>
  Formalism.MainNotions.BridgeLemma.l_theta D.host.E D.sp.cm.cmUnram

section Dual

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem exists_dual0 : ∃ g0 : Fin D.R.rS → (VS D).V, IsDual0 F0 g0 := by
  let Φ : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) := LinearMap.pi (fun a => (VS D).hT (F0.e a))
  have hsurj : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set μ : Fin D.R.rS → D.host.E := fun a => f (fun j => if a = j then 1 else 0) with hμdef
    have hv : ∀ v, ∑ a, (VS D).hT (F0.e a) v * μ a = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hle (LinearMap.mem_range_self Φ v)
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      simpa [Φ, LinearMap.pi_apply, smul_eq_mul, μ] using h1
    have hx : ∑ a, star (μ a) • F0.e a = 0 := by
      apply (VS D).nondeg.1
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      rw [← hv v]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hμ : ∀ a, μ a = 0 := by
      intro a
      have := Fintype.linearIndependent_iff.1 F0.e_indep (fun a => star (μ a)) hx a
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro u
    rw [LinearMap.pi_apply_eq_sum_univ f u]
    simp only [LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    have : f (fun j => if a = j then 1 else 0) = 0 := hμ a
    rw [this, smul_zero]
  refine ⟨fun b => Classical.choose (LinearMap.range_eq_top.1 hsurj (Pi.single b 1)), ?_⟩
  intro a b
  have h := Classical.choose_spec (LinearMap.range_eq_top.1 hsurj (Pi.single b 1))
  have h2 := congrFun h a
  simp only [Φ, LinearMap.pi_apply] at h2
  rw [h2, Pi.single_apply]

end Dual

theorem row_dual_frame : RowDualFrame := by
  intro D u F0 Λ hΛ
  obtain ⟨g0, hg0⟩ := exists_dual0 F0
  have hlat : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hiso : ∀ x ∈ F0.X, ∀ y ∈ F0.X, (VS D).hT x y = 0 := fun x hx y hy => hX_X F0 hx hy
  obtain ⟨P, P', hadj, hid, hX, _, hint', _⟩ :=
    Formalism.MainNotions.BridgeLemma.l_iso Formalism.MainNotions.BridgeLemma.l_adj Formalism.MainNotions.BridgeLemma.l_retr Formalism.MainNotions.BridgeLemma.l_theta
      D.host.E (VS D) Λ F0.X D.sp.cm.cmUnram hlat hu hiso

  have hker : ∀ w ∈ perpS (VS D) F0.X, P' w = 0 := by
    intro w hw
    apply (VS D).nondeg.2
    intro x
    rw [← hadj x w]
    exact hw _ (hX x)
  refine ⟨fun b => P' (g0 b), ?_, ?_⟩
  · intro a b
    show (VS D).hT (F0.e a) (P' (g0 b)) = _
    rw [← hadj, hid _ (e_mem_X F0 a), hg0 a b]
  · intro v hv
    have hg0' : ∀ a b, (VS D).hT (F0.e a) (g0 b) = if a = b then 1 else 0 := hg0
    have hyc : ycL F0 (fun b => P' (g0 b)) v = P' (ycL F0 g0 v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ycL_apply, ycL_apply, map_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [map_smul])
    have hperp : v - ycL F0 g0 v ∈ perpS (VS D) F0.X := by
      apply mem_perp_of F0
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, ycL_apply, map_sum]
      simp [hg0']
    have h1 : P' (ycL F0 g0 v) = P' v := by
      have := hker _ hperp
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [hyc, h1]
    exact hint' v hv

theorem rowClass_of_zunit (h : RowZUnit) : RowClass :=
  rowClass_of_three row_dual_frame h trace_one_unramified

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowUnitCondition
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (o : 𝓞 K) :
    ∃ o' : 𝓞 K, (o' : K) = star (o : K) := by
  have h1 : IsIntegral ℤ (star (o : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (o : K), h1⟩, rfl⟩

theorem exists_one {K : Type} [Field K] [NumberField K] [StarRing K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h : W →ₗ⋆[K] W →ₗ[K] K) (M : Submodule (𝓞 K) W)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h M) {z : W} (hz : z ∈ M)
    (hprim : ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c) : ∃ m ∈ M, h m z = 1 := by
  classical

  have memM : ∀ x : W, x ∈ M ↔ ∀ m ∈ M, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = h m x := by
    intro x
    conv_lhs => rw [← hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]

  let I : Ideal (𝓞 K) :=
    { carrier := {o | ∃ m ∈ M, h m z = star (o : K)}
      add_mem' := by
        rintro a b ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
        refine ⟨m₁ + m₂, M.add_mem hm₁ hm₂, ?_⟩
        rw [map_add (f := _), LinearMap.add_apply, e₁, e₂]
        show star (algebraMap (𝓞 K) K a) + star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a + b))
        rw [map_add (f := _), star_add]
      zero_mem' := ⟨0, M.zero_mem, by
        rw [map_zero, LinearMap.zero_apply]
        show (0 : K) = star (algebraMap (𝓞 K) K 0)
        rw [map_zero, star_zero]⟩
      smul_mem' := by
        rintro a b ⟨m, hm, e⟩
        refine ⟨a • m, M.smul_mem a hm, ?_⟩
        have ha : (a • m : W) = (algebraMap (𝓞 K) K a) • m := (algebraMap_smul K a m).symm
        rw [ha, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e]
        simp only [smul_eq_mul, starRingEnd_apply]
        show star (algebraMap (𝓞 K) K a) * star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a * b))
        rw [map_mul, star_mul'] }
  have memI : ∀ o : 𝓞 K, o ∈ I ↔ ∃ m ∈ M, h m z = star (o : K) := fun o => Iff.rfl
  by_contra hne
  push_neg at hne
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, e⟩ := (memI 1).1 h1
    exact hne m hm (by rw [e]; show star (algebraMap (𝓞 K) K 1) = 1; rw [map_one, star_one])
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField K)
  obtain ⟨c, hc, hc1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hP0 hPmax.ne_top
  have hPne : (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hPne] at hc

  have hcz : (star c) • z ∈ M := by
    rw [memM]
    intro m hm
    obtain ⟨t, ht⟩ := (memM z).1 hz m hm
    obtain ⟨t', ht'⟩ := star_int t
    have e1 : h m z = star (t' : K) := by rw [ht', star_star]; exact ht.symm
    have ht'I : t' ∈ I := (memI t').2 ⟨m, hm, e1⟩
    have hcy := hc _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨t', hIP ht'I, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at hcy
    obtain ⟨s, hs⟩ := hcy
    obtain ⟨s', hs'⟩ := star_int s
    refine ⟨s', ?_⟩
    rw [map_smul, smul_eq_mul, e1, ← star_mul']
    change (s' : K) = _
    rw [hs']
    congr 1
  obtain ⟨o, ho⟩ := hprim _ hcz
  obtain ⟨o', ho'⟩ := star_int o
  apply hc1
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨o', by change (o' : K) = c; rw [ho', ho, star_star]⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_unit_condition : RowZUnit := by
  intro D u F0 Λ hrow
  obtain ⟨_, hMU, hzM, hprim⟩ := row_lattice_mass_holds D u F0 Λ hrow
  obtain ⟨m, hm, hm1⟩ := exists_one (hWb D F0) (Mof D F0 Λ) hMU hzM hprim
  obtain ⟨a, haΛ, rfl⟩ := (RowMPf.mem_Mof D F0 Λ m).1 hm
  refine ⟨a, haΛ, a.2, ?_⟩
  rw [zbar, hWb_mk] at hm1
  exact hm1

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_unit_condition : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnit := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf.row_unit_condition
end
end

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_class_holds : RowClass := rowClass_of_zunit row_unit_condition

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowsMassOfParts
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

end Pos

section Generic

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

end Generic

section Bridge

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_isSymm : (hWb D F0).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [hWb_mk, hWb_mk]
  exact (VS D).herm.eq a.1 b.1

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := by
  refine ⟨Subgroup.one_mem _, fun j => ?_, rfl⟩
  ext x
  simp

theorem one_mem_hz {V1 : Type} [AddCommGroup V1] [Module D.host.E V1]
    (h1 : V1 →ₗ⋆[D.host.E] V1 →ₗ[D.host.E] D.host.E) (z : V1) :
    (1 : V1 ≃ₗ[D.host.E] V1) ∈ hz h1 z :=
  ⟨Subgroup.one_mem _, rfl⟩

theorem gmap_one' {V1 : Type} [AddCommGroup V1] [Module D.host.E V1] [Module (𝓞 D.host.E) V1]
    [IsScalarTower (𝓞 D.host.E) D.host.E V1] (M : Submodule (𝓞 D.host.E) V1) :
    Formalism.HermitianLatticesTheory.gmap (1 : V1 ≃ₗ[D.host.E] V1) M = M := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end Bridge

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AnisotropicComplementDefinite
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardLeOfNonpos
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CTEqConjTranspose
open Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefC

theorem cT_eq_conjTranspose {m k : Type} (P : Matrix m k ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) P = Pᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem jpq_mulVec_of_inr {p q : ℕ} (w : Fin p ⊕ Fin q → ℂ) (hw : ∀ j, w (Sum.inr j) = 0) :
    Formalism.UG.Jpq p q *ᵥ w = w := by
  have hr : w ∘ Sum.inr = 0 := funext hw
  ext x
  rcases x with i | j
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr]
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr, hw]

theorem sigNeg_card_le {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    (J : Matrix n n ℂ) (p q : ℕ) (hJ : Formalism.UG.HasSignature J p q) (u : ι → n → ℂ)
    (hu : LinearIndependent ℂ u)
    (hneg : ∀ d : ι → ℂ, (star (∑ a, d a • u a) ⬝ᵥ (J *ᵥ ∑ a, d a • u a)).re ≤ 0) :
    Fintype.card ι ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_eq_conjTranspose] at hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ
  set Qi : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  have key : ∀ v : n → ℂ, star v ⬝ᵥ (J *ᵥ v) =
      star (Qi *ᵥ (v ∘ e.symm)) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (Qi *ᵥ (v ∘ e.symm))) := by
    intro v
    have hv : Q *ᵥ (Qi *ᵥ (v ∘ e.symm)) = v ∘ e.symm := by
      rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    conv_rhs =>
      rw [← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, dotProduct_mulVec,
        ← Matrix.star_mulVec, hv, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    simp only [dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp_def])
  by_contra hlt
  push_neg at hlt
  let L : (ι → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ (Matrix.mulVecLin Qi) ∘ₗ
      (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Fintype.linearCombination ℂ u)
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hLd : L d = 0 := hdk
  have hyr : ∀ j, (Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm)) (Sum.inr j) = 0 := by
    intro j
    have := congrFun hLd j
    simp only [L, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply] at this
    exact this
  have hform := hneg d
  rw [key, jpq_mulVec_of_inr _ hyr] at hform
  set y := Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm) with hy
  have hnn : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
  have hz : star y ⬝ᵥ y = 0 := by
    rw [Complex.nonneg_iff] at hnn
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith [hnn.1]
    · simpa using hnn.2.symm
  have hy0 : y = 0 := dotProduct_star_self_eq_zero.1 hz
  have hv0 : (∑ a, d a • u a) ∘ e.symm = 0 := by
    rw [← Matrix.one_mulVec ((∑ a, d a • u a) ∘ e.symm), ← hQQi, ← Matrix.mulVec_mulVec, ← hy, hy0,
      Matrix.mulVec_zero]
  have hsum : ∑ a, d a • u a = 0 := by
    funext x
    have := congrFun hv0 (e x)
    simpa using this
  exact hd0 (funext (Fintype.linearIndependent_iff.1 hu d hsum))

theorem linIndep_map {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by
  first | exact Bl.SecondBlockLemmaJ.goal1 .. | (apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaJ.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaJ.goal1 <;> first | assumption | infer_instance)

end PI.UnitaryGroupMassFormula.CntFormula.WbDefC
end
end

open Matrix NumberField Module Formalism.BasicNotions

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefH

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def ctau (S : HSpace E) (τ : E →+* ℂ) (x : S.V) : Fin S.rank → ℂ := fun i => τ (S.frame.repr x i)

theorem hT_coord (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, starRingEnd_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [HSpace.gram, RingHom.id_apply]
  ring

theorem tau_hT (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x y : S.V) :
    τ (S.hT x y) = star (ctau S τ x) ⬝ᵥ ((S.gram.map τ) *ᵥ ctau S τ y) := by
  rw [hT_coord]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, ctau, map_sum, map_mul, hτ, Pi.star_apply, Matrix.map_apply,
    Finset.mul_sum, Complex.star_def]

theorem card_le_of_nonpos (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsig : Formalism.UG.HasSignature (S.gram.map τ) (S.sig τ).1 (S.sig τ).2)
    {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → S.V) (hv : LinearIndependent E v)
    (horth : ∀ a b, a ≠ b → S.hT (v a) (v b) = 0) (hnp : ∀ a, (τ (S.hT (v a) (v a))).re ≤ 0) :
    Fintype.card ι ≤ (S.sig τ).2 := by
  apply WbDefC.sigNeg_card_le (S.gram.map τ) _ _ hsig (fun a => ctau S τ (v a))
  · have hc : LinearIndependent E (fun a => fun i => S.frame.repr (v a) i) := by
      have := hv.map' S.frame.equivFun.toLinearMap S.frame.equivFun.ker
      simpa [Function.comp_def] using this
    exact WbDefC.linIndep_map τ _ hc
  · intro d
    have h1 : ∀ a b, star (ctau S τ (v a)) ⬝ᵥ ((S.gram.map τ) *ᵥ ctau S τ (v b)) = τ (S.hT (v a) (v b)) :=
      fun a b => (tau_hT S τ hτ (v a) (v b)).symm
    have hexp : star (∑ a, d a • ctau S τ (v a)) ⬝ᵥ ((S.gram.map τ) *ᵥ ∑ a, d a • ctau S τ (v a)) =
        ∑ a, star (d a) * d a * τ (S.hT (v a) (v a)) := by
      simp only [star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
        dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [horth b a hb, map_zero, mul_zero])
        (by simp)]
      ring
    rw [hexp, Complex.re_sum]
    apply Finset.sum_nonpos
    intro a _
    have key : (star (d a) * d a * τ (S.hT (v a) (v a))).re =
        ((d a).re ^ 2 + (d a).im ^ 2) * (τ (S.hT (v a) (v a))).re := by
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hnp a)

end PI.UnitaryGroupMassFormula.CntFormula.WbDefH
end
end

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tn_ne_zero (D : D7) (u : D.what₂.Word) : (Tn u : D.host.E) ≠ 0 := by
  unfold Tn
  exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem tau_negT (D : D7) (u : D.what₂.Word) (φ : D.host.E →+* ℂ) : (φ (-(Tn u))).re < 0 := by
  have hT := (D.mem u).A.T_prime.pos
  first
    | simp [Tn, hT]
    | (unfold Tn; simp; exact hT)

theorem rank_VS (D : D7) : (VS D).rank = D.R.k + D.R.rS + (D.R.rS + 1) := by
  unfold VS
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, zero_mul, add_zero]
  omega

theorem wbDef_pos (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    Formalism.HermitianLattices.Ext.L3.IsTotPosDef (hPerp (hWb D F0) (zbar D F0)) := by
  rintro ⟨y, hy⟩ hne φ
  induction y using Submodule.Quotient.induction_on with
  | H a => ?_
  have hya : (VS D).hT F0.z a.1 = 0 := by
    have h := hy
    rw [wPerp, LinearMap.mem_ker, zbar, hWb_mk] at h
    exact h
  have hna : a.1 ∉ F0.X := by
    intro hmem
    apply hne
    apply Subtype.ext
    show Submodule.Quotient.mk a = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmem
  have hval : hPerp (hWb D F0) (zbar D F0) ⟨Submodule.Quotient.mk a, hy⟩ ⟨Submodule.Quotient.mk a, hy⟩ =
      (VS D).hT a.1 a.1 := hWb_mk D F0 a a
  rw [hval]
  by_contra hle
  push Not at hle
  have hT0 := tn_ne_zero D u
  have hzX : ∀ x ∈ F0.X, (VS D).hT F0.z x = 0 := fun x hx => hT_perp_X D F0 (z_mem_perp D F0) hx
  let v : Option (Option (Fin D.R.rS)) → (VS D).V :=
    fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e)
  have hv : LinearIndependent D.host.E v := by
    show LinearIndependent D.host.E
      (fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e) : Option (Option (Fin D.R.rS)) → (VS D).V)
    rw [linearIndependent_option', linearIndependent_option']
    refine ⟨⟨F0.e_indep, ?_⟩, ?_⟩
    · intro hz
      have h := hzX F0.z hz
      rw [F0.z_norm] at h
      exact hT0 (neg_eq_zero.1 h)
    · intro ha
      have hle' : Submodule.span D.host.E
          (Set.range (fun o' : Option (Fin D.R.rS) => Option.casesOn' o' F0.z F0.e)) ≤
          F0.X ⊔ Submodule.span D.host.E {F0.z} := by
        rw [Submodule.span_le]
        rintro _ ⟨o, rfl⟩
        cases o with
        | none => exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        | some i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (hle' ha)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have h1 : (VS D).hT F0.z a.1 = c * (-(Tn u)) := by
        rw [← hxw, map_add (f := _), map_smul, hzX x hx, F0.z_norm, smul_eq_mul, zero_add]
      rw [hya] at h1
      have hc : c = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact h
        · exact absurd (neg_eq_zero.1 h) hT0
      apply hna
      rw [← hxw, hc, zero_smul, add_zero]
      exact hx
  have horth : ∀ o o', o ≠ o' → (VS D).hT (v o) (v o') = 0 := by
    intro o o' hne'
    match o, o', hne' with
    | none, none, h => exact absurd rfl h
    | none, some none, _ =>
      show (VS D).hT a.1 F0.z = 0
      rw [← (VS D).herm.eq F0.z a.1, hya, map_zero]
    | none, some (some j), _ => exact hT_perp_X D F0 a.2 (Submodule.subset_span ⟨j, rfl⟩)
    | some none, none, _ => exact hya
    | some none, some none, h => exact absurd rfl h
    | some none, some (some j), _ => exact hzX _ (Submodule.subset_span ⟨j, rfl⟩)
    | some (some i), none, _ => exact hT_X_perp D F0 (Submodule.subset_span ⟨i, rfl⟩) a.2
    | some (some i), some none, _ => exact F0.z_orth i
    | some (some i), some (some j), _ => exact F0.e_iso i j
  have hnp : ∀ o, (φ ((VS D).hT (v o) (v o))).re ≤ 0 := by
    intro o
    match o with
    | none => exact hle
    | some none =>
      show (φ ((VS D).hT F0.z F0.z)).re ≤ 0
      rw [F0.z_norm]
      exact le_of_lt (tau_negT D u φ)
    | some (some i) =>
      show (φ ((VS D).hT (F0.e i) (F0.e i))).re ≤ 0
      rw [F0.e_iso i i]
      simp
  have hcard := WbDefH.card_le_of_nonpos (VS D) φ (D.sp.cm.cmUnram.2.1 φ) (D.sp.Y_sig 0 φ) v hv horth hnp
  have hs : (VS D).sig φ = D.R.sigY0 := D.sp.baseSpace_signature_eq φ
  rw [hs] at hcard
  simp [Ranks.sigY0] at hcard

private theorem perpS_eq_ker_pi_hT (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    perpS (VS D) F0.X = LinearMap.ker (LinearMap.pi fun a => (VS D).hT (F0.e a)) := by
  ext y
  rw [LinearMap.mem_ker]
  constructor
  · intro hy
    have hy2 : ∀ x ∈ F0.X, (VS D).hT x y = 0 := hy
    funext a
    exact hy2 _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro hy
    have hy' : ∀ a, (VS D).hT (F0.e a) y = 0 := fun a => congrFun hy a
    show ∀ x ∈ F0.X, (VS D).hT x y = 0
    intro x hx
    unfold Formalism.MainNotions.S.FlagG.X at hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hy' a
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul c x _ h1 => simp [h1]

private theorem range_pi_hT_eq_top (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    LinearMap.range (LinearMap.pi fun a => (VS D).hT (F0.e a)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have key : ∀ a, f (fun j => if a = j then 1 else 0) = 0 := by
    have hw : ∀ y, (VS D).hT (∑ a, star (f (fun j => if a = j then 1 else 0)) • F0.e a) y = 0 := by
      intro y
      have h1 : f ((LinearMap.pi fun a => (VS D).hT (F0.e a)) y) = 0 :=
        LinearMap.mem_ker.mp (hf (LinearMap.mem_range_self _ y))
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      simpa [LinearMap.pi_apply, smul_eq_mul, mul_comm] using h1
    have h0 := (VS D).nondeg.1 _ hw
    intro a
    have := Fintype.linearIndependent_iff.mp F0.e_indep
      (fun a => star (f (fun j => if a = j then 1 else 0))) h0 a
    simpa using this
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [key]

theorem wbDef_dim (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) = D.R.k := by
  unfold wPerp
  have hle : F0.X ≤ perpS (VS D) F0.X := by
    rw [perpS_eq_ker_pi_hT D u F0]
    unfold Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext b
    exact F0.e_iso b a
  have hX : finrank D.host.E F0.X = D.R.rS := by
    unfold Formalism.MainNotions.S.FlagG.X
    rw [finrank_span_eq_card F0.e_indep, Fintype.card_fin]
  have hnX : finrank D.host.E (nX D F0) = D.R.rS :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans hX
  have hP : finrank D.host.E (perpS (VS D) F0.X) + D.R.rS = D.R.k + D.R.rS + (D.R.rS + 1) := by
    rw [perpS_eq_ker_pi_hT D u F0]
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun a => (VS D).hT (F0.e a))
    rw [range_pi_hT_eq_top D u F0, finrank_top, Module.finrank_fin_fun] at h1
    have h2 := (VS D).rank_eq
    rw [rank_VS D] at h2
    omega
  have hq : finrank D.host.E (WbQ D F0) + finrank D.host.E (nX D F0) =
      finrank D.host.E (perpS (VS D) F0.X) :=
    Submodule.finrank_quotient_add_finrank (nX D F0)
  have hsurj : Function.Surjective (hWb D F0 (zbar D F0)) := by
    intro c
    refine ⟨(c / -(Tn u)) • zbar D F0, ?_⟩
    rw [map_smul, hWb_zbar, smul_eq_mul]
    have hT0 := tn_ne_zero D u
    field_simp
  have hk := LinearMap.finrank_range_add_finrank_ker (hWb D F0 (zbar D F0))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hk
  omega

theorem anisotropic_complement_definite : WbDef := by
  unfold WbDef
  intro D u F0
  exact ⟨wbDef_pos D u F0, wbDef_dim D u F0⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem row_lattice_mass : RowsMass := by
  intro D u u' _ F0 what₂ hrows
  obtain ⟨hK, hF, -⟩ := field_dictionary_holds D
  obtain ⟨hd, hk⟩ := anisotropic_complement_definite D u F0
  have hGH : GlueHyp D.host.E D.host.F (hWb D F0) (zbar D F0) (D.mem u).A.T :=
    ⟨hK, hF, hWb_isSymm D F0, hWb_zbar D F0, (D.mem u).A.T_prime.pos, hd⟩
  have hrl : ∀ Λ ∈ what₂, IsRowLat D F0 Λ := hrows.1
  have hinj : Set.InjOn (Mof D F0) (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)) := by
    intro Λ₁ h₁ Λ₂ h₂ he
    obtain ⟨γ, hγ, hγe⟩ := (row_class_holds D u F0 Λ₁ Λ₂ (hrl Λ₁ h₁) (hrl Λ₂ h₂)).2
      ⟨1, one_mem_hz D _ _, by rw [gmap_one' D, he]⟩
    obtain ⟨Λ', _, hu⟩ := hrows.2 Λ₂ (hrl Λ₂ h₂)
    have e1 := hu Λ₁ ⟨h₁, γ, hγ, hγe⟩
    have e2 := hu Λ₂ ⟨h₂, 1, one_mem_stabF D F0, gmap_one' D Λ₂⟩
    rw [e1, e2]
  have hreps : IsHzReps (hWb D F0) (zbar D F0) (what₂.image (Mof D F0)) := by
    refine ⟨fun M hM => ?_, fun M hM => ?_⟩
    · obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hM
      exact row_lattice_mass_holds D u F0 Λ (hrl Λ hΛ)
    · obtain ⟨Λ, hΛ, rfl⟩ := row_surjective D u F0 M hM
      obtain ⟨Λ', ⟨hΛ'm, γ, hγ, hγΛ'⟩, hu⟩ := hrows.2 Λ hΛ
      obtain ⟨σ, hσ, hσM⟩ := (row_class_holds D u F0 Λ' Λ (hrl Λ' hΛ'm) hΛ).1 ⟨γ, hγ, hγΛ'⟩
      refine ⟨Mof D F0 Λ', ⟨Finset.mem_image_of_mem _ hΛ'm, σ, hσ, hσM⟩, ?_⟩
      rintro M'' ⟨hM'', σ', hσ', hσ'M⟩
      obtain ⟨Λ'', hΛ''m, rfl⟩ := Finset.mem_image.1 hM''
      obtain ⟨γ'', hγ'', hγ''Λ⟩ := (row_class_holds D u F0 Λ'' Λ (hrl Λ'' hΛ''m) hΛ).2 ⟨σ', hσ', hσ'M⟩
      rw [hu Λ'' ⟨hΛ''m, γ'', hγ'', hγ''Λ⟩]
  have hk2 : 2 ≤ finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) := by
    rw [hk]
    have := D.R.m_add_three_le_k
    omega
  have hne : ∃ M, IsGlueLat (hWb D F0) (zbar D F0) M :=
    GluedLatticeMass.glued_exists hGH hk2 ⟨Mof D F0 (VS D).L0, RowMPf.Mof_isLattice D F0 _ (VS D).standardTuple_isLattice,
      RowMPf.Mof_unimod D F0 _ (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular⟩
  have e := GluedLatticeMass.glued_lattice_mass_formula hGH (by omega) hne hreps
  rw [hk] at e
  rw [← e, Finset.sum_image hinj]
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_congr rfl fun Λ hΛ => ?_
  unfold wRow
  rw [row_weight_formula D u F0 Λ (hrl Λ hΛ)]

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

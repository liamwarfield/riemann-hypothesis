module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenEqOneOfContinuousMulFinitePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenEqOneOfContinuousMulFinitePoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenKer

open GlobalTheory.AdelicU Filter Topology

theorem eq_one_on_finite_of_mul : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  intro D T K hK F hF h1 hmul
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig T.gram
  have hc := continuous_ofFin D.sp.cm.sig T.gram
  have hN : {y | ‖F (ofFin D.sp.cm.sig T.gram y) - 1‖ < 1 / 2} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (isOpen_lt (continuous_norm.comp ((hF.comp hc).sub continuous_const)) continuous_const).mem_nhds
      (by simp [h1])
  have hK' : {y | ofFin D.sp.cm.sig T.gram y ∈ K} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (hK.preimage hc).mem_nhds (by simp [one_mem])
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hN hK')
  refine ⟨W.toSubgroup.comap (projFin D.sp.cm.sig T.gram),
    W.isOpen.preimage (continuous_projFin D.sp.cm.sig T.gram), ?_⟩
  intro k hk hkf
  have hkk : ∀ n : ℕ, ofFin D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram (k ^ n)) = k ^ n := fun n => by
    have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig T.gram (k ^ n)
    rwa [mem_finPts.1 (pow_mem hkf n), map_one, one_mul] at h
  have hW' : ∀ n : ℕ, ‖F (k ^ n) - 1‖ < 1 / 2 ∧ k ^ n ∈ K := fun n => by
    have : projFin D.sp.cm.sig T.gram (k ^ n) ∈ W := by
      rw [map_pow]; exact pow_mem (show projFin D.sp.cm.sig T.gram k ∈ W from hk) n
    have h := hW this
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hkk n] at h
    exact h
  have hpow : ∀ n : ℕ, F (k ^ n) = F k ^ n := fun n => by
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hmul _ (hW' n).2 (pow_mem hkf n) _ (by simpa using (hW' 1).2) hkf, ih, pow_succ]
  exact GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    rw [← hpow]; exact (hW' m).1.le

end GlobalTheory.OpenKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenEqOneOfContinuousMulFinitePointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_eq_one_of_continuous_mul_finitePoints : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  first | exact @GlobalTheory.OpenKer.eq_one_on_finite_of_mul | exact GlobalTheory.OpenKer.eq_one_on_finite_of_mul | (intros; apply GlobalTheory.OpenKer.eq_one_on_finite_of_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix
open scoped Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeilLevelStab

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho GlobalTheory.Mem.CoefInv

variable {D : D7}

theorem actO_one_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem actO_one_mul (S T : HSp D) (k k' : GA D T) (x : WO S T) :
    actO S T 1 (k * k') x = actO S T 1 k (actO S T 1 k' x) := by
  unfold actO
  rw [inv_one, GlobalTheory.AdelicLatMove.mt_one, GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_one, Matrix.mul_assoc]

theorem actO_nsmul (S T : HSp D) (g : GA D S) (h : GA D T) (c : ℕ) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x :=
  map_nsmul (GlobalTheory.LatLevel.actHom S T g h) c x

def MovesMod (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) (k : GA D T) : Prop :=
  ∀ x ∈ L, ∃ l ∈ L, actO S T 1 k x = x + c • l

theorem movesMod_one (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : MovesMod S T L c 1 :=
  fun x _ => ⟨0, zero_mem _, by rw [actO_one_one, smul_zero, add_zero]⟩

theorem movesMod_mul {S T : HSp D} {L : AddSubgroup (WO S T)} {c : ℕ} {k k' : GA D T}
    (hk : MovesMod S T L c k) (hk' : MovesMod S T L c k') : MovesMod S T L c (k * k') := by
  intro x hx
  obtain ⟨l', hl', e'⟩ := hk' x hx
  obtain ⟨l, hl, e⟩ := hk x hx
  obtain ⟨l'', hl'', e''⟩ := hk l' hl'
  refine ⟨l + (l' + c • l''), add_mem hl (add_mem hl' (AddSubgroup.nsmul_mem _ hl'' c)), ?_⟩
  rw [actO_one_mul, e', GlobalTheory.LatNhds.actO_add, actO_nsmul, e, e'']
  simp only [smul_add]
  abel

def stabK (S T : HSp D) (L : AddSubgroup (WO S T)) (c : ℕ) : Subgroup (GA D T) where
  carrier := {k | MovesMod S T L c k ∧ MovesMod S T L c k⁻¹}
  one_mem' := ⟨movesMod_one S T L c, by rw [inv_one]; exact movesMod_one S T L c⟩
  mul_mem' := fun ha hb => ⟨movesMod_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact movesMod_mul hb.2 ha.2⟩
  inv_mem' := fun ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isOpen_stabK (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (c : ℕ) (hc : 0 < c) :
    IsOpen ((stabK S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) c : Subgroup (GA D T)) : Set (GA D T)) := by
  have h := eventually_mod ΛS ΛT hS hT c hc
  have ht : Filter.Tendsto (fun k : GA D T => ((1 : GA D S), k)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const (y := (1 : GA D S))).prodMk continuous_id).tendsto (1 : GA D T)
    exact this
  have ti : Filter.Tendsto (fun k : GA D T => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D T)).tendsto 1
    rwa [inv_one] at this
  have h1 := ht.eventually h
  have h2 := ti.eventually h1
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [h1, h2] with k hk hk'
  exact ⟨hk, hk'⟩

theorem exists_level_stab_of_selfDual (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧
      (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 →
        actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧
      (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
        actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧
          ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hLdef
  obtain ⟨n, hn, hnU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  obtain ⟨hdual, happrox, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  refine ⟨L.map (nsmulAddMonoidHom n), stabK S T L (2 * n * n), ?_,
    isOpen_stabK S T ΛS ΛT hS hT (2 * n * n) (by positivity), ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hnU u hu
  · intro x
    obtain ⟨ρ, hρ, u, hu, hf⟩ := happrox (x - realIdem D • x) (fin_part x)
    refine ⟨ρ, hρ, ?_⟩
    rintro _ ⟨l, hl, rfl⟩ -
    have hnl : n • l ∈ L := AddSubgroup.nsmul_mem _ hl n
    have e : x - ρ = (realIdem D • x + (x - realIdem D • x - ρ - u)) + u := by abel
    show ψ (symplO S T (x - ρ) (n • l)) = 1
    rw [e, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      symplO_real_fin S T (real_part x) (latO_fin hnl), symplO_real_fin S T hf (latO_fin hnl), zero_add, zero_add]
    exact (hdual u (latO_fin hu)).1 hu _ hnl
  · rintro k ⟨hk, -⟩ - _ ⟨l, hl, rfl⟩ -
    obtain ⟨l', hl', e⟩ := hk l hl
    have hm : l + (2 * n * n) • l' ∈ L := add_mem hl (AddSubgroup.nsmul_mem _ hl' _)
    have e2 : actO S T 1 k (n • l) = n • (l + (2 * n * n) • l') := by rw [actO_nsmul, e]
    refine ⟨⟨_, hm, e2.symm⟩, ?_⟩
    show (actO S T 1 k (n • l)).map (infPart D) = 0
    rw [e2]
    exact latO_fin (AddSubgroup.nsmul_mem _ hm n)
  · rintro k ⟨hk, -⟩ hkf w hw
    have hw' : ∀ l ∈ L, ψ (symplO S T (n • w) l) = 1 := fun l hl => by
      rw [symplO_nsmul]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))
    have hff : (n • w - realIdem D • (n • w)).map (infPart D) = 0 := fin_part _
    have hfL : n • w - realIdem D • (n • w) ∈ L := GlobalTheory.LatVac.mem_of_char hψ hS hT hff fun u hu => by
      rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_real_fin S T (real_part _) (latO_fin hu), sub_zero]
      exact hw' u hu
    obtain ⟨l, hl, e⟩ := hk _ hfL
    have hreal := actO_real (one_mem (GfC S)) hkf (real_part (n • w))
    have e1 : actO S T 1 k w = w + 2 • (n • l) := by
      refine nsmul_cancel hn ?_
      rw [← actO_nsmul, show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel,
        GlobalTheory.LatNhds.actO_add, hreal, e, ← add_assoc, ← show n • w = realIdem D • (n • w) + (n • w - realIdem D • (n • w)) by abel]
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      ring
    have hd : actO S T 1 k w - w = 2 • (n • l) := by rw [e1, add_sub_cancel_left]
    refine ⟨⟨2 • l, AddSubgroup.nsmul_mem _ hl 2, ?_⟩, ?_, ?_⟩
    · rw [hd]
      exact smul_comm n 2 l
    · rw [hd]
      exact latO_fin (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl n) 2)
    · rw [hd, two_nsmul, symplOH_add_right, symplOH_add_self]
      exact hw _ ⟨l, hl, rfl⟩ (latO_fin (AddSubgroup.nsmul_mem _ hl n))

theorem exists_level_stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  intro D ψ S T hψ U hU
  exact exists_level_stab_of_selfDual ψ S T hψ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) U hU

end GlobalTheory.WeilLevelStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  first | exact @GlobalTheory.WeilLevelStab.exists_level_stab | exact GlobalTheory.WeilLevelStab.exists_level_stab | (intros; apply GlobalTheory.WeilLevelStab.exists_level_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionProdConjEqOfHeisenbergFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionProdConjEqOfHeisenbergFixed
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFixedProd

theorem setIntegral_add_right {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hper : ∀ γ ∈ Γ, ∀ x, h (γ + x) = h x) (l : G) :
    ∫ x in 𝓕, h (x + l) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have hs : IsAddFundamentalDomain Γ ((fun x => x - l) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_sub_right μ l).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by
        show (g +ᵥ x) - l = g +ᵥ (x - l)
        simp only [AddSubgroup.vadd_def, vadd_eq_add]
        abel)
  have e1 : ∫ x in 𝓕, h (x + l) ∂μ = ∫ y in (fun x => x - l) ⁻¹' 𝓕, h y ∂μ := by
    rw [← (measurePreserving_add_right μ l).setIntegral_preimage_emb (measurableEmbedding_addRight l) h]
    congr 2
    ext x
    simp
  rw [e1]
  exact hs.setIntegral_eq h𝓕 fun g x => hper g g.2 x

theorem prod_eq_of_fixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  intro D ψ S T hψ N M hMV hc hn f g hf hfN hg hgN x
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hcomp := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f}
      add_mem' := fun {a b} ha hb => ⟨GlobalTheory.WeilVacMove.isTheta_add ha.1 hb.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        have e2 := congrFun (hb.2 u hu h0) w
        simp only [heisO, Pi.add_apply] at e1 e2 ⊢
        rw [mul_add, e1, e2]⟩
      zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun u _ _ => by funext w; simp [heisO]⟩
      smul_mem' := fun c a ha => ⟨GlobalTheory.WeilVacMove.isTheta_smul c ha.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢
        rw [mul_left_comm, e1]⟩ }
  have hb : ∀ a ∈ Θ, ∃ C : ℝ, ∀ w, ‖a w‖ ≤ C := fun a ha => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖a (γ + w)‖ = ‖a w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (ha.1.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha.1.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  have hMΘ : ∀ a ∈ Θ, M a ∈ Θ := fun a ha => hMV a ha.1 ha.2
  have hpol : ∀ a a', a ∈ Θ → a' ∈ Θ → ∫ w in 𝓕, M a w * star (M a' w) ∂μ = ∫ w in 𝓕, a w * star (a' w) ∂μ :=
    fun a a' ha ha' => GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) Θ (fun b hb => hb.1.cont.measurable) hb M
      hMΘ (fun b hb => hn μ 𝓕 hμ h𝓕 b hb.1 hb.2) a a' ha ha'
  have hint : ∀ a a', IsThetaFunO ψ S T a → IsThetaFunO ψ S T a' →
      Integrable (fun w => a w * star (a' w)) (μ.restrict 𝓕) := fun a a' ha ha' => by
    have hcont : Continuous fun w => a w * star (a' w) := ha.cont.mul ha'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ ha ha' hγ w]
    exact hC _ h
  have hfix : ∀ a a', a ∈ Θ → a' ∈ Θ → ∀ l ∈ N, l.map (infPart D) = 0 → ∀ w,
      a (w + l) * star (a' (w + l)) = a w * star (a' w) := fun a a' ha ha' l hl h0 w => by
    have e1 := congrFun (ha.2 l hl h0) w
    have e2 := congrFun (ha'.2 l hl h0) w
    simp only [heisO] at e1 e2
    rw [← e1, ← e2, star_mul']
    linear_combination -(a (w + l) * star (a' (w + l))) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T w l)
  have hfΘ : f ∈ Θ := ⟨hf, hfN⟩
  have hgΘ : g ∈ Θ := ⟨hg, hgN⟩
  have hadd : ∀ y z γ : WO S T, ψ (symplO S T (y + z) γ) = ψ (symplO S T y γ) * ψ (symplO S T z γ) := fun y z γ => by
    simp only [← l4, l1, AddChar.map_add_eq_mul]
    ring
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => hadd x y γ)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M g x) - f x * star (g x))
    (((hMΘ f hfΘ).1.cont.mul (hMΘ g hgΘ).1.cont.star).sub (hf.cont.mul hg.cont.star))
    (fun γ hγ x => by
      rw [GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ,
        GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hγ])
    (fun γ => by
      show ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0
      by_cases hγ : ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (γ : WO S T) l) = 1
      · have hγf : heisO ψ S T γ f ∈ Θ := ⟨hth _ f hf, fun u hu h0 => by
          funext w
          have a1 := congrFun (hcomp u γ f) w
          have a2 := congrFun (hcomp γ u f) w
          rw [hfN u hu h0, add_comm (γ : WO S T) u] at a2
          simp only [Pi.smul_apply, smul_eq_mul] at a1 a2
          rw [a1, a2]
          congr 1
          have h1 := hγ u hu h0
          rw [← l4, AddChar.map_add_eq_mul] at h1
          rw [GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) u]
          have h2 : ψ (-symplOH S T (γ : WO S T) u) * ψ (symplOH S T (γ : WO S T) u) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination (-ψ (-symplOH S T (γ : WO S T) u)) * h1 + ψ (symplOH S T (γ : WO S T) u) * h2⟩
        have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) = fun x =>
            M (heisO ψ S T γ f) x * star (M g x) - heisO ψ S T γ f x * star (g x) := by
          funext x
          rw [hc _ f hf hfN hγ, GlobalTheory.ThetaSchur.heisO_rat hf γ.2, GlobalTheory.ThetaSchur.heisO_rat (hMΘ f hfΘ).1 γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hMΘ _ hγf).1 (hMΘ g hgΘ).1) (hint _ _ hγf.1 hg), hpol _ _ hγf hgΘ, sub_self]
      · push_neg at hγ
        obtain ⟨l, hl, h0, hne⟩ := hγ
        have hper : ∀ δ ∈ ratL T S, ∀ x, (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)))
            (δ + x) = (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) x := by
          intro δ hδ x
          simp only
          rw [hadd, (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T δ).2 hδ γ γ.2, one_mul,
            GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hδ,
            GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hδ]
        have htr := GlobalTheory.ThetaFixedProd.setIntegral_add_right (G := WO S T) (ratL T S) μ h𝓕
          (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) hper l
        simp only [hadd, hfix _ _ (hMΘ f hfΘ) (hMΘ g hgΘ) l hl h0, hfix _ _ hfΘ hgΘ l hl h0] at htr
        have hsk : symplO S T l γ = -symplO S T (γ : WO S T) l := by
          rw [← l4, ← l4, GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) l]
          abel
        have hc1 : ψ (symplO S T l γ) ≠ 1 := fun h1 => by
          apply hne
          rw [hsk] at h1
          have h2 : ψ (symplO S T (γ : WO S T) l) * ψ (-symplO S T (γ : WO S T) l) = 1 := by
            rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
          rw [h1, mul_one] at h2
          exact h2
        have e2 : (fun x => ψ (symplO S T x γ) * ψ (symplO S T l γ) * (M f x * star (M g x) - f x * star (g x))) =
            fun x => ψ (symplO S T l γ) * (ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) := by
          funext x
          ring
        rw [e2, integral_const_mul] at htr
        have h3 : (ψ (symplO S T l γ) - 1) *
            ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0 := by
          linear_combination htr
        exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc1))
  exact sub_eq_zero.1 (congrFun key x)

end GlobalTheory.ThetaFixedProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionProdConjEqOfHeisenbergFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_prod_conj_eq_of_heisenbergFixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  first | exact @GlobalTheory.ThetaFixedProd.prod_eq_of_fixed | exact GlobalTheory.ThetaFixedProd.prod_eq_of_fixed | (intros; apply GlobalTheory.ThetaFixedProd.prod_eq_of_fixed <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilLevel

theorem stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary
theorem prodId : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := GlobalTheory.T.thetaFunction_prod_conj_eq_of_heisenbergFixed
theorem openKer : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := GlobalTheory.T.exists_open_eq_one_of_continuous_mul_finitePoints

theorem scalar_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ))
    (hAR : ∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1)
    (hM : ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hp : ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      ∀ x, M f x * star (M g x) = f x * star (g x)) :
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → M f = c • f := by
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨l1, l2, l3, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
    rw [Complex.star_def, Complex.mul_conj', h]; simp
  have skew : ∀ x y : WO S T, symplOH S T y x = -symplOH S T x y := fun x y => by
    have := l3 (x + y)
    rw [l1, l2, l2, l3, l3] at this
    linear_combination this

  have hfix : ∀ w g, (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T w g) = (heisO ψ S T w g)) := by
    intro w g hg hw u hu hu0
    have e1 := hcomp u w g
    have e2 := hcomp w u g
    rw [hg u hu hu0] at e2
    rw [e1, add_comm u w]
    have hs : ψ (symplOH S T u w) = ψ (symplOH S T w u) := by
      have h1 := hw u hu hu0
      rw [← l4] at h1
      have h2 : ψ (symplOH S T w u) * ψ (symplOH S T w u) = 1 := by
        rw [← AddChar.map_add_eq_mul]; exact h1
      rw [skew w u, AddChar.map_neg_eq_inv]
      exact inv_eq_of_mul_eq_one_right h2
    rw [hs, e2]
  by_cases h0 : ∃ f₀ x₀, IsThetaFunO ψ S T f₀ ∧ (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f₀ = f₀) ∧ f₀ x₀ ≠ 0
  · obtain ⟨f₀, x₀, hf₀, hf₀N, hx₀⟩ := h0
    have h1 := hp f₀ f₀ hf₀ hf₀N hf₀ hf₀N x₀
    have hn1 : ‖M f₀ x₀‖ = ‖f₀ x₀‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ x₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]; exact norm_ne_zero_iff.2 hx₀
    have hs : star (M f₀ x₀) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ x₀) / star (M f₀ x₀), fun f hf hfN => funext fun x => ?_⟩
    obtain ⟨γ, hγ, hA⟩ := hAR (x₀ - x)
    set w := x₀ - x - γ with hw
    have hg := hth w f₀ hf₀
    have hgN := hfix w f₀ hf₀N hA
    have h2 := hp f (heisO ψ S T w f₀) hf hfN hg hgN x
    rw [hc w f₀ hf₀ hf₀N hA] at h2
    obtain ⟨δ, hδ⟩ := (ratL T S).neg_mem hγ
    have hxw : x + w = ratW T S δ + x₀ := by
      have hδ' : ratW T S δ = -γ := hδ
      rw [hδ', hw]; abel
    simp only [heisO, hxw] at h2
    rw [hf₀.quasi δ x₀, (hM f₀ hf₀ hf₀N).quasi δ x₀] at h2
    rw [star_mul', star_mul', star_mul', star_mul'] at h2
    have h3 : M f x * star (M f₀ x₀) = f x * star (f₀ x₀) := by
      linear_combination (ψ (symplOH S T x w) * ψ (-symplOH S T (ratW T S δ) x₀)) * h2
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * hunit (symplOH S T x w)
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * ψ (symplOH S T x w) * star (ψ (symplOH S T x w))
          * hunit (-symplOH S T (ratW T S δ) x₀)
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h3, mul_comm]
  · refine ⟨0, fun f hf hfN => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hfN, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.WeilLevel

module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulasStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatrices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisComb

variable {D : D7}

theorem heisO_finset_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (g : ι → WO S T → ℂ) :
    heisO ψ S T x (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i • heisO ψ S T x (g i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (comb ψ S T c' f) =
      ∑ x ∈ c.support, ∑ y ∈ c'.support, (c x * c' y) • heisO ψ S T x (heisO ψ S T y f) := by
  unfold comb
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [heisO_finset_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

theorem symplO_half (S T : HSp D) (e e' : AE D) (x y : WO S T) (he : cA D e = e) (hee : e * e' = 0)
    (hx : IsHalf e x) (hy : IsHalf e' y) : symplO S T x y = 0 := by
  have h0 : e * cA D e' = 0 := by
    conv_lhs => rw [← he]
    rw [← map_mul, hee, map_zero]
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hy c b, ← hx d a, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D e' * cA D (y c b)) * incA D (T.gram c d) * (e * x d a)
        = (e * cA D e') * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ c c' : WO S T →₀ ℂ, ∃ c'' : WO S T →₀ ℂ, (∀ w ∈ c''.support, ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y) ∧ ∀ f, comb ψ S T c'' f = comb ψ S T c (comb ψ S T c' f)) ∧ (∀ c c' : WO S T →₀ ℂ, (∀ x ∈ c.support, ∀ y ∈ c'.support, symplO S T x y = 0) → ∀ f, comb ψ S T c (comb ψ S T c' f) = comb ψ S T c' (comb ψ S T c f)) ∧ (∀ (c : WO S T →₀ ℂ) f, IsThetaFunO ψ S T f → IsFinComb c → IsStdChar D ψ (-1) → IsThetaFunO ψ S T (comb ψ S T c f)) ∧ ∀ (e e' : AE D) (x y : WO S T), cA D e = e → e * e' = 0 → IsHalf e x → IsHalf e' y → symplO S T x y = 0 := by
  intro D ψ S T
  refine ⟨fun c c' => ?_, fun c c' h f => ?_, fun c f hf hc hψ => ?_,
    fun e e' x y he hee hx hy => symplO_half S T e e' x y he hee hx hy⟩
  · classical
    refine ⟨∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y)), ?_,
      fun f => ?_⟩
    · intro w hw
      have h1 := Finsupp.support_finsetSum hw
      rw [Finset.mem_biUnion] at h1
      obtain ⟨x, hx, hw2⟩ := h1
      have h2 := Finsupp.support_finsetSum hw2
      rw [Finset.mem_biUnion] at h2
      obtain ⟨y, hy, hw3⟩ := h2
      have h3 := Finsupp.support_single_subset hw3
      rw [Finset.mem_singleton] at h3
      exact ⟨x, hx, y, hy, h3⟩
    · rw [comb_comb, comb_eq_sum]
      rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]
  · rw [comb_comb, comb_comb, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    have h0 : symplOH S T x y = 0 := by
      unfold symplOH
      rw [h x hx y hy, mul_zero]
    have h1 : symplOH S T y x = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]
    rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, h0, h1, add_comm x y, mul_comm (c x)]
  · exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf (WO S T) c.support id (fun u => c u) hc

end GlobalTheory.HeisComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_eq_zero_of_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (a : AE D) (ha : toEAf D a = 0) : q.pr a = 0 := by
  have h0 : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) he).1
  have h1 : finPart D a = 0 :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective (by
      rw [map_zero]; exact ha)
  have h2 : q.e * a = 0 := GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_mul, h0, zero_mul]) (by rw [map_mul, h1, mul_zero])
  rw [← q.pr_sec (q.pr a), q.sec_pr, h2, map_zero]

def prF (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) : EAf D →+* k :=
  (RingHom.liftOfSurjective (toEAf D) (fun s => GlobalTheory.ResLoc.toEAf_surj s))
    ⟨q.pr, fun a ha => (RingHom.mem_ker).2 (q.pr_eq_zero_of_toEAf he a ((RingHom.mem_ker).1 ha))⟩

theorem prF_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (a : AE D) :
    q.prF he (toEAf D a) = q.pr a :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem pr_mem_iff (q : SplitPt D k) (a : AE D) :
    q.pr a ∈ 𝒪[k] ↔ toEAf D q.e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [q.int_iff, q.sec_pr, ← map_mul]
  exact ⟨GlobalTheory.IdemRes.toEAf_mem_of_finPart, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_iff_val_lt (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : x ∈ PP.asIdeal ↔
      valuation k (q.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D)) < 1 := by
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  rw [e1, prF_toEAf]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, Submodule.zero_mem, true_iff]
    simp
  have hx' : (x : D.host.E) ≠ 0 := fun h => hx (RingOfIntegers.coe_eq_zero_iff.1 h)
  set y := q.pr (incA D (x : D.host.E)) with hy
  have hy0 : y ≠ 0 := fun h => by
    have : (q.pr.comp (incA D)) (x : D.host.E) = 0 := h
    exact hx' ((map_eq_zero_iff _ (q.pr.comp (incA D)).injective).1 this)
  have hinv : q.pr (incA D ((x : D.host.E)⁻¹)) = y⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  rw [he.2 x hx, ← q.sec_pr, ← q.int_iff, hinv]
  change ¬ valuation k y⁻¹ ≤ 1 ↔ _
  rw [not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy0), inv_inv]

theorem val_lt_of_mem_idS (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) :
    valuation k (q.prF he s.1) < 1 := by
  have hint : ∀ c : Formalism.L2.Herm.intAf D.host.F D.host.E, valuation k (q.prF he c.1) ≤ 1 := fun c => by
    obtain ⟨a, ha⟩ := GlobalTheory.ResLoc.toEAf_surj c.1
    have := (q.pr_mem_iff a).2 (by rw [ha]; exact mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1 c.2)
    rw [← ha, prF_toEAf]; exact this
  refine Submodule.span_induction (p := fun s _ => valuation k (q.prF he s.1) < 1) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact (q.mem_iff_val_lt he a).1 ha
  · simp
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hint c) zero_le').trans_lt (by rwa [one_mul])

theorem resS_eq_zero_of_mem {PP : Formalism.L2.DIV.Pl D.host.E} {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) : Formalism.L2.DIV.resS D.host.F PP s = 0 := by
  have : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ RingHom.ker (Formalism.L2.DIV.resS D.host.F PP) :=
    Ideal.map_le_iff_le_comap.2 fun b hb => Ideal.mem_comap.2 ((RingHom.mem_ker).2 (by
      rw [Formalism.L2.DIV.resS_oToS]; exact Ideal.Quotient.eq_zero_iff_mem.2 hb))
  exact (RingHom.mem_ker).1 (this hs)

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prF_mem_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    q.prF he z ∈ 𝒪[k] ↔ toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj z
  rw [prF_toEAf]; exact q.pr_mem_iff a

theorem resS_eq_zero_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP s = 0 ↔ valuation k (q.prF he s.1) < 1 := by
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h1 : Formalism.L2.DIV.resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal a := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) PP a, ← sub_eq_zero, ← map_sub]
    exact resS_eq_zero_of_mem ha
  have h2 := q.val_lt_of_mem_idS he ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub] at h2
  rw [h1, Ideal.Quotient.eq_zero_iff_mem, q.mem_iff_val_lt he]
  constructor
  · intro h; simpa using Valuation.map_add_lt _ h2 h
  · intro h; simpa using Valuation.map_sub_lt _ h h2

theorem mem_intAf_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ q.prF he z ∈ 𝒪[k] := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  rw [q.prF_mem_iff he]
  constructor
  · intro hz
    exact ⟨mul_mem (sub_mem (one_mem _) hint) hz, mul_mem hint hz⟩
  · rintro ⟨h1, h2⟩
    have : z = (1 - toEAf D q.e) * z + toEAf D q.e * z := by
      rw [sub_mul, one_mul, sub_add_cancel]
    rw [this]; exact add_mem h1 h2

set_option maxHeartbeats 1000000 in
theorem resS_off (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (PP' : Formalism.L2.DIV.Pl D.host.E) (hne : PP' ≠ PP) (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have h0 : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D q.e, hint⟩ = 0 := by
    obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' ⟨toEAf D q.e, hint⟩
    rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
    rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' ⟨toEAf D q.e, hint⟩] at h2
    change Valued.v (GlobalTheory.StdFrames.cpt PP' (toEAf D q.e) - _) < 1 at h2
    rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 PP' hne, zero_sub, Valuation.map_neg] at h2
    exact h2
  have e1 : (⟨(1 - toEAf D q.e) * z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (1 - ⟨toEAf D q.e, hint⟩) * ⟨z, hz⟩ :=
    Subtype.ext (by rw [Subring.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one])
  refine (congrArg (Formalism.L2.DIV.resS D.host.F PP') e1).trans ?_
  rw [map_mul, map_sub, map_one, h0, sub_zero, one_mul]

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

theorem exists_lift_isRed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∃ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) ∧ GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ∧ (∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP' ≠ PP → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  refine ⟨q.prF he, q.prF_toEAf he, ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal,
    fun s => (q.prF_mem_iff he s.1).2 (mul_mem hint s.2), fun s => q.resS_eq_zero_iff he s⟩,
    q.mem_intAf_iff he, fun PP' hne z hz hz' => q.resS_off he PP' hne z hz hz'⟩

end GlobalTheory.FinPl.SplitPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_projection_integral_reduction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∃ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) ∧ GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ∧ (∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP' ≠ PP → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  first | exact @GlobalTheory.FinPl.SplitPt.exists_lift_isRed | exact GlobalTheory.FinPl.SplitPt.exists_lift_isRed | (intros; apply GlobalTheory.FinPl.SplitPt.exists_lift_isRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.LinSpace

variable {D : D7}

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp [heisO, mul_add]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w; simp [heisO]; ring

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) :
    heisO ψ S T u 0 = 0 := by
  funext w; simp [heisO]

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi := by intro γ w; simp
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' ψ S T u⟩
  cont := continuous_const
  smooth := by intro k L _ _ w; exact contDiff_const }

theorem isThetaFunO_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := {
  quasi := by intro γ w; simp [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, ?_, ?_⟩
    · rw [AddSubgroup.coe_inf]; exact hU.inter hV
    · intro u hu h0
      rw [heisO_add', hUf u hu.1 h0, hVg u hu.2 h0]
  cont := hf.cont.add hg.cont
  smooth := by
    intro k L hL hL' w
    exact (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (c : ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi := by intro γ w; simp [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', hUf u hu h0]⟩
  cont := continuous_const.mul hf.cont
  smooth := by
    intro k L hL hL' w
    exact contDiff_const.mul (hf.smooth k L hL hL' w) }

end GlobalTheory.LocMod.LinSpace


open GlobalTheory.LocMod.LinSpace in
theorem GlobalTheory.LocMod.Place.isModel_linear : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  intro D k _ _ _ _ p ψ Y Y' _ _ _ _ S T FS FT
  refine ⟨⟨fun Φ => isThetaFunO_zero ψ S T, ?_, ?_⟩, ?_⟩
  · intro x Φ Φ' _; simp [heisO_zero']
  · intro y _ Φ Φ' _; simp [heisO_zero']
  · intro T₁ T₂ h₁ h₂
    refine ⟨⟨fun Φ => isThetaFunO_add (h₁.theta Φ) (h₂.theta Φ), ?_, ?_⟩, fun c => ⟨fun Φ => isThetaFunO_smul c (h₁.theta Φ), ?_, ?_⟩⟩
    · intro x Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.trans x Φ Φ' h, h₂.trans x Φ Φ' h, heisO_add']
    · intro y hy Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.modul y hy Φ Φ' h, h₂.modul y hy Φ Φ' h, heisO_add']
    · intro x Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.trans x Φ Φ' h, heisO_smul']
    · intro y hy Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.modul y hy Φ Φ' h, heisO_smul']
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalPlace_local_models_linear_subspace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  first | exact @GlobalTheory.LocMod.Place.isModel_linear | exact GlobalTheory.LocMod.Place.isModel_linear | (intros; apply GlobalTheory.LocMod.Place.isModel_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixSourceFormulas

theorem mixed_source : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  intro D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ f hf
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ ho.std S T).1
  have hbr : ∀ (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 :=
    fun f x => (GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 f x
  have hmv := GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hun := GlobalTheory.T.wittMixedModel_unipotent_formulas D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hlv := fun w => GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ (heisO ψ S T w f) (hth w f hf)
  unfold I195MixedCoordinates_3601ff04f10fcda6f28caf89.source at hmv
  unfold I195MixedCoordinates_34c45ee3f9864caed77cce75.source at hlv
  unfold HypDec.mixS HypDec.extX HypDec.extY HypDec.ext0 at hbr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    have hor := GlobalTheory.T.mixedCoordinate_origin_weilRep_target_equivariant D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ h (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f) (hth _ f hf)
    unfold I195MixedCoordinates_6a77e1566d048881366221d8.source at hor
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [(hmv x).1 h, hor]
    exact congrArg (om₀ (1, h)) (hbr f (mt T h⁻¹ ⬝ x)).symm
  · intro g x
    have e := (hmv x).2.1 1 g
    rw [map_one, one_mul, Units.val_one, Matrix.mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).1 g]
    exact congrArg (om₀ (g, 1)) (hbr f x).symm
  · intro a x
    have e := (hmv x).2.1 a 1
    rw [map_one, mul_one] at e
    unfold I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source
    rw [e, (hlv _).2.2 a]
    exact congrArg (fun (z : WO S₀ T → ℂ) => (((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • z) (hbr f (x ⬝ a.1)).symm
  · intro b x
    exact (hun x).1 b
  · intro c x
    exact (hun x).2 c

end GlobalTheory.MixSourceFormulas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelFormulasWittSource_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  first | exact @GlobalTheory.MixSourceFormulas.mixed_source | exact GlobalTheory.MixSourceFormulas.mixed_source | (intros; apply GlobalTheory.MixSourceFormulas.mixed_source <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem smul_mem_latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) (w : AE D)
    (hw : finPart D w ∈ intAE D) : ∀ y ∈ latMul S 𝔞 L P, w • y ∈ latMul S 𝔞 L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := AddMonoidHom.mk' (fun u => w • u) fun x y => smul_add w x y
  have main : latMul S 𝔞 L P ≤ (latMul S 𝔞 L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) := AddMonoidHom.mk'
      (fun y => fun i => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] (a * x i)) y)
      fun y y' => funext fun i => (GlobalTheory.LatticeStable.liftMul D _).map_add y y'
    have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, a, ha, o • x, L.smul_mem o hx, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · funext i
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finPart_e_int (q : SplitPt D k) : finPart D q.e ∈ intAE D := by
  have h := (q.int_iff 1).1 (one_mem _)
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  rwa [h1] at h

theorem e_mul_mem_latV (q : SplitPt D k) (S : HSp D) (L : Lat S) {s : Fin S.rank → D.host.E} (hs : s ∈ L) :
    (fun j => q.e * incA D (s j)) ∈ latV S L (· = q.v) := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hg : (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    AddSubgroup.subset_closure ⟨α, hα, fun u hu => h0 u hu, 1, rfl, s, hs, rfl⟩
  have he : q.e • (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    smul_mem_latMul S {1} L (· = q.v) q.e (finPart_e_int q) _ hg
  convert he using 1
  funext j
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]
  rw [Pi.smul_apply, smul_eq_mul, one_mul]
  have : pairA D.host.F 0 α ⊗ₜ[D.host.F] s j = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D (s j) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, ← mul_assoc, hee]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem rankOne_mem_latO (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) {y : Fin T.rank → AE D} (hy : y ∈ latA T LT P) :
    (Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
  let Φ : (Fin T.rank → AE D) →+ WO S T := AddMonoidHom.mk'
    (fun y => Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j))
    fun y y' => Matrix.ext fun i j => add_mul (y i) (y' i) _
  have main : latA T LT P ≤ (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    ext i j
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  exact main hy

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul (q : SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
open GlobalTheory.FinPl

theorem up_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT x hx
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S LS hS
  set u := (ofSplit q).up FS FT x with hu_def
  let z : Fin n → Y' → k := fun c => FS.γ *ᵥ (fun m => q.pr (incA D (s c m)))
  let y : Fin n → Fin T.rank → AE D := fun c i => ∑ m, u i m * incA D (s c m)
  have hz : ∀ c r, z c r ∈ 𝒪[k] := by
    intro c
    refine (hFS (z c)).2 ?_
    have : (fun i => q.sec ((FS.β *ᵥ z c) i)) = fun j => q.e * incA D (s c j) := by
      funext j
      simp only [z, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      exact q.sec_pr _
    rw [this]
    exact e_mul_mem_latV q S LS (hs c).1
  have hy : ∀ c, y c ∈ latA T LT (· = q.v) := by
    intro c
    rw [hU.2 T LT]
    have hint : ∀ r, (x *ᵥ z c) r ∈ 𝒪[k] := fun r =>
      Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hx r m) (hz c m)
    convert (hFT (x *ᵥ z c)).1 hint using 1
    funext i
    change ∑ m, q.sec ((FT.β * x * FS.γ) i m) * incA D (s c m) = _
    simp_rw [sec_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    simp only [z, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc]
    rfl
  have hdec : u = ∑ c, (Matrix.of fun i j => y c i * incA D (∑ l, star (s' c l) * S.gram l j) : WO S T) := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, y, Finset.sum_mul]
    rw [Finset.sum_comm]
    have key : ∀ m, ∑ c, u i m * incA D (s c m) * incA D (∑ l, star (s' c l) * S.gram l j) =
        u i m * incA D (if m = j then 1 else 0) := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hss m j, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp [apply_ite]
  rw [hdec]
  exact sum_mem fun c _ => rankOne_mem_latO S T LS LT _ (hs c).2 (hy c)

end GlobalTheory.UpMem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  first | exact @GlobalTheory.UpMem.up_mem_latO | exact GlobalTheory.UpMem.up_mem_latO | (intros; apply GlobalTheory.UpMem.up_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocModU

theorem upAdd {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x x' : Matrix Y Y' k) :
    p.up FS FT (x + x') = p.up FS FT x + p.up FS FT x' := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply]

theorem upZero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : p.up FS FT 0 = 0 := by
  unfold Place.up
  ext i j
  simp [Matrix.map_apply]

theorem charZero_of_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) : CharZero k :=
  (RingHom.charZero_iff (ϕ := p.π.comp (incA D)) (RingHom.injective _)).1 inferInstance

theorem localModel_uniq_transport_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ
  haveI : CharZero k := charZero_of_place p
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.T.heisenberg_frame_half_inverse D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have hcce : cA D (cA D p.e) * cA D p.e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hec]
  have halfSum1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have halfSum2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro T₁ T₂ h₁ h₂ Φ₀ hΦ₀ h12
    let W : Submodule ℂ (Matrix Y Y' k → ℂ) := (LinearMap.ker (T₁ - T₂)).map (SB (Matrix Y Y' k)).subtype
    have memW : ∀ Φ : SB (Matrix Y Y' k), Φ.1 ∈ W ↔ T₁ Φ = T₂ Φ := by
      intro Φ
      constructor
      · rintro ⟨Ψ, hΨ, hΨe⟩
        have : Ψ = Φ := Subtype.ext hΨe
        subst this
        simpa [sub_eq_zero] using hΨ
      · intro h
        exact ⟨Φ, by simpa [sub_eq_zero] using h, rfl⟩
    have hWle : W ≤ SB (Matrix Y Y' k) := by
      rintro _ ⟨Ψ, -, rfl⟩
      exact Ψ.2
    have hWeq := GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible k Y Y' ψk hcont hne W hWle
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ x hx
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        refine (memW ⟨_, hx⟩).2 ?_
        rw [h₁.trans x Φ ⟨_, hx⟩ (fun t => rfl), h₂.trans x Φ ⟨_, hx⟩ (fun t => rfl), hΦ'])
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ b hb
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have hmod : ∀ t, (⟨_, hb⟩ : SB (Matrix Y Y' k)).1 t = ψ (symplO S T (p.up FS FT t) y) * Φ.1 t := by
          intro t
          show _ = _
          rw [hsymk t y hy, hyb t]
          rfl
        refine (memW ⟨_, hb⟩).2 ?_
        rw [h₁.modul y hy Φ _ hmod, h₂.modul y hy Φ _ hmod, hΦ'])
      Φ₀.1 ((memW Φ₀).2 h12) (fun h => hΦ₀ (Subtype.ext h))
    ext1 Φ
    have hm : Φ.1 ∈ W := by rw [hWeq]; exact Φ.2
    exact (memW Φ).1 hm
  ·
    intro T₁ h₁ A hA1 hA2
    refine ⟨fun Φ => hA1 _ (h₁.theta Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
    · show A (T₁ Φ') = heisO ψ S T (p.up FS FT x) (A (T₁ Φ))
      rw [h₁.trans x Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum1 _ (hup x).1)]
    · show A (T₁ Φ') = heisO ψ S T y (A (T₁ Φ))
      rw [h₁.modul y hy Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum2 _ hy)]
  ·
    intro f₀ hf₀ hfx hfy
    let Z := GlobalTheory.PlaceModel.half S T (cA D p.e)
    let χ : Matrix Y Y' k → Z → ℂ := fun t z => ψ (symplO S T (p.up FS FT t) z.1)
    have hZ : ∀ z : Z, IsHalf (cA D p.e) z.1 := fun z => (GlobalTheory.PlaceModel.isHalf_iff S T).2 z.2
    obtain ⟨Tm, htr, hmo, hvac, hspan⟩ := GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices k Y Y' Z χ
      (fun a b z => by simp only [χ, upAdd, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul])
      (fun a z z' => by simp only [χ, AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
      (fun z => by simp only [χ, upZero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one])
      (fun a => by simp only [χ, ZeroMemClass.coe_zero, GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one])
      (fun n hn z => by
        obtain ⟨z', hz', e⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) n hn z.1 z.2
        exact ⟨⟨z', hz'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact e)⟩)
      (fun n hn z z' h => by
        apply Subtype.ext
        have h' : n • z.1 = n • z'.1 := by
          have := congrArg Subtype.val h
          simpa only [AddSubgroup.coe_nsmul] using this
        rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hn z.1, h', GlobalTheory.PlaceModel.inv_smul_nsmul S T hn])
      (fun x hx => GlobalTheory.T.matrix_integral_of_addChar_trace_dual k Y Y' ψk hcont hne x fun b hb => by
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have key : ∀ t, χ t ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ = ((ψk (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) := by
          intro t
          show ψ _ = _
          rw [hsymk t y hy, hyb t]
        have := hx ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ (fun u hu => by
          rw [key, hb u hu, Circle.coe_one])
        rw [key] at this
        exact Circle.ext (by simpa using this))
      (WO S T → ℂ) (fun x => GlobalTheory.PlaceModel.heisL S T ψ (p.up FS FT x)) (fun z => GlobalTheory.PlaceModel.heisL S T ψ z.1)
      (fun x x' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hce _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x).1) _
          ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x').1), upAdd])
      (fun z z' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hcce _ z.2 _ z'.2]
        rfl)
      (fun x z f => GlobalTheory.PlaceModel.heisL_comm S T ψ _ _ f)
      (fun f => by
        rw [upZero]
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      (fun f => by
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      f₀ (fun u hu => hfx u hu)
      (fun z hz => hfy z.1 (hZ z) hz)
    have hsplit := p.split
    have hstd : IsCharAF D.host.F ψ := hψ.1
    refine ⟨Tm, ⟨fun Φ => ?_, fun x Φ Φ' h => htr x Φ Φ' h, fun y hy Φ Φ' h =>
      hmo ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ Φ Φ' h⟩, hvac⟩
    have hfin {a : WO S T} (ha : a.map (infPart D) = 0) {f : WO S T → ℂ}
        (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
      simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hstd f hf
        Unit Finset.univ (fun _ => a) (fun _ => 1) (fun _ _ => ha)
    have hzero : IsThetaFunO ψ S T 0 := by
      refine ⟨?_, ?_, continuous_const, ?_⟩
      · intro γ w; simp only [Pi.zero_apply, mul_zero]
      · exact ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
      · intro k L _ _ w; exact contDiff_const
    have hadd {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
        IsThetaFunO ψ S T (f + g) := by
      refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
      · intro γ w; simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
      · obtain ⟨U, hU, h1⟩ := hf.level
        obtain ⟨U', hU', h2⟩ := hg.level
        refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu.1 h0) w
        have e2 := congrFun (h2 u hu.2 h0) w
        unfold heisO at e1 e2 ⊢
        rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
      · intro k L h1 h2 w; exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)
    have hsmul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
        IsThetaFunO ψ S T (c • f) := by
      refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
      · intro γ w; rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
      · obtain ⟨U, hU, h1⟩ := hf.level
        refine ⟨U, hU, fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu h0) w
        unfold heisO at e1 ⊢
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
      · intro k L h1 h2 w; exact contDiff_const.mul (hf.smooth k L h1 h2 w)
    have hs := hspan Φ
    generalize Tm Φ = g at hs
    induction hs using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨w, rfl⟩ := hw
      exact hfin (GlobalTheory.SplitScalar.half_fin hsplit (hup w.1).1)
        (hfin
          (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj hsplit) (hZ w.2)) hf₀)
    | zero => exact hzero
    | add _ _ _ _ h1 h2 => exact hadd h1 h2
    | smul c _ _ h1 => exact hsmul c h1

end GlobalTheory.LocModU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSchrodingerModel_uniq_transport_exists : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  first | exact @GlobalTheory.LocModU.localModel_uniq_transport_exist | exact GlobalTheory.LocModU.localModel_uniq_transport_exist | (intros; apply GlobalTheory.LocModU.localModel_uniq_transport_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

open IsDedekindDomain NumberField

namespace GlobalTheory.LocMod.LevelPlaces

open IsDedekindDomain NumberField GlobalTheory.IdemSupport

theorem splitPt_v_eq_under {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.L2.NTheta.IsIdemAt q.e P) : q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  obtain ⟨ε, hε, hsum⟩ := q.above
  have hc0 : Φ (cA D q.e) P = 0 := by
    have := ev_mul (Φ := Φ) q.e (cA D q.e) P
    rw [q.split.2.1, ev_zero, hd.2.1, one_mul] at this
    exact this.symm
  have h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0 := by
    rw [← hsum, ev_add, hd.2.1, hc0, add_zero]; exact one_ne_zero
  by_contra hne
  exact h1 ((place_comp hΦ hε).2.2 P (Ne.symm hne))

end GlobalTheory.LocMod.LevelPlaces

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombination
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

theorem rebase : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → (∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat MS ΛS → β.IsLat MT ΛT → ∀ f₀ g, Over ψ α β LS LT f₀ (latInd ΛS ΛT) g → Vac ψ S T MS MT (· = p.v) g ∧ ∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → Over ψ α β MS MT g Ψ f) ∧ ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S T α β LS MS LT MT hLS hLT hMS hMT
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β
  refine ⟨fun ΛS ΛT hΛS hΛT f₀ g hg => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨-, -, hvac0, -, ⟨Tm, hTm⟩, hall⟩ := id hg
    have hE := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n n' S T α β MS MT hMS hMT hU ΛS ΛT hΛS hΛT
    have hgT : g = Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v))) := by
      rw [← hE]; exact hall Tm hTm
    have hmono := sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e
        (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 g Tm := by
      refine ⟨fun Φ hΦ x hx => hTm.trans Φ (hmono Φ hΦ) x hx, fun Φ hΦ y hy => hTm.modul Φ (hmono Φ hΦ) y hy, ?_⟩
      rw [one_smul, hgT]
    have hth : IsThetaFunO ψ S T g := ((hOB LS LT hLS hLT f₀ hvac0).2.1 _ g hg).1
    have hvacg : Vac ψ S T MS MT (· = p.v) g := by
      refine ⟨hth, ?_⟩
      rw [hgT]
      exact latVac_image D k p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
    refine ⟨hvacg, fun Ψ f hf => ?_⟩
    obtain ⟨f', hf', -⟩ := (hOB MS MT hMS hMT g hvacg).1 Ψ hf.2.2.2.1
    have e1 : f' = Tm (extFun α β Ψ) := hf'.2.2.2.2.2 Tm hTm'
    have e2 : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    refine ⟨hMS, hMT, hvacg, hf.2.2.2.1, ⟨Tm, hTm'⟩, fun T' hT' => ?_⟩
    rw [e2, ← e1]
    exact hf'.2.2.2.2.2 T' hT'
  · obtain ⟨c, hc, hcomb⟩ := GlobalTheory.T.splitPlaceSchwartzBruhat_acts_as_supported_combination D k p n n' ψ hψ S T α β LS LT hLS hLT Ψ hΨ
    refine ⟨c, hc, fun f₀ hvac => ?_⟩
    obtain ⟨f, hf, -⟩ := (hOB LS LT hLS hLT f₀ hvac).1 Ψ hΨ
    exact ⟨hLS, hLT, hvac, hΨ, hf.2.2.2.2.1, fun T' hT' => (hcomb f₀ T' hT').symm⟩

end GlobalTheory.FinPl.Rebase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → (∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat MS ΛS → β.IsLat MT ΛT → ∀ f₀ g, Over ψ α β LS LT f₀ (latInd ΛS ΛT) g → Vac ψ S T MS MT (· = p.v) g ∧ ∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → Over ψ α β MS MT g Ψ f) ∧ ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀) := by
  first | exact @GlobalTheory.FinPl.Rebase.rebase | exact GlobalTheory.FinPl.Rebase.rebase | (intros; apply GlobalTheory.FinPl.Rebase.rebase <;> assumption)
end
end

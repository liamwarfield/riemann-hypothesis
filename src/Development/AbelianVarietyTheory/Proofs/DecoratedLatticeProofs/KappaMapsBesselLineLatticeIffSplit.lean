module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.UnitPlaces

variable {D : D7}

theorem pairA_sum {κ : Type} (s : Finset κ) (f : κ → Af D.host.F) :
    pairA D.host.F 0 (∑ i ∈ s, f i) = ∑ i ∈ s, pairA D.host.F 0 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.FinPlLoc.pairA_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.FinPlLoc.pairA_add, ih]

theorem latMul_mono (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latMul S 𝔞 L P ≤ latMul S 𝔞 L P' := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact AddSubgroup.subset_closure ⟨α, hαi, fun v hv => hα v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem latMul_le_of_parts (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (M : AddSubgroup (Fin S.rank → AE D))
    {P : Pl D → Prop} (s : Finset (Pl D)) (hs : ∀ w, P w → w ∈ s) (h : ∀ w ∈ s, latMul S 𝔞 L (· = w) ≤ M) :
    latMul S 𝔞 L P ≤ M := by
  classical
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  have hdec : α = ∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α := by
    refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u ∈ s
    · simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos hu]
    · have h0 : evalV D.host.F u α = 0 := hα u fun h' => hu (hs u h')
      simp [h0]
  have hsum : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
      ∑ w ∈ s, fun i => pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = w) * α) ⊗ₜ[D.host.F] (a * x i) := by
    funext i
    rw [Finset.sum_apply, ← TensorProduct.sum_tmul, ← pairA_sum, ← hdec]
  show _ ∈ M
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun w hw => h w hw (AddSubgroup.subset_closure
    ⟨GlobalTheory.FinPlLoc.ePl D (· = w) * α, fun u => ?_, fun u hu => ?_, a, ha, x, hx, rfl⟩)
  · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ u) (hαi u)
  · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hu, zero_mul]

theorem latA_eq_latV : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  intro D k _ _ _ _ ι p I P hP S L
  classical
  let s : Finset (Pl D) := (I.map fun i => (p i).v).toFinset
  have hs : ∀ w, P w → w ∈ s := by
    intro w hw
    obtain ⟨i, rfl⟩ := (hP.mem w).1 hw
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨i, hP.all i, rfl⟩)
  have hsi : ∀ w ∈ s, ∃ i, w = (p i).v := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
    exact ⟨i, rfl⟩
  have hsP : ∀ w ∈ s, P w := fun w hw => (hP.mem w).2 (hsi w hw)
  have hloc : ∀ w ∈ s, latA S L (· = w) = latV S L (· = w) := by
    intro w hw
    obtain ⟨i, rfl⟩ := hsi w hw
    exact (hP.unit i).2 S L
  apply le_antisymm
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).le.trans (latMul_mono S {1} L fun u (hu : u = w) => hu ▸ hsP w hw)
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).ge.trans (latMul_mono S {a | a ∈ D.host.AA} L fun u (hu : u = w) => hu ▸ hsP w hw)

end GlobalTheory.FinPl.UnitPlaces

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  first | exact @GlobalTheory.FinPl.UnitPlaces.latA_eq_latV | exact GlobalTheory.FinPl.UnitPlaces.latA_eq_latV | (intros; apply GlobalTheory.FinPl.UnitPlaces.latA_eq_latV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalves
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SplitHalves

variable {D : D7}

theorem sum_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} [DecidableEq ι] (hP : Places p I P) :
    ∑ i ∈ I.toFinset, GlobalTheory.FinPlLoc.idem D (· = (p i).v) = GlobalTheory.FinPlLoc.idem D P := by
  classical
  rw [← sub_eq_zero]
  apply GlobalTheory.FinPlLoc.eq_zero_of_comp
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.infPart_pair, Finset.sum_const_zero, sub_zero]
  · intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.compAt_idem]
    by_cases hw : P w
    · obtain ⟨j, rfl⟩ := (hP.mem w).1 hw
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (hP.inj h.symm)))
        (fun hj => absurd (List.mem_toFinset.2 (hP.all j)) hj), if_pos rfl, if_pos hw, sub_self]
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h => hw ((hP.mem w).2 ⟨i, h⟩))), if_neg hw, sub_self]

theorem mem_intAt_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  intro D k _ _ _ _ ι p I P hP a
  classical
  have hpr (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
    have he : q.pr q.e = 1 := by rw [← GlobalTheory.FinPl.FrameLat.sec_one, q.pr_sec]
    have h0 : q.e * cA D (q.sec c) = 0 := by
      rw [← cA_cA q.e, ← map_mul, ← GlobalTheory.FinPl.FrameLat.e_mul_sec q c,
        ← mul_assoc, GlobalTheory.FinPl.FrameLat.cAe_mul_e, zero_mul, map_zero]
    have h1 := congrArg q.pr h0
    rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1
  have hs (q : SplitPt D k) (a : AE D) (t : k) :
      a * q.sec t ∈ intAt D (· = q.v) ↔ q.pr a * t ∈ 𝒪[k] := by
    rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right,
      GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q (GlobalTheory.FinPl.FrameLat.sec_mem_idAt q _),
      hpr, q.pr_sec, and_iff_left (zero_mem _), mul_comm]
  have hcs (q : SplitPt D k) (a : AE D) (t : k) :
      a * cA D (q.sec t) ∈ intAt D (· = q.v) ↔ q.pr (cA D a) * t ∈ 𝒪[k] := by
    have hm : cA D (q.sec t) * a = cA D (q.sec (t * q.pr (cA D a))) := by
      rw [← GlobalTheory.FinPl.FrameLat.sec_mul_right, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA]
    rw [mul_comm, hm, GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q
      (GlobalTheory.FinPl.FrameLat.csec_mem_idAt _), hpr, GlobalTheory.SeeSaw.cA_cA, q.pr_sec,
      and_iff_right (zero_mem _), mul_comm]
  have hsec1 : ∀ i, (p i).sec 1 ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hs (p i) 1 1).2 (by simp)
  have hcsec1 : ∀ i, cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hcs (p i) 1 1).2 (by simp)
  constructor
  · intro h
    have hr := (GlobalTheory.IwaIdeals.mem_intAt_iff.1 h).2
    refine ⟨h.1, fun i => ⟨?_, ?_⟩⟩
    · have h1 : a * (p i).sec 1 ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hsec1 i)).2⟩
      simpa using (hs (p i) a 1).1 h1
    · have h1 : a * cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hcsec1 i)).2⟩
      simpa using (hcs (p i) a 1).1 h1
  · rintro ⟨hid, hh⟩
    refine ⟨hid, ?_⟩
    have ha : a = ∑ i ∈ I.toFinset, (a * (p i).sec 1 + a * cA D ((p i).sec 1)) := by
      conv_lhs => rw [← (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 hid, ← sum_idem hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      set ε := GlobalTheory.FinPlLoc.idem D (· = (p i).v)
      have h1 : ε * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
      have h2 := (GlobalTheory.FinPl.FrameLat.idem_iff (p i) _).1 h1
      have he : ε * (p i).sec 1 = (p i).sec 1 :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _)
      have hce : ε * cA D ((p i).sec 1) = cA D ((p i).sec 1) :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1)
      rw [GlobalTheory.FinPl.FrameLat.sec_one] at he hce ⊢
      calc ε * a = ((p i).e + cA D (p i).e) * (ε * a) := h2.symm
        _ = (ε * (p i).e) * a + (ε * cA D (p i).e) * a := by
          rw [add_mul, mul_left_comm, ← mul_assoc, mul_left_comm (cA D (p i).e), ← mul_assoc]
        _ = a * (p i).e + a * cA D (p i).e := by rw [he, hce, mul_comm (p i).e, mul_comm (cA D (p i).e)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_add (f := _)]
    exact add_mem ((hs (p i) a 1).2 (by simpa using (hh i).1)).2
      ((hcs (p i) a 1).2 (by simpa using (hh i).2)).2

end GlobalTheory.FinPl.SplitHalves

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalvesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves | exact GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves | (intros; apply GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 400000

namespace GlobalTheory.FinPl.ScalarDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl.FrameLat

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w =>
    (Submodule.mem_iInf _).1 hw ⟨w.1, fun hp => w.2 (hPQ _ hp)⟩⟩

theorem pr_eq_zero (q : SplitPt D k) {w : Pl D} (hw : w ≠ q.v) {a : AE D} (ha : a ∈ idAt D (· = w)) : q.pr a = 0 := by
  have h1 : q.e * a ∈ idAt D (· = w) := Ideal.mul_mem_left _ _ ha
  have h2 : q.e * a ∈ idAt D (· = q.v) := Ideal.mul_mem_right _ _ (e_mem_idAt q)
  unfold idAt at h1 h2
  have h0 : q.e * a = 0 := by
    apply GlobalTheory.FinPlLoc.eq_zero_of_comp
    · exact RingHom.mem_ker.1 (Ideal.mem_inf.1 h1).1
    · intro u
      by_cases hu : u = w
      · subst hu
        exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h2).2 ⟨u, hw⟩)
      · exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h1).2 ⟨u, hu⟩)
  rw [← q.pr_sec (q.pr a), q.sec_pr, h0, map_zero]

theorem pr_cA_xi_int (q : SplitPt D k) (hU : q.UnitAA) :
    q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] ∧ q.pr (cA D (incA D D.host.xi0⁻¹)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [GlobalTheory.SplitLineSim.pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := hU.1 _ hc
  have a1 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1.1).1 h2.1).2
  have a2 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.2.1).1 h2.2).2
  rw [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at a1 a2
  exact ⟨a1, a2⟩

theorem cond_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP h h' hh hh' hs hhe d hd
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hv : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  have hne_v : ∀ i j, i ≠ j → (p i).v ≠ (p j).v := fun i j hij e => hij (hP.inj e)
  have hU := fun i => pr_cA_xi_int (p i) (hP.unit i)
  have hprod : ∀ i, (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr (cA D (incA D D.host.xi0)) = 1 := by
    intro i
    rw [← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one, map_one]
  have hch : cA D (incA D h) = incA D h := by
    rw [cA_incA, hhe, star_mul, star_mul, star_star, hs]
    ring_nf
  have hx1 : incA D D.host.xi0⁻¹ * incA D h = cA D (incA D D.host.xi0) * incA D h' := by
    rw [cA_incA, ← map_mul, ← map_mul, hhe, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hX : ∀ c, incA D D.host.xi0⁻¹ * cA D d * c * incA D h =
      cA D (incA D D.host.xi0) * (cA D d * incA D h') * c := fun c => by
    linear_combination (cA D d * c) * hx1
  have hcX : ∀ c, cA D (incA D D.host.xi0⁻¹ * cA D d * c * incA D h) =
      cA D (incA D D.host.xi0⁻¹) * d * (cA D c * incA D h) := fun c => by
    simp only [map_mul, Formalism.L2.Theta.cA_cA, hch]
    ring
  constructor
  · intro hdc c hc hcc
    refine (GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).2 ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc), fun i => ⟨?_, ?_⟩⟩
    · rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).1 (hdc i).2) (hcc i).1
    · rw [hcX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).2 (hdc i).1) (hcc i).2
  · intro H i
    have hsup : ∀ {a : AE D}, a ∈ idAt D (· = (p i).v) → a ∈ idAt D P :=
      fun ha => idAt_mono (fun w hw => by rw [hw]; exact hv i) ha

    have hcond1 : ∀ j, (p j).pr ((p i).sec 1) ∈ 𝒪[k] ∧
        (p j).pr (cA D ((p i).sec 1)) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      by_cases hij : j = i
      · subst hij
        rw [(p j).pr_sec, GlobalTheory.SplitLineSim.pr_cA_sec, zero_mul]
        exact ⟨one_mem _, zero_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) 1),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) 1), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h1 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (sec_mem_idAt (p i) 1)) hcond1)).2 i).1
    rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr, (p i).pr_sec, mul_one] at h1

    have hh0 : (p i).pr (incA D h) ≠ 0 := by
      intro h0
      have := congrArg (p i).pr (congrArg (incA D) (mul_inv_cancel₀ hh))
      rw [map_mul (incA D), map_mul (p i).pr, h0, zero_mul, map_one, map_one] at this
      exact zero_ne_one this
    have hcond2 : ∀ j, (p j).pr (cA D ((p i).sec ((p i).pr (incA D h))⁻¹)) ∈ 𝒪[k] ∧
        (p j).pr (cA D (cA D ((p i).sec ((p i).pr (incA D h))⁻¹))) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      rw [Formalism.L2.Theta.cA_cA]
      by_cases hij : j = i
      · subst hij
        rw [GlobalTheory.SplitLineSim.pr_cA_sec, (p j).pr_sec, inv_mul_cancel₀ hh0]
        exact ⟨zero_mem _, one_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) ((p i).pr (incA D h))⁻¹),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h2 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹)) hcond2)).2 i).2
    rw [hcX, Formalism.L2.Theta.cA_cA] at h2
    have e3 : (p i).pr (cA D (incA D D.host.xi0⁻¹) * d * ((p i).sec ((p i).pr (incA D h))⁻¹ * incA D h)) =
        (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d := by
      simp only [map_mul, (p i).pr_sec]
      rw [inv_mul_cancel₀ hh0, mul_one]
    rw [e3] at h2
    refine ⟨?_, ?_⟩
    · have e2 : (p i).pr d = (p i).pr (cA D (incA D D.host.xi0)) *
          ((p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d) := by
        linear_combination (-(p i).pr d) * hprod i
      rw [e2]; exact mul_mem (hU i).1 h2
    · have e1 : (p i).pr (cA D d) * (p i).pr (incA D h') = (p i).pr (cA D (incA D D.host.xi0⁻¹)) *
          ((p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D d) * (p i).pr (incA D h'))) := by
        linear_combination (-((p i).pr (cA D d) * (p i).pr (incA D h'))) * hprod i
      rw [e1]; exact mul_mem (hU i).2 h1

end GlobalTheory.FinPl.ScalarDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_lineConditions_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  first | exact @GlobalTheory.FinPl.ScalarDual.cond_dual | exact GlobalTheory.FinPl.ScalarDual.cond_dual | (intros; apply GlobalTheory.FinPl.ScalarDual.cond_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMemLineLatticeCompletionIffScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineProj

variable {D : D7}

theorem latV_le_of {S : HSp D} (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    GlobalTheory.FinPl.latV S L P ≤ GlobalTheory.FinPl.latV S L P' := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, hα, hP, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun v hv => hP v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem row_iA {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    star (vecB o ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0 := by
  show star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, o.orth,
    Matrix.vecMul_zero]

theorem row_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  show (star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ (o.iB *ᵥ ζ) = _
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem star_self {L : HSp D} (ζ : Fin L.rank → D.host.E) :
    star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, gram_conjTranspose, ← Matrix.dotProduct_mulVec]

theorem sum_incA_mulVec {s t : ℕ} (ρ : Fin s → D.host.E) (N : Matrix (Fin s) (Fin t) D.host.E) (u : Fin t → AE D) :
    ∑ j, incA D (ρ j) * (rat N *ᵥ u) j = ∑ a, incA D ((ρ ᵥ* N) a) * u a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {q : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} {o : OrthDec S₀ A L} {ζ : Fin L.rank → D.host.E}
  {α : Frame q A n} {α₀ : Frame q S₀ (n ⊕ Fin 1)} {M : Lat S₀} {Λ : Submodule 𝒪[k] (n → k)}

theorem e_vecB_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) :
    (fun r => q.e * incA D (vecB o ζ r)) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  let y0 : n ⊕ Fin 1 → k := Sum.elim 0 (fun _ => 1)
  have hb0 : α₀.b *ᵥ y0 = fun r => q.pr (incA D (vecB o ζ r)) := by
    rw [hsum, Matrix.fromCols_mulVec]
    funext r
    have h1 : y0 ∘ Sum.inl = 0 := Sum.elim_comp_inl _ _
    rw [Pi.add_apply, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y0,
      Sum.elim_inr, mul_one]
    rfl
  have hy0 : y0 ∈ lastKer Λ := by
    refine GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨?_, ?_⟩
    · show (Sum.elim 0 (fun _ => 1) : n ⊕ Fin 1 → k) ∘ Sum.inl ∈ Λ
      rw [Sum.elim_comp_inl]; exact zero_mem _
    · exact one_mem _
  have h := (hlat y0).1 hy0
  rw [hb0] at h
  simpa only [q.sec_pr] using h

theorem pr_coeff_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) {m : Fin S₀.rank → AE D} {c : AE D}
    (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r))
    (hem : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v)) : q.pr c ∈ 𝒪[k] := by
  let pu : Fin A.rank → k := fun a => q.pr ((o.pA *ᵥ m) a)
  let y : n ⊕ Fin 1 → k := Sum.elim (α.b' *ᵥ pu) (fun _ => q.pr c)
  have hbx : α₀.b *ᵥ y = fun r => q.pr (m r) := by
    rw [hsum, Matrix.fromCols_mulVec]
    have h1 : (o.jA.map q.pr * α.b) *ᵥ (y ∘ Sum.inl) = o.jA.map q.pr *ᵥ pu := by
      show (o.jA.map q.pr * α.b) *ᵥ (α.b' *ᵥ pu) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one]
    rw [h1]
    funext r
    rw [hmdec r, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y,
      Sum.elim_inr]
    exact mul_comm _ _
  have hy : y ∈ lastKer Λ := by
    refine (hlat y).2 ?_
    rw [hbx]
    simpa only [q.sec_pr] using hem
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).2

theorem pr_cA_mem {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : q.pr (cA D a) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) ((FrameLat.cA_int_iff a).2 ha.2)

theorem e_mul_mem (hM : IsSelfDualC S₀ M) {P : Pl D → Prop} {m : Fin S₀.rank → AE D}
    (hm : m ∈ GlobalTheory.FinPl.latV S₀ M P) : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  refine FrameLat.mem_of_pairing hM (fun r => Ideal.mul_mem_right _ _ (FrameLat.e_mem_idAt q)) fun s hs => ?_
  have h : FrameLat.pairing S₀ s (fun r => q.e * m r) = q.e * FrameLat.pairing S₀ s m := by
    simp only [FrameLat.pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) (FrameLat.pairing_int hM hs hm)

end Local

theorem pairing_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (e c : AE D)
    {m : Fin S₀.rank → AE D} (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r)) :
    (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * (c * incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ)) := by
  have h1 : (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * ∑ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.map_mul, FrameLat.cA_incA, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply]; ring
  rw [h1]
  congr 1
  have h2 : ∀ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b =
      incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * (o.jA *ᵥ (o.pA *ᵥ m)) b +
        c * (incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * incA D (vecB o ζ b)) := fun b => by
    rw [hmdec b]; ring
  simp only [h2, Finset.sum_add_distrib]
  rw [OrthDec.jA, sum_incA_mulVec, row_iA]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← RingHom.map_mul,
    ← map_sum]
  rfl

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj


set_option maxHeartbeats 1000000 in
theorem lineProj_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr m hm
  have hr : L.rank = 1 := hζ.1
  let i0 : Fin L.rank := ⟨0, by omega⟩
  have hsub : ∀ j : Fin L.rank, j = i0 := fun j => Fin.ext (by have := j.2; simp only [i0]; omega)
  have hz0 : ζ i0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [hsub j, h0]; rfl
    rw [this]; simp
  have hmid : ∀ r, m r ∈ idAt D P := FrameLat.latV_supp hm
  set c : AE D := (o.pB *ᵥ m) i0 * incA D (ζ i0)⁻¹ with hc
  have hcid : c ∈ idAt D P := by
    refine Ideal.mul_mem_right _ _ ?_
    show (∑ j, o.pB i0 j * m j) ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmid j)
  have hpB : o.pB *ᵥ m = fun j => c * incA D (ζ j) := by
    funext j
    rw [hsub j, hc, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hz0, RingHom.map_one, mul_one]
  have hjB : o.jB *ᵥ (o.pB *ᵥ m) = fun r => c * incA D (vecB o ζ r) := by
    rw [hpB]; funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, vecB, map_sum, RingHom.map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r) := by
    intro r
    have h : m = o.jA *ᵥ (o.pA *ᵥ m) + o.jB *ᵥ (o.pB *ᵥ m) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        rw [OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, rat, rat, rat,
          ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
          o.iA_qA_add, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
    conv_lhs => rw [h]
    rw [Pi.add_apply, hjB]
  rw [hjB]
  refine (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n S₀ A L o ζ hζ α α₀ M Λ hM hfr c hcid).2 fun i => ?_
  obtain ⟨hsum, hlat⟩ := hfr i
  have hvP : P (p i).v := (hP.mem _).2 ⟨i, rfl⟩
  have hpre : (p i).pr (p i).e = 1 := by rw [← FrameLat.sec_one, (p i).pr_sec]
  refine ⟨pr_coeff_mem hsum hlat hmdec (e_mul_mem hM hm), ?_⟩
  have hzP := latV_le_of M (P := (· = (p i).v)) (P' := P) (fun w hw => by rw [hw]; exact hvP) (e_vecB_mem hsum hlat)
  have hH := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S₀ M hM P m hmid).1 hm _ hzP
  have h := pr_cA_mem (q := p i) hH
  rw [pairing_eq o ζ (p i).e c hmdec, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, Formalism.L2.Theta.cA_cA, hpre, one_mul,
    FrameLat.cA_incA, row_vecB, star_self, RingHom.map_mul] at h
  exact h

end GlobalTheory.LineProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineProjection_mem_splitCoreCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  first | exact @GlobalTheory.LineProj.lineProj_mem | exact GlobalTheory.LineProj.lineProj_mem | (intros; apply GlobalTheory.LineProj.lineProj_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MxAtEmbedKappa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KapLatSupp

theorem mxAt_embed_kappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S T A : HSp D) (o : OrthDec T A L') (P : Pl D → Prop) (x : WO S L'), MxAt P x → MxAt P ((B.o.resS S).symm (0, l.κ S x)) ∧ MxAt P ((o.resT S).symm (0, x)) := by
  intro D ρ B L' ζ' l S T A o P x hx
  refine ⟨?_, ?_⟩
  · rw [OrthDec.resS_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_r GlobalTheory.LastOpPf.mxAt_zero _)
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LinkKapMx.mxAt_linkKappa D ρ B L' ζ' l S P x hx) _)
  · rw [OrthDec.resT_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_l _ GlobalTheory.LastOpPf.mxAt_zero) (GlobalTheory.LastOpPf.mxAt_mul_l _ hx)

end GlobalTheory.KapLatSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaAdjointTauFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaAdjointTauFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem doubleSum_eq_dotProduct_mapMatrix_mulVec {R K : Type*} [CommRing R] {m n : ℕ} (g : R → R) (f : K → R)
    (s : Fin m → R) (G : Matrix (Fin m) (Fin n) K) (v : Fin n → R) :
    (∑ i, ∑ j, g (s i) * f (G i j) * v j) = (fun i => g (s i)) ⬝ᵥ (G.map f *ᵥ v) := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem ringHom_conjTranspose_smul_dotProduct_adjoint {R : Type*} [CommRing R] {m n : ℕ} (σ : R →+* R) (c : R)
    (s : Fin m → R) (Y : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (a : Fin n → R) :
    (fun i => σ (s i)) ⬝ᵥ ((c • ((Y.map σ)ᵀ * G)) *ᵥ a)
      = c * ((fun k => σ ((Y *ᵥ s) k)) ⬝ᵥ (G *ᵥ a)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 2
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMul, mulVec, dotProduct, map_sum, map_mul, mul_comm]


set_option maxHeartbeats 2000000 in
theorem kappa_adj : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  intro D ρ B L' ζ' l S x a s
  simp only [Link.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  have hG : gA S * giA S = 1 := by
    have h := Matrix.mul_nonsing_inv (HSpace.gram S) (gram_isUnit_det S)
    have h2 : (HSpace.gram S * (HSpace.gram S)⁻¹).map (incA D)
        = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) := by rw [h]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  rw [doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D) s, doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D)]
  rw [show (HSpace.gram S).map (incA D) = gA S from rfl,
    show (HSpace.gram B.L).map (incA D) = gA B.L from rfl]
  have hG' : ∀ N : Mx D S.rank B.L.rank, HMul.hMul (gA S) (HMul.hMul (giA S) N) = N := by
    intro N
    rw [← Matrix.mul_assoc, hG]
    exact Matrix.one_mul N
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, hG']
  exact ringHom_conjTranspose_smul_dotProduct_adjoint (cA D) _ s _ _ a

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaAdjointTauFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLinkKappa_adjoint_tau_factor : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  first | exact @GlobalTheory.kappa_adj | exact GlobalTheory.kappa_adj | (intros; apply GlobalTheory.kappa_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMemLineLatticeCompletionIffScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.KappaLeft

theorem latV_mem_idAt {D : D7} {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : ∀ r, y r ∈ idAt D P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, rfl⟩ := hw
    intro r
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => intro r; exact zero_mem _
  | add x y _ _ hx hy => intro r; exact add_mem (hx r) (hy r)
  | neg x _ hx => intro r; exact neg_mem (hx r)

end GlobalTheory.Corev.KappaLeft


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Corev.kappa_mem_latO_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ σ B B' l S α α₀ M LS Λ hM hLS hα x hx
  have hcA : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  have hMx : MxAt P ((B.o.resS S).symm (0, l.κ S x)) :=
    (GlobalTheory.KapLatSupp.mxAt_embed_kappa D ρ B B'.L B'.ζ l S B'.V₀ B'.A B'.o P x hx).1
  have hu : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]

  have hline : ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ v : Fin L.rank → AE D,
      (∀ r, v r ∈ idAt D P) → ∃ c : AE D, c ∈ idAt D P ∧ v = c • ratV ζ := by
    intro L ζ hL v hv
    obtain ⟨hrk, hne⟩ := hL
    have hr : ∀ r r' : Fin L.rank, r = r' := fun r r' => Fin.ext (by omega)
    let r₀ : Fin L.rank := ⟨0, by omega⟩
    have hζ : ζ r₀ ≠ 0 := by
      intro h0
      apply hne
      have : ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero]
    refine ⟨v r₀ * incA D (ζ r₀)⁻¹, Ideal.mul_mem_right _ _ (hv r₀), ?_⟩
    funext r
    rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
  have hjB : ∀ c : AE D, B.o.jB *ᵥ (c • ratV B.ζ) = fun r => c * incA D (vecB B.o B.ζ r) := by
    intro c
    funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpj : ∀ c : AE D, B.o.pB *ᵥ (B.o.jB *ᵥ (c • ratV B.ζ)) = c • ratV B.ζ := by
    intro c
    rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]

  have hsupp : ∀ m : Fin B.V₀.rank → AE D, ∀ r, (((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m) r ∈ idAt D P := by
    intro m r
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hMx r j)

  have hpair : ∀ (y : Fin S.rank → AE D) (d c : AE D), (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ →
      (∑ i, ∑ j, cA D (y i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ)) j) =
        incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) := by
    intro y d c hxy
    rw [GlobalTheory.T.besselLinkKappa_adjoint_tau_factor D ρ B B'.L B'.ζ l S x (c • ratV B.ζ) y]
    have h1 : ((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ y = d • ratV (-B.ζ) := by
      rw [← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_smul, ← l.map]
      congr 1
      ext i
      simp [rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1]
    have hh : incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) =
        ∑ i, ∑ j, incA D (star (B.ζ i)) * incA D (HSpace.gram B.L i j) * incA D (B.ζ j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum, mul_assoc]
    rw [hh, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ratV, Pi.neg_apply, map_mul, map_neg, hcA, star_neg]
    ring
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP S LS]
  constructor
  · rintro ⟨-, h⟩ y hy
    have hz : ∀ r, ((x : Matrix _ _ (AE D)) *ᵥ y) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r j)
    obtain ⟨d, hdI, hxd⟩ := hline B'.L B'.ζ B'.line _ hz
    refine ⟨d, hdI, hxd, fun c hc hl => ?_⟩
    have hm : (fun r => c * incA D (vecB B.o B.ζ r)) ∈ latV B.V₀ M P :=
      (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).2 hl
    have h1 := h _ hm
    have hI := hsupp (fun r => c * incA D (vecB B.o B.ζ r))
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ (fun r => c * incA D (vecB B.o B.ζ r)) =
        (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← hjB, ← Matrix.mulVec_mulVec, hpj]
    rw [heq] at h1 hI
    have h2 := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).1 h1 y hy
    rwa [hpair y d c hxd] at h2
  · intro h
    refine ⟨hMx, fun m hm => ?_⟩
    have hv : ∀ r, (B.o.pB *ᵥ m) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (GlobalTheory.Corev.KappaLeft.latV_mem_idAt hm j)
    obtain ⟨c, hc, hcv⟩ := hline B.L B.ζ B.line _ hv
    have hjp := GlobalTheory.T.lineProjection_mem_splitCoreCompletion D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα m hm
    rw [hcv, hjB] at hjp
    have hl := (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).1 hjp
    have hI := hsupp m
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m = (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← Matrix.mulVec_mulVec, hcv]
    rw [heq] at hI ⊢
    refine (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).2 fun s hs => ?_
    obtain ⟨d, -, hxd, hd⟩ := h s hs
    rw [hpair s d c hxd]
    exact hd c hc hl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMemLineLatticeCompletionIffScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_mem_lineLatticeCompletion_iff_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  first | exact @GlobalTheory.Corev.kappa_mem_latO_iff | exact GlobalTheory.Corev.kappa_mem_latO_iff | (intros; apply GlobalTheory.Corev.kappa_mem_latO_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Corev.mem_latO_line_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  intro D k _ _ _ _ ι p I P hP n'' _ _ σ B' γ γ₀ M' Λ' hM' hγ S LS hLS x hx
  have hu : (B'.o.resT S).symm (0, x) = B'.o.jB ⬝ x := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  have hMx : MxAt P (B'.o.jB ⬝ x) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)
  obtain ⟨hrk, hne⟩ := B'.line
  have hr : ∀ r r' : Fin B'.L.rank, r = r' := fun r r' => Fin.ext (by omega)
  let r₀ : Fin B'.L.rank := ⟨0, by omega⟩
  have hζ : B'.ζ r₀ ≠ 0 := by
    intro h0
    apply hne
    have : B'.ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
    rw [this, Matrix.mulVec_zero, dotProduct_zero]
  have hjB : ∀ d : AE D, B'.o.jB *ᵥ (d • ratV B'.ζ) = fun r => d * incA D (vecB B'.o B'.ζ r) := by
    intro d
    funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ y, (B'.o.jB ⬝ x) *ᵥ y ∈ latV B'.V₀ M' P ↔ ∃ d : AE D, d ∈ idAt D P ∧
      (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧
        (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k]) := by
    intro y
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have hz : ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ ∈ idAt D P := by
        simp only [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r₀ j)
      set d : AE D := ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ * incA D (B'.ζ r₀)⁻¹ with hd
      have hdI : d ∈ idAt D P := Ideal.mul_mem_right _ _ hz
      have hzd : (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ := by
        funext r
        rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, hd, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
      rw [hzd, hjB] at h
      exact ⟨d, hdI, hzd, (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).1 h⟩
    · rintro ⟨d, hdI, hzd, hc⟩
      rw [hzd, hjB]
      exact (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).2 hc
  rw [hu, GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S B'.V₀ LS M' hLS hM' P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP B'.V₀ M']
  constructor
  · rintro ⟨-, h⟩ y hy
    exact (key y).1 (h y hy)
  · intro h
    exact ⟨hMx, fun y hy => (key y).2 (h y hy)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  first | exact @GlobalTheory.Corev.mem_latO_line_iff | exact GlobalTheory.Corev.mem_latO_line_iff | (intros; apply GlobalTheory.Corev.mem_latO_line_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMapsBesselLineLatticeIffSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaLat

theorem star_self_pair : ∀ (D : D7) (L : HSp D) (ζ : Fin L.rank → D.host.E), star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  intro D L ζ
  have hG := GlobalTheory.MixModel.gram_conjTranspose L
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hG, Matrix.dotProduct_mulVec]

theorem kappa_line_lat_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x hx
  rw [GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar D k ι p I P hP n'' σ B' γ γ₀ M' Λ' hM' (fun i => ⟨(hfr i).2.1, (hfr i).2.2.2⟩) S LS hLS x hx,
    GlobalTheory.T.kappa_mem_lineLatticeCompletion_iff_scalar D k ι p I P hP n' ρ σ B B' l S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) x hx]
  have h1 : (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ≠ 0 := B.line.2
  have h2 : (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ) ≠ 0 := B'.line.2
  have h3 := star_self_pair D B'.L B'.ζ
  have h4 : (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) = D.host.xi0 * star D.host.xi0 * (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ) := l.norm
  exact forall₂_congr fun y _ => exists_congr fun d => and_congr_right fun hd => and_congr_right fun _ =>
    GlobalTheory.T.splitPlace_lineConditions_dual D k ι p I P hP _ _ h1 h2 h3 h4 d hd

end GlobalTheory.KappaLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMapsBesselLineLatticeIffSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_maps_besselLineLattice_iff_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  first | exact @GlobalTheory.KappaLat.kappa_line_lat_iff | exact GlobalTheory.KappaLat.kappa_line_lat_iff | (intros; apply GlobalTheory.KappaLat.kappa_line_lat_iff <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.KapLat

open GlobalTheory.FinPl

variable {D : D7}

def pairH (L : HSp D) (z y : Fin L.rank → AE D) : AE D := (fun a => cA D (z a)) ⬝ᵥ (gA L *ᵥ y)

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem tmul_eq (γ : Af D.host.F) (e : D.host.E) :
    pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 * e) = (pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D e := by
  rw [incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem cA_tmul_one (a : AF D.host.F) : cA D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have := GlobalTheory.SelfDualAt.cA_alg (D := D) a
  simpa [Algebra.TensorProduct.algebraMap_apply] using this

theorem pairH_add_left (L : HSp D) (z z' y : Fin L.rank → AE D) : pairH L (z + z') y = pairH L z y + pairH L z' y := by
  simp only [pairH, dotProduct, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem pairH_neg_left (L : HSp D) (z y : Fin L.rank → AE D) : pairH L (-z) y = -pairH L z y := by
  simp only [pairH, dotProduct, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem pairH_zero_left (L : HSp D) (y : Fin L.rank → AE D) : pairH L 0 y = 0 := by
  simp only [pairH, dotProduct, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem pairH_add_right (L : HSp D) (z y y' : Fin L.rank → AE D) : pairH L z (y + y') = pairH L z y + pairH L z y' := by
  simp only [pairH, Matrix.mulVec_add, dotProduct_add]

theorem pairH_neg_right (L : HSp D) (z y : Fin L.rank → AE D) : pairH L z (-y) = -pairH L z y := by
  simp only [pairH, Matrix.mulVec_neg, dotProduct_neg]

theorem pairH_zero_right (L : HSp D) (z : Fin L.rank → AE D) : pairH L z 0 = 0 := by
  simp only [pairH, Matrix.mulVec_zero, dotProduct_zero]

theorem pairH_gen (L : HSp D) (α β : Af D.host.F) (x x' : Fin L.rank → D.host.E) :
    pairH L (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (1 * ∑ i, ∑ j, star (x i) * L.gram i j * x' j) := by
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tmul_eq, pairH, dotProduct, Matrix.mulVec, gA, rat, Matrix.map_apply, map_mul, cA_tmul_one,
    GlobalTheory.DualPairCheck.cA_incA, map_sum]
  rw [← hp, ← one_mul (1 : D.host.E), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem pairH_int {L : HSp D} {LL : Lat L} (hL : IsSelfDualC L LL) {P : Pl D → Prop} {z y : Fin L.rank → AE D}
    (hz : z ∈ latV L LL P) (hy : y ∈ latV L LL P) : finPart D (pairH L z y) ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, -, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβi, -, c', hc', x', hx', rfl⟩ := hy
      rw [Set.mem_singleton_iff] at hc'
      subst hc'
      obtain ⟨b, hb⟩ := (hL.2 x').1 hx' x hx
      rw [pairH_gen, ← hb, GlobalTheory.LatVac.finPart_tmul, one_mul]
      exact AddSubgroup.subset_closure ⟨α * β, GlobalTheory.FinPl.LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pairH_zero_right]; exact zero_mem _
    | add y y' _ _ h h' => rw [pairH_add_right, RingHom.map_add (f := _)]; exact add_mem h h'
    | neg y _ h => rw [pairH_neg_right, RingHom.map_neg]; exact neg_mem h
  | zero => rw [pairH_zero_left]; exact zero_mem _
  | add z z' _ _ h h' => rw [pairH_add_left, RingHom.map_add (f := _)]; exact add_mem h h'
  | neg z _ h => rw [pairH_neg_left, RingHom.map_neg]; exact neg_mem h

end GlobalTheory.KapLat

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.KapLat2

open GlobalTheory.FinPl GlobalTheory.KapLat

variable {D : D7}

theorem pairH_eq (S : HSp D) (t : Fin S.rank → D.host.E) (x : Fin S.rank → AE D) :
    pairH S (fun l => incA D (t l)) x = ∑ b, (∑ k, incA D (star (t k)) * gA S k b) * x b := by
  unfold pairH
  rw [Matrix.dotProduct_mulVec]
  simp only [dotProduct, Matrix.vecMul, GlobalTheory.DualPairCheck.cA_incA]

theorem smul_mulVec' {m n : ℕ} (c : AE D) (M : Mx D m n) (v : Fin n → AE D) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]


set_option maxHeartbeats 800000 in
theorem mem_latV_of_pairH {S : HSp D} {MS : Lat S} (hS : IsSelfDualC S MS) {P : Pl D → Prop}
    {x : Fin S.rank → AE D} (hx : ∀ b, x b ∈ idAt D P)
    (hint : ∀ t ∈ MS, finPart D (pairH S (fun a => incA D (t a)) x) ∈ intAE D) : x ∈ latV S MS P := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  have hyv : ∀ i, (fun l => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)) ∈
      latV S MS P := fun i =>
    AddSubgroup.subset_closure ⟨GlobalTheory.FinPl.LatMem.indP D.host.F P, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _,
      GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hdualA : ∀ a b, ∑ i, incA D (s i a) * ∑ k, incA D (star (s' i k)) * gA S k b = incA D (if a = b then 1 else 0) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hdual a b, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, gA, rat, Matrix.map_apply]
  have h2 : ∀ a, ∑ i, incA D (s i a) * ∑ b, (∑ k, incA D (star (s' i k)) * gA S k b) * x b = x a := by
    intro a
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ b, ∑ i, incA D (s i a) * ((∑ k, incA D (star (s' i k)) * gA S k b) * x b) =
        incA D (if a = b then 1 else 0) * x b := by
      intro b
      rw [← hdualA a b, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [h3]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, map_one, one_mul]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have key : x = ∑ i, fun a => pairH S (fun l => incA D (s' i l)) x *
      pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i a) := by
    funext a
    rw [Finset.sum_apply]
    have h1 : ∀ i, pairH S (fun l => incA D (s' i l)) x *
        pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i a) =
        (incA D (s i a) * ∑ b, (∑ k, incA D (star (s' i k)) * gA S k b) * x b) *
          (pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      intro i
      rw [tmul_eq, pairH_eq]
      ring
    simp only [h1]
    rw [← Finset.sum_mul, h2 a]
    exact (GlobalTheory.FinPl.LatMem.mul_indP (hx a)).symm
  rw [key]
  exact sum_mem fun i _ => GlobalTheory.FinPl.LatIndHalf.mul_mem_latV (hint _ (hs' i)) (hyv i)

theorem pairH_kap (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'')
    (t : Fin S.rank → D.host.E) (y : Fin L.rank → AE D) :
    pairH S (fun a => incA D (t a)) (GlobalTheory.FinPl.kap τ S w *ᵥ y) =
      incA D (-D.host.xi0⁻¹) * pairH L ((rat τ : Mx D L.rank L''.rank) *ᵥ (w *ᵥ fun a => incA D (t a))) y := by
  unfold pairH GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec', dotProduct_smul, smul_eq_mul]
  congr 1
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  funext a
  rw [Matrix.mulVec_mulVec, RingHom.map_mulVec, adj, Matrix.vecMul_transpose]
  rfl

end GlobalTheory.KapLat2

namespace GlobalTheory.KapLat2

open GlobalTheory.FinPl GlobalTheory.KapLat


set_option maxHeartbeats 800000 in
theorem kap_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (MS : GlobalTheory.FinPl.Lat S) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L''), q.UnitAA → IsSelfDualC S MS → IsSelfDualC L LL → IsSelfDualC L'' LZ → (∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → ∀ w ∈ latO S L'' (MS : Set _) (LZ : Set _) (· = q.v), GlobalTheory.FinPl.kap τ S w ∈ latO L S (LL : Set _) (MS : Set _) (· = q.v) := by
  intro D k _ _ _ _ q S L L'' τ MS LL LZ hU hS hL hZ hτ w hw
  have hwP : MxAt (· = q.v) w := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  have huP : MxAt (· = q.v) (GlobalTheory.FinPl.kap τ S w) := GlobalTheory.LastOpPf.mxAt_kap τ S hwP
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D L S LL MS hL hS]
  refine ⟨huP, fun y hy => ?_⟩
  rw [hU.2 S MS]
  have hyP : ∀ b, y b ∈ idAt D (· = q.v) := GlobalTheory.ContrComb.LatT.latV_entry_mem hy
  refine mem_latV_of_pairH hS (fun b => ?_) (fun t ht => ?_)
  · show (GlobalTheory.FinPl.kap τ S w *ᵥ y) b ∈ _
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (huP b j)
  · show finPart D (pairH S (fun a => incA D (t a)) (GlobalTheory.FinPl.kap τ S w *ᵥ y)) ∈ intAE D
    rw [pairH_kap]

    let yv : Fin S.rank → AE D := fun l =>
      pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = q.v)) ⊗ₜ[D.host.F] (1 * t l)
    have hyv : yv ∈ latV S MS (· = q.v) :=
      AddSubgroup.subset_closure ⟨GlobalTheory.FinPl.LatMem.indP D.host.F (· = q.v), GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _,
        GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
    have hwt : (w *ᵥ fun a => incA D (t a)) = w *ᵥ yv := by
      funext j
      simp only [Matrix.mulVec, dotProduct, yv, tmul_eq]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, GlobalTheory.FinPl.LatMem.mul_indP (hwP j l)]
    have hz : (rat τ : Mx D L.rank L''.rank) *ᵥ (w *ᵥ fun a => incA D (t a)) ∈ latV L LL (· = q.v) := by
      rw [hwt]
      refine hτ _ ?_
      rw [← hU.2 L'' LZ]
      exact GlobalTheory.FinPl.LatMem.latO_maps hS hw hyv
    have hint := pairH_int hL hz hy
    have hid : pairH L ((rat τ : Mx D L.rank L''.rank) *ᵥ (w *ᵥ fun a => incA D (t a))) y ∈ idAt D (· = q.v) := by
      simp only [pairH, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hyP b))
    have h3 := (hU.1 _ ⟨hid, hint⟩).2.2
    rw [map_neg, neg_mul, map_neg]
    exact neg_mem h3

end GlobalTheory.KapLat2
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineHomAdjointTwist_mem_completedHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (MS : GlobalTheory.FinPl.Lat S) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L''), q.UnitAA → IsSelfDualC S MS → IsSelfDualC L LL → IsSelfDualC L'' LZ → (∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → ∀ w ∈ latO S L'' (MS : Set _) (LZ : Set _) (· = q.v), GlobalTheory.FinPl.kap τ S w ∈ latO L S (LL : Set _) (MS : Set _) (· = q.v) := by
  first | exact @GlobalTheory.KapLat2.kap_mem_latO | exact GlobalTheory.KapLat2.kap_mem_latO | (intros; apply GlobalTheory.KapLat2.kap_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplit

theorem mem_latV_iff_wParts {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = p.v)) :
    y ∈ GlobalTheory.FinPl.latV S L (· = p.v) ↔ (fun i => p.sec (p.pr (y i))) ∈ GlobalTheory.FinPl.latV S L (· = p.v) ∧
      ∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = p.v) →
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * p.pr (cA D (y j)) ∈ 𝒪[k] := by
  have hy' : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    rw [Pi.add_apply, p.sec_pr, p.sec_pr, map_mul, GlobalTheory.LatVac.cA_cA, ← add_mul]
    exact ((GlobalTheory.FinPl.FrameLat.idem_iff p (y i)).1 (hy i)).symm
  conv_lhs => rw [hy']
  rw [GlobalTheory.FinPl.FrameLat.decomp hL, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]

theorem latV_eq_of_wPart : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L L' : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → IsSelfDualC S L' → (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v)) → GlobalTheory.FinPl.latV S L (· = q.v) = GlobalTheory.FinPl.latV S L' (· = q.v) := by
  intro D k _ _ _ _ q S L L' hL hL' h
  have key : ∀ (M M' : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → IsSelfDualC S M' →
      (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M' (· = q.v)) →
      ∀ y, y ∈ GlobalTheory.FinPl.latV S M (· = q.v) → y ∈ GlobalTheory.FinPl.latV S M' (· = q.v) := by
    intro M M' hM hM' hMM' y hy
    have hs : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = q.v) := fun i => GlobalTheory.FinPl.FrameLat.latV_supp hy i
    rw [mem_latV_iff_wParts q hM y hs] at hy
    rw [mem_latV_iff_wParts q hM' y hs]
    exact ⟨(hMM' _).1 hy.1, fun x hx => hy.2 x ((hMM' x).2 hx)⟩
  ext y
  exact ⟨key L L' hL hL' h y, key L' L hL' hL (fun x => (h x).symm) y⟩

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : GlobalTheory.FinPl.SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (b : Fin n → k) :
    ((rat M : Mx D m n) *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map ((ofSplit q).π.comp (incA D)) *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => GlobalTheory.SplitInt.mul_sec q _ _

end

theorem exists_lineLat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  intro D k _ _ _ _ q S A B o MS MA Y _ _ FA FS z hMS hMA ⟨LB₀, hLB₀⟩ hβA hβB hIS hIA
  set f : D.host.E →+* k := (ofSplit q).π.comp (incA D) with hf
  have hpr : (ofSplit q).pr = ⇑f := rfl
  rw [hpr] at hβA hβB
  have hc : Fintype.card (Y ⊕ Unit) = S.rank := FS.card_eq
  have hcA : Fintype.card Y = A.rank := FA.card_eq
  have hB1 : B.rank = 1 := by
    have := o.rank_add
    rw [Fintype.card_sum, hcA, Fintype.card_unit] at hc
    omega
  have hsub : ∀ i j : Fin B.rank, i = j := fun i j => Fin.ext (by omega)
  haveI : Subsingleton (Fin B.rank) := ⟨hsub⟩
  let i₀ : Fin B.rank := ⟨0, by omega⟩

  have hcol : ∀ c : Y ⊕ Unit → k, FS.β *ᵥ c =
      o.iA.map f *ᵥ (FA.β *ᵥ fun a => c (Sum.inl a)) + c (Sum.inr ()) • (o.iB.map f *ᵥ z) := by
    intro c
    funext r
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton, hβA, hβB,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => by ring
    · exact Finset.sum_congr rfl fun s _ => by ring
  have hz : z i₀ ≠ 0 := by
    intro h0
    have hz0 : z = 0 := funext fun i => by rw [hsub i i₀, h0]; rfl
    have h1 := congrFun (congrFun FS.γβ (Sum.inr ())) (Sum.inr ())
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [hβB, hz0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hz' : ∀ i, z i ≠ 0 := fun i => by rw [hsub i i₀]; exact hz
  let FB : Frame k B.rank Unit :=
    { β := Matrix.of fun i _ => z i
      γ := Matrix.of fun _ i => (z i)⁻¹
      βγ := by
        ext i j
        rw [hsub j i]
        simp [Matrix.mul_apply, hz' i]
      γβ := by
        ext u u'
        rw [Subsingleton.elim u' u]
        simp [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, hz] }
  obtain ⟨LB, hLB, -, hLBw⟩ := GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D k q B Unit FB LB₀ hLB₀
  obtain ⟨L', hL', hL'o⟩ := GlobalTheory.OrthSumLat.exists_selfDual_orthAt D S A B o MA LB hMA hLB
  have hFBv : ∀ y : k, (FB.β *ᵥ fun _ => y) = fun i => z i * y := fun y => by
    funext i
    simp [FB, Matrix.mulVec, dotProduct]
  refine ⟨LB, hLB, ?_, fun y => ?_⟩
  ·
    have hqA : o.qA.map f * o.iA.map f = 1 := by
      rw [← Matrix.map_mul, o.qA_iA, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqAB : o.qA.map f * o.iB.map f = 0 := by
      rw [← Matrix.map_mul, o.qA_iB, Matrix.map_zero _ (map_zero f)]
    have hqB : o.qB.map f * o.iB.map f = 1 := by
      rw [← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqBA : o.qB.map f * o.iA.map f = 0 := by
      rw [← Matrix.map_mul, o.qB_iA, Matrix.map_zero _ (map_zero f)]
    have hw : ∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S MS (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v) := by
      intro x
      set c := FS.γ *ᵥ x with hcdef
      have hx : x = FS.β *ᵥ c := by rw [hcdef, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      have hqx : o.qA.map f *ᵥ x = FA.β *ᵥ fun a => c (Sum.inl a) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iA.map f), hqA,
          Matrix.one_mulVec, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iB.map f), hqAB, Matrix.zero_mulVec, smul_zero,
          add_zero]
      have hqBx : o.qB.map f *ᵥ x = FB.β *ᵥ fun _ => c (Sum.inr ()) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iA.map f), hqBA,
          Matrix.zero_mulVec, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iB.map f), hqB, Matrix.one_mulVec, zero_add,
          hFBv]
        funext i
        simp [mul_comm]
      have eS := hIS c
      rw [← hx] at eS
      have eA := hIA (fun a => c (Sum.inl a))
      have eB := hLBw (fun _ => c (Sum.inr ()))
      rw [← eS, hL'o q.v, show o.pA = rat o.qA from rfl, show o.pB = rat o.qB from rfl, rat_mulVec_sec,
        rat_mulVec_sec, ← hf, hqx, hqBx, ← eA, ← eB, Sum.forall]
    intro y
    rw [latV_eq_of_wPart D k q S MS L' hMS hL' hw]
    exact hL'o q.v y
  · have := hLBw (fun _ => y)
    rw [hFBv] at this
    exact ⟨fun h => this.1 fun _ => h, fun h => this.2 h ()⟩

end GlobalTheory.LineSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualLineLattice_splitting_sum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  first | exact @GlobalTheory.LineSplit.exists_lineLat | exact GlobalTheory.LineSplit.exists_lineLat | (intros; apply GlobalTheory.LineSplit.exists_lineLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtPlaces

theorem splitAt_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ hbas FY sc hFY N₁ M₁ hN₁ hFYN hM₁ hcore PP hP
  have hq : (l PP hP).q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := (l PP hP).under
  obtain ⟨hsc, hstep, hhz, -, -, hτ⟩ := hFY PP hP
  have hξ : valuation (l PP hP).k (ofSplit (l PP hP).q).xi = 1 := by
    have h1 := hsc (0 + 1 + 1)
    rw [hstep 0, map_mul, hsc 0, one_mul] at h1
    exact h1
  have hxi : (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ
    exact zero_ne_one hξ

  have key : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ LL : GlobalTheory.FinPl.Lat (y.bes j ρ h).L, IsSelfDualC _ LL ∧
      GlobalTheory.FinPl.OrthAt (y.bes j ρ h).o (M₁ j ρ h) (a.x j).L LL (l PP hP).q.v ∧
      ∀ t : (l PP hP).k, (t ∈ 𝒪[(l PP hP).k] ↔ (fun i => (l PP hP).q.sec
        ((fun i => sc PP hP j * (ofSplit (l PP hP).q).pr ((y.bes j ρ h).ζ i)) i * t)) ∈ GlobalTheory.FinPl.latV _ LL (· = (l PP hP).q.v)) := by
    intro j ρ h
    have hj : j ≤ (l PP hP).s + 1 := by have := (l PP hP).hs; omega
    have hs0 : sc PP hP j ≠ 0 := by
      intro h0
      have h1 := hsc j
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (l PP hP).k (ofSplit (l PP hP).q) hxi).1 _ ρ ((y.bes j ρ h).lev (a.x j).vol)
      (sc PP hP j) ((l PP hP).FX j hj) hs0).1
    have hIntM := hcore PP hP j ρ h hj F₀ hF₀
    have hA : IsSelfDualC (D.sp.X j) (a.x j).L := (hIs.x j (by omega)).sd
    refine GlobalTheory.T.exists_selfDualLineLattice_splitting_sum D (l PP hP).k (l PP hP).q (y.bes j ρ h).V₀ (D.sp.X j) (y.bes j ρ h).L (y.bes j ρ h).o (M₁ j ρ h)
      (a.x j).L _ ((l PP hP).FX j hj) F₀ _ (hM₁ j ρ h) hA ⟨_, GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D _⟩ hF₀.1 (fun r => ?_)
      hIntM ((l PP hP).latX j hj)
    rw [hF₀.2 r]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.MixPer.vecB, Matrix.mulVec, dotProduct, Matrix.map_apply, GlobalTheory.LocMod.Place.pr, map_sum, map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hx : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
    rcases hP with hP' | hP'
    · intro ht
      exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hP', rfl⟩) ht
    · exact GlobalTheory.tuplePlace_under_not_mem_tP W u hW a y m b₀ k ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ
        hbas FY sc hFY PP hP'
  refine ⟨fun j ρ h => ?_, fun j h => ?_⟩
  · obtain ⟨LL, hLL, hO, -⟩ := key j ρ h
    exact ⟨LL, hLL, hq ▸ hO⟩
  · have hjs : j = (l PP hP).s := by have := (l PP hP).hs; omega
    subst hjs
    obtain ⟨LL, hLL, hO, hLLw⟩ := key _ 0 h
    obtain ⟨LZ₀, hLZ₀, -⟩ := hLZ _ h (l PP hP).q.v (hq ▸ hx)
    obtain ⟨LZ, hLZsd, hLZO, hLZw⟩ := GlobalTheory.T.exists_selfDualLineLattice_splitting_sum D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1 + 1)) D.sp.X' a.Lz
      (a.oT _ h) (a.x ((l PP hP).s + 1 + 1)).L a.LT _ (l PP hP).FT (l PP hP).FM
      (fun i => (ofSplit (l PP hP).q).pr (a.ζ₀ i)) (hIs.x _ (by omega)).sd hsdT ⟨LZ₀, hLZ₀⟩
      (fun r b => by rw [(l PP hP).last]; rfl) (fun r => by rw [(l PP hP).last]; rfl) (l PP hP).latM (l PP hP).latT
    refine ⟨LL, LZ, hLL, hLZsd, hq ▸ hO, hNT ▸ hq ▸ hLZO, ?_⟩
    intro w hw
    rw [← hq] at hw ⊢
    rw [hvτ]
    have hmap := GlobalTheory.T.splitPlace_line_similitude_maps_selfDual_lattice D (l PP hP).k (l PP hP).q (y.bes _ 0 h).L a.Lz (y.τ _ h) LL LZ _ _ (-(ofSplit (l PP hP).q).xi)
      (l PP hP).unit hLL hLZsd (y.bes _ 0 h).line.1 hpre.line.1 hLLw hLZw (by rw [Valuation.map_neg]; exact hξ)
      (by rw [hτ h]; funext i; simp only [Pi.smul_apply, smul_eq_mul]; ring) (hTau _ h).1
    exact GlobalTheory.T.lineHomAdjointTwist_mem_completedHomLattice D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1)) (y.bes _ 0 h).L a.Lz (y.τ _ h)
      (a.x ((l PP hP).s + 1)).L LL LZ (l PP hP).unit (hIs.x _ (by omega)).sd hLL hLZsd hmap w hw

end GlobalTheory.SplitAtPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_equation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.SplitAtPlaces.splitAt_places | exact GlobalTheory.SplitAtPlaces.splitAt_places | (intros; apply GlobalTheory.SplitAtPlaces.splitAt_places <;> assumption)
end

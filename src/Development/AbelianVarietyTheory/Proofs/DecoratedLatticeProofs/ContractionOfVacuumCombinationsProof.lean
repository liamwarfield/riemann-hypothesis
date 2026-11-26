module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMapsBesselLineLatticeIffSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalves
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfGen

variable {D : D7}

theorem list_sum_pair {ι : Type} (l : List ι) (α : ι → Af D.host.F) :
    (l.map fun i => pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E)).sum =
      pairA D.host.F 0 (l.map α).sum ⊗ₜ[D.host.F] (1 : D.host.E) := by
  induction l with
  | nil => simp [GlobalTheory.FinPlLoc.pairA_zero]
  | cons a l ih => simp [List.map_cons, List.sum_cons, ih, GlobalTheory.FinPlLoc.pairA_add, TensorProduct.add_tmul]

theorem sum_splitIdem_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} (h : Places p I P) :
    (I.map fun i => (p i).e + cA D (p i).e).sum = GlobalTheory.FinPlLoc.idem D P := by
  classical
  choose ε hε hεe using fun i => (p i).above
  choose α hαe hα1 hα0 using hε
  have hterm : ∀ i, (p i).e + cA D (p i).e = pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    intro i
    rw [hεe i, hαe i]
    rfl
  rw [List.map_congr_left (fun i _ => hterm i), list_sum_pair]
  unfold GlobalTheory.FinPlLoc.idem
  congr 2
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (I.map α).sum = evalV D.host.F w (GlobalTheory.FinPlLoc.ePl D P)
  rw [GlobalTheory.FinPlLoc.evalV_ePl, map_list_sum, List.map_map, ← List.sum_toFinset _ h.nodup]
  by_cases hw : P w
  · rw [if_pos hw]
    obtain ⟨j, rfl⟩ := (h.mem w).1 hw
    have hj : ∀ i, evalV D.host.F (p j).v (α i) = if i = j then 1 else 0 := by
      intro i
      split_ifs with hij
      · subst hij; exact hα1 i
      · exact hα0 i _ fun hv => hij (h.inj hv.symm)
    simp only [Function.comp_apply, hj]
    rw [Finset.sum_ite_eq' , if_pos (List.mem_toFinset.2 (h.all j))]
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact hα0 i w fun hv => hw ((h.mem w).2 ⟨i, hv⟩)

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hsum]

theorem smul_mem_halves {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {e : AE D} (he : IsSplitIdem D e) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    e • u ∈ {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  have hee : e * e = e := he.1
  refine ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT P e ?_ u hu, e, he, ?_⟩
  · exact GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← map_mul, hee])
  · rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hee]

theorem entry_mem_idAt {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : ∀ i j, u i j ∈ idAt D P := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hy
    exact fun i j => GlobalTheory.FinPlLoc.pair_mem_idAt P α hα _
  | zero => exact fun i j => zero_mem _
  | add y z _ _ hy hz => exact fun i j => add_mem (hy i j) (hz i j)
  | neg y _ hy => exact fun i j => neg_mem (hy i j)

theorem latO_le_closure_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT P, u ∈ AddSubgroup.closure {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  intro D k _ _ _ _ ι p I P h S T LS LT u hu
  have hsum := sum_splitIdem_eq h
  have hu' : GlobalTheory.FinPlLoc.idem D P • u = u := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff P _).1 (entry_mem_idAt hu i j)
  have hdec : u = (I.map fun i => (p i).e • u + cA D (p i).e • u).sum := by
    conv_lhs => rw [← hu', ← hsum, List.sum_smul, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, add_smul]
  rw [hdec]
  refine AddSubgroup.list_sum_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact add_mem (AddSubgroup.subset_closure (smul_mem_halves (p i).split hu))
    (AddSubgroup.subset_closure (smul_mem_halves (isSplitIdem_cA (p i).split) hu))

end GlobalTheory.HalfGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalvesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT P, u ∈ AddSubgroup.closure {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  first | exact @GlobalTheory.HalfGen.latO_le_closure_halves | exact GlobalTheory.HalfGen.latO_le_closure_halves | (intros; apply GlobalTheory.HalfGen.latO_le_closure_halves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaSurjectiveSupportedConjugateHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaSurjectiveSupportedConjugateHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkKapInv

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem isHalf_mul_l {e : AE D} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hx k j]

theorem isHalf_mul_r {e : AE D} {l m n : ℕ} {x : Mx D l m} (hx : IsHalf e x) (A : Mx D m n) : IsHalf e (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hx i k]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) :=
  fun i j => by
    show cA D e * cA D (x j i) = cA D (x j i)
    rw [← map_mul, hx j i]

def tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (_l : Link B L' ζ') :
    Matrix (Fin L'.rank) (Fin B.L.rank) D.host.E := fun i j => -(B.ζ j)⁻¹ * ζ' i

theorem mul_tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    l.τ * tauPlus l = 1 := by
  obtain ⟨hr, hq⟩ := B.line
  have hsub : ∀ a b : Fin B.L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hne : ∀ a, B.ζ a ≠ 0 := by
    intro a ha
    apply hq
    have h0 : B.ζ = 0 := funext fun b => by rw [hsub b a]; exact ha
    rw [h0]; simp
  funext a b
  rw [hsub b a, Matrix.one_apply_eq, Matrix.mul_apply]
  have hm := congrFun l.map a
  rw [Pi.neg_apply, Matrix.mulVec, dotProduct] at hm
  simp only [tauPlus]
  calc ∑ k, l.τ a k * (-(B.ζ a)⁻¹ * ζ' k) = -(B.ζ a)⁻¹ * ∑ k, l.τ a k * ζ' k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [hm, neg_mul_neg, inv_mul_cancel₀ (hne a)]

theorem kappa_inv : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ')
    (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧
      ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  intro D ρ B L' ζ' l S P h
  refine ⟨(rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h, ?_, fun hh => ?_, fun e he => ?_⟩
  · show ofAdj B.L S ((rat l.τ : Mx D B.L.rank L'.rank) * ((rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h)) = h
    rw [← Matrix.mul_assoc, ← rat_mul, mul_tauPlus l, rat_one, Matrix.one_mul, GlobalTheory.LastOpPf.ofAdj_starAdj]
  · exact GlobalTheory.LastOpPf.mxAt_mul_l _ (GlobalTheory.LastOpPf.mxAt_smul _ (GlobalTheory.LastOpPf.mxAt_mul_l _
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LastOpPf.mxAt_adj hh) _)))
  · exact isHalf_mul_l _ (isHalf_smul _ (isHalf_mul_l _ (isHalf_mul_r (isHalf_adj he) _)))

end GlobalTheory.LinkKapInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaSurjectiveSupportedConjugateHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧ ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  first | exact @GlobalTheory.LinkKapInv.kappa_inv | exact GlobalTheory.LinkKapInv.kappa_inv | (intros; apply GlobalTheory.LinkKapInv.kappa_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemHomLatticeCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemHomLatticeCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineProj

open GlobalTheory.IwaPlace

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {π : Mx D S.rank S.rank} (h : adj π ⬝ gA S = gA S ⬝ π) (x y : Fin S.rank → AE D) :
    hermAt S (π *ᵥ x) y = hermAt S x (π *ᵥ y) := by
  have e : (fun i => cA D ((π *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj π := by
    funext i
    rw [adj, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec (cA D) π y i
  have e2 : gA S *ᵥ (π *ᵥ x) = adj π *ᵥ (gA S *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x) h.symm
  rw [hermAt_eq, hermAt_eq, e, e2]
  exact Matrix.dotProduct_mulVec _ _ _

theorem hermAt_smul (S : HSp D) (a : AE D) (x y : Fin S.rank → AE D) :
    hermAt S (a • x) y = hermAt S x (cA D a • y) := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermAt_add_left (S : HSp D) (x x' y : Fin S.rank → AE D) :
    hermAt S (x + x') y = hermAt S x y + hermAt S x' y := by
  simp only [hermAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem add_mem_intAt {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem proj_selfAdj {S A L : HSp D} (o : OrthDec S A L) :
    adj (o.jB ⬝ o.pB) ⬝ gA S = gA S ⬝ (o.jB ⬝ o.pB) := by
  rw [o.pB_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_of_half (p : SplitPt D k) {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {π : Mx D S.rank S.rank}
    (h : adj π ⬝ gA S = gA S ⬝ π)
    (hw : ∀ z ∈ latV S M (· = p.v), π *ᵥ (p.e • z) ∈ latV S M (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S M (· = p.v)) : π *ᵥ y ∈ latV S M (· = p.v) := by
  obtain ⟨hs, -, hd⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M p.v hM
  refine (hd _ (mulVec_mem_idAt π (hs y hy))).2 fun x hx => ?_
  have hy' : y = p.e • y + cA D p.e • y := by
    funext i
    rw [← add_smul, Pi.smul_apply, smul_eq_mul]
    exact ((FrameLat.idem_iff p (y i)).1 (hs y hy i)).symm
  rw [hy', Matrix.mulVec_add, hermAt_add_left]
  refine add_mem_intAt ((hd _ (hs _ (hw y hy))).1 (hw y hy) x hx) ?_
  rw [hermAt_mulVec S h, hermAt_smul, GlobalTheory.DualPairCheck.cA_cA, ← Matrix.mulVec_smul]
  exact (hd y (hs y hy)).1 hy _ (hw x hx)

theorem proj_frame {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    (x : n ⊕ Fin 1 → k) :
    (o.jB ⬝ o.pB).map p.pr *ᵥ (α₀.b *ᵥ x) = α₀.b *ᵥ Sum.elim 0 (x ∘ Sum.inr) := by
  have h1 : (o.jB * o.pB).map p.pr * o.jA.map p.pr = 0 := by
    rw [← Matrix.map_mul, Matrix.mul_assoc, o.pB_jA, Matrix.mul_zero]
    exact Matrix.map_zero _ (map_zero _)
  have h2 : (o.jB * o.pB) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      exact RingHom.map_mulVec (incA D) o.iB ζ i
    rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, o.pB_jB, Matrix.mul_one]
  have h3 : (o.jB * o.pB).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = fun i => p.pr (ratV (vecB o ζ) i) := by
    funext i
    have := RingHom.map_mulVec p.pr (o.jB * o.pB) (ratV (vecB o ζ)) i
    rw [h2] at this
    exact this.symm
  rw [IsSumFrame] at h
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_fromCols, ← Matrix.mul_assoc, h1, Matrix.zero_mul,
    ← Matrix.replicateCol_mulVec, h3, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec,
    Matrix.mulVec_zero]

theorem proj_half {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    {M : Lat S} {Λ : Submodule 𝒪[k] (n → k)} (hΛ : α₀.IsLat M (lastKer Λ)) {z : Fin S.rank → AE D}
    (hz : z ∈ latV S M (· = p.v)) : (o.jB ⬝ o.pB) *ᵥ (p.e • z) ∈ latV S M (· = p.v) := by
  have hb : α₀.b *ᵥ (α₀.b' *ᵥ fun i => p.pr (z i)) = fun i => p.pr (z i) := by
    rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
  have h1 : (α₀.b' *ᵥ fun i => p.pr (z i)) ∈ lastKer Λ := by
    refine (hΛ _).2 ?_
    rw [hb]
    simp only [p.sec_pr]
    exact GlobalTheory.FinPlLoc.smul_latV p.v (FrameLat.e_mem_intAt p) hz
  have h2 : (Sum.elim 0 ((α₀.b' *ᵥ fun i => p.pr (z i)) ∘ Sum.inr) : n ⊕ Fin 1 → k) ∈ lastKer Λ :=
    GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨Λ.zero_mem, (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 h1).2⟩
  have h3 := (hΛ _).1 h2
  rw [← proj_frame o ζ h, hb] at h3
  convert h3 using 1
  funext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← p.sec_pr, RingHom.map_mulVec]
  rfl

theorem lineProj_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ B S α α₀ M LS Λ hM hLS h x hx
  have hπ : ∀ y ∈ latV B.V₀ M P, (B.o.jB * B.o.pB) *ᵥ y ∈ latV B.V₀ M P := by
    intro y hy
    refine (GlobalTheory.FinPlLoc.part_lat P B.V₀ M _ hM.1).2 ⟨mulVec_mem_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
    obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
    rw [← Matrix.mulVec_smul]
    exact mulVec_mem_of_half (p i) hM (proj_selfAdj B.o) (fun z hz => proj_half B.o B.ζ (h i).1 (h i).2 hz)
      (GlobalTheory.FinPlLoc.smul_latV _ he hy)
  obtain ⟨hx1, hx2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P x).1 hx
  have e : (B.o.resS S).symm (0, (B.o.resS S x).2) = x * (B.o.jB * B.o.pB) := by
    rw [OrthDec.resS_symm_apply, OrthDec.resS_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
  rw [e]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx1 i l)
  · have := hx2 _ (hπ y hy)
    rwa [Matrix.mulVec_mulVec] at this

end GlobalTheory.LineProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemHomLatticeCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineProjection_mem_homLatticeCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  first | exact @GlobalTheory.LineProj.lineProj_mem_latO | exact GlobalTheory.LineProj.lineProj_mem_latO | (intros; apply GlobalTheory.LineProj.lineProj_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContraction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.LineVanish

variable {D : D7}

theorem mxAt_mul_right' {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem fin_of_mxAt' {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem isHalf_mul_right {e : AE D} {m n r : ℕ} {u : Mx D m n} (hu : IsHalf e u) (N : Mx D n r) :
    IsHalf e (u * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hu i k]

theorem isHalf_mul_left {e : AE D} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (N * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hu k j]

theorem contr_smul_left' {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem step3 : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V T : HSp D) (LV : Lat V) (LT : Lat T), IsSelfDualC V LV → IsSelfDualC T LT → ∀ y : WO V T, MxAt P y → y ∉ latO V T (LV : Set _) (LT : Set _) P → ∃ u ∈ latO V T (LV : Set _) (LT : Set _) P, (∃ e, IsSplitIdem D e ∧ IsHalf e u) ∧ ψ (symplO V T u y) ≠ 1 := by
  intro D k _ _ _ _ ι p I P hP ψ hψ V T LV LT hLV hLT y hy hout
  by_contra hno
  push_neg at hno
  apply hout
  have hadd : ∀ a b : WO V T, symplO V T (a + b) y = symplO V T a y + symplO V T b y := by
    intro a b
    have h := GlobalTheory.SplitScalar.symplO_sub_left V T (a + b) b y
    rw [add_sub_cancel_right] at h
    rw [h]; ring
  have hneg : ∀ a : AF D.host.F, ψ a = 1 → ψ (-a) = 1 := by
    intro a ha
    calc ψ (-a) = ψ (-a) * ψ a := by rw [ha, mul_one]
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let K : AddSubgroup (WO V T) :=
    { carrier := {u | ψ (symplO V T u y) = 1}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, GlobalTheory.SplitScalar.symplO_zero_left, AddChar.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hadd, AddChar.map_add_eq_mul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h0 : symplO V T (-a) y = -symplO V T a y := by
          have := hadd (-a) a
          rw [neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_left] at this
          exact eq_neg_of_add_eq_zero_left this.symm
        rw [h0]; exact hneg _ ha }
  rw [GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V T LV LT hLV hLT P y hy]
  intro u' hu'
  have hle : AddSubgroup.closure {x : WO V T | x ∈ latO V T (LV : Set _) (LT : Set _) P ∧
      ∃ e, IsSplitIdem D e ∧ IsHalf e x} ≤ K := by
    apply (AddSubgroup.closure_le K).2
    intro u hu
    exact hno u hu.1 hu.2
  have hK : u' ∈ K := hle
    (GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves D k ι p I P hP V T _ _ u' hu')
  rw [GlobalTheory.SplitScalar.symplO_skew]
  exact hneg _ hK


set_option maxHeartbeats 2000000 in
theorem vanish : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr y hy hout f₁ f₂ h₁ h₂
  classical

  have hyM : MxAt P ((B.o.resS S).symm (0, y)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right' hy _
  obtain ⟨u, hu, ⟨e, he, heu⟩, hψu⟩ := step3 D k ι p I P hP ψ hψ B.V₀ S M LS hM hLS _ hyM hout
  set h := (B.o.resS S u).2 with hh
  have hhN : (B.o.resS S).symm (0, h) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    GlobalTheory.T.lineProjection_mem_homLatticeCompletion D k ι p I P hP n' ρ B S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) u hu
  have hhalf : IsHalf e h := isHalf_mul_right heu _
  have hhmx : MxAt P h := by
    have := ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P _).1 hhN).1
    have h2 : (B.o.resS S ((B.o.resS S).symm (0, h))).2 = h := by rw [AddEquiv.apply_symm_apply]
    rw [← h2]; exact mxAt_mul_right' this _
  have hpair : symplO B.V₀ S ((B.o.resS S).symm (0, h)) ((B.o.resS S).symm (0, y)) =
      symplO B.V₀ S u ((B.o.resS S).symm (0, y)) := by
    rw [B.o.symplO_resS, B.o.symplO_resS S u, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.SplitScalar.symplO_zero_right, GlobalTheory.SplitScalar.symplO_zero_right]

  obtain ⟨x', hkx, hxmx, hxhalf⟩ := GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf D ρ B B'.L B'.ζ l S P h
  have hx'N : (B'.o.resT S).symm (0, x') ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P := by
    rw [GlobalTheory.T.kappa_maps_besselLineLattice_iff_split D k ι p I P hP n' n'' ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x' (hxmx hhmx), hkx]
    exact hhN
  have hx'half : IsHalf (cA D e) ((B'.o.resT S).symm (0, x')) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (hxhalf e hhalf)
  have hf₂ : heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x')) f₂ = f₂ :=
    h₂.2.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he) _ hx'N hx'half
  have hf₁ : heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x')) f₁ = f₁ := by
    rw [hkx]
    exact h₁.2.2 e he _ hhN (by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]; exact isHalf_mul_right hhalf _)
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt' hyM) h₁.1
  have hmove := GlobalTheory.T.besselLineContraction_heisenberg_invariant D ψ hψ ρ σ B B' l S vL _ f₂ hth h₂.1 x'
  rw [hf₂, GlobalTheory.SplitScalar.heisO_comm, hf₁, contr_smul_left', hkx, hpair] at hmove
  set C := GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂
  have : (ψ (symplO B.V₀ S u ((B.o.resS S).symm (0, y))) - 1) • C = 0 := by
    rw [sub_smul, hmove, one_smul, sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψu)

end GlobalTheory.FinPl.LineVanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContractionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  first | exact @GlobalTheory.FinPl.LineVanish.vanish | exact GlobalTheory.FinPl.LineVanish.vanish | (intros; apply GlobalTheory.FinPl.LineVanish.vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfGeneratedPointActsScalarOnLatticeVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfGeneratedPointActsScalarOnLatticeVacua
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfGenScalar

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (z : WO S T),
    z ∈ AddSubgroup.closure {u | u ∈ Λ ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e u} →
    ∃ c : ℂ, ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T z f = c • f := by
  intro D ψ S T Λ z hz
  induction hz using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨huΛ, e, he, hh⟩ := hu
    exact ⟨1, fun f hf => by rw [one_smul]; exact hf.2 e he u huΛ hh⟩
  | zero => exact ⟨1, fun f _ => by rw [one_smul]; exact GlobalTheory.SplitScalar.heisO_zero ψ S T f⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨cx, hcx⟩ := ihx
    obtain ⟨cy, hcy⟩ := ihy
    refine ⟨(ψ (symplOH S T x y))⁻¹ * (cx * cy), fun f hf => ?_⟩
    have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T x y f
    rw [hcy f hf, GlobalTheory.SplitScalar.heisO_smul, hcx f hf, smul_smul] at h1
    have hne := addChar_ne_zero ψ (symplOH S T x y)
    rw [mul_smul, mul_comm cx cy, h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  | neg x _ ihx =>
    obtain ⟨cx, hcx⟩ := ihx
    by_cases h0 : cx = 0
    · refine ⟨0, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, h0, zero_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      have hf0 : f = 0 := by
        have h2 : heisO ψ S T (-x) (0 : WO S T → ℂ) = 0 := by
          simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
        rw [h2] at h1
        exact (smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero ψ _)
      subst hf0
      rw [zero_smul]
      simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
    · refine ⟨ψ (symplOH S T (-x) x) / cx, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, GlobalTheory.SplitScalar.heisO_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]

end GlobalTheory.HalfGenScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfGeneratedPointActsScalarOnLatticeVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfGenerated_point_acts_scalar_on_latticeVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (z : WO S T), z ∈ AddSubgroup.closure {u | u ∈ Λ ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e u} → ∃ c : ℂ, ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T z f = c • f := by
  first | exact @GlobalTheory.HalfGenScalar.exists_scalar | exact GlobalTheory.HalfGenScalar.exists_scalar | (intros; apply GlobalTheory.HalfGenScalar.exists_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ContrOpProof

variable {D : D7}

theorem mxAt_mul_right {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem mxAt_mul_left {P : Pl D → Prop} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : MxAt P u) :
    MxAt P (N * u) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hu k j)

theorem mxAt_sub {P : Pl D → Prop} {m n : ℕ} {u v : Mx D m n} (hu : MxAt P u) (hv : MxAt P v) : MxAt P (u - v) :=
  fun i j => by simpa only [Matrix.sub_apply] using Ideal.sub_mem _ (hu i j) (hv i j)

theorem mxAt_neg {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : MxAt P (-u) :=
  fun i j => by simpa only [Matrix.neg_apply] using Submodule.neg_mem _ (hu i j)

theorem fin_of_mxAt {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem biComb_single (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S) (a' : WO S A') (r : ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' (Finsupp.single a r) (Finsupp.single a' 1) C u v =
      r * heisO ψ A S a (fun u' => heisO ψ S A' a' (C u') v) u := by
  by_cases hr : r = 0
  · subst hr
    simp [biComb, comb]
  · simp [biComb, comb, Finsupp.support_single_ne_zero _ hr]

theorem symplOH_self {S T : HSp D} (x : WO S T) : symplOH S T x (-x) = 0 := by
  have h1 := GlobalTheory.SplitScalar.symplOH_skew S T x x
  have h2 := GlobalTheory.SplitScalar.symplOH_add_self S T x x
  have h3 : symplO S T x x = 0 := by
    rw [← h2]
    nth_rewrite 2 [h1]
    exact add_neg_cancel _
  have h4 : symplOH S T x x = 0 := by rw [symplOH, h3, mul_zero]
  have h5 := GlobalTheory.SplitScalar.symplOH_add_right S T x x (-x)
  rw [add_neg_cancel, GlobalTheory.ContrComb.symplOH_zero_right, h4, zero_add] at h5
  exact h5.symm

theorem heisO_neg_cancel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T (-x) g) = g := by
  rw [GlobalTheory.SplitScalar.heisO_heisO, add_neg_cancel, GlobalTheory.SplitScalar.heisO_zero, symplOH_self, AddChar.map_zero_eq_one,
    one_smul]

theorem line_step {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ)
    (hf₁ : IsThetaFunO ψ B.V₀ S f₁) (hf₂ : IsThetaFunO ψ S B'.V₀ f₂) (y : WO B.L S) (w : WO S B'.L)
    (hy : ((B.o.resS S).symm (0, y)).map (infPart D) = 0)
    (hk : (-(B.o.resS S).symm (0, l.κ S w)).map (infPart D) = 0) (c : ℂ)
    (hc : GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y - l.κ S w)) f₁) f₂ =
      c • GlobalTheory.Unf.contr l S vL f₁ f₂) :
    GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, w)) f₂) =
      (ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S w)) ((B.o.resS S).symm (0, y))) * c) •
        GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S (-(B.o.resS S).symm (0, l.κ S w))
      (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁)) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hk (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hy hf₁)
  have hmove := GlobalTheory.T.besselLineContraction_heisenberg_invariant D ψ hψ ρ σ B B' l S vL _ f₂ hth hf₂ w
  rw [heisO_neg_cancel] at hmove
  rw [hmove, GlobalTheory.SplitScalar.heisO_heisO, contr_smul_left]
  have he : -(B.o.resS S).symm (0, l.κ S w) + (B.o.resS S).symm (0, y) = (B.o.resS S).symm (0, y - l.κ S w) := by
    rw [← map_neg, ← map_add (f := _), Prod.neg_mk, neg_zero, Prod.mk_add_mk, zero_add, neg_add_eq_sub]
  rw [he, hc, smul_smul]


open Classical in
def cstL (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop)
    (y : WO B.L S) : ℂ :=
  if (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P then
    (if h : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f
      then h.choose else 0) else 0

def coefL (ψ : AddChar (AF D.host.F) ℂ) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop) (u : WO B.V₀ S) (u' : WO S B'.V₀) : ℂ :=
  ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S (B'.o.resT S u').2)) ((B.o.resS S).symm (0, (B.o.resS S u).2))) *
    cstL ψ B S M LS P ((B.o.resS S u).2 - l.κ S (B'.o.resT S u').2)

set_option maxHeartbeats 2000000 in
theorem contrOp : ∀ D : D7, ContrOp D := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr e₁ e₂ he₁ he₂
  classical
  have key : ∀ y, MxAt P y → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ =
        cstL ψ B S M LS P y • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
    intro y hy f₁ f₂ h₁ h₂
    by_cases hin : (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P
    · have hex : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f := by
        obtain ⟨c, hc⟩ := GlobalTheory.T.halfGenerated_point_acts_scalar_on_latticeVacua D ψ B.V₀ S _ _ (GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves D k ι p I P hP B.V₀ S _ _ _ hin)
        exact ⟨c, fun f hf => hc f hf.2⟩
      have hcst : cstL ψ B S M LS P y = hex.choose := by simp only [cstL, if_pos hin, dif_pos hex]
      rw [hcst, hex.choose_spec f₁ h₁, contr_smul_left]
    · have hcst : cstL ψ B S M LS P y = 0 := by simp only [cstL, if_neg hin]
      rw [hcst, zero_smul, GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction D k ι p I P hP n' n'' ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr
        y hy hin f₁ f₂ h₁ h₂]
  let s := e₁.support ×ˢ e₂.support
  refine ⟨⟨s.card, fun i => Finsupp.single (B.o.resS S (s.equivFin.symm i).1.1).1
      (e₁ (s.equivFin.symm i).1.1 * e₂ (s.equivFin.symm i).1.2 *
        coefL ψ B B' l S M LS P (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2),
    fun i => Finsupp.single (B'.o.resT S (s.equivFin.symm i).1.2).1 1⟩, ?_, ?_⟩
  · intro i
    have hq := (s.equivFin.symm i).2
    rw [Finset.mem_product] at hq
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_right (he₁ _ hq.1) _
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_left _ (he₂ _ hq.2)
  intro f₁ f₂ h₁ h₂
  have hth₁ : ∀ u, MxAt P u → IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S u f₁) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₁.1
  have hth₂ : ∀ u, MxAt P u → IsThetaFunO ψ S B'.V₀ (heisO ψ S B'.V₀ u f₂) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₂.1
  have hint : ∀ g₁ g₂, IsThetaFunO ψ B.V₀ S g₁ → IsThetaFunO ψ S B'.V₀ g₂ → ∀ (u : WO B.A S) (v : WO S B'.A),
      IntegrableOn (fun x => g₂ ((B'.o.resT S).symm (v, x)) * g₁ ((B.o.resS S).symm (u, l.κ S x))) vL.𝓕 vL.μ := by
    intro g₁ g₂ hg₁ hg₂ u v
    obtain ⟨hc, hp⟩ := GlobalTheory.T.theta_contraction_integrand_continuous_periodic D ρ σ B B' l S ψ g₁ g₂ hg₁ hg₂
    exact (GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
      (fun x q => g₂ ((B'.o.resT S).symm (q.2, x)) * g₁ ((B.o.resS S).symm (q.1, l.κ S x))) hc
      (fun γ' hγ x q => hp γ' hγ x q.1 q.2)).1 (u, v)
  have hLR : ∀ (g₁ : WO B.V₀ S → ℂ) (g₂ : WO S B'.V₀ → ℂ) (b : WO B.A S) (b' : WO S B'.A),
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (b, 0)) g₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b', 0)) g₂) =
        fun u₀ v₀ => heisO ψ B.A S b (fun u'' => heisO ψ S B'.A b' (GlobalTheory.Unf.contr l S vL g₁ g₂ u'') v₀) u₀ := by
    intro g₁ g₂ b b'
    funext u₀ v₀
    rw [← GlobalTheory.ContrComb.heis_left ψ l S vL g₁ _ b u₀ v₀]
    congr 1
    funext u''
    rw [GlobalTheory.ContrComb.heis_right]
  have heL : ∀ z : WO B.L S, MxAt P z → MxAt P ((B.o.resS S).symm (0, z)) := by
    intro z hz
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right hz _
  have pair : ∀ u, MxAt P u → ∀ u', MxAt P u' →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) =
        fun u₀ v₀ => coefL ψ B B' l S M LS P u u' * heisO ψ B.A S (B.o.resS S u).1
          (fun u'' => heisO ψ S B'.A (B'.o.resT S u').1 (GlobalTheory.Unf.contr l S vL f₁ f₂ u'') v₀) u₀ := by
    intro u hu u' hu'
    have hsL : u = (B.o.resS S).symm ((B.o.resS S u).1, 0) + (B.o.resS S).symm (0, (B.o.resS S u).2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hsR : u' = (B'.o.resT S).symm ((B'.o.resT S u').1, 0) + (B'.o.resT S).symm (0, (B'.o.resT S u').2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hoL : symplO B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0)) ((B.o.resS S).symm (0, (B.o.resS S u).2)) = 0 := by
      rw [B.o.symplO_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hoR : symplO S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0)) ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) = 0 := by
      rw [B'.o.symplO_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hy : MxAt P (B.o.resS S u).2 := mxAt_mul_right hu _
    have hw : MxAt P (B'.o.resT S u').2 := mxAt_mul_left _ hu'
    have hkw : MxAt P (l.κ S (B'.o.resT S u').2) := GlobalTheory.T.besselLink_kappa_preserves_supported_matrices D ρ B B'.L B'.ζ l S P _ hw
    have hline := line_step ψ hψ l S vL f₁ f₂ h₁.1 h₂.1 (B.o.resS S u).2 (B'.o.resT S u').2 (fin_of_mxAt (heL _ hy))
      (fin_of_mxAt (mxAt_neg (heL _ hkw))) _ (key _ (mxAt_sub hy hkw) f₁ f₂ h₁ h₂)
    have e1 : heisO ψ B.V₀ S u f₁ = heisO ψ B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0))
        (heisO ψ B.V₀ S ((B.o.resS S).symm (0, (B.o.resS S u).2)) f₁) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoL, ← hsL]
    have e2 : heisO ψ S B'.V₀ u' f₂ = heisO ψ S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0))
        (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) f₂) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoR, ← hsR]
    rw [e1, e2, hLR, hline]
    funext u₀ v₀
    simp only [coefL, heisO, Pi.smul_apply, smul_eq_mul]
    ring
  funext u₀ v₀
  have hexp : GlobalTheory.Unf.contr l S vL (comb ψ _ _ e₁ f₁) (comb ψ _ _ e₂ f₂) u₀ v₀ =
      ∑ u' ∈ e₂.support, ∑ u ∈ e₁.support, (e₂ u' * e₁ u) *
        GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) u₀ v₀ := by
    simp only [GlobalTheory.Unf.contr, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    have hI : ∀ u' ∈ e₂.support, ∀ u ∈ e₁.support, IntegrableOn (fun x =>
        e₂ u' * heisO ψ S B'.V₀ u' f₂ ((B'.o.resT S).symm (v₀, x)) *
          (e₁ u * heisO ψ B.V₀ S u f₁ ((B.o.resS S).symm (u₀, l.κ S x)))) vL.𝓕 vL.μ := by
      intro u' hu' u hu
      refine Integrable.congr ((hint _ _ (hth₁ u (he₁ u hu)) (hth₂ u' (he₂ u' hu')) u₀ v₀).const_mul (e₂ u' * e₁ u))
        (ae_of_all _ fun x => ?_)
      simp only
      ring
    rw [integral_finsetSum _ fun u' hu' => integrable_finsetSum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [integral_finsetSum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hexp, Finset.sum_comm]
  simp only [BiOp.app, Finset.sum_apply]
  rw [Equiv.sum_comp s.equivFin.symm (fun q : s => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1.1).1 (e₁ q.1.1 * e₂ q.1.2 * coefL ψ B B' l S M LS P q.1.1 q.1.2))
      (Finsupp.single (B'.o.resT S q.1.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀),
    Finset.sum_coe_sort s (fun q => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1).1 (e₁ q.1 * e₂ q.2 * coefL ψ B B' l S M LS P q.1 q.2))
      (Finsupp.single (B'.o.resT S q.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀), Finset.sum_product]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
  rw [pair u (he₁ u hu) u' (he₂ u' hu'), biComb_single]
  ring

end GlobalTheory.FinPl.ContrOpProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contractionOfVacuumCombinations_proof : ∀ D : D7, GlobalTheory.FinPl.ContrOp D := by
  first | exact @GlobalTheory.FinPl.ContrOpProof.contrOp | exact GlobalTheory.FinPl.ContrOpProof.contrOp | (intros; apply GlobalTheory.FinPl.ContrOpProof.contrOp <;> assumption)
end

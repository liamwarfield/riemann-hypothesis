module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.CellLevels

variable {D : D7}

private theorem congGrp_mono' (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  unfold congGrp at hg ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  rw [← Ideal.Quotient.factor_comp_mk h, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hg, map_one]

private theorem idAt_mono_decorated_lattice {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro x hx
  unfold idAt at hx ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem grpAt_le_of_imp (V : HSp D) {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : grpAt V P ≤ grpAt V P' := by
  unfold grpAt
  exact congGrp_mono' V (idAt_mono_decorated_lattice h)

def commProd {G : Type*} [Group G] (A B : Subgroup G) (h : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    rw [mul_assoc, ← mul_assoc b, h b hb a' ha']; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by rw [_root_.mul_inv_rev, h _ (B.inv_mem hb) _ (A.inv_mem ha)]⟩

private theorem idAt_inf_le_idAt_and (P P' : Pl D → Prop) : idAt D P ⊓ idAt D P' ≤ idAt D (fun p => P p ∧ P' p) := by
  intro x hxx
  have hx := (Ideal.mem_inf.1 hxx).1
  have hx' := (Ideal.mem_inf.1 hxx).2
  unfold idAt at hx hx' ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx hx' ⊢
  refine ⟨hx.1, fun w => ?_⟩
  by_cases hp : P w.1
  · exact hx'.2 ⟨w.1, fun h' => w.2 ⟨hp, h'⟩⟩
  · exact hx.2 ⟨w.1, hp⟩

private theorem congGrp_inf_le_congGrp_inf (V : HSp D) (I J : Ideal (AE D)) : congGrp V I ⊓ congGrp V J ≤ congGrp V (I ⊓ J) := by
  intro g hg
  have hI := (Subgroup.mem_inf.1 hg).1
  have hJ := (Subgroup.mem_inf.1 hg).2
  unfold congGrp at hI hJ ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hI hJ ⊢
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have eI := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hI i j
  have eJ := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hJ i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] at eI eJ ⊢
  split_ifs at eI eJ ⊢ with hij
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩

private theorem mem_grpAt_and_of_mem_grpAt (V : HSp D) {P P' : Pl D → Prop} {g : GA D V} (h : g ∈ grpAt V P) (h' : g ∈ grpAt V P') :
    g ∈ grpAt V (fun p => P p ∧ P' p) := by
  unfold grpAt at h h' ⊢
  exact congGrp_mono' V (idAt_inf_le_idAt_and P P') (congGrp_inf_le_congGrp_inf V _ _ ⟨h, h'⟩)

private theorem inK_congr_of_iff {V : HSp D} {L : Lat V} {P P' : Pl D → Prop} (h : ∀ p, P p ↔ P' p) (κ : GA D V) :
    InK V L P κ ↔ InK V L P' κ := by
  rw [show P = P' from funext fun p => propext (h p)]

private theorem mem_grpAt_of_inK {V : HSp D} {L : Lat V} {P : Pl D → Prop} {κ : GA D V} (h : InK V L P κ) : κ ∈ grpAt V P := by
  unfold InK at h
  exact h.1

theorem levels : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  intro D V L gP Q JG hL hdisj hJle hJc hJo
  obtain ⟨-, -, -, hQcle, -, -, -, -, hKQ, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q
  obtain ⟨-, -, -, -, hPcomm, ⟨e, he⟩, -, -, -, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V gP
  have hQP : ∀ p, p ∈ Q → p ∉ gP := fun p hp => Finset.disjoint_left.mp hdisj hp

  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hKQ L hL (· ∈ Q)

  obtain ⟨⟨K₃, hK₃, hK₃c, hK₃o⟩, -⟩ := hKQ L hL (fun p => p ∉ gP ∧ p ∉ Q)
  have hpq : ∀ p, (p ∉ gP ∧ p ∈ Q) ↔ p ∈ Q := fun p => ⟨And.right, fun h => ⟨hQP p h, h⟩⟩

  have hsplit : ∀ κ, InK V L (· ∉ gP) κ ↔
      ∃ a b, InK V L (· ∈ Q) a ∧ InK V L (fun p => p ∉ gP ∧ p ∉ Q) b ∧ κ = a * b := by
    intro κ
    refine ((hKQ L hL (· ∉ gP)).2 κ).trans ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).1 ha, hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).2 ha, hb, rfl⟩
  have hK₁le : K₁ ≤ grpAt V (· ∈ Q) := fun g hg => mem_grpAt_of_inK ((hK₁ g).1 hg)
  have hK₃le : K₃ ≤ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := fun g hg => mem_grpAt_of_inK ((hK₃ g).1 hg)
  have hJQ : grpAt V (· ∈ gP) ≤ grpAt V (· ∉ Q) := grpAt_le_of_imp V fun p hp hq => hQP p hq hp

  have hc : ∀ b ∈ JG, ∀ a ∈ K₃, b * a = a * b := fun b hb a ha =>
    hPcomm b (hJle hb) a (grpAt_le_of_imp V (fun p hp => hp.1) (hK₃le ha))
  have hmem : ∀ g, g ∈ commProd K₃ JG hc ↔ ∃ a ∈ K₃, ∃ b ∈ JG, g = a * b := fun g => Iff.rfl
  refine ⟨K₁, commProd K₃ JG hc, hK₁, hK₁le, ?_, hK₁c, ?_, hK₁o, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (hmem g).1 hg
    exact mul_mem (grpAt_le_of_imp V (fun p hp => hp.2) (hK₃le ha)) (hJQ (hJle hb))
  · have hset : (commProd K₃ JG hc : Set (GA D V)) =
        (fun p : GA D V × GA D V => p.1 * p.2) '' ((K₃ : Set (GA D V)) ×ˢ (JG : Set (GA D V))) := by
      ext g
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [hset]
    exact (hK₃c.prod hJc).image continuous_mul
  ·
    obtain ⟨φ, hφc, hφ, hφ1⟩ : ∃ φ : grpAt V (· ∉ Q) → grpAt V (· ∈ gP) × grpAt V (· ∉ gP),
        Continuous φ ∧ (∀ g : grpAt V (· ∉ Q), (g : GA D V) = ((φ g).1 : GA D V) * (φ g).2) ∧ φ 1 = 1 := by
      refine ⟨fun g => e.symm ⟨g, hQcle g.2⟩, ?_, ?_, ?_⟩
      · exact e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
      · intro g
        rw [← he, Homeomorph.apply_symm_apply]
      · rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [he]
        simp

    have h3 : ∀ g : grpAt V (· ∉ Q), ((φ g).2 : GA D V) ∈ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := by
      intro g
      have e2 : ((φ g).2 : GA D V) = ((φ g).1 : GA D V)⁻¹ * g := by
        rw [hφ g, inv_mul_cancel_left]
      refine mem_grpAt_and_of_mem_grpAt V (φ g).2.2 ?_
      rw [e2]
      exact mul_mem (inv_mem (hJQ (φ g).1.2)) g.2
    obtain ⟨ψ, hψc, hψ⟩ : ∃ ψ : grpAt V (· ∉ Q) → grpAt V (fun p => p ∉ gP ∧ p ∉ Q),
        Continuous ψ ∧ ∀ g : grpAt V (· ∉ Q), (ψ g : GA D V) = (φ g).2 :=
      ⟨fun g => ⟨(φ g).2, h3 g⟩, (continuous_subtype_val.comp (continuous_snd.comp hφc)).subtype_mk _, fun _ => rfl⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    have hU : ψ ⁻¹' ((K₃.subgroupOf (grpAt V (fun p => p ∉ gP ∧ p ∉ Q)) : Subgroup _) :
        Set (grpAt V (fun p => p ∉ gP ∧ p ∉ Q))) ∩
        (fun g => (φ g).1) ⁻¹' ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) ∈
        nhds (1 : grpAt V (· ∉ Q)) := by
      refine IsOpen.mem_nhds ((hK₃o.preimage hψc).inter (hJo.preimage (continuous_fst.comp hφc))) ⟨?_, ?_⟩
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ, hφ1]
        exact K₃.one_mem
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hφ1]
        exact JG.one_mem
    refine Filter.mem_of_superset hU ?_
    rintro g ⟨h1, h2⟩
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ] at h1
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf] at h2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmem]
    refine ⟨(φ g).2, h1, (φ g).1, h2, ?_⟩
    rw [hφ g]
    exact hPcomm _ (φ g).1.2 _ (φ g).2.2
  · intro g
    rw [hmem]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, (hK₃ a).1 ha, b, hb, rfl⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      exact ⟨κ, (hK₃ κ).2 hκ, k, hk, rfl⟩
  · intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨κ, hκ, k, hk, rfl⟩ := (hmem b).1 hb
      exact ⟨a * κ, (hsplit _).2 ⟨a, κ, (hK₁ a).1 ha, (hK₃ κ).1 hκ, rfl⟩, k, hk, (mul_assoc a κ k).symm⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := (hsplit κ).1 hκ
      exact ⟨a, (hK₁ a).2 ha, b * k, (hmem _).2 ⟨b, (hK₃ b).2 hb, k, hk, rfl⟩, mul_assoc a b k⟩

end GlobalTheory.CellLevels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAwayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  first | exact @GlobalTheory.CellLevels.levels | exact GlobalTheory.CellLevels.levels | (intros; apply GlobalTheory.CellLevels.levels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinLaw

theorem combAt_aconv {D : D7} {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) :
    ∀ l : List (WO S T →₀ ℂ), (∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) → GlobalTheory.FinPl.CombAt P (aconv l) := by
  intro l
  induction l with
  | nil =>
    intro _ u hu i j
    have h0 : aconv ([] : List (WO S T →₀ ℂ)) = Finsupp.single 0 1 := rfl
    rw [h0, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  | cons e l ih =>
    intro hl u hu
    have e1 : aconv (e :: l) = aconv [e, aconv l] := by
      apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := WO S T)
      rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_pair]
    rw [e1] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.QValOuter.mem_support_aconv_pair _ _ hu
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (hl e List.mem_cons_self a ha i j)
      (ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) b hb i j)

theorem comb_aconv_cons {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ)
    (l : List (WO S T →₀ ℂ)) (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum]
  have hG0 : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have hGa : ∀ u (a b : ℂ), (a + b) • heisO ψ S T u f = a • heisO ψ S T u f + b • heisO ψ S T u f :=
    fun u a b => add_smul _ _ _
  show (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).sum
    (fun u a => a • heisO ψ S T u f) = _
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finsupp.sum_single_index (hG0 _), GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (h x hx y hy)]

theorem comb_aconv_map {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (p : Fin r → GlobalTheory.FinPl.Pl D)
    (hp : Function.Injective p) (E : Fin r → WO S T →₀ ℂ) (hE : ∀ a, GlobalTheory.FinPl.CombAt (· = p a) (E a))
    (f : WO S T → ℂ) :
    ∀ L : List (Fin r), L.Nodup → comb ψ S T (aconv (L.map E)) f = L.foldr (fun a g => comb ψ S T (E a) g) f := by
  intro L
  induction L with
  | nil => intro _; exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    intro hL
    rw [List.map_cons, comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = p a)) (P' := fun v => ∃ b ∈ L, v = p b) ?_ (hE a x hx) ?_
    · rintro _ rfl ⟨b, hb, hab⟩
      exact (List.nodup_cons.1 hL).1 (hp hab ▸ hb)
    · exact combAt_aconv _ (L.map E) (fun e he => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
        exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun v hv => ⟨b, hb, hv⟩) (hE b u hu)) y hy

theorem eQ_comb_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ Ψ, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ → ∀ i, ∃ f, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f ∧ comb c.ψ _ _ (w.eQ j) Ψ = comb c.ψ _ _ ((F.Q i).eL j) f := by
  intro D c v t w F hc hv hP j hj Ψ hΨ i
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1)) P P' hd
  have hca : ∀ a, GlobalTheory.FinPl.CombAt (· = (F.Q a).q.v) ((F.Q a).eL j) := by
    intro a u hu r q'
    have := (F.Q a).hs
    exact (GlobalTheory.FinPl.FrameLat.idem_iff (F.Q a).q _).2 (((F.Q a).eL_at j ((F.Q a).s - j) (by omega)).1 u hu r q')
  have hdisj : ∀ a b : Fin F.r, a ≠ b → ∀ p, p = (F.Q a).q.v → ¬ p = (F.Q b).q.v := fun a b hab p ha hb =>
    hab (hP.inj (ha.symm.trans hb))
  let g : Fin F.r → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((F.Q a).eL j) f
  have hfold : comb c.ψ _ _ (w.eQ j) Ψ = (List.finRange F.r).foldr g Ψ := by
    rw [hP.eQ j hj, List.ofFn_eq_map]
    exact comb_aconv_map c.ψ (fun a => (F.Q a).q.v) hP.inj (fun a => (F.Q a).eL j) hca Ψ _ (List.nodup_finRange _)
  refine ⟨((List.finRange F.r).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) Ψ :=
      GlobalTheory.GSuppComb.vac_mono (fun p hp => by rw [hp]; exact (hP.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin F.r), (∀ a ∈ l, a ≠ i) →
        GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a l ih =>
        intro hl
        exact ((hI (· = (F.Q a).q.v) (· = (F.Q i).q.v) (hdisj a i (hl a List.mem_cons_self))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange F.r).mem_erase_iff.1 ha).1
  · rw [hfold]
    exact GlobalTheory.GSuppComb.foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ
      (List.mem_finRange i)

theorem local_scalar_law : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ), (ofSplit q).IsComp χS μS → (ofSplit q).IsComp χT μT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (e : WO S T →₀ ℂ) (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → (ofSplit q).IsCombAt ψ FS FT e Φ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∀ g gk h hk, (ofSplit q).IsLoc FS g gk → (ofSplit q).IsLoc FT h hk → ∀ z : ℂ, (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ = z • Φ → ω (g, h) (comb ψ S T e f) = z • comb ψ S T e f := by
  intro D k _ _ _ _ q hU ψ ψk hψ hch hcond S T χS χT ω hω μS μT cS cT Y Y' _ _ _ _ FS FT LS LT hLS hLT hFS hFT e Φ hΦ
    hcomb f hf g gk h hk hg hh z hz
  obtain ⟨Tm, hTm, hTO⟩ :=
    (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T FS FT ψ ψk hψ hch hcond LS LT hLS hLT hFS hFT).2 f hf
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  let Φs : SB (Matrix Y Y' k) := ⟨Φ, hΦ⟩
  have e1 : Tm Φs = comb ψ S T e f := by rw [hcomb.2 Tm hTm O Φs hO rfl, hTO O hO]
  have e2 := GlobalTheory.T.weilDatum_localModel_formula D k (ofSplit q) ψ S T χS χT ω hω μS μT cS cT Y Y' FS FT Tm hTm g gk h hk hg hh Φs (z • Φs)
    (by rw [Submodule.coe_smul]; exact hz.symm)
  rw [← e1, e2, map_smul]

theorem om_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ζ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (Φ : Matrix b a k → ℂ) :
    om (μ * ζ) g h Φ = ((ζ (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (((ζ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)) • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val]
  ring

variable {D : D7}

theorem isComp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ) (h' : p.IsComp χ' μ') :
    p.IsComp (χ * χ') (μ * μ') := fun x a ha => by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Circle.coe_mul, h x a ha, h' x a ha]

theorem isComp_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) : p.IsComp χ⁻¹ μ⁻¹ := fun x a ha => by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv, h x a ha]

theorem place_law (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t)
    (hc : c.Is) (ht : t.Is) (hv : v.Is) (hP : F.Pins w) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r)
    (cc : ℕ) (hcc : j + 1 + cc = (F.Q i).s + 1) (x : GL ((F.Q i).X (j + 1) ⊕ Fin cc) (F.Q i).k)
    (hx : x ∈ ((F.Q i).T.lev (j + 1) cc hcc).J) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, (F.Q i).gl (j + 1) cc hcc x) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) ((F.Q i).gl (j + 1) cc hcc x, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) =
          a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  have hs := (F.Q i).hs
  obtain ⟨d, rfl⟩ : ∃ d, cc = d + 1 := ⟨cc - 1, by omega⟩
  have hjd : j + (d + 1) = (F.Q i).s := by omega
  have hjd' : j + 1 + d = (F.Q i).s := by omega
  obtain ⟨χz, hV, hW, hV', hW'⟩ := hP.mid j σ h
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (F.Q i).q) χz
  refine ⟨(((F.Q i).T.lev (j + 1) (d + 1) hcc).lam ⟨x, hx⟩ : ℂ) * (((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ),
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP j (by omega) Ψ₁ h₁ i
    rw [hfe]
    have hw := (t.sBF j (σ + 1) h).weil
    rw [(ht.sBF j (σ + 1) h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu j (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χV (((F.Q i).T.mu (j + 1))⁻¹ * ζ) := by
      rw [hV]; exact isComp_mul _ hmu hζ
    have cT : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χW ((F.Q i).T.mu (j + 1))⁻¹ := by
      rw [hW]; exact hmu
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY j (d + 1 + 1) (by omega)) 1 1 := by
      have := (F.Q i).gl_loc j (d + 1 + 1) (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om j) hw _ _ cS cT _ _
      ((F.Q i).FY j (d + 1 + 1) (by omega)) ((F.Q i).FY (j + 1) (d + 1) (by omega)) (v.N j) (v.N (j + 1))
      (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) ((F.Q i).latY j (d + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).eL j) ((F.Q i).T.Phi j (d + 1) hjd)
      ((F.Q i).reg.1 j (d + 1) hjd) ((F.Q i).eL_at j (d + 1) hjd) f hf 1 1 _ x h1 ((F.Q i).gl_loc _ _ _ x) _ ?_
    rw [map_one, map_one, Units.val_one, one_smul, mul_inv, inv_inv, om_twist, ((F.Q i).laws.1 j (d + 1) hjd).2 ⟨x, hx⟩,
      smul_smul]
    congr 1
    simp only [map_one, MonoidHom.inv_apply, inv_one, Units.val_one, one_mul, inv_inv, mul_inv, Units.val_inv_eq_inv_val]
    ring
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP (j + 1) (by omega) Ψ₂ h₂ i
    rw [hfe]
    have hw := (t.sFB j σ h).weil
    rw [(ht.sFB j σ h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu (j + 1) (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χV ((F.Q i).T.mu (j + 1 + 1))⁻¹ := by
      rw [hV']; exact hmu
    have cT : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χW (((F.Q i).T.mu (j + 1 + 1))⁻¹ * ζ) := by
      rw [hW']; exact isComp_mul _ hmu hζ
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY (j + 1 + 1) d (by omega)) 1 1 := by
      have := (F.Q i).gl_loc (j + 1 + 1) d (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om (j + 1)) hw _ _
      cS cT _ _ ((F.Q i).FY (j + 1) (d + 1) (by omega)) ((F.Q i).FY (j + 1 + 1) d (by omega)) (v.N (j + 1))
      (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).latY (j + 1 + 1) d (by omega)) ((F.Q i).eL (j + 1))
      ((F.Q i).T.Phi (j + 1) d hjd') ((F.Q i).reg.1 (j + 1) d hjd') ((F.Q i).eL_at (j + 1) d hjd') f hf _ x 1 1
      ((F.Q i).gl_loc _ _ _ x) h1 _ ?_
    rw [inv_inv, ((F.Q i).laws.1 (j + 1) d hjd').1 ⟨x, hx⟩, smul_smul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem inverse_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  intro D c v t w F hc ht hv _ hP j σ h k hk
  refine Subgroup.iSup_induction (fun i => GlobalTheory.QuotientFiniteLevel.locK F j σ h i)
    (C := fun k => ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)
    (show k ∈ ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i from hk) ?_ ?_ ?_
  · intro i k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hk
    exact place_law D c v t w F hc ht hv hP j σ h i _ _ x hx
  · refine ⟨1, one_ne_zero, fun Ψ₁ Ψ₂ _ _ => ⟨?_, ?_⟩⟩
    · rw [show ((1 : GA D (c.V j)), (1 : GA D (c.V (j + 1)))) = 1 from rfl, map_one, inv_one, one_smul]; rfl
    · rw [show ((1 : GA D (c.V (j + 1))), (1 : GA D (c.V (j + 1 + 1)))) = 1 from rfl, map_one, one_smul]; rfl
  · rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a * b, mul_ne_zero ha hb, fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
    · have e : ((1 : GA D (c.V j)), x * y) = (1, x) * (1, y) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).1, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).1, smul_smul, mul_inv,
        mul_comm b⁻¹]
    · have e : (x * y, (1 : GA D (c.V (j + 1 + 1)))) = (x, 1) * (y, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).2, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).2, smul_smul, mul_comm b a]

end GlobalTheory.QFinLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  first | exact @GlobalTheory.QFinLaw.inverse_laws | exact GlobalTheory.QFinLaw.inverse_laws | (intros; apply GlobalTheory.QFinLaw.inverse_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmoothKFiniteUnitHighestWeightVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmoothKFiniteUnitHighestWeightVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealZetaSmoothHi

theorem exists_smooth_highestUnit : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ w : M.H τ, w ∈ M.sm τ ∧ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ ∧ IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) w := by
  intro h D V S M τ
  obtain ⟨hC, hN, hU, hI, -, ⟨K, hK⟩, -⟩ := M.ds τ
  haveI := hC
  obtain ⟨v, hv, hv0, hw⟩ := hK.2.2.2.1
  have hwS : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := K.smul_mem _ hv
  have hKf : IsKFin (M.ε τ) (M.σ τ) (((‖v‖⁻¹ : ℝ) : ℂ) • v) := ⟨K, hK.1, hwS, hK.2.1⟩
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.subset_span ?_
    exact h.smoothVec hU hI hKf (M.fr_unit τ) (M.fr_gram τ)
  · exact Submodule.subset_span hKf
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
  · exact (le_sSup hK : K ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) hwS
  · intro θ hθ
    rw [map_smul, hw θ hθ, smul_comm]

end GlobalTheory.RealZetaSmoothHi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmoothKFiniteUnitHighestWeightVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ w : M.H τ, w ∈ M.sm τ ∧ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ ∧ IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) w := by
  first | exact @GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit | exact GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit | (intros; apply GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseFn

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.Mem.Col2.DetSpec

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [StarRing E] {n : ℕ}

variable {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem fn_eq {p : DecoF E n ST SG Q} {k : GL (Fin n) (AfE F E)} (h : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (P : ST)
    (r : Fin n) (hr : r.1 + 1 = n) (c : 𝓞 E)
    (hrow : ∀ i, HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r i)) (if i = r then Ideal.Quotient.mk P.1.asIdeal c else 0))
    (x : Fin n → 𝓞 E) : p.deco.1.f P (fun i => (x i : E)) = Ideal.Quotient.mk P.1.asIdeal (c * x r) := by
  refine HasRes.unique (h.f P _ (hN ▸ (Formalism.L2.Col.mem_stdLat _).2 fun i => ⟨x i, rfl⟩) r hr) ?_
  choose ρ hρ hv using hrow
  refine ⟨∑ i, ρ i * x i, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, hρ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE]
      rw [← Finset.sum_sub_distrib]
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
      show Valued.v (_ * algebraMap E (P.1.adicCompletion E) (algebraMap (𝓞 E) E (x i)) - _) < 1
      rw [← _root_.sub_mul, map_mul, valued_algebraMap]
      exact (mul_le_of_le_one_right' (P.1.valuation_le_one (x i))).trans_lt (hv i)

end Loc

end GlobalTheory.BaseFn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMulHeightPowOfBoundedFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMulHeightPowOfBoundedFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.realZeta_integrable_mul_heightPow : ∀ {G : Type} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G] (μ : Measure G) (z m : G → ℂ) (H : G → ℝ) (C : ℝ) (b t : ℕ), Integrable z μ → Integrable m μ → Continuous H → (∀ g, 0 < H g ∧ H g ≤ 1) → t ≤ b → (∀ g, ‖z g‖ ≤ C * H g ^ ((b : ℝ) / 2) * ‖m g‖) → Integrable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (t : ℂ) / 2)) μ := by
  intro G _ _ _ μ z m H C b t hz hm hH hpos htb hbound
  have hmeas : AEStronglyMeasurable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0:ℝ):ℂ) - (t:ℂ)/2)) μ := by
    refine hz.aestronglyMeasurable.mul ?_
    exact ((Complex.measurable_ofReal.comp hH.measurable).pow_const _).aestronglyMeasurable
  refine Integrable.mono' (hm.norm.const_mul (max C 0)) hmeas ?_
  refine Filter.Eventually.of_forall (fun g => ?_)
  obtain ⟨h0, h1⟩ := hpos g
  have hre : (((0:ℝ):ℂ) - (t:ℂ)/2).re = -(t:ℝ)/2 := by simp; ring
  have hcpow : ‖((H g : ℝ) : ℂ) ^ (((0:ℝ):ℂ) - (t:ℂ)/2)‖ = H g ^ (-(t:ℝ)/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h0, hre]
  rw [norm_mul, hcpow]
  have hw : 0 ≤ H g ^ (-(t:ℝ)/2) := Real.rpow_nonneg h0.le _
  have hprod : H g ^ ((b:ℝ)/2) * H g ^ (-(t:ℝ)/2) = H g ^ (((b:ℝ) - t)/2) := by
    rw [← Real.rpow_add h0]; ring_nf
  have htb' : (t:ℝ) ≤ b := by exact_mod_cast htb
  have hle1 : H g ^ (((b:ℝ) - t)/2) ≤ 1 := Real.rpow_le_one h0.le h1 (by linarith)
  have hnn : 0 ≤ H g ^ (((b:ℝ) - t)/2) := Real.rpow_nonneg h0.le _
  calc ‖z g‖ * H g ^ (-(t:ℝ)/2) ≤ C * H g ^ ((b:ℝ)/2) * ‖m g‖ * H g ^ (-(t:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (hbound g) hw
    _ = C * (H g ^ ((b:ℝ)/2) * H g ^ (-(t:ℝ)/2)) * ‖m g‖ := by ring
    _ = C * H g ^ (((b:ℝ) - t)/2) * ‖m g‖ := by rw [hprod]
    _ ≤ max C 0 * ‖m g‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc C * H g ^ (((b:ℝ) - t)/2) ≤ max C 0 * H g ^ (((b:ℝ) - t)/2) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
          _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hle1 (le_max_right _ _)
          _ = max C 0 := mul_one _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMulHeightPowOfBoundedFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor : ∀ {G : Type} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G] (μ : Measure G) (z m : G → ℂ) (H : G → ℝ) (C : ℝ) (b t : ℕ), Integrable z μ → Integrable m μ → Continuous H → (∀ g, 0 < H g ∧ H g ≤ 1) → t ≤ b → (∀ g, ‖z g‖ ≤ C * H g ^ ((b : ℝ) / 2) * ‖m g‖) → Integrable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (t : ℂ) / 2)) μ := by
  first | exact @GlobalTheory.realZeta_integrable_mul_heightPow | exact GlobalTheory.realZeta_integrable_mul_heightPow | (intros; apply GlobalTheory.realZeta_integrable_mul_heightPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthSumSp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def col {V W : HSpace E} {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E) :
    Matrix (Fin (GlobalTheory.Doubling.hsum V W).rank) (Fin k) E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem col_gram {V W : HSpace E} {k l : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E)
    (X' : Matrix (Fin V.rank) (Fin l) E) (Y' : Matrix (Fin W.rank) (Fin l) E) :
    (col X Y)ᴴ * (GlobalTheory.Doubling.hsum V W).gram * col X' Y' = Xᴴ * V.gram * X' + Yᴴ * W.gram * Y' := by
  rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, col, col, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp

def orthSumDec (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := col 1 0
  iB := col 0 1
  isoA := by rw [col_gram]; simp
  isoB := by rw [col_gram]; simp
  orth := by rw [col_gram]; simp
  rank_add := rfl

@[reducible] def posSp (D : D7) (ρ : ℕ) : HSp D where
  V := Fin ρ → D.host.E
  hT := Formalism.BasicNotions.Examples₂.diagForm ρ (fun _ => false)
  herm := Formalism.BasicNotions.Examples₂.diagForm_isSymm ρ _
  nondeg := Formalism.BasicNotions.Examples₂.diagForm_nondeg ρ _
  rank := ρ
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := fun _ => (ρ, 0)
  L0 := Formalism.BasicNotions.Examples₂.stdLat ρ
  standardTuple_isLattice := Formalism.BasicNotions.Examples₂.stdLat_isLattice ρ
  baseLattice_isUnimodular := Formalism.BasicNotions.Examples₂.stdLat_unimod Formalism.BasicNotions.Examples₂.star_isIntegral ρ _

theorem posSp_sigOK (D : D7) (ρ : ℕ) : (posSp D ρ).SigOK :=
  Formalism.BasicNotions.Examples₂.posSpace_sigOK (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ

theorem posSp_gram (D : D7) (ρ : ℕ) : (posSp D ρ).gram = 1 := by
  funext i j
  rw [Matrix.one_apply]
  refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ (fun _ => false) ρ 0 i j).trans ?_
  simp [Formalism.BasicNotions.Examples₂.sgn]

@[reducible] def hypSp (D : D7) (ρ : ℕ) : HSp D :=
  GlobalTheory.Doubling.hdbl (posSp D ρ)

theorem hypSp_sigOK (D : D7) (ρ : ℕ) : (hypSp D ρ).SigOK :=
  GlobalTheory.Doubling.sigOK_hdbl (posSp_sigOK D ρ)

theorem hypSp_sig (D : D7) (ρ : ℕ) (τ) : (hypSp D ρ).sig τ = (ρ, ρ) := by
  show (ρ, 0) + (0, ρ) = (ρ, ρ)
  simp

def hypSumDec (D : D7) (A : HSp D) (ρ : ℕ) : HypDec (GlobalTheory.Doubling.hsum A (hypSp D ρ)) A ρ where
  e := col 0 (col (1 : Matrix (Fin ρ) (Fin ρ) D.host.E) (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))
  e' := col 0 (col ((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E)) (-((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))))
  i₀ := col 1 0
  ee := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e' := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]
    simp [Matrix.smul_eq_diagonal_mul, ← two_mul]
  iso := by rw [col_gram]; simp
  i₀e := by rw [col_gram]; simp
  i₀e' := by rw [col_gram]; simp
  rank_add := by show A.rank + 2 * ρ = A.rank + (ρ + ρ); omega

theorem exists_orthSum_hypSum : ∀ (D : D7), (∀ A L : HSp D, A.SigOK → L.SigOK → ∃ (S : HSp D) (_ : OrthDec S A L), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + L.sig τ) ∧ ∀ (A : HSp D) (ρ : ℕ), A.SigOK → ∃ (S : HSp D) (_ : HypDec S A ρ), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + (ρ, ρ) := by
  intro D
  refine ⟨fun A L hA hL => ⟨_, orthSumDec D A L, GlobalTheory.Doubling.sigOK_hsum hA hL, fun τ => rfl⟩,
    fun A ρ hA => ⟨_, hypSumDec D A ρ, GlobalTheory.Doubling.sigOK_hsum hA (hypSp_sigOK D ρ), fun τ => ?_⟩⟩
  show A.sig τ + (hypSp D ρ).sig τ = _
  rw [hypSp_sig]

end GlobalTheory.OrthSumSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalSum_and_hyperbolicSum_spaces : ∀ (D : D7), (∀ A L : HSp D, A.SigOK → L.SigOK → ∃ (S : HSp D) (_ : OrthDec S A L), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + L.sig τ) ∧ ∀ (A : HSp D) (ρ : ℕ), A.SigOK → ∃ (S : HSp D) (_ : HypDec S A ρ), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + (ρ, ρ) := by
  first | exact @GlobalTheory.OrthSumSp.exists_orthSum_hypSum | exact GlobalTheory.OrthSumSp.exists_orthSum_hypSum | (intros; apply GlobalTheory.OrthSumSp.exists_orthSum_hypSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCopy
noncomputable section

namespace GlobalTheory.SeeSaw.TopLevel

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix
open scoped TensorProduct

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]

theorem lev_iff (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E}
    (hJ' : J' = 1) (hJ : J = 1) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (hL : S.Lb = Formalism.L2.Col.stdLat E n) {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n') (ht : 0 < t) (hn : n = r + s * t) {SG : Finset (Pl E)}
    (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (hR : RdLev hc S.U S.chi Set.univ (parFam h t s P χ) emb) (P' : LevelP SG r ℂ)
    (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K))
    (hcg : ∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K))
    (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hgy : ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) :
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ ↔ g ∈ lev hc 1 1 (parDat h t s P χ) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    refine and_congr Iff.rfl ((hH _).trans ⟨fun h w _ => h w, fun h w => h w (Set.mem_univ w)⟩)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨h1, h2, -, h4⟩
      exact (hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv).1.2 fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w)
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      refine ⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩
      have := (hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv).1.1 hy w
      rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  have h3 := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 h4
  obtain ⟨r1, r2⟩ := hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ g : ℂˣ) : ℂ) = emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) := by
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy (r1.1 hy)]
  show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
  rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
    (isOfFinOrder_of_finite ⟨_, r1.1 hy w⟩)).norm_eq_one
  refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
  exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
    (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))

theorem exists_copy {A : Type} [CommRing A] {n n' : ℕ} (e : n' = n) (g : GL (Fin n') A) :
    ∃ y : GL (Fin n) A, ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j) := by
  subst e
  exact ⟨g, fun _ _ => rfl⟩


attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in
theorem rd_all {B : Base} {X : PreX B.toPre} (I : TC B X) [NeZero (B.R.N B.R.m - 1)] {Lb U chi y lat st}
    (h : I.ReadsP I.mu0 Lb U chi y lat st) (c : (I.stX I.mu0).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi Set.univ (rowTyG I.Ch I.Ps) B.embLL :=
  haveI : IsEmpty (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; infer_instance
  rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := Set.univ) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup I.mu0))
    B.embLL (U := U) (chi := chi) (y := y c) (k := 1) (p := ((I.stX I.mu0).rep c).1.1) (by rw [mul_one]; exact h.pt c)
    (fun v _ => map_one _) (fun P hP => absurd hP (Finset.notMem_empty _))
    (fun x q hq => h.lev c x q (by rwa [mul_one] at hq))
    (fun x κ h1 h2 => h.chr c x κ h1 (by rwa [mul_one] at h2))

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.SeeSaw.TopLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOneCombSphLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.SphOne

theorem isOneComb_sph_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), L.J = KO k _ → (∀ j, L.lam j = 1) → IsOneComb ψ ν P L 1 (Finsupp.single 1 1) ∧ prX (Cgrp L.J 1) = KO k n := by
  intro k _ _ _ _ _ _ n _ _ c P h1 h2 ψ _ hψ ν hν L hJ hlam
  obtain ⟨J, lam⟩ := L
  dsimp only at hJ hlam
  subst hJ
  have e : lam = 1 := MonoidHom.ext fun j => hlam j
  subst e
  refine ⟨?_, GlobalTheory.QPl.PinTest.prX_KO⟩
  exact GlobalTheory.QPl.PinTest.isOneComb_sph hψ hν h1 h2

end GlobalTheory.QPl.SphOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDLatY

theorem exists_selfDual_latY : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  intro D L hT Gi Gl Kc Yd cX ex W hp j hj
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  exact ⟨(pk W).ΛY j, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D (Yc D j) ((pk W).βY j) ((pk W).ΛY j) _ (hC.lev.βY j hj)⟩

end GlobalTheory.SDLatY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_self_dual_lattice_chain : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  first | exact @GlobalTheory.SDLatY.exists_selfDual_latY | exact GlobalTheory.SDLatY.exists_selfDual_latY | (intros; apply GlobalTheory.SDLatY.exists_selfDual_latY <;> assumption)
end
end

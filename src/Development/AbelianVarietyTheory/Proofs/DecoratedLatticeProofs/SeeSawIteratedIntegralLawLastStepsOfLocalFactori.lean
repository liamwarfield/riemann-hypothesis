module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLastTwoSteps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsAllTwistPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsAllTwistPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QLastCore

theorem symplO_eq_zero_of_disj : ∀ (D : D7) (S T : HSp D) (P P' : GlobalTheory.FinPl.Pl D → Prop), (∀ x, P x → ¬ P' x) → ∀ x y : WO S T, GlobalTheory.FinPl.MxAt P x → GlobalTheory.FinPl.MxAt P' y → symplO S T x y = 0 := by
  intro D S T P P' hPP x y hx hy
  have hz : ∀ a b : AE D, a ∈ GlobalTheory.FinPl.idAt D P → b ∈ GlobalTheory.FinPl.idAt D P' → b * a = 0 := by
    intro a b ha hb
    have m1 : b * a ∈ GlobalTheory.FinPl.idAt D P := Ideal.mul_mem_left _ _ ha
    have m2 : b * a ∈ GlobalTheory.FinPl.idAt D P' := Ideal.mul_mem_right _ _ hb
    rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at m1 m2
    refine GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ m1.1 fun w => ?_
    by_cases hw : P w
    · exact m2.2 w (hPP w hw)
    · exact m1.2 w hw
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * x d a = 0 := hz _ _ (hx d a) (GlobalTheory.LastOpPf.cA_mem_idAt (hy c b))
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a
        = incA D (S.gram⁻¹ a b) * incA D (T.gram c d) * (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem half_one_sub_of_ne : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k'), q.v ≠ q'.v → ∀ (m n : ℕ) (u : Mx D m n), IsHalf (q'.e + cA D q'.e) u → IsHalf (1 - (q.e + cA D q.e)) u := by
  intro D k k' _ _ _ _ _ _ _ _ q q' hne m n u hu i j
  obtain ⟨ε, hε, hs⟩ := q.above
  obtain ⟨ε', hε', hs'⟩ := q'.above
  have h1 : u i j ∈ GlobalTheory.FinPl.idAt D (· = q'.v) := ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q'.v ε' hε').1 _).2 (hs' ▸ hu i j)
  have h2 : u i j ∈ GlobalTheory.FinPl.idAt D (· ≠ q.v) :=
    PinEx.idAt_mono (fun x (hx : x = q'.v) => hx ▸ fun e => hne e.symm) h1
  have h3 := (GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).2 _ h2
  rw [sub_mul, one_mul, hs, h3, sub_zero]

theorem comb_single_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), comb ψ S T (Finsupp.single 0 1) f = f := by
  intro D ψ S T f
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  have hh : hO S T w 0 = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, hh]

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    AddMonoidAlgebra.ofCoeff (aconv (e :: l)) = AddMonoidAlgebra.ofCoeff e * AddMonoidAlgebra.ofCoeff (aconv l) := by
  rw [AddMonoidAlgebra.mul_def]
  change AddMonoidAlgebra.ofCoeff (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)) = _
  simp only [AddMonoidAlgebra.ofCoeff_finsuppSum, AddMonoidAlgebra.ofCoeff_single, AddMonoidAlgebra.coeff_ofCoeff]

theorem aconv_nil {G : Type} [AddMonoid G] : AddMonoidAlgebra.ofCoeff (aconv ([] : List (G →₀ ℂ))) = 1 := rfl

theorem conv_alg : (∀ (G : Type) [AddCommMonoid G] (c d : G →₀ ℂ) (l : List (G →₀ ℂ)), aconv (aconv [c, d] :: l) = aconv (c :: d :: l)) ∧ (∀ (G : Type) [AddMonoid G] (c : G →₀ ℂ), aconv [c] = c) ∧ (∀ (G : Type) [AddMonoid G] (l : List (G →₀ ℂ)), aconv (Finsupp.single 0 1 :: l) = aconv l) ∧ (∀ (G : Type) [AddMonoid G] (l : List (G →₀ ℂ)) (H : AddSubmonoid G), (∀ x ∈ l, ∀ g ∈ x.support, g ∈ H) → ∀ g ∈ (aconv l).support, g ∈ H) ∧ (∀ (G : Type) [Monoid G] (l : List (G →₀ ℂ)) (H : Submonoid G), (∀ x ∈ l, ∀ g ∈ x.support, g ∈ H) → ∀ g ∈ (conv l).support, g ∈ H) := by
  classical
  refine ⟨fun G _ c d l => ?_, fun G _ c => ?_, fun G _ l => ?_, fun G _ l H hl => ?_, fun G _ l H hl => ?_⟩
  · apply AddMonoidAlgebra.ofCoeff_injective
    rw [aconv_cons, aconv_cons, aconv_cons, aconv_cons, aconv_cons, aconv_nil, mul_one, mul_assoc]
  · apply AddMonoidAlgebra.ofCoeff_injective
    rw [aconv_cons, aconv_nil, mul_one]
  · apply AddMonoidAlgebra.ofCoeff_injective
    rw [aconv_cons]
    exact one_mul _
  · induction l with
    | nil =>
      intro g hg
      have e : aconv ([] : List (G →₀ ℂ)) = Finsupp.single 0 1 := rfl
      rw [e] at hg
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
      exact H.zero_mem
    | cons e l ih =>
      intro g hg
      change g ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support at hg
      obtain ⟨x, hx, hg1⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
      obtain ⟨y, hy, hg2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg1)
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg2)]
      exact H.add_mem (hl e (List.mem_cons_self ..) x hx) (ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) y hy)
  · induction l with
    | nil =>
      intro g hg
      have e : conv ([] : List (G →₀ ℂ)) = Finsupp.single 1 1 := rfl
      rw [e] at hg
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
      exact H.one_mem
    | cons e l ih =>
      intro g hg
      change g ∈ (e.sum fun g a => (conv l).sum fun h b => Finsupp.single (g * h) (a * b)).support at hg
      obtain ⟨x, hx, hg1⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
      obtain ⟨y, hy, hg2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg1)
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg2)]
      exact H.mul_mem (hl e (List.mem_cons_self ..) x hx) (ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) y hy)

theorem sum_conv_cons : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (a : GA D S →₀ ℂ) (l : List (GA D S →₀ ℂ)) (X : WO S T → ℂ), ∑ g ∈ (conv (a :: l)).support, conv (a :: l) g • om (g, 1) X = ∑ g ∈ a.support, a g • om (g, 1) (∑ g' ∈ (conv l).support, conv l g' • om (g', 1) X) := by
  intro D S T om a l X
  change (a.sum fun g x => (conv l).sum fun h y => Finsupp.single (g * h) (x * y)).sum (fun g x => x • om (g, 1) X) =
    a.sum fun g x => x • om (g, 1) ((conv l).sum fun g' y => y • om (g', 1) X)
  rw [Finsupp.sum_sum_index (h := fun g x => x • om (g, 1) X) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_sum_index (h := fun g x => x • om (g, 1) X) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum_single_index, zero_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [smul_smul]
  congr 1
  rw [show ((g * h, (1 : GA D T)) : GA D S × GA D T) = (g, 1) * (h, 1) by simp, map_mul]
  rfl

theorem comb_aconv_cons : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ)) (f : WO S T → ℂ), (∀ x ∈ a.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) → comb ψ S T (aconv (a :: l)) f = comb ψ S T a (comb ψ S T (aconv l) f) := by
  intro D ψ S T a l f hs
  change (a.sum fun g x => (aconv l).sum fun h y => Finsupp.single (g + h) (x * y)).sum (fun u b => b • heisO ψ S T u f) =
    a.sum fun g x => x • heisO ψ S T g ((aconv l).sum fun h y => y • heisO ψ S T h f)
  rw [Finsupp.sum_sum_index (h := fun u b => b • heisO ψ S T u f) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun g hg => ?_
  rw [Finsupp.sum_sum_index (h := fun u b => b • heisO ψ S T u f) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum_single_index, zero_smul]
  simp only [Finsupp.sum]
  rw [GlobalTheory.HeisComb.heisO_finset_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [GlobalTheory.WeilVacMove.heisO_heisO, smul_smul, smul_smul]
  have h0 : symplOH S T g h = 0 := by unfold symplOH; rw [hs g hg h hh, mul_zero]
  rw [h0, AddChar.map_zero_eq_one]
  simp

theorem sum_om_comb_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (b : GA D S →₀ ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ g ∈ b.support, ∀ u ∈ e.support, actO S T g 1 u = u) → ∑ g ∈ b.support, b g • om (g, 1) (comb ψ S T e f) = comb ψ S T e (∑ g ∈ b.support, b g • om (g, 1) f) := by
  intro D ψ S T χS χT om hw b e f hf hact
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.smul_sum, GlobalTheory.HeisComb.heisO_finset_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun g hg => ?_
  rw [hw.om_heis g 1 u f hf, hact g hg u hu, smul_comm]

theorem actO_eq_of_disj : ∀ (D : D7) (S T : HSp D) (P P' : GlobalTheory.FinPl.Pl D → Prop), (∀ x, P x → ¬ P' x) → ∀ g ∈ GlobalTheory.FinPl.grpAt S P, ∀ u : WO S T, GlobalTheory.FinPl.MxAt P' u → actO S T g 1 u = u := by
  intro D S T P P' hPP g hg u hu
  have hz : ∀ a b : AE D, a ∈ GlobalTheory.FinPl.idAt D P → b ∈ GlobalTheory.FinPl.idAt D P' → b * a = 0 := by
    intro a b ha hb
    have m1 : b * a ∈ GlobalTheory.FinPl.idAt D P := Ideal.mul_mem_left _ _ ha
    have m2 : b * a ∈ GlobalTheory.FinPl.idAt D P' := Ideal.mul_mem_right _ _ hb
    rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at m1 m2
    refine GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ m1.1 fun w => ?_
    by_cases hw : P w
    · exact m2.2 w (hPP w hw)
    · exact m1.2 w hw
  have hg' : g⁻¹ ∈ GlobalTheory.FinPl.grpAt S P := inv_mem hg
  have hm : ∀ i k, Formalism.L2.Theta.mt S g⁻¹ i k - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i k ∈ GlobalTheory.FinPl.idAt D P := by
    intro i k
    have h1 := MonoidHom.mem_ker.1 hg'
    have h2 := congrArg (fun x : GL (Fin S.rank) (AE D ⧸ GlobalTheory.FinPl.idAt D P) => x.val i k) h1
    change Ideal.Quotient.mk _ (Formalism.L2.Theta.mt S g⁻¹ i k) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ GlobalTheory.FinPl.idAt D P)) i k at h2
    rw [← Ideal.Quotient.eq, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  unfold actO
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, Matrix.one_mul]
  ext i k
  rw [show Formalism.L2.Theta.mt S g⁻¹ = 1 + (Formalism.L2.Theta.mt S g⁻¹ - 1) by abel, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_zero (fun l _ => ?_), add_zero]
  exact hz _ _ (by simpa using hm l k) (hu i l)

theorem s_eq {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) : Q.s = j := by
  have := Q.hs; omega

theorem oneplace_at {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (hc : c.Is) (hv : v.Is)
    (j : ℕ) (hj : Q.s = j) (h : j + 2 * 0 + 2 = D.R.m) (hr : c.Lz.rank = 1)
    (hτ : (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram)
    (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) (hs₁ : s₁.χW = χ j)
    (om : GA D (c.V j) × GA D (c.V (j + 1)) →* Module.End ℂ (WO (c.V j) (c.V (j + 1)) → ℂ)) (hom : s₁.om = om)
    (oma omb) (ha : IsWeilDatumO c.ψ (c.X j) (c.X (j + 1)) (χ j) (χ j) oma)
    (hb : IsWeilDatumO c.ψ (c.X (j + 1)) (c.X (j + 1 + 1)) (χ (j + 1)) (χ (j + 1)) omb)
    (c₁ : WO (c.X j) (c.X (j + 1)) →₀ ℂ) (c₂ : WO (c.X (j + 1)) (c.X (j + 1 + 1)) →₀ ℂ)
    (h₁ : ∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) (h₂ : ∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u)
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ)
    (hΨ₁ : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Q.q.v) Ψ₁)
    (hΨ₂ : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· = Q.q.v) Ψ₂)
    (φ : GA D (c.X j) → ℂ) (hφ : IsContAut (c.X j) φ) (α : Q.Ch j) (u : Q.Ch (j + 1 + 1)) :
    (Q.idx (j + 1) : ℂ) • c.bl j oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst j h (v.τ j h) s₁
      (∑ g ∈ (Q.εL j α).support, Q.εL j α g • om (g, 1) (comb c.ψ _ _ (Q.eL j) Ψ₁)) (comb c.ψ _ _ (Q.eT j h) Ψ₂))) =
      ∑ y, Q.wt (j + 1) y • c.bl j oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL j α y]) (aconv [c₂, Q.dL (j + 1) y u])
        (c.lst j h (v.τ j h) s₁ Ψ₁ Ψ₂)) := by
  subst hj hom
  have e : Q.eT Q.s h = Q.eLT := rfl
  rw [e, GlobalTheory.T.seeSaw_twistPlace_last_two_steps D c v χ Q hc hv h hr hτ s₁ hs₁ oma omb ha hb c₁ c₂ h₁ h₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Q.wt_pen y, smul_smul]

theorem half_mx {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {m n : ℕ} {u : Mx D m n} (hu : IsHalf (q.e + cA D q.e) u) (P : GlobalTheory.FinPl.Pl D → Prop)
    (hP : P q.v) : GlobalTheory.FinPl.MxAt P u :=
  fun i j => PinEx.idAt_mono (fun x (hx : x = q.v) => hx ▸ hP) (PinEx.mem_idAt_of_supp q (hu i j))

theorem mx_inf {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : GlobalTheory.FinPl.MxAt P u) :
    u.map (infPart D) = 0 := by
  ext i j
  have := hu i j
  simp only [GlobalTheory.FinPl.idAt, Submodule.mem_inf, RingHom.mem_ker] at this
  simpa using this.1

def mxSub {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (m n : ℕ) : AddSubmonoid (Mx D m n) where
  carrier := {u | GlobalTheory.FinPl.MxAt P u}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)

def halfSub {D : D7} (e : AE D) (m n : ℕ) : AddSubmonoid (Mx D m n) where
  carrier := {u | IsHalf e u}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun ha hb i j => by simp only [Matrix.add_apply, mul_add, ha i j, hb i j]

section Facts
variable {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m)
include h

theorem eL_half : ∀ u ∈ (Q.eL j).support, IsHalf (Q.q.e + cA D Q.q.e) u := by
  have hs := s_eq Q h; subst hs; exact (Q.eL_at Q.s 0 rfl).1

theorem eT_half : ∀ u ∈ (Q.eT j h).support, IsHalf (Q.q.e + cA D Q.q.e) u := by
  have hs := s_eq Q h; subst hs; exact Q.eLT_at.1

theorem dL_half (α : Q.Ch j) (y : Q.Ch (j + 1)) : ∀ u ∈ (Q.dL j α y).support, IsHalf (Q.q.e + cA D Q.q.e) u := by
  have hs := s_eq Q h; subst hs; exact (Q.dL_pen α y).1

theorem dL_half' (y : Q.Ch (j + 1)) (u' : Q.Ch (j + 1 + 1)) :
    ∀ u ∈ (Q.dL (j + 1) y u').support, IsHalf (Q.q.e + cA D Q.q.e) u := by
  have hs := s_eq Q h; subst hs; exact (Q.dL_top y u').1

theorem εL_grp (α : Q.Ch j) : ∀ g ∈ (Q.εL j α).support, ∀ P : GlobalTheory.FinPl.Pl D → Prop, P Q.q.v → g ∈ GlobalTheory.FinPl.grpAt (c.V j) P := by
  have hs := s_eq Q h; subst hs
  intro g hg P hP
  obtain ⟨e, -, he⟩ := Q.εL_at Q.s 0 h 0 rfl α
  rw [he] at hg
  classical
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  exact GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D Q.k Q.q _ _ (Q.gl_loc Q.s (0 + 1) _ x).1 P hP

end Facts

theorem gen_mem_idAt' {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (α : Af D.host.F) (hα : ∀ w, ¬ P w → evalV D.host.F w α = 0)
    (x : D.host.E) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ GlobalTheory.FinPl.idAt D P := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hα _ w.2, TensorProduct.zero_tmul]

theorem latO_mx {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : GlobalTheory.FinPl.MxAt P u := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
    intro i j
    exact gen_mem_idAt' P α hα _
  | zero => exact fun _ _ => zero_mem _
  | add x y _ _ hx hy => exact fun i j => add_mem (hx i j) (hy i j)
  | neg x _ hx => exact fun i j => neg_mem (hx i j)

theorem latO_mono {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ x, P' x → P x) : latO S T LS LT P' ≤ latO S T LS LT P :=
  AddSubgroup.closure_mono fun _ ⟨α, hαi, hα, rest⟩ => ⟨α, hαi, fun v hv => hα v (fun h' => hv (h v h')), rest⟩

theorem heisO_comm_of {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {x y : WO S T}
    (h1 : symplO S T x y = 0) (h2 : symplO S T y x = 0) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = heisO ψ S T y (heisO ψ S T x f) := by
  rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, add_comm]
  have e1 : symplOH S T x y = 0 := by unfold symplOH; rw [h1, mul_zero]
  have e2 : symplOH S T y x = 0 := by unfold symplOH; rw [h2, mul_zero]
  rw [e1, e2]

theorem comb_vac_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (P : GlobalTheory.FinPl.Pl D → Prop) (p : GlobalTheory.FinPl.Pl D), P p → IsStdChar D ψ (-1) → ∀ (e : WO S T →₀ ℂ) (f : WO S T → ℂ), (∀ u ∈ e.support, GlobalTheory.FinPl.MxAt (· ≠ p) u) → GlobalTheory.FinPl.Vac ψ S T LS LT P f → GlobalTheory.FinPl.Vac ψ S T LS LT (· = p) (comb ψ S T e f) := by
  intro D ψ S T LS LT P p hP hstd e f he hf
  have hdisj1 : ∀ x : GlobalTheory.FinPl.Pl D, x = p → ¬ x ≠ p := fun x hx h => h hx
  have hdisj2 : ∀ x : GlobalTheory.FinPl.Pl D, x ≠ p → ¬ x = p := fun x hx h => hx h
  have hcomm : ∀ u, GlobalTheory.FinPl.MxAt (· = p) u → heisO ψ S T u (comb ψ S T e f) = comb ψ S T e (heisO ψ S T u f) := by
    intro u hu
    unfold comb
    rw [GlobalTheory.HeisComb.heisO_finset_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [heisO_comm_of ψ (symplO_eq_zero_of_disj D S T _ _ hdisj1 u x hu (he x hx)) (symplO_eq_zero_of_disj D S T _ _ hdisj2 x u (he x hx) hu)]
  have hmono : latO S T (LS : Set _) (LT : Set _) (· = p) ≤ latO S T (LS : Set _) (LT : Set _) P :=
    latO_mono fun x (hx : x = p) => hx ▸ hP
  refine ⟨(GlobalTheory.HeisComb.main D ψ S T).2.2.1 e f hf.1 (fun u hu => mx_inf (he u hu)) hstd, ?_, ?_⟩
  · intro u hu
    have h2u : 2 • u ∈ latO S T (LS : Set _) (LT : Set _) (· = p) := nsmul_mem hu 2
    rw [hcomm _ (latO_mx h2u), hf.2.1 _ (hmono hu)]
  · intro e' he' u hu hhalf
    rw [hcomm _ (latO_mx hu), hf.2.2 e' he' u (hmono hu) hhalf]

theorem sum_om_vac_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (p : GlobalTheory.FinPl.Pl D) (b : GA D S →₀ ℂ) (f : WO S T → ℂ), (∀ g ∈ b.support, g ∈ GlobalTheory.FinPl.grpAt S (· ≠ p)) → GlobalTheory.FinPl.Vac ψ S T LS LT (· = p) f → GlobalTheory.FinPl.Vac ψ S T LS LT (· = p) (∑ g ∈ b.support, b g • om (g, 1) f) := by
  intro D ψ S T χS χT om hw LS LT p b f hb hf
  have hdisj : ∀ x : GlobalTheory.FinPl.Pl D, x ≠ p → ¬ x = p := fun x hx h => hx h
  have hcomm : ∀ u, GlobalTheory.FinPl.MxAt (· = p) u →
      heisO ψ S T u (∑ g ∈ b.support, b g • om (g, 1) f) = ∑ g ∈ b.support, b g • om (g, 1) (heisO ψ S T u f) := by
    intro u hu
    rw [GlobalTheory.HeisComb.heisO_finset_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [hw.om_heis g 1 u f hf.1, actO_eq_of_disj D S T _ _ hdisj g (hb g hg) u hu]
  refine ⟨GlobalTheory.Core.Rk.Collect.theta_sum b.support (fun g => b g) (fun g => om (g, 1) f) (fun g => hw.om_pres _ f hf.1), ?_, ?_⟩
  · intro u hu
    have h2u : 2 • u ∈ latO S T _ _ (· = p) := nsmul_mem hu 2
    rw [hcomm _ (latO_mx h2u), hf.2.1 _ hu]
  · intro e' he' u hu hhalf
    rw [hcomm _ (latO_mx hu), hf.2.2 e' he' u hu hhalf]

theorem biComb_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' (Finsupp.single 0 1) (Finsupp.single 0 1) C = C := by
  funext u w
  simp only [biComb, comb_single_zero]

theorem sum_conv_nil {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (X : WO S T → ℂ) :
    ∑ g ∈ (conv ([] : List (GA D S →₀ ℂ))).support, conv ([] : List (GA D S →₀ ℂ)) g • om (g, 1) X = X := by
  have e : conv ([] : List (GA D S →₀ ℂ)) = Finsupp.single 1 1 := rfl
  rw [e, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  show om 1 X = X
  rw [map_one]; rfl

set_option maxHeartbeats 4000000 in
theorem iter_places {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} {w : VTup t} (F : QFam v t) (hc : c.Is) (ht : t.Is)
    (hv : v.Is) (hW : WeilOK (t := t) v) (hF : F.Pins w) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ)
    (hΨ₁ : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁)
    (hΨ₂ : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂)
    (φ : GA D (c.X j) → ℂ) (hφ : IsContAut (c.X j) φ) (α : t.Ch j) (β : t.Ch (j + 1 + 1)) :
    ∀ (n : ℕ) (σ : Fin n → Fin F.r), Function.Injective σ →
    ∀ (c₁ : WO (c.X j) (c.X (j + 1)) →₀ ℂ) (c₂ : WO (c.X (j + 1)) (c.X (j + 1 + 1)) →₀ ℂ),
    (∀ k, ∀ u ∈ c₁.support, IsHalf (1 - ((F.Q (σ k)).q.e + cA D (F.Q (σ k)).q.e)) u) →
    (∀ k, ∀ u ∈ c₂.support, IsHalf (1 - ((F.Q (σ k)).q.e + cA D (F.Q (σ k)).q.e)) u) →
    (∏ k, ((F.Q (σ k)).idx (j + 1) : ℂ)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ c₁ c₂
      (c.lst j h (v.τ j h) (t.sBF j 0 h)
        (∑ g ∈ (conv (List.ofFn fun k => (F.Q (σ k)).εL j (F.eqv j α (σ k)))).support,
          conv (List.ofFn fun k => (F.Q (σ k)).εL j (F.eqv j α (σ k))) g •
            t.om j (g, 1) (comb c.ψ _ _ (aconv (List.ofFn fun k => (F.Q (σ k)).eL j)) Ψ₁))
        (comb c.ψ _ _ (aconv (List.ofFn fun k => (F.Q (σ k)).eT j h)) Ψ₂))) =
    ∑ y : (k : Fin n) → (F.Q (σ k)).Ch (j + 1), (∏ k, (F.Q (σ k)).wt (j + 1) (y k)) •
      c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _
        (aconv (c₁ :: List.ofFn fun k => (F.Q (σ k)).dL j (F.eqv j α (σ k)) (y k)))
        (aconv (c₂ :: List.ofFn fun k => (F.Q (σ k)).dL (j + 1) (y k) (F.eqv (j + 1 + 1) β (σ k))))
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  have hstd : IsStdChar D c.ψ (-1) := hc.std
  have hom : (t.sBF j 0 h).om = t.om j := (ht.sBF j 0 h).1
  have hweil : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j 0 h).χV (t.sBF j 0 h).χW (t.om j) := hom ▸ (t.sBF j 0 h).weil
  have hne : ∀ a b : Fin F.r, a ≠ b → (F.Q a).q.v ≠ (F.Q b).q.v := fun a b hab e => hab (hF.inj e)
  have hinQ : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  intro n
  induction n with
  | zero =>
    intro σ _ c₁ c₂ _ _
    simp only [List.ofFn_zero, Finset.univ_eq_empty, Finset.prod_empty, one_smul, Fintype.sum_unique]
    have e0 : aconv ([] : List (WO (c.V j) (c.V (j + 1)) →₀ ℂ)) = Finsupp.single 0 1 := rfl
    have e0' : aconv ([] : List (WO (c.V (j + 1)) c.T →₀ ℂ)) = Finsupp.single 0 1 := rfl
    rw [e0, e0', comb_single_zero, comb_single_zero, sum_conv_nil, conv_alg.2.1, conv_alg.2.1]
  | succ n ih =>
    intro σ hσ c₁ c₂ h₁ h₂
    have hτ : Function.Injective (fun k : Fin n => σ k.succ) := hσ.comp (Fin.succ_injective _)
    have hne0 : ∀ k : Fin n, (F.Q (σ k.succ)).q.v ≠ (F.Q (σ 0)).q.v :=
      fun k => hne _ _ (fun e => Fin.succ_ne_zero k (hσ e))

    have hEsupp : ∀ g ∈ (conv (List.ofFn fun k : Fin n => (F.Q (σ k.succ)).εL j (F.eqv j α (σ k.succ)))).support,
        g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ≠ (F.Q (σ 0)).q.v) := by
      refine conv_alg.2.2.2.2 _ _ (GlobalTheory.FinPl.grpAt (c.V j) (· ≠ (F.Q (σ 0)).q.v)).toSubmonoid ?_
      intro x hx g hg
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      exact εL_grp (F.Q (σ k.succ)) h _ g hg _ (hne0 k)
    have hLsupp : ∀ u ∈ (aconv (List.ofFn fun k : Fin n => (F.Q (σ k.succ)).eL j)).support,
        GlobalTheory.FinPl.MxAt (· ≠ (F.Q (σ 0)).q.v) u := by
      refine conv_alg.2.2.2.1 (WO (c.V j) (c.V (j + 1))) _ (mxSub _ _ _) ?_
      intro x hx u hu
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      exact half_mx _ (eL_half (F.Q (σ k.succ)) h u hu) _ (hne0 k)
    have hTsupp : ∀ u ∈ (aconv (List.ofFn fun k : Fin n => (F.Q (σ k.succ)).eT j h)).support,
        GlobalTheory.FinPl.MxAt (· ≠ (F.Q (σ 0)).q.v) u := by
      refine conv_alg.2.2.2.1 (WO (c.V (j + 1)) c.T) _ (mxSub _ _ _) ?_
      intro x hx u hu
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      exact half_mx _ (eT_half (F.Q (σ k.succ)) h u hu) _ (hne0 k)
    have hd0 : ∀ p : GlobalTheory.FinPl.Pl D, p = (F.Q (σ 0)).q.v → ¬ p ≠ (F.Q (σ 0)).q.v := fun p hp hp' => hp' hp
    have hd1 : ∀ p : GlobalTheory.FinPl.Pl D, p ≠ (F.Q (σ 0)).q.v → ¬ p = (F.Q (σ 0)).q.v := fun p hp hp' => hp hp'
    simp only [List.ofFn_succ]
    rw [sum_conv_cons, comb_aconv_cons D c.ψ _ _ _ _ Ψ₁ (fun x hx y hy => symplO_eq_zero_of_disj D _ _ _ _ hd0 x y
        (half_mx _ (eL_half (F.Q (σ 0)) h x hx) _ rfl) (hLsupp y hy)),
      comb_aconv_cons D c.ψ _ _ _ _ Ψ₂ (fun x hx y hy => symplO_eq_zero_of_disj D _ _ _ _ hd0 x y
        (half_mx _ (eT_half (F.Q (σ 0)) h x hx) _ rfl) (hTsupp y hy)),
      sum_om_comb_comm D c.ψ _ _ _ _ (t.om j) hweil _ _ _
        ((GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ Ψ₁ hΨ₁.1 (fun u hu => mx_inf (hLsupp u hu)) hstd)
        (fun g hg u hu => actO_eq_of_disj D _ _ _ _ hd1 g (hEsupp g hg) u (half_mx _ (eL_half (F.Q (σ 0)) h u hu) _ rfl))]
    rw [Fin.prod_univ_succ, mul_comm, mul_smul]
    obtain ⟨hr, hτv⟩ := hW.tau j h
    rw [oneplace_at (F.Q (σ 0)) hc hv j (s_eq _ h) h hr hτv (t.sBF j 0 h) (hF.lastc j h) (t.om j) hom (t.kom j)
      (t.kom (j + 1)) (hF.kom j (by omega)) (hF.kom (j + 1) (by omega)) c₁ c₂ (h₁ 0) (h₂ 0) _ _
      (sum_om_vac_at D c.ψ _ _ _ _ (t.om j) hweil _ _ _ _ _ hEsupp
        (comb_vac_at D c.ψ _ _ _ _ _ _ (hinQ (σ 0)) hstd _ _ hLsupp hΨ₁))
      (comb_vac_at D c.ψ _ _ _ _ _ _ (hinQ (σ 0)) hstd _ _ hTsupp hΨ₂) φ hφ (F.eqv j α (σ 0))
      (F.eqv (j + 1 + 1) β (σ 0)), Finset.smul_sum]
    rw [← (Fin.consEquiv (fun k : Fin (n + 1) => (F.Q (σ k)).Ch (j + 1))).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y₀ _ => ?_
    rw [smul_comm, ih (fun k => σ k.succ) hτ _ _ ?_ ?_, Finset.smul_sum]
    · refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_smul]
      rw [conv_alg.1, conv_alg.1]
    · intro k
      refine conv_alg.2.2.2.1 (WO (c.X j) (c.X (j + 1))) _ (halfSub _ _ _) ?_
      intro x hx u hu
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact h₁ k.succ u hu
      · exact half_one_sub_of_ne D _ _ (F.Q (σ k.succ)).q (F.Q (σ 0)).q (hne0 k) _ _ u (dL_half (F.Q (σ 0)) h _ _ u hu)
    · intro k
      refine conv_alg.2.2.2.1 (WO (c.X (j + 1)) (c.X (j + 1 + 1))) _ (halfSub _ _ _) ?_
      intro x hx u hu
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact h₂ k.succ u hu
      · exact half_one_sub_of_ne D _ _ (F.Q (σ k.succ)).q (F.Q (σ 0)).q (hne0 k) _ _ u (dL_half' (F.Q (σ 0)) h _ _ u hu)


set_option maxHeartbeats 4000000 in
theorem core : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ → ∀ φ, IsContAut (c.X j) φ → ∀ α β, (∏ i, ((F.Q i).idx (j + 1) : ℂ)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ (conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i))).support, conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) g • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) = ∑ γ, (∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i))) (aconv (List.ofFn fun i => (F.Q i).dL (j + 1) (F.eqv (j + 1) γ i) (F.eqv (j + 1 + 1) β i))) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w F hc ht hv hW hF j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  have h1 : ∀ k : Fin F.r, ∀ u ∈ (Finsupp.single (0 : WO (c.X j) (c.X (j + 1))) (1 : ℂ)).support,
      IsHalf (1 - ((F.Q (id k)).q.e + cA D (F.Q (id k)).q.e)) u := by
    intro k u hu
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu; intro a b; simp
  have h2 : ∀ k : Fin F.r, ∀ u ∈ (Finsupp.single (0 : WO (c.X (j + 1)) (c.X (j + 1 + 1))) (1 : ℂ)).support,
      IsHalf (1 - ((F.Q (id k)).q.e + cA D (F.Q (id k)).q.e)) u := by
    intro k u hu
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu; intro a b; simp
  have H := iter_places F hc ht hv hW hF j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β F.r id Function.injective_id _ _ h1 h2
  rw [biComb_one] at H
  simp only [conv_alg.2.2.1, id] at H
  rw [hF.eQ j (by omega), hF.eQT j h, H]
  exact (Fintype.sum_equiv (F.eqv (j + 1)) _ _ fun γ => rfl).symm

end GlobalTheory.QLastCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsAllTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_last_two_steps_all_twist_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ → ∀ φ, IsContAut (c.X j) φ → ∀ α β, (∏ i, ((F.Q i).idx (j + 1) : ℂ)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ (conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i))).support, conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) g • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) = ∑ γ, (∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i))) (aconv (List.ofFn fun i => (F.Q i).dL (j + 1) (F.eqv (j + 1) γ i) (F.eqv (j + 1 + 1) β i))) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QLastCore.core | exact GlobalTheory.QLastCore.core | (intros; apply GlobalTheory.QLastCore.core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDoubleThetaLiftIntegrableLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDoubleThetaLiftIntegrableLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastDbl

variable {D : D7}

theorem ker_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (a : ℂ) (C : WO A S → WO S X → ℂ) (h₀ : GA D A)
    (h₁ : GA D S) (h₂ : GA D X) :
    GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ = a * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂ := by
  unfold GlobalTheory.SeeSmallPf.ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (a • C) u v) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : (fun u => (a • C) u v) = a • fun u => C u v := by
      funext u; simp only [Pi.smul_apply]
    rw [e, map_smul]; simp only [Pi.smul_apply]
  rw [e1, map_smul]; simp only [Pi.smul_apply, smul_eq_mul]

theorem biLift_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ (a • C) h₂ = a * biLift oma omX vA vS φ C h₂ := by
  rw [GlobalTheory.SeeSmallPf.biLift_eq, GlobalTheory.SeeSmallPf.biLift_eq]
  have e : ∀ h₀ h₁, φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ =
      a * (φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂) := fun h₀ h₁ => by rw [ker_smul]; ring
  simp only [e, integral_const_mul]

theorem theta_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (a • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w)) }

theorem sum_fin {G M : Type} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  intro D c v t hc ht hW j h Y hY φ hφ
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', hχV, hWa, hWz, hWX, hWT, hWTb, hWz''⟩ := hW.last j h
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X j) := (hc.x j (by omega)).cpt
  have hS : CoCpt (c.X (j + 1)) := (hc.x (j + 1) (by omega)).cpt
  have hτ := (hW.tau j h).2
  obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d hc.std
  have hY' : IsThetaFunO c.ψ (c.X (j + 1)) c.T (fun w => Y ((c.jac j 0 h).d.ext0 c.T w)) := (hthS Y).2 hY
  have hC : ∀ Z : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ Z →
      IsBiTheta c.ψ (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1)) (c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y) := by
    intro Z hZ
    have hZ' : IsThetaFunO c.ψ (c.B j 0 h).V (c.J j 0 h).W Z := hZ
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero (t.sBF j 0 h) hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
      (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) hτ (flatBF (t.sBF j 0 h) Z) _ hΞ hY'
  refine ⟨fun X hX f hf => GlobalTheory.SeeSmallPf.outer hB hWa hWX (hC X hX) hA hS hc.cpt (c.x j).vol (c.x (j + 1)).vol c.volT
    (c.oT (j + 1 + 1) h) hφ hf, fun G s a X hX => ?_⟩
  have hsum : ∀ (Z : G → WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • Z g) Y =
      ∑ g ∈ s, a g • c.lst j h (v.τ j h) (t.sBF j 0 h) (Z g) Y := by
    intro Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hsm : ∀ (b : ℂ) (Z : WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (b • Z) Y =
      b • c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y := by
    intro b Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Pi.smul_apply, smul_eq_mul]
    ring
  funext h₂
  rw [hsum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ g, a g * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) h₂ =
      c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (a g • X g) Y) h₂ := fun g => by
    rw [hsm]; exact (biLift_smul _ _ _ _ _ _ _ _).symm
  simp only [e1]
  rw [sum_fin s, sum_fin s]
  have e2 : (∑ i : Fin s.card, a (s.equivFin.symm i) • c.lst j h (v.τ j h) (t.sBF j 0 h) (X (s.equivFin.symm i)) Y) =
      ∑ i : Fin s.card, c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y :=
    Finset.sum_congr rfl fun i _ => (hsm _ _).symm
  rw [e2]
  exact (GlobalTheory.SeeSmallPf.biLift_sum hB hWa hWX hA hS (c.x j).vol (c.x (j + 1)).vol hφ
    (fun i => c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y)
    (fun i => hC _ (theta_smul _ (hX _))) h₂).symm

end GlobalTheory.LastDbl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDoubleThetaLiftIntegrableLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastDoubleThetaLift_integrable_linear : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  first | exact @GlobalTheory.LastDbl.main | exact GlobalTheory.LastDbl.main | (intros; apply GlobalTheory.LastDbl.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem relIndex_KO_ne_zero {k n : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)) (hJ : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n))
  haveI : Finite (KO k n ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (hJ.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem QAt.idx_last_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  intro D c v χ Q
  refine ⟨?_, ?_⟩
  · rw [Q.idx_mid (Q.s + 1) 0 rfl]
    exact relIndex_KO_ne_zero _ (Q.reg.2.2 _ _ _).1
  · rw [Q.idx_top]
    exact relIndex_KO_ne_zero _ Q.openT

end GlobalTheory.QPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_last_two_level_indices_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  first | exact @GlobalTheory.QPl.QAt.idx_last_ne_zero | exact GlobalTheory.QPl.QAt.idx_last_ne_zero | (intros; apply GlobalTheory.QPl.QAt.idx_last_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactori
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QLastPf

theorem heisO_smul' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem comb_smul_left {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • e) f = a • comb ψ S T e f := by
  by_cases ha : a = 0
  · simp [comb, ha]
  · rw [comb, comb, Finsupp.support_smul_eq ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finsupp.smul_apply, smul_smul, smul_eq_mul]

theorem comb_smul_right {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T e (a • f) = a • comb ψ S T e f := by
  rw [comb, comb, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_smul', smul_comm]

theorem biComb_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a b : ℂ) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' (a • e) (b • e') C = (a * b) • biComb ψ A S A' e e' C := by
  funext u v
  simp only [biComb, comb_smul_left]
  have e1 : (fun u' => (b • comb ψ S A' e' (C u')) v) = b • fun u' => comb ψ S A' e' (C u') v := by
    funext u'; simp
  rw [e1, comb_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul, biComb]
  ring

theorem block_smul₂ {D : D7} (c : Comm D) (j : ℕ) (oma : Om (c.X j) (c.X (j + 1))) (omb : Om (c.X (j + 1)) (c.X (j + 1 + 1)))
    (φ : GA D (c.X j) → ℂ) (a : ℂ) (C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) :
    c.bl j oma omb φ (a • C) = a • c.bl j oma omb φ C := by
  funext h₂
  simp only [Comm.bl, biLift, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h₁
  rw [← integral_const_mul]
  congr 1; funext h₀
  have e1 : ∀ v, (fun u => a * C u v) = a • fun u => C u v := fun v => by funext u; simp
  simp_rw [e1, map_smul]
  have e2 : (fun v => (a • oma (h₀, h₁) (fun u => C u v)) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v; simp
  rw [e2, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem alg_of_core : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ → ∀ φ, IsContAut (c.X j) φ → ∀ α β, c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ (w.ε j α).support, w.ε j α g • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) = (w.cQ j * w.εT (j + 1 + 1) h β 1) • ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  obtain ⟨F, hF⟩ := id hpin
  obtain ⟨hX, hY⟩ := GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions D c v t w F hc hF j h Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
  have hom : ∀ g, IsThetaFunO c.ψ _ _ (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    rw [← (ht.sBF j 0 h).1]
    exact (t.sBF j 0 h).weil.om_pres _ _ hX
  have lin := fun (s : Finset (GA D (c.V j))) (a : GA D (c.V j) → ℂ) => (GlobalTheory.T.lastDoubleThetaLift_integrable_linear D c v t hc ht hW j h _ hY φ hφ).2 _ s a _ hom
  have hcore := GlobalTheory.T.seeSaw_last_two_steps_all_twist_places D c v t w F hc ht hv hW hF j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  have hidx : ∀ i, ((F.Q i).idx (j + 1) : ℂ) ≠ 0 ∧ ((F.Q i).idx (j + 1 + 1) : ℂ) ≠ 0 := by
    intro i
    have h1 := GlobalTheory.T.twistPlace_last_two_level_indices_ne_zero D c v F.χ (F.Q i)
    rw [hs i] at h1
    exact ⟨Nat.cast_ne_zero.2 h1.1, Nat.cast_ne_zero.2 h1.2⟩
  have htop : ∀ i u, (F.Q i).wt (j + 1 + 1) u = (F.Q i).idx (j + 1 + 1) := by
    intro i
    have h1 := (F.Q i).wt_top
    rw [hs i] at h1
    exact h1
  set E := conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) with hE
  set P := ∏ i, (F.Q i).wt j (F.eqv j α i) with hP
  set Z := fun g => t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁) with hZ
  have hε : w.ε j α = P • E := hF.ε j 0 h α
  have hsum : ∑ g ∈ (w.ε j α).support, w.ε j α g • Z g = ∑ g ∈ E.support, (P * E g) • Z g := by
    rw [hε]
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [Finsupp.support_smul_eq hP0]
      rfl
  have hL : c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h)
      (∑ g ∈ (w.ε j α).support, w.ε j α g • Z g) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) =
      P • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h)
        (∑ g ∈ E.support, E g • Z g) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) := by
    rw [hsum, ← lin E.support (fun g => P * E g), ← lin E.support (fun g => E g), Finset.smul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [smul_smul]
  simp only [hZ] at hL
  rw [hL]
  have hR : ∀ γ, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
      (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) = (P * ∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) •
      c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)))
        (aconv (List.ofFn fun i => (F.Q i).dL (j + 1) (F.eqv (j + 1) γ i) (F.eqv (j + 1 + 1) β i)))
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
    intro γ
    rw [hF.dQ j (by omega) α γ, hF.dQ (j + 1) (by omega) γ β, biComb_smul, block_smul₂]
  simp only [hR]
  have hεT : w.εT (j + 1 + 1) h β 1 = ∏ i, ((F.Q i).idx (j + 1 + 1) : ℂ) := by
    rw [hF.εT (j + 1 + 1) h β, Finsupp.single_eq_same]
    exact Finset.prod_congr rfl fun i _ => htop i _
  rw [hεT, hF.cQ j (by omega)]
  simp only [← smul_smul]
  rw [← Finset.smul_sum, ← hcore, smul_smul, smul_smul, smul_smul]
  congr 1
  have hone : (∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹) *
      (∏ i, ((F.Q i).idx (j + 1 + 1) : ℂ)) * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    field_simp [(hidx i).1, (hidx i).2]
  linear_combination (-P) * hone

theorem qLast_of_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is →
    WeilOK (t := t) v → QPin v w → QLast v w := by
  intro D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ f hf _
  obtain ⟨F, hF⟩ := id hpin
  obtain ⟨hX, hY⟩ := GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions D c v t w F hc hF j h Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
  have hfc : IsContAut c.T f := ⟨fun γ hγ g => hf.left γ hγ g, hf.cont⟩
  have hom : ∀ g, IsThetaFunO c.ψ _ _ (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    rw [← (ht.sBF j 0 h).1]
    exact (t.sBF j 0 h).weil.om_pres _ _ hX
  have han := fun α => GlobalTheory.T.lastDoubleThetaLift_integrable_linear D c v t hc ht hW j h _ hY (φ α) (hφ α).1
  set Y := comb c.ψ _ _ (w.eQT j h) Ψ₂ with hYd
  set X := comb c.ψ _ _ (w.eQ j) Ψ₁ with hXd
  set E := (c.oT (j + 1 + 1) h).emb with hE
  set K := fun α γ β => c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
    (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) with hK
  set G := fun α => c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h)
    (∑ g ∈ (w.ε j α).support, w.ε j α g • t.om j (g, 1) X) Y) with hG
  have key : ∀ α, (fun h' => f h' * G α (E (h', 1))) = fun h' => ∑ g ∈ (w.ε j α).support, w.ε j α g *
      (f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) X) Y) (E (h', 1))) := by
    intro α
    funext h'
    simp only [hG]
    rw [← (han α).2 _ _ _ _ hom, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hint : ∀ α, IntegrableOn (fun h' => f h' * G α (E (h', 1))) c.volT.𝓕 c.volT.μ := by
    intro α
    rw [key α]
    exact integrable_finsetSum _ fun g _ => ((han α).1 _ (hom g) f hfc).const_mul _
  have hL : ∀ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
      (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) X) Y) (E (h', 1)) ∂c.volT.μ =
      ∫ h' in c.volT.𝓕, f h' * G α (E (h', 1)) ∂c.volT.μ := by
    intro α
    rw [key α, integral_finsetSum _ fun g _ => ((han α).1 _ (hom g) f hfc).const_mul _]
    exact Finset.sum_congr rfl fun g _ => (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl fun α _ => hL α, ← integral_finsetSum _ fun α _ => hint α]

  have hcard : Fintype.card (t.Ch (j + 1 + 1)) = 1 := by
    rw [Fintype.card_congr (F.eqv (j + 1 + 1)), Fintype.card_pi]
    refine Finset.prod_eq_one fun i _ => ?_
    have hs : (F.Q i).s = j := by have := (F.Q i).hs; omega
    have h1 := (F.Q i).one
    rw [hs] at h1
    exact h1
  have hβ : ∀ β, (w.cQ j * ∫ h' in c.volT.𝓕, trc (w.εT (j + 1 + 1) h β) f h' *
      (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂))) (E (h', 1)) ∂c.volT.μ) =
      ∫ h' in c.volT.𝓕, ∑ α, f h' * G α (E (h', 1)) ∂c.volT.μ := by
    intro β
    have htrc : trc (w.εT (j + 1 + 1) h β) f = w.εT (j + 1 + 1) h β 1 • f := by
      rw [hF.εT (j + 1 + 1) h β]
      by_cases ha : (∏ i, (F.Q i).wt (j + 1 + 1) (F.eqv (j + 1 + 1) β i)) = 0
      · simp [trc, ha]
      · rw [trc, Finsupp.support_single _ ha, Finset.sum_singleton]
        funext x
        simp [rTrans]
    rw [← integral_const_mul]
    congr 1
    funext h'
    have hG' : ∀ α, G α = (w.cQ j * w.εT (j + 1 + 1) h β 1) • ∑ γ, K α γ β := fun α =>
      alg_of_core D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ (φ α) (hφ α).1 α β
    simp only [hG', htrc, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun β _ => hβ β, Finset.sum_const, Finset.card_univ, hcard, one_smul]

end GlobalTheory.QLastPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactoriStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QLast v w := by
  first | exact @GlobalTheory.QLastPf.qLast_of_pin | exact GlobalTheory.QLastPf.qLast_of_pin | (intros; apply GlobalTheory.QLastPf.qLast_of_pin <;> assumption)
end

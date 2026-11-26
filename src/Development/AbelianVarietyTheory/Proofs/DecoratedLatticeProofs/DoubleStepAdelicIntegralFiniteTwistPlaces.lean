module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandInvariantAtSuccPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandFiniteDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedInnerIntegralAtFirstOfSplitPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal

theorem quotient_integral_of_subsingleton {G : Type} [Group G] [MeasurableSpace G] [Subsingleton G] {R : Subgroup G}
    (μR : Measure R) (μG : Measure G) (hR : μR Set.univ = 1) (hG : μG Set.univ = 1) (f : G → ℂ) :
    IsQuotIntL1 μR μG f (f 1) := by
  haveI : IsProbabilityMeasure μR := ⟨hR⟩
  haveI : IsProbabilityMeasure μG := ⟨hG⟩
  have hc : ∀ x, f x = f 1 := fun x => by rw [Subsingleton.elim x 1]
  have hf : f = fun _ => f 1 := funext hc
  refine ⟨fun _ => f 1, integrable_const _, fun _ => integrable_const _, fun h => ?_, ?_⟩
  · simp [hc h]
  · simp

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem conv_nil' {G : Type} [Monoid G] : conv ([] : List (G →₀ ℂ)) = Finsupp.single 1 1 := rfl

theorem aconv_singleton' {G : Type} [AddMonoid G] (c : G →₀ ℂ) : aconv [c] = c := by
  simp only [aconv, List.foldr_cons, List.foldr_nil]
  conv_rhs => rw [← Finsupp.sum_single c]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem aconv_nil' {G : Type} [AddMonoid G] : aconv ([] : List (G →₀ ℂ)) = Finsupp.single 0 1 := rfl

theorem comb_single_zero' (S' T : HSp D) (u : WO S' T → ℂ) :
    comb ψ S' T (Finsupp.single 0 1) u = u := by
  simp [comb, Finsupp.support_single_ne_zero _ one_ne_zero, heisO_zero_eq]

theorem trc_single_one' {V : HSp D} (u : GA D V → ℂ) : trc (Finsupp.single 1 1) u = u := by
  simp only [trc, Finsupp.support_single_ne_zero (1 : GA D V) (one_ne_zero (α := ℂ)), Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext x
  show u (x * 1) = u x
  rw [mul_one]

theorem value_zero_eq (Q : Fin 0 → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ 1 1 := by
  simp only [value, integrand, List.ofFn_zero, conv_nil', aconv_singleton', trc_single_one']
  rw [GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]
  simp [aconv_nil', comb_single_zero']
end

end GlobalTheory.QVal

namespace GlobalTheory.QVal

theorem valQr_zero : ∀ D : D7, ValQr D 0 := by
  intro D ψ _ σ S Q _ μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ _
  obtain ⟨-, -, -, -, e1, e2, e3, e4⟩ := hN
  have hP : ¬ ∃ v, places Q v := fun ⟨_, i, _⟩ => i.elim0
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.J.W (places Q)) := by
    rw [grpAt_eq_bot S.J.W hP]; infer_instance
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) := by
    rw [grpAt_eq_bot S.B'.V hP]; infer_instance
  simp only [IsEmpty.forall_iff, Set.setOf_true] at e1 e2 e3 e4
  refine ⟨fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1, ?_, fun q => ?_⟩
  · have := quotient_integral_of_subsingleton ρ₁ μ₁ e2 e1 (fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1)
    simpa [value_zero_eq] using this
  · have := quotient_integral_of_subsingleton ρ₂ μ₂ e4 e3 (fun y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ q.1 y.1)
    simpa using this

end GlobalTheory.QVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedIntegralValueAtRPlaces_zero : ∀ D : D7, ValQr D 0 := by
  first | exact @GlobalTheory.QVal.valQr_zero | exact GlobalTheory.QVal.valQr_zero | (intros; apply GlobalTheory.QVal.valQr_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem gl₂_comm (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (a : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)
    (b : GL (Q'.n₂ ⊕ Fin (Q'.c + 1)) Q'.k) : Q₀.gl₂ a * Q'.gl₂ b = Q'.gl₂ b * Q₀.gl₂ a := by
  have h0 : Q₀.gl₂ a ∈ grpAt S.B'.V (· = Q₀.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q₀.k Q₀.q S.B'.V _ Q₀.F.G₂ Q₀.gl₂ Q₀.loc₂).2.1]; exact ⟨a, rfl⟩
  have h1 : Q'.gl₂ b ∈ grpAt S.B'.V (· = Q'.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q'.k Q'.q S.B'.V _ Q'.F.G₂ Q'.gl₂ Q'.loc₂).2.1]; exact ⟨b, rfl⟩
  exact GlobalTheory.SeeSawLastValue.grpAt_comm (fun p hp hp' => hne (hp.symm.trans hp')) h0 h1

theorem typed_trc (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (e : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k →₀ ℂ)
    {f : GA D S.B'.V → ℂ} (hf : Q'.Typed f) : Q'.Typed (trc (e.mapDomain Q₀.gl₂) f) := by
  classical
  intro j
  funext x
  have hj := hf j
  simp only [rTrans, Pi.smul_apply, smul_eq_mul, trc_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  have := congrFun hj (x * Q₀.gl₂ a)
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at this
  rw [mul_assoc x, ← gl₂_comm Q₀ Q' hne, ← mul_assoc, this]
  ring

theorem away_pair (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) {A T : HSp D} (c d : WO A T →₀ ℂ) (hc : Q'.Away c)
    (hd : ∀ u ∈ d.support, IsHalf (Q₀.q.e + cA D Q₀.q.e) u) : Q'.Away (aconv [c, d]) := by
  obtain ⟨ε₀, hε₀, he₀⟩ := Q₀.q.above
  obtain ⟨ε', hε', he'⟩ := Q'.q.above
  have horth : algebraMap (AF D.host.F) (AE D) ε' * algebraMap (AF D.host.F) (AE D) ε₀ = 0 := by
    rw [← map_mul, GlobalTheory.VacuumFrameCompare.place_orth hε' hε₀ (Ne.symm hne), map_zero]
  intro u hu i j
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_aconv_pair c d hu
  have h1 := hc a ha i j
  have h2 := hd b hb i j
  rw [he'] at h1 ⊢
  rw [he₀] at h2
  have h3 : (1 - algebraMap (AF D.host.F) (AE D) ε') * b i j = b i j := by
    rw [← h2, sub_mul, one_mul, ← mul_assoc, horth, zero_mul, sub_zero]
  rw [Matrix.add_apply, mul_add, h1, h3]

theorem hyps_succ {r : ℕ} (Q : Fin (r + 1) → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ} {f₁ : WO S.B.V S.J.W → ℂ} {f₂ : WO S.J.W S.B'.V → ℂ}
    {φ : GA D S.B.A → ℂ} {f : GA D S.B'.V → ℂ} {g : GA D S.B.V} {h₁ : GA D S.J.W} {h₂ : GA D S.B'.V}
    (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (γ : (Q 0).A₁) (β : (Q 0).A₂) :
    Hyps (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  obtain ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩ := hH
  have hne : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  have hP : ∀ v, places (fun i : Fin r => Q i.succ) v → places Q v := fun v ⟨i, hi⟩ => ⟨i.succ, hi⟩
  refine ⟨fun i => ⟨away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).1 ((Q 0).ent₁ γ).1,
      away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).2 ((Q 0).ent₂ γ β).1⟩, t1, t2, fun i => hv i.succ, hφ,
    contAut_trc _ hf, fun i => typed_trc (Q 0) (Q i.succ) (hne i) _ (ht i.succ),
    grpOff_anti D _ _ _ hP hg, grpOff_anti D _ _ _ hP hh₁, grpOff_anti D _ _ _ hP hh₂⟩

theorem trc_conv_cons {V : HSp D} (E : GA D V →₀ ℂ) (l : List (GA D V →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) (f : GA D V → ℂ) :
    trc (conv (E :: l)) f = trc (conv l) (trc E f) := by
  have e1 : conv (E :: l) =
      (MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ (GA D V)).coeff := by
    rw [← comm_conv E l h, ← conv_cons]
  rw [e1, trc_mul]

theorem sum_pi_succ {r : ℕ} {α : Fin (r + 1) → Type} [∀ i, Fintype (α i)] (F : (∀ i, α i) → ℂ) :
    ∑ γ, F γ = ∑ a : α 0, ∑ γ' : ∀ i : Fin r, α i.succ, F (Fin.cons a γ') := by
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem value_succ {r : ℕ} (Q : Fin (r + 1) → QStep S)
    (hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a)
    (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ)
    (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = ∑ p : (Q 0).A₁ × (Q 0).A₂, (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2) *
      value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
        (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  classical
  have hX : ∀ (γ0 : (Q 0).A₁) (β0 : (Q 0).A₂) (γ' : ∀ i : Fin r, (Q i.succ).A₁) (β' : ∀ i : Fin r, (Q i.succ).A₂),
      S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)))
        (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)
          ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i).e₂ ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i)).mapDomain (Q i).gl₂)) f)
        g h₁ h₂ =
      S.val (aconv (aconv [c₁, (Q 0).d₁ γ0] :: List.ofFn fun i => (Q i.succ).d₁ (γ' i)))
        (aconv (aconv [c₂, (Q 0).d₂ γ0 β0] :: List.ofFn fun i => (Q i.succ).d₂ (γ' i) (β' i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i.succ).e₂ (β' i)).mapDomain (Q i.succ).gl₂))
          (trc (((Q 0).e₂ β0).mapDomain (Q 0).gl₂) f)) g h₁ h₂ := by
    intro γ0 β0 γ' β'
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [aconv_pair_cons, aconv_pair_cons, trc_conv_cons]
    intro x hx e he y hy
    rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact hcomm i a b
  rw [Fintype.sum_prod_type]
  simp only [value]
  simp only [sum_pi_succ (α := fun i => ↥(Q i).A₁), sum_pi_succ (α := fun i => ↥(Q i).A₂)]
  simp only [hX]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ0 _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β0 _ => Finset.sum_congr rfl fun γ' _ => Finset.sum_congr rfl fun β' _ => ?_
  ring

theorem outer : ∀ (D : D7) (r : ℕ), ValQr D r → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ μ₁ ρ₁ μ₂ ρ₂, Norm (fun i => Q i.succ) μ₁ ρ₁ μ₂ ρ₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) := by
  intro D r IH ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  have hinj' : Function.Injective fun i : Fin r => (Q i.succ).q.v := hinj.comp (Fin.succ_injective _)
  have hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a :=
    fun i => gl₂_comm (Q 0) (Q i.succ) fun h => Fin.succ_ne_zero i (hinj h).symm
  have key := GlobalTheory.SeeSaw.VanMany.iteratedQuotientIntegral_finite_linearCombination ρ₁ μ₁ ρ₂ μ₂ (I := (Q 0).A₁ × (Q 0).A₂)
    (fun p => (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2))
    (fun p x y => integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ x.1 y.1)
    (fun p => value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂)
    (fun p => IH ψ hψ σ S (fun i => Q i.succ) hinj' μ₁ ρ₁ μ₂ ρ₂ hN _ _ f₁ f₂ φ _ g h₁ h₂ (hyps_succ Q hinj hH p.1 p.2))
  rw [value_succ Q hcomm]
  convert key using 1
  funext x y
  simp only [innerVal, Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

end GlobalTheory.QValOuter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedIntegralValue_succ_places_outer : ∀ (D : D7) (r : ℕ), ValQr D r → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ μ₁ ρ₁ μ₂ ρ₂, Norm (fun i => Q i.succ) μ₁ ρ₁ μ₂ ρ₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) := by
  first | exact @GlobalTheory.QValOuter.outer | exact GlobalTheory.QValOuter.outer | (intros; apply GlobalTheory.QValOuter.outer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal.LevCO

variable {D : D7}

theorem isCO_iSup_map (V : HSp D) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) (gl : ∀ i, GL (Y i) (k i) →* GA D V)
    (hgl : ∀ i g, SuppAt (q i).e V (gl i g) ∧ (mt V (gl i g)).map (q i).pr = (F i).β * g.val * (F i).γ)
    (L : ∀ i, Subgroup (GL (Y i) (k i))) (hL : ∀ i, IsCO (L i)) :
    IsCO ((⨆ i, (L i).map (gl i)).subgroupOf (GlobalTheory.FinPl.grpAt V (fun p => ∃ i, (q i).v = p))) := by
  set P : GlobalTheory.FinPl.Pl D → Prop := fun p => ∃ i, (q i).v = p with hPdef
  have hA : GlobalTheory.FinPl.grpAt V P = GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v) := by
    congr 1
    funext p
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  obtain ⟨Ψ, hc, -, -, huniq⟩ := GlobalTheory.FixLev.exists_section V k q hq Y F
  let lh : ∀ i, GA D V →* GL (Y i) (k i) := fun i => GlobalTheory.FixLev.locHom (q i) V (F i)
  have hlh_self : ∀ i g, lh i (gl i g) = g := fun i g =>
    Units.ext (GlobalTheory.FixLev.frame_cancel (F i) ((GlobalTheory.FixLev.locHom_spec _ _ _ _).symm.trans (hgl i g).2))
  have hmat_ne : ∀ i j, i ≠ j → ∀ g, (mt V (gl j g)).map (q i).pr = 1 := fun i j hij g =>
    GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k j) (q i) (q j) V (gl j g) (fun e => hij (hq e)) (hgl j g).1
  have hlh_ne : ∀ i j, i ≠ j → ∀ g, lh i (gl j g) = 1 := fun i j hij g => Units.ext (by
    show (F i).γ * (mt V (gl j g)).map (q i).pr * (F i).β = 1
    rw [hmat_ne i j hij g, Matrix.mul_one, (F i).γβ])
  set H := ⨆ i, (L i).map (gl i) with hHdef
  have hglA : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt V P := fun i g =>
    GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i g).1 P ⟨i, rfl⟩
  have hHL : ∀ x ∈ H, ∀ i, lh i x ∈ L i := by
    intro x hx i
    have hle : H ≤ (L i).comap (lh i) := iSup_le fun j => Subgroup.map_le_iff_le_comap.2 fun g hg => by
      show lh i (gl j g) ∈ L i
      by_cases hij : i = j
      · subst hij
        rw [hlh_self]
        exact hg
      · rw [hlh_ne i j hij]
        exact one_mem _
    exact hle hx
  let Φ : (∀ i, GL (Y i) (k i)) → GA D V := fun y => ((List.finRange r).map fun i => gl i (y i)).prod
  have hΦA : ∀ y, Φ y ∈ GlobalTheory.FinPl.grpAt V P := fun y =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact hglA i (y i)
  have hΦH : ∀ y, (∀ i, y i ∈ L i) → Φ y ∈ H := fun y hy =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ (hy i))
  have hΦloc : ∀ y i, (mt V (Φ y)).map (q i).pr = (F i).β * (y i).val * (F i).γ := fun y i => by
    show (mt V ((List.finRange r).map fun i => gl i (y i)).prod).map (q i).pr = _
    rw [GlobalTheory.FixLev.map_mt_list_prod, List.map_map]
    exact (GlobalTheory.FixLev.list_prod_single (fun i' => (mt V (gl i' (y i'))).map (q i).pr) i
      (fun i' hi' => hmat_ne i i' (Ne.symm hi') _) _ (List.nodup_finRange r) (List.mem_finRange i)).trans
      (hgl i (y i)).2
  have hΨΦ : ∀ y, Ψ y = Φ y := fun y => huniq (Φ y) (by rw [← hA]; exact hΦA y) y (hΦloc y)
  have hx_eq : ∀ x ∈ GlobalTheory.FinPl.grpAt V P, Ψ (fun i => lh i x) = x := fun x hx =>
    huniq x (by rw [← hA]; exact hx) _ fun i => GlobalTheory.FixLev.locHom_spec _ _ _ x
  have hmem : ∀ x : GlobalTheory.FinPl.grpAt V P, (x : GA D V) ∈ H ↔ ∀ i, lh i x ∈ L i := fun x =>
    ⟨fun h => hHL _ h, fun h => by rw [← hx_eq x x.2, hΨΦ]; exact hΦH _ h⟩
  refine ⟨?_, ?_⟩
  · have hset : ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P)) =
        ⋂ i, (fun g : GlobalTheory.FinPl.grpAt V P => lh i g.1) ⁻¹' (L i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact hmem g
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hL i).1.preimage ((GlobalTheory.FixLev.continuous_locHom _ _ _).comp continuous_subtype_val)
  · rw [Subtype.isCompact_iff]
    have himg : (((↑) : GlobalTheory.FinPl.grpAt V P → GA D V) ''
        ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P))) =
        Ψ '' Set.pi Set.univ fun i => (L i : Set _) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : GA D V) ∈ H := Subgroup.mem_subgroupOf.1 hx
        exact ⟨fun i => lh i x, fun i _ => hHL _ hx' i, hx_eq x x.2⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨Ψ y, ?_⟩, ?_, rfl⟩
        · rw [hΨΦ]
          exact hΦA y
        · show Ψ y ∈ H
          rw [hΨΦ]
          exact hΦH y fun i => hy i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hL i).2).image hc

theorem isCO_levJ_levB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  intro D ψ σ S r Q hinj
  exact ⟨isCO_iSup_map S.J.W (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₁) (fun i => (Q i).gl₁)
      (fun i g => (Q i).loc₁ g) (fun i => (Q i).L₁.J) (fun i => (Q i).co₁),
    isCO_iSup_map S.B'.V (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₂) (fun i => (Q i).gl₂)
      (fun i g => (Q i).loc₂ g) (fun i => (Q i).L₂.J) (fun i => (Q i).co₂)⟩

end GlobalTheory.QVal.LevCO

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompactOpen_product_levels_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S), Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  first | exact @GlobalTheory.QVal.LevCO.isCO_levJ_levB | exact GlobalTheory.QVal.LevCO.isCO_levJ_levB | (intros; apply GlobalTheory.QVal.LevCO.isCO_levJ_levB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureQuotientGroupProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralOneDoubleCosetEqMulValue
open MeasureTheory GlobalTheory.Grow

namespace GlobalTheory

theorem quotientIntegral_oneDoubleCoset_eq_mul_value (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G)
    (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (ρ : Measure R) (μ : Measure G) (hρ : ρ.IsHaarMeasure) (hρr : ρ.IsMulRightInvariant) (hμ : μ.IsHaarMeasure)
    (t : G) : ∃ w : ℂ, w ≠ 0 ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) →
      (∀ g, f g ≠ 0 → ∃ r ∈ R, ∃ k ∈ K, g = r * t * k) → IsQuotIntL1 ρ μ f (w * f t) := by

  set T : Set G := {g | t⁻¹ * g ∈ K} with hT
  set S : Set R := {r | t⁻¹ * ((r : G) * t) ∈ K} with hS
  have hemb : Topology.IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal

  have hAo : ∀ h : G, IsOpen {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h =>
    hKo.preimage (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  have hAc : ∀ h : G, IsCompact {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h => by
    have h1 : IsCompact ((fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G)) := by
      have e : (fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G) = (fun g => t * g * h⁻¹) '' (K : Set G) := by
        ext g; constructor
        · intro hg; exact ⟨t⁻¹ * (g * h), hg, by group⟩
        · rintro ⟨k, hk, rfl⟩; simpa [mul_assoc] using hk
      rw [e]; exact hKc.image (by fun_prop)
    exact hemb.isCompact_preimage h1
  have hTm : MeasurableSet T := (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμT : μ T = μ K := measure_preimage_mul μ t⁻¹ K
  have hμK0 : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hμKt : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hSo : IsOpen S := by simpa using hAo t
  have hSc : IsCompact S := by simpa using hAc t
  have hρS0 : ρ S ≠ 0 := (hSo.measure_pos ρ ⟨1, by simp [hS]⟩).ne'
  have hρSt : ρ S ≠ ⊤ := hSc.measure_lt_top.ne
  set c : ℝ := ρ.real S with hc
  have hc0 : c ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hρS0, hρSt⟩
  have hμK : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hμK0, hμKt⟩
  refine ⟨(μ.real K : ℂ) / (c : ℂ), div_ne_zero (by exact_mod_cast hμK) (by exact_mod_cast hc0), fun f hfl hfr hfs => ?_⟩
  set a : ℂ := f t / (c : ℂ) with ha
  refine ⟨T.indicator fun _ => a, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hTm).2 (integrableOn_const (by rw [hμT]; exact hμKt))
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e]
    exact (integrable_indicator_iff (hAo h).measurableSet).2
      (integrableOn_const (hAc h).measure_lt_top.ne)
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e, integral_indicator_const _ (hAo h).measurableSet]
    by_cases hne : ∃ s ∈ R, ∃ k ∈ K, h = s * t * k
    · obtain ⟨s, hs, k, hk, rfl⟩ := hne
      have eA : {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = (fun r : R => r * ⟨s, hs⟩) ⁻¹' S := by
        ext r
        simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul]
        have : t⁻¹ * ((r : G) * (s * t * k)) = t⁻¹ * ((r : G) * s * t) * k := by group
        rw [this, Subgroup.mul_mem_cancel_right _ hk]
      have e1 : ρ.real {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = c := by
        rw [eA, hc, measureReal_def, measureReal_def, measure_preimage_mul_right]
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [e1, ha, mul_assoc, hfl s hs, hfr k hk, Complex.real_smul]
      field_simp
    · have hf : f h = 0 := by
        by_contra hf; exact hne (hfs h hf)
      have eA : {r : R | t⁻¹ * ((r : G) * h) ∈ K} = ∅ := by
        ext r
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hr
        exact hne ⟨(r : G)⁻¹, inv_mem r.2, t⁻¹ * ((r : G) * h), hr, by group⟩
      rw [hf, eA]; simp
  · rw [integral_indicator_const _ hTm]
    have e2 : μ.real T = μ.real K := by simp only [measureReal_def, hμT]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
    rw [e2, ha, Complex.real_smul]
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqSumIndicator
namespace GlobalTheory.DoubleCosetIndicator

def dc {G : Type} [Group G] (R K : Subgroup G) (t : G) : Set G :=
  {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}

theorem dc_subset {G : Type} [Group G] (R K : Subgroup G) {s t x : G}
    (hs : x ∈ dc R K s) (ht : x ∈ dc R K t) : dc R K s ⊆ dc R K t := by
  rintro y ⟨a, ha, b, hb, rfl⟩
  obtain ⟨r, hr, κ, hκ, hx⟩ := hs
  obtain ⟨r', hr', κ', hκ', hx'⟩ := ht
  have hrs : r * s * κ = r' * t * κ' := hx.symm.trans hx'
  have hs' : s = r⁻¹ * r' * t * κ' * κ⁻¹ := by
    calc s = r⁻¹ * (r * s * κ) * κ⁻¹ := by group
      _ = r⁻¹ * (r' * t * κ') * κ⁻¹ := by rw [hrs]
      _ = r⁻¹ * r' * t * κ' * κ⁻¹ := by group
  refine ⟨a * r⁻¹ * r', R.mul_mem (R.mul_mem ha (R.inv_mem hr)) hr', κ' * κ⁻¹ * b,
    K.mul_mem (K.mul_mem hκ' (K.inv_mem hκ)) hb, ?_⟩
  rw [hs']
  group

theorem exists_eq_sum_indicator {G : Type} [Group G] {M : Type} [AddCommMonoid M]
    (R K : Subgroup G) (T : Finset G) (φ : G → M)
    (hR : ∀ r ∈ R, ∀ x : G, φ (r * x) = φ x) (hK : ∀ κ ∈ K, ∀ x : G, φ (x * κ) = φ x)
    (hT : ∀ x : G, φ x ≠ 0 → ∃ t ∈ T, x ∈ dc R K t) :
    ∃ c : G → M, (∀ t : G, c t = 0 ∨ c t = φ t) ∧
      ∀ x : G, φ x = ∑ t ∈ T, Set.indicator (dc R K t) (fun _ => c t) x := by
  classical

  let S : G → Finset G := fun t => T.filter (fun t' => dc R K t' = dc R K t)
  let rep : G → G := fun t => if h : (S t).Nonempty then h.choose else t
  let c : G → M := fun t => if t ∈ T ∧ rep t = t then φ t else 0
  have hdc_eq : ∀ {s t x : G}, x ∈ dc R K s → x ∈ dc R K t → dc R K s = dc R K t := fun hs ht =>
    Set.Subset.antisymm (dc_subset R K hs ht) (dc_subset R K ht hs)
  have hinv : ∀ {s x : G}, x ∈ dc R K s → φ x = φ s := by
    rintro s x ⟨r, hr, κ, hκ, rfl⟩
    rw [hK κ hκ, hR r hr]
  refine ⟨c, fun t => ?_, fun x => ?_⟩
  · simp only [c]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hx : ∃ t ∈ T, x ∈ dc R K t
  · obtain ⟨t0, ht0, hxt0⟩ := hx
    have hS : (S t0).Nonempty := ⟨t0, Finset.mem_filter.mpr ⟨ht0, rfl⟩⟩
    obtain ⟨ht1T, ht1dc⟩ := Finset.mem_filter.mp hS.choose_spec
    have hrep : ∀ t, dc R K t = dc R K t0 → rep t = hS.choose := by
      intro t ht
      have hSt : S t = S t0 := by simp only [S, ht]
      simp only [rep, hSt, dif_pos hS]
    have hxt1 : x ∈ dc R K hS.choose := by rw [ht1dc]; exact hxt0
    rw [Finset.sum_eq_single hS.choose]
    · have hc1 : c hS.choose = φ hS.choose := by
        simp only [c]
        rw [if_pos ⟨ht1T, hrep _ ht1dc⟩]
      rw [Set.indicator_of_mem hxt1, hc1, hinv hxt1]
    · intro t _ hne
      by_cases hxt : x ∈ dc R K t
      · have hc0 : c t = 0 := by
          simp only [c]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (h.symm.trans (hrep t (hdc_eq hxt hxt0)))
        rw [Set.indicator_of_mem hxt, hc0]
      · rw [Set.indicator_of_notMem hxt]
    · intro h
      exact absurd ht1T h
  · push_neg at hx
    have hφ : φ x = 0 := by
      by_contra h
      obtain ⟨t, ht, hxt⟩ := hT x h
      exact hx t ht hxt
    rw [hφ]
    symm
    exact Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (hx t ht) _

theorem main : (let d1 : {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → G → Set G := @(fun {G : Type} [Group G] (R K : Subgroup G) (t : G) ↦ {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}); ∀ {G : Type} [inst : Group G] {M : Type} [inst_1 : AddCommMonoid M] (R K : Subgroup G) (T : Finset G) (φ : G → M), (∀ r ∈ R, ∀ (x : G), φ (r * x) = φ x) → (∀ κ ∈ K, ∀ (x : G), φ (x * κ) = φ x) → (∀ (x : G), φ x ≠ (0 : M) → ∃ t ∈ T, x ∈ d1 R K t) → ∃ (c : G → M), (∀ (t : G), c t = (0 : M) ∨ c t = φ t) ∧ ∀ (x : G), φ x = ∑ t ∈ T, Set.indicator (d1 R K t) (fun (x : G) ↦ c t) x) := by
  intro d1 G _ M _ R K T φ hR hK hT
  exact exists_eq_sum_indicator R K T φ hR hK hT

end GlobalTheory.DoubleCosetIndicator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureQuotientGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IterPeel

section Alg

variable {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
  [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂}
  {μ₂ : Measure G₂}

theorem quot_congr {f f' : G₁ → ℂ} {z z' : ℂ} (h : IsQuotIntL1 ρ₁ μ₁ f z) (hf : ∀ x, f x = f' x) (hz : z = z') :
    IsQuotIntL1 ρ₁ μ₁ f' z' := by
  obtain rfl : f = f' := funext hf
  exact hz ▸ h

theorem iterated_integral_congr {f f' : G₁ → G₂ → ℂ} {z z' : ℂ} (h : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z) (hf : ∀ x y, f x y = f' x y)
    (hz : z = z') : Iter2 ρ₁ μ₁ ρ₂ μ₂ f' z' := by
  obtain rfl : f = f' := funext fun x => funext fun y => hf x y
  exact hz ▸ h

theorem iterated_integral_zero : Iter2 ρ₁ μ₁ ρ₂ μ₂ 0 0 :=
  ⟨0, IsQuotIntL1.zero, fun _ => IsQuotIntL1.zero⟩

theorem iterated_integral_add {f f' : G₁ → G₂ → ℂ} {z z' : ℂ} (h : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z) (h' : Iter2 ρ₁ μ₁ ρ₂ μ₂ f' z') :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (f + f') (z + z') := by
  obtain ⟨g, hg, hq⟩ := h
  obtain ⟨g', hg', hq'⟩ := h'
  exact ⟨g + g', hg.add hg', fun q => (hq q).add (hq' q)⟩

theorem iterated_integral_mul {u : G₁ → ℂ} {v : G₂ → ℂ} {c d : ℂ} (hu : IsQuotIntL1 ρ₁ μ₁ u c) (hv : IsQuotIntL1 ρ₂ μ₂ v d) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => u x * v y) (c * d) :=
  ⟨fun x => u x * d, quot_congr (hu.smul d) (fun x => by simp [mul_comm]) (mul_comm _ _),
    fun x => quot_congr (hv.smul (u x)) (fun y => by simp) rfl⟩

end Alg

theorem iterated_integral_unique {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁]
    [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂]
    [BorelSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} (hR₁ : IsClosed (R₁ : Set G₁)) (hR₂ : IsClosed (R₂ : Set G₂))
    {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂} {μ₂ : Measure G₂} [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure]
    [ρ₁.IsHaarMeasure] [ρ₂.IsHaarMeasure] [ρ₁.IsInvInvariant] [ρ₂.IsInvInvariant] {f : G₁ → G₂ → ℂ} {z z' : ℂ}
    (h : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z) (h' : Iter2 ρ₁ μ₁ ρ₂ μ₂ f z') : z = z' := by
  obtain ⟨g, hg, hq⟩ := h
  obtain ⟨g', hg', hq'⟩ := h'
  have e : g = g' := funext fun q => (hq q).unique hR₂ (hq' q)
  subst e
  exact hg.unique hR₁ hg'

section Prod

variable {A B : Type} [Group A] [MeasurableSpace A] [Group B] [MeasurableSpace B] (R : Subgroup A) (S : Subgroup B)

def prodMEquiv : R.prod S ≃ᵐ R × S where
  toEquiv := (R.prodEquiv S).toEquiv
  measurable_toFun := by
    change Measurable fun x : R.prod S => ((⟨x.1.1, x.2.1⟩ : R), (⟨x.1.2, x.2.2⟩ : S))
    exact (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
      (measurable_snd.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    change Measurable fun q : R × S => (⟨((q.1 : A), (q.2 : B)), ⟨q.1.2, q.2.2⟩⟩ : R.prod S)
    exact ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)).subtype_mk

theorem quot_prod {r : Measure R} {s : Measure S} {a : Measure A} {b : Measure B} [SFinite r] [SFinite s] [SFinite a]
    [SFinite b] (p : Measure (R.prod S)) (hp : p.map (R.prodEquiv S) = r.prod s) {u : A → ℂ} {v : B → ℂ} {c d : ℂ}
    (hu : IsQuotIntL1 r a u c) (hv : IsQuotIntL1 s b v d) :
    IsQuotIntL1 p (a.prod b) (fun X => u X.1 * v X.2) (c * d) := by
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := hu
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := hv
  have hp' : p.map (prodMEquiv R S) = r.prod s := hp
  refine ⟨fun X => U X.1 * V X.2, hU1.mul_prod hV1, fun X => ?_, fun X => ?_, ?_⟩
  · have := (hU2 X.1).mul_prod (hV2 X.2)
    rw [← hp', integrable_map_equiv] at this
    exact this
  · have e := integral_map_equiv (μ := p) (prodMEquiv R S)
      (fun q : R × S => U ((q.1 : A) * X.1) * V ((q.2 : B) * X.2))
    have e2 := integral_prod_mul (μ := r) (ν := s) (fun q : R => U ((q : A) * X.1)) (fun q : S => V ((q : B) * X.2))
    rw [hp'] at e
    show u X.1 * v X.2 = _
    rw [hU3, hV3, ← e2, e]
    rfl
  · rw [integral_prod_mul, hU4, hV4]

end Prod

end GlobalTheory.IterPeel

namespace GlobalTheory.IterPeel

section Cells

variable {G : Type} [Group G]

def cell (R K : Subgroup G) (t : G) : Set G := {x | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}

def chi (R K : Subgroup G) (t : G) (x : G) : ℂ := (cell R K t).indicator 1 x

theorem mul_mem_cell_left {R K : Subgroup G} {t x s : G} (hs : s ∈ R) : s * x ∈ cell R K t ↔ x ∈ cell R K t := by
  constructor
  · rintro ⟨r, hr, κ, hκ, h⟩
    refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, κ, hκ, ?_⟩
    calc x = s⁻¹ * (s * x) := by group
      _ = s⁻¹ * (r * t * κ) := by rw [h]
      _ = s⁻¹ * r * t * κ := by group
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    exact ⟨s * r, R.mul_mem hs hr, κ, hκ, by group⟩

theorem mul_mem_cell_right {R K : Subgroup G} {t x k : G} (hk : k ∈ K) : x * k ∈ cell R K t ↔ x ∈ cell R K t := by
  constructor
  · rintro ⟨r, hr, κ, hκ, h⟩
    refine ⟨r, hr, κ * k⁻¹, K.mul_mem hκ (K.inv_mem hk), ?_⟩
    calc x = (x * k) * k⁻¹ := by group
      _ = (r * t * κ) * k⁻¹ := by rw [h]
      _ = r * t * (κ * k⁻¹) := by group
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    exact ⟨r, hr, κ * k, K.mul_mem hκ hk, by group⟩

theorem decomp {M : Type} [AddCommMonoid M] (R K : Subgroup G) (T : Finset G) : ∀ φ : G → M,
    (∀ r ∈ R, ∀ x, φ (r * x) = φ x) → (∀ κ ∈ K, ∀ x, φ (x * κ) = φ x) →
    (∀ x, φ x ≠ 0 → ∃ t ∈ T, x ∈ cell R K t) →
    ∃ c : G → M, (∀ t, c t = 0 ∨ c t = φ t) ∧ ∀ x, φ x = ∑ t ∈ T, (cell R K t).indicator (fun _ => c t) x := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetIndicator.main
  | exact _root_.GlobalTheory.DoubleCosetIndicator.main
  | (apply _root_.GlobalTheory.DoubleCosetIndicator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetIndicator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetIndicator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetIndicator.main ..)

theorem indicator_fun_apply {X Y : Type} (s : Set X) (c : Y → ℂ) (x : X) (y : Y) :
    (s.indicator (fun _ => c) x) y = s.indicator 1 x * c y := by
  classical
  by_cases h : x ∈ s <;> simp [h]

theorem indicator_const_eq {X : Type} (s : Set X) (m : ℂ) (x : X) :
    s.indicator (fun _ => m) x = s.indicator 1 x * m := by
  classical
  by_cases h : x ∈ s <;> simp [h]

end Cells

theorem mem_cell_prod {A B : Type} [Group A] [Group B] (R K : Subgroup A) (S L : Subgroup B) (t X : A × B) :
    X ∈ cell (R.prod S) (K.prod L) t ↔ X.1 ∈ cell R K t.1 ∧ X.2 ∈ cell S L t.2 := by
  constructor
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    rw [Subgroup.mem_prod] at hr hκ
    exact ⟨⟨r.1, hr.1, κ.1, hκ.1, rfl⟩, ⟨r.2, hr.2, κ.2, hκ.2, rfl⟩⟩
  · rintro ⟨⟨r, hr, κ, hκ, h1⟩, ⟨r', hr', κ', hκ', h2⟩⟩
    exact ⟨(r, r'), Subgroup.mem_prod.2 ⟨hr, hr'⟩, (κ, κ'), Subgroup.mem_prod.2 ⟨hκ, hκ'⟩, Prod.ext h1 h2⟩

theorem chi_prod {A B : Type} [Group A] [Group B] (R K : Subgroup A) (S L : Subgroup B) (t X : A × B) :
    chi (R.prod S) (K.prod L) t X = chi R K t.1 X.1 * chi S L t.2 X.2 := by
  classical
  simp only [chi, Set.indicator_apply, mem_cell_prod, Pi.one_apply]
  split_ifs <;> simp_all

theorem quot_chi {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G)
    (hR : IsClosed (R : Set G)) (hK : IsCO K) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (t : G) : ∃ w, IsQuotIntL1 ρ μ (chi R K t) w := by
  classical
  have : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  obtain ⟨w, -, hw⟩ := quotientIntegral_oneDoubleCoset_eq_mul_value G R K hR hK.2 hK.1 ρ μ inferInstance inferInstance inferInstance t
  refine ⟨_, hw _ ?_ ?_ ?_⟩
  · intro r hr g; by_cases h : g ∈ cell R K t <;> simp [chi, h, mul_mem_cell_left hr]
  · intro k hk g; by_cases h : g ∈ cell R K t <;> simp [chi, h, mul_mem_cell_right hk]
  · intro g hg
    by_contra h
    have h' : g ∉ cell R K t := h
    exact hg (by unfold chi; exact Set.indicator_of_notMem h' _)

end GlobalTheory.IterPeel

namespace GlobalTheory.IterPeel

theorem iterated_integral_product_groups : ∀ (A₁ : Type) [Group A₁] [TopologicalSpace A₁] [IsTopologicalGroup A₁] [SecondCountableTopology A₁] [LocallyCompactSpace A₁] [T2Space A₁] [MeasurableSpace A₁] [BorelSpace A₁] (B₁ : Type) [Group B₁] [TopologicalSpace B₁] [IsTopologicalGroup B₁] [SecondCountableTopology B₁] [LocallyCompactSpace B₁] [T2Space B₁] [MeasurableSpace B₁] [BorelSpace B₁] (A₂ : Type) [Group A₂] [TopologicalSpace A₂] [IsTopologicalGroup A₂] [SecondCountableTopology A₂] [LocallyCompactSpace A₂] [T2Space A₂] [MeasurableSpace A₂] [BorelSpace A₂] (B₂ : Type) [Group B₂] [TopologicalSpace B₂] [IsTopologicalGroup B₂] [SecondCountableTopology B₂] [LocallyCompactSpace B₂] [T2Space B₂] [MeasurableSpace B₂] [BorelSpace B₂] (R₁ : Subgroup A₁) (S₁ : Subgroup B₁) (R₂ : Subgroup A₂) (S₂ : Subgroup B₂), IsClosed (R₁ : Set A₁) → IsClosed (S₁ : Set B₁) → IsClosed (R₂ : Set A₂) → IsClosed (S₂ : Set B₂) → ∀ (a₁ : Measure A₁) (b₁ : Measure B₁) (a₂ : Measure A₂) (b₂ : Measure B₂) (r₁ : Measure R₁) (s₁ : Measure S₁) (r₂ : Measure R₂) (s₂ : Measure S₂) (p₁ : Measure (R₁.prod S₁)) (p₂ : Measure (R₂.prod S₂)), a₁.IsHaarMeasure → b₁.IsHaarMeasure → a₂.IsHaarMeasure → b₂.IsHaarMeasure → r₁.IsHaarMeasure → s₁.IsHaarMeasure → r₂.IsHaarMeasure → s₂.IsHaarMeasure → r₁.IsInvInvariant → s₁.IsInvInvariant → r₂.IsInvInvariant → s₂.IsInvInvariant → p₁.map (R₁.prodEquiv S₁) = r₁.prod s₁ → p₂.map (R₂.prodEquiv S₂) = r₂.prod s₂ → ∀ (K₁ : Subgroup A₁) (L₁ : Subgroup B₁) (K₂ : Subgroup A₂) (L₂ : Subgroup B₂), IsCO K₁ → IsCO L₁ → IsCO K₂ → IsCO L₂ → ∀ f : A₁ × B₁ → A₂ × B₂ → ℂ, (∀ x y, ∀ r ∈ R₂.prod S₂, ∀ κ ∈ K₂.prod L₂, f x (r * y * κ) = f x y) → (∀ x y, ∀ κ ∈ K₁.prod L₁, f (x * κ) y = f x y) → (∀ x y, ∀ r ∈ R₁.prod S₁, f (r * x) y = f x y) → (∃ T : Finset (A₁ × B₁), ∀ x y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₁.prod S₁, ∃ κ ∈ K₁.prod L₁, x = r * t * κ) → (∀ x, ∃ T : Finset (A₂ × B₂), ∀ y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₂.prod S₂, ∃ κ ∈ K₂.prod L₂, y = r * t * κ) → ∀ (g : A₁ → A₂ → ℂ) (z : ℂ), (∀ x y, Iter2 s₁ b₁ s₂ b₂ (fun x' y' => f (x, x') (y, y')) (g x y)) → Iter2 r₁ a₁ r₂ a₂ g z → Iter2 p₁ (a₁.prod b₁) p₂ (a₂.prod b₂) f z := by
  intro A₁ _ _ _ _ _ _ _ _ B₁ _ _ _ _ _ _ _ _ A₂ _ _ _ _ _ _ _ _ B₂ _ _ _ _ _ _ _ _ R₁ S₁ R₂ S₂ hR₁ hS₁ hR₂ hS₂
    a₁ b₁ a₂ b₂ r₁ s₁ r₂ s₂ p₁ p₂ ha₁ hb₁ ha₂ hb₂ hr₁ hs₁ hr₂ hs₂ hir₁ his₁ hir₂ his₂ hp₁ hp₂ K₁ L₁ K₂ L₂
    hK₁ hL₁ hK₂ hL₂ f hfy hfx hfl hTx hTy g z hg hz
  classical
  haveI : LocallyCompactSpace R₁ := hR₁.locallyCompactSpace
  haveI : LocallyCompactSpace S₁ := hS₁.locallyCompactSpace
  haveI : LocallyCompactSpace R₂ := hR₂.locallyCompactSpace
  haveI : LocallyCompactSpace S₂ := hS₂.locallyCompactSpace

  let P : (A₁ × B₁ → A₂ × B₂ → ℂ) → Prop := fun F => ∃ (G : A₁ → A₂ → ℂ) (Z : ℂ),
    (∀ x y, Iter2 s₁ b₁ s₂ b₂ (fun x' y' => F (x, x') (y, y')) (G x y)) ∧ Iter2 r₁ a₁ r₂ a₂ G Z ∧
      Iter2 p₁ (a₁.prod b₁) p₂ (a₂.prod b₂) F Z
  have P0 : P 0 := ⟨0, 0, fun x y => iterated_integral_zero, iterated_integral_zero, iterated_integral_zero⟩
  have Padd : ∀ F F', P F → P F' → P (F + F') := by
    rintro F F' ⟨G, Z, h1, h2, h3⟩ ⟨G', Z', h1', h2', h3'⟩
    exact ⟨G + G', Z + Z', fun x y => iterated_integral_add (h1 x y) (h1' x y), iterated_integral_add h2 h2', iterated_integral_add h3 h3'⟩
  have Pel : ∀ (t : A₁ × B₁) (u : A₂ × B₂) (d : ℂ),
      P (fun X Y => d * (chi (R₁.prod S₁) (K₁.prod L₁) t X * chi (R₂.prod S₂) (K₂.prod L₂) u Y)) := by
    intro t u d
    obtain ⟨w₁, hw₁⟩ := quot_chi R₁ K₁ hR₁ hK₁ r₁ a₁ t.1
    obtain ⟨w₁', hw₁'⟩ := quot_chi S₁ L₁ hS₁ hL₁ s₁ b₁ t.2
    obtain ⟨w₂, hw₂⟩ := quot_chi R₂ K₂ hR₂ hK₂ r₂ a₂ u.1
    obtain ⟨w₂', hw₂'⟩ := quot_chi S₂ L₂ hS₂ hL₂ s₂ b₂ u.2
    refine ⟨fun x y => d * w₁' * w₂' * chi R₁ K₁ t.1 x * chi R₂ K₂ u.1 y, d * w₁' * w₂' * w₁ * w₂,
      fun x y => ?_, ?_, ?_⟩
    · refine iterated_integral_congr (iterated_integral_mul (hw₁'.smul (d * chi R₁ K₁ t.1 x * chi R₂ K₂ u.1 y)) hw₂') (fun x' y' => ?_) (by ring)
      simp only [chi_prod, Pi.smul_apply, smul_eq_mul]
      ring
    · refine iterated_integral_congr (iterated_integral_mul (hw₁.smul (d * w₁' * w₂')) hw₂) (fun x y => ?_) (by ring)
      simp only [Pi.smul_apply, smul_eq_mul]
    · refine iterated_integral_congr (iterated_integral_mul ((quot_prod R₁ S₁ p₁ hp₁ hw₁ hw₁').smul d) (quot_prod R₂ S₂ p₂ hp₂ hw₂ hw₂'))
        (fun X Y => ?_) (by ring)
      simp only [chi_prod, Pi.smul_apply, smul_eq_mul]
      ring

  obtain ⟨T, hT⟩ := hTx
  obtain ⟨c, hc, hce⟩ := decomp (M := A₂ × B₂ → ℂ) (R₁.prod S₁) (K₁.prod L₁) T f
    (fun r hr x => funext fun y => hfl x y r hr) (fun κ hκ x => funext fun y => hfx x y κ hκ)
    (fun x hx => by
      obtain ⟨y, hy⟩ : ∃ y, f x y ≠ 0 := by
        by_contra h; push_neg at h; exact hx (funext h)
      obtain ⟨t, ht, r, hr, κ, hκ, e⟩ := hT x y hy
      exact ⟨t, ht, r, hr, κ, hκ, e⟩)
  have hY : ∀ t, ∃ (U : Finset (A₂ × B₂)) (d : A₂ × B₂ → ℂ),
      ∀ y, c t y = ∑ u ∈ U, (cell (R₂.prod S₂) (K₂.prod L₂) u).indicator (fun _ => d u) y := by
    intro t
    rcases hc t with h | h
    · exact ⟨∅, 0, fun y => by simp [h]⟩
    · obtain ⟨U, hU⟩ := hTy t
      obtain ⟨d, -, hd⟩ := decomp (M := ℂ) (R₂.prod S₂) (K₂.prod L₂) U (f t)
        (fun r hr y => by simpa using hfy t y r hr 1 (Subgroup.one_mem _))
        (fun κ hκ y => by simpa using hfy t y 1 (Subgroup.one_mem _) κ hκ)
        (fun y hy => by
          obtain ⟨u, hu, r, hr, κ, hκ, e⟩ := hU y hy
          exact ⟨u, hu, r, hr, κ, hκ, e⟩)
      exact ⟨U, d, fun y => by rw [h, hd y]⟩
  choose U d hd using hY
  have hfe : f = ∑ t ∈ T, ∑ u ∈ U t,
      (fun X Y => d t u * (chi (R₁.prod S₁) (K₁.prod L₁) t X * chi (R₂.prod S₂) (K₂.prod L₂) u Y)) := by
    funext X Y
    rw [hce X, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_apply, Finset.sum_apply, indicator_fun_apply, hd t Y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [indicator_const_eq]
    simp only [chi]
    ring
  have hPf : P f := by
    rw [hfe]
    refine Finset.sum_induction _ P Padd P0 fun t _ => ?_
    exact Finset.sum_induction _ P Padd P0 fun u _ => Pel t u (d t u)
  obtain ⟨G, Z, h1, h2, h3⟩ := hPf
  have hG : G = g := funext fun x => funext fun y => iterated_integral_unique hS₁ hS₂ (h1 x y) (hg x y)
  subst hG
  rw [← iterated_integral_unique hR₁ hR₂ h2 hz]
  exact h3

end GlobalTheory.IterPeel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureQuotientGroupProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_quotient_group_product : ∀ (A₁ : Type) [Group A₁] [TopologicalSpace A₁] [IsTopologicalGroup A₁] [SecondCountableTopology A₁] [LocallyCompactSpace A₁] [T2Space A₁] [MeasurableSpace A₁] [BorelSpace A₁] (B₁ : Type) [Group B₁] [TopologicalSpace B₁] [IsTopologicalGroup B₁] [SecondCountableTopology B₁] [LocallyCompactSpace B₁] [T2Space B₁] [MeasurableSpace B₁] [BorelSpace B₁] (A₂ : Type) [Group A₂] [TopologicalSpace A₂] [IsTopologicalGroup A₂] [SecondCountableTopology A₂] [LocallyCompactSpace A₂] [T2Space A₂] [MeasurableSpace A₂] [BorelSpace A₂] (B₂ : Type) [Group B₂] [TopologicalSpace B₂] [IsTopologicalGroup B₂] [SecondCountableTopology B₂] [LocallyCompactSpace B₂] [T2Space B₂] [MeasurableSpace B₂] [BorelSpace B₂] (R₁ : Subgroup A₁) (S₁ : Subgroup B₁) (R₂ : Subgroup A₂) (S₂ : Subgroup B₂), IsClosed (R₁ : Set A₁) → IsClosed (S₁ : Set B₁) → IsClosed (R₂ : Set A₂) → IsClosed (S₂ : Set B₂) → ∀ (a₁ : Measure A₁) (b₁ : Measure B₁) (a₂ : Measure A₂) (b₂ : Measure B₂) (r₁ : Measure R₁) (s₁ : Measure S₁) (r₂ : Measure R₂) (s₂ : Measure S₂) (p₁ : Measure (R₁.prod S₁)) (p₂ : Measure (R₂.prod S₂)), a₁.IsHaarMeasure → b₁.IsHaarMeasure → a₂.IsHaarMeasure → b₂.IsHaarMeasure → r₁.IsHaarMeasure → s₁.IsHaarMeasure → r₂.IsHaarMeasure → s₂.IsHaarMeasure → r₁.IsInvInvariant → s₁.IsInvInvariant → r₂.IsInvInvariant → s₂.IsInvInvariant → p₁.map (R₁.prodEquiv S₁) = r₁.prod s₁ → p₂.map (R₂.prodEquiv S₂) = r₂.prod s₂ → ∀ (K₁ : Subgroup A₁) (L₁ : Subgroup B₁) (K₂ : Subgroup A₂) (L₂ : Subgroup B₂), IsCO K₁ → IsCO L₁ → IsCO K₂ → IsCO L₂ → ∀ f : A₁ × B₁ → A₂ × B₂ → ℂ, (∀ x y, ∀ r ∈ R₂.prod S₂, ∀ κ ∈ K₂.prod L₂, f x (r * y * κ) = f x y) → (∀ x y, ∀ κ ∈ K₁.prod L₁, f (x * κ) y = f x y) → (∀ x y, ∀ r ∈ R₁.prod S₁, f (r * x) y = f x y) → (∃ T : Finset (A₁ × B₁), ∀ x y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₁.prod S₁, ∃ κ ∈ K₁.prod L₁, x = r * t * κ) → (∀ x, ∃ T : Finset (A₂ × B₂), ∀ y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₂.prod S₂, ∃ κ ∈ K₂.prod L₂, y = r * t * κ) → ∀ (g : A₁ → A₂ → ℂ) (z : ℂ), (∀ x y, Iter2 s₁ b₁ s₂ b₂ (fun x' y' => f (x, x') (y, y')) (g x y)) → Iter2 r₁ a₁ r₂ a₂ g z → Iter2 p₁ (a₁.prod b₁) p₂ (a₂.prod b₂) f z := by
  first | exact @GlobalTheory.IterPeel.iterated_integral_product_groups | exact GlobalTheory.IterPeel.iterated_integral_product_groups | (intros; apply GlobalTheory.IterPeel.iterated_integral_product_groups <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepAdelicIntegralFiniteTwistPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QVal

theorem valQr_succ (D : D7) (r : ℕ) (IH : ValQr D r) : ValQr D (r + 1) := by
  intro ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  obtain ⟨lc₁, lc₂, cl₁, cl₂, cl₃, cl₄, μ₁', ρ₁', μ₂', ρ₂', m₁, s₁, m₂, s₂, p₁, p₂, hN', hL, i₁, i₂, i₃, i₄, e₁, e₂, hred⟩ :=
    GlobalTheory.T.periodGroups_reduce_splitPlaceFamily_succ D ψ σ S r Q hinj μ₁ ρ₁ μ₂ ρ₂ hN
  have hN'' := hN'
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := hN''
  have hL' := hL
  obtain ⟨b1, -, b3, -, b5, -, b7, -⟩ := hL'
  obtain ⟨co₁, co₂⟩ := GlobalTheory.T.isCompactOpen_product_levels_family D ψ σ S r (fun i => Q i.succ) (hinj.comp (Fin.succ_injective _))
  obtain ⟨v1, v2, v3⟩ := GlobalTheory.T.doubleThetaStep_integrand_invariant_at_succ_places D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  obtain ⟨n1, n2⟩ := GlobalTheory.T.doubleThetaStep_integrand_finite_doubleCosets D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  apply hred (integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)
  haveI := lc₁
  haveI := lc₂
  haveI : BorelSpace (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) := GlobalTheory.SplitFlip.borel_GL
  exact GlobalTheory.T.haar_measure_quotient_group_product _ _ _ _ _ _ _ _ cl₁ cl₃ cl₂ cl₄ μ₁' m₁ μ₂' m₂ ρ₁' s₁ ρ₂' s₂ p₁ p₂ a1 b1 a3 b5 a2 b3 a4 b7 i₁ i₃ i₂ i₄
    e₁ e₂ _ _ _ _ co₁ (Q 0).co₁ co₂ (Q 0).co₂ (pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) v1 v2 v3 n1 n2
    (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) _
    (fun x y => GlobalTheory.T.iteratedInnerIntegral_at_first_of_splitPlaces D ψ hψ σ S r Q hinj m₁ s₁ m₂ s₂ hL c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH x.1 x.2 y.1 y.2)
    (GlobalTheory.T.iteratedIntegralValue_succ_places_outer D r IH ψ hψ σ S Q hinj μ₁' ρ₁' μ₂' ρ₂' hN' c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH)

theorem valQ : ∀ D : D7, ValQ D := fun D => valQ_of_valQr D fun r => by
  induction r with
  | zero => exact GlobalTheory.T.iteratedIntegralValueAtRPlaces_zero D
  | succ r ih => exact valQr_succ D r ih

end GlobalTheory.QVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepAdelicIntegralFiniteTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_adelicIntegral_finiteTwistPlaces : ∀ D : D7, ValQ D := by
  first | exact @GlobalTheory.QVal.valQ | exact GlobalTheory.QVal.valQ | (intros; apply GlobalTheory.QVal.valQ <;> assumption)
end

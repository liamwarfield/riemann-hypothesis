module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Y.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
    IsTanAtG Y.oF.t (ptF y) w ∧ w ≫ Y.m0.toSABMap.φ = u ∧ w ≫ Y.m.φ = v

def Matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S)) : Prop :=
  a.x = ptF y ≫ Y.jQ ∧
    (∀ i : Fin Dw.p, ∃ j : Fin (Dw.mult τ.1), (j : ℕ) = i ∧ SameVec Y y (y.u τ.1 j) (a.v i).left) ∧
    ∀ i : Fin Dw.q, ∃ j : Fin (Dw.mult (conjEmb τ.1)), (j : ℕ) = i ∧ SameVec Y y (y.u (conjEmb τ.1) j) (a.w i).left

def Reads (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H)
    (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), GlobalTheory.FlatLine.Tested y →
    ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a →
      evR Xo c f y = sig S (algebraMap c.F S) a

end GlobalTheory.BdryUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.FormMul

variable {n : ℕ}

theorem repr_mul (a b : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (a * b) S = ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr a p.1 * (bas n).repr b p.2 * (bas n).repr (bas n p.1 * bas n p.2) S := by
  conv_lhs => rw [← (bas n).sum_repr a, ← (bas n).sum_repr b]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_coefwise (T : (V n → ℂ) → ℂ) (H : V n → Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (coefwise T H) S = T (fun x => (bas n).repr (H x) S) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [coefwise, map_sum, Finsupp.single_apply]

theorem coefwise_mul {v : V n} {T : (V n → ℂ) → ℂ}
    (hsum : ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T (fun x => ∑ p, f p x) = ∑ p, T (f p))
    (hmul : ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T (fun x => f x * g x) = f v * T g + T f * g v)
    (hconst : ∀ c : ℂ, T (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    coefwise T (fun x => F x * G x) = coefwise T F * G v + F v * coefwise T G := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (F x * G x) S) = fun x => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
    funext fun x => repr_mul _ _ _
  rw [repr_coefwise, e, map_add (f := _), Finsupp.add_apply, repr_mul (coefwise T F), repr_mul (F v)]
  simp only [repr_coefwise]
  rw [hsum (fun p x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S)
    (fun p => ((hF p.1).mul (hG p.2)).mul (differentiableAt_const _)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hmul (fun x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2) (fun _ => (bas n).repr (bas n p.1 * bas n p.2) S)
    ((hF p.1).mul (hG p.2)) (differentiableAt_const _), hconst,
    hmul (fun x => (bas n).repr (F x) p.1) (fun x => (bas n).repr (G x) p.2) (hF p.1) (hG p.2)]
  ring

theorem exists_ι_mul (y : Alt n) : ∃ y' : Alt n, ∀ m, ExteriorAlgebra.ι ℂ m * y = y' * ExteriorAlgebra.ι ℂ m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨algebraMap ℂ _ r, fun m => (Algebra.commutes r _).symm⟩
  | ι x => exact ⟨-ExteriorAlgebra.ι ℂ x, fun m => by
      rw [neg_mul]; exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m x)⟩
  | mul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', fun m => by rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]⟩
  | add a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', fun m => by rw [mul_add, ha, hb, add_mul]⟩

theorem sum_mul_leibniz {v : V n} (g : Fin n → (Fin n ⊕ Fin n → ℂ)) (T : Fin n → (V n → ℂ) → ℂ)
    (hsum : ∀ a, ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T a (fun x => ∑ p, f p x) = ∑ p, T a (f p))
    (hmul : ∀ a, ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T a (fun x => f x * g x) = f v * T a g + T a f * g v)
    (hconst : ∀ a, ∀ c : ℂ, T a (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      (∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F) * G v +
        y * ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G := by
  obtain ⟨y, hy⟩ := exists_ι_mul (F v)
  refine ⟨y, ?_⟩
  have h (a : Fin n) : ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F * G v + y * (ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G) := by
    simp only [coefwise_mul (hsum a) (hmul a) (hconst a) hF hG, mul_add, ← mul_assoc, hy]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

theorem delAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, delAt (fun x => F x * G x) v = delAt F v * G v + y * delAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inl a) 1) (fun a f => del f v (coordVec a))
    (fun a f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => del_mul hf hg _) (fun a c => by rw [del_const]; rfl) hF hG

theorem dbarAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, dbarAt (fun x => F x * G x) v = dbarAt F v * G v + y * dbarAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inr a) 1) (fun a f => dbar f v (coordVec a))
    (fun a f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => dbar_mul hf hg _) (fun a c => by rw [dbar_const]; rfl) hF hG

variable {M : Type} [TopologicalSpace M]

theorem loc_mul (A : HolAtlas M n) (α β : A.Fld) (i : A.ι) (v : V n) :
    A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · simp

theorem differentiableAt_coef {A : HolAtlas M n} {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt
    (by simp)

end GlobalTheory.CxForm.FormMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
noncomputable section

open ValuativeRel Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace GlobalTheory.GaussNonvanish

section Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rep {c : ℕ} (y : Res k c) : k := ((Quotient.out y : 𝒪[k]) : k)

theorem rep_le_one {c : ℕ} (y : Res k c) : valuation k (rep y) ≤ 1 := (Quotient.out y).2

theorem mk_eq_mk_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) a = Ideal.Quotient.mk _ b ↔
      valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd, ← map_pow]
  rfl

theorem val_pow_lt_one {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) : valuation k (ϖ : k) ^ c < 1 := by
  have h : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  exact pow_lt_one' h (by omega)

theorem val_rep_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    valuation k (rep (y : Res k c)) = 1 := by
  have h1 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c) - 1) ≤
      valuation k (ϖ : k) ^ c := by
    have := (mk_eq_mk_iff hϖ c (Quotient.out (y : Res k c) * Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c)) 1).1
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Units.mul_inv, map_one])
    simpa [rep] using this
  have h2 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c)) = 1 := by
    have := (valuation k).map_one_add_of_lt (h1.trans_lt (val_pow_lt_one hϖ hc))
    simpa using this
  rw [map_mul] at h2
  refine le_antisymm (rep_le_one _) ?_
  calc (1 : ValueGroupWithZero k) = _ := h2.symm
    _ ≤ _ := mul_le_of_le_one_right' (rep_le_one _)

theorem rep_ne_zero {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : rep (y : Res k c) ≠ 0 := by
  intro h
  have := val_rep_unit hϖ hc y
  rw [h, map_zero] at this
  exact zero_ne_one this

def uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : kˣ := Units.mk0 _ (rep_ne_zero hϖ hc y)

theorem psi_congr {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1) {a b : k} (h : valuation k (a - b) ≤ 1) : ψl a = ψl b := by
  rw [show a = b + (a - b) by ring, hadd, hO _ h, mul_one]

theorem nu_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν) {a b : kˣ}
    (hb : valuation k (b : k) = 1) (h : valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c) : ν a = ν b := by
  have hlt : valuation k ((a : k) - b) < valuation k (b : k) := by
    rw [hb]; exact h.trans_lt (val_pow_lt_one hϖ hc1)
  have ha : valuation k (a : k) = 1 := ((valuation k).map_eq_of_sub_lt hlt).trans hb
  have hw : a * b⁻¹ ∈ unitCong (ϖ ^ c) := by
    refine ⟨by simp [ha, hb], ?_⟩
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ b.ne_zero]
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one, Units.val_pow_eq_pow_val, map_pow]
    exact h
  have := hc _ hw
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

end Generic
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def gS (ψl : k → ℂ) (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (x : k) : ℂ :=
  ∑ y : (Res k c)ˣ, (((ν (uRep hϖ hc y))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep (y : Res k c) / (ϖ : k) ^ c)

variable {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
  {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
include hadd hO hc

end Sums
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_condLE {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (hν : Continuous fun x : kˣ => (ν x : ℂ)) :
    ∃ e, CondLE ϖ e ν := by
  have hopen : IsOpen {x : kˣ | ‖(ν x : ℂ) - 1‖ < 1 / 2} := isOpen_lt (by fun_prop) continuous_const
  obtain ⟨V, hV, hV'⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.1 hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ Units.val ⁻¹' V := by rw [hV']; simp
    simpa using this
  have h2 : (fun z : k => z + 1) ⁻¹' V ∈ 𝓝 (0 : k) :=
    (hV.preimage (by fun_prop)).mem_nhds (by simpa using h1)
  obtain ⟨s, hs⟩ := exists_cball_subset h2
  obtain ⟨p, hp, hp'⟩ := GlobalTheory.LocLanglands.exists_unit_pow k (ord k s).toNat
  have hsmall : ∀ x ∈ unitCong (ϖ ^ (ord k s).toNat), ‖(ν x : ℂ) - 1‖ < 1 / 2 := fun x hx => by
    have h3 : (x : k) - 1 ∈ GlobalTheory.SplitWeil.cball s := by
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      refine hx.2.trans ?_
      rw [Units.val_pow_eq_pow_val, map_pow, hϖ, ← hp, GlobalTheory.LocLanglands.valuation_le_iff_ord, hp']
      exact Int.self_le_toNat _
    have h4 : x ∈ Units.val ⁻¹' V := by simpa using hs h3
    rw [hV'] at h4
    exact h4
  refine ⟨(ord k s).toNat, fun x hx => Units.ext ?_⟩
  refine GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m => ?_
  have := hsmall (x ^ m) (pow_mem hx m)
  rw [map_pow, Units.val_pow_eq_pow_val] at this
  exact this.le

end Main
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Place

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel

theorem val_le_one_iff {F : Type} [Field F] [NumberField F] (v : Pl F) (x : Fv F v) :
    valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

end Place
end GlobalTheory.GaussNonvanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.TripleSpace

theorem hasSig_neg_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (-M) q p := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨?_, ?_⟩
  · have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  · let Q : Matrix (Fin n) (Fin q ⊕ Fin p) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e Sum.swap
    refine ⟨Q.map star, ?_⟩
    have hQ : (Q.map star)ᵀ = Qᴴ := rfl
    have hQ2 : (Q.map star).map star = Q := by ext a b; simp
    rw [hQ, hQ2, Matrix.mul_neg, Matrix.neg_mul]
    have key : Qᴴ * M * Q = ((Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) *
        Matrix.reindex e e M * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix Sum.swap Sum.swap := by
      have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by ext a b; rfl
      have hM : M = (Matrix.reindex e e M).submatrix e e := by ext a b; simp
      have hQh : Qᴴ = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ.submatrix Sum.swap e := by
        simp only [Q, Matrix.conjTranspose_submatrix]
      rw [hc, hQh, hM, ← Matrix.submatrix_mul _ _ _ e _ e.bijective, Matrix.reindex_apply,
        Matrix.submatrix_submatrix]
      simp only [Q]
      rw [← Matrix.submatrix_mul _ _ _ e _ e.bijective]
      simp [Matrix.reindex_apply]
    rw [key, hP]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply]


open Formalism.IndefR.Datum in
theorem isCartan_neg_conj {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (-(G.map star)) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsG : sᴴ * G = G * s := by
    calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = (sᴴ * G * s) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h2]
  have e2 : sᵀ * G.map star * s.map star = G.map star := by
    have := congrArg (fun X => X.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have a1 : sᴴ.map (starRingEnd ℂ) = sᵀ := by ext a b; simp [Matrix.conjTranspose_apply]
    have a2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = M.map star := fun M => rfl
    rw [a1, a2, a2] at this
    exact this
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · have e1 : (-s).map star = -(s.map star) := by ext a b; simp
    rw [e1, Matrix.transpose_neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, e2]
  · intro x hx
    have hz := h3.dotProduct_mulVec_pos hx
    have hGs : (G.map star) *ᵥ star x = star (G *ᵥ x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum]
    have key : ((-s) *ᵥ x) ⬝ᵥ ((-(G.map star)) *ᵥ star x) = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg, hGs,
        ← star_star (s *ᵥ x), star_dotProduct_star]
      congr 1
      rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hsG]
    rw [key, Complex.star_def, Complex.conj_re]
    exact (Complex.pos_iff.1 hz).1

theorem star_gram {D : D7} (V : HSp D) (a b : Fin V.rank) : star (V.gram a b) = V.gram b a :=
  V.herm.eq (V.frame a) (V.frame b)

theorem form_neg_eq {D : D7} (V : HSp D) (y x : Fin V.rank → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x =
      -star (∑ i, ∑ j, star ((star x) i) * V.gram i j * (star y) j) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Matrix.smul_apply, star_sum, Pi.star_apply,
    star_star, star_mul', star_gram, Finset.mul_sum, smul_eq_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show y b * (-1 * V.gram b a * star (x a)) = -(star (x a) * V.gram b a * y b)
  ring

theorem mem_starLat_iff_form {D : D7} (V : HSp D) {Λ₀ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hsd : IsSelfDualC V Λ₀) (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Col.starLat D.host.E Λ₀ ↔ ∀ x ∈ Formalism.L2.Col.starLat D.host.E Λ₀,
      IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x) := by
  rw [Formalism.L2.Col.mem_starLat, hsd.2]
  constructor
  · intro H x hx
    obtain ⟨b, hb⟩ := H (star x) hx
    rw [form_neg_eq, ← hb]
    exact ((RingOfIntegers.isIntegral_coe b).map (starRingEnd D.host.E).toIntAlgHom).neg
  · intro H x hx
    have h := H (star x) (by rw [Formalism.L2.Col.mem_starLat, star_star]; exact hx)
    rw [form_neg_eq, star_star] at h
    have h2 := h.neg.map (starRingEnd D.host.E).toIntAlgHom
    rw [neg_neg] at h2
    exact ⟨⟨_, h2⟩, star_star (R := D.host.E) _⟩

theorem negConj_isHerm : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW₁ G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((-1 : D.host.E) • (spW₁ G i j).gram) Λ (fun w => -W.cart (.grid (i : ℕ) (j : ℕ)) (τf w)) bas)
        ((D.R.m - j) / 2) ((spW₁ G i j).rank - (D.R.m - j) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hB
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hV := node_isV G hL hR
  have hsd : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) := hV.sd
  have hlat : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) := by
    let N := G.Λ (.grid (i : ℕ) (j : ℕ))
    have hN : Submodule.IsFullLattice D.host.E N :=
      Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsd
    letI : Submodule.IsLattice D.host.E (Formalism.L2.Col.starLat D.host.E N) :=
      Formalism.L2.Col.brp_starLat_lattice D.host.E N hsd.1
    refine ⟨?_⟩
    have heq : star '' (N : Set (Fin (spW₁ G i j).rank → D.host.E)) =
        (Formalism.L2.Col.starLat D.host.E N : Set (Fin (spW₁ G i j).rank → D.host.E)) := by
      ext x
      change (∃ y, y ∈ N ∧ star y = x) ↔ star x ∈ N
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨star x, hx, star_star x⟩
    rw [← heq]
    exact Formalism.L2.Col.brp_star_span_top D.host.E _ (Submodule.IsFullLattice.span_eq_top (self := hN))
  have hb : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) β :=
    fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) _ (GlobalTheory.AdelicU.isCMExt_host D)
  refine ⟨Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ))),
    fun v => if h : v ∈ B.P then (hb ⟨v, h⟩).choose else 1, ⟨?_, ?_, hlat, ?_, ?_, ?_⟩⟩
  · intro a b
    show star (((-1 : D.host.E) • (spW₁ G i j).gram) b a) = ((-1 : D.host.E) • (spW₁ G i j).gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, star_gram]
  · intro w
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, ← hV.rank] at hs
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 = -((spW₁ G i j).gram.map (B.emb w).1) := by
      ext a b; simp
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _ _
    rw [eJ]
    exact hasSig_neg_of_hasSignature hs
  · intro y
    exact mem_starLat_iff_form (spW₁ G i j) hsd y
  · intro w
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 =
        -((gramAt D (spW₁ G i j) (τf w)).map star) := by
      ext a b; simp [gramAt, hB]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _
    rw [eJ]
    exact isCartan_neg_conj (W.cart_is _ hR (τf w))
  · intro v
    show GlobalTheory.AdelicU.IsSplitBasis _ _ (if h : v.1 ∈ B.P then (hb ⟨v.1, h⟩).choose else 1)
    rw [dite_eq_left v.2]
    exact (hb v).choose_spec

end GlobalTheory.TripleSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_negConj_member_hermitianLatticeSpaceData : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW₁ G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((-1 : D.host.E) • (spW₁ G i j).gram) Λ (fun w => -W.cart (.grid (i : ℕ) (j : ℕ)) (τf w)) bas)
        ((D.R.m - j) / 2) ((spW₁ G i j).rank - (D.R.m - j) / 2) := by
  first | exact @GlobalTheory.TripleSpace.negConj_isHerm | exact GlobalTheory.TripleSpace.negConj_isHerm | (intros; apply GlobalTheory.TripleSpace.negConj_isHerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FrameCoord {K : Type} [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K)
    {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)} (m1 : SABMap t₀ Xo.univ.t y.x)
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ)
    (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K) : Prop :=
  ∀ i, ∃ (u : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A),
    u ≫ m1.φ = y.u ρ i ∧ u ≫ m2.φ = w.left ≫ F.φ ∧ IsLieComb (v i) F.v w

def LocBasis {K : Type} [Field K] [NumberField K] {n : ℕ} (𝔓 : HeightOneSpectrum (𝓞 K))
    (L : Submodule (𝓞 K) (Fin n → K)) {m : ℕ} (b : Fin m → Fin n → K) : Prop :=
  (∀ i, b i ∈ L) ∧ LinearIndependent K b ∧
    ∀ x ∈ L, ∃ d : 𝓞 K, d ∉ 𝔓.asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b)

end GlobalTheory.PtDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
noncomputable section

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (σ) in
def finK {n : ℕ} (W : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : Set (UA σ W.J) :=
  {x | ∃ k ∈ KInf σ W τ, ∃ g ∈ UAt σ W (fun u : AF F => u.2), x = k * g}

variable {a a' : ℕ}

structure InducedMaj (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop where
  cartan : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)
  tie : ∀ w, ∃ a : Fin n₁ → ℂ, Y.θ w * (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) =
    (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) * Y₁.θ w

theorem InducedMaj.of_comm {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w))
    (h₂ : ∀ w, Y.θ w * H.ι.map (B.emb w).1 = H.ι.map (B.emb w).1 * Y₁.θ w) : InducedMaj B H Y Y₁ :=
  ⟨h₁, fun w => ⟨0, by
    have e : Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) (0 : Fin n₁ → ℂ) = 0 := by ext; simp [Matrix.vecMulVec_apply]
    rw [e, add_zero]; exact h₂ w⟩⟩


variable (σ) in
def IsIsoPlane (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
    (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) ∧ InducedMaj B H Y Y₁

theorem IsIsoPlane.of_adapted {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w))
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) : IsIsoPlane σ B H Y Y₁ :=
  ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, h, .of_comm h₁ fun w => (hH.cartan w).1⟩

end GlobalTheory.ThK.DescB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjTypeOverReal

theorem exists_tau_of_val {D : D7} (ψ : D.host.E →+* ℂ)
    (h : ψ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) :
    ∃ τ : D.what₂.Tau, tauE D τ = ψ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 ψ
  refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, ?_⟩
  simp [tauE]

theorem sqrt_sq' {D : D7} : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [map_pow, h3, h0]
  simp

theorem exists_conj_tauE_over (D : D7) (w : InfinitePlace D.host.F) : ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  haveI : Algebra.IsAlgebraic D.host.F D.host.E := inferInstance
  haveI : Module.IsTorsionFree D.host.F ℂ := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let ψ : D.host.E →ₐ[D.host.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : (ψ : D.host.E →+* ℂ).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    rfl
  have hreal : (starRingEnd ℂ).comp w.embedding = w.embedding := by
    have hw : w.IsReal := IsTotallyReal.isReal w
    have := (InfinitePlace.isReal_iff.1 hw)
    exact this
  have h0 : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : (ψ : D.host.E →+* ℂ) D.host.sqrtMinusD ^ 2 =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    rw [← map_pow, sqrt_sq', h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · obtain ⟨τ, hτ⟩ := exists_tau_of_val (ψ : D.host.E →+* ℂ) h2
    refine ⟨τ, ?_⟩
    rw [hτ, RingHom.comp_assoc, hψ, hreal]
  · obtain ⟨τ, hτ⟩ := exists_tau_of_val ((starRingEnd ℂ).comp (ψ : D.host.E →+* ℂ))
      (by rw [RingHom.comp_apply, h2]; simp)
    refine ⟨τ, ?_⟩
    rw [hτ, ← RingHom.comp_assoc]
    have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; simp
    rw [hcc, RingHom.id_comp, hψ]

theorem conj_tauE_over_realPlace : ∀ {D : D7} (w : InfinitePlace D.host.F), ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding :=
  fun {D} w => exists_conj_tauE_over D w

end GlobalTheory.ConjTypeOverReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_tauE_comp_algebraMap_eq_embedding : ∀ {D : D7} (w : InfinitePlace D.host.F), ∃ τ : D.what₂.Tau,
    ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
  first | exact @GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace | exact GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace | (intros; apply GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

def infScale (s : ℝ) : AF F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) s), 1)

theorem infScale_mul_fst (s : ℝ) (x : AF F) : (infScale F s * x).1 = (infScale F s).1 * x.1 := rfl

theorem infScale_mul_snd (s : ℝ) (x : AF F) : (infScale F s * x).2 = x.2 := by
  show (infScale F s).2 * x.2 = x.2
  simp [infScale]

theorem evI_infScale_mul (s : ℝ) (x : AF F) : evI F (infScale F s * x) = s • evI F x := by
  unfold evI
  rw [infScale_mul_fst, map_mul]
  simp only [infScale, Prod.fst, RingEquiv.apply_symm_apply, Algebra.smul_def]

end GlobalTheory.TorusTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
noncomputable section

namespace GlobalTheory.ThK.EvUniq

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def FinRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (v : Pl F)
    (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ) : Prop :=
  (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) φ φ₁ →
      ∀ χ₁ ∈ SB (Fin n × Fin d₁ → Fv F v), Acts (evFin F v) (M₁.co.rho B.ψ z) (T φ) χ₁ → T φ₁ = χ₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → T φ₁ = T φ

def InfRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁)
    (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) : Prop :=
  (∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) f f₁ →
      ∀ g₁ : SInf F (Fin n × Fin d₁), Acts (evI F) (M₁.co.rho B.ψ z) (T f) g₁ → T f₁ = g₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (M.co.rho B.ψ u) f f₁ → T f₁ = T f

end GlobalTheory.ThK.EvUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TwistRam

theorem not_unrAt_alpha_div_beta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w P hP hu hS
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hS
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hS (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : ¬ (L.xiH t).UnrAt w := by
    refine (hL.Q_ram t w).2 ?_
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := P) (Q := w) hu.symm with h | h
    · exact Or.inl (h ▸ hP)
    · exact Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  have e0 : alpha G t i j / beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  rw [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)]
  intro hn
  apply hxi
  have e : L.xiH t = GlobalTheory.FunObj.SqNum.nuH G t i j * G.ch.chiH (D.R.m - i) / L.C.mu0 j := by
    rw [GlobalTheory.FunObj.SqNum.nuH, div_mul_cancel, mul_div_cancel_left]
  rw [e, div_eq_mul_inv]
  exact (hn.mul hchi).mul hmu.inv

end GlobalTheory.TwistRam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_at_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | (intros; apply GlobalTheory.TwistRam.not_unrAt_alpha_div_beta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def nmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  1 - Matrix.vecMulVec (u + c • x) (incM F J *ᵥ fun i => cA σ (x i)) -
    Matrix.vecMulVec x (incM F J *ᵥ fun i => cA σ (u i))

theorem nmat_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (v : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : nmat σ J x u c *ᵥ v = v - hA σ J v x • (u + c • x) - hA σ J v u • x := by
  ext i
  simp only [nmat, hA, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.vecMulVec_mulVec, Pi.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm v, dotProduct_comm v]
  ring

end GlobalTheory.UnipMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ArchInj

theorem eq_zero_of_at_of_piInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) z → (∀ w, piInf (τ w) z = 0) → z = 0 :=
  fun _ _ _ _ _ _ _ _ hCM τ z hz h0 => GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ z hz h0

end GlobalTheory.ArchInj
end
